module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverIn
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78 CFSG.ONSchreier
  CFSG.Sporadic.ONOddCore CFSG.Blueprint.NativeSporadic Cover

@[expose] def ONQ (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Group.IsPerfect ↥K ∧
    Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 80640

theorem onQ_inL : PairClass.InL ONQ := fun _ _ _ _ _ h => h.1

theorem onPair_quotient {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .ONan L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 80640) :
    ONPair (↥L ⧸ center ↥L) ⊤ ((K.subgroupOf L).map (q ↥L)) (q ↥L ⟨u, hu⟩) := by
  refine ⟨Subgroup.mem_top _, hcov.orderOf_q_involution hu hu2, le_top, ?_, ?_, hcard⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  · have := isPerfect_subgroupOf_of_le hKL hKperf
    exact Group.IsPerfect.map _


theorem on_inFacts {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) : InFacts L K u := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  obtain ⟨x, c, hxL, hxx, hx1, hxc, hcP, hcz, hgen, hone⟩ := on_row_facts
  let eK : ↥K ≃* ↥onL := ((Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    (Subgroup.equivMapOfInjective _ Ψ hΨ)).trans (MulEquiv.subgroupCongr hK₀)
  have heK : ∀ k : K, ((eK k : onL) : Equiv.Perm (Fin N)) = Ψ ⟨k, hKL k.2⟩ := fun k => rfl
  have hone_K : OneClassOutside K := oneClassOutside_of_equiv eK hone
  have huK : u ∈ K := by
    have h0 : onz ∈ (K.subgroupOf L).map Ψ := by
      rw [hK₀]
      exact onz_mem_L
    obtain ⟨k, hk, hkz⟩ := h0
    have hkeq : k = ⟨u, hu⟩ := hΨ (hkz.trans hΨu.symm)
    have h1 : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    rwa [hkeq] at h1
  obtain ⟨k₁, hk₁, hk₁x⟩ : ∃ k ∈ K.subgroupOf L, Ψ k = x := by
    have h0 : x ∈ (K.subgroupOf L).map Ψ := by
      rw [hK₀]
      exact hxL
    exact h0
  have hv₀K : (k₁ : G) ∈ K := Subgroup.mem_subgroupOf.1 hk₁
  have hv₀sq : (k₁ : G) * (k₁ : G) = 1 := by
    have : k₁ * k₁ = 1 := hΨ (by rw [map_mul, hk₁x, hxx, map_one])
    exact congrArg Subtype.val this
  have hv₀1 : (k₁ : G) ≠ 1 := by
    intro h
    apply hx1
    have : k₁ = 1 := Subtype.ext h
    rw [← hk₁x, this, map_one]
  have hv₀c : (k₁ : G) ∉ (Subgroup.center ↥K).map K.subtype := by
    rintro ⟨y, hy, hyv⟩
    apply hxc
    have hyc := (mem_center_iff_of_equiv eK y).1 hy
    have hex : ((eK y : onL) : Equiv.Perm (Fin N)) = x := by
      rw [heK]
      have : (⟨(y : G), hKL y.2⟩ : ↥L) = k₁ := Subtype.ext hyv
      rw [this, hk₁x]
    exact ⟨eK y, hyc, hex⟩
  have hv₀cand : (k₁ : G) ∈ vCandidates K u := by
    have hsup : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 huK)
    refine ⟨?_, hv₀c, orderOf_eq_two_of_mul_self hv₀sq hv₀1⟩
    rw [hsup]
    exact hv₀K
  obtain ⟨l₀, hl₀⟩ := hΨR c hcP
  have hl₀conj : (l₀ : G) * u * (l₀ : G)⁻¹ = u * (k₁ : G) := by
    have h1 : Ψ (l₀ * ⟨u, hu⟩ * l₀⁻¹) = Ψ (⟨u, hu⟩ * k₁) := by
      calc Ψ (l₀ * ⟨u, hu⟩ * l₀⁻¹) = c * onz * c⁻¹ := by
            rw [map_mul, map_mul, map_inv, hl₀, hΨu]
        _ = onz * x := hcz
        _ = Ψ (⟨u, hu⟩ * k₁) := by rw [map_mul, hΨu, hk₁x]
    exact congrArg Subtype.val (hΨ h1)
  have hnorm : ∀ d ∈ L ⊓ centralizer ({u} : Set G), K.map (conjHom d) = K := by
    intro d hd
    have hdL : d ∈ L := hd.1
    have hdu : d * u = u * d := mem_centralizer_singleton_iff.1 hd.2
    have hdM : Ψ ⟨d, hdL⟩ ∈ onM := by
      rw [onM_eq_centralizer_z]
      refine ⟨hΨL _, mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hΨu, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdu
    have hle : K.map (conjHom d) ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      have hkK' : (⟨k, hKL hk⟩ : ↥L) ∈ K.subgroupOf L := hk
      have h1 : Ψ ⟨k, hKL hk⟩ ∈ onL := by
        rw [← hK₀]
        exact ⟨_, hkK', rfl⟩
      have h2 := on_L_conj_mem hdM h1
      rw [← hK₀] at h2
      obtain ⟨k', hk', hk'e⟩ := h2
      have h4 : k' = ⟨d, hdL⟩ * ⟨k, hKL hk⟩ * ⟨d, hdL⟩⁻¹ :=
        hΨ (by rw [hk'e, map_mul, map_mul, map_inv])
      have h3 := Subgroup.mem_subgroupOf.1 hk'
      rw [h4] at h3
      exact h3
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (conjHom_injective d)])
  have hgen₀ : K ⊔ K.map (conjHom (l₀ : G)) = L := by
    refine le_antisymm (sup_le hKL ?_) ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact L.mul_mem (L.mul_mem l₀.2 (hKL hk)) (L.inv_mem l₀.2)
    · intro g hg
      let H : Subgroup ↥L := (K ⊔ K.map (conjHom (l₀ : G))).subgroupOf L
      let HY : Subgroup (Equiv.Perm (Fin N)) := H.map Ψ
      have h1 : onL ≤ HY := by
        rw [← hK₀]
        rintro _ ⟨k, hk, rfl⟩
        exact ⟨k, Subgroup.mem_subgroupOf.2
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hk)), rfl⟩
      have h2 : onL.map (MulAut.conj c).toMonoidHom ≤ HY := by
        rw [← hK₀]
        rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        refine ⟨l₀ * k * l₀⁻¹, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right
          ⟨(k : G), Subgroup.mem_subgroupOf.1 hk, rfl⟩), ?_⟩
        rw [map_mul, map_mul, map_inv, hl₀]
        rfl
      obtain ⟨h, hH, hhg⟩ := (hgen.trans (sup_le h1 h2)) (hΨL ⟨g, hg⟩)
      have hh : h = ⟨g, hg⟩ := hΨ hhg
      rw [hh] at hH
      exact Subgroup.mem_subgroupOf.1 hH
  exact ⟨huK, hone_K, hnorm, (k₁ : G), hv₀cand, (l₀ : G), l₀.2, hl₀conj, hgen₀⟩

theorem sol78SettingLocalQ_on : Sol78SettingLocalQ .ONan ONQ ONQ := by
  intro H _ _ L K u hcov hQ
  refine ⟨?_, hQ⟩
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  have F := on_inFacts hTop hP
  exact solomonLocalQ_of_pinned hcov hu hu2 hKL hKu hKperf
    (pinnedLocal_of_solomonLocal (solomonLocal_on hTop hP)
      fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩)

theorem sol78Local39Q_on : Sol78Local39Q .ONan ONQ := by
  intro H _ _ N L K t u hcov hset hQ
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  exact (inFacts_of_quotient hcov.2.1 hcov.1.1 hu hu2 hKL hKu hKperf
    (on_inFacts hTop hP)).local39 hKL (mem_centralizer_iff.2 hKu) hset.hyp35

end CFSG.EvenSporadicStandard.Induction
