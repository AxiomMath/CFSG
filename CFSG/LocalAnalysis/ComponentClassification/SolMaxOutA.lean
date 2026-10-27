module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36U

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

theorem eq_bot_of_perfect_of_le_range {G G' : Type*} [Group G] [Group G'] [Group.IsSolvable G]
    (f : G →* G') {K : Subgroup G'} (hK : ⁅K, K⁆ = K) (hKf : K ≤ f.range) : K = ⊥ := by
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := G)
  have h1 : ∀ j : ℕ, K ≤ (derivedSeries G j).map f := by
    intro j
    induction j with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map]
      exact hKf
    | succ j ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ← hK]
      exact commutator_mono ih ih
  have h2 := h1 k
  rw [hk, Subgroup.map_bot] at h2
  exact le_bot_iff.mp h2

variable {X : Type} [Group X]

variable {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)}

theorem le_coreActionKernel_of_le_centralizer_of_ne_one (hρ : IsPermAction θ ρ) [Finite X]
    (hm : 5 ≤ m) {s : X} (hsN : s ∈ normalizer (M : Set X)) (hs1 : ρ ⟨s, hsN⟩ ≠ 1)
    {L : Subgroup X} (hLN : L ≤ normalizer (M : Set X)) (hLs : L ≤ centralizer ({s} : Set X))
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin m)) (hperf : ⁅L, L⁆ = L) :
    L ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  by_contra hLK
  have hk := mem_coreNOf_of_rho_eq_one_of_not_le hρ hLN hm θL hperf hLK
  set A := (L.subgroupOf (normalizer (M : Set X))).map ρ with hAdef
  set K₀ : Subgroup (Perm (Fin m)) :=
    centralizer ({ρ ⟨s, hsN⟩} : Set (Perm (Fin m))) ⊓ alternatingGroup (Fin m) with hK₀def
  have hAK₀ : A ≤ K₀ := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLs hy))
    · have hyo : (y : X) ∈ oddGen L := by rw [oddGen_eq_of_perfect hperf]; exact hy
      exact mem_alternatingGroup_of_mem_oddGen (ρ := ρ) hLN hyo y.2
  have hcardL := card_eq_of_alt (by omega) θL
  have hk₁ := card_eq_card_map_mul_card_inf_ker' ρ (L.subgroupOf (normalizer (M : Set X)))
  have hLs' : Nat.card (L.subgroupOf (normalizer (M : Set X))) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv
  have hinf : Nat.card (L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) ≤
      Nat.card (coreNOf L) := by
    have h1 : L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker ≤
        (coreNOf L).subgroupOf (normalizer (M : Set X)) := by
      rintro z ⟨hz, hzk⟩
      exact hk _ hz hzk
    rw [← Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hLN)).toEquiv]
    exact Subgroup.card_le_of_le h1
  have hOpos : 0 < Nat.card (coreNOf L) := Nat.card_pos
  have h1 : (m.factorial / 2) * Nat.card (coreNOf L) ≤ Nat.card A * Nat.card (coreNOf L) := by
    calc (m.factorial / 2) * Nat.card (coreNOf L) = Nat.card L := hcardL.symm
      _ = Nat.card A * Nat.card (L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) := by
          rw [← hLs', hk₁]
      _ ≤ Nat.card A * Nat.card (coreNOf L) := Nat.mul_le_mul_left _ hinf
  have h2 := Nat.le_of_mul_le_mul_right h1 hOpos
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hK₀eq : K₀ = alternatingGroup (Fin m) := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [nat_card_alternatingGroup, Nat.card_fin]
    exact h2.trans (Subgroup.card_le_of_le hAK₀)
  apply hs1
  refine eq_one_of_commute_fixAlt (τ := 1) (fun x hx => by simp at hx) (by simp; omega)
    fun b _ => ?_
  have hb : (b : Perm (Fin m)) ∈ K₀ := by rw [hK₀eq]; exact b.2
  exact (mem_centralizer_singleton_iff.mp (mem_inf.1 hb).1).symm

theorem eq_of_isPComponent_of_four (hρ : IsPermAction θ ρ) [Finite X] (hm : 9 ≤ m) {x : X}
    (hxN : x ∈ normalizer (M : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, hxN⟩).support.card = 4)
    (hCN : centralizer ({x} : Set X) ≤ normalizer (M : Set X)) {N P : Subgroup X}
    (hN : N ≤ centralizer ({x} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({x} : Set X))))
    (hNsurj : ∀ b ∈ fixAlt (ρ ⟨x, hxN⟩), ∃ (z : X) (hz : z ∈ N),
      ρ ⟨z, hCN (hN hz)⟩ = (b : Perm (Fin m)))
    (hP : P ≤ centralizer ({x} : Set X))
    (hPpc : IsPComponent 2 (P.subgroupOf (centralizer ({x} : Set X))))
    (hPK : ¬ P ≤ UnbalancedLayer.coreActionKernel M) : P = N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer ({x} : Set X) with hYdef
  set σ := ρ ⟨x, hxN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    convert map_one ρ
    exact Subtype.ext hx2
  have hσc : σ.support.card ≤ m := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  set OY := (pPrimeCore 2 ↥Y).map Y.subtype with hOYdef
  have hOYY : OY ≤ Y := map_subtype_le _
  have hOYN : OY ≤ normalizer (M : Set X) := fun w hw => hCN (hOYY hw)
  have hOYodd : Odd (Nat.card OY) := by
    rw [hOYdef, card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOYA : ∀ w : ↥OY, ρ (inclusion hOYN w) ∈ alternatingGroup (Fin m) := by
    intro w
    have hwo : (w : X) ∈ oddGen OY := by
      refine mem_oddGen w.2 (hOYodd.of_dvd_nat ?_)
      have := orderOf_dvd_natCard w
      rwa [← Subgroup.orderOf_coe] at this
    exact mem_alternatingGroup_of_mem_oddGen (ρ := ρ) hOYN hwo _
  let ψ : ↥OY →* alternatingGroup (Fin m) := (ρ.comp (inclusion hOYN)).codRestrict _ hOYA
  have hψ : ∀ w : ↥OY, ((ψ w : alternatingGroup (Fin m)) : Perm (Fin m)) =
      ρ (inclusion hOYN w) := fun _ => rfl
  have hψodd : Odd (Nat.card ψ.range) := by
    have h1 := Subgroup.card_map_dvd (H := (⊤ : Subgroup ↥OY)) ψ
    rw [← MonoidHom.range_eq_map, Subgroup.card_top] at h1
    exact hOYodd.of_dvd_nat h1
  have hψc : ∀ g ∈ ψ.range, (g : Perm (Fin m)) * σ = σ * g := by
    rintro _ ⟨w, rfl⟩
    rw [hψ, hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hOYY w.2))
  have hψn : ∀ b ∈ fixAlt σ, ∀ g ∈ ψ.range, b * g * b⁻¹ ∈ ψ.range := by
    rintro b hb _ ⟨w, rfl⟩
    obtain ⟨z, hz, hzb⟩ := hNsurj b hb
    have hzY : z ∈ Y := hN hz
    obtain ⟨w', hw', hw'e⟩ := w.2
    have hc := (inferInstance : (pPrimeCore 2 ↥Y).Normal).conj_mem w' hw' ⟨z, hzY⟩
    have hzw : z * (w : X) * z⁻¹ ∈ OY := ⟨_, hc, by rw [← hw'e]; rfl⟩
    refine ⟨⟨_, hzw⟩, Subtype.ext ?_⟩
    rw [hψ]
    change ρ ⟨z * (w : X) * z⁻¹, hOYN hzw⟩ = (b : Perm (Fin m)) * ρ (inclusion hOYN w) *
      (b : Perm (Fin m))⁻¹
    rw [← hzb]
    have h1 : (⟨z * (w : X) * z⁻¹, hOYN hzw⟩ : ↥(normalizer (M : Set X))) =
        ⟨z, hCN hzY⟩ * inclusion hOYN w * (⟨z, hCN hzY⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hbot := eq_bot_of_odd_of_commute hσ2 hx4.le (by omega) hψodd hψc hψn
  have hOY1 : ∀ (w : X) (hw : w ∈ OY), ρ ⟨w, hOYN hw⟩ = 1 := by
    intro w hw
    have h1 : ψ ⟨w, hw⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot, mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [hψ] at h2
    exact h2
  by_contra hne
  have hne' : P.subgroupOf Y ≠ N.subgroupOf Y := fun h => by
    rw [subgroupOf_inj, inf_of_le_left hP, inf_of_le_left hN] at h
    exact hne h
  obtain ⟨-, -, hc', -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hPpc hNpc).2
      hne'
  obtain ⟨-, -, hsP, -, -⟩ := id hPpc
  have hPN : ∀ (p : X) (hp : p ∈ P) (z : X) (hz : z ∈ N),
      ρ ⟨p, hCN (hP hp)⟩ * ρ ⟨z, hCN (hN hz)⟩ = ρ ⟨z, hCN (hN hz)⟩ * ρ ⟨p, hCN (hP hp)⟩ := by
    intro p hp z hz
    have h1 : ⁅(⟨p, hP hp⟩ : ↥Y), (⟨z, hN hz⟩ : ↥Y)⁆ ∈ pPrimeCore 2 ↥Y := by
      have h2 := hc' (commutator_mem_commutator (show (⟨p, hP hp⟩ : ↥Y) ∈ P.subgroupOf Y from hp)
        (show (⟨z, hN hz⟩ : ↥Y) ∈ N.subgroupOf Y from hz))
      have h3 := (mem_inf.1 h2).1
      rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsP] at h3
      exact (mem_inf.1 h3).2
    have h4 : ρ ⁅(⟨p, hCN (hP hp)⟩ : ↥(normalizer (M : Set X))), ⟨z, hCN (hN hz)⟩⁆ = 1 :=
      hOY1 (p * z * p⁻¹ * z⁻¹) ⟨_, h1, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  have hPfix : ∀ p (hp : p ∈ P), ∀ v ∉ σ.support, ρ ⟨p, hCN (hP hp)⟩ v = v := by
    intro p hp v hv
    refine apply_eq_of_commute_fixAlt (by omega) (fun b hb => ?_) hv
    obtain ⟨z, hz, hzb⟩ := hNsurj b hb
    rw [← hzb]
    exact hPN p hp z hz
  have hPN' : P ≤ normalizer (M : Set X) := hP.trans hCN
  have hPperf : ⁅P, P⁆ = P := UnbalancedCorr.commutator_eq_of_isPComponent hP hPpc
  have hP'perf : ⁅P.subgroupOf (normalizer (M : Set X)), P.subgroupOf (normalizer (M : Set X))⁆ =
      P.subgroupOf (normalizer (M : Set X)) := by
    apply Subgroup.map_injective (normalizer (M : Set X)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPN', hPperf]
  set Pρ := (P.subgroupOf (normalizer (M : Set X))).map ρ with hPρdef
  have hPρperf : ⁅Pρ, Pρ⁆ = Pρ := by rw [hPρdef, ← Subgroup.map_commutator, hP'perf]
  have hPρle : Pρ ≤ (Perm.ofSubtype : Perm (Subtype (· ∈ σ.support)) →* Perm (Fin m)).range := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Perm.mem_range_ofSubtype_iff]
    intro v hv
    by_contra hvσ
    exact (Perm.mem_support.mp hv) (hPfix w hw v hvσ)
  have : Group.IsSolvable (Perm (Subtype (· ∈ σ.support))) := Equiv.Perm.isSolvable
    (le_of_eq (by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hx4]))
  have hbotP := eq_bot_of_perfect_of_le_range _ hPρperf hPρle
  apply hPK
  intro p hp
  have h1 : ρ ⟨p, hPN' hp⟩ ∈ Pρ := ⟨⟨p, hPN' hp⟩, hp, rfl⟩
  rw [hbotP, mem_bot] at h1
  exact hρ.mem_coreActionKernel _ h1

end CFSG.ComponentClassification.SolMax
