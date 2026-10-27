module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81S9

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

theorem Nine81.le_of_isPerfect_of_isSolvable_quotient {G : Type*} [Group G] {N L : Subgroup G}
    [N.Normal] (hsol : Group.IsSolvable (G ⧸ N)) (hL : Group.IsPerfect L) : L ≤ N := by
  set π := QuotientGroup.mk' N
  have hperf : Group.IsPerfect (L.map π) := by
    have := hL
    exact Group.IsPerfect.ofSurjective (π.subgroupMap_surjective L)
  have hbot : L.map π = ⊥ := by
    by_contra hne
    have : Nontrivial (L.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hsol' : Group.IsSolvable (L.map π) :=
      Group.isSolvable_of_isSolvable_injective (L.map π).subtype_injective
    exact Group.IsPerfect.not_isSolvable (L.map π) hsol'
  rw [← QuotientGroup.ker_mk' N]
  exact (Subgroup.map_eq_bot_iff L).mp hbot

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem layerIn_eq_bot (hCP : CF81L2CentPerfect) {v : H} (hst : d.Stage7 v) :
    layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) with hW
  have hJN := H₁.centralizer_le_normalizer_J
  have hzJ : d.z ∈ h.J := (mem_inf.mp d.z_D).2
  have hzN : d.z ∈ normalizer (h.J : Set H) := le_normalizer hzJ
  obtain ⟨-, p, f, hp, hp2, hf, -, hJt⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := lieModel_of_isSec8JType hp hp2 hf hJt
  have hL : ∀ L : Subgroup ↥W, IsPComponent 2 L → False := by
    intro L hL
    have hperf : Group.IsPerfect L := CatalogueBHeldSmallCore.pComponent_perfect 2 L hL
    set L' : Subgroup H := L.map W.subtype with hL'
    have hL'W : L' ≤ W := map_subtype_le L
    have hperf' : Group.IsPerfect L' :=
      Group.IsPerfect.ofSurjective (W.subtype.subgroupMap_surjective L)
    have hL'a : L' ≤ centralizer ({h.a} : Set H) := hL'W.trans inf_le_left
    have hL'N : L' ≤ normalizer (h.J : Set H) := hL'a.trans hJN
    have hL'z : ∀ x ∈ L', x * d.z = d.z * x := by
      intro x hx
      have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hL'W hx)).1
      have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hL'W hx)).2
      have h1' : x * h.a⁻¹ = h.a⁻¹ * x := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, inv_mul_cancel_left]
      calc x * d.z = (x * h.a⁻¹) * (h.a * d.z) := by group
        _ = h.a⁻¹ * (x * (h.a * d.z)) := by rw [h1']; group
        _ = h.a⁻¹ * (h.a * d.z * x) := by rw [h2]
        _ = d.z * x := by group
    have hzbar : rhoE h.J d.z = MulAut.conj ((⟨d.z, hzJ⟩ : ↥h.J) : ↥h.J ⧸ pPrimeCore 2 ↥h.J) :=
      rhoE_of_mem_J hzJ
    have hzS : d.z ∈ h.S := (mem_inf.mp d.z_D).1
    have hzP : d.z ∉ h.P := fun hP => by
      have h1 : d.z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨d.z_D, hP⟩
      rw [h.D_inf_P_eq_bot H₁.center_J, mem_bot] at h1
      have h2 := d.z_ord
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hz2 : orderOf (((⟨d.z, hzJ⟩ : ↥h.J) : ↥h.J ⧸ pPrimeCore 2 ↥h.J)) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← QuotientGroup.mk_pow]
        have : (⟨d.z, hzJ⟩ : ↥h.J) ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow]
          rw [← d.z_ord]
          exact pow_orderOf_eq_one _)
        rw [this, QuotientGroup.mk_one]
      · intro h1
        apply hzP
        refine mem_inf.mpr ⟨hzS, (rhoE_eq_one_iff hzN).mp ?_⟩
        rw [hzbar, h1, map_one]
    have hRC : rhoImg h.J L' ≤ centralizer ({MulAut.conj ((⟨d.z, hzJ⟩ : ↥h.J) :
        ↥h.J ⧸ pPrimeCore 2 ↥h.J)} : Set (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J))) := by
      intro σ hσ
      obtain ⟨x, hx, hxN, rfl⟩ := exists_of_mem_rhoImg hσ
      rw [mem_centralizer_singleton_iff, ← hzbar, ← rhoE_mul hzN hxN, ← rhoE_mul hxN hzN,
        hL'z x hx]
    have hRperf : Group.IsPerfect (rhoImg h.J L') := by
      have : Group.IsPerfect (L'.subgroupOf (normalizer (h.J : Set H))) :=
        Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hL'N).symm.toMonoidHom)
          (subgroupOfEquivOfLe hL'N).symm.surjective
      exact Group.IsPerfect.ofSurjective ((Eight.oddBarAction h.J).subgroupMap_surjective _)
    have hR := hCP _ p' f' hp' hp2' hf' hJL _ hz2 _ hRC hRperf
    have hL'Y : L' ≤ Y9 h := fun x hx => mem_inf.mpr ⟨hL'a hx, (rhoE_eq_one_iff (hL'N hx)).mp
      (by
        have := rhoE_mem_rhoImg hL'N hx
        rwa [hR, mem_bot] at this)⟩
    obtain ⟨N, hNn, hNc, hNq⟩ := d.hasNormalPComplement_kernel hst
    have hperf'' : Group.IsPerfect (L'.subgroupOf (Y9 h)) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hL'Y).symm.toMonoidHom)
        (subgroupOfEquivOfLe hL'Y).symm.surjective
    have hsol : Group.IsSolvable (↥(Y9 h) ⧸ N) := by
      have := hNq.isNilpotent
      infer_instance
    have hLN := Nine81.le_of_isPerfect_of_isSolvable_quotient hsol hperf''
    have hcardL : Nat.card L = Nat.card (L'.subgroupOf (Y9 h)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hL'Y).toEquiv, hL',
        card_map_of_injective W.subtype_injective]
    have hodd : Nat.Coprime 2 (Nat.card L) := by
      rw [hcardL]
      exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le hLN) hNc
    obtain ⟨-, -, hq⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).1 hL
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have htop : pPrimeCore 2 ↥L = ⊤ := by
      apply le_antisymm le_top
      apply le_sSup
      exact ⟨Subgroup.normal_top, by rw [Subgroup.card_top]; exact hodd⟩
    rw [htop] at hnt
    exact (not_nontrivial_iff_subsingleton.mpr (QuotientGroup.subsingleton_quotient_top)) hnt
  show (pLayer ↥W 2).map W.subtype = ⊥
  have : pLayer ↥W 2 = ⊥ := sSup_eq_bot.mpr fun L hL' => (hL L hL').elim
  rw [this, Subgroup.map_bot]

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
