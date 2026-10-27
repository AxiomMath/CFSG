module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MHH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem mem_center_of_card_ker_two {E S : Type*} [Group E] [Group S] (π : E →* S)
    (hk : Nat.card π.ker = 2) {z : E} (hz : z ∈ π.ker) : z ∈ center E := by
  classical
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · rw [hz1]
    simp
  have hfin : (π.ker : Set E).Finite := by
    have : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
    exact Set.toFinite _
  have hncard : (π.ker : Set E).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hk
  have h2 : ∀ w ∈ π.ker, w = 1 ∨ w = z := by
    intro w hw
    by_contra hcon
    push Not at hcon
    have h3 : ({1, z, w} : Set E).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, z, w, fun h => hz1 h.symm, fun h => hcon.1 h.symm, fun h => hcon.2 h.symm, rfl⟩
    have hle : ({1, z, w} : Set E).ncard ≤ (π.ker : Set E).ncard := by
      refine Set.ncard_le_ncard ?_ hfin
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact π.ker.one_mem
      · exact hz
      · exact hw
    omega
  have hconj : g * z * g⁻¹ ∈ π.ker := π.normal_ker.conj_mem z hz g
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  rcases h2 _ hconj with h | h
  · exact absurd h hne
  · calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]

theorem noPerfectDoubleCover_of_noTwoCover {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hc : center S = ⊥) (h : CFSG.GH74.Generic.NoTwoCover S) :
    CFSG.Monster.Schur.NoPerfectDoubleCover S := by
  intro E _ π hπ hE hk
  have : Finite E := by
    have h1 := (π.ker).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hk] at h1
    refine Nat.finite_of_card_ne_zero ?_
    rw [h1]
    have : 0 < Nat.card S := Nat.card_pos
    omega
  have hker : π.ker ≤ center E := fun z hz => mem_center_of_card_ker_two π hk hz
  have hZ : center E = π.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    rw [MonoidHom.mem_ker]
    have : π z ∈ center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro s
      obtain ⟨g, rfl⟩ := hπ s
      rw [← map_mul, ← map_mul, hz g]
    rw [hc, Subgroup.mem_bot] at this
    exact this
  have e : E ⧸ center E ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hq : CFSG.Open.IsQuasisimple E := ⟨Group.isPerfect_def.1 hE, MulEquiv.isSimpleGroup e⟩
  have h2 : IsPGroup 2 ↥(center E) := by
    rw [hZ]
    exact IsPGroup.of_card (n := 1) (by rw [hk]; norm_num)
  have hq' := (CFSG.Foundations.SteinbergCA.quasisimple_iff E).2.2.1.2 hq
  have h0 := h E hq' h2 ⟨e⟩
  rw [hZ] at h0
  rw [h0, Subgroup.card_bot] at hk
  omega

theorem center_eq_bot_of_equiv {Y G : Type*} [Group Y] [Group G] (e : Y ≃* G)
    (hc : center G = ⊥) : center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := congrArg e (hz (e.symm g))
    simpa using this
  rw [hc, Subgroup.mem_bot] at hz'
  exact e.injective (by simpa using hz')

theorem mem_innSub_of_card_le {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card Y) (b : MulAut Y) : b ∈ innSub Y := by
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := conj_injective_of_center_bot hc
  have hcardI : Nat.card ↥(innSub Y) = Nat.card Y := by
    have hrange : innSub Y = (MulAut.conj : Y →* MulAut Y).range := rfl
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have htop : innSub Y = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hcardI]
    exact hcard
  rw [htop]
  exact Subgroup.mem_top b

theorem noR_two_M11
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M11) : NoR 2 Y := by
  have hnt := CFSG.GH74.KGroups.M11.noTwoCover_M11 Y hY
  obtain ⟨e⟩ := hY
  let e0 : Y ≃* NativeSporadic.M11 := e
  have : IsSimpleGroup NativeSporadic.M11 := fam_m11_simplicity.2.2
  have hsimple : IsSimpleGroup Y := MulEquiv.isSimpleGroup e0
  have : Finite Y := Finite.of_equiv _ e0.symm.toEquiv
  have hc : center Y = ⊥ := center_eq_bot_of_equiv e0 m11_center_eq_bot'
  have hnp := noPerfectDoubleCover_of_noTwoCover hsimple hc hnt
  intro K _ _ hK ⟨f⟩ h2
  have hodd := CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
    hnp K (Group.isPerfect_def.1 hK.1) ⟨f⟩
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem n1_M11
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M11) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} (h : N1Config Y p b R₀) :
    ∃ r : ℕ, HHObsAt p r Y b ∧ (r = 2 → NoR 2 Y) := by
  have hNoR := noR_two_M11 hY
  obtain ⟨e⟩ := hY
  let e' : Y ≃* ↥NativeSporadic.M11 := e
  have hc : Subgroup.center ↥NativeSporadic.M11 = ⊥ := m11_center_eq_bot'
  have hAut : Nat.card (MulAut ↥NativeSporadic.M11) ≤ Nat.card ↥NativeSporadic.M11 :=
    m11_mulAut_card
  have hcard : Nat.card (MulAut ↥NativeSporadic.M11) ≤ 2 * Nat.card ↥NativeSporadic.M11 := by
    omega
  have hpc := pCfg_top_of_n1_equiv e' hc hcard h
  have hp : p.Prime := h.1
  have hp2 : p ≠ 2 := h.2.1
  have hbo : orderOf b = p := h.2.2.1
  have hp3 : p = 3 := by
    by_contra hp3
    rw [← Subgroup.subgroupOf_self] at hpc
    exact not_pCfg_of_noP le_rfl (k := 4) (by rw [m11_card]; norm_num)
      (by rw [m11_card]; norm_num)
      (Certificates.certificate5253.2.2.2.2.2.2.2.2.2.1 p hp hp2 hp3) hpc
  have hcY : center Y = ⊥ := center_eq_bot_of_equiv e' hc
  have hYfin : Finite Y := Finite.of_equiv _ e'.symm.toEquiv
  have hbY : Nat.card (MulAut Y) ≤ Nat.card Y := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
    exact hAut
  obtain ⟨y₀, hy₀⟩ := mem_innSub_of_card_le hcY hbY b
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := conj_injective_of_center_bot hcY
  have hxo : orderOf (e' y₀) = 3 := by
    rw [MulEquiv.orderOf_eq, ← orderOf_injective (MulAut.conj : Y →* MulAut Y) hinj y₀]
    rw [hy₀, hbo, hp3]
  have hxo' : orderOf ((e' y₀ : ↥NativeSporadic.M11) : Equiv.Perm (Fin 11)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hxo
  obtain ⟨u, hu, v, hv, huu, hvv, huv, hxu, hxv, hne⟩ :=
    Certificates.certificate5253.2.2.2.2.2.2.2.2.2.2 _ (e' y₀).2 hxo'
  refine ⟨2, ?_, fun _ => hNoR⟩
  exact hhObsAt_of_equiv_pair e' hp2 (hy₀.symm) (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)
    (Subtype.ext huu) (Subtype.ext hvv) (Subtype.ext huv) (Or.inr (Or.inl (Subtype.ext hxu)))
    (Or.inr (Or.inr (Subtype.ext hxv)))
    (Or.inl fun h1 => hne (hxu.symm.trans (congrArg Subtype.val h1)))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
