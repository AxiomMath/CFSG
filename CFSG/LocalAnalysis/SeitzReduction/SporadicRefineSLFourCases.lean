module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourA8
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuter
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.Sporadic.SmallOddCore.HS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem index_ne_two_of_isPerfect {G : Type*} [Group G] (hG : Group.IsPerfect G)
    (H : Subgroup G) : H.index ≠ 2 := by
  intro h2
  have hc : commutator G ≤ H := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    rw [commutatorElement_def, mul_mem_iff_of_index_two h2, mul_mem_iff_of_index_two h2,
      mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
    tauto
  rw [hG.commutator_eq_top, top_le_iff] at hc
  rw [hc, index_top] at h2
  norm_num at h2

section McL


theorem false_of_mcl_index_two {S : Type} [Group S] (e : S ≃* NativeSporadic.McL) {s : S}
    (hs : orderOf s = 2) {H : Subgroup (fixedSubgroup (MulAut.conj s))} (hH : H.index = 2) :
    False := by
  obtain ⟨hperf, -, -⟩ :=
    Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hs
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have : Group.IsPerfect (centralizer ({s} : Set S)) := hperf
  have hperf' : Group.IsPerfect (fixedSubgroup (MulAut.conj s)) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  exact index_ne_two_of_isPerfect hperf' H hH

end McL

section HS


theorem hs_inner_card_centralizer {S : Type} [Group S] (e : S ≃* NativeSporadic.HS) {s : S}
    (hs : orderOf s = 2) :
    Nat.card (centralizer ({s} : Set S)) = 7680 ∨
      Nat.card (centralizer ({s} : Set S)) = 2880 := by
  set θ : S ≃* hsP := e.trans hsPermEquiv with hθ
  set r : Equiv.Perm (Fin 3850) := ((θ s : hsP) : Equiv.Perm (Fin 3850)) with hrdef
  have hrP : r ∈ hsP := (θ s).2
  have hrR : r ∈ hsR := (le_sup_left : hsP ≤ hsP ⊔ zpowers hsU) hrP
  have hord : orderOf r = 2 := by
    rw [hrdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs]
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨row, hrow, g, hg, hrg⟩ := hcover r hrR hord
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows row hrow
  have hrepP : tp 3850 row.rep ∈ hsP := by
    have h : tp 3850 row.rep = g⁻¹ * r * g := by rw [hrg]; group
    rw [h]
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hrP) hg
  have hinner : row.outer = false := by
    cases h : row.outer
    · rfl
    · exact absurd hrepP (hout.1 h)
  have hcard : Nat.card ↥(hsP ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 3850)))) =
      row.centOrder := by
    rw [hrg, inf_centralizer_conj hsP hg, card_map_of_injective (MulAut.conj g).injective]
    exact hcent
  set ι : S →* Equiv.Perm (Fin 3850) := hsP.subtype.comp θ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp θ.injective
  have hrange : ι.range = hsP := by
    rw [hι, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr θ.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hCS : Nat.card (centralizer ({s} : Set S)) =
      Nat.card ↥(hsP ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 3850)))) := by
    rw [Nat.card_congr
      (Sporadic.Recognition.McLCentralizer.centralizerEquivOfInjective ι hιinj s).toEquiv,
      hrange]
    rfl
  rw [hCS, hcard]
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · left
    rfl
  · right
    rfl
  · exact absurd hinner (by decide)
  · exact absurd hinner (by decide)

end HS

section ON


theorem on_outer_false_of_SL_four {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.ON)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {K : Type} [Field K] (hK : Nat.card K = 2) {D : Subgroup S} (hfix : ∀ x ∈ D, σ x = x)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDcard : Nat.card D = 20160 := card_of_mulEquiv_SL_four hK eD
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 6) (G := D)
    (by rw [hDcard]; norm_num)
  set T₀ : Subgroup S := K₀.map D.subtype with hT₀def
  have hT₀ : Nat.card T₀ = 64 := by
    rw [hT₀def, card_map_of_injective D.subtype_injective, hK₀]
    norm_num
  have hfixT : ∀ x ∈ T₀, σ x = x := by
    rintro _ ⟨y, -, rfl⟩
    exact hfix y y.2
  obtain ⟨q, hqT, hqo, W, hWT, hWcard, hWq⟩ :=
    on_outer_exists_of_fix_card_sixtyfour e hσ hout hT₀ hfixT
  obtain ⟨q', hq'K, rfl⟩ := hqT
  have hWD : W ≤ D := fun w hw => by
    obtain ⟨y, -, rfl⟩ := hWT hw
    exact y.2
  set W' : Subgroup D := W.comap D.subtype with hW'def
  have hW'K : W' ≤ K₀ := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hWT hw
    have : y = w := Subtype.ext hyw
    rw [← this]
    exact hy
  have hW'card : Nat.card W' = 32 := by
    have h : W'.map D.subtype = W := by
      rw [hW'def, map_comap_eq, range_subtype, inf_of_le_right hWD]
    rw [← hWcard, ← h, card_map_of_injective D.subtype_injective]
  have hW'q : ∀ w ∈ W', w * q' = q' * w := by
    intro w hw
    exact Subtype.ext (hWq w hw)
  have hq'o : orderOf q' = 4 := by
    rw [← hqo]
    exact (Subgroup.orderOf_coe q').symm
  have h := card_le_sixteen_of_mulEquiv_SL_four hK eD (IsPGroup.of_card hK₀) hq'K hq'o hW'K hW'q
  omega

end ON

end CFSG.SeitzReduction.SporadicRefine
