module

public import CFSG.ClassicalGroups.UnitaryFlag.InvolutionCenters
public import CFSG.ClassicalGroups.UnitaryFlag.SU3NonisotropicStabilizer
public import CFSG.Open.LocalVocabulary
import CFSG.GH74.KGroups.CoverEven
import CFSG.StronglyEmbedded.PSL2Facts
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.ClassicalGroups.UnitaryFlag.LineSU2
import CFSG.GroupTheory.SteinbergCBCEPrism
import CFSG.GroupTheory.ElementaryAbelianTransport
import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import Certificates.Certificate43

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {m : ℕ} {K : Type} [Field K]

theorem exists_le_isotropicTransvectionGroup_of_isElemAbelian (h : UnitaryFieldData 2 m K)
    {P : Subgroup (unitarySU 2 m K 3)} (hP : CFSG.Open.IsElemAbelian 2 P) (hP1 : P ≠ ⊥) :
    ∃ L ∈ isotropicLines h 3, P ≤ isotropicTransvectionGroup h 3 L := by
  obtain ⟨t, htP, ht1⟩ : ∃ t ∈ P, t ≠ 1 := by
    by_contra h
    apply hP1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have ht2 : t ^ 2 = 1 := hP.2 t htP
  obtain ⟨hL, -, -⟩ := involution_mem_isotropicTransvectionGroup h ht2 ht1
  refine ⟨LinearMap.range (subOne t), hL, ?_⟩
  intro z hz
  by_cases hz1 : z = 1
  · subst hz1
    exact Subgroup.one_mem _
  have hz2 : z ^ 2 = 1 := hP.2 z hz
  have htz : t * z = z * t :=
    congrArg Subtype.val (hP.1.is_comm.comm ⟨t, htP⟩ ⟨z, hz⟩)
  have hrange : LinearMap.range (subOne t) = LinearMap.range (subOne z) :=
    range_subOne_eq_of_commute h ht2 ht1 hz2 hz1 htz
  rw [hrange]
  exact (involution_mem_isotropicTransvectionGroup h hz2 hz1).2.1

theorem mulVec_eq_of_mem_isotropicTransvectionGroup (h : UnitaryFieldData 2 m K)
    {p : Submodule K (Fin 3 → K)} (hp : p ∈ isotropicLines h 3)
    {x : unitarySU 2 m K 3} (hx : x ∈ isotropicTransvectionGroup h 3 p)
    {v : Fin 3 → K} (hv : v ∈ hermPerp h p) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hker := ker_subOne_of_mem_isotropicTransvectionGroup hp hx hx1
  have hsub : subOne x v = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact hv
  have hsmul : x • v = v := by
    have h := subOne_apply h x v
    rw [hsub] at h
    exact sub_eq_zero.mp h.symm
  rw [← Matrix.mulVecLin_apply, ← unitarySU_smul_def h x v]
  exact hsmul

theorem stdHermForm_ne_zero_of_isotropicLines_ne (h : UnitaryFieldData 2 m K)
    {p p' : Submodule K (Fin 3 → K)} (hp : p ∈ isotropicLines h 3)
    (hp' : p' ∈ isotropicLines h 3) (hne : p ≠ p') {a b : Fin 3 → K}
    (hap : a ∈ p) (hbp : b ∈ p') (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    stdHermForm h 3 a b ≠ 0 := by
  intro hab
  have hpb : p' = K ∙ b := eq_span_singleton_of_mem_of_finrank_eq_one hp'.1 hbp hb0
  have ha_perp : a ∈ hermPerp h p' := by
    rw [mem_hermPerp]
    intro y hy
    rw [hpb] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [LinearMap.map_smulₛₗ₂]
    have hba : stdHermForm h 3 b a = 0 := by
      rw [← (stdHermForm_isSymm h 3).eq a b, hab, map_zero]
    rw [hba, smul_zero]
  have hbot : a ∈ (⊥ : Submodule K (Fin 3 → K)) := by
    rw [← inf_hermPerp_eq_bot hp hp' hne.symm]
    exact Submodule.mem_inf.mpr ⟨hap, ha_perp⟩
  exact ha0 (by simpa using hbot)

theorem exists_nonzero_mem_inf_hermPerp (h : UnitaryFieldData 2 m K)
    {p p' : Submodule K (Fin 3 → K)} (hp : p ∈ isotropicLines h 3)
    (hp' : p' ∈ isotropicLines h 3) (hne : p ≠ p') :
    ∃ v ∈ hermPerp h p ⊓ hermPerp h p', v ∉ p ∧ stdHermForm h 3 v v ≠ 0 := by
  have hdim_pos : 0 < Module.finrank K ↥(hermPerp h p ⊓ hermPerp h p') := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (hermPerp h p) (hermPerp h p')
    rw [finrank_hermPerp hp, finrank_hermPerp hp'] at hsum
    have hle : Module.finrank K ↥(hermPerp h p ⊔ hermPerp h p') ≤ 3 := by
      have hle' := Submodule.finrank_le (hermPerp h p ⊔ hermPerp h p')
      rwa [Module.finrank_fin_fun] at hle'
    omega
  obtain ⟨v, hv_inf, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (p := hermPerp h p ⊓ hermPerp h p') (by
      intro hbot
      rw [hbot, finrank_bot] at hdim_pos
      omega)
  obtain ⟨hvp, hvp'⟩ := Submodule.mem_inf.mp hv_inf
  have hvp_not : v ∉ p := by
    intro hmem
    have : v ∈ p ⊓ hermPerp h p' := Submodule.mem_inf.mpr ⟨hmem, hvp'⟩
    rw [inf_hermPerp_eq_bot hp hp' hne.symm] at this
    exact hv0 ((Submodule.mem_bot (R := K) (M := Fin 3 → K)).mp this)
  have hvv : stdHermForm h 3 v v ≠ 0 :=
    stdHermForm_self_ne_zero_of_mem_hermPerp h hp hvp hvp_not
  exact ⟨v, hv_inf, hvp_not, hvv⟩

theorem exists_isotropic_pair_nonisotropic_of_ne (h : UnitaryFieldData 2 m K)
    {p p' : Submodule K (Fin 3 → K)} (hp : p ∈ isotropicLines h 3)
    (hp' : p' ∈ isotropicLines h 3) (hne : p ≠ p') :
    ∃ e f v : Fin 3 → K, e ∈ p ∧ f ∈ p' ∧ v ∈ hermPerp h p ∧ v ∈ hermPerp h p' ∧
      stdHermForm h 3 e e = 0 ∧ stdHermForm h 3 f f = 0 ∧ stdHermForm h 3 e f = 1 ∧
      stdHermForm h 3 e v = 0 ∧ stdHermForm h 3 f v = 0 ∧ stdHermForm h 3 v v ≠ 0 := by
  obtain ⟨a, ha0, haa, hpa⟩ := exists_eq_span_of_mem_isotropicLines hp
  obtain ⟨b, hb0, hbb, hpb⟩ := exists_eq_span_of_mem_isotropicLines hp'
  have hap : a ∈ p := hpa.symm ▸ Submodule.mem_span_singleton_self a
  have hbp : b ∈ p' := hpb.symm ▸ Submodule.mem_span_singleton_self b
  have hab : stdHermForm h 3 a b ≠ 0 :=
    stdHermForm_ne_zero_of_isotropicLines_ne h hp hp' hne hap hbp ha0 hb0
  let c : K := (stdHermForm h 3 a b)⁻¹
  let f : Fin 3 → K := c • b
  have hf_mem : f ∈ p' := Submodule.smul_mem p' c hbp
  have hef : stdHermForm h 3 a f = 1 := by
    change stdHermForm h 3 a (c • b) = 1
    rw [LinearMap.map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hab
  have hff : stdHermForm h 3 f f = 0 := (mem_isotropicLines.mp hp').2 f hf_mem
  obtain ⟨v, hv_inf, hvp_not, hvv⟩ := exists_nonzero_mem_inf_hermPerp h hp hp' hne
  obtain ⟨hvp, hvp'⟩ := Submodule.mem_inf.mp hv_inf
  have hev : stdHermForm h 3 a v = 0 := (mem_hermPerp.mp hvp) a hap
  have hfv : stdHermForm h 3 f v = 0 := (mem_hermPerp.mp hvp') f hf_mem
  exact ⟨a, f, v, hap, hf_mem, hvp, hvp', haa, hff, hef, hev, hfv, hvv⟩

theorem isotropicTransvectionGroup_sup_le_stabilizer (h : UnitaryFieldData 2 m K)
    {p p' : Submodule K (Fin 3 → K)} (hp : p ∈ isotropicLines h 3)
    (hp' : p' ∈ isotropicLines h 3) {v : Fin 3 → K}
    (hvp : v ∈ hermPerp h p) (hvp' : v ∈ hermPerp h p') :
    isotropicTransvectionGroup h 3 p ⊔ isotropicTransvectionGroup h 3 p' ≤
      MulAction.stabilizer (unitarySU 2 m K 3) v := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [MulAction.mem_stabilizer_iff, unitarySU_smul_def h x v, Matrix.mulVecLin_apply]
    exact mulVec_eq_of_mem_isotropicTransvectionGroup h hp hx hvp
  · intro x hx
    rw [MulAction.mem_stabilizer_iff, unitarySU_smul_def h x v, Matrix.mulVecLin_apply]
    exact mulVec_eq_of_mem_isotropicTransvectionGroup h hp' hx hvp'

theorem exists_sylow_two_ne_of_isL2 {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X m) :
    ∃ S S' : Sylow 2 X, S ≠ S' := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hm h
  let S : Sylow 2 X := Sylow.nonempty.some
  have hpair : CFSG.CGT.Timmesfeld75.IsL2Pair X (S : Subgroup X) (2 ^ m) :=
    CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (by omega) ⟨e⟩ S
  have : Finite X := hpair.finite
  have hfin : Finite (Sylow 2 X) :=
    Finite.of_injective (fun T : Sylow 2 X => (T : Subgroup X))
      (fun T U htu => Sylow.ext htu)
  have h2m : 0 < 2 ^ m := by positivity
  have h2m_gt : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
  have hcard : 1 < Nat.card (Sylow 2 X) := by
    have hLcard : Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1) := hpair.card_eq_mul
    have hNcard : Nat.card (Subgroup.normalizer (S : Set X)) = 2 ^ m * (2 ^ m - 1) :=
      hpair.card_normalizer
    have hmul := Subgroup.card_mul_index (H := Subgroup.normalizer (S : Set X))
    rw [hLcard, hNcard] at hmul
    have hindex : (Subgroup.normalizer (S : Set X)).index = 2 ^ m + 1 := by
      have h1 : (2 ^ m) * ((2 ^ m - 1) * (Subgroup.normalizer (S : Set X)).index) =
          (2 ^ m) * ((2 ^ m) ^ 2 - 1) := by
        rw [← hmul]; ring
      have h2 : (2 ^ m - 1) * (Subgroup.normalizer (S : Set X)).index =
          (2 ^ m) ^ 2 - 1 :=
        Nat.eq_of_mul_eq_mul_left h2m h1
      have h3 : (2 ^ m) ^ 2 - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
        rw [show (2 ^ m) ^ 2 - 1 = (2 ^ m) ^ 2 - 1 ^ 2 from by norm_num]
        rw [Nat.sq_sub_sq]
        ring
      have h4 : (2 ^ m - 1) * (2 ^ m + 1) =
          (2 ^ m - 1) * (Subgroup.normalizer (S : Set X)).index := by
        rw [← h3, h2]
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 ^ m - 1) h4.symm
    rw [Sylow.card_eq_index_normalizer, hindex]
    omega
  have : Nontrivial (Sylow 2 X) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨S', hS'ne⟩ := exists_ne S
  exact ⟨S, S', hS'ne.symm⟩

theorem exists_isotropic_sup_of_isL2 (h : UnitaryFieldData 2 m K) {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup (unitarySU 2 m K 3)}
    (hL : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 L n) :
    ∃ p p', p ∈ isotropicLines h 3 ∧ p' ∈ isotropicLines h 3 ∧ p ≠ p' ∧
      L ≤ isotropicTransvectionGroup h 3 p ⊔ isotropicTransvectionGroup h 3 p' := by
  obtain ⟨S, S', hS'ne⟩ := exists_sylow_two_ne_of_isL2 hn hL
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hn hL
  have hsup : (S : Subgroup L) ⊔ (S' : Subgroup L) = ⊤ :=
    CFSG.BenderSuzuki.psl2_sup_sylow_eq_top e hn hS'ne
  have hpair : CFSG.CGT.Timmesfeld75.IsL2Pair L (S : Subgroup L) (2 ^ n) :=
    CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (by omega) ⟨e⟩ S
  have hpair' : CFSG.CGT.Timmesfeld75.IsL2Pair L (S' : Subgroup L) (2 ^ n) :=
    CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (by omega) ⟨e⟩ S'
  have h2m : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
  have hS_ne_bot : (S : Subgroup L) ≠ ⊥ := by
    intro hbot
    have := hpair.card_eq
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hS'_ne_bot : (S' : Subgroup L) ≠ ⊥ := by
    intro hbot
    have := hpair'.card_eq
    rw [hbot, Subgroup.card_bot] at this
    omega
  let T := (S : Subgroup L).map L.subtype
  let T' := (S' : Subgroup L).map L.subtype
  have hT_ne_bot : T ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (S : Subgroup L))
      L.subtype_injective).not.mpr hS_ne_bot
  have hT'_ne_bot : T' ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (S' : Subgroup L))
      L.subtype_injective).not.mpr hS'_ne_bot
  obtain ⟨p, hp, hT_le_Tp⟩ := exists_le_isotropicTransvectionGroup_of_isElemAbelian h
    (CFSG.Open.IsElemAbelian.map hpair.isElemAbelian L.subtype) hT_ne_bot
  obtain ⟨p', hp', hT'_le_Tp'⟩ := exists_le_isotropicTransvectionGroup_of_isElemAbelian h
    (CFSG.Open.IsElemAbelian.map hpair'.isElemAbelian L.subtype) hT'_ne_bot
  have hmap_sup : T ⊔ T' = L := by
    change (S : Subgroup L).map L.subtype ⊔ (S' : Subgroup L).map L.subtype = L
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  have hpp' : p ≠ p' := by
    intro hpp
    have hT'_le_Tp : T' ≤ isotropicTransvectionGroup h 3 p := by
      rwa [← hpp] at hT'_le_Tp'
    have hL_le_Tp : L ≤ isotropicTransvectionGroup h 3 p := by
      rw [← hmap_sup]
      exact sup_le hT_le_Tp hT'_le_Tp
    have h2 : IsPGroup 2 L := (isPGroup_isotropicTransvectionGroup h hp).to_le hL_le_Tp
    have htop : ∀ U : Sylow 2 L, (U : Subgroup L) = ⊤ := fun U =>
      (U.is_maximal' (h2.to_subgroup ⊤) le_top).symm
    exact hS'ne (Sylow.ext ((htop S).trans (htop S').symm))
  refine ⟨p, p', hp, hp', hpp', ?_⟩
  rw [← hmap_sup]
  exact sup_le (le_trans hT_le_Tp le_sup_left) (le_trans hT'_le_Tp' le_sup_right)

theorem exists_nonisotropic_le_stabilizer_of_isL2 (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {n : ℕ} (hn : 2 ≤ n) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 L n) :
    ∃ v : Fin 3 → K, stdHermForm h 3 v v ≠ 0 ∧ L ≤ MulAction.stabilizer (unitarySU 2 m K 3) v ∧
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
        (MulAction.stabilizer (unitarySU 2 m K 3) v) m := by
  obtain ⟨p, p', hp, hp', hpp', hL_le_sup⟩ := exists_isotropic_sup_of_isL2 h hn hL
  obtain ⟨e0, f0, v, -, -, hvp, hvp', he0e0, hf0f0, he0f0, he0v, hf0v, hvv⟩ :=
    exists_isotropic_pair_nonisotropic_of_ne h hp hp' hpp'
  refine ⟨v, hvv,
    le_trans hL_le_sup (isotropicTransvectionGroup_sup_le_stabilizer h hp hp' hvp hvp'), ?_⟩
  exact isL2_of_forall_mem_iff_mulVec_eq h hm hvv he0e0 hf0f0 he0f0 he0v hf0v (fun g => by
    rw [MulAction.mem_stabilizer_iff, unitarySU_smul_def h g v, Matrix.mulVecLin_apply])

theorem exists_nonisotropic_forall_mem_iff_of_isL2 (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {L : Subgroup (unitarySU 2 m K 3)}
    (hL : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 L m) :
    ∃ v : Fin 3 → K, stdHermForm h 3 v v ≠ 0 ∧
      ∀ g : unitarySU 2 m K 3,
        g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
  have : Finite K := h.finite
  obtain ⟨v, hvv, hL_le_stab, hLv_isL2⟩ := exists_nonisotropic_le_stabilizer_of_isL2 h hm hm hL
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hm hL
  obtain ⟨eLv⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hm hLv_isL2
  have h_eq : L = MulAction.stabilizer (unitarySU 2 m K 3) v :=
    Subgroup.eq_of_le_of_card_ge hL_le_stab
      (le_of_eq (by rw [Nat.card_congr e.toEquiv, Nat.card_congr eLv.toEquiv]))
  refine ⟨v, hvv, fun g => ?_⟩
  rw [h_eq, MulAction.mem_stabilizer_iff, unitarySU_smul_def h g v, Matrix.mulVecLin_apply]

end CFSG.ClassicalGroups.UnitaryFlag

end
