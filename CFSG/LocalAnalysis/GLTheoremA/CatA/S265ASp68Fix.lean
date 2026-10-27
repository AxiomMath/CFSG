module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68Grp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LieType.SeitzGeneration.OuterSpData
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265A
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innGrp
open CFSG.RankThree.Classical (higher_symplectic_outer_order_divides_field_multiplier_bound)

private theorem map_inf_fixSubgroup {Ω P : Type} [Group Ω] [Group P] (f : P →* Ω)
    (hf : Function.Injective f) {α : Ω →* MulAut P} (hαf : ∀ g y, f (α g y) = g * f y * g⁻¹)
    (H : Subgroup P) (g : Ω) :
    (H ⊓ fixSubgroup (α g)).map f = H.map f ⊓ Subgroup.centralizer ({g} : Set Ω) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyH, hyg⟩, rfl⟩
    refine ⟨⟨y, hyH, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hαf g y
    rw [mem_fixSubgroup.mp hyg] at h1
    calc f y * g = g * f y * g⁻¹ * g := by rw [← h1]
      _ = g * f y := by group
  · rintro ⟨⟨y, hyH, rfl⟩, hyg⟩
    refine ⟨y, ⟨hyH, mem_fixSubgroup.mpr (hf ?_)⟩, rfl⟩
    rw [hαf, ← Subgroup.mem_centralizer_singleton_iff.mp hyg]
    group

theorem QUNL.map_eq_one_of_sp68 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (h : QUNL 3 S B T x b) {K : Type} [Field K] [Finite K] (hK8 : Nat.card K = 8)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {f : StatedProj (StatedSp 3 K) →* Ω}
    (hf : Function.Injective f) (hSmap : (⊤ : Subgroup (StatedProj (StatedSp 3 K))).map f = S)
    {α : Ω →* MulAut (StatedProj (StatedSp 3 K))} (hαf : ∀ g y, f (α g y) = g * f y * g⁻¹)
    (hαb : α b = fieldAut 3 K σ)
    (hDI : ∀ c ∈ Dgrp b x, α c ∈ (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range →
      α c = 1) :
    ∀ t ∈ T, α t = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := h.cfg.elem
  have hconj : Function.Injective (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _) :=
    CFSG.RankThree.CASymplecticSubfield.conj_injective_of_center_eq_bot
      (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by norm_num))
  have hOut : Nat.card (Outer (StatedProj (StatedSp 3 K))) ∣ 3 := by
    have h1 := (higher_symplectic_outer_order_divides_field_multiplier_bound Nat.prime_two
      (by norm_num : 1 ≤ 3) (le_refl 3) (hK8.trans (by norm_num) : Nat.card K = 2 ^ 3)).1
    norm_num at h1
    exact h1
  set A : Subgroup (StatedProj (StatedSp 3 K)) := (B.map α).comap MulAut.conj with hA
  have hAe : IsElemAbelian 3 A := (hB.map α).comap hconj
  have hAfix : A ≤ fixSubgroup (fieldAut 3 K σ) := by
    intro a ha
    obtain ⟨c, hcB, hca⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp ha)
    have hcomm : α c * α b = α b * α c := by rw [← map_mul, ← map_mul, hB.comm hcB h.cfg.hb]
    rw [hca, hαb, CFSG.RankThree.CASymplecticSubfield.mul_conj_eq] at hcomm
    exact mem_fixSubgroup.mpr (hconj (mul_right_cancel hcomm)).symm
  have hA9 : 9 ≤ Nat.card A := by
    have hker3 : Nat.card ↥(α.ker ⊓ B) ≤ 3 := by
      have hle : α.ker ⊓ B ≤ Subgroup.zpowers x := by
        rintro c ⟨hck, hcB⟩
        refine (h.cfg.centB c hcB).mp
          (centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_))
        rw [← hSmap] at hs
        obtain ⟨z, -, rfl⟩ := hs
        have h1 := hαf c z
        rw [MonoidHom.mem_ker.mp hck, MulAut.one_apply] at h1
        calc f z * c = c * f z * c⁻¹ * c := by rw [← h1]
          _ = c * f z := by group
      calc Nat.card ↥(α.ker ⊓ B) ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
        _ = orderOf x := Nat.card_zpowers x
        _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hB.2 x h.cfg.xB)
    have hBM : Nat.card B = Nat.card (B.map α) * Nat.card ↥(α.ker ⊓ B) := by
      rw [← Subgroup.relIndex_ker B α, Subgroup.relIndex_mul_card]
    have hMA : (innGrp (StatedProj (StatedSp 3 K))).relIndex (B.map α) * Nat.card A =
        Nat.card (B.map α) := by
      have h1 : Nat.card A = Nat.card ↥(innGrp (StatedProj (StatedSp 3 K)) ⊓ B.map α) := by
        rw [← Subgroup.card_map_of_injective (K := A) hconj, hA, Subgroup.map_comap_eq]
        rfl
      rw [h1, Subgroup.relIndex_mul_card]
    have hr3 : (innGrp (StatedProj (StatedSp 3 K))).relIndex (B.map α) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) ((Subgroup.relIndex_dvd_index_of_normal _ _).trans
        (by rw [Subgroup.index_eq_card]; exact hOut))
    have hB81 : 81 ≤ Nat.card B := le_trans (by norm_num) h.cfg.big
    have : 81 ≤ 3 * Nat.card A * 3 := calc
      81 ≤ Nat.card B := hB81
      _ = Nat.card (B.map α) * Nat.card ↥(α.ker ⊓ B) := hBM
      _ ≤ Nat.card (B.map α) * 3 := Nat.mul_le_mul_left _ hker3
      _ = (innGrp (StatedProj (StatedSp 3 K))).relIndex (B.map α) * Nat.card A * 3 := by
        rw [hMA]
      _ ≤ 3 * Nat.card A * 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr3)
    omega
  have h9dvd : 3 ^ 2 ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := hAe.isPGroup.exists_card_eq
    rw [hk] at hA9 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_dvd_pow 3 hk2
  obtain ⟨A₀, hA₀9, -, hA₀A⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := ⊥) (L := A) (by rw [Subgroup.card_bot]; exact one_dvd _) h9dvd bot_le
  have hIpart : Ipart 3 S b = (fixSubgroup (fieldAut 3 K σ)).map f := by
    have h1 := map_inf_fixSubgroup f hf hαf ⊤ b
    rw [top_inf_eq, hSmap, hαb] at h1
    show GLAPLayer 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) = _
    rw [← h1, ← CFSG.glaPLayer_map_eq_of_injective Nat.prime_three f hf,
      glaPLayer_fixSubgroup_fieldAut_eight hK8 hσ]
  have hAL : ∀ a ∈ A, a ≠ 1 → GLAPLayer 3 (fixSubgroup (fieldAut 3 K σ) ⊓
      Subgroup.centralizer ({a} : Set (StatedProj (StatedSp 3 K)))) = ⊥ := by
    intro a ha ha1
    obtain ⟨c, hcB, hca⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp ha)
    have hcD : c ∉ Dgrp b x := fun hcD => ha1 (hconj (by
      rw [map_one, ← hca]
      exact hDI c hcD (MonoidHom.mem_range.mpr ⟨a, hca.symm⟩)))
    have hfixa : fixSubgroup (α c) =
        Subgroup.centralizer ({a} : Set (StatedProj (StatedSp 3 K))) := by
      ext y
      rw [mem_fixSubgroup, hca, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
        mul_inv_eq_iff_eq_mul, eq_comm]
    have h1 := map_inf_fixSubgroup f hf hαf (fixSubgroup (fieldAut 3 K σ)) c
    rw [hfixa, ← hIpart] at h1
    have hnl : GLAPLayer 3 ((fixSubgroup (fieldAut 3 K σ) ⊓
        Subgroup.centralizer ({a} : Set (StatedProj (StatedSp 3 K)))).map f) = ⊥ := by
      rw [h1]
      exact h.nl c hcB hcD
    rw [← CFSG.glaPLayer_map_eq_of_injective Nat.prime_three f hf] at hnl
    exact (Subgroup.map_eq_bot_iff_of_injective _ hf).mp hnl
  have hU : (T.map α).comap MulAut.conj = ⊥ :=
    eq_bot_of_normalized_two_subgroup_fieldAut_eight hK8 hσ (hA₀A.trans hAfix)
      (hAe.mono hA₀A) (by rw [hA₀9]; norm_num) (fun a ha ha1 => hAL a (hA₀A ha) ha1)
      ((h.cfg.two.map α).comap_of_injective _ hconj)
      (hA₀A.trans ((Subgroup.comap_mono ((Subgroup.map_mono h.cfg.bnorm).trans
        (Subgroup.le_normalizer_map α))).trans (Subgroup.le_normalizer_comap _)))
  intro t ht
  obtain ⟨k, hk⟩ := h.cfg.two ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk (α t) : Outer (StatedProj (StatedSp 3 K))) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, ← map_pow, htk, map_one, QuotientGroup.mk_one])
  have h2 := (orderOf_dvd_natCard
    (QuotientGroup.mk (α t) : Outer (StatedProj (StatedSp 3 K)))).trans hOut
  have h3 := Nat.dvd_gcd h1 h2
  rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one] at h3
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (show α t ∈
    (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range from
      (QuotientGroup.eq_one_iff (α t)).mp (orderOf_eq_one_iff.mp h3))
  have hpU : p ∈ (T.map α).comap MulAut.conj :=
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨t, ht, hp.symm⟩)
  rw [hU, Subgroup.mem_bot] at hpU
  rw [← hp, hpU, map_one]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
