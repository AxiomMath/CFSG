module

public import CFSG.ClassicalInvolution.WeakCT.Amalgam
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.ClassicalInvolution.Phan.Center
public import CFSG.ClassicalInvolution.WeakCT.Center
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open scoped MatrixGroups

def l62Elt (K : Type) [Field K] : SL(2, K) :=
  ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; norm_num⟩

theorem l62Elt_pow_three (K : Type) [Field K] : l62Elt K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  show (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_three, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem l62Elt_ne_one (K : Type) [Field K] : l62Elt K ≠ 1 := by
  intro h
  have h10 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp [l62Elt] at h10

theorem l62Elt_orderOf (K : Type) [Field K] : orderOf (l62Elt K) = 3 :=
  orderOf_eq_prime (l62Elt_pow_three K) (l62Elt_ne_one K)

theorem l62_three_dvd_mul_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : 3 ∣ q * (q ^ 2 - 1) := by
  by_cases h3 : 3 ∣ q
  · exact h3.mul_right _
  · have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
    have h2 : q ^ 2 % 3 = 1 := by
      rcases hmod with h | h <;> simp [Nat.pow_mod, h]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have d2 : 3 ∣ q ^ 2 - 1 := by omega
    exact d2.mul_left q

theorem l62_two_le_pRank_of_hom {H T : Type} [Group H] [Group T] [Finite T] {b : H}
    (hb : orderOf b = 3) (φ : (Subgroup.zpowers b) × (Subgroup.zpowers b) →* T)
    (hφ : Function.Injective φ) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) := by
  have hcz : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hexp : ∀ u : Subgroup.zpowers b, u ^ 3 = 1 := fun u =>
    orderOf_dvd_iff_pow_eq_one.1 (by rw [← hcz]; exact orderOf_dvd_natCard u)
  have hcomm : ∀ x y : (Subgroup.zpowers b) × (Subgroup.zpowers b), x * y = y * x :=
    fun x y => Prod.ext (mul_comm' x.1 y.1) (mul_comm' x.2 y.2)
  have hpow : ∀ z : (Subgroup.zpowers b) × (Subgroup.zpowers b), z ^ 3 = 1 := fun z =>
    Prod.ext (by simp [hexp]) (by simp [hexp])
  have hA : Nat.card ((Subgroup.zpowers b) × (Subgroup.zpowers b)) = 3 ^ 2 := by
    rw [Nat.card_prod, hcz]
    norm_num
  exact CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow hA φ hφ le_top

theorem l62_disjoint_blockEmb_four (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] :
    Disjoint (CFSG.ClassicalInvolution.Phan.blockEmb K p f 4 2 0 (by norm_num)).range
      (CFSG.ClassicalInvolution.Phan.blockEmb K p f 4 2 2 (by norm_num)).range := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨A, rfl⟩ ⟨B, hB⟩
  have h0 : 0 + 2 ≤ 4 := by norm_num
  have hA : A = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro x y
    have h1 := congrFun (congrFun (congrArg (fun g : CFSG.ClassicalInvolution.Phan.Su K p f 4 =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hB)
      (CFSG.ClassicalInvolution.Phan.blockIdx 0 h0 x))
      (CFSG.ClassicalInvolution.Phan.blockIdx 0 h0 y)
    have hnot : ¬ (2 ≤ (CFSG.ClassicalInvolution.Phan.blockIdx 0 h0 x).val ∧
        (CFSG.ClassicalInvolution.Phan.blockIdx 0 h0 x).val < 2 + 2) := by
      rw [CFSG.ClassicalInvolution.Phan.blockIdx_val]
      have := x.isLt
      omega
    rw [CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb,
      CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb,
      CFSG.ClassicalInvolution.Phan.blockMat_apply_blockIdx,
      CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left _ hnot] at h1
    simp only [Matrix.one_apply,
      (CFSG.ClassicalInvolution.Phan.blockIdx_injective h0).eq_iff] at h1
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply]
    exact h1.symm
  rw [hA, map_one]

theorem l62_two_le_pRank_statedProj_sl (n : ℕ) (hn : 5 ≤ n) (K : Type) [Field K] [Finite K] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  have h4 : 0 + 4 ≤ n := by omega
  let θ : SL(n, K) →* StatedProj (StatedSL n K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).comp
      (specialLinearGroupEquivStatedSL n K).toMonoidHom
  have hθ : θ.ker ≤ Subgroup.center SL(n, K) := by
    intro A hA
    have h1 : specialLinearGroupEquivStatedSL n K A ∈
        (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := (QuotientGroup.eq_one_iff _).mp hA
    rw [← map_center_eq_statedScalars n K] at h1
    obtain ⟨B, hB, hBA⟩ := h1
    rwa [← (specialLinearGroupEquivStatedSL n K).injective hBA]
  have hinj : Function.Injective
      (θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K n 4 0 h4)) :=
    CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective hθ h4 (by omega)
  have h2a : 0 + 2 ≤ 4 := by norm_num
  have h2b : 2 + 2 ≤ 4 := by norm_num
  let f₁ : ↥(Subgroup.zpowers (l62Elt K)) →* SL(4, K) :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL K 4 2 0 h2a).comp
      (Subgroup.zpowers (l62Elt K)).subtype
  let f₂ : ↥(Subgroup.zpowers (l62Elt K)) →* SL(4, K) :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL K 4 2 2 h2b).comp
      (Subgroup.zpowers (l62Elt K)).subtype
  have hc12 : ∀ u v : ↥(Subgroup.zpowers (l62Elt K)), Commute (f₁ u) (f₂ v) := fun u v =>
    CFSG.ClassicalInvolution.WeakCT.blockSL_comm h2a h2b (Or.inl (by norm_num))
      (u : SL(2, K)) (v : SL(2, K))
  have hd : Disjoint f₁.range f₂.range := by
    refine Disjoint.mono ?_ ?_
      (CFSG.ClassicalInvolution.WeakCT.blockSL_disjoint (K := K) h2a h2b (by norm_num))
    · rintro _ ⟨u, rfl⟩
      exact ⟨(u : SL(2, K)), rfl⟩
    · rintro _ ⟨u, rfl⟩
      exact ⟨(u : SL(2, K)), rfl⟩
  have hi1 : Function.Injective f₁ :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := K) h2a).comp Subtype.val_injective
  have hi2 : Function.Injective f₂ :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := K) h2b).comp Subtype.val_injective
  have hg : Function.Injective (MonoidHom.noncommCoprod f₁ f₂ hc12) :=
    (MonoidHom.noncommCoprod_injective f₁ f₂ hc12).2 ⟨hi1, hi2, hd⟩
  exact l62_two_le_pRank_of_hom (l62Elt_orderOf K)
    ((θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K n 4 0 h4)).comp
      (MonoidHom.noncommCoprod f₁ f₂ hc12))
    (hinj.comp hg)

theorem l62_two_le_pRank_statedProj_su (n : ℕ) (hn : 5 ≤ n) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))) := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hUF.charP
  have h4 : 0 + 4 ≤ n := by omega
  let θ : CFSG.ClassicalInvolution.Phan.Su K p f n →* StatedProj (StatedSU n (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).comp
      (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n)).toMonoidHom
  have hθ : θ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f n) := by
    intro g hg
    have h1 : (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n) g :
        StatedSU n (p ^ f) K) ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) :=
      (QuotientGroup.eq_one_iff _).mp hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hcen : (Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈
        Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hgc : ((g : GL (Fin n) K)) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
    have := Subgroup.mem_center_iff.mp hcen (h : GL (Fin n) K)
    show (h : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (h : GL (Fin n) K)
    rw [hgc]
    exact this
  have hinj : Function.Injective
      (θ.comp (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 4 0 h4)) :=
    CFSG.ClassicalInvolution.Phan.comp_blockEmb_injective hK hθ h4 (by omega) (by omega)
  have hcard2 : Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 2) = p ^ f * ((p ^ f) ^ 2 - 1) :=
    (Nat.card_congr (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2)).toEquiv).trans
      (CFSG.RankThree.SubgroupLists.card_statedSU_two hK)
  have h3dvd : 3 ∣ Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 2) := by
    rw [hcard2]
    exact l62_three_dvd_mul_sq_sub_one (p ^ f) (Nat.one_le_pow _ _ hp.pos)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have h2a : 0 + 2 ≤ 4 := by norm_num
  have h2b : 2 + 2 ≤ 4 := by norm_num
  let f₁ : ↥(Subgroup.zpowers b) →* CFSG.ClassicalInvolution.Phan.Su K p f 4 :=
    (CFSG.ClassicalInvolution.Phan.blockEmb K p f 4 2 0 h2a).comp (Subgroup.zpowers b).subtype
  let f₂ : ↥(Subgroup.zpowers b) →* CFSG.ClassicalInvolution.Phan.Su K p f 4 :=
    (CFSG.ClassicalInvolution.Phan.blockEmb K p f 4 2 2 h2b).comp (Subgroup.zpowers b).subtype
  have hc12 : ∀ u v : ↥(Subgroup.zpowers b), Commute (f₁ u) (f₂ v) := fun u v =>
    CFSG.ClassicalInvolution.Phan.blockEmb_comm h2a h2b (Or.inl (by norm_num))
      (u : CFSG.ClassicalInvolution.Phan.Su K p f 2) (v : CFSG.ClassicalInvolution.Phan.Su K p f 2)
  have hd : Disjoint f₁.range f₂.range := by
    refine Disjoint.mono ?_ ?_ (l62_disjoint_blockEmb_four K p f)
    · rintro _ ⟨u, rfl⟩
      exact ⟨(u : CFSG.ClassicalInvolution.Phan.Su K p f 2), rfl⟩
    · rintro _ ⟨u, rfl⟩
      exact ⟨(u : CFSG.ClassicalInvolution.Phan.Su K p f 2), rfl⟩
  have hi1 : Function.Injective f₁ :=
    (CFSG.ClassicalInvolution.Phan.blockEmb_injective (K := K) (p := p) (f := f) h2a).comp
      Subtype.val_injective
  have hi2 : Function.Injective f₂ :=
    (CFSG.ClassicalInvolution.Phan.blockEmb_injective (K := K) (p := p) (f := f) h2b).comp
      Subtype.val_injective
  have hg : Function.Injective (MonoidHom.noncommCoprod f₁ f₂ hc12) :=
    (MonoidHom.noncommCoprod_injective f₁ f₂ hc12).2 ⟨hi1, hi2, hd⟩
  exact l62_two_le_pRank_of_hom hb
    ((θ.comp (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 4 0 h4)).comp
      (MonoidHom.noncommCoprod f₁ f₂ hc12))
    (hinj.comp hg)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
