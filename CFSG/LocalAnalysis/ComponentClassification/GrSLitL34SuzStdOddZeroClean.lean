module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem swapDiag_comp_injective {P : Subgroup G} {t : G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hodd : Odd (Nat.card (center ↥P))) {I : Subgroup G} (hIP : I ≤ P)
    (hI : Open.IsElemAbelian 2 I) :
    Function.Injective ((HarrisLit.swapDiag P t hc).comp (Subgroup.inclusion hIP)) := by
  have hI2 : IsElemTwo I :=
    ⟨isMulCommutative_iff_of_setLike.mp hI.1, fun x hx => by rw [← sq]; exact hI.2 x hx⟩
  intro i i' hii'
  have hδ : HarrisLit.swapDiag P t hc (Subgroup.inclusion hIP i) =
      HarrisLit.swapDiag P t hc (Subgroup.inclusion hIP i') := hii'
  have hmem : Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ ∈
      (HarrisLit.swapDiag P t hc).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hδ, mul_inv_cancel]
  have hcen : Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ ∈
      Subgroup.center ↥P := CFSG.OddStandard.HigherRank.F3.ker_swapDiag_le_center hc hmem
  have hi2 : Subgroup.inclusion hIP i * Subgroup.inclusion hIP i = 1 := by
    apply Subtype.ext
    exact hI2.2 (i : G) i.2
  have hi'2 : Subgroup.inclusion hIP i' * Subgroup.inclusion hIP i' = 1 := by
    apply Subtype.ext
    exact hI2.2 (i' : G) i'.2
  have hcomm : Subgroup.inclusion hIP i * Subgroup.inclusion hIP i' =
      Subgroup.inclusion hIP i' * Subgroup.inclusion hIP i := by
    apply Subtype.ext
    exact hI2.1 (i : G) i.2 (i' : G) i'.2
  have hb2 : (Subgroup.inclusion hIP i')⁻¹ * (Subgroup.inclusion hIP i')⁻¹ = 1 := by
    rw [← mul_inv_rev, hi'2, inv_one]
  have hb : (Subgroup.inclusion hIP i')⁻¹ * Subgroup.inclusion hIP i =
      Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ := by
    calc (Subgroup.inclusion hIP i')⁻¹ * Subgroup.inclusion hIP i
        = (Subgroup.inclusion hIP i')⁻¹ * (Subgroup.inclusion hIP i *
            Subgroup.inclusion hIP i') * (Subgroup.inclusion hIP i')⁻¹ := by group
      _ = (Subgroup.inclusion hIP i')⁻¹ * (Subgroup.inclusion hIP i' *
            Subgroup.inclusion hIP i) * (Subgroup.inclusion hIP i')⁻¹ := by rw [hcomm]
      _ = Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ := by group
  have hsq : (Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ *
          (Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹)
        = Subgroup.inclusion hIP i * ((Subgroup.inclusion hIP i')⁻¹ *
            Subgroup.inclusion hIP i) * (Subgroup.inclusion hIP i')⁻¹ := by group
      _ = Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i *
            (Subgroup.inclusion hIP i')⁻¹) * (Subgroup.inclusion hIP i')⁻¹ := by rw [hb]
      _ = (Subgroup.inclusion hIP i * Subgroup.inclusion hIP i) *
            ((Subgroup.inclusion hIP i')⁻¹ * (Subgroup.inclusion hIP i')⁻¹) := by group
      _ = 1 := by rw [hi2, hb2, mul_one]
  have h1 : orderOf (Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹) = 1 := by
    have hdvd : orderOf (Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹) ∣
        Nat.gcd (Nat.card (Subgroup.center ↥P)) 2 :=
      Nat.dvd_gcd (Subgroup.orderOf_dvd_natCard _ hcen) (orderOf_dvd_of_pow_eq_one hsq)
    rw [show Nat.gcd (Nat.card (Subgroup.center ↥P)) 2 = 1 from
      Nat.coprime_two_right.mpr hodd, Nat.dvd_one] at hdvd
    exact hdvd
  have hone : Subgroup.inclusion hIP i * (Subgroup.inclusion hIP i')⁻¹ = 1 :=
    orderOf_eq_one_iff.mp h1
  have heq : Subgroup.inclusion hIP i = Subgroup.inclusion hIP i' := mul_inv_eq_one.mp hone
  exact Subtype.ext (congrArg (fun z : ↥P => (z : G)) heq)

omit [Finite G] in
private theorem commute_mem_range_swapDiag {P : Subgroup G} {t : G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    {I : Subgroup G} (hIP : I ≤ P) (hI : Open.IsElemAbelian 2 I) {x : G} (hx : x ∈ I)
    {y : G} (hy : y ∈ ((HarrisLit.swapDiag P t hc).comp (Subgroup.inclusion hIP)).range) :
    x * y = y * x := by
  obtain ⟨i, rfl⟩ := hy
  have hfi : HarrisLit.swapDiag P t hc (Subgroup.inclusion hIP i) =
      (i : G) * MulAut.conj t (i : G) := by
    rw [HarrisLit.swapDiag_apply]
    rfl
  have hxi : x * (i : G) = (i : G) * x :=
    isMulCommutative_iff_of_setLike.mp hI.1 x hx (i : G) i.2
  have hxt : x * MulAut.conj t (i : G) = MulAut.conj t (i : G) * x :=
    (Subgroup.mem_centralizer_iff.mp (hc (hIP hx)) _
      ⟨(i : G), hIP i.2, rfl⟩).symm
  change x * HarrisLit.swapDiag P t hc (Subgroup.inclusion hIP i) =
    HarrisLit.swapDiag P t hc (Subgroup.inclusion hIP i) * x
  rw [hfi]
  calc x * ((i : G) * MulAut.conj t (i : G))
      = x * (i : G) * MulAut.conj t (i : G) := by group
    _ = (i : G) * x * MulAut.conj t (i : G) := by rw [hxi]
    _ = (i : G) * (x * MulAut.conj t (i : G)) := by group
    _ = (i : G) * (MulAut.conj t (i : G) * x) := by rw [hxt]
    _ = (i : G) * MulAut.conj t (i : G) * x := by group

theorem wGroup_eq_bot_of_le_of_l34SuzOddZero
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hK : K = (HarrisLit.swapDiag P t hc).range) (hodd : Odd (Nat.card (center ↥P)))
    {I : Subgroup G} (hIP : I ≤ P) (hI : Open.IsElemAbelian 2 I) (hI8 : 8 ≤ Nat.card I) :
    wGroup I = ⊥ := by
  have hB : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hS.base.2.2.2.2.2.1
  have hI2 : IsElemTwo I :=
    ⟨isMulCommutative_iff_of_setLike.mp hI.1, fun x hx => by rw [← sq]; exact hI.2 x hx⟩
  have hI3 : IsAbelianTwoOfRank 3 I := hI2.isAbelianTwoOfRank hI8
  let f : ↥I →* G := (HarrisLit.swapDiag P t hc).comp (Subgroup.inclusion hIP)
  let J : Subgroup G := f.range
  have hinj : Function.Injective f := swapDiag_comp_injective hc hodd hIP hI
  have hcardJ : Nat.card J = Nat.card I := by
    show Nat.card ↥(f.range) = Nat.card ↥I
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hJ8 : 8 ≤ Nat.card J := hcardJ ▸ hI8
  have hJ2 : IsElemTwo J := by
    constructor
    · rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      show f i * f i' = f i' * f i
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hI2.1 (i : G) i.2 (i' : G) i'.2)
    · rintro _ ⟨i, rfl⟩
      show f i * f i = 1
      rw [← map_mul, ← map_one f]
      congr 1
      exact Subtype.ext (hI2.2 (i : G) i.2)
  have hJ3 : IsAbelianTwoOfRank 3 J := hJ2.isAbelianTwoOfRank hJ8
  have hJleK : J ≤ K := by
    rw [hK]
    rintro _ ⟨i, rfl⟩
    exact ⟨Subgroup.inclusion hIP i, rfl⟩
  have hJA : J ≤ A := hJleK.trans (le_A_of_l34SuzOddData hD)
  have hJt : J ≤ centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hS.t_mem x (hJA hx))
  have hJbot : wGroup J = ⊥ :=
    wGroup_eq_bot_of_l34SuzOdd hSch hC4 hSV hS hJt hJ2.isElemAbelian hJ8
  have hcommIJ : ∀ x ∈ I, ∀ y ∈ J, x * y = y * x := fun x hx y hy =>
    commute_mem_range_swapDiag hc hIP hI hx hy
  calc wGroup I = wGroup J := wGroup_eq_of_commute hB hI3 hJ3 hcommIJ
    _ = ⊥ := hJbot

theorem wGroup_eq_bot_of_le_centralizer_of_l34 (hG : L34BaseSetting G) {P : Subgroup G}
    (hPq : IsQuasisimple ↥P) (hPodd : Odd (Nat.card (center ↥P)))
    (hPL : IsL34Type (↥P ⧸ center ↥P))
    (hW : ∀ I : Subgroup G, I ≤ P → Open.IsElemAbelian 2 I → 8 ≤ Nat.card I → wGroup I = ⊥)
    {F : Subgroup G} (hFP : F ≤ centralizer (P : Set G)) (hF : Open.IsElemAbelian 2 F)
    (hF8 : 8 ≤ Nat.card F) : wGroup F = ⊥ := by
  have hB : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hG.2.2.2.2.2.1
  obtain ⟨e, heP, he⟩ := exists_involution_mem_of_l34Odd hPq hPodd hPL
  obtain ⟨E, hE, -, hEab, hE16⟩ := exists_elemAbelian_sixteen_of_l34Odd hPq hPodd hPL heP he
  have hE8 : 8 ≤ Nat.card E := by rw [hE16]; norm_num
  have hEbot : wGroup E = ⊥ := hW E (hE.trans inf_le_left) hEab hE8
  have hE2 : IsElemTwo E :=
    ⟨isMulCommutative_iff_of_setLike.mp hEab.1, fun x hx => by rw [← sq]; exact hEab.2 x hx⟩
  have hF2 : IsElemTwo F :=
    ⟨isMulCommutative_iff_of_setLike.mp hF.1, fun x hx => by rw [← sq]; exact hF.2 x hx⟩
  have hE3 : IsAbelianTwoOfRank 3 E := hE2.isAbelianTwoOfRank hE8
  have hF3 : IsAbelianTwoOfRank 3 F := hF2.isAbelianTwoOfRank hF8
  have hcomm : ∀ x ∈ F, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hFP hx) y (hE hy).1).symm
  calc wGroup F = wGroup E := wGroup_eq_of_commute hB hF3 hE3 hcomm
    _ = ⊥ := hEbot

end CFSG.ComponentClassification.GrSLit.L34Sec5S
