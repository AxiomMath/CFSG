module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerSL2
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)

private theorem conjAut_two_eq_one_iff_scalar {K : Type} [Field K] [CharP K 2]
    (A : GL (Fin 2) K) :
    conjAut 2 K A = 1 ↔ ∃ u : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  constructor
  · intro h
    have hinj : Function.Injective (proj 2 K) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_proj, CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot K]
    have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
        (A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) =
          (g : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) := by
      intro g
      have hg : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A g = g := by
        apply hinj
        rw [← conjAut_proj A g]
        simpa using congrArg (fun φ : MulAut (projectiveSL 2 K) => φ (proj 2 K g)) h
      have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
        (x : Matrix (Fin 2) (Fin 2) K)) hg
      rw [coe_slConjugation] at hmat
      have hAinv : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc (A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)
          = ((A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
              ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
              (A : Matrix (Fin 2) (Fin 2) K) := by
            rw [mul_assoc, mul_assoc, hAinv, mul_one]
        _ = (g : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) := by
            rw [hmat]
    have hT := hcomm CFSG.QuasiDihedralFusion.sl2T
    have hU := hcomm CFSG.QuasiDihedralFusion.sl2U
    have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      have h := congrFun (congrFun hT 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, CFSG.QuasiDihedralFusion.coe_sl2T] using h
    have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      have h := congrFun (congrFun hT 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, CFSG.QuasiDihedralFusion.coe_sl2T] at h
      linear_combination h
    have h01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      have h := congrFun (congrFun hU 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, CFSG.QuasiDihedralFusion.coe_sl2U, h10] using h
    have hmat : (A : Matrix (Fin 2) (Fin 2) K) =
        Matrix.scalar (Fin 2) ((A : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h10, h01, h00]
    have ha0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      have hA0 : (A : Matrix (Fin 2) (Fin 2) K) = 0 := by
        rw [hmat, h0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hone : (A : Matrix (Fin 2) (Fin 2) K) *
          ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hA0, zero_mul] at hone
      exact zero_ne_one hone
    refine ⟨Units.mk0 ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ha0, ?_⟩
    apply Units.ext
    simpa using hmat
  · rintro ⟨u, rfl⟩
    exact conjAut_scalar u

private theorem card_le_linear_recipe {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ) (hd : 2 ≤ d)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))))
    (hE : E ≤ Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))))
    (habel : IsElemAbelian p E) : Nat.card E ≤ p ^ (d - 1) := by
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))) ≤
      RecipeFieldLinear.recI d K := by
    refine (Subgroup.closure_le (RecipeFieldLinear.recI d K)).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rw [RecipeFieldLinear.coe_recI]
      exact hx
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldLinear.conj_mem_recI r
  have hErec : E ≤ RecipeFieldLinear.recI d K := hE.trans hcl
  let e := TypeA.recipeEquiv d K
  let E' : Subgroup (MulAut (projectiveSL d K)) := E.map (MulAut.congr e).toMonoidHom
  have hE'D : E' ≤ linearAutGroup d K := by
    intro y hy
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldLinear.mem_recI_iff).mp (hErec hxE)
  have hE'abel : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map habel _
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · obtain rfl : d = 2 := by omega
    let ρ : (⊤ : Subgroup (GL (Fin 2) K)) →* MulAut (projectiveSL 2 K) :=
      (conjAut 2 K).comp (⊤ : Subgroup (GL (Fin 2) K)).subtype
    have hker : ∀ A : (⊤ : Subgroup (GL (Fin 2) K)),
        ρ A = 1 ↔ (A : GL (Fin 2) K) ∈ Subgroup.center (GL (Fin 2) K) := by
      intro A
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, conjAut_two_eq_one_iff_scalar]
      exact CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff.symm
    have hrange : E' ≤ ρ.range := by
      intro y hy
      have hyD : y ∈ linearAutGroup 2 K := hE'D hy
      rw [mem_linearAutGroup_iff] at hyD
      obtain ⟨A, hA⟩ := hyD
      exact ⟨⟨A, Subgroup.mem_top A⟩, hA⟩
    have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
      hp hp2 hpK (by norm_num : 0 < 2) (⊤ : Subgroup (GL (Fin 2) K)) ρ hker E' hrange hE'abel
    rw [hcardE'] at hbound
    simpa using hbound
  · let ρ : (⊤ : Subgroup (GL (Fin d) K)) →* MulAut (projectiveSL d K) :=
      (conjAut d K).comp (⊤ : Subgroup (GL (Fin d) K)).subtype
    have hker : ∀ A : (⊤ : Subgroup (GL (Fin d) K)),
        ρ A = 1 ↔ (A : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      intro A
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.conjAut_eq_one_iff_scalar hge]
      exact CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff.symm
    have hrange : E' ≤ ρ.range := by
      intro y hy
      have hyD : y ∈ linearAutGroup d K := hE'D hy
      rw [mem_linearAutGroup_iff] at hyD
      obtain ⟨A, hA⟩ := hyD
      exact ⟨⟨A, Subgroup.mem_top A⟩, hA⟩
    have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
      hp hp2 hpK (by omega : 0 < d) (⊤ : Subgroup (GL (Fin d) K)) ρ hker E' hrange hE'abel
    rw [hcardE'] at hbound
    exact hbound

private theorem card_le_unitary_recipe {d n : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hne : ¬(d = 3 ∧ 2 ^ n = 2)) (hK : Nat.card K = (2 ^ n) ^ 2)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    (hE : E ≤ Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)) ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))))
    (habel : IsElemAbelian p E) : Nat.card E ≤ p ^ (d - 1) := by
  have h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn hK
  have hd1 : 1 ≤ d := by omega
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)) ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ≤
      RecipeFieldSU.recIU d h hd1 := by
    refine (Subgroup.closure_le (RecipeFieldSU.recIU d h hd1)).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rw [RecipeFieldSU.coe_recIU h hK hd1]
      exact hx
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldSU.conj_mem_recIU h hd1 r
  have hErec : E ≤ RecipeFieldSU.recIU d h hd1 := hE.trans hcl
  let e := InndiagSU.projEquiv h hd1
  let E' : Subgroup (MulAut (UnitaryHigher.primeFormP h ((1 : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K))) := E.map (MulAut.congr e).toMonoidHom
  have hE'D : E' ≤ UnitaryHigher.primeFormD h ((1 : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) := by
    intro y hy
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldSU.mem_recIU_iff h hd1).mp (hErec hxE)
  have hE'abel : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map habel _
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_diagonal
    h hd hne hp hp2 hpq E' hE'D hE'abel
  rw [hcardE'] at hbound
  exact hbound

theorem rk2_inndiag_card_le_linear {lab : GLALabel} (hlab : GLAInLambda2 lab) (htag : lab.tag = .A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ lab.n - 1) :
    Rk2LabelAll lab fun R _ I _ => IsSimpleGroup R →
      ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
        IsElemAbelian p E → Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .A := htag
  cases ht
  dsimp only [GLAInLambda2] at hlab ⊢
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  intro _ E hE habel
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hpq
  have hl1 : 1 ≤ l := hlab.2.1
  have hbound := card_le_linear_recipe (d := l + 1) (K := K) hp hp2 hpK (by omega) E hE habel
  have hord : rk2Ord p n = 1 := (rk2Ord_eq_one_iff (p := p) (n := n)).2 hpq
  have hmul : rk2Mult ⟨.A, l, n⟩ (rk2Ord p n) = l := by
    rw [hord]
    simp [rk2Mult]
  calc Nat.card E ≤ p ^ (l + 1 - 1) := hbound
    _ = p ^ rk2Mult ⟨.A, l, n⟩ (rk2Ord p n) := by rw [hmul]; simp

theorem rk2_inndiag_card_le_unitary {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .twA) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    Rk2LabelAll lab fun R _ I _ => IsSimpleGroup R →
      ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
        IsElemAbelian p E → Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .twA := htag
  cases ht
  dsimp only [GLAInLambda2] at hlab ⊢
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  intro _ E hE habel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hn : 1 ≤ n := by simpa using hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  have hd : 3 ≤ l + 1 := by omega
  have hne : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h3, h2⟩
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hl
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hbound := card_le_unitary_recipe (d := l + 1) (n := n) (K := K) hp hp2 hpq hn hd hne hK E hE habel
  have hord : rk2Ord p n = 2 := (rk2Ord_eq_two_iff hp hp2).2 hpq
  have hmul : rk2Mult ⟨.twA, l, n⟩ (rk2Ord p n) = l := by
    rw [hord]
    simp [rk2Mult]
  calc Nat.card E ≤ p ^ (l + 1 - 1) := hbound
    _ = p ^ rk2Mult ⟨.twA, l, n⟩ (rk2Ord p n) := by rw [hmul]; simp

theorem rk2_pSubgroup_le_inn_linear {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .A := htag
  cases ht
  dsimp only [GLAInLambda2] at hlab ⊢
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  intro E hE hEp
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fact p.Prime := ⟨hp⟩
  have hl1 : 1 ≤ l := hlab.2.1
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K)) Set.univ ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K) →*
          MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K)))) ≤
      RecipeFieldLinear.recI (l + 1) K := by
    refine (Subgroup.closure_le (RecipeFieldLinear.recI (l + 1) K)).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rw [RecipeFieldLinear.coe_recI]
      exact hx
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldLinear.conj_mem_recI r
  have hErec : E ≤ RecipeFieldLinear.recI (l + 1) K := hE.trans hcl
  let e := TypeA.recipeEquiv (l + 1) K
  let E' : Subgroup (MulAut (projectiveSL (l + 1) K)) := E.map (MulAut.congr e).toMonoidHom
  have hE'D : E' ≤ linearAutGroup (l + 1) K := by
    intro y hy
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldLinear.mem_recI_iff).mp (hErec hxE)
  have hE'p : IsPGroup p E' := hEp.map (MulAut.congr e).toMonoidHom
  let H := linearAutGroup (l + 1) K
  let N : Subgroup H := (inner (projectiveSL (l + 1) K)).subgroupOf H
  have hrel : (inner (projectiveSL (l + 1) K)).relIndex H ∣
      Nat.gcd (l + 1) (Nat.card K - 1) :=
    UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := l + 1) (by omega)
  have hpd' : ¬ p ∣ Nat.gcd (l + 1) (Nat.card K - 1) := by
    simpa [rk2DiagIndex, hK] using hpd
  have hNindex : ¬ p ∣ N.index := by
    change ¬ p ∣ (inner (projectiveSL (l + 1) K)).relIndex H
    exact fun hd => hpd' (hd.trans hrel)
  have hcard : Nat.card (E'.subgroupOf H) = Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'D).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hE'p
  have hE''p : IsPGroup p (E'.subgroupOf H) :=
    IsPGroup.of_card (by rw [hcard, ha])
  have hle : E'.subgroupOf H ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294Large.le_of_isPGroup_of_not_dvd_index hp N hNindex hE''p
  have hE'inner : E' ≤ inner (projectiveSL (l + 1) K) := by
    intro x hx
    have hxH : x ∈ H := hE'D hx
    have hmem : (⟨x, hxH⟩ : H) ∈ E'.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hx
    exact (Subgroup.mem_subgroupOf).mp (hle hmem)
  intro x hx
  change x ∈ inner (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K))
  have hx' : MulAut.congr e x ∈ inner (projectiveSL (l + 1) K) :=
    hE'inner (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hx)
  rw [← inner_map_congr e] at hx'
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hyx' : y = x := (MulAut.congr e).injective hyx
  rwa [hyx'] at hy

theorem rk2_pSubgroup_le_inn_unitary {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .twA) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .twA := htag
  cases ht
  dsimp only [GLAInLambda2] at hlab ⊢
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  intro E hE hEp
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := by simpa using hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  have hd : 3 ≤ l + 1 := by omega
  have hne : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h3, h2⟩
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hl
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn hK
  have hd1 : 1 ≤ l + 1 := by omega
  have hcl : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
          (LargeEvenGUSet (Fin (l + 1)) K (2 ^ n)) ∪
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))))) ≤
      RecipeFieldSU.recIU (l + 1) h hd1 := by
    refine (Subgroup.closure_le (RecipeFieldSU.recIU (l + 1) h hd1)).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rw [RecipeFieldSU.coe_recIU h hK hd1]
      exact hx
    · rintro _ ⟨r, rfl⟩
      exact RecipeFieldSU.conj_mem_recIU h hd1 r
  have hErec : E ≤ RecipeFieldSU.recIU (l + 1) h hd1 := hE.trans hcl
  let e := InndiagSU.projEquiv h hd1
  let E' : Subgroup (MulAut (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K))) := E.map (MulAut.congr e).toMonoidHom
  have hE'D : E' ≤ UnitaryHigher.primeFormD h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K) := by
    intro y hy
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hy
    exact (RecipeFieldSU.mem_recIU_iff h hd1).mp (hErec hxE)
  have hE'p : IsPGroup p E' := hEp.map (MulAut.congr e).toMonoidHom
  let D := UnitaryHigher.primeFormD h ((1 : GL (Fin (l + 1)) K) :
    Matrix (Fin (l + 1)) (Fin (l + 1)) K)
  let N : Subgroup D :=
    (inner (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K))).subgroupOf D
  have hout := UnitaryHigher.unitary_full_diagonal_outer_order (p := 2) (f := n) (K := K)
    (n := l + 1) h hd hne
  have hDcard : Nat.card (D ⧸ (inner (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K))).subgroupOf D) = Nat.gcd (l + 1) (2 ^ n + 1) :=
    hout.2.2.1
  have hpd' : ¬ p ∣ Nat.gcd (l + 1) (2 ^ n + 1) := by
    simpa [rk2DiagIndex] using hpd
  have hNindex : ¬ p ∣ N.index := by
    rw [Subgroup.index_eq_card]
    change ¬ p ∣ Nat.card (D ⧸ (inner (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K))).subgroupOf D)
    rw [hDcard]
    exact hpd'
  have hcard : Nat.card (E'.subgroupOf D) = Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'D).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hE'p
  have hE''p : IsPGroup p (E'.subgroupOf D) :=
    IsPGroup.of_card (by rw [hcard, ha])
  have hle : E'.subgroupOf D ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294Large.le_of_isPGroup_of_not_dvd_index hp N hNindex hE''p
  have hE'inner : E' ≤ inner (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K)) := by
    intro x hx
    have hxD : x ∈ D := hE'D hx
    have hmem : (⟨x, hxD⟩ : D) ∈ E'.subgroupOf D := (Subgroup.mem_subgroupOf).mpr hx
    exact (Subgroup.mem_subgroupOf).mp (hle hmem)
  intro x hx
  change x ∈ inner (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
  have hx' : MulAut.congr e x ∈ inner (UnitaryHigher.primeFormP h ((1 : GL (Fin (l + 1)) K) :
      Matrix (Fin (l + 1)) (Fin (l + 1)) K)) :=
    hE'inner (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hx)
  rw [← inner_map_congr e] at hx'
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hyx' : y = x := (MulAut.congr e).injective hyx
  rwa [hyx'] at hy


end CFSG.LocalAnalysis.GLTheoremA
