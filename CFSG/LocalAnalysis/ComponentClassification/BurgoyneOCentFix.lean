module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOResGrp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (isSubnormal_subgroupOf_of_normalizes
  mul_conj_mul_inv)

variable {K : Type} [Field K] {d : ℕ}

abbrev isoCent (R A : GL (Fin d) K) : Subgroup (GL (Fin d) K) :=
  CatalogueBGraphForm.isometryGroup d K R ⊓ centralizer ({A} : Set (GL (Fin d) K))

theorem conj_mem_isoCent {R A h : GL (Fin d) K}
    (hh : h ∈ CatalogueBGraphForm.isometryGroup d K R) {c : Kˣ}
    (hc : A * h * A⁻¹ = GeneralLinearGroup.scalar (Fin d) c * h) {z : GL (Fin d) K}
    (hz : z ∈ isoCent R A) : h * z * h⁻¹ ∈ isoCent R A := by
  obtain ⟨hzI, hzC⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hh hzI) (inv_mem hh), ?_⟩
  rw [mem_centralizer_singleton_iff] at hzC ⊢
  have hs : ∀ g : GL (Fin d) K, g * GeneralLinearGroup.scalar (Fin d) c =
      GeneralLinearGroup.scalar (Fin d) c * g := fun g => (commute_scalar c g).eq
  have e1 : A * h = GeneralLinearGroup.scalar (Fin d) c * h * A := by
    rw [← hc, inv_mul_cancel_right]
  have e2 : h⁻¹ * A = GeneralLinearGroup.scalar (Fin d) c * A * h⁻¹ := by
    have : h⁻¹ * (A * h) * h⁻¹ = h⁻¹ * (GeneralLinearGroup.scalar (Fin d) c * h * A) * h⁻¹ := by
      rw [e1]
    calc h⁻¹ * A = h⁻¹ * (A * h) * h⁻¹ := by group
      _ = h⁻¹ * (GeneralLinearGroup.scalar (Fin d) c * h * A) * h⁻¹ := this
      _ = h⁻¹ * (h * GeneralLinearGroup.scalar (Fin d) c) * A * h⁻¹ := by rw [hs h]; group
      _ = GeneralLinearGroup.scalar (Fin d) c * A * h⁻¹ := by group
  calc h * z * h⁻¹ * A = h * z * (h⁻¹ * A) := by group
    _ = h * z * (GeneralLinearGroup.scalar (Fin d) c * A * h⁻¹) := by rw [e2]
    _ = (h * z * GeneralLinearGroup.scalar (Fin d) c) * A * h⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin d) c * h * (z * A) * h⁻¹ := by rw [hs (h * z)]; group
    _ = GeneralLinearGroup.scalar (Fin d) c * h * (A * z) * h⁻¹ := by rw [hzC]
    _ = (GeneralLinearGroup.scalar (Fin d) c * h * A) * z * h⁻¹ := by group
    _ = A * (h * z * h⁻¹) := by rw [← e1]; group

theorem conj_mem_commutator_isoCent {R A h : GL (Fin d) K}
    (hh : h ∈ CatalogueBGraphForm.isometryGroup d K R) {c : Kˣ}
    (hc : A * h * A⁻¹ = GeneralLinearGroup.scalar (Fin d) c * h) {z : GL (Fin d) K}
    (hz : z ∈ ⁅isoCent R A, isoCent R A⁆) : h * z * h⁻¹ ∈ ⁅isoCent R A, isoCent R A⁆ := by
  have hmap : (isoCent R A).map (MulAut.conj h).toMonoidHom ≤ isoCent R A := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_isoCent hh hc hx
  have := commutator_mono hmap hmap
  rw [← Subgroup.map_commutator] at this
  exact this ⟨z, hz, rfl⟩

variable [Finite K]

theorem cent_fix (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))).range ≤ B)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ oddCoreIn B (oκ _ g))
    {X : GL (Fin d) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) :
    (g'.val.left : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map g'.val.right *
        ((g'.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (X : Matrix (Fin d) (Fin d) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ R) = ⁅CatalogueBGraphForm.isometryGroup d K R,
      CatalogueBGraphForm.isometryGroup d K R⁆ := matrixDerived_oQ h2 R hR
  set A := g.val.left with hA
  set Z := isoCent R A with hZ
  set t := oκ (oQ R) g with ht
  set φ := (matrixDerivedConjugation (oQ R) g).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ R), ((φ Y : matrixDerived (oQ R)) : GL (Fin d) K) =
      A * Y * A⁻¹ := by
    intro Y
    change (matrixDerivedConjugation (oQ R) g Y).val = _
    rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply]
  have hφt : ∀ Y, t (projH (matrixDerived (oQ R)) Y) = projH (matrixDerived (oQ R)) (φ Y) :=
    fun Y => kappa_lift _ Y
  have hZH : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [hHeq]
    exact commutator_mono inf_le_left inf_le_left
  have hZZ : ⁅Z, Z⁆ ≤ Z := Subgroup.commutator_le_self Z
  set F := ⁅Z, Z⁆.subgroupOf (matrixDerived (oQ R)) with hF
  have hF1 : ∀ Y ∈ F, φ Y = Y := by
    intro Y hY
    apply Subtype.ext
    rw [hφc]
    have hc := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hZZ (mem_subgroupOf.1 hY))).2
    rw [← hc, mul_inv_cancel_right]
  have hF2 : ∀ h : matrixDerived (oQ R), h⁻¹ * φ h ∈
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ R)) →
      ∀ Y ∈ F, h * Y * h⁻¹ ∈ F := by
    intro h hh Y hY
    obtain ⟨c, hc⟩ := hh
    have hc' : ((h : GL (Fin d) K))⁻¹ * (A * h * A⁻¹) = GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      change _ = ((h : GL (Fin d) K))⁻¹ * ((φ h : matrixDerived (oQ R)) : GL (Fin d) K)
      rw [hφc]
    have hcA : A * h * A⁻¹ = GeneralLinearGroup.scalar (Fin d) c * h := by
      calc A * h * A⁻¹ = (h : GL (Fin d) K) * (((h : GL (Fin d) K))⁻¹ * (A * h * A⁻¹)) := by
            group
        _ = (h : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by rw [hc']
        _ = GeneralLinearGroup.scalar (Fin d) c * h := (commute_scalar c (h : GL (Fin d) K)).eq
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K R :=
      Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
    rw [mem_subgroupOf] at hY ⊢
    exact conj_mem_commutator_isoCent hhI hcA hY
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixedH hinj hB φ hφt hF1 hF2
  obtain ⟨hperf, m, L, hsup, hL⟩ := hcd
  have hfixL : ∀ i, ∀ Y : matrixDerived (oQ R), (Y : GL (Fin d) K) ∈ L i →
      oκ (oQ R) g' (projH (matrixDerived (oQ R)) Y) = projH (matrixDerived (oQ R)) Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf (matrixDerived (oQ R)) with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans hZH)).symm hq
    have hLF : Lh ≤ F := fun Z' hZ' => mem_subgroupOf.2 (hLI (mem_subgroupOf.1 hZ'))
    have hQim := isQuasisimple_map_conjProjH hinj hLhq
    have hQsub : ((Lh.map (conjProjH (matrixDerived (oQ R)))).subgroupOf
        (B ⊓ centralizer ({t} : Set _))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hLF) ?_ hsub
      rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
      have hx' : (x : GL (Fin d) K) ∈ ⁅Z, Z⁆ := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      simpa using hLn _ hx' _ hl'
    have hc := commute_of_mem_pPrimeCore ((map_mono hLF).trans hle) hQim hQsub
      (even_card_of_isQuasisimple hQim) hy ⟨Y, mem_subgroupOf.2 hY, rfl⟩
    apply hinj
    rw [← mul_conj_mul_inv]
    change _ * conjProjH (matrixDerived (oQ R)) Y * _ = conjProjH (matrixDerived (oQ R)) Y
    rw [hc, mul_inv_cancel_right]
  have hFsup : F ≤ MonoidHom.eqLocus ((oκ (oQ R) g').toMonoidHom.comp
      (projH (matrixDerived (oQ R)))) (projH (matrixDerived (oQ R))) := by
    intro Y hY
    have hY' : (Y : GL (Fin d) K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf (matrixDerived (oQ R))).map
        (matrixDerived (oQ R)).subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hZH)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z' hZ' => ?_ :
      (⨆ i, (L i).subgroupOf (matrixDerived (oQ R))) ≤ _) hY'L
    exact hfixL i Z' (mem_subgroupOf.1 hZ')
  have hperfF : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (matrixDerived (oQ R)).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZH, hperf]
  exact kappa_eq_of_fix g' hperfF (fun Y hY => hFsup hY) (X := ⟨X, hZH hX⟩) (mem_subgroupOf.2 hX)

omit [Finite K] in
theorem commute_of_odd_gen {R : GL (Fin d) K} (hd : 0 < d)
    (hker : OKer (oQ R)) {g g' : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hg'1 : g'.val.right = 1) {c : K}
    (hA2 : (g.val.left : Matrix (Fin d) (Fin d) K) * g.val.left = c • 1) (hc : c ≠ 0)
    (hodd : Odd (orderOf (oκ _ g')))
    (hcomm : oκ _ g' * oκ _ g = oκ _ g * oκ _ g') :
    (g'.val.left : Matrix (Fin d) (Fin d) K) * g.val.left =
      (g.val.left : Matrix (Fin d) (Fin d) K) * g'.val.left := by
  set D := (g'.val.left : Matrix (Fin d) (Fin d) K) with hD
  set Am := (g.val.left : Matrix (Fin d) (Fin d) K) with hAm
  have hleft : ∀ x y : similarityPairs (oQ R), x.val.right = 1 →
      (x * y).val.left = x.val.left * y.val.left := by
    intro x y hx
    change (x.val * y.val).left = _
    rw [SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply]
  have hright : ∀ x y : similarityPairs (oQ R), x.val.right = 1 → y.val.right = 1 →
      (x * y).val.right = 1 := by
    intro x y hx hy
    change (x.val * y.val).right = 1
    rw [SemidirectProduct.mul_right, hx, hy, mul_one]
  have hinvl : ∀ x : similarityPairs (oQ R), x.val.right = 1 → x⁻¹.val.left = x.val.left⁻¹ := by
    intro x hx
    change (x.val⁻¹).left = _
    rw [SemidirectProduct.inv_left, hx, inv_one, map_one, MulAut.one_apply]
  have hinvr : ∀ x : similarityPairs (oQ R), x.val.right = 1 → x⁻¹.val.right = 1 := by
    intro x hx
    change (x.val⁻¹).right = 1
    rw [SemidirectProduct.inv_right, hx, inv_one]
  have hk : oκ _ (g' * g * g'⁻¹ * g⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨-, l, hl⟩ := hker _ hk
  have hl' : g'.val.left * g.val.left * g'.val.left⁻¹ * g.val.left⁻¹ =
      GeneralLinearGroup.scalar (Fin d) l := by
    rw [hl, hleft _ _ (hright _ _ (hright _ _ hg'1 hg1) (hinvr _ hg'1)),
      hleft _ _ (hright _ _ hg'1 hg1), hleft _ _ hg'1, hinvl _ hg'1, hinvl _ hg1]
  have hDA : D * Am = (l : K) • (Am * D) := by
    have e : g'.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) l *
        (g.val.left * g'.val.left) := by
      rw [← hl']
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul] at e'
    exact e'
  have hpow : ∀ k : ℕ, D ^ k * Am = (l : K) ^ k • (Am * D ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, hDA, Matrix.mul_smul, ← Matrix.mul_assoc, ih,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, pow_succ, mul_comm ((l : K) ^ k) (l : K)]
  have hpowg : ∀ k : ℕ, ((g' ^ k).val.left : Matrix (Fin d) (Fin d) K) = D ^ k ∧
      (g' ^ k).val.right = 1 := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      rw [pow_succ, hleft _ _ ih.2, Units.val_mul, ih.1, pow_succ]
      exact ⟨rfl, hright _ _ ih.2 hg'1⟩
  set m := orderOf (oκ _ g') with hm
  obtain ⟨-, l', hl'm⟩ := hker _ (by rw [map_pow]; exact pow_orderOf_eq_one (oκ _ g'))
  have hDm : D ^ m = (l' : K) • 1 := by
    rw [← (hpowg m).1, ← hl'm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hA0 : Am ≠ 0 := by
    intro h0
    rw [h0, Matrix.zero_mul] at hA2
    have := congrFun (congrFun hA2 ⟨0, hd⟩) ⟨0, hd⟩
    simp at this
    exact hc this.symm
  have hlm : (l : K) ^ m = 1 := by
    have e := hpow m
    rw [hDm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at e
    have e2 : ((l' : K) - (l : K) ^ m * l') • Am = 0 := by rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.1 e2 with h | h
    · have hl0 : (l' : K) ≠ 0 := l'.ne_zero
      have : (1 - (l : K) ^ m) * l' = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · linear_combination -h'
      · exact absurd h' hl0
    · exact absurd h hA0
  have hl2 : (l : K) * l = 1 := by
    have e : D * (Am * Am) = ((l : K) * l) • ((Am * Am) * D) := by
      rw [← Matrix.mul_assoc, hDA, Matrix.smul_mul, Matrix.mul_assoc, hDA, Matrix.mul_smul,
        smul_smul, Matrix.mul_assoc]
    rw [hA2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at e
    have hD0 : D ≠ 0 := by
      intro h0
      have e1 := congrArg (fun M => M ^ m) h0
      simp only [hDm] at e1
      rw [zero_pow (by have := hodd.pos; omega)] at e1
      have := congrFun (congrFun e1 ⟨0, hd⟩) ⟨0, hd⟩
      simp at this
    have e2 : (c - (l : K) * l * c) • D = 0 := by rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.1 e2 with h | h
    · have : (1 - (l : K) * l) * c = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · linear_combination -h'
      · exact absurd h' hc
    · exact absurd h hD0
  have hl1 : (l : K) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have : (l : K) ^ m = l := by
      rw [hk, pow_succ, pow_mul, sq, hl2, one_pow, one_mul]
    rw [← this, hlm]
  rw [hDA, hl1, one_smul]

end CFSG.ComponentClassification.Burgoyne.O
