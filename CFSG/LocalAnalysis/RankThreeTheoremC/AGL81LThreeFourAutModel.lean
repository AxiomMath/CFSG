module

import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.ClassTwoPairing
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped IsMulCommutative commutatorElement

private theorem exists_central_commutator_pairing {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    (hclass : commutator P ≤ Subgroup.center P) (hZ : Nat.card (Subgroup.center P) = q) :
    ∃ c : P → P → ZMod q, (∀ x x' y, c (x * x') y = c x y + c x' y) ∧
      (∀ x y y', c x (y * y') = c x y + c x y') ∧ (∀ x y, c x y = 0 ↔ x * y = y * x) ∧
      ∀ σ : MulAut P, ∃ k : ZMod q, ∀ x y, c (σ x) (σ y) = k * c x y := by
  let e : Subgroup.center P ≃* Multiplicative (ZMod q) :=
    mulEquivOfPrimeCardEq hZ ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod q))
  let κ : P → P → Subgroup.center P := fun x y =>
    ⟨⁅x, y⁆, CFSG.RankThreeEvenClassification.Helpers.classTwo_commutator_mem_center hclass x y⟩
  refine ⟨fun x y => (e (κ x y)).toAdd, fun x x' y => ?_, fun x y y' => ?_, fun x y => ?_,
    fun σ => ?_⟩
  · dsimp only
    rw [← toAdd_mul, ← map_mul]
    exact congrArg (fun w => (e w).toAdd) (Subtype.ext
      (CFSG.RankThreeEvenClassification.Helpers.classTwo_commutator_mul_left hclass x x' y))
  · dsimp only
    rw [← toAdd_mul, ← map_mul]
    exact congrArg (fun w => (e w).toAdd) (Subtype.ext
      (CFSG.RankThreeEvenClassification.Helpers.classTwo_commutator_mul_right hclass x y y'))
  · dsimp only
    rw [toAdd_eq_zero, EmbeddingLike.map_eq_one_iff, ← commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  ·
    let τ := MulAut.characteristic (Subgroup.center P) σ
    let g : ZMod q →+ ZMod q := AddMonoidHom.mk'
      (fun t => (e (τ (e.symm (Multiplicative.ofAdd t)))).toAdd) fun s t => by
        simp only [ofAdd_add, map_mul, toAdd_mul]
    refine ⟨g 1, fun x y => ?_⟩
    have hg : g (e (κ x y)).toAdd = (e (κ (σ x) (σ y))).toAdd := by
      show (e (τ (e.symm (Multiplicative.ofAdd (e (κ x y)).toAdd)))).toAdd = _
      rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      exact congrArg (fun w => (e w).toAdd) (Subtype.ext (map_commutatorElement σ x y))
    have h := map_nsmul g (e (κ x y)).toAdd.val 1
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, hg] at h
    dsimp only
    rw [h, mul_comm]

private theorem exists_bilinForm_of_pairing {q : ℕ} {P : Type} [Group P] {W : Type}
    [AddCommGroup W] [Module (ZMod q) W] (π : P → W) (hπ : Function.Surjective π)
    (hπmul : ∀ x y, π (x * y) = π x + π y) (hπker : ∀ x, π x = 0 ↔ x ∈ Subgroup.center P)
    (c : P → P → ZMod q) (hcl : ∀ x x' y, c (x * x') y = c x y + c x' y)
    (hcr : ∀ x y y', c x (y * y') = c x y + c x y') (hc0 : ∀ x y, c x y = 0 ↔ x * y = y * x) :
    ∃ B : LinearMap.BilinForm (ZMod q) W, (∀ x y, B (π x) (π y) = c x y) ∧
      (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧ ∀ w : W, B w w = 0 := by
  have hπ1 : π 1 = 0 := by
    have h := hπmul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hπinv : ∀ x, π x⁻¹ = -π x := by
    intro x
    have h := hπmul x⁻¹ x
    rw [inv_mul_cancel, hπ1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hwd : ∀ x x', π x = π x' → ∀ y, c x y = c x' y ∧ c y x = c y x' := by
    intro x x' h y
    have hz : x⁻¹ * x' ∈ Subgroup.center P := by
      rw [← hπker, hπmul, hπinv, h, neg_add_cancel]
    have hzy := Subgroup.mem_center_iff.mp hz y
    constructor
    · conv_rhs => rw [← mul_inv_cancel_left x x']
      rw [hcl, (hc0 _ _).mpr hzy.symm, add_zero]
    · conv_rhs => rw [← mul_inv_cancel_left x x']
      rw [hcr, (hc0 _ _).mpr hzy, add_zero]
  let s := Function.surjInv hπ
  have hs : ∀ u, π (s u) = u := Function.surjInv_eq hπ
  let f : W → W → ZMod q := fun u v => c (s u) (s v)
  have hf : ∀ x y, f (π x) (π y) = c x y := fun x y => by
    dsimp only [f]
    rw [(hwd _ _ (hs (π x)) _).1, (hwd _ _ (hs (π y)) _).2]
  have H1 : ∀ u u' v, f (u + u') v = f u v + f u' v := by
    intro u u' v
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨x', rfl⟩ := hπ u'
    obtain ⟨y, rfl⟩ := hπ v
    rw [← hπmul, hf, hf, hf, hcl]
  have H3 : ∀ u v v', f u (v + v') = f u v + f u v' := by
    intro u v v'
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨y, rfl⟩ := hπ v
    obtain ⟨y', rfl⟩ := hπ v'
    rw [← hπmul, hf, hf, hf, hcr]
  let B : LinearMap.BilinForm (ZMod q) W := LinearMap.mk₂ (ZMod q) f H1
    (fun a u v => ZMod.map_smul (AddMonoidHom.mk' (fun u => f u v) fun u u' => H1 u u' v) a u)
    H3 (fun a u v => ZMod.map_smul (AddMonoidHom.mk' (f u) (H3 u)) a v)
  have hB : ∀ x y, B (π x) (π y) = c x y := hf
  refine ⟨B, hB, fun u hu => ?_, fun w => ?_⟩
  · obtain ⟨x, rfl⟩ := hπ u
    rw [hπker, Subgroup.mem_center_iff]
    intro y
    exact ((hc0 x y).mp ((hB x y).symm.trans (hu (π y)))).symm
  · obtain ⟨x, rfl⟩ := hπ w
    exact (hB x x).trans ((hc0 x x).mpr rfl)

private theorem exists_commutator_bilinForm {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    (hclass : commutator P ≤ Subgroup.center P) (hZ : Nat.card (Subgroup.center P) = q)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] (π : P → W) (hπ : Function.Surjective π)
    (hπmul : ∀ x y, π (x * y) = π x + π y) (hπker : ∀ x, π x = 0 ↔ x ∈ Subgroup.center P) :
    ∃ B : LinearMap.BilinForm (ZMod q) W, (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧
      (∀ w : W, B w w = 0) ∧ ∀ (σ : MulAut P) (T : W → W), (∀ x, T (π x) = π (σ x)) →
        ∃ k : ZMod q, ∀ u v : W, B (T u) (T v) = k * B u v := by
  obtain ⟨c, hcl, hcr, hc0, hcσ⟩ := exists_central_commutator_pairing hclass hZ
  obtain ⟨B, hB, hBnd, hBalt⟩ := exists_bilinForm_of_pairing π hπ hπmul hπker c hcl hcr hc0
  refine ⟨B, hBnd, hBalt, fun σ T hT => ?_⟩
  obtain ⟨k, hk⟩ := hcσ σ
  refine ⟨k, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := hπ u
  obtain ⟨y, rfl⟩ := hπ v
  rw [hT, hT, hB, hB]
  exact hk x y

theorem hasSmallSympModel {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {V : Type} [Group V] [Finite V]
    (hV : IsPGroup q V) (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod q) W) (_ : Module.Finite (ZMod q) W)
      (ρ : MulAut V →* (Module.End (ZMod q) W)ˣ),
      (∀ x : MulAut V, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1) ∧
      (Module.finrank (ZMod q) W ≤ 3 ∨
        (Module.finrank (ZMod q) W = 4 ∧ ∃ B : LinearMap.BilinForm (ZMod q) W,
          (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧ (∀ w : W, B w w = 0) ∧
          ∀ x : MulAut V, ∃ c : ZMod q, ∀ u v : W,
            B ((ρ x : Module.End (ZMod q) W) u) ((ρ x : Module.End (ZMod q) W) v) = c * B u v)) := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  rcases subsingleton_or_nontrivial V with hV1 | hV1
  ·
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, fun x _ => ⟨0, ?_⟩,
      Or.inl ?_⟩
    · ext v
      exact Subsingleton.elim _ _
    · exact Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le 3)
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hV
  haveI := hDchar
  have hDq : IsPGroup q D := hV.to_subgroup D
  obtain ⟨-, -, -, hEA, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDq
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hDq
  set Q := D ⧸ frattini D
  haveI : IsMulCommutative Q := hEA.toIsMulCommutative
  letI : AddCommGroup (Additive Q) := Additive.addCommGroup
  letI : Module (ZMod q) (Additive Q) := IsElementaryAbelian.isVectorSpace q
  haveI : Finite (Additive Q) := inferInstanceAs (Finite Q)
  haveI : Module.Finite (ZMod q) (Additive Q) := Module.Finite.of_finite
  let lin : MulAut Q →* Module.End (ZMod q) (Additive Q) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap q
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let ρ : MulAut V →* (Module.End (ZMod q) (Additive Q))ˣ :=
    (lin.comp ((quotientAutomorphism (frattini D)).comp (MulAut.characteristic D))).toHomUnits
  refine ⟨Additive Q, inferInstance, inferInstance, inferInstance, ρ, ?_, ?_⟩
  ·
    intro x hx
    have h1 : quotientAutomorphism (frattini D) (MulAut.characteristic D x) = 1 := by
      ext y
      exact congrArg (fun u : (Module.End (ZMod q) (Additive Q))ˣ =>
        (u : Module.End (ZMod q) (Additive Q)) (Additive.ofMul y)) hx
    obtain ⟨k, hk⟩ := hker ⟨MulAut.characteristic D x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : MulAut.characteristic D (x ^ q ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h3 : x ^ q ^ k ∈ fixingSubgroup (MulAut V) (D : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      exact congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : V)) h2
    obtain ⟨j, hj⟩ := hDfix ⟨_, h3⟩
    refine ⟨k + j, ?_⟩
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hj
  have hexp : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro c
    have hab : ⁅(a : V), (b : V)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set V) :=
      hDcomm (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _))
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hab.2 c c.2
    simpa only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] using this
  have hrD : CFSG.pRank q D ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top q D,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono hq1 le_top).trans hr
  have hfr : frattini D = commutator D := CFSG.RankThree.PartTwo.frattini_eq_commutator hDq hexp
  have hfin : Nat.card (Additive Q) = q ^ Module.finrank (ZMod q) (Additive Q) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  have hfin' : Nat.card (D ⧸ commutator D) = q ^ Module.finrank (ZMod q) (Additive Q) := by
    rw [← hfr]
    exact hfin
  have hdim : CFSG.pRank q (D ⧸ commutator D) = Module.finrank (ZMod q) (Additive Q) :=
    (CFSG.RankThree.PartTwo.quotient_commutator_rank (Fact.out : q.Prime) hexp hfin').2
  obtain ⟨h12, h3, -⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDq hexp hclass
  rcases Nat.lt_or_ge (CFSG.pRank q D) 3 with hlt | hge
  · exact Or.inl (hdim ▸ (h12 (by omega)).trans (by norm_num))
  obtain ⟨i, hi, -⟩ := h3 (le_antisymm hrD hge)
  fin_cases i
  · exact Or.inl (hdim ▸ hi.2.2.le)
  ·
    obtain ⟨-, hZ, hcz, h4⟩ := hi
    refine Or.inr ⟨hdim ▸ h4, ?_⟩
    have hΦ : frattini D = Subgroup.center D := hfr.trans hcz
    obtain ⟨B, hBnd, hBalt, hBsim⟩ := exists_commutator_bilinForm hclass hZ
      (fun x : D => Additive.ofMul (x : Q))
      (fun u => (QuotientGroup.mk_surjective (Additive.toMul u)).imp fun x hx =>
        congrArg Additive.ofMul hx)
      (fun x y => rfl)
      (fun x => by
        rw [← hΦ, ← QuotientGroup.eq_one_iff]
        exact Iff.rfl)
    exact ⟨B, hBnd, hBalt, fun x => hBsim (MulAut.characteristic D x)
      (fun u => (ρ x : Module.End (ZMod q) (Additive Q)) u) fun a => rfl⟩
  · exact Or.inl (hdim ▸ hi.2.2.2.le)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
