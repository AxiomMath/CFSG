module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aRankT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section Combinatorics

variable {f : ℕ}

@[expose] def shiftPair (f : ℕ) (c : (Fin f → Bool) × (Fin f → Bool)) :
    (Fin f → Bool) × (Fin f → Bool) :=
  (shiftBits f c.1, shiftBits f c.2)

theorem shiftPair_iterate (s : ℕ) (a b : Fin f → Bool) :
    (shiftPair f)^[s] (a, b) = ((shiftBits f)^[s] a, (shiftBits f)^[s] b) := by
  induction s generalizing a b with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (shiftBits f a) (shiftBits f b)

@[expose] def feat (p : Bool × Bool → Prop) [DecidablePred p]
    (c : (Fin f → Bool) × (Fin f → Bool)) : Finset (Fin f) :=
  Finset.univ.filter fun i => p (c.1 i, c.2 i)

theorem feat_shift (p : Bool × Bool → Prop) [DecidablePred p]
    (c : (Fin f → Bool) × (Fin f → Bool)) :
    feat p (shiftPair f c) = (feat p c).image (finRotate f) := by
  ext j
  constructor
  · intro h
    refine Finset.mem_image.mpr ⟨(finRotate f).symm j, ?_, (finRotate f).apply_symm_apply j⟩
    simpa [feat, shiftPair, shiftBits] using h
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    have hi' := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show p (c.1 ((finRotate f).symm (finRotate f i)), c.2 ((finRotate f).symm (finRotate f i)))
    rw [Equiv.symm_apply_apply]
    exact hi'

theorem feat_iterate (p : Bool × Bool → Prop) [DecidablePred p]
    (c : (Fin f → Bool) × (Fin f → Bool)) (s : ℕ) :
    feat p ((shiftPair f)^[s] c) = (feat p c).image ((finRotate f)^[s]) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', feat_shift, ih, Finset.image_image, Function.iterate_succ']

theorem card_feat_iterate (p : Bool × Bool → Prop) [DecidablePred p]
    (c : (Fin f → Bool) × (Fin f → Bool)) (s : ℕ) :
    (feat p ((shiftPair f)^[s] c)).card = (feat p c).card := by
  rw [feat_iterate]
  exact Finset.card_image_of_injective _ ((finRotate f).injective.iterate s)

@[expose] def pairOrbit (f : ℕ) (c : (Fin f → Bool) × (Fin f → Bool)) :
    Finset ((Fin f → Bool) × (Fin f → Bool)) :=
  (Finset.range f).image fun s => (shiftPair f)^[s] c

theorem orbit_cover (hf : 1 ≤ f) (p : Bool × Bool → Prop) [DecidablePred p]
    (c : (Fin f → Bool) × (Fin f → Bool)) (hne : (feat p c).Nonempty) :
    f ≤ (pairOrbit f c).card * (feat p c).card := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  have hrot1 : ∀ y : Fin (m + 1), (finRotate (m + 1) y).val = (y.val + 1) % (m + 1) := by
    intro y
    rw [coe_finRotate]
    split_ifs with h
    · subst h
      simp [Fin.val_last]
    · have : y.val < m := by
        have h1 := y.isLt
        have h2 : y.val ≠ m := fun hh => h (Fin.ext (by simpa [Fin.val_last] using hh))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]
  have hrot : ∀ (s : ℕ) (y : Fin (m + 1)),
      ((finRotate (m + 1))^[s] y).val = (y.val + s) % (m + 1) := by
    intro s
    induction s with
    | zero =>
      intro y
      simp [Nat.mod_eq_of_lt y.isLt]
    | succ s ih =>
      intro y
      rw [Function.iterate_succ_apply', hrot1, ih]
      rw [Nat.add_mod _ 1 (m + 1), Nat.mod_mod, ← Nat.add_mod, add_assoc]
  have hsub : (Finset.univ : Finset (Fin (m + 1))) ⊆
      (pairOrbit (m + 1) c).biUnion (fun c' => feat p c') := by
    intro x _
    rw [Finset.mem_biUnion]
    have hs : (x.val + (m + 1) - y₀.val) % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
    refine ⟨(shiftPair (m + 1))^[(x.val + (m + 1) - y₀.val) % (m + 1)] c, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr hs, rfl⟩
    · rw [feat_iterate]
      refine Finset.mem_image.mpr ⟨y₀, hy₀, Fin.ext ?_⟩
      rw [hrot]
      have h1 := x.isLt
      have h2 := y₀.isLt
      have : (y₀.val + (x.val + (m + 1) - y₀.val) % (m + 1)) % (m + 1) = x.val := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have e : y₀.val + (x.val + (m + 1) - y₀.val) = x.val + (m + 1) := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
      exact this
  calc m + 1 = (Finset.univ : Finset (Fin (m + 1))).card := by simp
    _ ≤ ((pairOrbit (m + 1) c).biUnion fun c' => feat p c').card := Finset.card_le_card hsub
    _ ≤ ∑ c' ∈ pairOrbit (m + 1) c, (feat p c').card := Finset.card_biUnion_le
    _ = (pairOrbit (m + 1) c).card * (feat p c).card := by
      rw [Finset.sum_congr rfl (g := fun _ => (feat p c).card)]
      · simp
      · intro c' hc'
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc'
        exact card_feat_iterate p c s

end Combinatorics

section Arith

theorem eight_mul_le_eight_pow {h : ℕ} (hh : 1 ≤ h) : 8 * h ≤ 8 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    rw [pow_succ]
    omega

theorem eight_mul_add_one_le_nine_pow {k : ℕ} (hk : 1 ≤ k) : 8 * k + 1 ≤ 9 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem four_mul_le_orbit_sum {f : ℕ} (hf : 1 ≤ f) (a b : Fin f → Bool)
    (hne : a ≠ zeros f ∨ b ≠ zeros f) (j₀ : ℕ) (h1 : (shiftBits f)^[j₀] a = b)
    (h2 : (shiftBits f)^[j₀] b = a) (rk : (Fin f → Bool) × (Fin f → Bool) → ℕ)
    (hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤ 2 * rk c + 1) :
    4 * f ≤ ∑ c ∈ pairOrbit f (a, b), rk c := by
  classical
  let c₀ : (Fin f → Bool) × (Fin f → Bool) := (a, b)
  let pH : Bool × Bool → Prop := fun x => x.1 = true ∧ x.2 = true
  let pA : Bool × Bool → Prop := fun x => x.1 = true
  let pB : Bool × Bool → Prop := fun x => x.2 = true
  let pS : Bool × Bool → Prop := fun x => x.1 ≠ x.2
  have hcntH : ∀ s : ℕ, cntH ((shiftPair f)^[s] c₀).1 ((shiftPair f)^[s] c₀).2 = cntH a b :=
    fun s => card_feat_iterate pH c₀ s
  have hcntS : ∀ s : ℕ, cntS ((shiftPair f)^[s] c₀).1 ((shiftPair f)^[s] c₀).2 = cntS a b :=
    fun s => card_feat_iterate pS c₀ s
  have hrk : ∀ c' ∈ pairOrbit f c₀, 3 ^ cntS a b * 8 ^ cntH a b ≤ 2 * rk c' + 1 := by
    intro c' hc'
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc'
    have := hdim ((shiftPair f)^[s] c₀)
    rwa [hcntS, hcntH] at this
  have hsum : ∀ B : ℕ, (∀ c' ∈ pairOrbit f c₀, B ≤ rk c') →
      (pairOrbit f c₀).card * B ≤ ∑ c ∈ pairOrbit f c₀, rk c := by
    intro B hB
    calc (pairOrbit f c₀).card * B = ∑ _c ∈ pairOrbit f c₀, B := by simp
      _ ≤ ∑ c ∈ pairOrbit f c₀, rk c := Finset.sum_le_sum hB
  by_cases hH : 0 < cntH a b
  · have hne' : (feat pH c₀).Nonempty := Finset.card_pos.mp hH
    have hcov := orbit_cover hf pH c₀ hne'
    have hcard : (feat pH c₀).card = cntH a b := rfl
    rw [hcard] at hcov
    have hb : ∀ c' ∈ pairOrbit f c₀, 4 * cntH a b ≤ rk c' := by
      intro c' hc'
      have h := hrk c' hc'
      have h8 : 8 * cntH a b ≤ 8 ^ cntH a b := eight_mul_le_eight_pow hH
      have h3 : 1 ≤ 3 ^ cntS a b := Nat.one_le_pow _ _ (by norm_num)
      have : 8 ^ cntH a b ≤ 3 ^ cntS a b * 8 ^ cntH a b := Nat.le_mul_of_pos_left _ h3
      omega
    have := hsum _ hb
    calc 4 * f ≤ 4 * ((pairOrbit f c₀).card * cntH a b) := by omega
      _ = (pairOrbit f c₀).card * (4 * cntH a b) := by ring
      _ ≤ _ := this
  · have hH0 : cntH a b = 0 := by omega
    have hdisj : ∀ i, ¬ (a i = true ∧ b i = true) := by
      intro i hi
      have : i ∈ Finset.univ.filter fun i => a i = true ∧ b i = true := by simp [hi]
      have hc : (Finset.univ.filter fun i => a i = true ∧ b i = true).card = 0 := hH0
      rw [Finset.card_eq_zero] at hc
      rw [hc] at this
      simp at this
    have hAB : (feat pA c₀).card = (feat pB c₀).card := by
      have h3 := card_feat_iterate pA c₀ j₀
      rw [shiftPair_iterate, h1, h2] at h3
      exact h3.symm
    set k := (feat pA c₀).card with hk
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      have hkb : (feat pB c₀).card = 0 := by rw [← hAB]; exact hk0'
      rw [hk, Finset.card_eq_zero] at hk0'
      rw [Finset.card_eq_zero] at hkb
      rcases hne with ha | hb'
      · apply ha
        funext i
        by_contra hi
        have hi' : a i = true := by simpa [zeros] using hi
        have : i ∈ feat pA c₀ := by simp [feat, pA, c₀, hi']
        rw [hk0'] at this
        simp at this
      · apply hb'
        funext i
        by_contra hi
        have hi' : b i = true := by simpa [zeros] using hi
        have : i ∈ feat pB c₀ := by simp [feat, pB, c₀, hi']
        rw [hkb] at this
        simp at this
    have hS : cntS a b = 2 * k := by
      have hu : (Finset.univ.filter fun i => a i ≠ b i) =
          (feat pA c₀) ∪ (feat pB c₀) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, feat, pA, pB, c₀]
        have := hdisj i
        cases ha : a i <;> cases hb' : b i <;> simp_all
      have hdj : Disjoint (feat pA c₀) (feat pB c₀) := by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        simp only [feat, pA, pB, c₀, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
        exact hdisj i ⟨hiA, hiB⟩
      show (Finset.univ.filter fun i => a i ≠ b i).card = 2 * k
      rw [hu, Finset.card_union_of_disjoint hdj, ← hAB]
      ring
    have hne' : (feat pA c₀).Nonempty := Finset.card_pos.mp (by omega)
    have hcov : f ≤ (pairOrbit f c₀).card * k := orbit_cover hf pA c₀ hne'
    have hb : ∀ c' ∈ pairOrbit f c₀, 4 * k ≤ rk c' := by
      intro c' hc'
      have h := hrk c' hc'
      rw [hS, hH0] at h
      have h9 : 8 * k + 1 ≤ 9 ^ k := eight_mul_add_one_le_nine_pow hk1
      have : 3 ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
      rw [this, pow_zero, mul_one] at h
      omega
    have := hsum _ hb
    calc 4 * f ≤ 4 * ((pairOrbit f c₀).card * k) := by omega
      _ = (pairOrbit f c₀).card * (4 * k) := by ring
      _ ≤ _ := this

end Arith

section Sum

open CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matMap dualMat MatIso)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem sum_rank_le3 (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {ι : Type} [Fintype ι]
    [DecidableEq ι] (PF : SL(3, F) →* Matrix ι ι F) (z : SL(3, F))
    (O : Finset ((Fin f → Bool) × (Fin f → Bool)))
    (hO : ∀ c ∈ O, 0 < repMultiplicity (matRep PF) (matRep (tensorRep (F := F) F c.1 c.2))) :
    ∑ c ∈ O, (tensorRep (F := F) F c.1 c.2 z - 1).rank ≤ (PF z - 1).rank := by
  classical
  have key := CFSG.QuasithinUnique.Setup.X7b.sum_repMultiplicity_mul_fixedCodim_le (k := F)
    (matRep PF) {z} (ι := ↥O) (fun t => TIdx f t.1.1 t.1.2 → F)
    (fun t => matRep (tensorRep (F := F) F t.1.1 t.1.2))
    (fun t t' h => Subtype.ext (Prod.ext
      ((tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _ h).1
      ((tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _ h).2))
  have hc : ∀ t : ↥O, Module.finrank F (TIdx f t.1.1 t.1.2 → F) -
      Module.finrank F (CFSG.QuasithinUnique.Setup.X7b.repFixedSpace
        (matRep (tensorRep (F := F) F t.1.1 t.1.2)) {z}) =
        (tensorRep (F := F) F t.1.1 t.1.2 z - 1).rank := fun t =>
    CFSG.QuasithinUnique.Setup.X7b.fixedCodim_matRep _ z
  simp only [hc] at key
  rw [CFSG.QuasithinUnique.Setup.X7b.fixedCodim_matRep PF z] at key
  refine le_trans ?_ key
  rw [← Finset.sum_coe_sort O]
  refine Finset.sum_le_sum fun t _ => ?_
  exact Nat.le_mul_of_pos_left _ (hO t t.2)

end Sum

section Model

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap dualMat dualMat_apply MatIso)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep matRepEquiv)

variable {k G : Type} [Field k] [Group G] {U : Type} [AddCommGroup U] [Module k U] {n : ℕ}

theorem toMatRep_dual (ρ : Representation k G U) (bas : Module.Basis (Fin n) k U) :
    toMatRep ρ.dual bas.dualBasis = dualMat (toMatRep ρ bas) := by
  refine MonoidHom.ext fun g => ?_
  ext a b
  simp [toMatRep, LinearMap.toMatrix_apply, dualMat_apply, Matrix.transpose_apply]

theorem exists_matIso_dual (ρ : Representation k G U) (bas : Module.Basis (Fin n) k U)
    (e : ρ.Equiv ρ.dual) :
    ∃ P Q : Matrix (Fin n) (Fin n) k,
      MatIso (toMatRep ρ bas) (dualMat (toMatRep ρ bas)) P Q := by
  obtain ⟨P, Q, h⟩ := CFSG.QuasithinUnique.Setup.X7.MatIso.exists_of_equiv
    ((matRepEquiv ρ bas).symm.trans (e.trans (matRepEquiv ρ.dual bas.dualBasis)))
  rw [toMatRep_dual] at h
  exact ⟨P, Q, h⟩

theorem invariant_dichotomy (ρ : Representation k G U) (hirr : ρ.IsIrreducible)
    (bas : Module.Basis (Fin n) k U) :
    ∀ N : Submodule k (Fin n → k),
      (∀ g, ∀ v ∈ N, (toMatRep ρ bas g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro N hN
  have h := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2
  let N' : Submodule k U := N.comap bas.equivFun.toLinearMap
  have hN' : ∀ g, ∀ u ∈ N', ρ g u ∈ N' := by
    intro g u hu
    show bas.equivFun (ρ g u) ∈ N
    have e := Representation.IntertwiningMap.isIntertwining ρ (matRep (toMatRep ρ bas))
      (matRepEquiv ρ bas).toIntertwiningMap g u
    have e' : bas.equivFun (ρ g u) = (toMatRep ρ bas g).mulVec (bas.equivFun u) := e
    rw [e']
    exact hN g _ hu
  rcases h N' hN' with h0 | h1
  · left
    rw [eq_bot_iff]
    intro y hy
    have hu : bas.equivFun.symm y ∈ N' := by
      show bas.equivFun (bas.equivFun.symm y) ∈ N
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    rw [h0, Submodule.mem_bot] at hu
    have : y = 0 := by
      have h2 := congrArg bas.equivFun hu
      rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact (Submodule.mem_bot _).mpr this
  · right
    rw [eq_top_iff]
    intro y _
    have hu : bas.equivFun.symm y ∈ N' := by rw [h1]; exact Submodule.mem_top
    have : bas.equivFun (bas.equivFun.symm y) ∈ N := hu
    rwa [LinearEquiv.apply_symm_apply] at this

end Model

section Final

open CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matMap matMap_apply dualMat dualMat_apply MatIso)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)

theorem selfDualInvolutionRank : SelfDualInvolutionRank := by
  intro f F _ _ hF hf U _ _ _ ρ hirr hnt hsd t ht1 ht2
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hNat
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  let n := Module.finrank (ZMod 2) U
  let bas : Module.Basis (Fin n) (ZMod 2) U := Module.finBasis (ZMod 2) U
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hirr₀ := invariant_dichotomy ρ hirr bas
  have hnt₀ : ∃ g, toMatRep ρ bas g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h1 => hg ?_⟩
    have h3 : LinearMap.toMatrix bas bas (ρ g) = LinearMap.toMatrix bas bas 1 := by
      rw [LinearMap.toMatrix_one]
      exact h1
    exact (LinearMap.toMatrix bas bas).injective h3
  obtain ⟨P₀, Q₀, hP₀⟩ := exists_matIso_dual ρ bas hsd.some
  have hdm : matMap φ (dualMat (toMatRep ρ bas)) = dualMat (matMap φ (toMatRep ρ bas)) := by
    refine MonoidHom.ext fun g => ?_
    simp [matMap_apply, dualMat_apply, Matrix.transpose_map]
  have hP := hP₀.map φ
  rw [hdm] at hP
  obtain ⟨a, b, hne, hmult, j₀, h1, h2⟩ := exists_orbit_label hF hf (toMatRep ρ bas) hirr₀ hnt₀ hP
  set PF := matMap φ (toMatRep ρ bas) with hPF
  have hO : ∀ c ∈ pairOrbit f (a, b), 0 < repMultiplicity (matRep PF)
      (matRep (tensorRep (F := F) F c.1 c.2)) := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    rw [shiftPair_iterate]
    exact hmult s
  have hsum := sum_rank_le3 hF hf PF t (pairOrbit f (a, b)) hO
  have hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤ 2 * (tensorRep (F := F) F c.1 c.2 t - 1).rank + 1 := by
    intro c
    have := dim_le_two_mul_rank_tensorRep (F := F) c.1 c.2
    rwa [← rank_tensorRep_involution (F := F) c.1 c.2 ht1 ht2] at this
  have h4 := four_mul_le_orbit_sum hf a b hne j₀ h1 h2
    (fun c => (tensorRep (F := F) F c.1 c.2 t - 1).rank) hdim
  have hrank : (PF t - 1).rank ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
    have e1 : PF t - 1 = (toMatRep ρ bas t - 1).map φ := by
      ext a b
      by_cases hab : a = b <;> simp [PF, matMap_apply, hab]
    have e2 : (toMatRep ρ bas t - 1).rank =
        Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
      have e3 : toMatRep ρ bas t - 1 = LinearMap.toMatrix bas bas (ρ t - 1) := by
        rw [map_sub, LinearMap.toMatrix_one]
        rfl
      rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
    rw [← e2, e1]
    exact CFSG.QuasithinUnique.Setup.X7b.rank_map_ringHom_le φ _
  exact le_trans h4 (le_trans hsum hrank)

end Final

end CFSG.QuasithinUnique.Setup.X7a
