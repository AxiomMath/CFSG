module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Span.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreCharacteristic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4

public section

namespace CFSG

open scoped Pointwise commutatorElement

universe u v w

private def defectHom {N : Type u} {S : Type w} [Group N] [Group S] [MulDistribMulAction S N]
    (A : Subgroup N) (hSA : ∀ (s : S) (a : N), a ∈ A → s • a = a)
    (hSN : ∀ (s : S) (n : N), n⁻¹ * (s • n) ∈ A) : S →* (N → A) where
  toFun s m := ⟨m⁻¹ * (s • m), hSN s m⟩
  map_one' := by
    funext m
    apply Subtype.ext
    show m⁻¹ * ((1 : S) • m) = 1
    rw [one_smul, inv_mul_cancel]
  map_mul' s t := by
    funext m
    apply Subtype.ext
    show m⁻¹ * ((s * t) • m) = m⁻¹ * (s • m) * (m⁻¹ * (t • m))
    have h2 : s • (m⁻¹ * (t • m)) = m⁻¹ * (t • m) := hSA s _ (hSN t m)
    calc m⁻¹ * ((s * t) • m) = m⁻¹ * (s • (m * (m⁻¹ * (t • m)))) := by
          rw [mul_smul, mul_inv_cancel_left]
      _ = m⁻¹ * (s • m) * (m⁻¹ * (t • m)) := by
          rw [smul_mul', h2, mul_assoc]

theorem smul_eq_self_of_perfect_of_trivial_on_abelian {N : Type u} {S : Type w} [Group N] [Group S]
    [MulDistribMulAction S N] [Group.IsPerfect S] (A : Subgroup N)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hSA : ∀ (s : S) (a : N), a ∈ A → s • a = a)
    (hSN : ∀ (s : S) (n : N), n⁻¹ * (s • n) ∈ A) (s : S) (n : N) : s • n = n := by
  have hS : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  let δ : S →* (N → A) := defectHom A hSA hSN
  have hker : ⁅(⊤ : Subgroup S), ⊤⁆ ≤ δ.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    funext m
    apply Subtype.ext
    exact hA _ (δ x m).2 _ (δ y m).2
  have hs' : s ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := by
    rw [hS]
    exact Subgroup.mem_top s
  have hs : δ s = 1 := hker hs'
  have h : n⁻¹ * (s • n) = 1 := congrArg (fun f => ((f n : A) : N)) hs
  exact (inv_mul_eq_one.mp h).symm

theorem smul_eq_self_of_pGroup_of_trivial_on_subgroup {N : Type u} {S : Type w} [Group N] [Finite N]
    [Group S] [MulDistribMulAction S N] {p : ℕ} (hp : p.Prime) (hSp : IsPGroup p S)
    (hpN : ¬ p ∣ Nat.card N) (A : Subgroup N) (hSA : ∀ (s : S) (a : N), a ∈ A → s • a = a)
    (hSN : ∀ (s : S) (n : N), n⁻¹ * (s • n) ∈ A) (s : S) (n : N) : s • n = n := by
  let δ : S →* (N → A) := defectHom A hSA hSN
  obtain ⟨k, hk⟩ := hSp s
  have h1 : δ s ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h2 : δ s ^ Nat.card N = 1 := by
    funext m
    apply Subtype.ext
    show ((δ s m : A) : N) ^ Nat.card N = 1
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
  have hs : δ s = 1 := by
    have h : δ s ^ Nat.gcd (p ^ k) (Nat.card N) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  have h : n⁻¹ * (s • n) = 1 := congrArg (fun f => ((f n : A) : N)) hs
  exact (inv_mul_eq_one.mp h).symm

theorem smul_eq_self_of_perfect_or_pGroup_of_fixedPoints {N : Type u} {Q : Type v} {S : Type w}
    [Group N] [Finite N] [Group Q] [Group S]
    [MulDistribMulAction Q N] [MulDistribMulAction S N] [SMulCommClass Q S N]
    (hS : Group.IsPerfect S ∨ ∃ p : ℕ, p.Prime ∧ IsPGroup p S ∧ ¬ p ∣ Nat.card N)
    (hN : Group.IsSolvable N) (hNodd : Odd (Nat.card N)) (T : Subgroup Q) [Finite T]
    (hTN : Nat.Coprime (Nat.card T) (Nat.card N))
    (hgen : ∀ (V : Type u) [Group V] [Finite V] [MulDistribMulAction Q V] (r : ℕ), r.Prime →
      IsElementaryAbelian r V → Odd (Nat.card V) → Nat.Coprime (Nat.card T) (Nat.card V) →
        Subgroup.closure (⋃ g : Q, (fun v => g • v) '' {v : V | ∀ t ∈ T, (t : Q) • v = v}) = ⊤)
    (hfix : ∀ n : N, (∀ t ∈ T, (t : Q) • n = n) → ∀ s : S, s • n = n) :
    ∀ (s : S) (n : N), s • n = n := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ (N' : Type u) [Group N'] [Finite N'] [MulDistribMulAction Q N'] [MulDistribMulAction S N']
      [SMulCommClass Q S N'], Nat.card N' = k → Nat.card N' ∣ Nat.card N →
        Group.IsSolvable N' → Odd (Nat.card N') → Nat.Coprime (Nat.card T) (Nat.card N') →
          (∀ n : N', (∀ t ∈ T, (t : Q) • n = n) → ∀ s : S, s • n = n) →
            ∀ (s : S) (n : N'), s • n = n
  have hP : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih N' _ _ _ _ _ hk hdvd hsol hodd hcop hfix' s n
    by_cases hnt : Nontrivial N'
    swap
    · have : Subsingleton N' := not_nontrivial_iff_subsingleton.mp hnt
      exact Subsingleton.elim _ _
    have : Group.IsSolvable N' := hsol
    obtain ⟨A, r, hAchar, hAne, hr, hAel⟩ :=
      ComponentClassification.CatalogueBHeldSmallCore.exists_characteristic_elementaryAbelian N'
    have : A.Characteristic := hAchar
    have hQA : IsInvariant Q N' A := isInvariant_of_characteristic (A := Q) A
    have hSA : IsInvariant S N' A := isInvariant_of_characteristic (A := S) A
    have hAtriv : ∀ (s : S) (a : N'), a ∈ A → s • a = a := by
      have hcardA : Nat.card A ∣ Nat.card N' := Subgroup.card_subgroup_dvd_card A
      have hgenA := hgen A r hr hAel (hodd.of_dvd_nat hcardA) (hcop.coprime_dvd_right hcardA)
      let F : Subgroup A :=
        { carrier := {a | ∀ s : S, s • (a : N') = a}
          mul_mem' := fun {a b} ha hb s => by
            show s • ((a : N') * b) = a * b
            rw [smul_mul', ha s, hb s]
          one_mem' := fun s => smul_one s
          inv_mem' := fun {a} ha s => by
            show s • ((a : N')⁻¹) = (a : N')⁻¹
            rw [smul_inv', ha s] }
      have hF : F = ⊤ := by
        rw [eq_top_iff, ← hgenA, Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hx
        obtain ⟨g, c, hc, rfl⟩ := hx
        intro s'
        have hc' : ∀ t ∈ T, (t : Q) • (c : N') = c := fun t ht => congrArg Subtype.val (hc t ht)
        show s' • (g • (c : N')) = g • (c : N')
        rw [← smul_comm g s' (c : N'), hfix' (c : N') hc' s']
      intro s a ha
      have hmem : (⟨a, ha⟩ : A) ∈ F := hF ▸ Subgroup.mem_top _
      exact hmem s
    let : MulDistribMulAction Q (N' ⧸ A) := quotientMulDistribMulAction (A := Q) (G := N') A hQA
    let : MulDistribMulAction S (N' ⧸ A) := quotientMulDistribMulAction (A := S) (G := N') A hSA
    have hmkQ : ∀ (g : Q) (m : N'), g • (m : N' ⧸ A) = ((g • m : N') : N' ⧸ A) := fun _ _ => rfl
    have hmkS : ∀ (x : S) (m : N'), x • (m : N' ⧸ A) = ((x • m : N') : N' ⧸ A) := fun _ _ => rfl
    have : SMulCommClass Q S (N' ⧸ A) := ⟨fun g x y => by
      induction y using QuotientGroup.induction_on with
      | H m => rw [hmkS, hmkQ, hmkQ, hmkS, smul_comm]⟩
    have hcardq : Nat.card (N' ⧸ A) ∣ Nat.card N' := Subgroup.card_quotient_dvd_card A
    have hlt : Nat.card (N' ⧸ A) < k := by
      have hA1 : 1 < Nat.card A := by
        have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
        exact Finite.one_lt_card
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup A
      have hpos : 0 < Nat.card (N' ⧸ A) := Nat.card_pos
      rw [← hk, hprod]
      exact lt_mul_of_one_lt_right hpos hA1
    have hfixq : ∀ x : N' ⧸ A, (∀ t ∈ T, (t : Q) • x = x) → ∀ s : S, s • x = x := by
      let : MulDistribMulAction T N' := MulDistribMulAction.compHom N' T.subtype
      have hTA : IsInvariant T N' A := ⟨fun t m => hQA.invariant (t : Q) m⟩
      let : MulDistribMulAction T (N' ⧸ A) := quotientMulDistribMulAction (A := T) (G := N') A hTA
      have hquot : fixedPointSubgroup T (N' ⧸ A) =
          (fixedPointSubgroup T N').map (QuotientGroup.mk' A) :=
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime (G := N') (A := T) hsol hcop A hTA
      intro x hx s'
      have hxT : x ∈ fixedPointSubgroup T (N' ⧸ A) := by
        intro t
        induction x using QuotientGroup.induction_on with
        | H m =>
          have h := hx t t.2
          exact h
      rw [hquot] at hxT
      obtain ⟨m, hm, rfl⟩ := hxT
      have hm' : ∀ t ∈ T, (t : Q) • m = m := fun t ht => hm ⟨t, ht⟩
      show s' • ((m : N') : N' ⧸ A) = ((m : N') : N' ⧸ A)
      rw [hmkS, hfix' m hm' s']
    have htrivq := ih _ hlt (N' ⧸ A) rfl (hcardq.trans hdvd) inferInstance
      (hodd.of_dvd_nat hcardq) (hcop.coprime_dvd_right hcardq) hfixq
    have hcos : ∀ (x : S) (m : N'), m⁻¹ * (x • m) ∈ A := by
      intro x m
      have h := htrivq x (m : N' ⧸ A)
      rw [hmkS] at h
      exact QuotientGroup.eq.mp h.symm
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h := hAel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
      exact congrArg Subtype.val h
    rcases hS with hperf | ⟨p, hp, hSp, hpN⟩
    · exact smul_eq_self_of_perfect_of_trivial_on_abelian A hAcomm hAtriv hcos s n
    · exact smul_eq_self_of_pGroup_of_trivial_on_subgroup hp hSp (fun h => hpN (h.trans hdvd)) A
        hAtriv hcos s n
  exact hP _ N rfl dvd_rfl hN hNodd hTN hfix

theorem closure_translates_fixedPoints_eq_top_of_zmod {Q : Type v} [Group Q] (T : Subgroup Q)
    (hadd : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → Nat.Coprime (Nat.card T) r →
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod r) W] [Finite W] [DistribMulAction Q W],
        Submodule.span (ZMod r) (⋃ g : Q, (fun w => g • w) '' {w : W | ∀ t ∈ T, (t : Q) • w = w}) =
          ⊤)
    (V : Type u) [Group V] [Finite V] [MulDistribMulAction Q V] (r : ℕ) (hr : r.Prime)
    (hV : IsElementaryAbelian r V) (hVo : Odd (Nat.card V))
    (hVc : Nat.Coprime (Nat.card T) (Nat.card V)) :
    Subgroup.closure (⋃ g : Q, (fun v => g • v) '' {v : V | ∀ t ∈ T, (t : Q) • v = v}) = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  by_cases hnt : Nontrivial V
  swap
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 1]
    exact one_mem _
  have hrV : r ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup r V).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
    rw [hk]
    exact dvd_pow_self r hk0
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hVo) (even_iff_two_dvd.mpr hrV)
  have hTr : Nat.Coprime (Nat.card T) r := hVc.coprime_dvd_right hrV
  let : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => hV.toIsMulCommutative.is_comm.comm a b }
  have hexp : ∀ x : Additive V, r • x = 0 := by
    intro x
    show Additive.ofMul ((Additive.toMul x) ^ r) = Additive.ofMul 1
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p r V)]
  let : Module (ZMod r) (Additive V) := AddCommGroup.zmodModule (n := r) hexp
  let : DistribMulAction Q (Additive V) :=
    { smul := fun g w => Additive.ofMul (g • Additive.toMul w)
      one_smul := fun w => by
        show Additive.ofMul ((1 : Q) • Additive.toMul w) = w
        rw [one_smul]
        rfl
      mul_smul := fun g h w => by
        show Additive.ofMul ((g * h) • Additive.toMul w) =
          Additive.ofMul (g • (h • Additive.toMul w))
        rw [mul_smul]
      smul_zero := fun g => by
        show Additive.ofMul (g • (1 : V)) = Additive.ofMul 1
        rw [smul_one]
      smul_add := fun g w w' => by
        show Additive.ofMul (g • (Additive.toMul w * Additive.toMul w')) =
          Additive.ofMul (g • Additive.toMul w * g • Additive.toMul w')
        rw [smul_mul'] }
  have hspan := hadd r hr2 hTr (Additive V)
  set H := Subgroup.closure (⋃ g : Q, (fun v => g • v) '' {v : V | ∀ t ∈ T, (t : Q) • v = v})
  let H' : Submodule (ZMod r) (Additive V) :=
    AddSubgroup.toZModSubmodule (n := r) (Subgroup.toAddSubgroup H)
  have hsub : (⋃ g : Q, (fun w : Additive V => g • w) ''
      {w : Additive V | ∀ t ∈ T, (t : Q) • w = w}) ⊆ (H' : Set (Additive V)) := by
    intro w hw
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hw
    obtain ⟨g, c, hc, rfl⟩ := hw
    show g • Additive.toMul c ∈ H
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨g, Additive.toMul c, fun t ht => congrArg Additive.toMul (hc t ht), rfl⟩
  have htop : (⊤ : Submodule (ZMod r) (Additive V)) ≤ H' :=
    hspan.symm.le.trans (Submodule.span_le.mpr hsub)
  rw [eq_top_iff]
  intro v _
  exact htop (Submodule.mem_top (x := Additive.ofMul v))

end CFSG

end
