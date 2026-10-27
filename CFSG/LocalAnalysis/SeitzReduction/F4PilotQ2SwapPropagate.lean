module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2Diagonal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn TwistOn signConj)

variable {G : Type*} [Group G] {t : G}

section Lft

variable {D : Subgroup G} (P : SwapParam t D)

theorem swapParam_lft_mul {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    P.lft (x * y) = P.lft x * P.lft y := by
  rw [P.lft_of_mem (D.mul_mem hx hy), P.lft_of_mem hx, P.lft_of_mem hy, ← map_mul]
  congr 1
  ext <;> simp

theorem swapParam_lft_one : P.lft 1 = 1 := by
  rw [P.lft_of_mem D.one_mem]
  exact map_one P.Ψ

theorem swapParam_lft_inv {x : G} (hx : x ∈ D) : P.lft x⁻¹ = (P.lft x)⁻¹ := by
  rw [P.lft_of_mem (D.inv_mem hx), P.lft_of_mem hx, ← map_inv]
  congr 1
  ext <;> simp

theorem swapParam_lft_pow {x : G} (hx : x ∈ D) (n : ℕ) : P.lft (x ^ n) = P.lft x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, swapParam_lft_one]
  | succ n ih => rw [pow_succ, pow_succ, swapParam_lft_mul P (D.pow_mem hx n) hx, ih]

theorem swapParam_lft_commute_of_commute {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x * y = y * x) : P.lft x * y = y * P.lft x := by
  have hdy : P.Ψ (⟨y, hy⟩, ⟨y, hy⟩) = y := P.diag ⟨y, hy⟩
  rw [P.lft_of_mem hx, ← hdy, ← map_mul, ← map_mul]
  congr 1
  ext
  · exact hxy
  · simp

theorem swapParam_lft_mem_range {x : G} : P.lft x ∈ P.Ψ.range := by
  by_cases hx : x ∈ D
  · rw [P.lft_of_mem hx]
    exact ⟨_, rfl⟩
  · rw [P.lft_of_not_mem hx]
    exact P.Ψ.range.one_mem

end Lft

section Propagation

variable {DX DY : Subgroup G} (PX : SwapParam t DX) (PY : SwapParam t DY)

theorem lft_eq_lft_of_overlapCentralizer {X Y X'' Y'' O : Subgroup G}
    (hrX : PX.Ψ.range = centralizerPerfectCore X) (hrY : PY.Ψ.range = centralizerPerfectCore Y)
    (hX'' : X'' ≤ DX) (hY'' : Y'' ≤ DY) (hT : X ⊔ X'' ≤ Y ⊔ Y'')
    (hOX : O ≤ DX) (hOY : O ≤ DY) (hagree : AgreeOn PX PY O)
    {u : G} (huX : u ∈ DX) (huY : u ∈ DY) (huX'' : ∀ x ∈ X'', u * x = x * u)
    (huY'' : ∀ y ∈ Y'', u * y = y * u) (huO : ∀ o ∈ O, u * o * u⁻¹ ∈ O)
    (hM : ∀ c : G, c ∈ centralizer (X : Set G) → c ∈ centralizer (X'' : Set G) →
      (∀ o ∈ O, c * PX.lft o = PX.lft o * c) →
      (∀ o ∈ O, c * (t * PX.lft o * t⁻¹) = (t * PX.lft o * t⁻¹) * c) →
      Odd (orderOf c) ∧ PX.lft u * c = c * PX.lft u)
    {k : ℕ} (hu : u ^ 2 ^ k = 1) :
    PY.lft u = PX.lft u := by
  have hbY : ∀ y ∈ Y, y * PY.lft u = PY.lft u * y := by
    intro y hy
    have hbE : PY.lft u ∈ centralizerPerfectCore Y := hrY ▸ swapParam_lft_mem_range PY
    exact mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer Y hbE) y hy
  have hbY'' : ∀ y ∈ Y'', y * PY.lft u = PY.lft u * y := fun y hy =>
    (swapParam_lft_commute_of_commute PY huY (hY'' hy) (huY'' y hy)).symm
  have hbT : Y ⊔ Y'' ≤ centralizer ({PY.lft u} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hbY y hy))
      (fun y hy => mem_centralizer_singleton_iff.2 (hbY'' y hy))
  have hbX : PY.lft u ∈ centralizer (X : Set G) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hbT (hT (mem_sup_left hx)))
  have hbX'' : PY.lft u ∈ centralizer (X'' : Set G) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hbT (hT (mem_sup_right hx)))
  have haX : PX.lft u ∈ centralizer (X : Set G) := by
    have haE : PX.lft u ∈ centralizerPerfectCore X := hrX ▸ swapParam_lft_mem_range PX
    exact centralizerPerfectCore_le_centralizer X haE
  have haX'' : PX.lft u ∈ centralizer (X'' : Set G) := mem_centralizer_iff.2 fun x hx =>
    (swapParam_lft_commute_of_commute PX huX (hX'' hx) (huX'' x hx)).symm
  have hconj : ∀ o ∈ O, PY.lft u * PX.lft o * (PY.lft u)⁻¹ =
      PX.lft u * PX.lft o * (PX.lft u)⁻¹ := by
    intro o ho
    have h1 := hagree (u * o * u⁻¹) (huO o ho)
    rw [swapParam_lft_mul PY (DY.mul_mem huY (hOY ho)) (DY.inv_mem huY),
      swapParam_lft_mul PY huY (hOY ho), swapParam_lft_inv PY huY,
      swapParam_lft_mul PX (DX.mul_mem huX (hOX ho)) (DX.inv_mem huX),
      swapParam_lft_mul PX huX (hOX ho), swapParam_lft_inv PX huX, hagree o ho] at h1
    exact h1
  set c : G := (PX.lft u)⁻¹ * PY.lft u with hc
  have hcX : c ∈ centralizer (X : Set G) := mul_mem (inv_mem haX) hbX
  have hcX'' : c ∈ centralizer (X'' : Set G) := mul_mem (inv_mem haX'') hbX''
  have hcO : ∀ o ∈ O, c * PX.lft o = PX.lft o * c := by
    intro o ho
    calc c * PX.lft o = (PX.lft u)⁻¹ * (PY.lft u * PX.lft o * (PY.lft u)⁻¹) * PY.lft u := by
          rw [hc]; group
      _ = (PX.lft u)⁻¹ * (PX.lft u * PX.lft o * (PX.lft u)⁻¹) * PY.lft u := by rw [hconj o ho]
      _ = PX.lft o * c := by rw [hc]; group
  have hcO' : ∀ o ∈ O, c * (t * PX.lft o * t⁻¹) = (t * PX.lft o * t⁻¹) * c := by
    intro o ho
    have ha' := PX.commute_lft_conj_lft u o
    have hb' := PY.commute_lft_conj_lft u o
    rw [hagree o ho] at hb'
    exact (ha'.inv_left.mul_left hb').eq
  obtain ⟨hodd, hac⟩ := hM c hcX hcX'' hcO hcO'
  have hbac : PY.lft u = PX.lft u * c := by rw [hc, mul_inv_cancel_left]
  have hapow : PX.lft u ^ 2 ^ k = 1 := by
    rw [← swapParam_lft_pow PX huX, hu, swapParam_lft_one]
  have hbpow : PY.lft u ^ 2 ^ k = 1 := by
    rw [← swapParam_lft_pow PY huY, hu, swapParam_lft_one]
  have hcpow : c ^ 2 ^ k = 1 := by
    have h1 := hbpow
    rw [hbac, (Commute.mul_pow hac (2 ^ k)), hapow, one_mul] at h1
    exact h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hcpow)
  have hc1 : c = 1 := by
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    · exfalso
      rw [hj] at hodd
      exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩)
  rw [hbac, hc1, mul_one]

end Propagation

section Closure

variable {DX DY : Subgroup G} {PX : SwapParam t DX} {PY : SwapParam t DY}

theorem agreeOn_closure {S : Set G} (hS : ∀ x ∈ S, x ∈ DX ∧ x ∈ DY)
    (h : ∀ x ∈ S, PY.lft x = PX.lft x) : AgreeOn PX PY (closure S) := by
  have hle : closure S ≤ DX ⊓ DY := (closure_le _).2 fun x hx => ⟨(hS x hx).1, (hS x hx).2⟩
  intro x hx
  induction hx using closure_induction with
  | mem x hx => exact h x hx
  | one => rw [swapParam_lft_one, swapParam_lft_one]
  | mul x y hx hy ihx ihy =>
    rw [swapParam_lft_mul PY (hle hx).2 (hle hy).2, swapParam_lft_mul PX (hle hx).1 (hle hy).1,
      ihx, ihy]
  | inv x hx ihx =>
    rw [swapParam_lft_inv PY (hle hx).2, swapParam_lft_inv PX (hle hx).1, ihx]

end Closure

section Signs

variable {D D' D'' : Subgroup G}

theorem swapParam_flip_range' (P : SwapParam t D) : P.flip.Ψ.range = P.Ψ.range := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(b, a), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(b, a), rfl⟩

theorem twistOn_trans (ht2 : t * t = 1) {s s' : ℤˣ} {P : SwapParam t D} {P' : SwapParam t D'}
    {P'' : SwapParam t D''} {O : Subgroup G} (h : TwistOn s P P' O) (h' : TwistOn s' P' P'' O) :
    TwistOn (s' * s) P P'' O := fun x hx => by
  rw [h' x hx, h x hx, SeitzQ2.signConj_mul ht2]

theorem swapParam_lft_injOn (P : SwapParam t D) (hinj : Function.Injective P.Ψ) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) (h : P.lft x = P.lft y) : x = y := by
  rw [P.lft_of_mem hx, P.lft_of_mem hy] at h
  exact congrArg Subtype.val (congrArg Prod.fst (hinj h))

theorem commute_signConj_lft (P : SwapParam t D) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a * b = b * a) (s s' : ℤˣ) :
    Commute (signConj t s (P.lft a)) (signConj t s' (P.lft b)) := by
  have h0 : Commute (P.lft a) (P.lft b) := by
    change P.lft a * P.lft b = P.lft b * P.lft a
    rw [← swapParam_lft_mul P ha hb, ← swapParam_lft_mul P hb ha, hab]
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · simpa only [SeitzQ2.signConj_one] using h0
  · simpa only [SeitzQ2.signConj_one, SeitzQ2.signConj_neg_one] using P.commute_lft_conj_lft a b
  · simpa only [SeitzQ2.signConj_one, SeitzQ2.signConj_neg_one] using
      (P.commute_lft_conj_lft b a).symm
  · simp only [SeitzQ2.signConj_neg_one]
    change t * P.lft a * t⁻¹ * (t * P.lft b * t⁻¹) = t * P.lft b * t⁻¹ * (t * P.lft a * t⁻¹)
    calc t * P.lft a * t⁻¹ * (t * P.lft b * t⁻¹) = t * (P.lft a * P.lft b) * t⁻¹ := by group
      _ = t * (P.lft b * P.lft a) * t⁻¹ := by rw [h0.eq]
      _ = t * P.lft b * t⁻¹ * (t * P.lft a * t⁻¹) := by group

theorem eq_of_twistOn_of_not_commute {s s' : ℤˣ} {P : SwapParam t D} {P' : SwapParam t D'}
    (hinj : Function.Injective P'.Ψ) {A B : Subgroup G} (hA : TwistOn s P P' A)
    (hB : TwistOn s' P P' B) {a b : G} (haA : a ∈ A) (hbB : b ∈ B) (ha : a ∈ D') (hb : b ∈ D')
    (hab : a * b ≠ b * a) : s = s' := by
  by_contra hss
  have hc : Commute (P'.lft a) (P'.lft b) := by
    rw [hA a haA, hB b hbB]
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
    · exact absurd rfl hss
    · simpa only [SeitzQ2.signConj_one, SeitzQ2.signConj_neg_one] using P.commute_lft_conj_lft a b
    · simpa only [SeitzQ2.signConj_one, SeitzQ2.signConj_neg_one] using
        (P.commute_lft_conj_lft b a).symm
    · exact absurd rfl hss
  apply hab
  refine swapParam_lft_injOn P' hinj (D'.mul_mem ha hb) (D'.mul_mem hb ha) ?_
  rw [swapParam_lft_mul P' ha hb, swapParam_lft_mul P' hb ha, hc.eq]

theorem commute_lft_of_twistOn (ht2 : t * t = 1) {s s' : ℤˣ} (R : SwapParam t D)
    {P : SwapParam t D'} {Q : SwapParam t D''} {A B : Subgroup G} (hP : TwistOn s R P A)
    (hQ : TwistOn s' R Q B) {a b : G} (haA : a ∈ A) (hbB : b ∈ B) (ha : a ∈ D) (hb : b ∈ D)
    (hab : a * b = b * a) :
    Commute (P.lft a) (Q.lft b) ∧ Commute (P.lft a) (t * Q.lft b * t⁻¹) := by
  rw [hP a haA, hQ b hbB]
  refine ⟨commute_signConj_lft R ha hb hab s s', ?_⟩
  have e : t * signConj t s' (R.lft b) * t⁻¹ = signConj t (-1 * s') (R.lft b) := by
    rw [SeitzQ2.signConj_mul ht2, SeitzQ2.signConj_neg_one]
  rw [e]
  exact commute_signConj_lft R ha hb hab s _

end Signs

section Edge

open CFSG.Quasithin (perfectCore perfectCore_le)

variable [Finite G] {DX DY : Subgroup G}

theorem overlap_eq_of_sup_eq (PX : SwapParam t DX) (PY : SwapParam t DY)
    (hinjX : Function.Injective PX.Ψ) (hinjY : Function.Injective PY.Ψ)
    {X Y X'' Y'' : Subgroup G} (hrX : PX.Ψ.range = centralizerPerfectCore X)
    (hrY : PY.Ψ.range = centralizerPerfectCore Y) (hX'' : X'' ≤ DX) (hY'' : Y'' ≤ DY)
    (hT : X ⊔ X'' = Y ⊔ Y'') :
    perfectCore (DY ⊓ centralizer (Y'' : Set G)) =
      perfectCore (DX ⊓ centralizer (X'' : Set G)) := by
  rw [PX.perfectCore_inf_centralizer_eq hinjX hrX hX'',
    PY.perfectCore_inf_centralizer_eq hinjY hrY hY'', hT]

theorem agreeOn_or_flipOn_of_sup_eq (PX : SwapParam t DX) (PY : SwapParam t DY)
    (hinjX : Function.Injective PX.Ψ) (hinjY : Function.Injective PY.Ψ)
    {X Y X'' Y'' : Subgroup G} (hrX : PX.Ψ.range = centralizerPerfectCore X)
    (hrY : PY.Ψ.range = centralizerPerfectCore Y) (hX'' : X'' ≤ DX) (hY'' : Y'' ≤ DY)
    (hT : X ⊔ X'' = Y ⊔ Y'')
    [IsSimpleGroup (perfectCore (DX ⊓ centralizer (X'' : Set G)))]
    (hZ : center (perfectCore (DX ⊓ centralizer (X'' : Set G))) = ⊥) :
    AgreeOn PX PY (perfectCore (DX ⊓ centralizer (X'' : Set G))) ∨
      FlipOn PX PY (perfectCore (DX ⊓ centralizer (X'' : Set G))) := by
  have hO := overlap_eq_of_sup_eq PX PY hinjX hinjY hrX hrY hX'' hY'' hT
  have hOX : perfectCore (DX ⊓ centralizer (X'' : Set G)) ≤ DX :=
    (perfectCore_le _).trans inf_le_left
  have hOY : perfectCore (DX ⊓ centralizer (X'' : Set G)) ≤ DY :=
    hO ▸ (perfectCore_le _).trans inf_le_left
  refine SeitzQ2.agreeOn_or_flipOn_of_map_prod_eq PX PY hOX hOY hZ ?_
  have h1 := PX.centralizerPerfectCore_sup_eq hinjX hrX hX''
  have h2 := PY.centralizerPerfectCore_sup_eq hinjY hrY hY''
  rw [← hT, hO] at h2
  rw [← h1, ← h2]

theorem exists_twistOn_of_edge (ht2 : t * t = 1) (PX : SwapParam t DX) (PY : SwapParam t DY)
    (hinjX : Function.Injective PX.Ψ) (hinjY : Function.Injective PY.Ψ)
    {X Y X'' Y'' : Subgroup G} (hrX : PX.Ψ.range = centralizerPerfectCore X)
    (hrY : PY.Ψ.range = centralizerPerfectCore Y) (hX'' : X'' ≤ DX) (hY'' : Y'' ≤ DY)
    (hT : X ⊔ X'' = Y ⊔ Y'')
    [IsSimpleGroup (perfectCore (DX ⊓ centralizer (X'' : Set G)))]
    (hZ : center (perfectCore (DX ⊓ centralizer (X'' : Set G))) = ⊥) (S : Set G)
    (hS : ∀ u ∈ S, u ∈ DX ∧ u ∈ DY ∧ (∀ x ∈ X'', u * x = x * u) ∧ (∀ y ∈ Y'', u * y = y * u) ∧
      (∀ o ∈ perfectCore (DX ⊓ centralizer (X'' : Set G)),
        u * o * u⁻¹ ∈ perfectCore (DX ⊓ centralizer (X'' : Set G))) ∧ ∃ k : ℕ, u ^ 2 ^ k = 1)
    (hM : ∀ u ∈ S, ∀ c : G, c ∈ centralizer (X : Set G) → c ∈ centralizer (X'' : Set G) →
      (∀ o ∈ perfectCore (DX ⊓ centralizer (X'' : Set G)), c * PX.lft o = PX.lft o * c) →
      (∀ o ∈ perfectCore (DX ⊓ centralizer (X'' : Set G)),
        c * (t * PX.lft o * t⁻¹) = (t * PX.lft o * t⁻¹) * c) →
      Odd (orderOf c) ∧ PX.lft u * c = c * PX.lft u) :
    ∃ s : ℤˣ, TwistOn s PX PY (closure S) := by
  set O := perfectCore (DX ⊓ centralizer (X'' : Set G)) with hOdef
  have hO := overlap_eq_of_sup_eq PX PY hinjX hinjY hrX hrY hX'' hY'' hT
  have hOX : O ≤ DX := (perfectCore_le _).trans inf_le_left
  have hOY : O ≤ DY := by
    rw [hOdef, ← hO]
    exact (perfectCore_le _).trans inf_le_left
  have hSD : ∀ x ∈ S, x ∈ DX ∧ x ∈ DY := fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩
  have hprop : ∀ (Q : SwapParam t DY), Q.Ψ.range = centralizerPerfectCore Y → AgreeOn PX Q O →
      AgreeOn PX Q (closure S) := by
    intro Q hrQ hQ
    refine agreeOn_closure hSD fun u hu => ?_
    obtain ⟨huX, huY, huX'', huY'', huO, k, hk⟩ := hS u hu
    exact lft_eq_lft_of_overlapCentralizer PX Q hrX hrQ hX'' hY'' hT.le hOX hOY hQ huX huY huX''
      huY'' huO (hM u hu) hk
  rcases agreeOn_or_flipOn_of_sup_eq PX PY hinjX hinjY hrX hrY hX'' hY'' hT hZ with hA | hF
  · exact ⟨1, SeitzQ2.twistOn_one_iff.2 (hprop PY hrY hA)⟩
  · have hA' : AgreeOn PX PY.flip O := (SeitzQ2.agreeOn_flip_iff ht2).2 hF
    have h := hprop PY.flip ((swapParam_flip_range' PY).trans hrY) hA'
    refine ⟨-1, SeitzQ2.twistOn_neg_one_iff.2 ((SeitzQ2.agreeOn_flip_iff ht2).1 h)⟩

end Edge

end CFSG.SeitzReduction.F4Pilot
