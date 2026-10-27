module

public import CFSG.Certificates.Kernel.Sp6Insp443.CentSound
public import CFSG.Certificates.Kernel.Sp6Insp443.SixSound

public section

namespace CFSG.KS.Sp6I

open CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {Γ : Type*} [Group Γ]

theorem of_mem_closure_finite [Finite Γ] {Q : Γ → Prop} (h1 : Q 1)
    (hmul : ∀ x y, Q x → Q y → Q (x * y)) {S₀ : Set Γ} (hS : ∀ x ∈ S₀, Q x) {g : Γ}
    (hg : g ∈ Subgroup.closure S₀) : Q g := by
  have hpow : ∀ x, Q x → ∀ m : Nat, Q (x ^ m) := by
    intro x hx m
    induction m with
    | zero => rw [pow_zero]; exact h1
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih hx
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx =>
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel (orderOf_pos x),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow x hx _

theorem mem_map_conj_inv_iff {g x : Γ} {K : Subgroup Γ} :
    x ∈ K.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

@[expose] def FanoP (A : Subgroup Γ) (K H : Nat → Subgroup Γ) (g : Γ) : Prop :=
  A.map (MulAut.conj g).toMonoidHom = A ∧ ∀ p, 0 < p → p < 8 → ∃ q, 0 < q ∧ q < 8 ∧
    (K p).map (MulAut.conj g).toMonoidHom = K q ∧ (H p).map (MulAut.conj g).toMonoidHom = H q

theorem fanoP_one {A : Subgroup Γ} {K H : Nat → Subgroup Γ} : FanoP A K H 1 :=
  ⟨map_conj_one A, fun p hp hp8 => ⟨p, hp, hp8, map_conj_one _, map_conj_one _⟩⟩

theorem fanoP_mul {A : Subgroup Γ} {K H : Nat → Subgroup Γ} {x y : Γ} (hx : FanoP A K H x)
    (hy : FanoP A K H y) : FanoP A K H (x * y) := by
  refine ⟨by rw [map_conj_mul', hy.1, hx.1], fun p hp hp8 => ?_⟩
  obtain ⟨q, hq, hq8, hk, hh⟩ := hy.2 p hp hp8
  obtain ⟨r, hr, hr8, hk', hh'⟩ := hx.2 q hq hq8
  exact ⟨r, hr, hr8, by rw [map_conj_mul', hk, hk'], by rw [map_conj_mul', hh, hh']⟩

theorem bool_eq_of_iff_false {b c : Bool} (h : b = false ↔ c = false) : b = c := by
  cases b <;> cases c <;> simp_all

theorem mtp_eq {d0 d1 d2 p q : Nat} (hq : q < 8)
    (h0 : dot3 d0 p = dot3 (Nat.shiftLeft 1 0) q) (h1 : dot3 d1 p = dot3 (Nat.shiftLeft 1 1) q)
    (h2 : dot3 d2 p = dot3 (Nat.shiftLeft 1 2) q) : mtp d0 d1 d2 p = q := by
  unfold mtp
  rw [h0, h1, h2]
  interval_cases q <;> rfl

variable {n : Nat}

theorem rep_getD_of_forall₂ {k : Nat} {Ts : List Table} {x : Nat → Equiv.Perm (Fin n)}
    (h : List.Forall₂ (Rep n) Ts (List.ofFn fun i : Fin k => x i)) :
    ∀ j < Ts.length, Rep n (Ts.getD j #[]) (x j) := by
  intro j hj
  rw [List.forall₂_iff_get] at h
  have hl : Ts.length = k := by simpa using h.1
  have := h.2 j hj (by simpa [hl] using hj)
  rw [List.getD_eq_getElem _ _ hj]
  simpa using this

theorem rep_spanTabs (hn : n < 2 ^ 32) {k : Nat} {Ts : List Table} {x : Nat → Equiv.Perm (Fin n)}
    (h : List.Forall₂ (Rep n) Ts (List.ofFn fun i : Fin k => x i)) {d : Nat} (hd : d < 2 ^ k) :
    Rep n ((spanTabs n Ts).getD d #[]) (mprod x d k) := by
  have hl : Ts.length = k := by simpa using h.length_eq
  have e : (spanTabs n Ts).getD d #[] = maskProd n Ts d := by
    unfold spanTabs
    rw [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map, List.getElem_range]
  rw [e, ← hl]
  exact maskProd_rep hn (rep_getD_of_forall₂ h) d

theorem fanoTestS_false_of_gens (hn : n < 2 ^ 32) {x a : Nat → Equiv.Perm (Fin n)}
    {ws as : List Table} {rows : List Nat}
    (hws : List.Forall₂ (Rep n) ws (List.ofFn fun i : Fin 6 => x i))
    (has : List.Forall₂ (Rep n) as (List.ofFn fun i : Fin 3 => a i))
    (hasq : ∀ i < 3, a i * a i = 1) (hac : ∀ i < 3, ∀ j < 3, Commute (a i) (a j))
    {K H : Nat → Subgroup (Equiv.Perm (Fin n))} {H₀ : Subgroup (Equiv.Perm (Fin n))}
    {S₀ : Set (Equiv.Perm (Fin n))}
    (hS : ∀ y ∈ S₀, FanoP (Subgroup.closure (Set.range fun i : Fin 3 => a i)) K H y)
    (hK : ∀ g ∈ H₀, (∀ i, ∃ c, g * (fun i : Fin 6 => x i) i * g⁻¹ =
      eElt (fun i : Fin 6 => x i) c) → g ∈ Subgroup.closure S₀)
    (hKa : ∀ i < 3, ∀ p, 0 < p → p < 8 → (a i ∈ K p ↔ dot3 (Nat.shiftLeft 1 i) p = false))
    (hKd : ∀ d < 8, ∀ p, 0 < p → p < 8 → (mprod a d 3 ∈ K p ↔ dot3 d p = false))
    (hHw : ∀ j < 6, ∀ p, 0 < p → p < 8 → (x j ∈ H p ↔ (rows.getD j 0).testBit p = false))
    (hHm : ∀ m < 64, ∀ p, 0 < p → p < 8 → (mprod x m 6 ∈ H p ↔ bsum rows m p = false))
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H₀) {T : Table} (hT : Rep n T g) :
    fanoTestS n ws (spanTabs n ws) as (spanTabs n as) rows T = false := by
  have hwl : ws.length = 6 := by simpa using hws.length_eq
  have hal : as.length = 3 := by simpa using has.length_eq
  have hwr := rep_getD_of_forall₂ hws
  have har := rep_getD_of_forall₂ has
  have hlenA : (spanTabs n as).length = 8 := by simp [spanTabs, hal]
  have hlenW : (spanTabs n ws).length = 64 := by simp [spanTabs, hwl]
  unfold fanoTestS
  rw [Bool.and_eq_false_iff]
  by_cases hN : conjIn n ws (spanTabs n ws) T = true
  · right
    have hN' : ∀ i, ∃ c, g * (fun i : Fin 6 => x i) i * g⁻¹ = eElt (fun i : Fin 6 => x i) c := by
      rw [conjIn_spanTabs, conjSpanIn_iff hn hws hws hT] at hN
      exact hN
    have hgc := hK g hg hN'
    have hPi := of_mem_closure_finite fanoP_one (fun _ _ => fanoP_mul) hS
      ((Subgroup.closure S₀).inv_mem hgc)
    have hP := of_mem_closure_finite fanoP_one (fun _ _ => fanoP_mul) hS hgc
    rw [Bool.or_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false']
    refine ⟨?_, ?_⟩
    · rw [conjIn_spanTabs, conjSpanIn_iff hn has has hT]
      intro i
      have hm : g * a i * g⁻¹ ∈ Subgroup.closure (Set.range fun i : Fin 3 => a i) := by
        rw [← hP.1]
        exact ⟨a i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
      obtain ⟨c, hc⟩ := exists_eElt_of_mem_closure (fun i => hasq i i.2)
        (fun i j => hac i i.2 j j.2) hm
      exact ⟨c, hc.symm⟩
    · unfold fanoEqOK
      rw [hlenA, hwl, hlenW, allIn_eq_true]
      intro d0 _ hd0
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases c0 : compEqN n T (as.getD 0 #[]) ((spanTabs n as).getD d0 #[]) = true
      swap
      · exact Or.inl (Bool.eq_false_iff.2 c0)
      right
      rw [allIn_eq_true]
      intro d1 _ hd1
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases c1 : compEqN n T (as.getD 1 #[]) ((spanTabs n as).getD d1 #[]) = true
      swap
      · exact Or.inl (Bool.eq_false_iff.2 c1)
      right
      rw [allIn_eq_true]
      intro d2 _ hd2
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases c2 : compEqN n T (as.getD 2 #[]) ((spanTabs n as).getD d2 #[]) = true
      swap
      · exact Or.inl (Bool.eq_false_iff.2 c2)
      right
      rw [allIn_eq_true]
      intro j _ hj
      rw [allIn_eq_true]
      intro m _ hm
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases cm : compEqN n T (ws.getD j #[]) ((spanTabs n ws).getD m #[]) = true
      swap
      · exact Or.inl (Bool.eq_false_iff.2 cm)
      right
      rw [allIn_eq_true]
      intro p hp1 hp8
      have hp : 0 < p := by omega
      obtain ⟨q, hq, hq8, hkq, hhq⟩ := hPi.2 p hp hp8
      have hconj : ∀ {b : Table} {u y : Equiv.Perm (Fin n)} {U : Table}, Rep n b u → Rep n U y →
          compEqN n T b U = true → g * u * g⁻¹ = y := by
        intro b u y U hb hU h
        have := (compEq_iff hT hb hU).1 h
        rw [this, mul_inv_cancel_right]
      have hbit : ∀ i < 3, ∀ {d : Nat}, d < 8 → g * a i * g⁻¹ = mprod a d 3 →
          dot3 d p = dot3 (Nat.shiftLeft 1 i) q := by
        intro i hi d hd he
        refine bool_eq_of_iff_false ?_
        rw [← hKd d hd p hp hp8, ← hKa i hi q hq hq8, ← hkq, mem_map_conj_inv_iff, he]
      have e0 := hconj (har 0 (by omega)) (rep_spanTabs hn has hd0) c0
      have e1 := hconj (har 1 (by omega)) (rep_spanTabs hn has hd1) c1
      have e2 := hconj (har 2 (by omega)) (rep_spanTabs hn has hd2) c2
      have em := hconj (hwr j (by omega)) (rep_spanTabs hn hws hm) cm
      have hmtp := mtp_eq hq8 (hbit 0 (by norm_num) hd0 e0) (hbit 1 (by norm_num) hd1 e1)
        (hbit 2 (by norm_num) hd2 e2)
      have hrow : bsum rows m p = (rows.getD j 0).testBit q := by
        refine bool_eq_of_iff_false ?_
        rw [← hHm m hm p hp hp8, ← hHw j hj q hq hq8, ← hhq, mem_map_conj_inv_iff, em]
      rw [hmtp, hrow, beq_self_eq_true]
  · left
    exact Bool.eq_false_iff.mpr hN

end CFSG.KS.Sp6I

end
