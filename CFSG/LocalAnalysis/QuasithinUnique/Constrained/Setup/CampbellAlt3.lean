module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.QuasithinUnique

@[expose] def permAct (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => w (σ⁻¹ i)

@[expose] def e0 : Fin 3 → ZMod 2 := ![1, 1, 0]

theorem permAct_mul (σ τ : Equiv.Perm (Fin 3)) (w : Fin 3 → ZMod 2) :
    permAct (σ * τ) w = permAct σ (permAct τ w) := by
  funext i
  simp [permAct, mul_inv_rev]

theorem permAct_one (w : Fin 3 → ZMod 2) : permAct 1 w = w := by
  funext i
  simp [permAct]

theorem permAct_inv_apply (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → ZMod 2) :
    permAct σ⁻¹ (permAct σ w) = w := by
  rw [← permAct_mul, inv_mul_cancel, permAct_one]

theorem permAct_zero (σ : Equiv.Perm (Fin 3)) : permAct σ 0 = 0 := by
  funext i; rfl

theorem permAct_add (σ : Equiv.Perm (Fin 3)) (w w' : Fin 3 → ZMod 2) :
    permAct σ (w + w') = permAct σ w + permAct σ w' := by
  funext i
  simp [permAct]

theorem mem_evenWeight_iff {m : ℕ} {w : Fin m → ZMod 2} : w ∈ evenWeight m ↔ ∑ i, w i = 0 := by
  simp [evenWeight, AddMonoidHom.mem_ker]

theorem key_fact : ∀ σ : alternatingGroup (Fin 3), σ ≠ 1 →
    permAct σ e0 ≠ e0 ∧ (∑ i, permAct σ e0 i = 0) ∧
      permAct σ (permAct σ e0) = e0 + permAct σ e0 ∧
      ∀ w : Fin 3 → ZMod 2, ∑ i, w i = 0 →
        w = 0 ∨ w = e0 ∨ w = permAct σ e0 ∨ w = e0 + permAct σ e0 := by
  decide

theorem e0_mem : e0 ∈ evenWeight 3 := by
  rw [mem_evenWeight_iff]; decide

theorem e0_ne_zero : e0 ≠ 0 := by decide

theorem klein_hom_exists {X : Type*} [Group X] (Q : Subgroup X) {u v : X} (hu : u ∈ Q) (hv : v ∈ Q)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hcomm : u * v = v * u)
    (hlist : ∀ x ∈ Q, x = 1 ∨ x = u ∨ x = v ∨ x = u * v)
    {M : Type*} [AddGroup M] (hcommM : ∀ a b : M, a + b = b + a) (m n : M) (hm2 : m + m = 0)
    (hn2 : n + n = 0) :
    ∃ f : Q →* Multiplicative M, f ⟨u, hu⟩ = Multiplicative.ofAdd m ∧
      f ⟨v, hv⟩ = Multiplicative.ofAdd n := by
  classical
  have huv1 : u * v ≠ 1 := by
    intro h
    apply huv
    have h1 : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    rw [h1, h2]
  have huv_u : u * v ≠ u := by
    intro h; apply hv1; simpa using h
  have huv_v : u * v ≠ v := by
    intro h; apply hu1; simpa using h
  have e1 : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have e2 : v * (u * v) = u := by rw [hcomm, ← mul_assoc, hv2, one_mul]
  have e3 : u * v * u = v := by rw [mul_assoc, ← hcomm, ← mul_assoc, hu2, one_mul]
  have e4 : u * v * v = u := by rw [mul_assoc, hv2, mul_one]
  have e5 : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = (u * v * u) * v := (mul_assoc (u * v) u v).symm
      _ = v * v := by rw [e3]
      _ = 1 := hv2
  have e6 : v * u = u * v := hcomm.symm
  have f1 : m + (m + n) = n := by rw [← add_assoc, hm2, zero_add]
  have f2 : n + (m + n) = m := by rw [hcommM m n, ← add_assoc, hn2, zero_add]
  have f3 : m + n + m = n := by rw [hcommM m n, add_assoc, hm2, add_zero]
  have f4 : m + n + n = m := by rw [add_assoc, hn2, add_zero]
  have f5 : m + n + (m + n) = 0 := by rw [← add_assoc, f3, hn2]
  have f6 : n + m = m + n := hcommM n m
  let g : X → M := fun x => if x = 1 then 0 else if x = u then m else if x = v then n else m + n
  have hg : ∀ x ∈ Q, ∀ y ∈ Q, g (x * y) = g x + g y := by
    intro x hx y hy
    rcases hlist x hx with h | h | h | h <;> rcases hlist y hy with h' | h' | h' | h' <;>
      simp only [h, h', g] <;> simp [hu2, hv2, e1, e2, e3, e4, e5, e6, huv1, huv_u, huv_v, hu1,
        hv1, huv.symm, hm2, hn2, f1, f2, f3, f4, f5, f6]
  refine ⟨MonoidHom.mk' (fun x : Q => Multiplicative.ofAdd (g (x : X))) (fun x y => ?_), ?_, ?_⟩
  · show Multiplicative.ofAdd (g ((x : X) * (y : X))) = _
    rw [hg x x.2 y y.2]
    rfl
  · simp [g, hu1]
  · simp [g, hv1, huv.symm]

open scoped commutatorElement

theorem klein_mul_mem {X : Type*} [Group X] {u v : X} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hcomm : u * v = v * u) {x y : X} (hx : x = 1 ∨ x = u ∨ x = v ∨ x = u * v)
    (hy : y = 1 ∨ y = u ∨ y = v ∨ y = u * v) :
    x * y = 1 ∨ x * y = u ∨ x * y = v ∨ x * y = u * v := by
  have e1 : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have e2 : v * (u * v) = u := by rw [hcomm, ← mul_assoc, hv2, one_mul]
  have e3 : u * v * u = v := by rw [mul_assoc, ← hcomm, ← mul_assoc, hu2, one_mul]
  have e4 : u * v * v = u := by rw [mul_assoc, hv2, mul_one]
  have e5 : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = (u * v * u) * v := (mul_assoc (u * v) u v).symm
      _ = v * v := by rw [e3]
      _ = 1 := hv2
  have e6 : v * u = u * v := hcomm.symm
  rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> simp only [h, h'] <;>
    simp [hu2, hv2, e1, e2, e3, e4, e5, e6]

theorem alt3_klein_data {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    {c : X} (hc3 : orderOf c = 3) (hQc : Q ⊔ zpowers c = ⊤)
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hexpQ : ∀ x ∈ Q, x ^ 2 = 1)
    (hkey : ∀ z ∈ Q, c * z * c⁻¹ = z → z = 1)
    (hirr : ∀ W : Subgroup X, W ≤ Q → W.Normal → W = ⊥ ∨ W = Q) (hQne : Q ≠ ⊥) :
    ∃ u v : X, u ∈ Q ∧ v ∈ Q ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧
      u * v = v * u ∧ v = c * u * c⁻¹ ∧ c * v * c⁻¹ = u * v ∧
      (∀ x ∈ Q, x = 1 ∨ x = u ∨ x = v ∨ x = u * v) := by
  classical
  have hc3' : c * c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc3] at h
    rw [← pow_two, ← pow_succ]; exact h
  have hQn : Q.Normal := inferInstance
  obtain ⟨⟨u, hu⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  set v : X := c * u * c⁻¹ with hvdef
  have hvQ : v ∈ Q := hQn.conj_mem u hu c
  have hu2 : u * u = 1 := by simpa [pow_two] using hexpQ u hu
  have hv2 : v * v = 1 := by simpa [pow_two] using hexpQ v hvQ
  have huv : u ≠ v := by
    intro h
    exact hu1 (hkey u hu h.symm)
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    have : c * u * c⁻¹ = 1 := h
    simpa using this
  have hcomm : u * v = v * u := hab u hu v hvQ
  have hcv : c * v * c⁻¹ = u * v := by
    set p : X := u * v * (c * v * c⁻¹) with hp
    have hpQ : p ∈ Q := mul_mem (mul_mem hu hvQ) (hQn.conj_mem v hvQ c)
    have hc2 : c * (c * v * c⁻¹) * c⁻¹ = u := by
      have : c * (c * v * c⁻¹) * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ := by
        rw [hvdef]; group
      rw [this, hc3']; simp
    have hpc : c * p * c⁻¹ = p := by
      have hcu : c * u * c⁻¹ = v := hvdef.symm
      have : c * p * c⁻¹ = (c * u * c⁻¹) * (c * v * c⁻¹) * (c * (c * v * c⁻¹) * c⁻¹) := by
        rw [hp]; group
      rw [this, hcu, hc2]
      have hcvQ : c * v * c⁻¹ ∈ Q := hQn.conj_mem v hvQ c
      calc v * (c * v * c⁻¹) * u = u * v * (c * v * c⁻¹) := by
            rw [hab (v * (c * v * c⁻¹)) (mul_mem hvQ hcvQ) u hu, ← mul_assoc]
        _ = p := rfl
    have hp1 : p = 1 := hkey p hpQ hpc
    have hcvQ : c * v * c⁻¹ ∈ Q := hQn.conj_mem v hvQ c
    have h2 : u * v * (c * v * c⁻¹) = 1 := hp1
    have h3 : (u * v) * (u * v) = 1 := by
      calc (u * v) * (u * v) = (u * (v * u)) * v := by group
        _ = (u * (u * v)) * v := by rw [← hcomm]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [hu2, hv2, one_mul]
    rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  refine ⟨u, v, hu, hvQ, hu1, hv1, huv, hu2, hv2, hcomm, hvdef, hcv, ?_⟩
  set W : Subgroup X := Subgroup.closure {u, v} with hW
  have huW : u ∈ W := Subgroup.subset_closure (Set.mem_insert _ _)
  have hvW : v ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hWQ : W ≤ Q := by
    rw [hW, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hvQ
  have hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hvW
      · rw [hcv]; exact mul_mem huW hvW
    | one => simp
    | mul x y _ _ hx hy =>
      have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx
  have hWnormal : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hQc]
    refine sup_le ?_ ?_
    · intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have hq' : ∀ w' ∈ W, q * w' * q⁻¹ = w' := fun w' hw' => by
        rw [hab q hq w' (hWQ hw'), mul_inv_cancel_right]
      constructor
      · intro hw; rw [hq' w hw]; exact hw
      · intro hw
        have hwQ' : q * w * q⁻¹ ∈ Q := hWQ hw
        have hwQ : w ∈ Q := by
          have := hQn.conj_mem _ hwQ' q⁻¹
          simpa [mul_assoc] using this
        rw [hab q hq w hwQ, mul_inv_cancel_right] at hw
        exact hw
    · rw [zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact hWc w
      · intro hw
        have h2 := hWc _ (hWc _ hw)
        have : c * (c * (c * w * c⁻¹) * c⁻¹) * c⁻¹ = w := by
          calc c * (c * (c * w * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * w * (c * c * c)⁻¹ := by group
            _ = w := by rw [hc3']; simp
        rwa [this] at h2
  have hWne : W ≠ ⊥ := fun h => hu1 (Subgroup.mem_bot.mp (h ▸ huW))
  have hWQ' : W = Q := (hirr W hWQ hWnormal).resolve_left hWne
  have hlist : ∀ x ∈ W, x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · simp
      · simp
    | one => simp
    | mul x y _ _ hx hy => exact klein_mul_mem hu2 hv2 hcomm hx hy
    | inv x _ hx =>
      have e3' : u * v * u = v := by rw [mul_assoc, ← hcomm, ← mul_assoc, hu2, one_mul]
      have e5 : u * v * (u * v) = 1 := by
        calc u * v * (u * v) = (u * v * u) * v := (mul_assoc (u * v) u v).symm
          _ = v * v := by rw [e3']
          _ = 1 := hv2
      have hx2 : x * x = 1 := by
        rcases hx with h | h | h | h
        · rw [h, one_mul]
        · rw [h]; exact hu2
        · rw [h]; exact hv2
        · rw [h]; exact e5
      have : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      rw [this]; exact hx
  intro x hx
  exact hlist x (hWQ' ▸ hx)

theorem card_klein {X : Type*} [Group X] (Q : Subgroup X) {u v : X} (hu : u ∈ Q) (hv : v ∈ Q)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hv2 : v * v = 1)
    (hlist : ∀ x ∈ Q, x = 1 ∨ x = u ∨ x = v ∨ x = u * v) : Nat.card Q = 4 := by
  classical
  have huv1 : u * v ≠ 1 := by
    intro h
    apply huv
    have h1 : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    rw [h1, h2]
  have huv_u : u * v ≠ u := by
    intro h; apply hv1; simpa using h
  have huv_v : u * v ≠ v := by
    intro h; apply hu1; simpa using h
  have hset : (Q : Set X) = ↑({1, u, v, u * v} : Finset X) := by
    ext x
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hx; exact hlist x hx
    · rintro (h | h | h | h) <;> rw [h]
      · exact one_mem _
      · exact hu
      · exact hv
      · exact mul_mem hu hv
  have hcardS : ({1, u, v, u * v} : Finset X).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using huv_v.symm.symm
    · simp [huv, huv_u.symm]
    · simp [hu1.symm, hv1.symm, huv1.symm]
  have : Nat.card Q = (Q : Set X).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, hcardS]

theorem alt3_of_irreducible {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hcard : Nat.card X = 3 * Nat.card Q)
    (hUQ : ⁅Q, (⊤ : Subgroup X)⁆ ≤ Q)
    (hcomm : ∀ q ∈ Q, ∀ u ∈ ⁅Q, (⊤ : Subgroup X)⁆, q * u = u * q)
    (hexp : ∀ x ∈ ⁅Q, (⊤ : Subgroup X)⁆, x ^ 2 = 1)
    (hno2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hne : ⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X < ⁅Q, (⊤ : Subgroup X)⁆)
    (hirr : ∀ W : Subgroup X, ⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X ≤ W → W ≤ ⁅Q, (⊤ : Subgroup X)⁆ →
      W.Normal → W = ⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X ∨ W = ⁅Q, (⊤ : Subgroup X)⁆) :
    Q = ⁅Q, (⊤ : Subgroup X)⁆ ∧ Nat.card Q = 4 ∧ Nat.card X = 12 ∧ center X = ⊥ ∧
      Nonempty (X ≃* alternatingGroup (Fin 4)) ∧
      ∃ (α : X →* alternatingGroup (Fin 3)) (β : Q →* Multiplicative (evenWeight 3)),
        Function.Surjective α ∧ α.ker = Q ∧ Function.Surjective β ∧ β.ker = ⊥ ∧
        ∀ (ℓ : X) (x y : Q), (y : X) = ℓ * x * ℓ⁻¹ →
          ((Multiplicative.toAdd (β y) : evenWeight 3) : Fin 3 → ZMod 2) =
            permAct (α ℓ : Equiv.Perm (Fin 3))
              ((Multiplicative.toAdd (β x) : evenWeight 3) : Fin 3 → ZMod 2) := by
  classical
  obtain ⟨c, hc3, hcQ, hQc⟩ := Alt3Core.alt3_step1 Q hQ2 hcard
  have hQU : Q ≤ ⁅Q, (⊤ : Subgroup X)⁆ :=
    Alt3Core.alt3_lemmaP Q hQ2 hc3 hQc hno2 _ hUQ
      (fun q hq => Subgroup.commutator_mem_commutator hq (Subgroup.mem_top c))
  have hEq : Q = ⁅Q, (⊤ : Subgroup X)⁆ := le_antisymm hQU hUQ
  have hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hcomm a ha b (hEq ▸ hb)
  have hexpQ : ∀ x ∈ Q, x ^ 2 = 1 := fun x hx => hexp x (hEq ▸ hx)
  have hkey : ∀ z ∈ Q, c * z * c⁻¹ = z → z = 1 := fun z hz hzc =>
    Alt3Core.alt3_key Q hQ2 hc3 hQc hno2 hab hexpQ hz hzc
  have hZbot : (⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzU, hzc⟩
    have hzQ : z ∈ Q := hEq ▸ hzU
    have h1 : c * z * c⁻¹ = z := by
      have := Subgroup.mem_center_iff.mp hzc c
      rw [this]; group
    rw [hkey z hzQ h1]; exact one_mem _
  have hQne : Q ≠ ⊥ := by
    intro hQ
    rw [hZbot, ← hEq] at hne
    exact lt_irrefl _ (hQ ▸ hne)
  have hirr' : ∀ W : Subgroup X, W ≤ Q → W.Normal → W = ⊥ ∨ W = Q := by
    intro W hWQ hWn
    have := hirr W (by rw [hZbot]; exact bot_le) (hEq ▸ hWQ) hWn
    rw [hZbot, ← hEq] at this
    exact this
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, hcomm', hvdef, hcv, hlist⟩ :=
    alt3_klein_data Q hc3 hQc hab hexpQ hkey hirr' hQne
  have hQ4 : Nat.card Q = 4 := card_klein Q hu hv hu1 hv1 huv hv2 hlist
  have hZ : Nat.card (⁅Q, (⊤ : Subgroup X)⁆ : Subgroup X) =
      4 * Nat.card (⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X : Subgroup X) := by
    rw [hZbot, Subgroup.card_bot, mul_one, ← hEq]; exact hQ4
  obtain ⟨-, -, hcard12, hcenter, -⟩ := Alt3Core.alt3_core Q hQ2 hcard hUQ hcomm hexp hno2 hZ
  refine ⟨hEq, hQ4, hcard12, hcenter, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSyl : Nat.card (Sylow 3 X) = 4 := by
    have hmod := card_sylow_modEq_one 3 X
    have hzc : Nat.card (zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
    have hidx : (zpowers c).index = 4 := by
      have := Subgroup.card_mul_index (zpowers c)
      rw [hzc, hcard12] at this
      omega
    have hzp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (p := 3) (n := 1) (by rw [hzc]; simp)
    let P : Sylow 3 X := hzp.toSylow (by rw [hidx]; omega)
    have hPc : (P : Subgroup X) = zpowers c := rfl
    have hdvd : Nat.card (Sylow 3 X) ∣ 4 := by
      have := Sylow.card_dvd_index P
      rwa [hPc, hidx] at this
    have hle : Nat.card (Sylow 3 X) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 X) := Nat.card_pos
    have hn1 : Nat.card (Sylow 3 X) ≠ 1 := by
      intro h1
      have hsub : Subsingleton (Sylow 3 X) := (Nat.card_eq_one_iff_unique.mp h1).1
      have hPn : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
      have hcP : c ∈ (P : Subgroup X) := by rw [hPc]; exact mem_zpowers c
      have hu0 : u ∈ Q := hu
      have hx : c * u * c⁻¹ * u⁻¹ ∈ (P : Subgroup X) := by
        have h2 : u * c⁻¹ * u⁻¹ ∈ (P : Subgroup X) := hPn.conj_mem c⁻¹ (inv_mem hcP) u
        have : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
        rw [this]; exact mul_mem hcP h2
      have hxQ : c * u * c⁻¹ * u⁻¹ ∈ Q := mul_mem (‹Q.Normal›.conj_mem u hu0 c) (inv_mem hu0)
      have hx3 : (c * u * c⁻¹ * u⁻¹) ^ 3 = 1 := by
        have := hPn
        have hxz : c * u * c⁻¹ * u⁻¹ ∈ zpowers c := by rw [← hPc]; exact hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        have hc3z : c ^ ((3 : ℕ) : ℤ) = 1 := by
          rw [zpow_natCast, ← hc3]; exact pow_orderOf_eq_one c
        rw [hc3z, one_zpow]
      have hx2 : (c * u * c⁻¹ * u⁻¹) ^ 2 = 1 := hexpQ _ hxQ
      have hx1 : c * u * c⁻¹ * u⁻¹ = 1 := by
        have : c * u * c⁻¹ * u⁻¹ = (c * u * c⁻¹ * u⁻¹) ^ 3 * ((c * u * c⁻¹ * u⁻¹) ^ 2)⁻¹ := by group
        rw [this, hx3, hx2]; simp
      have hfix : c * u * c⁻¹ = u := by
        have := mul_inv_eq_one.mp hx1
        exact this
      exact hu1 (hkey u hu0 hfix)
    have hn2 : Nat.card (Sylow 3 X) ≠ 2 := by
      intro h2
      rw [h2] at hmod
      exact absurd hmod (by decide)
    have hn3 : Nat.card (Sylow 3 X) ≠ 3 := by
      intro h3
      rw [h3] at hdvd
      omega
    omega
  have hA4 := CFSG.Glauberman.Dickson.huppert_II_8_17_b_order_twelve_four_sylow_three hcard12 hSyl
  refine ⟨hA4, ?_⟩
  have hX3 : Nat.card (X ⧸ Q) = 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    rw [hcard12, hQ4] at this
    omega
  have hA3card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  let θ : X ⧸ Q ≃* alternatingGroup (Fin 3) := mulEquivOfPrimeCardEq (p := 3) hX3 hA3card
  let α : X →* alternatingGroup (Fin 3) := θ.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hαs : Function.Surjective α := θ.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hαk : α.ker = Q := by
    ext x
    rw [MonoidHom.mem_ker]
    show θ (QuotientGroup.mk x) = 1 ↔ x ∈ Q
    rw [← map_one θ, θ.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hσ : α c ≠ 1 := fun h => hcQ (hαk ▸ (MonoidHom.mem_ker.mpr h))
  obtain ⟨hk1, hk2, hk3, hk4⟩ := key_fact (α c) hσ
  set σ : alternatingGroup (Fin 3) := α c with hσdef
  let m : evenWeight 3 := ⟨e0, e0_mem⟩
  let n : evenWeight 3 := ⟨permAct σ e0, mem_evenWeight_iff.mpr hk2⟩
  have hvec2 : ∀ w : Fin 3 → ZMod 2, w + w = 0 := by
    intro w; funext i
    have : (2 : ZMod 2) = 0 := by decide
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← two_mul, this, zero_mul]
  have hm2 : m + m = 0 := Subtype.ext (hvec2 e0)
  have hn2 : n + n = 0 := Subtype.ext (hvec2 (permAct σ e0))
  have hcommM : ∀ a b : evenWeight 3, a + b = b + a := fun a b => Subtype.ext (add_comm _ _)
  obtain ⟨f, hfu, hfv⟩ :=
    klein_hom_exists Q hu hv hu1 hv1 huv hu2 hv2 hcomm' hlist hcommM m n hm2 hn2
  have hfuv : f ⟨u * v, mul_mem hu hv⟩ = Multiplicative.ofAdd (m + n) := by
    have : (⟨u * v, mul_mem hu hv⟩ : Q) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [this, map_mul, hfu, hfv]; rfl
  have hf1 : f 1 = 1 := map_one f
  have hmn : m ≠ n := fun h => hk1 (congrArg Subtype.val h).symm
  have hm0 : m ≠ 0 := fun h => e0_ne_zero (congrArg Subtype.val h)
  have hn0 : n ≠ 0 := by
    intro h
    apply e0_ne_zero
    have hn' : permAct (σ : Equiv.Perm (Fin 3)) e0 = 0 := congrArg Subtype.val h
    have := permAct_inv_apply (σ : Equiv.Perm (Fin 3)) e0
    rw [hn'] at this
    rw [← this]
    funext i; rfl
  have hmn0 : m + n ≠ 0 := by
    intro h
    apply hmn
    calc m = m + (n + n) := by rw [hn2, add_zero]
      _ = (m + n) + n := (add_assoc _ _ _).symm
      _ = n := by rw [h, zero_add]
  have hval : ∀ x : Q, ((Multiplicative.toAdd (f x) : evenWeight 3) = 0 ∧ x = 1) ∨
      ((Multiplicative.toAdd (f x) : evenWeight 3) = m ∧ x = ⟨u, hu⟩) ∨
      ((Multiplicative.toAdd (f x) : evenWeight 3) = n ∧ x = ⟨v, hv⟩) ∨
      ((Multiplicative.toAdd (f x) : evenWeight 3) = m + n ∧ x = ⟨u * v, mul_mem hu hv⟩) := by
    intro x
    rcases hlist x x.2 with h | h | h | h
    · left
      have : x = 1 := Subtype.ext h
      rw [this, hf1]; exact ⟨rfl, rfl⟩
    · right; left
      have : x = ⟨u, hu⟩ := Subtype.ext h
      rw [this, hfu]; exact ⟨rfl, rfl⟩
    · right; right; left
      have : x = ⟨v, hv⟩ := Subtype.ext h
      rw [this, hfv]; exact ⟨rfl, rfl⟩
    · right; right; right
      have : x = ⟨u * v, mul_mem hu hv⟩ := Subtype.ext h
      rw [this, hfuv]; exact ⟨rfl, rfl⟩
  have hfs : Function.Surjective f := by
    intro w
    have hw := hk4 w.1 (mem_evenWeight_iff.mp w.2)
    rcases hw with h | h | h | h
    · exact ⟨1, by rw [hf1]; exact (congrArg Multiplicative.ofAdd (Subtype.ext h)).symm⟩
    · exact ⟨⟨u, hu⟩, by rw [hfu]; exact (congrArg Multiplicative.ofAdd (Subtype.ext h)).symm⟩
    · exact ⟨⟨v, hv⟩, by rw [hfv]; exact (congrArg Multiplicative.ofAdd (Subtype.ext h)).symm⟩
    · exact ⟨⟨u * v, mul_mem hu hv⟩, by
        rw [hfuv]; exact (congrArg Multiplicative.ofAdd (Subtype.ext h)).symm⟩
  have hfk : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx1 : Multiplicative.toAdd (f x) = (0 : evenWeight 3) := by
      have : f x = 1 := MonoidHom.mem_ker.mp hx
      rw [this]; rfl
    rcases hval x with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (h.symm.trans hx1) hm0
    · exact absurd (h.symm.trans hx1) hn0
    · exact absurd (h.symm.trans hx1) hmn0
  have hcu : c * u * c⁻¹ = v := hvdef.symm
  have hceq : ∀ x y : Q, (y : X) = c * x * c⁻¹ →
      ((Multiplicative.toAdd (f y) : evenWeight 3) : Fin 3 → ZMod 2) =
        permAct (σ : Equiv.Perm (Fin 3))
          ((Multiplicative.toAdd (f x) : evenWeight 3) : Fin 3 → ZMod 2) := by
    intro x y hy
    rcases hval x with ⟨hx0, hx⟩ | ⟨hxm, hx⟩ | ⟨hxn, hx⟩ | ⟨hxmn, hx⟩
    · have hy1 : y = 1 := Subtype.ext (by rw [hy, hx]; simp)
      rw [hy1, hf1, hx0]
      show (0 : Fin 3 → ZMod 2) = permAct _ 0
      rw [permAct_zero]
    · have hy1 : y = ⟨v, hv⟩ := Subtype.ext (by rw [hy, hx]; exact hcu)
      rw [hy1, hfv, hxm]
      rfl
    · have hy1 : y = ⟨u * v, mul_mem hu hv⟩ := Subtype.ext (by rw [hy, hx]; exact hcv)
      rw [hy1, hfuv, hxn]
      show e0 + permAct (σ : Equiv.Perm (Fin 3)) e0 = permAct (σ : Equiv.Perm (Fin 3)) (permAct (σ : Equiv.Perm (Fin 3)) e0)
      exact hk3.symm
    · have hcuv : c * (u * v) * c⁻¹ = u := by
        have : c * (u * v) * c⁻¹ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
        rw [this, hcu, hcv, hcomm', ← mul_assoc, hv2, one_mul]
      have hy1 : y = ⟨u, hu⟩ := Subtype.ext (by rw [hy, hx]; exact hcuv)
      rw [hy1, hfu, hxmn]
      show e0 = permAct (σ : Equiv.Perm (Fin 3)) (e0 + permAct (σ : Equiv.Perm (Fin 3)) e0)
      rw [permAct_add, hk3]
      funext i
      simp only [Pi.add_apply]
      have h2 : ∀ a b : ZMod 2, a = b + (a + b) := by decide
      exact h2 _ _
  let Good : Subgroup X :=
    { carrier := {ℓ | ∀ x y : Q, (y : X) = ℓ * x * ℓ⁻¹ →
        ((Multiplicative.toAdd (f y) : evenWeight 3) : Fin 3 → ZMod 2) =
          permAct (α ℓ : Equiv.Perm (Fin 3))
            ((Multiplicative.toAdd (f x) : evenWeight 3) : Fin 3 → ZMod 2)}
      one_mem' := by
        intro x y hy
        have : y = x := Subtype.ext (by rw [hy]; simp)
        rw [this, map_one]
        show _ = permAct (1 : Equiv.Perm (Fin 3)) _
        rw [permAct_one]
      mul_mem' := by
        intro ℓ₁ ℓ₂ h₁ h₂ x y hy
        have hz : ℓ₂ * (x : X) * ℓ₂⁻¹ ∈ Q := ‹Q.Normal›.conj_mem x x.2 ℓ₂
        have hy' : (y : X) = ℓ₁ * (ℓ₂ * x * ℓ₂⁻¹) * ℓ₁⁻¹ := by rw [hy]; group
        have e1 := h₁ ⟨ℓ₂ * (x : X) * ℓ₂⁻¹, hz⟩ y hy'
        have e2 := h₂ x ⟨ℓ₂ * (x : X) * ℓ₂⁻¹, hz⟩ rfl
        rw [e1, e2, ← permAct_mul, map_mul]
        rfl
      inv_mem' := by
        intro ℓ hℓ x y hy
        have hy' : (x : X) = ℓ * y * ℓ⁻¹ := by rw [hy]; group
        have e1 := hℓ y x hy'
        rw [e1, ← permAct_mul, map_inv, Subgroup.coe_inv, inv_mul_cancel, permAct_one] }
  have hQG : Q ≤ Good := by
    intro q hq x y hy
    have hα1 : α q = 1 := MonoidHom.mem_ker.mp (by rw [hαk]; exact hq)
    have : y = x := Subtype.ext (by
      rw [hy, hab q hq x x.2, mul_inv_cancel_right])
    rw [this, hα1]
    show _ = permAct (1 : Equiv.Perm (Fin 3)) _
    rw [permAct_one]
  have hcG : c ∈ Good := fun x y hy => hceq x y hy
  have hGood : Good = ⊤ := by
    rw [eq_top_iff, ← hQc]
    exact sup_le hQG (Subgroup.zpowers_le.mpr hcG)
  refine ⟨α, f, hαs, hαk, hfs, hfk, fun ℓ x y hy => ?_⟩
  have : ℓ ∈ Good := hGood ▸ Subgroup.mem_top ℓ
  exact this x y hy

section TypeLevel

variable {G : Type*} [Group G]

theorem blockQ_eq_map (L : Subgroup G) : blockQ L = (CFSG.pCore 2 L).map L.subtype := by
  unfold blockQ pCoreOf
  try with_reducible rfl

theorem blockU_eq_map (L : Subgroup G) :
    blockU L = ⁅CFSG.pCore 2 L, (⊤ : Subgroup L)⁆.map L.subtype := by
  change ⁅blockQ L, L⁆ = _
  rw [blockQ_eq_map, Subgroup.map_commutator]
  congr 1
  rw [← MonoidHom.range_eq_map]
  exact (Subgroup.range_subtype L).symm

theorem blockZ_eq_map (L : Subgroup G) :
    blockZ L = (⁅CFSG.pCore 2 L, (⊤ : Subgroup L)⁆ ⊓ Subgroup.center L).map L.subtype := by
  ext x
  constructor
  · rintro ⟨hxU, hxc⟩
    rw [blockU_eq_map] at hxU
    obtain ⟨u, hu, rfl⟩ := hxU
    refine ⟨u, ⟨hu, Subgroup.mem_center_iff.mpr ?_⟩, rfl⟩
    intro g
    apply L.subtype_injective
    have := Subgroup.mem_centralizer_iff.mp hxc (L.subtype g) g.2
    simpa using this
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    refine ⟨blockU_eq_map L ▸ ⟨u, hu, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have h1 := Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
    have h2 : ((⟨h, hh⟩ * u : L) : G) = ((u * ⟨h, hh⟩ : L) : G) := congrArg Subtype.val h1
    exact h2

end TypeLevel

section OrderThree

variable {G : Type*} [Group G] [Finite G]

theorem short_order_three_is_alternating_four {L : Subgroup G} (hs : IsShort2 L)
    (h3 : Nat.card (L ⧸ CFSG.pCore 2 L) = 3) :
    blockQ L = blockU L ∧ Nat.card (blockU L) = 4 ∧ blockZ L = ⊥ ∧
      Nonempty (↥L ≃* alternatingGroup (Fin 4)) ∧ IsAltType L 3 := by
  classical
  obtain ⟨hno2, -, ⟨hUcent, hUexp⟩, -, hZ, hirrL⟩ := hs
  let ι : L →* G := L.subtype
  have hι : Function.Injective ι := L.subtype_injective
  set Qt : Subgroup L := CFSG.pCore 2 L with hQt
  have hQtn : Qt.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 Qt := CFSG.pCore_isPGroup
  set Ut : Subgroup L := ⁅Qt, (⊤ : Subgroup L)⁆ with hUt
  have hQmap : blockQ L = Qt.map ι := blockQ_eq_map L
  have hUmap : blockU L = Ut.map ι := blockU_eq_map L
  have hZmap : blockZ L = (Ut ⊓ Subgroup.center L).map ι := blockZ_eq_map L
  have hUQ : Ut ≤ Qt := by
    have h1 : blockU L ≤ blockQ L := (le_inf_iff.mp hUcent).1
    rw [hUmap, hQmap] at h1
    exact (Subgroup.map_le_map_iff_of_injective hι).mp h1
  have hcomm : ∀ q ∈ Qt, ∀ u ∈ Ut, q * u = u * q := by
    intro q hq u hu
    have hu' : ι u ∈ blockU L := hUmap ▸ ⟨u, hu, rfl⟩
    have hq' : ι q ∈ blockQ L := hQmap ▸ ⟨q, hq, rfl⟩
    have hc := (le_inf_iff.mp hUcent).2 hu'
    have := Subgroup.mem_centralizer_iff.mp hc (ι q) hq'
    apply hι
    simpa using this
  have hexp : ∀ x ∈ Ut, x ^ 2 = 1 := by
    intro x hx
    have hx' : ι x ∈ blockU L := hUmap ▸ ⟨x, hx, rfl⟩
    have := hUexp (ι x) hx'
    apply hι
    simpa using this
  have hcardL : Nat.card L = 3 * Nat.card Qt := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Qt
    rw [h3] at h1
    exact h1
  have hne : Ut ⊓ Subgroup.center L < Ut := by
    have h1 : blockZ L < blockU L := hZ
    rw [hZmap, hUmap] at h1
    exact (Subgroup.map_lt_map_iff_of_injective hι).mp h1
  have hirr : ∀ W : Subgroup L, Ut ⊓ Subgroup.center L ≤ W → W ≤ Ut → W.Normal →
      W = Ut ⊓ Subgroup.center L ∨ W = Ut := by
    intro W hZW hWU hWn
    have hN : L ≤ Subgroup.normalizer ((W.map ι : Subgroup G) : Set G) := by
      have h := Subgroup.le_normalizer_map (H := W) ι
      rw [(Subgroup.normalizer_eq_top_iff).mpr hWn, Subgroup.map_top] at h
      rwa [show ι.range = L from Subgroup.range_subtype L] at h
    have := hirrL (W.map ι) (by rw [hZmap]; exact Subgroup.map_mono hZW)
      (by rw [hUmap]; exact Subgroup.map_mono hWU) hN
    rcases this with h | h
    · left
      rw [hZmap] at h
      exact Subgroup.map_injective hι h
    · right
      rw [hUmap] at h
      exact Subgroup.map_injective hι h
  obtain ⟨hEq, hQ4, hL12, hcenter, hA4, α, β, hαs, hαk, hβs, hβk, hequiv⟩ :=
    alt3_of_irreducible Qt hQ2 hcardL hUQ hcomm hexp hno2 hne hirr
  have hZbot : blockZ L = ⊥ := by
    rw [hZmap, hcenter, inf_bot_eq, Subgroup.map_bot]
  refine ⟨?_, ?_, hZbot, hA4, ?_⟩
  · rw [hQmap, hUmap]
    exact congrArg (Subgroup.map ι) hEq
  · have hEq' : Qt = Ut := hEq
    rw [hUmap, Subgroup.card_map_of_injective hι, ← hEq']
    exact hQ4
  ·
    let e1 : ↥(blockU L) ≃* ↥(Ut.map ι) := MulEquiv.subgroupCongr hUmap
    let e2 : ↥(Ut.map ι) ≃* ↥Ut := (Ut.equivMapOfInjective ι hι).symm
    let e3 : ↥Ut ≃* ↥Qt := MulEquiv.subgroupCongr hEq.symm
    let eU : ↥(blockU L) ≃* ↥Qt := (e1.trans e2).trans e3
    have hιeU : ∀ u : ↥(blockU L), ι (((eU u : Qt) : L)) = (u : G) := by
      intro u
      have h3 : (((Ut.equivMapOfInjective ι hι) ((Ut.equivMapOfInjective ι hι).symm (e1 u)) :
          ↥(Ut.map ι)) : G) = ((e1 u : ↥(Ut.map ι)) : G) := by
        rw [MulEquiv.apply_symm_apply]
      rw [Subgroup.coe_equivMapOfInjective_apply] at h3
      exact h3
    refine ⟨α, hαs, hαk, β.comp eU.toMonoidHom, hβs.comp eU.surjective, ?_, ?_⟩
    · rw [hZbot, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
      exact (MonoidHom.ker_eq_bot_iff β |>.mp hβk).comp eU.injective
    · intro ℓ u v huv i
      have hy : ((eU v : Qt) : L) = ℓ * ((eU u : Qt) : L) * ℓ⁻¹ := by
        apply hι
        rw [map_mul, map_mul, map_inv, hιeU v, hιeU u]
        exact huv
      have := hequiv ℓ (eU u) (eU v) hy
      exact congrFun this i

end OrderThree

end CFSG.QuasithinUnique.Setup.Campbell
