module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
variable {E : Type*} [CommGroup E]

theorem add_self_vec (y : V) : y + y = 0 := by
  rw [← two_smul (ZMod 2) y]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

@[expose] def fixSub (ρ : E →* Module.End (ZMod 2) V) (U : Submodule (ZMod 2) V) : Subgroup E where
  carrier := {e | ∀ u ∈ U, ρ e u = u}
  one_mem' := by
    intro u _
    simp
  mul_mem' := by
    intro a b ha hb u hu
    rw [map_mul, Module.End.mul_apply, hb u hu, ha u hu]
  inv_mem' := by
    intro a ha u hu
    have h := congrArg (ρ a⁻¹) (ha u hu)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact h.symm

theorem mem_fixSub {ρ : E →* Module.End (ZMod 2) V} {U : Submodule (ZMod 2) V} {e : E} :
    e ∈ fixSub ρ U ↔ ∀ u ∈ U, ρ e u = u := Iff.rfl


section Split

variable (ρ : E →* Module.End (ZMod 2) V) (hE3 : ∀ e : E, e ^ 3 = 1) (w : E)
  (U : Submodule (ZMod 2) V) (hU : ∀ e : E, ∀ u ∈ U, ρ e u ∈ U)

include hE3 in
theorem cube_apply (x : V) : ρ w (ρ w (ρ w x)) = x := by
  have h : ρ (w ^ 3) = 1 := by rw [hE3 w, map_one]
  have := congrArg (fun f : Module.End (ZMod 2) V => f x) h
  simpa [pow_succ, map_mul, Module.End.mul_apply] using this

@[expose] def Csub : Submodule (ZMod 2) V :=
  U ⊓ LinearMap.ker (ρ w - 1)

@[expose] def Dsub : Submodule (ZMod 2) V :=
  U ⊓ LinearMap.ker (ρ w * ρ w + ρ w + 1)

theorem mem_Csub {x : V} : x ∈ Csub ρ w U ↔ x ∈ U ∧ ρ w x = x := by
  simp [Csub, sub_eq_zero]

theorem mem_Dsub {x : V} : x ∈ Dsub ρ w U ↔ x ∈ U ∧ ρ w (ρ w x) + ρ w x + x = 0 := by
  simp [Dsub, Module.End.mul_apply]

include hE3 hU in
theorem Csub_add_Dsub : Csub ρ w U ⊔ Dsub ρ w U = U := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro u hu
    have hs : ρ w u ∈ U := hU w u hu
    have ht : ρ w (ρ w u) ∈ U := hU w _ hs
    have hc3 := cube_apply ρ hE3 w u
    have ha : u + ρ w u + ρ w (ρ w u) ∈ Csub ρ w U := by
      rw [mem_Csub]
      refine ⟨U.add_mem (U.add_mem hu hs) ht, ?_⟩
      rw [map_add, map_add, hc3]
      abel
    have hb : ρ w u + ρ w (ρ w u) ∈ Dsub ρ w U := by
      rw [mem_Dsub]
      refine ⟨U.add_mem hs ht, ?_⟩
      have e1 : ρ w (ρ w u + ρ w (ρ w u)) = ρ w (ρ w u) + u := by rw [map_add, hc3]
      have e2 : ρ w (ρ w (ρ w u + ρ w (ρ w u))) = u + ρ w u := by rw [e1, map_add, hc3]
      rw [e2, e1]
      have h1 : u + ρ w u + (ρ w (ρ w u) + u) + (ρ w u + ρ w (ρ w u)) =
          (u + u) + (ρ w u + ρ w u) + (ρ w (ρ w u) + ρ w (ρ w u)) := by abel
      rw [h1]
      simp only [add_self_vec, add_zero]
    have : u = (u + ρ w u + ρ w (ρ w u)) + (ρ w u + ρ w (ρ w u)) := by
      have h1 : u + ρ w u + ρ w (ρ w u) + (ρ w u + ρ w (ρ w u)) =
          u + (ρ w u + ρ w u) + (ρ w (ρ w u) + ρ w (ρ w u)) := by abel
      rw [h1]
      simp only [add_self_vec, add_zero]
    rw [this]
    exact Submodule.add_mem_sup ha hb


theorem comm_apply (e : E) (x : V) : ρ w (ρ e x) = ρ e (ρ w x) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

include hU in
theorem Csub_invariant {e : E} {x : V} (hx : x ∈ Csub ρ w U) : ρ e x ∈ Csub ρ w U := by
  rw [mem_Csub] at hx ⊢
  exact ⟨hU e x hx.1, by rw [comm_apply, hx.2]⟩

include hU in
theorem Dsub_invariant {e : E} {x : V} (hx : x ∈ Dsub ρ w U) : ρ e x ∈ Dsub ρ w U := by
  rw [mem_Dsub] at hx ⊢
  refine ⟨hU e x hx.1, ?_⟩
  have h1 : ρ w (ρ e x) = ρ e (ρ w x) := comm_apply ρ w e x
  have h2 : ρ w (ρ w (ρ e x)) = ρ e (ρ w (ρ w x)) := by rw [h1, comm_apply ρ w e (ρ w x)]
  rw [h2, h1, ← map_add, ← map_add, hx.2, map_zero]

theorem Csub_inf_Dsub : Csub ρ w U ⊓ Dsub ρ w U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hc, hd⟩ := Submodule.mem_inf.1 hx
  rw [mem_Csub] at hc
  rw [mem_Dsub] at hd
  have h := hd.2
  rw [hc.2, hc.2] at h
  rw [add_self_vec, zero_add] at h
  exact h

include hE3 hU in
theorem fixSub_eq_inf : fixSub ρ U = fixSub ρ (Csub ρ w U) ⊓ fixSub ρ (Dsub ρ w U) := by
  ext e
  simp only [Subgroup.mem_inf, mem_fixSub]
  constructor
  · intro h
    exact ⟨fun u hu => h u ((mem_Csub ρ w U).1 hu).1, fun u hu => h u ((mem_Dsub ρ w U).1 hu).1⟩
  · rintro ⟨hc, hd⟩ u hu
    have : u ∈ Csub ρ w U ⊔ Dsub ρ w U := by
      rw [Csub_add_Dsub ρ hE3 w U hU]
      exact hu
    obtain ⟨c, hc', d, hd', rfl⟩ := Submodule.mem_sup.1 this
    rw [map_add, hc c hc', hd d hd']

include hE3 hU in
theorem finrank_split :
    finrank (ZMod 2) (Csub ρ w U) + finrank (ZMod 2) (Dsub ρ w U) = finrank (ZMod 2) U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := V) (Csub ρ w U)
    (Dsub ρ w U)
  rw [Csub_add_Dsub ρ hE3 w U hU, Csub_inf_Dsub, finrank_bot, add_zero] at h
  exact h.symm


theorem eq_of_add_eq_zero_vec {a b : V} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [add_self_vec, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

include hE3 hU in
theorem sq_of_Csub_bot (hC : Csub ρ w U = ⊥) {u : V} (hu : u ∈ U) :
    ρ w (ρ w u) = ρ w u + u := by
  have hs : ρ w u ∈ U := hU w u hu
  have ht : ρ w (ρ w u) ∈ U := hU w _ hs
  have hc3 := cube_apply ρ hE3 w u
  have hx : ρ w (ρ w u) + ρ w u + u ∈ Csub ρ w U := by
    rw [mem_Csub]
    refine ⟨U.add_mem (U.add_mem ht hs) hu, ?_⟩
    rw [map_add, map_add, hc3]
    abel
  rw [hC, Submodule.mem_bot] at hx
  have : ρ w (ρ w u) + (ρ w u + u) = 0 := by rw [← add_assoc]; exact hx
  exact eq_of_add_eq_zero_vec this

include hE3 hU in
theorem eq_of_three (y z : E) (hy : Csub ρ y U = ⊥) (hz : Csub ρ z U = ⊥)
    (hyz : Csub ρ (y * z) U = ⊥) {u : V} (hu : u ∈ U) : ρ y u = ρ z u := by
  have hBu : ρ z u ∈ U := hU z u hu
  have hBBu : ρ z (ρ z u) ∈ U := hU z _ hBu
  have h1 := sq_of_Csub_bot ρ hE3 (y * z) U hU hyz hu
  simp only [map_mul, Module.End.mul_apply] at h1
  have e1 : ρ y (ρ z (ρ y (ρ z u))) = ρ y (ρ y (ρ z (ρ z u))) := by
    rw [comm_apply ρ z y (ρ z u)]
  have e2 := sq_of_Csub_bot ρ hE3 y U hU hy hBBu
  have e3 := sq_of_Csub_bot ρ hE3 z U hU hz hu
  rw [e1, e2, e3, map_add] at h1
  have h3 : (ρ y u + ρ z u) + (ρ y (ρ z u) + u) = 0 + (ρ y (ρ z u) + u) := by
    calc (ρ y u + ρ z u) + (ρ y (ρ z u) + u) = ρ y (ρ z u) + ρ y u + (ρ z u + u) := by abel
      _ = ρ y (ρ z u) + u := h1
      _ = _ := by rw [zero_add]
  exact eq_of_add_eq_zero_vec (add_right_cancel h3)

end Split

theorem index_fixSub_le [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1)
    (ρ : E →* Module.End (ZMod 2) V) :
    ∀ (n : ℕ) (U : Submodule (ZMod 2) V), finrank (ZMod 2) U = n →
      (∀ e : E, ∀ u ∈ U, ρ e u ∈ U) → (fixSub ρ U).index ≤ 3 ^ (n / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU
  by_cases hbig : 3 < (fixSub ρ U).index
  ·
    obtain ⟨w, hwK, hwC⟩ : ∃ w : E, w ∉ fixSub ρ U ∧ Csub ρ w U ≠ ⊥ := by
      by_contra hno
      push Not at hno
      have hK : fixSub ρ U ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hbig; omega
      obtain ⟨y, hy⟩ : ∃ y : E, y ∉ fixSub ρ U := by
        by_contra h
        push Not at h
        exact hK (eq_top_iff.2 fun x _ => h x)
      have key : ∀ z : E, z ∈ fixSub ρ U ∨ y * z ∈ fixSub ρ U ∨ y * z⁻¹ ∈ fixSub ρ U := by
        intro z
        by_cases hz : z ∈ fixSub ρ U
        · exact Or.inl hz
        by_cases hyz : y * z ∈ fixSub ρ U
        · exact Or.inr (Or.inl hyz)
        right; right
        have h3 : ∀ u ∈ U, ρ y u = ρ z u := fun u hu =>
          eq_of_three ρ hE3 U hU y z (hno y hy) (hno z hz) (hno _ hyz) hu
        rw [mem_fixSub]
        intro u hu
        have hzu : ρ z⁻¹ u ∈ U := hU z⁻¹ u hu
        have := h3 _ hzu
        rw [map_mul, Module.End.mul_apply, this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]
      have hcard : Nat.card (E ⧸ fixSub ρ U) ≤ 3 := by
        have hsurj : Function.Surjective
            (fun i : Fin 3 => (QuotientGroup.mk (y ^ (i : ℕ)) : E ⧸ fixSub ρ U)) := by
          intro q
          obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
          rcases key z with h | h | h
          · refine ⟨0, ?_⟩
            simp only [Fin.val_zero, pow_zero]
            exact ((QuotientGroup.eq_one_iff z).2 h).symm
          · refine ⟨2, ?_⟩
            simp only [Fin.val_two]
            rw [QuotientGroup.eq]
            have h3 : y ^ 3 = 1 := hE3 y
            have : (y ^ 2)⁻¹ * z = y * z := by
              calc (y ^ 2)⁻¹ * z = (y ^ 2)⁻¹ * y ^ 3 * z := by rw [h3, mul_one]
                _ = y * z := by group
            rw [this]
            exact h
          · refine ⟨1, ?_⟩
            simp only [Fin.val_one, pow_one]
            rw [QuotientGroup.eq]
            have : y⁻¹ * z = (y * z⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
            rw [this]
            exact (fixSub ρ U).inv_mem h
        have := Nat.card_le_card_of_surjective _ hsurj
        simpa using this
      rw [Subgroup.index_eq_card] at hbig
      omega
    have hsplit := finrank_split ρ hE3 w U hU
    have hCne := hwC
    have hDne : Dsub ρ w U ≠ ⊥ := by
      intro hD
      apply hwK
      intro u hu
      have : u ∈ Csub ρ w U ⊔ Dsub ρ w U := by
        rw [Csub_add_Dsub ρ hE3 w U hU]
        exact hu
      rw [hD, sup_bot_eq] at this
      exact ((mem_Csub ρ w U).1 this).2
    have hc : 1 ≤ finrank (ZMod 2) (Csub ρ w U) := Submodule.one_le_finrank_iff.2 hCne
    have hd : 1 ≤ finrank (ZMod 2) (Dsub ρ w U) := Submodule.one_le_finrank_iff.2 hDne
    have h1 := ih _ (by omega) (Csub ρ w U) rfl fun e u hu => Csub_invariant ρ w U hU hu
    have h2 := ih _ (by omega) (Dsub ρ w U) rfl fun e u hu => Dsub_invariant ρ w U hU hu
    calc (fixSub ρ U).index
        = (fixSub ρ (Csub ρ w U) ⊓ fixSub ρ (Dsub ρ w U)).index := by
          rw [← fixSub_eq_inf ρ hE3 w U hU]
      _ ≤ (fixSub ρ (Csub ρ w U)).index * (fixSub ρ (Dsub ρ w U)).index :=
          Subgroup.index_inf_le
      _ ≤ 3 ^ (finrank (ZMod 2) (Csub ρ w U) / 2) * 3 ^ (finrank (ZMod 2) (Dsub ρ w U) / 2) :=
          Nat.mul_le_mul h1 h2
      _ = 3 ^ (finrank (ZMod 2) (Csub ρ w U) / 2 + finrank (ZMod 2) (Dsub ρ w U) / 2) :=
          (pow_add _ _ _).symm
      _ ≤ 3 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · by_cases hK : fixSub ρ U = ⊤
    · rw [hK, Subgroup.index_top]
      exact Nat.one_le_pow _ _ (by norm_num)
    ·
      obtain ⟨e, he⟩ : ∃ e : E, e ∉ fixSub ρ U := by
        by_contra h
        push Not at h
        exact hK (eq_top_iff.2 fun x _ => h x)
      rw [mem_fixSub] at he
      push Not at he
      obtain ⟨u, hu, hne⟩ := he
      have hu0 : u ≠ 0 := fun h => hne (by rw [h, map_zero])
      have heu0 : ρ e u ≠ 0 := by
        intro h
        apply hu0
        have := cube_apply ρ hE3 e u
        rw [h, map_zero, map_zero] at this
        exact this.symm
      have hli : LinearIndependent (ZMod 2)
          (![⟨u, hu⟩, ⟨ρ e u, hU e u hu⟩] : Fin 2 → ↥U) := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have hst' : s • u + t • ρ e u = 0 := by
          have := congrArg Subtype.val hst
          simpa using this
        rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s with rfl | rfl <;>
          rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) t with rfl | rfl
        · exact ⟨rfl, rfl⟩
        · simp at hst'
          exact absurd hst' heu0
        · simp at hst'
          exact absurd hst' hu0
        · simp at hst'
          exact absurd (eq_of_add_eq_zero_vec hst').symm hne
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at h2
      calc (fixSub ρ U).index ≤ 3 := not_lt.1 hbig
        _ = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_three_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite E]
    (hE3 : ∀ e : E, e ^ 3 = 1) (f : E →* (Matrix ι ι (ZMod 2))ˣ)
    (hf : Function.Injective f) :
    Nat.card E ≤ 3 ^ (Fintype.card ι / 2) := by
  let ρ : E →* Module.End (ZMod 2) (ι → ZMod 2) :=
    { toFun := fun e => Matrix.mulVecLin
        ((f e : Matrix ι ι (ZMod 2)))
      map_one' := by simp; rfl
      map_mul' := fun a b => by simp [Matrix.mulVecLin_mul]; rfl }
  have hfix : fixSub ρ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [mem_fixSub] at he
    have hM : (f e : Matrix ι ι (ZMod 2)) = 1 := by
      ext j i
      have := congrFun (he (Pi.single i 1) Submodule.mem_top) j
      simpa [ρ, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have : f e = 1 := Units.ext hM
    rw [Subgroup.mem_bot]
    exact hf (by rw [this, map_one])
  have h := index_fixSub_le hE3 ρ _ ⊤ rfl (fun _ _ _ => Submodule.mem_top)
  rw [hfix, Subgroup.index_bot, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h

theorem card_le_three_pow_of_injective' {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [Group E]
    [Finite E] (hcomm : ∀ a b : E, a * b = b * a) (hE3 : ∀ e : E, e ^ 3 = 1)
    (f : E →* (Matrix ι ι (ZMod 2))ˣ) (hf : Function.Injective f) :
    Nat.card E ≤ 3 ^ (Fintype.card ι / 2) :=
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  card_le_three_pow_of_injective hE3 f hf

end CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
