module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchCode
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

@[expose] def extMul (N : ℕ) (mul : ℕ → ℕ → ℕ) (F : ℕ → ℕ) (z c d : ℕ) : ℕ :=
  if c < N then (if d < N then mul c d else mul c (d - N) + N)
  else (if d < N then mul (c - N) (F d) + N else mul (mul (c - N) (F (d - N))) z)

@[expose] def extInv (N : ℕ) (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (F : ℕ → ℕ) (z c : ℕ) : ℕ :=
  if c < N then inv c else F (inv (mul (c - N) z)) + N

theorem mem_sup_zpowers_iff {K : Subgroup G} {x : G} (hxN : x ∈ normalizer (K : Set G))
    (hx2 : x * x ∈ K) {y : G} : y ∈ K ⊔ zpowers x ↔ y ∈ K ∨ y * x⁻¹ ∈ K := by
  have hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => (mem_normalizer_iff.1 hxN k).1 hk
  have hxK' : ∀ k ∈ K, x⁻¹ * k * x ∈ K := fun k hk => by
    have := (mem_normalizer_iff.1 (inv_mem hxN) k).1 hk
    simpa using this
  have hxinv : x⁻¹ * x⁻¹ ∈ K := by
    have := K.inv_mem hx2
    simpa [mul_assoc] using this
  let L : Subgroup G :=
    { carrier := {y | y ∈ K ∨ y * x⁻¹ ∈ K}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (K.mul_mem ha hb)
        · exact Or.inr (by simpa [mul_assoc] using K.mul_mem ha hb)
        · right
          have : a * b * x⁻¹ = (a * x⁻¹) * (x * b * x⁻¹) := by group
          rw [this]; exact K.mul_mem ha (hxK b hb)
        · left
          have : a * b = (a * x⁻¹) * (x * (b * x⁻¹) * x⁻¹) * (x * x) := by group
          rw [this]
          exact K.mul_mem (K.mul_mem ha (hxK _ hb)) hx2
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (K.inv_mem ha)
        · right
          have : a⁻¹ * x⁻¹ = (x⁻¹ * (a * x⁻¹)⁻¹ * x) * (x⁻¹ * x⁻¹) := by group
          rw [this]
          exact K.mul_mem (hxK' _ (K.inv_mem ha)) hxinv }
  have hL : K ⊔ zpowers x = L := by
    refine le_antisymm (sup_le (fun k hk => Or.inl hk) (zpowers_le.2 (Or.inr (by simp)))) ?_
    rintro y (hy | hy)
    · exact mem_sup_left hy
    · have : y = (y * x⁻¹) * x := by group
      rw [this]
      exact mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers x))
  rw [hL]
  rfl

namespace CodeIso

variable {K : Subgroup G} {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso K N mul)

@[expose] noncomputable def extF (x : G) (y : (K ⊔ zpowers x : Subgroup G)) : ℕ := by
  classical
  exact if h : (y : G) ∈ K then Φ.f ⟨y, h⟩ else
    if h' : (y : G) * x⁻¹ ∈ K then Φ.f ⟨(y : G) * x⁻¹, h'⟩ + N else 0

theorem extF_of_mem {x : G} (y : (K ⊔ zpowers x : Subgroup G)) (h : (y : G) ∈ K) :
    Φ.extF x y = Φ.f ⟨y, h⟩ := by
  classical
  unfold extF
  rw [dite_eq_left h]

theorem extF_of_not_mem {x : G} (y : (K ⊔ zpowers x : Subgroup G)) (h : (y : G) ∉ K)
    (h' : (y : G) * x⁻¹ ∈ K) : Φ.extF x y = Φ.f ⟨(y : G) * x⁻¹, h'⟩ + N := by
  classical
  unfold extF
  rw [dite_eq_right h, dite_eq_left h']

@[expose] noncomputable def extCodeIso {x : G}
    (hxN : x ∈ normalizer (K : Set G)) (hxK : x ∉ K) (hx2 : x * x ∈ K) {F : ℕ → ℕ}
    (hF : ∀ k : K, Φ.f ⟨x * k * x⁻¹, (mem_normalizer_iff.1 hxN k).1 k.2⟩ = F (Φ.f k)) :
    CodeIso (K ⊔ zpowers x : Subgroup G) (2 * N) (extMul N mul F (Φ.f ⟨x * x, hx2⟩)) where
  f := Φ.extF x
  lt y := by
    by_cases h : (y : G) ∈ K
    · rw [Φ.extF_of_mem y h]; have := Φ.lt ⟨y, h⟩; omega
    · have h' := ((mem_sup_zpowers_iff hxN hx2).1 y.2).resolve_left h
      rw [Φ.extF_of_not_mem y h h']; have := Φ.lt ⟨_, h'⟩; omega
  inj := by
    intro a b hab
    by_cases ha : (a : G) ∈ K <;> by_cases hb : (b : G) ∈ K
    · rw [Φ.extF_of_mem a ha, Φ.extF_of_mem b hb] at hab
      exact Subtype.ext (congrArg Subtype.val (Φ.inj hab) :)
    · have hb' := ((mem_sup_zpowers_iff hxN hx2).1 b.2).resolve_left hb
      rw [Φ.extF_of_mem a ha, Φ.extF_of_not_mem b hb hb'] at hab
      have := Φ.lt ⟨a, ha⟩; omega
    · have ha' := ((mem_sup_zpowers_iff hxN hx2).1 a.2).resolve_left ha
      rw [Φ.extF_of_not_mem a ha ha', Φ.extF_of_mem b hb] at hab
      have := Φ.lt ⟨b, hb⟩; omega
    · have ha' := ((mem_sup_zpowers_iff hxN hx2).1 a.2).resolve_left ha
      have hb' := ((mem_sup_zpowers_iff hxN hx2).1 b.2).resolve_left hb
      rw [Φ.extF_of_not_mem a ha ha', Φ.extF_of_not_mem b hb hb'] at hab
      have := congrArg Subtype.val (Φ.inj (Nat.add_right_cancel hab))
      exact Subtype.ext (mul_right_cancel this)
  surj c hc := by
    by_cases hcN : c < N
    · obtain ⟨k, hk⟩ := Φ.surj c hcN
      exact ⟨⟨k, mem_sup_left k.2⟩, by rw [Φ.extF_of_mem _ k.2]; exact hk⟩
    · obtain ⟨k, hk⟩ := Φ.surj (c - N) (by omega)
      have hkx : (k : G) * x ∈ K ⊔ zpowers x := mul_mem (mem_sup_left k.2)
        (mem_sup_right (mem_zpowers x))
      have hnot : (k : G) * x ∉ K := fun h => hxK (by simpa using K.mul_mem (K.inv_mem k.2) h)
      have h' : (k : G) * x * x⁻¹ ∈ K := by simp
      refine ⟨⟨_, hkx⟩, ?_⟩
      rw [Φ.extF_of_not_mem ⟨_, hkx⟩ hnot h']
      have : (⟨(k : G) * x * x⁻¹, h'⟩ : K) = k := Subtype.ext (by simp)
      rw [this, hk]; omega
  map_mul a b := by
    have hK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => (mem_normalizer_iff.1 hxN k).1 hk
    by_cases ha : (a : G) ∈ K <;> by_cases hb : (b : G) ∈ K
    · have hab : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) ∈ K := K.mul_mem ha hb
      rw [Φ.extF_of_mem _ hab, Φ.extF_of_mem a ha, Φ.extF_of_mem b hb, extMul,
        ite_eq_left (Φ.lt _), ite_eq_left (Φ.lt _), ← Φ.map_mul]
      rfl
    · have hb' := ((mem_sup_zpowers_iff hxN hx2).1 b.2).resolve_left hb
      have hab : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) ∉ K := fun h =>
        hb (by simpa using K.mul_mem (K.inv_mem ha) h)
      have hab' : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) * x⁻¹ ∈ K := by
        simpa [mul_assoc] using K.mul_mem ha hb'
      rw [Φ.extF_of_not_mem _ hab hab', Φ.extF_of_mem a ha, Φ.extF_of_not_mem b hb hb', extMul,
        ite_eq_left (Φ.lt _), ite_eq_right (by have := Φ.lt ⟨_, hb'⟩; omega), Nat.add_sub_cancel,
        ← Φ.map_mul]
      congr 2
      exact Subtype.ext (by simp [mul_assoc])
    · have ha' := ((mem_sup_zpowers_iff hxN hx2).1 a.2).resolve_left ha
      have hxb := hK _ hb
      have hab' : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) * x⁻¹ ∈ K := by
        have : (a : G) * b * x⁻¹ = ((a : G) * x⁻¹) * (x * b * x⁻¹) := by group
        simpa [this] using K.mul_mem ha' hxb
      have hab : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) ∉ K := by
        intro h
        apply hxK
        have : x = ((a : G) * b * x⁻¹)⁻¹ * ((a : G) * b) := by group
        rw [this]
        exact K.mul_mem (K.inv_mem hab') h
      rw [Φ.extF_of_not_mem _ hab hab', Φ.extF_of_not_mem a ha ha', Φ.extF_of_mem b hb, extMul,
        ite_eq_right (by have := Φ.lt ⟨_, ha'⟩; omega), ite_eq_left (Φ.lt _), Nat.add_sub_cancel,
        ← hF ⟨b, hb⟩, ← Φ.map_mul]
      congr 2
      exact Subtype.ext (by simp only [coe_mul]; group)
    · have ha' := ((mem_sup_zpowers_iff hxN hx2).1 a.2).resolve_left ha
      have hb' := ((mem_sup_zpowers_iff hxN hx2).1 b.2).resolve_left hb
      have hab : ((a * b : (K ⊔ zpowers x : Subgroup G)) : G) ∈ K := by
        have : (a : G) * b = ((a : G) * x⁻¹) * (x * ((b : G) * x⁻¹) * x⁻¹) * (x * x) := by group
        rw [coe_mul, this]
        exact K.mul_mem (K.mul_mem ha' (hK _ hb')) hx2
      rw [Φ.extF_of_mem _ hab, Φ.extF_of_not_mem a ha ha', Φ.extF_of_not_mem b hb hb', extMul,
        ite_eq_right (by have := Φ.lt ⟨_, ha'⟩; omega), ite_eq_right (by have := Φ.lt ⟨_, hb'⟩; omega),
        Nat.add_sub_cancel, Nat.add_sub_cancel, ← hF ⟨_, hb'⟩, ← Φ.map_mul, ← Φ.map_mul]
      congr 1
      exact Subtype.ext (by simp only [coe_mul]; group)

include Φ in
theorem gen_ext (h0 : mul 0 0 = 0) (F : ℕ → ℕ) (z : ℕ) {gens : List ℕ}
    (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N) :
    Gen (extMul N mul F z) (gens ++ [N]) (2 * N) := by
  have hmul : ∀ c d, c < N → d < N → mul c d < N := fun c d hc hd => by
    rw [← Φ.f_g hc, ← Φ.f_g hd, ← Φ.map_mul]; exact Φ.lt _
  have hid : ∀ c, c < N → mul c 0 = c := fun c hc => by
    rw [← Φ.f_g hc, ← Φ.f_one h0, ← Φ.map_mul, mul_one]
  have key : ∀ c, Reach mul gens c → c < N ∧ Reach (extMul N mul F z) (gens ++ [N]) c := by
    intro c hc
    induction hc with
    | zero => exact ⟨Φ.pos, Reach.zero⟩
    | @step c g _ hg ih =>
      obtain ⟨hc, hr⟩ := ih
      have hgN := hgens _ hg
      refine ⟨hmul _ _ hc hgN, ?_⟩
      have e : extMul N mul F z c g = mul c g := by
        rw [extMul, ite_eq_left hc, ite_eq_left hgN]
      rw [← e]
      exact Reach.step hr (List.mem_append_left _ hg)
  intro c hc
  by_cases hcN : c < N
  · exact (key c (hG c hcN)).2
  · have h1 := (key (c - N) (hG _ (by omega))).2
    have e : extMul N mul F z (c - N) N = c := by
      rw [extMul, ite_eq_left (by omega : c - N < N), ite_eq_right (lt_irrefl N), Nat.sub_self,
        hid _ (by omega)]
      omega
    rw [← e]
    exact Reach.step h1 (List.mem_append_right _ (List.mem_singleton_self N))

end CodeIso

end CFSG.EvenSmallLie.OmegaEight.SpBranch
