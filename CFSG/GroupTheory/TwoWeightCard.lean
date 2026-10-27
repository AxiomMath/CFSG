module

public import CFSG.GroupTheory.ElementaryAbelianWeights
public import CFSG.GroupTheory.TwoWeightData

public section

namespace CFSG.GroupTheory.TwoWeights

section Rels

variable {G : Type*} [Group G]

@[reducible] def commGroupOfComm (E : Subgroup G) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) :
    CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hEc a.1 a.2 b.1 b.2) }

def conjAut (E : Subgroup G) (g : G) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) : ↥E ≃* ↥E where
  toFun e := ⟨g * e.1 * g⁻¹, hg _ e.2⟩
  invFun e := ⟨g⁻¹ * e.1 * g, hg' _ e.2⟩
  left_inv e := Subtype.ext (by simp [mul_assoc])
  right_inv e := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

def sgn (b : Bool) (e : G) : G := if b then e⁻¹ else e

theorem sgn_sgn (b c : Bool) (e : G) : sgn b (sgn c e) = sgn (xor b c) e := by
  cases b <;> cases c <;> simp [sgn]

theorem conj_sgn (g : G) (b : Bool) (e : G) : g * sgn b e * g⁻¹ = sgn b (g * e * g⁻¹) := by
  cases b <;> simp [sgn, mul_assoc]

def Wt (g : G) (b : Bool) (e : G) : Prop := g * e * g⁻¹ = sgn b e

theorem Wt.mul {g h : G} {b c : Bool} {e : G} (hg : Wt g b e) (hh : Wt h c e) :
    Wt (g * h) (xor b c) e := by
  unfold Wt at *
  calc g * h * e * (g * h)⁻¹ = g * (h * e * h⁻¹) * g⁻¹ := by group
    _ = g * sgn c e * g⁻¹ := by rw [hh]
    _ = sgn c (g * e * g⁻¹) := conj_sgn g c e
    _ = sgn c (sgn b e) := by rw [hg]
    _ = sgn (xor b c) e := by rw [sgn_sgn, Bool.xor_comm]

theorem Wt.step {g v c : G} {b : Bool} {e : G} (hgv : g * v = c * g) (hc : Wt c b e) :
    Wt v b (g⁻¹ * e * g) := by
  unfold Wt at *
  have hv : v = g⁻¹ * c * g := by
    calc v = g⁻¹ * (g * v) := by group
      _ = g⁻¹ * (c * g) := by rw [hgv]
      _ = g⁻¹ * c * g := by group
  calc v * (g⁻¹ * e * g) * v⁻¹ = g⁻¹ * (c * e * c⁻¹) * g := by rw [hv]; group
    _ = g⁻¹ * sgn b e * g := by rw [hc]
    _ = sgn b (g⁻¹ * e * g) := by
        have := conj_sgn g⁻¹ b e
        simpa using this

end Rels



inductive WI
  | u1 | u2 | u3 | a
  deriving DecidableEq

instance : Fintype WI := ⟨{.u1, .u2, .u3, .a}, fun x => by cases x <;> simp⟩

section Weights

variable {G : Type*} [Group G]

def σx (w : WI → Bool) : WI → Bool
  | .u1 => xor (w .u1) (w .a)
  | .u2 => xor (w .u3) (w .a)
  | .u3 => xor (w .u2) (w .a)
  | .a => w .a

def σy (w : WI → Bool) : WI → Bool
  | .u1 => w .u1
  | .u2 => xor (w .u2) (w .a)
  | .u3 => xor (xor (w .u1) (w .u3)) (w .a)
  | .a => w .a

def stepW (w : WI → Bool) (b : Fin 3) : WI → Bool :=
  if b = 1 then σx w else if b = 2 then σy w else w

theorem reach : ∀ w₀ w : WI → Bool, w₀ .a = true → w .a = true →
    ∃ b : Fin 4 → Fin 3, (List.ofFn b).foldl stepW w₀ = w := by decide

def gen (a u₁ u₂ u₃ : G) : WI → G
  | .u1 => u₁
  | .u2 => u₂
  | .u3 => u₃
  | .a => a

theorem coe_ite_inv (E : Subgroup G) (b : Bool) (e : ↥E) :
    ((if b then e⁻¹ else e : ↥E) : G) = sgn b (e : G) := by
  cases b <;> simp [sgn]

theorem weights_card {a u₁ u₂ u₃ x y : G} (D : Data a u₁ u₂ u₃ x y) (E : Subgroup G) [Finite E]
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hN : ∀ g ∈ ({u₁, u₂, u₃, a, x, y, x⁻¹, y⁻¹} : Set G), ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hinv : ∀ e ∈ E, a * e * a⁻¹ = e⁻¹) : E = ⊥ ∨ 3 ^ 8 ≤ Nat.card E := by
  classical
  by_cases hE : E = ⊥
  · exact Or.inl hE
  refine Or.inr ?_
  have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hE
  let _ : CommGroup ↥E := commGroupOfComm E hEc
  let v : WI → G := gen a u₁ u₂ u₃
  have hvsq : ∀ i, v i * v i = 1 := by
    intro i; cases i
    · exact D.u₁_u₁
    · exact D.u₂_u₂
    · exact D.u₃_u₃
    · exact D.a_a
  have hvc : ∀ i j, v i * v j = v j * v i := by
    intro i j; cases i <;> cases j <;>
      first | rfl | exact D.u₁_u₂ | exact D.u₁_u₃ | exact D.u₁_a | exact D.u₂_u₃ | exact D.u₂_a |
        exact D.u₃_a | exact D.u₁_u₂.symm | exact D.u₁_u₃.symm | exact D.u₁_a.symm |
        exact D.u₂_u₃.symm | exact D.u₂_a.symm | exact D.u₃_a.symm
  have hvN : ∀ i, ∀ e ∈ E, v i * e * (v i)⁻¹ ∈ E := by
    intro i; cases i
    · exact hN u₁ (by simp)
    · exact hN u₂ (by simp)
    · exact hN u₃ (by simp)
    · exact hN a (by simp)
  have hvinv : ∀ i, (v i)⁻¹ = v i := fun i => inv_eq_of_mul_eq_one_right (hvsq i)
  have hvN' : ∀ i, ∀ e ∈ E, (v i)⁻¹ * e * v i ∈ E := by
    intro i e he
    rw [hvinv]
    have := hvN i e he
    rwa [hvinv] at this
  let φ : WI → (↥E ≃* ↥E) := fun i => conjAut E (v i) (hvN i) (hvN' i)
  have hφc : ∀ i j (e : ↥E), φ i (φ j e) = φ j (φ i e) := by
    intro i j e
    apply Subtype.ext
    show v i * (v j * e.1 * (v j)⁻¹) * (v i)⁻¹ = v j * (v i * e.1 * (v i)⁻¹) * (v j)⁻¹
    calc v i * (v j * e.1 * (v j)⁻¹) * (v i)⁻¹ = (v i * v j) * e.1 * (v i * v j)⁻¹ := by group
      _ = (v j * v i) * e.1 * (v j * v i)⁻¹ := by rw [hvc i j]
      _ = v j * (v i * e.1 * (v i)⁻¹) * (v j)⁻¹ := by group
  have hφ2 : ∀ i (e : ↥E), φ i (φ i e) = e := by
    intro i e
    apply Subtype.ext
    show v i * (v i * e.1 * (v i)⁻¹) * (v i)⁻¹ = e.1
    calc v i * (v i * e.1 * (v i)⁻¹) * (v i)⁻¹ = (v i * v i) * e.1 * (v i * v i)⁻¹ := by group
      _ = e.1 := by rw [hvsq i]; group
  have hA3 : ∀ e : ↥E, e ^ 3 = 1 := fun e => Subtype.ext (hE3 e.1 e.2)
  have hwt : ∀ (e : ↥E) (w : WI → Bool), (∀ i, φ i e = if w i then e⁻¹ else e) ↔
      ∀ i, Wt (v i) (w i) (e : G) := by
    intro e w
    refine forall_congr' fun i => ?_
    rw [Subtype.ext_iff, coe_ite_inv]
    exact Iff.rfl
  obtain ⟨e₀, he₀1, w₀, hw₀⟩ := exists_weight_element hA3 φ hφc hφ2
  have hw₀' := (hwt e₀ w₀).1 hw₀
  have hw₀a : w₀ .a = true := by
    by_contra hf
    have hf' : w₀ .a = false := by simpa using hf
    have h1 : a * e₀.1 * a⁻¹ = sgn (w₀ .a) e₀.1 := hw₀' .a
    rw [hinv e₀.1 e₀.2, hf'] at h1
    simp only [sgn, Bool.false_eq_true, ite_false] at h1
    have h4 : e₀.1 * e₀.1 = 1 := by
      calc e₀.1 * e₀.1 = e₀.1 * e₀.1⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    have h5 : e₀.1 ^ 3 = (e₀.1 * e₀.1) * e₀.1 := by rw [pow_succ, pow_two]
    rw [h4, one_mul, hE3 e₀.1 e₀.2] at h5
    exact he₀1 (Subtype.ext h5.symm)
  let Has : (WI → Bool) → Prop := fun w =>
    ∃ e : G, e ∈ E ∧ e ≠ 1 ∧ ∀ i, Wt (v i) (w i) e
  have hHas₀ : Has w₀ := ⟨e₀.1, e₀.2, fun h => he₀1 (Subtype.ext h), hw₀'⟩
  have hstepx : ∀ w, Has w → Has (σx w) := by
    rintro w ⟨e, heE, he1, hwe⟩
    refine ⟨x⁻¹ * e * x, ?_, ?_, ?_⟩
    · have := hN x⁻¹ (by simp) e heE
      simpa using this
    · intro h
      apply he1
      have : e = x * (x⁻¹ * e * x) * x⁻¹ := by group
      rw [this, h]; group
    · intro i
      cases i
      · exact Wt.step D.x_u₁ (Wt.mul (hwe .u1) (hwe .a))
      · exact Wt.step D.x_u₂ (Wt.mul (hwe .u3) (hwe .a))
      · exact Wt.step D.x_u₃ (Wt.mul (hwe .u2) (hwe .a))
      · exact Wt.step D.a_x.symm (hwe .a)
  have hstepy : ∀ w, Has w → Has (σy w) := by
    rintro w ⟨e, heE, he1, hwe⟩
    refine ⟨y⁻¹ * e * y, ?_, ?_, ?_⟩
    · have := hN y⁻¹ (by simp) e heE
      simpa using this
    · intro h
      apply he1
      have : e = y * (y⁻¹ * e * y) * y⁻¹ := by group
      rw [this, h]; group
    · intro i
      cases i
      · exact Wt.step D.y_u₁ (hwe .u1)
      · exact Wt.step D.y_u₂ (Wt.mul (hwe .u2) (hwe .a))
      · exact Wt.step D.y_u₃ (Wt.mul (Wt.mul (hwe .u1) (hwe .u3)) (hwe .a))
      · exact Wt.step D.a_y.symm (hwe .a)
  have hreach : ∀ (l : List (Fin 3)) (w : WI → Bool), Has w → Has (l.foldl stepW w) := by
    intro l
    induction l with
    | nil => intro w h; exact h
    | cons b l ih =>
      intro w h
      apply ih
      unfold stepW
      split_ifs with h1 h2
      · exact hstepx w h
      · exact hstepy w h
      · exact h
  have hall : ∀ k : {w : WI → Bool // w .a = true}, ∃ e : ↥E, e ≠ 1 ∧
      ∀ i, φ i e = if k.1 i then e⁻¹ else e := by
    intro k
    obtain ⟨b, hb⟩ := reach w₀ k.1 hw₀a k.2
    have hk : Has k.1 := hb ▸ hreach (List.ofFn b) w₀ hHas₀
    obtain ⟨e, heE, he1, hwe⟩ := hk
    exact ⟨⟨e, heE⟩, fun h => he1 (congrArg Subtype.val h), (hwt ⟨e, heE⟩ k.1).2 hwe⟩
  choose ak hak1 hakw using hall
  have hfin := three_pow_le_card hA3 φ hφc (fun k : {w : WI → Bool // w .a = true} => k.1)
    Subtype.val_injective ak hak1 (fun k i => hakw k i)
  have hcard : Fintype.card {w : WI → Bool // w .a = true} = 8 := by decide
  rw [hcard] at hfin
  exact hfin

end Weights


section Core

variable {X : Type*} [Group X]

theorem star_core [Finite X] {A W : Subgroup X} {τ u₁ u₂ u₃ x y : X}
    (D : Data τ u₁ u₂ u₃ x y) (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A) (hu₃ : u₃ ∈ A) (hτ : τ ∈ A)
    (hx : x ∈ A) (hy : y ∈ A) (hW : IsPGroup 3 ↥W) (hW1 : W ≠ ⊥)
    (hAW : A ≤ Subgroup.normalizer (W : Set X))
    (hC : W ⊓ Subgroup.centralizer ({τ} : Set X) = ⊥) : 3 ^ 8 ∣ Nat.card X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hW1
  have : Nontrivial ↥(Subgroup.center ↥W) := hW.center_nontrivial
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥W) := hW.to_subgroup _
  have hZcard : 3 ∣ Nat.card ↥(Subgroup.center ↥W) := by
    rcases hZp.card_eq_or_dvd with h | h
    · have := Finite.one_lt_card (α := ↥(Subgroup.center ↥W))
      omega
    · exact h
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 3 hZcard
  set z : X := ((z₀ : ↥W) : X) with hzdef
  have hzW : z ∈ W := (z₀ : ↥W).2
  have hzc : ∀ w ∈ W, w * z = z * w := fun w hw => by
    have := Subgroup.mem_center_iff.1 z₀.2 ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hz3 : z ^ 3 = 1 := by
    have h : z₀ ^ 3 = 1 := by rw [← hz₀]; exact pow_orderOf_eq_one z₀
    have := congrArg (fun g : ↥(Subgroup.center ↥W) => ((g : ↥W) : X)) h
    simpa using this
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : z₀ = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz₀
    omega
  set S : Set X := {g | ∃ a ∈ A, g = a * z * a⁻¹} with hS
  set E : Subgroup X := Subgroup.closure S with hE
  have hSW : ∀ a ∈ A, a * z * a⁻¹ ∈ W := fun a ha =>
    (Subgroup.mem_normalizer_iff.1 (hAW ha) z).1 hzW
  have hSc : ∀ a ∈ A, ∀ w ∈ W, w * (a * z * a⁻¹) = (a * z * a⁻¹) * w := by
    intro a ha w hw
    have hw' : a⁻¹ * w * a ∈ W := (Subgroup.mem_normalizer_iff''.1 (hAW ha) w).1 hw
    have := hzc _ hw'
    calc w * (a * z * a⁻¹) = a * ((a⁻¹ * w * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * w * a)) * a⁻¹ := by rw [this]
      _ = (a * z * a⁻¹) * w := by group
  have hSS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    rintro s ⟨a, ha, rfl⟩ t ⟨b, hb, rfl⟩
    exact (hSc a ha _ (hSW b hb)).symm
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    rintro s ⟨a, ha, rfl⟩
    rw [conj_pow, hz3]
    group
  have hEW : E ≤ W := by
    rw [hE, Subgroup.closure_le]
    rintro s ⟨a, ha, rfl⟩
    exact hSW a ha
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := closure_pow_eq_one hS3 hSS
  have hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := closure_comm hSS
  have hEA : ∀ g ∈ A, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    refine conj_mem_closure g (fun s hs => ?_) e he
    obtain ⟨a, ha, rfl⟩ := hs
    have : g * (a * z * a⁻¹) * g⁻¹ = (g * a) * z * (g * a)⁻¹ := by group
    rw [this]
    exact Subgroup.subset_closure ⟨g * a, A.mul_mem hg ha, rfl⟩
  have hzE : z ∈ E := Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
  have hE1 : E ≠ ⊥ := fun h => hz1 (by rw [h] at hzE; exact (Subgroup.mem_bot.1 hzE))
  have hττ : τ * τ = 1 := D.a_a
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hinv : ∀ e ∈ E, τ * e * τ⁻¹ = e⁻¹ := by
    intro e he
    have he' : τ * e * τ⁻¹ ∈ E := hEA τ hτ e he
    have h1 : τ * (τ * e * τ⁻¹) * τ⁻¹ = e := by
      calc τ * (τ * e * τ⁻¹) * τ⁻¹ = (τ * τ) * e * (τ * τ) := by rw [hτi]; group
        _ = e := by rw [hττ]; group
    have h2 : τ * (e * (τ * e * τ⁻¹)) * τ⁻¹ = e * (τ * e * τ⁻¹) := by
      calc τ * (e * (τ * e * τ⁻¹)) * τ⁻¹
          = (τ * e * τ⁻¹) * (τ * (τ * e * τ⁻¹) * τ⁻¹) := by group
        _ = (τ * e * τ⁻¹) * e := by rw [h1]
        _ = e * (τ * e * τ⁻¹) := hEc _ he' _ he
    have hfc : e * (τ * e * τ⁻¹) ∈ Subgroup.centralizer ({τ} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc e * (τ * e * τ⁻¹) * τ = (τ * (e * (τ * e * τ⁻¹)) * τ⁻¹) * τ := by rw [h2]
        _ = τ * (e * (τ * e * τ⁻¹)) := by group
    have hf : e * (τ * e * τ⁻¹) ∈ W ⊓ Subgroup.centralizer ({τ} : Set X) :=
      Subgroup.mem_inf.2 ⟨W.mul_mem (hEW he) (hEW he'), hfc⟩
    rw [hC, Subgroup.mem_bot] at hf
    exact eq_inv_of_mul_eq_one_right hf
  have hN : ∀ g ∈ ({u₁, u₂, u₃, τ, x, y, x⁻¹, y⁻¹} : Set X), ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hEA _ hu₁ e he
    · exact hEA _ hu₂ e he
    · exact hEA _ hu₃ e he
    · exact hEA _ hτ e he
    · exact hEA _ hx e he
    · exact hEA _ hy e he
    · exact hEA _ (A.inv_mem hx) e he
    · exact hEA _ (A.inv_mem hy) e he
  have hcard := (weights_card D E hE3 hEc hN hinv).resolve_left hE1
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hEp
  rw [hn] at hcard
  have h8 : 8 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hdvd : Nat.card ↥E ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
  rw [hn] at hdvd
  exact (pow_dvd_pow 3 h8).trans hdvd

end Core

end CFSG.GroupTheory.TwoWeights
