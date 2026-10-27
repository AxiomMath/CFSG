module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup


private def indConj {G : Type*} [Group G] (K : Subgroup G) (n : G)
    (hn : n ∈ normalizer (K : Set G)) (k : ↥K) : ↥K :=
  ⟨n * k * n⁻¹, (mem_normalizer_iff.1 hn k).1 k.2⟩

private theorem indConj_mul {G : Type*} [Group G] (K : Subgroup G) (n : G)
    (hn : n ∈ normalizer (K : Set G)) (k k' : ↥K) :
    indConj K n hn (k * k') = indConj K n hn k * indConj K n hn k' := by
  apply Subtype.ext
  simp [indConj, mul_assoc]

private theorem indConj_indConj {G : Type*} [Group G] (K : Subgroup G) (n n' : G)
    (hn : n ∈ normalizer (K : Set G)) (hn' : n' ∈ normalizer (K : Set G))
    (hnn : n * n' ∈ normalizer (K : Set G)) (k : ↥K) :
    indConj K (n * n') hnn k = indConj K n hn (indConj K n' hn' k) := by
  apply Subtype.ext
  simp [indConj, mul_assoc]

private theorem indConj_one {G : Type*} [Group G] (K : Subgroup G)
    (h1 : (1 : G) ∈ normalizer (K : Set G)) (k : ↥K) : indConj K 1 h1 k = k := by
  apply Subtype.ext
  simp [indConj]

theorem exists_inducedHom {G Q : Type*} [Group G] [Group Q] (K N : Subgroup G) (f : ↥K →* Q)
    (hf : Function.Surjective f) (hN : N ≤ normalizer (K : Set G))
    (hker : ∀ n ∈ N, ∀ k k' : ↥K, (k' : G) = n * (k : G) * n⁻¹ → (f k = 1 ↔ f k' = 1)) :
    ∃ Φ : ↥N →* MulAut Q, ∀ (n : ↥N) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k' := by
  classical
  have hwd : ∀ n : ↥N, ∀ k₁ k₂ : ↥K, f k₁ = f k₂ →
      f (indConj K n (hN n.2) k₁) = f (indConj K n (hN n.2) k₂) := by
    intro n k₁ k₂ h12
    have h1 : f (k₁ * k₂⁻¹) = 1 := by rw [map_mul, map_inv, h12, mul_inv_cancel]
    have h2 := (hker n n.2 (k₁ * k₂⁻¹) (indConj K n (hN n.2) (k₁ * k₂⁻¹)) rfl).1 h1
    rw [indConj_mul, map_mul] at h2
    have : indConj K n (hN n.2) k₂⁻¹ = (indConj K n (hN n.2) k₂)⁻¹ := by
      apply Subtype.ext; simp [indConj, mul_assoc]
    rw [this, map_inv] at h2
    exact mul_inv_eq_one.1 h2
  let φ0 : ↥N → Q → Q := fun n q => f (indConj K n (hN n.2) (Classical.choose (hf q)))
  have hφ0 : ∀ (n : ↥N) (k : ↥K), φ0 n (f k) = f (indConj K n (hN n.2) k) := fun n k =>
    hwd n _ _ (Classical.choose_spec (hf (f k)))
  have hmul : ∀ (n : ↥N) (q₁ q₂ : Q), φ0 n (q₁ * q₂) = φ0 n q₁ * φ0 n q₂ := by
    intro n q₁ q₂
    obtain ⟨k₁, rfl⟩ := hf q₁
    obtain ⟨k₂, rfl⟩ := hf q₂
    have h1 : φ0 n (f k₁ * f k₂) = f (indConj K n (hN n.2) (k₁ * k₂)) := by
      rw [← map_mul]; exact hφ0 n _
    have h2 : φ0 n (f k₁) = f (indConj K n (hN n.2) k₁) := hφ0 n _
    have h3 : φ0 n (f k₂) = f (indConj K n (hN n.2) k₂) := hφ0 n _
    rw [h1, h2, h3, indConj_mul, map_mul]
  have hmulN : ∀ (n n' : ↥N) (q : Q), φ0 (n * n') q = φ0 n (φ0 n' q) := by
    intro n n' q
    obtain ⟨k, rfl⟩ := hf q
    have h1 : φ0 (n * n') (f k) = f (indConj K (n * n') (hN (n * n').2) k) := hφ0 _ k
    have h2 : φ0 n' (f k) = f (indConj K n' (hN n'.2) k) := hφ0 _ k
    have h3 : φ0 n (f (indConj K n' (hN n'.2) k)) =
        f (indConj K n (hN n.2) (indConj K n' (hN n'.2) k)) := hφ0 _ _
    rw [h1, h2, h3]
    exact congrArg f (indConj_indConj K n n' (hN n.2) (hN n'.2) (hN (n * n').2) k)
  have hone : ∀ q : Q, φ0 1 q = q := by
    intro q
    obtain ⟨k, rfl⟩ := hf q
    have h1 : φ0 1 (f k) = f (indConj K (1 : ↥N) (hN (1 : ↥N).2) k) := hφ0 _ k
    rw [h1]
    exact congrArg f (indConj_one K (hN (1 : ↥N).2) k)
  let e : ↥N → MulAut Q := fun n =>
    { toFun := φ0 n
      invFun := φ0 n⁻¹
      left_inv := fun q => by rw [← hmulN, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmulN, mul_inv_cancel, hone]
      map_mul' := hmul n }
  refine ⟨{ toFun := e, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext q; exact hone q
  · intro n n'; ext q; exact hmulN n n' q
  · intro n k k' hk'
    have : k' = indConj K n (hN n.2) k := Subtype.ext hk'
    subst this
    exact hφ0 n k



section Aux

variable {V : Type*} [CommGroup V]

private def InW (w w' x : V) : Prop := x = 1 ∨ x = w ∨ x = w' ∨ x = w * w'

private theorem inW_mul_w {w w' : V} (hw : w * w = 1) {x : V} (hx : InW w w' x) :
    InW w w' (w * x) := by
  rcases hx with rfl | rfl | rfl | rfl
  · simp [InW]
  · simp [InW, hw]
  · simp [InW]
  · right; right; left; rw [← mul_assoc, hw, one_mul]

private theorem inW_mul_w' {w w' : V} (hw' : w' * w' = 1) {x : V} (hx : InW w w' x) :
    InW w w' (w' * x) := by
  rcases hx with rfl | rfl | rfl | rfl
  · simp [InW]
  · right; right; right; rw [mul_comm]
  · simp [InW, hw']
  · right; left; rw [mul_left_comm, hw', mul_one]

private theorem inW_mul {w w' : V} (hw : w * w = 1) (hw' : w' * w' = 1) {x y : V}
    (hx : InW w w' x) (hy : InW w w' y) : InW w w' (x * y) := by
  rcases hy with rfl | rfl | rfl | rfl
  · simpa using hx
  · rw [mul_comm]; exact inW_mul_w hw hx
  · rw [mul_comm]; exact inW_mul_w' hw' hx
  · rw [← mul_assoc, mul_comm x w, mul_assoc]
    exact inW_mul_w hw (by rw [mul_comm]; exact inW_mul_w' hw' hx)

private theorem inW_one {w w' : V} : InW w w' 1 := Or.inl rfl

variable {w w' : V} {α β : MulAut V}

private theorem inW_apply_left (hw : w * w = 1) (hα : ∀ v, α v = v ∨ α v = w * v) {x : V}
    (hx : InW w w' x) : InW w w' (α x) := by
  rcases hα x with h | h
  · rwa [h]
  · rw [h]; exact inW_mul_w hw hx

private theorem inW_apply_right (hw' : w' * w' = 1) (hβ : ∀ v, β v = v ∨ β v = w' * v) {x : V}
    (hx : InW w w' x) : InW w w' (β x) := by
  rcases hβ x with h | h
  · rwa [h]
  · rw [h]; exact inW_mul_w' hw' hx

private theorem inW_comm (hV : ∀ v : V, v * v = 1) (hα : ∀ v, α v = v ∨ α v = w * v)
    (hβ : ∀ v, β v = v ∨ β v = w' * v) (v : V) : InW w w' ((α * β) v * v⁻¹) := by
  have hw : w * w = 1 := hV w
  have hw' : w' * w' = 1 := hV w'
  show InW w w' (α (β v) * v⁻¹)
  rcases hβ v with h | h
  · rw [h]
    rcases hα v with h' | h'
    · rw [h', mul_inv_cancel]; exact inW_one
    · rw [h', mul_assoc, mul_inv_cancel, mul_one]; exact Or.inr (Or.inl rfl)
  · rw [h, map_mul]
    have hw'a : InW w w' (α w') := inW_apply_left hw hα (Or.inr (Or.inr (Or.inl rfl)))
    rcases hα v with h' | h'
    · rw [h', mul_assoc, mul_inv_cancel, mul_one]; exact hw'a
    · rw [h', mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      exact inW_mul hw hw' hw'a (Or.inr (Or.inl rfl))

private theorem pow_twelve_aux (hV : ∀ v : V, v * v = 1)
    (hα : ∀ v, α v = v ∨ α v = w * v) (hβ : ∀ v, β v = v ∨ β v = w' * v) (v : V) :
    ((α * β) ^ 12) v = v := by
  classical
  have hw : w * w = 1 := hV w
  have hw' : w' * w' = 1 := hV w'
  set u : MulAut V := α * β with hu
  have huW : ∀ x, InW w w' x → InW w w' (u x) := fun x hx =>
    inW_apply_left hw hα (inW_apply_right hw' hβ hx)
  have hpow : ∀ n : ℕ, ∀ v, InW w w' ((u ^ n) v * v⁻¹) := by
    intro n
    induction n with
    | zero => intro v; simpa using inW_one
    | succ n ih =>
      intro v
      have h1 := inW_comm hV hα hβ ((u ^ n) v)
      have h2 := ih v
      have e : (u ^ (n + 1)) v * v⁻¹ =
          (u ((u ^ n) v) * ((u ^ n) v)⁻¹) * ((u ^ n) v * v⁻¹) := by
        rw [pow_succ', MulAut.mul_apply]; group
      rw [e]
      exact inW_mul hw hw' h1 h2
  let Y : Finset V := ({1, w, w', w * w'} : Finset V).erase 1
  have hYmem : ∀ x, x ∈ Y ↔ x ≠ 1 ∧ InW w w' x := by
    intro x
    simp only [Y, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, InW]
  have hYcard : Fintype.card Y ≤ 3 := by
    rw [Fintype.card_coe]
    have h4 : ({1, w, w', w * w'} : Finset V).card ≤ 4 := Finset.card_le_four
    have h1 : (1 : V) ∈ ({1, w, w', w * w'} : Finset V) := by simp
    have := Finset.card_erase_of_mem h1
    simp only [Y]
    omega
  have hYu : ∀ y ∈ Y, u y ∈ Y := by
    intro y hy
    obtain ⟨hy1, hyW⟩ := (hYmem y).1 hy
    refine (hYmem _).2 ⟨fun h => hy1 (u.injective (by rw [h, map_one])), huW y hyW⟩
  have h6 : ∀ y ∈ Y, (u ^ 6) y = y := by
    let f : Y → Y := fun y => ⟨u y, hYu y y.2⟩
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (u.injective (congrArg Subtype.val h))
    let σ : Equiv.Perm Y := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
    have hσpow : ∀ (n : ℕ) (y : Y), ((σ ^ n) y : V) = (u ^ n) y := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
        intro y
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', MulAut.mul_apply]
        show u ((σ ^ n) y : V) = u ((u ^ n) y)
        rw [ih]
    have hσ6 : σ ^ 6 = 1 := by
      have h1 : σ ^ Fintype.card (Equiv.Perm Y) = 1 := pow_card_eq_one
      rw [Fintype.card_perm] at h1
      obtain ⟨m, hm⟩ : (Fintype.card Y).factorial ∣ 6 :=
        Nat.factorial_dvd_factorial hYcard
      rw [hm, pow_mul, h1, one_pow]
    intro y hy
    have := hσpow 6 ⟨y, hy⟩
    rw [hσ6] at this
    exact this.symm
  have hfix : ∀ c : V, InW w w' c → (u ^ 6) c = c := by
    intro c hc
    by_cases h1 : c = 1
    · subst h1; simp
    · exact h6 c ((hYmem c).2 ⟨h1, hc⟩)
  have hc := hpow 6 v
  have hcfix := hfix _ hc
  set c := (u ^ 6) v * v⁻¹ with hcdef
  have hv6 : (u ^ 6) v = c * v := by rw [hcdef]; group
  calc ((u ^ 12) v) = (u ^ 6) ((u ^ 6) v) := by
        rw [show (12 : ℕ) = 6 + 6 from rfl, pow_add, MulAut.mul_apply]
    _ = (u ^ 6) (c * v) := by rw [hv6]
    _ = (u ^ 6) c * (u ^ 6) v := map_mul _ _ _
    _ = c * (c * v) := by rw [hcfix, hv6]
    _ = v := by rw [← mul_assoc, hV c, one_mul]

end Aux

private theorem pow_twelve_aux' {V : Type*} [Group V] (hc : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) {w w' : V} {α β : MulAut V}
    (hα : ∀ v, α v = v ∨ α v = w * v) (hβ : ∀ v, β v = v ∨ β v = w' * v) :
    (α * β) ^ 12 = 1 := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  ext v
  exact pow_twelve_aux hV hα hβ v



section Transfer

variable {G : Type*} [Group G]

private def conjAutV (V : Subgroup G) (x : G) (hx : x ∈ normalizer (V : Set G)) : MulAut ↥V where
  toFun v := ⟨x * v * x⁻¹, (mem_normalizer_iff.1 hx v).1 v.2⟩
  invFun v := ⟨x⁻¹ * v * x, by
    simpa using (mem_normalizer_iff.1 ((normalizer (V : Set G)).inv_mem hx) v).1 v.2⟩
  left_inv v := by apply Subtype.ext; simp [mul_assoc]
  right_inv v := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

private def conjActV (V : Subgroup G) : ↥(normalizer (V : Set G)) →* MulAut ↥V where
  toFun x := conjAutV V x x.2
  map_one' := by ext v; simp [conjAutV]
  map_mul' x y := by ext v; simp [conjAutV, mul_assoc]

private theorem conjActV_apply (V : Subgroup G) (x : ↥(normalizer (V : Set G))) (v : ↥V) :
    ((conjActV V x v : ↥V) : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

private theorem conjActV_eq_one (V : Subgroup G) (x : ↥(normalizer (V : Set G)))
    (hx : (x : G) ∈ centralizer (V : Set G)) : conjActV V x = 1 := by
  ext v
  rw [conjActV_apply, MulAut.one_apply]
  have := mem_centralizer_iff.1 hx v v.2
  rw [← this]
  group

theorem pow_twelve_mem_centralizer_of_small {V : Subgroup G}
    (hVc : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v) (hV2 : ∀ v ∈ V, v ^ 2 = 1) {g k : G}
    (hg : g ∈ normalizer (V : Set G)) (hk : k ∈ normalizer (V : Set G))
    (hg2 : g ^ 2 ∈ centralizer (V : Set G)) {w : G} (hw : w ∈ V)
    (hgw : ∀ v ∈ V, g * v * g⁻¹ = v ∨ g * v * g⁻¹ = w * v) :
    (g * k⁻¹ * g⁻¹ * k) ^ 12 ∈ centralizer (V : Set G) := by
  let g' : ↥(normalizer (V : Set G)) := ⟨g, hg⟩
  let k' : ↥(normalizer (V : Set G)) := ⟨k, hk⟩
  have hg'2 : conjActV V g' * conjActV V g' = 1 := by
    rw [← map_mul]
    apply conjActV_eq_one
    show g * g ∈ centralizer (V : Set G)
    rwa [← pow_two]
  have hinv : (conjActV V g')⁻¹ = conjActV V g' := inv_eq_of_mul_eq_one_right hg'2
  let w1 : ↥V := ⟨w, hw⟩
  have hαw : ∀ v : ↥V, conjActV V g' v = v ∨ conjActV V g' v = w1 * v := by
    intro v
    rcases hgw v v.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hβw : ∀ v : ↥V, ((conjActV V k')⁻¹ * conjActV V g' * conjActV V k') v = v ∨
      ((conjActV V k')⁻¹ * conjActV V g' * conjActV V k') v = ((conjActV V k')⁻¹ w1) * v := by
    intro v
    have e : ((conjActV V k')⁻¹ * conjActV V g' * conjActV V k') v =
        (conjActV V k')⁻¹ (conjActV V g' (conjActV V k' v)) := rfl
    rcases hαw (conjActV V k' v) with h | h
    · left; rw [e, h]; simp
    · right; rw [e, h, map_mul]; simp
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b => Subtype.ext (hVc a a.2 b b.2)
  have hsq : ∀ v : ↥V, v * v = 1 := fun v => Subtype.ext (by simpa [pow_two] using hV2 v v.2)
  have key := pow_twelve_aux' hcomm hsq hαw hβw
  let κ' : ↥(normalizer (V : Set G)) := g' * k'⁻¹ * g'⁻¹ * k'
  have hρκ : conjActV V κ' =
      conjActV V g' * ((conjActV V k')⁻¹ * conjActV V g' * conjActV V k') := by
    have e1 : conjActV V κ' =
        conjActV V g' * (conjActV V k')⁻¹ * (conjActV V g')⁻¹ * conjActV V k' := by
      simp only [κ', map_mul, map_inv]
    rw [e1, hinv]
    simp only [mul_assoc]
  rw [mem_centralizer_iff]
  intro v hv
  have hpow : conjActV V (κ' ^ 12) = (conjActV V κ') ^ 12 := map_pow _ _ _
  have h1 : conjActV V (κ' ^ 12) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    rw [hpow, hρκ, key, MulAut.one_apply]
  have h2 := congrArg Subtype.val h1
  rw [conjActV_apply] at h2
  have e : ((κ' ^ 12 : ↥(normalizer (V : Set G))) : G) = (g * k⁻¹ * g⁻¹ * k) ^ 12 := rfl
  rw [e] at h2
  calc v * (g * k⁻¹ * g⁻¹ * k) ^ 12
      = ((g * k⁻¹ * g⁻¹ * k) ^ 12 * v * ((g * k⁻¹ * g⁻¹ * k) ^ 12)⁻¹) *
          (g * k⁻¹ * g⁻¹ * k) ^ 12 := by rw [h2]
    _ = (g * k⁻¹ * g⁻¹ * k) ^ 12 * v := by group

end Transfer


end CFSG.LocalAnalysis.RankThreeTheoremC
