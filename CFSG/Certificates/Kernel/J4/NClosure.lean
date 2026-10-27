module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.J4NClosure

open Subgroup Pointwise

variable {G : Type*} [Group G]

@[expose] noncomputable def selProd {n : ℕ} (z : Fin n → G) (e : Fin n → Bool) : G :=
  (List.ofFn fun i => if e i then z i else 1).prod

theorem selProd_succ {n : ℕ} (z : Fin (n + 1) → G) (e : Fin (n + 1) → Bool) :
    selProd z e = (if e 0 then z 0 else 1) * selProd (z ∘ Fin.succ) (e ∘ Fin.succ) := by
  unfold selProd
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem selProd_false {n : ℕ} (z : Fin n → G) : selProd z (fun _ => false) = 1 := by
  unfold selProd
  simp

theorem selProd_commute {n : ℕ} (z : Fin n → G) (e : Fin n → Bool) {a : G}
    (h : ∀ i, Commute (z i) a) : Commute (selProd z e) a := by
  unfold selProd
  refine Commute.list_prod_left _ _ fun b hb => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hb
  split_ifs
  · exact h i
  · exact Commute.one_left a

variable {n : ℕ} {z : Fin n → G}

theorem selProd_mul_z (hsq : ∀ i, z i * z i = 1) (hc : ∀ i j, Commute (z i) (z j)) :
    ∀ (e : Fin n → Bool) (j : Fin n), selProd z e * z j = selProd z (Function.update e j (!e j)) := by
  induction n with
  | zero => exact fun _ j => j.elim0
  | succ n ih =>
    intro e j
    have ih' := ih (z := z ∘ Fin.succ) (fun i => hsq _) (fun i j => hc _ _)
    rw [selProd_succ, selProd_succ z]
    refine Fin.cases ?_ (fun j => ?_) j
    · have hP := selProd_commute (z ∘ Fin.succ) (e ∘ Fin.succ) (fun i => hc i.succ 0)
      have e1 : Function.update e 0 (!e 0) ∘ Fin.succ = e ∘ Fin.succ := by
        funext i
        simp
      rw [e1, mul_assoc, hP.eq, ← mul_assoc, Function.update_self]
      congr 1
      cases e 0 <;> simp [hsq]
    · have h' : selProd (z ∘ Fin.succ) (e ∘ Fin.succ) * z j.succ =
          selProd (z ∘ Fin.succ) (Function.update (e ∘ Fin.succ) j (!e j.succ)) :=
        ih' (e ∘ Fin.succ) j
      rw [mul_assoc, h', Function.update_of_ne (Fin.succ_ne_zero j).symm,
        Function.update_comp_eq_of_injective _ (Fin.succ_injective n)]

theorem selProd_sq (hsq : ∀ i, z i * z i = 1) (hc : ∀ i j, Commute (z i) (z j)) :
    ∀ e : Fin n → Bool, selProd z e * selProd z e = 1 := by
  induction n with
  | zero => exact fun e => by simp [selProd]
  | succ n ih =>
    intro e
    have hP := selProd_commute (z ∘ Fin.succ) (e ∘ Fin.succ) (a := if e 0 then z 0 else 1)
      (fun i => by
        split_ifs
        · exact hc i.succ 0
        · exact Commute.one_right _)
    rw [selProd_succ, mul_assoc, ← mul_assoc (selProd _ _), hP.eq, mul_assoc,
      ih (z := z ∘ Fin.succ) (fun i => hsq _) (fun i j => hc _ _), mul_one]
    split_ifs
    · exact hsq 0
    · exact mul_one 1

theorem closure_sub_range (hsq : ∀ i, z i * z i = 1) (hc : ∀ i j, Commute (z i) (z j)) :
    ((closure (Set.range z) : Subgroup G) : Set G) ⊆ Set.range (selProd z) := by
  intro a ha
  have hinv : ∀ j, (z j)⁻¹ = z j := fun j => inv_eq_of_mul_eq_one_right (hsq j)
  induction ha using closure_induction_right with
  | one => exact ⟨fun _ => false, selProd_false z⟩
  | mul_right x _ y hy ih =>
    obtain ⟨e, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    exact ⟨_, (selProd_mul_z hsq hc e j).symm⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨e, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    rw [hinv]
    exact ⟨_, (selProd_mul_z hsq hc e j).symm⟩

theorem elemAb (hsq : ∀ i, z i * z i = 1) (hc : ∀ i j, Commute (z i) (z j)) :
    (∀ a ∈ closure (Set.range z), ∀ b ∈ closure (Set.range z), a * b = b * a) ∧
    (∀ a ∈ closure (Set.range z), a * a = 1) ∧ Finite (closure (Set.range z)) ∧
    Nat.card (closure (Set.range z)) ≤ 2 ^ n := by
  have hs := closure_sub_range hsq hc
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, ?_, ?_⟩
  · obtain ⟨e, rfl⟩ := hs ha
    obtain ⟨e', rfl⟩ := hs hb
    exact (selProd_commute z e fun i =>
      (selProd_commute z e' fun j => hc j i).symm).eq
  · obtain ⟨e, rfl⟩ := hs ha
    exact selProd_sq hsq hc e
  · exact ((Set.finite_range _).subset hs).to_subtype
  · calc Nat.card (closure (Set.range z)) ≤ Nat.card (Set.range (selProd z)) :=
          Nat.card_mono (Set.finite_range _) hs
      _ ≤ Nat.card (Fin n → Bool) := Finite.card_range_le _
      _ = 2 ^ n := by simp [Nat.card_eq_fintype_card]

theorem mem_normalizer_of_conj {S : Set G} [Finite (closure S)] {g : G}
    (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ closure S) : g ∈ normalizer (closure S) := by
  have fwd : ∀ h ∈ closure S, g⁻¹ * h * g ∈ closure S := by
    intro h hh
    induction hh using closure_induction with
    | mem s hs => exact hg s hs
    | one => simp [one_mem]
    | mul a b _ _ ha hb =>
      have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  rw [mem_normalizer_iff'']
  intro h
  refine ⟨fwd h, fun hh => ?_⟩
  let φ : closure S → closure S := fun v => ⟨g⁻¹ * v * g, fwd v v.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa [φ] using this)
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨_, hh⟩
  have := congrArg Subtype.val hv
  have hvh : (v : G) = h := by simpa [φ] using this
  rw [← hvh]
  exact v.2

theorem nclosure_bound {n : ℕ} (x y z : G) (w : Fin (n + 1) → G)
    (hw : ∀ i, w i ∈ closure ({x, y} : Set G)) (hw0 : w 0 = 1)
    (hsq : ∀ i, ((w i)⁻¹ * z * w i) * ((w i)⁻¹ * z * w i) = 1)
    (hc : ∀ i j, Commute ((w i)⁻¹ * z * w i) ((w j)⁻¹ * z * w j))
    (hx : ∀ i, x⁻¹ * ((w i)⁻¹ * z * w i) * x ∈ closure (Set.range fun i => (w i)⁻¹ * z * w i))
    (hy : ∀ i, y⁻¹ * ((w i)⁻¹ * z * w i) * y ∈ closure (Set.range fun i => (w i)⁻¹ * z * w i)) :
    closure (Set.range fun i => (w i)⁻¹ * z * w i) ≤ closure ({x, y, z} : Set G) ∧
    closure ({x, y, z} : Set G) ≤ normalizer (closure (Set.range fun i => (w i)⁻¹ * z * w i)) ∧
    Nat.card (closure ({x, y, z} : Set G)) ≤ 2 ^ (n + 1) * Nat.card (closure ({x, y} : Set G)) := by
  set zi : Fin (n + 1) → G := fun i => (w i)⁻¹ * z * w i with hzi
  set V := closure (Set.range zi)
  set N := closure ({x, y} : Set G)
  set K := closure ({x, y, z} : Set G)
  obtain ⟨-, -, hfin, hcard⟩ := elemAb (z := zi) hsq hc
  have hz : z ∈ V := by
    have : zi 0 = z := by simp [hzi, hw0]
    rw [← this]
    exact subset_closure ⟨0, rfl⟩
  have hNK : N ≤ K := closure_mono (by intro a ha; rcases ha with rfl | rfl <;> simp)
  have hzK : z ∈ K := subset_closure (by simp)
  have hVK : V ≤ K := by
    refine closure_le _ |>.2 ?_
    rintro _ ⟨i, rfl⟩
    exact mul_mem (mul_mem (inv_mem (hNK (hw i))) hzK) (hNK (hw i))
  have hgen : ∀ g, (∀ i, g⁻¹ * zi i * g ∈ V) → g ∈ normalizer V := fun g hg =>
    mem_normalizer_of_conj (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact hg i)
  have hxN := hgen x hx
  have hyN := hgen y hy
  have hNnorm : N ≤ normalizer V := by
    refine closure_le _ |>.2 ?_
    intro a ha
    rcases ha with rfl | rfl
    · exact hxN
    · exact hyN
  have hKnorm : K ≤ normalizer V := by
    refine closure_le _ |>.2 ?_
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact hxN
    · exact hyN
    · exact le_normalizer hz
  refine ⟨hVK, hKnorm, ?_⟩
  have hKVN : K ≤ V ⊔ N := by
    refine closure_le _ |>.2 ?_
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact le_sup_right (a := V) (subset_closure (by simp))
    · exact le_sup_right (a := V) (subset_closure (by simp))
    · exact le_sup_left (b := N) hz
  have hset : ((V ⊔ N : Subgroup G) : Set G) = (V : Set G) * (N : Set G) :=
    coe_mul_of_right_le_normalizer_left V N hNnorm
  rcases finite_or_infinite N with hN | hN
  · have hVNfin : Finite (V ⊔ N : Subgroup G) := by
      have : ((V : Set G) * (N : Set G)).Finite :=
        Set.Finite.mul (Set.toFinite (V : Set G)) (Set.toFinite (N : Set G))
      rw [← hset] at this
      exact this.to_subtype
    calc Nat.card K ≤ Nat.card (V ⊔ N : Subgroup G) := card_le_of_le hKVN
      _ = Nat.card ((V : Set G) * (N : Set G)) := by
          rw [← hset]
          rfl
      _ ≤ Nat.card V * Nat.card N := Set.natCard_mul_le
      _ ≤ 2 ^ (n + 1) * Nat.card N := Nat.mul_le_mul_right _ hcard
  · have : Infinite K := Infinite.of_injective _ (inclusion_injective hNK)
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end CFSG.Certificates.J4NClosure

end
