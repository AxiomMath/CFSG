module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_normalizer {B : Subgroup G} {s : G}
    (hs : s ∈ normalizer (B : Set G)) (hs2 : s * s ∈ B) {x : G} :
    x ∈ B ⊔ zpowers s ↔ x ∈ B ∨ x * s⁻¹ ∈ B := by
  have hconj : ∀ b ∈ B, s * b * s⁻¹ ∈ B := fun b hb => (mem_normalizer_iff.mp hs b).mp hb
  have hconj' : ∀ b ∈ B, s⁻¹ * b * s ∈ B := fun b hb => (mem_normalizer_iff''.mp hs b).mp hb
  have hsi : s⁻¹ * s⁻¹ ∈ B := by rw [← mul_inv_rev]; exact inv_mem hs2
  let T : Subgroup G :=
    { carrier := {x | x ∈ B ∨ x * s⁻¹ ∈ B}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · right; rw [mul_assoc]; exact mul_mem hx hy
        · right
          have e : x * y * s⁻¹ = (x * s⁻¹) * (s * y * s⁻¹) := by group
          rw [e]; exact mul_mem hx (hconj y hy)
        · left
          have e : x * y = (x * s⁻¹) * (s * (y * s⁻¹) * s⁻¹) * (s * s) := by group
          rw [e]; exact mul_mem (mul_mem hx (hconj _ hy)) hs2
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · right
          have e : x⁻¹ * s⁻¹ = (s⁻¹ * (x * s⁻¹)⁻¹ * s) * (s⁻¹ * s⁻¹) := by group
          rw [e]; exact mul_mem (hconj' _ (inv_mem hx)) hsi }
  constructor
  · intro hx
    have hle : B ⊔ zpowers s ≤ T := by
      refine sup_le (fun b hb => Or.inl hb) ?_
      rw [zpowers_le]
      right
      rw [mul_inv_cancel]
      exact one_mem _
    exact hle hx
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have e : x = (x * s⁻¹) * s := by group
      rw [e]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers s))

theorem card_sup_zpowers_le [Finite G] {B : Subgroup G} {s : G}
    (hs : s ∈ normalizer (B : Set G)) (hs2 : s * s ∈ B) :
    Nat.card (B ⊔ zpowers s : Subgroup G) ≤ 2 * Nat.card B := by
  classical
  have hsub : ((B ⊔ zpowers s : Subgroup G) : Set G) ⊆
      (B : Set G) ∪ (fun b => b * s) '' (B : Set G) := by
    intro x hx
    rcases (mem_sup_zpowers_of_normalizer hs hs2).mp hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨x * s⁻¹, h1, by group⟩
  calc Nat.card (B ⊔ zpowers s : Subgroup G)
      = ((B ⊔ zpowers s : Subgroup G) : Set G).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ((B : Set G) ∪ (fun b => b * s) '' (B : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (B : Set G).ncard + ((fun b => b * s) '' (B : Set G)).ncard :=
        Set.ncard_union_le _ _
    _ = 2 * Nat.card B := by
        rw [Set.ncard_image_of_injective _ (mul_left_injective s), ← Nat.card_coe_set_eq]
        change Nat.card B + Nat.card B = _
        ring

theorem card_sup_closure_le [Finite G] {A : Subgroup G} (S : Finset G)
    (hA : ∀ s ∈ S, s ∈ normalizer (A : Set G)) (hsq : ∀ s ∈ S, s * s ∈ A)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ A) :
    Nat.card (A ⊔ closure (S : Set G) : Subgroup G) ≤ Nat.card A * 2 ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hsS ih =>
    have ih' := ih (fun x hx => hA x (Finset.mem_insert_of_mem hx))
      (fun x hx => hsq x (Finset.mem_insert_of_mem hx))
      (fun x hx y hy => hcomm x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
    set B := A ⊔ closure (S : Set G) with hBdef
    have heq : A ⊔ closure ((insert s S : Finset G) : Set G) = B ⊔ zpowers s := by
      rw [Finset.coe_insert, Set.insert_eq, closure_union, ← zpowers_eq_closure, hBdef]
      rw [sup_comm (zpowers s), sup_assoc]
    have hsA := hA s (Finset.mem_insert_self s S)
    have hsB : s ∈ normalizer (B : Set G) := by
      apply mem_normalizer_of_conj_mem
      have hle : B ≤ B.comap (MulAut.conj s).toMonoidHom := by
        refine sup_le (fun a ha => ?_) ?_
        · exact mem_sup_left ((mem_normalizer_iff.mp hsA a).mp ha)
        · rw [closure_le]
          intro s' hs'
          change s * s' * s⁻¹ ∈ B
          have e : s * s' * s⁻¹ = (s * s' * s⁻¹ * s'⁻¹) * s' := by group
          rw [e]
          exact mul_mem (mem_sup_left (hcomm s (Finset.mem_insert_self s S) s'
            (Finset.mem_insert_of_mem hs'))) (mem_sup_right (subset_closure hs'))
      exact fun b hb => hle hb
    have hs2 : s * s ∈ B := mem_sup_left (hsq s (Finset.mem_insert_self s S))
    rw [heq, Finset.card_insert_of_notMem hsS, pow_succ]
    calc Nat.card (B ⊔ zpowers s : Subgroup G) ≤ 2 * Nat.card B := card_sup_zpowers_le hsB hs2
      _ ≤ 2 * (Nat.card A * 2 ^ S.card) := Nat.mul_le_mul_left _ ih'
      _ = Nat.card A * (2 ^ S.card * 2) := by ring

theorem exists_invariant_of_odd_index [Finite G] {Λ P E : Subgroup G}
    (hodd : Odd (P.relIndex Λ)) (hΛE : Λ ≤ normalizer (E : Set G)) (f : G → ZMod 2)
    (hf : ∀ x ∈ E, ∀ y ∈ E, f (x * y) = f x + f y)
    (hfP : ∀ p ∈ P, ∀ x ∈ E, f (p⁻¹ * x * p) = f x) :
    ∃ F : G → ZMod 2, (∀ x ∈ E, ∀ y ∈ E, F (x * y) = F x + F y) ∧
      (∀ l ∈ Λ, ∀ x ∈ E, F (l⁻¹ * x * l) = F x) ∧
      (∀ x ∈ E, (∀ l ∈ Λ, l * x = x * l) → F x = f x) := by
  classical
  set P' := P.subgroupOf Λ with hP'
  have : Fintype (Λ ⧸ P') := Fintype.ofFinite _
  have hconjE : ∀ c ∈ Λ, ∀ x ∈ E, c⁻¹ * x * c ∈ E := fun c hc x hx =>
    (mem_normalizer_iff''.mp (hΛE hc) x).mp hx
  let F : G → ZMod 2 := fun x => ∑ c : Λ ⧸ P', f (((c.out : Λ) : G)⁻¹ * x * (c.out : Λ))
  refine ⟨F, fun x hx y hy => ?_, fun l hl x hx => ?_, fun x hx hxΛ => ?_⟩
  · simp only [F, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : ((c.out : Λ) : G)⁻¹ * (x * y) * (c.out : Λ) =
        (((c.out : Λ) : G)⁻¹ * x * (c.out : Λ)) * (((c.out : Λ) : G)⁻¹ * y * (c.out : Λ)) := by
      group
    rw [e]
    exact hf _ (hconjE _ (c.out).2 x hx) _ (hconjE _ (c.out).2 y hy)
  · simp only [F]
    let σ : Λ ⧸ P' ≃ Λ ⧸ P' := MulAction.toPerm (⟨l, hl⟩⁻¹ : Λ)
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hmk : (QuotientGroup.mk (((⟨l, hl⟩⁻¹ : Λ) * c.out)) : Λ ⧸ P') = σ c := by
      change _ = (⟨l, hl⟩⁻¹ : Λ) • c
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    have hrel : ((⟨l, hl⟩⁻¹ : Λ) * c.out)⁻¹ * (σ c).out ∈ P' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hmk]
    set p : Λ := ((⟨l, hl⟩⁻¹ : Λ) * c.out)⁻¹ * (σ c).out with hpdef
    have hpP : (p : G) ∈ P := hrel
    have hσ : ((σ c).out : G) = l⁻¹ * (c.out : G) * p := by
      rw [hpdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hσ]
    have e : (l⁻¹ * (c.out : G) * (p : G))⁻¹ * (l⁻¹ * x * l) * (l⁻¹ * (c.out : G) * p) =
        (p : G)⁻¹ * (((c.out : Λ) : G)⁻¹ * x * (c.out : Λ)) * p := by group
    rw [e, hfP _ hpP _ (hconjE _ (c.out).2 _ hx)]
  · simp only [F]
    have hterm : ∀ c : Λ ⧸ P', f (((c.out : Λ) : G)⁻¹ * x * (c.out : Λ)) = f x := by
      intro c
      have := hxΛ _ (c.out).2
      rw [mul_assoc, ← this]
      group
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Λ ⧸ P') : ZMod 2) = 1 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index, hP', ← Subgroup.relIndex]
      exact (ZMod.natCast_eq_one_iff_odd).mpr hodd
    rw [hcard, one_mul]

end CFSG.EvenSmallLie.UnitarySix.YamadaD
