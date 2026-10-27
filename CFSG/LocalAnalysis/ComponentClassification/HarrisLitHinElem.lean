module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinRankSix

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

variable {G : Type*} [Group G]

@[expose] def ElemTwo (E : Subgroup G) : Prop :=
  (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1

theorem elemTwo_closure {S : Set G} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) : ElemTwo (closure S) := by
  have hc : ∀ x ∈ closure S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have hle : closure S ≤ centralizer {y} := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact hcomm z hz y hy
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hcc : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    have hle : closure S ≤ centralizer {x} := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hc x hx z hz).symm
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  refine ⟨hcc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hcc x hx y hy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem elemTwo_zpowers {x : G} (hx : x * x = 1) : ElemTwo (zpowers x) := by
  rw [zpowers_eq_closure]
  exact elemTwo_closure (fun a ha b hb => by
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]) (fun a ha => by
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hx)

theorem card_zpowers_of_sq {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (zpowers x) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1

theorem elemTwo_sup [Finite G] {A B : Subgroup G} (hA : ElemTwo A) (hB : ElemTwo B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    ElemTwo (A ⊔ B) ∧ Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  constructor
  · rw [sup_eq_closure]
    refine elemTwo_closure ?_ ?_
    · rintro x (hx | hx) y (hy | hy)
      · exact hA.1 x hx y hy
      · exact hAB x hx y hy
      · exact (hAB y hy x hx).symm
      · exact hB.1 x hx y hy
    · rintro x (hx | hx)
      · exact hA.2 x hx
      · exact hB.2 x hx
  · rw [← Nat.card_prod]
    let f : ↥A × ↥B → ↥(A ⊔ B) := fun ab =>
      ⟨(ab.1 : G) * ab.2, mul_mem (mem_sup_left ab.1.2) (mem_sup_right ab.2.2)⟩
    refine Nat.card_le_card_of_injective f fun ⟨a, b⟩ ⟨a', b'⟩ h => ?_
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hinf, mem_bot] at hmem
    have ha : (a : G) = a' := by
      rw [← one_mul (a : G), ← mul_inv_cancel (a' : G), mul_assoc, hmem, mul_one]
    have hb : (b : G) = b' := by
      rw [ha] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem elemTwo_pair [Finite G] {x y : G} (hxy : x * y = y * x) (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    ElemTwo (zpowers x ⊔ zpowers y) ∧ 4 ≤ Nat.card ↥(zpowers x ⊔ zpowers y) := by
  have hpow : ∀ {z : G}, z * z = 1 → ∀ k : ℤ, z ^ k = 1 ∨ z ^ k = z := by
    intro z hz k
    by_cases hz1 : z = 1
    · left
      rw [hz1, one_zpow]
    · have ho : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
      rw [← zpow_mod_orderOf, ho]
      rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
      · left
        rw [Nat.cast_ofNat, hk2, zpow_zero]
      · right
        rw [Nat.cast_ofNat, hk2, zpow_one]
  have hzx : ∀ a ∈ zpowers x, a = 1 ∨ a = x := by
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact hpow hx k
  have hinf : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨hax, hay⟩
    rw [mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hay
    rcases hzx _ hax with h | h
    · exact h
    · exfalso
      rcases hpow hy k with h' | h'
      · exact hx1 (by rw [← h, h'])
      · exact hne (by rw [← h, h'])
  have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ zpowers y, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow hxy i j).eq
  obtain ⟨hE, hcard⟩ := elemTwo_sup (elemTwo_zpowers hx) (elemTwo_zpowers hy) hcomm hinf
  refine ⟨hE, ?_⟩
  rw [card_zpowers_of_sq hx hx1, card_zpowers_of_sq hy hy1] at hcard
  omega

theorem not_sectionalTwoRankLE_of_equiv {Y P : Type*} [Group Y] [Group P] (e : Y ≃* P)
    {C : Subgroup Y} {C' : Subgroup P} (hCC' : C.map e.toMonoidHom = C') {E : Subgroup P}
    (hEC : E ≤ C') (hE : ElemTwo E) {r : ℕ} (hcard : 2 ^ r < Nat.card E) :
    ¬ GH74.SectionalTwoRankLE ↥C r := by
  have hEr : E ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  obtain ⟨hcardE, hc, hs⟩ := elemAbelian_comap e.injective hEr hE.1 hE.2
  refine not_sectionalTwoRankLE_of_le (E := E.comap e.toMonoidHom) ?_ hc
    (fun x hx => by rw [pow_two]; exact hs x hx) (by rw [hcardE]; exact hcard)
  intro y hy
  have : e y ∈ C' := hEC hy
  rw [← hCC'] at this
  obtain ⟨c, hc, hce⟩ := this
  rw [← e.injective hce]
  exact hc

end CFSG.ComponentClassification.HarrisLit.Hin
