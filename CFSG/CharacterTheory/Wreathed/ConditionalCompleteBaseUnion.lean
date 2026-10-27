module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseCount
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseGeneric

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

theorem pair_labels_facts {X : Type*} {γ : Fin 4 → X} (hγ : Function.Injective γ)
    {P Q : Fin 2 → X} (h0 : (P 0 = γ 0 ∧ Q 0 = γ 1) ∨ (P 0 = γ 1 ∧ Q 0 = γ 0))
    (h1 : (P 1 = γ 2 ∧ Q 1 = γ 3) ∨ (P 1 = γ 3 ∧ Q 1 = γ 2)) :
    Function.Injective P ∧ Function.Injective Q ∧ (∀ e e', P e ≠ Q e') ∧
      (∀ e, (∃ l, P e = γ l) ∧ ∃ l, Q e = γ l) ∧ ∀ l, ∃ e, γ l = P e ∨ γ l = Q e := by
  have key : ∃ ip iq : Fin 2 → Fin 4, (∀ e, P e = γ (ip e)) ∧ (∀ e, Q e = γ (iq e)) ∧
      Function.Injective ip ∧ Function.Injective iq ∧ (∀ e e', ip e ≠ iq e') ∧
      ∀ l, ∃ e, l = ip e ∨ l = iq e := by
    have hfin : ∀ (ip iq : Fin 2 → Fin 4), P 0 = γ (ip 0) → P 1 = γ (ip 1) → Q 0 = γ (iq 0) →
        Q 1 = γ (iq 1) → (∀ e, P e = γ (ip e)) ∧ ∀ e, Q e = γ (iq e) := by
      intro ip iq a b c d
      refine ⟨fun e => ?_, fun e => ?_⟩ <;> fin_cases e <;> assumption
    rcases h0 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h1 with ⟨c, d⟩ | ⟨c, d⟩
    · exact ⟨![0, 2], ![1, 3], (hfin ![0, 2] ![1, 3] a c b d).1,
        (hfin ![0, 2] ![1, 3] a c b d).2, by decide⟩
    · exact ⟨![0, 3], ![1, 2], (hfin ![0, 3] ![1, 2] a c b d).1,
        (hfin ![0, 3] ![1, 2] a c b d).2, by decide⟩
    · exact ⟨![1, 2], ![0, 3], (hfin ![1, 2] ![0, 3] a c b d).1,
        (hfin ![1, 2] ![0, 3] a c b d).2, by decide⟩
    · exact ⟨![1, 3], ![0, 2], (hfin ![1, 3] ![0, 2] a c b d).1,
        (hfin ![1, 3] ![0, 2] a c b d).2, by decide⟩
  obtain ⟨ip, iq, hP, hQ, hip, hiq, hpq, hcov⟩ := key
  refine ⟨fun e e' h => hip (hγ (by rw [← hP, ← hP]; exact h)),
    fun e e' h => hiq (hγ (by rw [← hQ, ← hQ]; exact h)),
    fun e e' h => hpq e e' (hγ (by rw [← hP, ← hQ]; exact h)),
    fun e => ⟨⟨ip e, hP e⟩, ⟨iq e, hQ e⟩⟩, fun l => ?_⟩
  obtain ⟨e, he | he⟩ := hcov l
  · exact ⟨e, Or.inl (by rw [hP, he])⟩
  · exact ⟨e, Or.inr (by rw [hQ, he])⟩

theorem pair_labels_image {X : Type*} [DecidableEq X] {γ : Fin 4 → X} {P Q : Fin 2 → X}
    (h0 : (P 0 = γ 0 ∧ Q 0 = γ 1) ∨ (P 0 = γ 1 ∧ Q 0 = γ 0))
    (h1 : (P 1 = γ 2 ∧ Q 1 = γ 3) ∨ (P 1 = γ 3 ∧ Q 1 = γ 2)) :
    ({P 0, Q 0, P 1, Q 1} : Finset X) = Finset.univ.image γ := by
  have himg : Finset.univ.image γ = {γ 0, γ 1, γ 2, γ 3} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨l, rfl⟩
      fin_cases l <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [himg]
  rcases h0 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h1 with ⟨c, d⟩ | ⟨c, d⟩ <;> rw [a, b, c, d] <;>
    ext x <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ}
  {J : Finset ℕ} {χ : ℕ → ι} {y₀ C : ι → ℤ} {xj : ℕ → ι → ℤ} {M : ℕ} {γ : ℕ → Fin 4 → ι}
  {P Q : ℕ → Fin 2 → ι} {β : Type*} {V : Finset β} {ψ : β → ι}

theorem complete_base_union (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj)
    (hγB : ∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∈ B)
    (hγinj : ∀ r ∈ Finset.Ico 1 M, Function.Injective (γ r))
    (hγcore : ∀ r ∈ Finset.Ico 1 M, ∀ l,
      γ r l ≠ p ∧ γ r l ≠ A ∧ γ r l ≠ Bq ∧ γ r l ≠ Dq ∧ γ r l ≠ ω)
    (hγodd : ∀ r ∈ Finset.Ico 1 M, ∀ l, ∀ j ∈ J, γ r l ≠ χ j)
    (hdisj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l')
    (hPQ : ∀ r ∈ Finset.Ico 1 M,
      ((P r 0 = γ r 0 ∧ Q r 0 = γ r 1) ∨ (P r 0 = γ r 1 ∧ Q r 0 = γ r 0)) ∧
        ((P r 1 = γ r 2 ∧ Q r 1 = γ r 3) ∨ (P r 1 = γ r 3 ∧ Q r 1 = γ r 2)))
    (hψinj : Set.InjOn ψ V)
    (hψ : ∀ I ∈ V, ψ I ∈ B ∧ Outside0 p A Bq Dq ω J χ (ψ I) ∧
      ∀ t ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ t l)
    (hexh : ∀ φ ∈ B, φ = p ∨ φ = A ∨ φ = Bq ∨ φ = Dq ∨ φ = ω ∨ (∃ j ∈ J, φ = χ j) ∨
      (∃ t ∈ Finset.Ico 1 M, ∃ l, φ = γ t l) ∨ ∃ I ∈ V, φ = ψ I)
    {R : Type*} (d : ι → R) {δ b d' Δ : R} (hdχ : ∀ j ∈ J, d (χ j) = δ)
    (hdP : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (P r e) = b)
    (hdQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (Q r e) = d') (hdψ : ∀ I ∈ V, d (ψ I) = Δ) :
    B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
        ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) ∪
        ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2) ∪
        V.image ψ ∧
      B.card = 5 + J.card + 4 * (M - 1) + V.card ∧
      Multiset.map d B.val = {d p, d A, d Bq, d Dq, d ω} + Multiset.replicate J.card δ +
        Multiset.replicate (2 * (M - 1)) b + Multiset.replicate (2 * (M - 1)) d' +
        Multiset.replicate V.card Δ := by
  have hL := fun r (hr : r ∈ Finset.Ico 1 M) =>
    pair_labels_facts (hγinj r hr) (hPQ r hr).1 (hPQ r hr).2
  have hPγ : ∀ r ∈ Finset.Ico 1 M, ∀ e, ∃ l, P r e = γ r l := fun r hr e => ((hL r hr).2.2.2.1 e).1
  have hQγ : ∀ r ∈ Finset.Ico 1 M, ∀ e, ∃ l, Q r e = γ r l := fun r hr e => ((hL r hr).2.2.2.1 e).2
  have hmem5 : ∀ φ, φ ∈ ({p, A, Bq, Dq, ω} : Finset ι) ↔
      φ = p ∨ φ = A ∨ φ = Bq ∨ φ = Dq ∨ φ = ω := fun φ => by simp
  have hB : B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2) ∪
      V.image ψ := by
    ext φ
    simp only [Finset.mem_union, hmem5, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
      and_true, Prod.exists]
    constructor
    · intro hφ
      rcases hexh φ hφ with h | h | h | h | h | ⟨j, hj, rfl⟩ | ⟨t, ht, l, rfl⟩ | ⟨I, hI, rfl⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
      · obtain ⟨e, he | he⟩ := (hL t ht).2.2.2.2 l
        · exact Or.inl (Or.inl (Or.inr ⟨t, e, ht, he.symm⟩))
        · exact Or.inl (Or.inr ⟨t, e, ht, he.symm⟩)
      · exact Or.inr ⟨I, hI, rfl⟩
    · rintro ((((h | ⟨j, hj, rfl⟩) | ⟨r, e, hr, rfl⟩) | ⟨r, e, hr, rfl⟩) | ⟨I, hI, rfl⟩)
      · rcases h with rfl | rfl | rfl | rfl | rfl
        exacts [hS.hp, hS.hA, hS.hBq, hS.hDq, hS.hω]
      · exact hS.hχB j hj
      · obtain ⟨l, hl⟩ := hPγ r hr e
        rw [hl]
        exact hγB r hr l
      · obtain ⟨l, hl⟩ := hQγ r hr e
        rw [hl]
        exact hγB r hr l
      · exact (hψ I hI).1
  have hPinj : Set.InjOn (fun rl : ℕ × Fin 2 => P rl.1 rl.2)
      ↑(Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))) := by
    rintro ⟨r, e⟩ hr ⟨r', e'⟩ hr' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
      Set.mem_univ, and_true] at hr hr'
    simp only at h
    by_cases hrr : r = r'
    · subst hrr
      rw [(hL r hr).1 h]
    · obtain ⟨l, hl⟩ := hPγ r hr e
      obtain ⟨l', hl'⟩ := hPγ r' hr' e'
      exact absurd (hl.symm.trans (h.trans hl')) (hdisj r hr r' hr' hrr l l')
  have hQinj : Set.InjOn (fun rl : ℕ × Fin 2 => Q rl.1 rl.2)
      ↑(Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))) := by
    rintro ⟨r, e⟩ hr ⟨r', e'⟩ hr' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
      Set.mem_univ, and_true] at hr hr'
    simp only at h
    by_cases hrr : r = r'
    · subst hrr
      rw [(hL r hr).2.1 h]
    · obtain ⟨l, hl⟩ := hQγ r hr e
      obtain ⟨l', hl'⟩ := hQγ r' hr' e'
      exact absurd (hl.symm.trans (h.trans hl')) (hdisj r hr r' hr' hrr l l')
  have hq : [p, A, Bq, Dq, ω].Nodup := by
    simp [List.nodup_cons, hS.hAp.symm, hS.hBp.symm, hS.hDp.symm, hS.hωp.symm, hS.hBA.symm,
      hS.hDA.symm, hS.hωA.symm, hS.hDB.symm, hS.hωB.symm, hS.hωD.symm]
  have hcoreγ : ∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∉ ({p, A, Bq, Dq, ω} : Finset ι) := by
    intro r hr l h
    obtain ⟨n1, n2, n3, n4, n5⟩ := hγcore r hr l
    rcases (hmem5 _).mp h with h | h | h | h | h <;> contradiction
  have hχγ : ∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∉ J.image χ := by
    intro r hr l h
    obtain ⟨j, hj, hjl⟩ := Finset.mem_image.mp h
    exact hγodd r hr l j hj hjl.symm
  have hd₁ : Disjoint ({p, A, Bq, Dq, ω} : Finset ι) (J.image χ) := by
    rw [Finset.disjoint_left]
    intro φ h1 h2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨n1, n2, n3, n4, n5⟩ := hS.hχcore j hj
    rcases (hmem5 _).mp h1 with h | h | h | h | h <;> contradiction
  have hd₂ : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) := by
    rw [Finset.disjoint_right]
    intro φ h2 h1
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp h2
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨l, hl⟩ := hPγ r hr e
    simp only at h1
    rw [hl] at h1
    rcases Finset.mem_union.mp h1 with h | h
    · exact hcoreγ r hr l h
    · exact hχγ r hr l h
  have hd₃ : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2) := by
    rw [Finset.disjoint_right]
    intro φ h2 h1
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp h2
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨l, hl⟩ := hQγ r hr e
    simp only at h1
    rcases Finset.mem_union.mp h1 with h | h
    · rw [hl] at h
      rcases Finset.mem_union.mp h with h | h
      · exact hcoreγ r hr l h
      · exact hχγ r hr l h
    · obtain ⟨⟨r', e'⟩, hre', he⟩ := Finset.mem_image.mp h
      have hr' := (Finset.mem_product.mp hre').1
      simp only at he
      by_cases hrr : r' = r
      · subst hrr
        exact (hL r' hr).2.2.1 e' e he
      · obtain ⟨l', hl'⟩ := hPγ r' hr' e'
        exact hdisj r' hr' r hr hrr l' l (hl'.symm.trans (he.trans hl))
  have hd₄ : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => P rl.1 rl.2) ∪
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun rl => Q rl.1 rl.2)
      (V.image ψ) := by
    rw [Finset.disjoint_right]
    intro φ h2 h1
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨-, ⟨n1, n2, n3, n4, n5, n6⟩, n7⟩ := hψ I hI
    rcases Finset.mem_union.mp h1 with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · rcases (hmem5 _).mp h with h | h | h | h | h <;> contradiction
        · obtain ⟨j, hj, hjI⟩ := Finset.mem_image.mp h
          exact n6 j hj hjI.symm
      · obtain ⟨⟨r, e⟩, hre, he⟩ := Finset.mem_image.mp h
        obtain ⟨l, hl⟩ := hPγ r (Finset.mem_product.mp hre).1 e
        exact n7 r (Finset.mem_product.mp hre).1 l (he.symm.trans hl)
    · obtain ⟨⟨r, e⟩, hre, he⟩ := Finset.mem_image.mp h
      obtain ⟨l, hl⟩ := hQγ r (Finset.mem_product.mp hre).1 e
      exact n7 r (Finset.mem_product.mp hre).1 l (he.symm.trans hl)
  obtain ⟨hcard, hmul⟩ := card_and_degree_multiset B d p A Bq Dq ω hq χ J hS.hχinj P Q hPinj
    hQinj V ψ hψinj hd₁ hd₂ hd₃ hd₄ hB hdχ hdP hdQ hdψ
  exact ⟨hB, hcard, hmul⟩

end CFSG.Wreathed.ConditionalCompleteBase
