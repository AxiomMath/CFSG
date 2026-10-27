module

public import CFSG.LocalAnalysis.SectionRank.QTK.SectionLiftB
public import CFSG.Quasithin.Background.A3FactsRank

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.Quasithin.A3Facts

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem le_pRank_of_le {p : ℕ} (hp : 1 < p) {M E : Subgroup X} (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p M := CFSG.SectionRank.le_pRank hp hEM hE hk

theorem exists_eq_pRank {p : ℕ} (hp : 1 < p) (M : Subgroup X) :
    ∃ E : Subgroup X, E ≤ M ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ CFSG.Open.pRank p M := CFSG.SectionRank.exists_pRank hp M

theorem pRank_le_pRank_map {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : 1 < p) (f : X →* Y)
    (hf : Function.Injective f) (M : Subgroup X) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M.map f) := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEM, hE, hEk⟩ := hk
  refine le_pRank_of_le hp (Subgroup.map_mono hEM) (isElemAbelian_map f hE) ?_
  rw [Subgroup.card_map_of_injective hf, hEk]

theorem pRank_normalizer_le_of_mulEquiv {Y : Type*} [Group Y] [Finite Y] (e : X ≃* Y) {p : ℕ}
    (hp : 1 < p) (h : ∀ R : Subgroup Y, R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank p (normalizer (R : Set Y)) ≤ 2) (R : Subgroup X) (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) : CFSG.Open.pRank p (normalizer (R : Set X)) ≤ 2 := by
  have hR' : R.map e.toMonoidHom ≠ ⊥ := fun hb =>
    hR ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
  calc CFSG.Open.pRank p (normalizer (R : Set X))
      ≤ CFSG.Open.pRank p ((normalizer (R : Set X)).map e.toMonoidHom) :=
        pRank_le_pRank_map hp e.toMonoidHom e.injective _
    _ ≤ CFSG.Open.pRank p (normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y)) := by
        refine csSup_le' fun k hk => ?_
        obtain ⟨E, hEM, hE, hEk⟩ := hk
        exact le_pRank_of_le hp (hEM.trans (Subgroup.le_normalizer_map _)) hE hEk
    _ ≤ 2 := h _ hR' (hR2.map _)

end Rank

section Prod

variable {A B : Type*} [Group A] [Group B]

theorem isElemAbelian_prod {p : ℕ} {E₁ : Subgroup A} {E₂ : Subgroup B}
    (h₁ : CFSG.Open.IsElemAbelian p E₁) (h₂ : CFSG.Open.IsElemAbelian p E₂) :
    CFSG.Open.IsElemAbelian p (E₁.prod E₂) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have ha := congrArg Subtype.val (h₁.1.is_comm.comm ⟨a.1.1, a.2.1⟩ ⟨b.1.1, b.2.1⟩)
    have hb := congrArg Subtype.val (h₂.1.is_comm.comm ⟨a.1.2, a.2.2⟩ ⟨b.1.2, b.2.2⟩)
    exact Prod.ext ha hb
  · exact Prod.ext (h₁.2 _ hx.1) (h₂.2 _ hx.2)

theorem isPGroup_prod_bot {R : Subgroup A} (hR : IsPGroup 2 R) :
    IsPGroup 2 (R.prod (⊥ : Subgroup B)) := by
  intro x
  obtain ⟨k, hk⟩ := hR ⟨x.1.1, x.2.1⟩
  refine ⟨k, Subtype.ext (Prod.ext ?_ ?_)⟩
  · simpa using congrArg Subtype.val hk
  · have h2 : x.1.2 = 1 := Subgroup.mem_bot.mp x.2.2
    simp [h2]

theorem prod_le_normalizer_prod_bot {R₁ E₁ : Subgroup A} (h : E₁ ≤ normalizer (R₁ : Set A))
    (E₂ : Subgroup B) :
    E₁.prod E₂ ≤ normalizer ((R₁.prod (⊥ : Subgroup B) : Subgroup (A × B)) : Set (A × B)) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  have hR := mem_normalizer_iff.mp (h hg.1) x.1
  simp only [Subgroup.mem_prod, Subgroup.mem_bot, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
    Prod.snd_inv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hR.mp h1, by rw [h2, mul_one, mul_inv_cancel]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hR.mpr h1, ?_⟩
    have := congrArg (fun z => g.2⁻¹ * z * g.2) h2
    simpa [mul_assoc] using this

end Prod

end CFSG.SectionRank.QTK
