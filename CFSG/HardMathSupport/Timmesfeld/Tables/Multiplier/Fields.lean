module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Open (GriessAllModelsStatement)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem conj_injective_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxz : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut X => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · rw [h] at hxz
    exact Subgroup.mem_bot.mp hxz
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem card_mulAut_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) :
    Nat.card (MulAut X) = Nat.card (Outer X) * Nat.card X := by
  rw [(inner X).card_eq_card_quotient_mul_card_subgroup]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_simple hn)).toEquiv).symm

theorem tables112_T11_ge (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧
      6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6 := by
  obtain ⟨rfl, ⟨e⟩, hcube, h8⟩ := identify_of_two_le_pRank_center hGA hSpM hq hK hp hp2 h2
  have : Group.IsPerfect L := ⟨hq.1⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  refine ⟨rfl, ?_, ?_, ?_⟩
  · refine le_antisymm (CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEab => ?_) h2
    exact (card_le_torsion_center hEab hE).trans hcube.le
  · obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
    let φ : L →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hφ : Function.Surjective φ :=
      e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = Subgroup.center L := by
      ext g
      simp [φ]
    refine six_le_pRank_of_cover φ hφ hker.le (Z := E) (hker ▸ hEZ) (fun z hz => hEab.2 z hz) ?_
    rw [hEcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.center L) := Nat.pow_le_pow_right (by norm_num) h2
  · refine (pRank_mulAut_le hp).trans ?_
    have hn : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq
    refine (pRank_top_le_factorization hp).trans ?_
    rw [card_mulAut_of_simple hn, h8, Nat.card_congr e.toEquiv,
      CFSG.LieType.Multipliers.U43.card_X₀]
    by_contra hlt
    push Not at hlt
    have h7 : 3 ^ 7 ∣ 8 * 3265920 :=
      (hp.pow_dvd_iff_le_factorization (by norm_num)).2 hlt
    revert h7
    norm_num

theorem pRank_le_six (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 6 := by
  obtain ⟨rfl, ⟨e⟩, hcube, -⟩ := identify_of_two_le_pRank_center hGA hSpM hq hK hp hp2 h2
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  let φ : L →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : φ.ker = Subgroup.center L := by
    ext g
    simp [φ]
  let ψ : E →* X₀ := φ.comp E.subtype
  have hψr : ψ.range = E.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hr : Nat.card ψ.range ≤ 3 ^ 4 := by
    rw [hψr]
    exact card_elemAbelian_le_X₀ (CFSG.SectionRank.isElemAbelian_map hE φ)
  have hmem : ∀ x : ψ.ker, ((x.1 : E) : L) ∈ Subgroup.center L := fun x => by
    rw [← hker]
    exact x.2
  have hk : Nat.card ψ.ker ≤ 9 := by
    rw [← hcube]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨((x.1 : E) : L), hmem x⟩, Subtype.ext (hE.2 _ x.1.2)⟩ :
        {z : Subgroup.center L // z ^ 3 = 1})) ?_
    intro x y hxy
    have h := congrArg (fun w : {z : Subgroup.center L // z ^ 3 = 1} => ((w.1 : L))) hxy
    exact Subtype.ext (Subtype.ext h)
  rw [← h1]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 9 * 3 ^ 4 := Nat.mul_le_mul hk hr
    _ = 3 ^ 6 := by norm_num

theorem tables112_T11 (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 6 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6 := by
  obtain ⟨h1, h2', h3, h4⟩ := tables112_T11_ge hGA hSpM hq hK hp hp2 h2
  exact ⟨h1, h2', le_antisymm (pRank_le_six hGA hSpM hq hK hp hp2 h2) h3, h4⟩

theorem tables112_T11_field (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers) :
    ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
        2 ≤ CFSG.Open.pRank p (Subgroup.center L) →
        p = 3 ∧ CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧
          CFSG.Open.pRank 3 (⊤ : Subgroup L) = 6 ∧
          CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6 :=
  fun _ _ _ hq hK _ hp hp2 _ h2 => tables112_T11 hGA hSpM hq hK hp hp2 h2

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
