module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Basic.Finite.Defs
import CFSG.GroupTheory.PerfectCoverProduct

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {Q X S T : Type*} [Group Q] [Group X] [Group S] [Group T]

theorem inf_ker_commutator_comap_eq_bot (η : Q →* X) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center Q) (α : X →* S) (β : X →* T)
    (hαβ : ∀ a : X, α a = 1 → β a = 1 → a = 1) (L : Subgroup X)
    (hL : ⁅L, L⁆ = L) (hLα : L.map α = ⊤) (hLβ : L ≤ β.ker)
    (hcov : ∀ E : Subgroup Q, commutator ↥E = ⊤ → ∀ f : ↥E →* S, Function.Surjective f →
      f.ker ≤ Subgroup.center ↥E → f.ker = ⊥) :
    ⁅L.comap η, L.comap η⁆ ⊓ η.ker = ⊥ := by
  classical
  set Q₁ : Subgroup Q := ⁅L.comap η, L.comap η⁆ with hQ₁
  let f : ↥Q₁ →* S := α.comp (η.comp Q₁.subtype)
  have hQ₁L : Q₁ ≤ L.comap η := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hfs : Function.Surjective f := by
    intro s
    obtain ⟨x, hxL, hxs⟩ : ∃ x ∈ L, α x = s := by
      have hs : s ∈ L.map α := by rw [hLα]; exact Subgroup.mem_top s
      exact hs
    obtain ⟨q, hq, hqx⟩ : x ∈ Q₁.map η := by
      rw [hQ₁, PerfectCover.map_commutator_comap η hη hL]
      exact hxL
    exact ⟨⟨q, hq⟩, by change α (η q) = s; rw [hqx, hxs]⟩
  have hfker : ∀ q : ↥Q₁, f q = 1 ↔ η q = 1 := by
    intro q
    constructor
    · intro h1
      exact hαβ (η q) h1 (hLβ (hQ₁L q.2))
    · intro h1
      change α (η q) = 1
      rw [h1, map_one]
  have hfcenter : f.ker ≤ Subgroup.center ↥Q₁ := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker ((hfker q).1 hq)) g)
  have hperf : Group.IsPerfect ↥Q₁ := PerfectCover.isPerfect_commutator_comap η hη hker hL
  have hbot : f.ker = ⊥ := hcov Q₁ hperf.commutator_eq_top f hfs hfcenter
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.1 hx
  have hx' : (⟨x, hxQ⟩ : Q₁) ∈ f.ker := (hfker ⟨x, hxQ⟩).2 hxZ
  rw [hbot, Subgroup.mem_bot] at hx'
  simpa using congrArg Subtype.val hx'

theorem commutator_prod_factors_eq_top {Q S₁ S₂ : Type*} [Group Q] [Group S₁] [Group S₂]
    (hQ : commutator Q = ⊤) (η : Q →* S₁ × S₂) (hη : Function.Surjective η) :
    commutator S₁ = ⊤ ∧ commutator S₂ = ⊤ := by
  have hQp : Group.IsPerfect Q := ⟨hQ⟩
  constructor
  · have hperf : Group.IsPerfect S₁ :=
      Group.IsPerfect.ofSurjective (f := (MonoidHom.fst S₁ S₂).comp η) (by
        intro s
        obtain ⟨q, hq⟩ := hη (s, 1)
        exact ⟨q, by simpa using congrArg Prod.fst hq⟩)
    exact hperf.commutator_eq_top
  · have hperf : Group.IsPerfect S₂ :=
      Group.IsPerfect.ofSurjective (f := (MonoidHom.snd S₁ S₂).comp η) (by
        intro s
        obtain ⟨q, hq⟩ := hη (1, s)
        exact ⟨q, by simpa using congrArg Prod.snd hq⟩)
    exact hperf.commutator_eq_top

theorem prod_factors_commutator_data {S₁ S₂ : Type*} [Group S₁] [Group S₂]
    (hS₁ : commutator S₁ = ⊤) (hS₂ : commutator S₂ = ⊤) :
    ⁅((⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂)),
        ((⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂))⁆
      = (⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂) ∧
    ⁅((⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂)),
        ((⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂))⁆
      = (⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂) ∧
    ⁅((⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂)),
        ((⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂))⁆ = ⊥ ∧
    ∀ x : S₁ × S₂, ∃ u ∈ (⊤ : Subgroup S₁).prod (⊥ : Subgroup S₂),
      ∃ v ∈ (⊥ : Subgroup S₁).prod (⊤ : Subgroup S₂), x = u * v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_prod_prod, ← commutator_def, hS₁,
      Subgroup.commutator_bot_left]
  · rw [Subgroup.commutator_prod_prod, Subgroup.commutator_bot_left, ← commutator_def, hS₂]
  · rw [Subgroup.commutator_prod_prod, Subgroup.commutator_bot_right,
      Subgroup.commutator_bot_left, Subgroup.bot_prod_bot]
  · intro x
    exact ⟨(x.1, 1), ⟨Subgroup.mem_top x.1, Subgroup.mem_bot.mpr rfl⟩,
      (1, x.2), ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top x.2⟩, by ext <;> simp⟩

theorem ker_eq_bot_of_perfect_central_prod_of_forall {Q S₁ S₂ : Type*} [Group Q] [Group S₁]
    [Group S₂] (hQ : commutator Q = ⊤) (η : Q →* S₁ × S₂) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center Q)
    (hcov₁ : ∀ E : Subgroup Q, commutator ↥E = ⊤ → ∀ f : ↥E →* S₁, Function.Surjective f →
      f.ker ≤ Subgroup.center ↥E → f.ker = ⊥)
    (hcov₂ : ∀ E : Subgroup Q, commutator ↥E = ⊤ → ∀ f : ↥E →* S₂, Function.Surjective f →
      f.ker ≤ Subgroup.center ↥E → f.ker = ⊥) :
    η.ker = ⊥ := by
  classical
  have hQp : Group.IsPerfect Q := ⟨hQ⟩
  obtain ⟨hS₁, hS₂⟩ := commutator_prod_factors_eq_top hQ η hη
  obtain ⟨hL₁perf, hL₂perf, hc, hX⟩ := prod_factors_commutator_data hS₁ hS₂
  set L₁ : Subgroup (S₁ × S₂) := (⊤ : Subgroup S₁).prod ⊥ with hL₁
  set L₂ : Subgroup (S₁ × S₂) := (⊥ : Subgroup S₁).prod ⊤ with hL₂
  have hL₁fst : L₁.map (MonoidHom.fst S₁ S₂) = ⊤ := by
    rw [eq_top_iff]
    intro s _
    exact ⟨(s, 1), by rw [hL₁]; exact ⟨Subgroup.mem_top s, Subgroup.mem_bot.mpr rfl⟩, rfl⟩
  have hL₁snd : L₁ ≤ (MonoidHom.snd S₁ S₂).ker := by
    intro x hx
    rw [hL₁] at hx
    exact (Subgroup.mem_prod.1 hx).2
  have hL₂snd : L₂.map (MonoidHom.snd S₁ S₂) = ⊤ := by
    rw [eq_top_iff]
    intro s _
    exact ⟨(1, s), by rw [hL₂]; exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top s⟩, rfl⟩
  have hL₂fst : L₂ ≤ (MonoidHom.fst S₁ S₂).ker := by
    intro x hx
    rw [hL₂] at hx
    exact (Subgroup.mem_prod.1 hx).1
  have hker₁ : ⁅L₁.comap η, L₁.comap η⁆ ⊓ η.ker = ⊥ :=
    inf_ker_commutator_comap_eq_bot η hη hker (MonoidHom.fst S₁ S₂) (MonoidHom.snd S₁ S₂)
      (fun a ha hb => Prod.ext ha hb) L₁ hL₁perf hL₁fst hL₁snd hcov₁
  have hker₂ : ⁅L₂.comap η, L₂.comap η⁆ ⊓ η.ker = ⊥ :=
    inf_ker_commutator_comap_eq_bot η hη hker (MonoidHom.snd S₁ S₂) (MonoidHom.fst S₁ S₂)
      (fun a ha hb => Prod.ext hb ha) L₂ hL₂perf hL₂snd hL₂fst hcov₂
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a₁, ha₁, a₂, ha₂, hz'⟩ :=
    PerfectCover.exists_eq_mul_commutator_comap η hQp hη hker hL₁perf hL₂perf hc hX z
  have hηa₁ : η a₁ ∈ L₁ :=
    (Subgroup.commutator_le_of_le (K := L₁.comap η) le_rfl le_rfl) ha₁
  have hηa₂ : η a₂ ∈ L₂ :=
    (Subgroup.commutator_le_of_le (K := L₂.comap η) le_rfl le_rfl) ha₂
  have hηz : η a₁ * η a₂ = 1 := by
    rw [← map_mul, ← hz']
    exact hz
  have h₁ : η a₁ = 1 := by
    refine Prod.ext ?_ (Subgroup.mem_bot.mp hηa₁.2)
    have h := congrArg Prod.fst hηz
    simpa [Subgroup.mem_bot.mp hηa₂.1] using h
  have h₂ : η a₂ = 1 := by
    refine Prod.ext (Subgroup.mem_bot.mp hηa₂.1) ?_
    have h := congrArg Prod.snd hηz
    simpa [Subgroup.mem_bot.mp hηa₁.2] using h
  have ha₁' : a₁ ∈ ⁅L₁.comap η, L₁.comap η⁆ ⊓ η.ker := Subgroup.mem_inf.2 ⟨ha₁, h₁⟩
  have ha₂' : a₂ ∈ ⁅L₂.comap η, L₂.comap η⁆ ⊓ η.ker := Subgroup.mem_inf.2 ⟨ha₂, h₂⟩
  rw [hker₁, Subgroup.mem_bot] at ha₁'
  rw [hker₂, Subgroup.mem_bot] at ha₂'
  rw [hz', ha₁', ha₂', mul_one]
  exact Subgroup.one_mem _

theorem ker_eq_bot_of_perfect_central_of_mulEquiv {G : Type*} [Group G] (c : G ≃* S)
    (hcover : ∀ (E : Type) [Group E] [Finite E] (p : E →* S),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥) :
    ∀ (E : Type) [Group E] [Finite E] (p : E →* G),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥ := by
  intro E _ _ p hp hker hcommE
  let q : E →* S := c.toMonoidHom.comp p
  have hq : Function.Surjective q := c.surjective.comp hp
  have hqker : q.ker = p.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change c (p x) = 1 ↔ p x = 1
    exact ⟨fun h => c.injective (by rw [map_one]; exact h), fun h => by rw [h, map_one]⟩
  have hkerq : q.ker ≤ Subgroup.center E := by rw [hqker]; exact hker
  have hqbot : q.ker = ⊥ := hcover E q hq hkerq hcommE
  rw [← hqker, hqbot]

end CFSG.GroupTheory
