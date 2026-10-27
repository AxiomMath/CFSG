module

public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.RankThree.PartOne.SEITZ3 Subgroup

theorem index_modEq_one_of_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A S : Subgroup G} (hSA : S ≤ A) (hSp : IsPGroup p ↥S) (hSidx : ¬ p ∣ S.index)
    (hNS : ∀ n ∈ normalizer (S : Set G), n ∈ A) : A.index ≡ 1 [MOD p] := by
  have hmod : Nat.card (G ⧸ A) ≡ Nat.card (MulAction.fixedPoints S (G ⧸ A)) [MOD p] :=
    hSp.card_modEq_card_fixedPoints (G ⧸ A)
  have hfixed_iff : ∀ g : G, ((g : G ⧸ A) ∈ MulAction.fixedPoints S (G ⧸ A)) ↔
      ∀ s ∈ S, g⁻¹ * s * g ∈ A := by
    intro g
    rw [MulAction.mem_fixedPoints]
    have key : ∀ s : ↥S, s • (g : G ⧸ A) = (g : G ⧸ A) ↔ g⁻¹ * (s : G)⁻¹ * g ∈ A := by
      intro s
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have e : ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
      rw [e]
    simp only [key]
    constructor
    · intro h s hs
      have h1 := h ⟨s⁻¹, S.inv_mem hs⟩
      have e2 : g⁻¹ * (((⟨s⁻¹, S.inv_mem hs⟩ : ↥S) : G))⁻¹ * g = g⁻¹ * s * g := by
        simp
      rwa [e2] at h1
    · intro h s
      exact h _ (S.inv_mem s.2)
  have hfix : MulAction.fixedPoints S (G ⧸ A) = {((1 : G) : G ⧸ A)} := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Set.mem_singleton_iff, hfixed_iff, QuotientGroup.eq]
    constructor
    · intro hg
      obtain ⟨m, hmM, hmn⟩ := exists_mem_normalizer_of_conj_le hSA hSp hSidx hg
      have hgm : g * m ∈ A := hNS _ hmn
      have h6 := A.mul_mem hgm (A.inv_mem hmM)
      have h7 : g⁻¹ * 1 = (g * m * (m : G)⁻¹)⁻¹ := by group
      rw [h7]
      exact A.inv_mem (by simpa using h6)
    · intro hg s hs
      have hgM : g ∈ A := by simpa using A.inv_mem hg
      exact A.mul_mem (A.mul_mem (A.inv_mem hgM) (hSA hs)) hgM
  have hcard : Nat.card (MulAction.fixedPoints S (G ⧸ A)) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  rw [hcard] at hmod
  exact hmod

theorem eq_top_of_normalizer_le_of_maximal {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (A M : Subgroup G) (hmax : ∀ N : Subgroup G, A ≤ N → N = A ∨ N = ⊤)
    (hA1 : A ≠ ⊥) (hind : ¬ A.index ≡ 1 [MOD p]) (hAM : A ≤ M) (S : Sylow p G)
    (hNS : ∀ n ∈ normalizer (S : Set G), n ∈ normalizer (M : Set G)) : M = ⊤ := by
  have hNA : normalizer (A : Set G) = A := by
    rcases hmax _ (le_normalizer (H := A)) with h | h
    · exact h
    · exfalso
      have hnormal : A.Normal := normalizer_eq_top_iff.1 h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with h' | h'
      · exact hA1 h'
      · exact hind (by rw [h', index_top])
  rcases hmax M hAM with h | h
  · exfalso
    have hNS' : ∀ n ∈ normalizer (S : Set G), n ∈ A := fun n hn => by
      have := hNS n hn
      rwa [h, hNA] at this
    have hSA : (S : Subgroup G) ≤ A := fun s hs => hNS' s (le_normalizer hs)
    exact hind (index_modEq_one_of_normalizer_le hSA S.isPGroup' S.not_dvd_index hNS')
  · exact h

@[expose] def compSet {G : Type*} [Group G] (E : Subgroup G) : Set G :=
  {s | ∃ x ∈ E, x ≠ 1 ∧ ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({x} : Set G) ∧
    CFSG.IsQuasisimple L ∧ s ∈ L}

theorem conj_mem_compSet {G : Type*} [Group G] {E : Subgroup G} {n : G}
    (hn : ∀ x ∈ E, n * x * n⁻¹ ∈ E) {s : G} (hs : s ∈ compSet E) : n * s * n⁻¹ ∈ compSet E := by
  obtain ⟨x, hx, hx1, L, hLC, hLq, hsL⟩ := hs
  refine ⟨n * x * n⁻¹, hn x hx, fun h => hx1 ?_, L.map (MulAut.conj n).toMonoidHom, ?_, ?_,
    ⟨s, hsL, rfl⟩⟩
  · have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * l * n⁻¹ * (n * x * n⁻¹) = n * (l * x) * n⁻¹ := by group
      _ = n * (x * l) * n⁻¹ := by rw [h1]
      _ = n * x * n⁻¹ * (n * l * n⁻¹) := by group
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap (MulAut.conj n) L) hLq

theorem mem_normalizer_closure_compSet {G : Type*} [Group G] {E : Subgroup G} {n : G}
    (hn : ∀ x ∈ E, n * x * n⁻¹ ∈ E) (hn' : ∀ x ∈ E, n⁻¹ * x * n ∈ E) :
    n ∈ normalizer (Subgroup.closure (compSet E) : Set G) := by
  have key : ∀ m : G, (∀ x ∈ E, m * x * m⁻¹ ∈ E) →
      ∀ h ∈ Subgroup.closure (compSet E), m * h * m⁻¹ ∈ Subgroup.closure (compSet E) := by
    intro m hm h hh
    have : Subgroup.closure (compSet E) ≤
        (Subgroup.closure (compSet E)).comap (MulAut.conj m).toMonoidHom :=
      Subgroup.closure_le _ |>.2 fun s hs => Subgroup.subset_closure (conj_mem_compSet hm hs)
    exact this hh
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact key n hn h
  · intro hh
    have := key n⁻¹ (by simpa using hn') _ hh
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
