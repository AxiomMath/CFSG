module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_glaPPrimeCoreOf_of_normal_sub {p : ℕ} {A N : Subgroup G} (hNA : N ≤ A)
    (hn : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p A := by
  have hnorm : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn' a => ?_⟩
    have := hn a a.2 n hn'
    simpa [Subgroup.mem_subgroupOf] using this
  have hcard : Nat.card (N.subgroupOf A) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
  have h1 : N.subgroupOf A ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcard ▸ hc⟩
  have h2 := Subgroup.map_mono (f := A.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hNA] at h2

theorem barX_eq_bot_of_le_glaPPrimeCoreOf {p : ℕ} {X S : Subgroup G} (h : S ≤ GLAPPrimeCoreOf p X) :
    barX p X S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ GLAPPrimeCoreOf p X := h (Subgroup.mem_subgroupOf.1 hk)
  obtain ⟨k', hk'', hkk⟩ := hk'
  have : k' = k := Subtype.ext hkk
  subst this
  exact (QuotientGroup.eq_one_iff _).2 hk''

theorem le_glaPPrimeCoreOf_of_barX_eq_bot {p : ℕ} {X S : Subgroup G} (hSX : S ≤ X)
    (h : barX p X S = ⊥) : S ≤ GLAPPrimeCoreOf p X := by
  intro s hs
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨s, hSX hs⟩ : ↥X)) ∈ barX p X S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨⟨s, hSX hs⟩, hmem, rfl⟩

theorem barX_mono {p : ℕ} {X A B : Subgroup G} (h : A ≤ B) : barX p X A ≤ barX p X B := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem nontrivial_of_open_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  obtain ⟨-, hs⟩ := h
  haveI := hs.toNontrivial
  by_contra hQ
  rw [not_nontrivial_iff_subsingleton] at hQ
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [Subsingleton.elim a b])

theorem normalizer_of_normalizes_component {p : ℕ} (hp : p.Prime) {X K Y L : Subgroup G} {g : G}
    (hK : GLAPComponent p X K) (hgX : g ∈ X) (hYX : Y ≤ X) (hYK : Y ≤ K)
    (hLY : GLAPComponent p Y L) (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have hK₂ : GLAPComponent p X (GLBConj g K) := by
    have h := glaPComponent_gLBConj hK g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgX)] at h
  have hLK : L ≤ K := hLY.1.trans hYK
  have hLX : L ≤ X := hLK.trans hK.1
  have hLK₂ : L ≤ GLBConj g K := by
    have h := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g hLK
    rwa [gLBConj_eq_of_mem_normalizer hgL] at h
  by_contra hne
  have hbar : barX p X K ≠ barX p X (GLBConj g K) :=
    fun h => hne (glaPComponent_unique hK hK₂ h).symm
  have hcomm : ⁅barX p X K, barX p X (GLBConj g K)⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute
        ((CFSG.isComponent_iff_open _).2 hK.2.2.1)
        ((CFSG.isComponent_iff_open _).2 hK₂.2.2.1) with h | h
    · exact absurd h hbar
    · exact h
  have hLL : ⁅barX p X L, barX p X L⁆ = ⊥ := by
    refine eq_bot_iff.2 ?_
    calc ⁅barX p X L, barX p X L⁆ ≤ ⁅barX p X K, barX p X (GLBConj g K)⁆ :=
          Subgroup.commutator_mono (barX_mono hLK) (barX_mono hLK₂)
      _ = ⊥ := hcomm
  have hLLX : ⁅L, L⁆ ≤ GLAPPrimeCoreOf p X :=
    le_glaPPrimeCoreOf_of_barX_eq_bot (commutator_le_of_le' hLX hLX)
      ((barX_commutator p hLX hLX).trans hLL)
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X ⊓ Y : Subgroup G)) := by
    refine Nat.Coprime.coprime_dvd_right ?_
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime p X)
    exact Subgroup.card_dvd_of_le inf_le_left
  have hTY : GLAPPrimeCoreOf p X ⊓ Y ≤ GLAPPrimeCoreOf p Y := by
    refine le_glaPPrimeCoreOf_of_normal_sub inf_le_right ?_ hcop
    intro a ha n hn
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hn.2) (Subgroup.inv_mem _ ha)⟩
    have hnorm := le_normalizer_glaPPrimeCoreOf p X (hYX ha)
    exact (Subgroup.mem_normalizer_iff.1 hnorm n).1 hn.1
  have hLLY : ⁅L, L⁆ ≤ GLAPPrimeCoreOf p Y :=
    le_trans (le_inf hLLX (commutator_le_of_le' hLY.1 hLY.1)) hTY
  have hbot : barX p Y L = ⊥ := by
    have h1 : ⁅barX p Y L, barX p Y L⁆ = ⊥ := by
      rw [← barX_commutator p hLY.1 hLY.1]
      exact barX_eq_bot_of_le_glaPPrimeCoreOf hLLY
    have h2 := barX_perfect_of_glaPComponent hLY
    rw [h1] at h2
    exact h2.symm
  have hsub : Subsingleton ↥(barX p Y L) := by
    rw [hbot]
    infer_instance
  exact (not_nontrivial_iff_subsingleton.2 hsub) (nontrivial_of_open_isQuasisimple hLY.2.2.1.2.2)

end CFSG.LocalAnalysis.GLTheoremA.K156

end
