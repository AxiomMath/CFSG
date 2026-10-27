module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Gen
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Greatest

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_greatest {z : G} {M V X : Subgroup G} (hMz : M = centralizer {z})
    (hVF : V ≤ Fm M) (hX : X ∈ XfamR z M V) (hmax : ∀ Y ∈ XfamR z M V, Y ≤ X) :
    M ≤ normalizer (X : Set G) := by
  have hVX : ∀ v ∈ V, v ∈ normalizer (X : Set G) := hX.2.2.1
  have hgood : ∀ b ∈ M, (∀ v ∈ V, b⁻¹ * v * b ∈ normalizer (X : Set G)) →
      b ∈ normalizer (X : Set G) := by
    intro b hb hV
    exact mem_normalizer_of_cj_eq (cj_eq_of_le (hmax _ (cj_mem_XfamR hMz hb hX hV)))
  have : Group.IsNilpotent ↥(Fm M) := Fm_nilpotent M
  have hF : Fm M ≤ normalizer (X : Set G) := by
    by_contra hnot
    set U : Subgroup ↥(Fm M) := (normalizer (X : Set G)).subgroupOf (Fm M) with hU
    have hUtop : U < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hnot ?_
      intro f hf
      have : (⟨f, hf⟩ : ↥(Fm M)) ∈ U := h ▸ Subgroup.mem_top _
      exact this
    obtain ⟨b, hbN, hbU⟩ : ∃ b ∈ normalizer (U : Set ↥(Fm M)), b ∉ U := by
      have := (Group.normalizerCondition_of_isNilpotent (G := ↥(Fm M))) U hUtop
      exact IsConcreteLE.exists_of_lt this
    have hbM : (b : G) ∈ M := Fm_le M b.2
    have hbX : (b : G) ∈ normalizer (X : Set G) := by
      refine hgood b hbM fun v hv => ?_
      have hvF : v ∈ Fm M := hVF hv
      have hvU : (⟨v, hvF⟩ : ↥(Fm M)) ∈ U := hVX v hv
      have h2 := ((Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbN)) ⟨v, hvF⟩).1 hvU
      simpa [hU, Subgroup.mem_subgroupOf] using h2
    exact hbU hbX
  intro b hb
  refine hgood b hb fun v hv => hF ?_
  have hnorm := le_normalizer_Fm M
  have := Subgroup.mem_normalizer_iff.1 (hnorm (M.inv_mem hb)) v
  simpa using this.1 (hVF hv)

end Greatest

theorem lemma18_8R_of (h171 : Prop17_1) : Lemma18_8R := by
  intro G _ _ z k S M p E t hctx
  rintro ⟨X, hX, hmax⟩
  have hMz : M = centralizer {z} := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hMc : IsCoatom M := hctx.base.ctx.mem.1
  have hsimple : IsSimpleGroup G := hctx.base.ctx.ctx.std.kps.1
  have hVF : Vof M E ≤ Fm M := inf_le_left
  have hMN := le_normalizer_of_greatest hMz hVF hX hmax
  obtain ⟨hXbot, hXtop, -, hXz, -, -⟩ := hX
  have hdich : normalizer (X : Set G) = M ∨ normalizer (X : Set G) = ⊤ := by
    rcases eq_or_lt_of_le hMN with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hMc.2 _ h)
  rcases hdich with h | h
  ·
    have hXM : X ≤ M := fun x hx => h ▸ Subgroup.le_normalizer hx
    apply hXbot
    rw [← hXz, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    have hxz : x ∈ centralizer ({z} : Set G) := hMz ▸ hXM hx
    have hc : Commute x z := Subgroup.mem_centralizer_singleton_iff.1 hxz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Subgroup.mem_bot.2 ((commutatorElement_eq_one_iff_commute).2 (hc.zpow_right n))
  ·
    have hn : X.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases hsimple.eq_bot_or_eq_top_of_normal X with h' | h'
    exacts [hXbot h', hXtop h']

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
