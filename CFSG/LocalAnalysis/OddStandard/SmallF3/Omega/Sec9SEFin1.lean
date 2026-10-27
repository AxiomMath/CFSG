module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem simHasDim_of_inducesTypeSome {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) {r : ℕ} {α : ℤˣ}
    (h : InducesTypeSome L s 6 (-1) r α) : SimHasDim (ffInducesHom hm e ⟨s, hs⟩) r := by
  obtain ⟨V', _, _, _, Q', hQ', e', x', hd', hs', hix', hty⟩ := h
  exact simHasDim_of_inducesViaP hQ hQ' hm ⟨hd', hs'⟩ e e'
    (ffInducesHom_spec hm e ⟨s, hs⟩) hix' hty.simHasDim

theorem innerOn_of_model (hM : Asc82E16Model) {L F : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hL : commutator ↥L = ⊤)
    (hFN : F ≤ Subgroup.normalizer (L : Set G)) (hF : IsElemAb2 F 4)
    (hFC : F ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hinv : ∀ (f : G) (hf : f ∈ F), f ≠ 1 →
      (SimInOmegaStar hQ (ffInducesHom hm e ⟨f, hFN hf⟩) ∧
          SimHasDim (ffInducesHom hm e ⟨f, hFN hf⟩) 4) ∨
        SimHasDim (ffInducesHom hm e ⟨f, hFN hf⟩) 3) :
    ∀ (f : G) (hf : f ∈ F), SimInOmegaStar hQ (ffInducesHom hm e ⟨f, hFN hf⟩) := by
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e
  let Ψ : ↥F →* ProjSim Q := Φ.comp (Subgroup.inclusion hFN)
  have hΨ : ∀ g : ↥F, Ψ g = ffInducesHom hm e ⟨(g : G), hFN g.2⟩ := fun _ => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : ffInducesHom hm e ⟨(g : G), hFN g.2⟩ = 1 := by
      rw [← hΨ g]; exact hg
    have hcent : (g : G) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hL ⟨(g : G), hFN g.2⟩).mp hg'
    have hbot : (g : G) ∈ (⊥ : Subgroup G) := by
      rw [← hFC]
      exact ⟨g.2, hcent⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  let Fbar : Subgroup (ProjSim Q) := Ψ.range
  have hcard : Nat.card Fbar = Nat.card ↥F :=
    (Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm
  have hFbar : IsElemAb2 Fbar 4 := by
    haveI : IsMulCommutative ↥F := hF.1.1
    refine ⟨⟨Subgroup.range_isMulCommutative Ψ, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
      have hg2 : g ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hF.1.2 (g : G) g.2, Subgroup.coe_one]
      rw [← map_pow, hg2, map_one]
    · rw [hcard, hF.2]
  have hdich : ∀ f ∈ Fbar, f ≠ 1 →
      (SimInOmegaStar hQ f ∧ SimHasDim f 4) ∨ SimHasDim f 3 := by
    intro f hf hne
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hf
    have hgne : (g : G) ≠ 1 := by
      intro hg1
      exact hne (by rw [show g = 1 from Subtype.ext hg1, map_one])
    simpa only [hΨ g] using hinv (g : G) g.2 hgne
  intro f hf
  have hmem : Ψ ⟨f, hf⟩ ∈ Fbar := MonoidHom.mem_range.mpr ⟨⟨f, hf⟩, rfl⟩
  simpa only [hΨ] using hM V Q hQ hm.1 hm.2 Fbar hFbar hdich (Ψ ⟨f, hf⟩) hmem

end CFSG.OddStandard.SmallF3.Omega
