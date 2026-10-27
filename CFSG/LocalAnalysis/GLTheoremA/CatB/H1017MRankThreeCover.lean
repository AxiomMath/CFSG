module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem card_center_centralizer_of_cover {G J : Type} [Group G] [Group J] {ζ : G}
    {D : Subgroup G} (hC : Subgroup.centralizer ({ζ} : Set G) = D) {ρ : D →* J}
    (hρ : Function.Surjective ρ) (hJ : Subgroup.center J = ⊥)
    (hker : ∀ d : D, ρ d = 1 ↔ (d : G) ∈ Subgroup.zpowers ζ) :
    Nat.card (Subgroup.center ↥(Subgroup.centralizer ({ζ} : Set G))) = orderOf ζ := by
  set H := Subgroup.centralizer ({ζ} : Set G)
  have hζH : ζ ∈ H := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hζZ : (⟨ζ, hζH⟩ : H) ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hmap : (Subgroup.center H).map H.subtype = Subgroup.zpowers ζ := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.2 ⟨⟨ζ, hζH⟩, hζZ, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    have hzD : (z : G) ∈ D := hC.le z.2
    have hc : ρ ⟨z, hzD⟩ ∈ Subgroup.center J := by
      refine Subgroup.mem_center_iff.2 fun j => ?_
      obtain ⟨d, rfl⟩ := hρ j
      have hw : (d : G) * z = z * d := by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨d, hC.ge d.2⟩)
      have hdz : d * ⟨z, hzD⟩ = ⟨z, hzD⟩ * d := Subtype.ext hw
      exact ((map_mul ρ d _).symm.trans (congrArg ρ hdz)).trans (map_mul ρ _ d)
    rw [hJ, Subgroup.mem_bot] at hc
    exact (hker ⟨z, hzD⟩).1 hc
  rw [← Subgroup.card_subtype H (Subgroup.center H), hmap, Nat.card_zpowers]

private theorem isElemAbelian_map_hom {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    {E : Subgroup X} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    show f x * f y = f y * f x
    haveI := hE.1
    have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at this
    rw [← map_mul, ← map_mul, this]
  · rintro _ ⟨x, hx, rfl⟩
    show f x ^ p = 1
    rw [← map_pow, hE.2 x hx, map_one]


theorem exists_elemAbelian_of_fi24Cover {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (f : H ⧸ Subgroup.center H ≃* CFSG.Blueprint.NativeSporadic.Fi24prime) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 7 := by
  obtain ⟨c⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime
  obtain ⟨F, hF, hFc⟩ := i1017FiTwoFourCoverRank_holds H
    ⟨TauCeti.CFSGIndex.sporadic .Fi24Prime, rfl, ⟨f.trans c⟩⟩ hZ
  exact ⟨F.map H.subtype, isElemAbelian_map_hom H.subtype hF, by rw [Subgroup.card_subtype, hFc]⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
