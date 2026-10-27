module

public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerSylowTransfer
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.AGLEmbedding.TwoGenInner (sylowOfIsSylowTwoOf mem_normalizer_of_mem_normalizer_map)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped commutatorElement

theorem centerQuotientConj_mk {Y : Type} [Group Y] (L : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (l : L) :
    centerQuotientConj L ⟨x, hx⟩ (QuotientGroup.mk l) =
      QuotientGroup.mk (L.normalizerMonoidHom ⟨x, hx⟩ l) := rfl

theorem exists_perfect_centralizer_lift {Y : Type} [Group Y] (L : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y))
    {N₀ : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hN₀ : ⁅N₀, N₀⁆ = N₀)
    (hfix : ∀ y ∈ N₀, centerQuotientConj L ⟨x, hx⟩ y = y) :
    ∃ W : Subgroup L, ⁅W, W⁆ = W ∧ W.map (QuotientGroup.mk' (Subgroup.center ↥L)) = N₀ ∧
      ∀ w ∈ W, x * (w : Y) * x⁻¹ = w := by
  set π := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hker : π.ker ≤ Subgroup.center ↥L := by
    intro g hg
    rwa [hπ, QuotientGroup.ker_mk'] at hg
  obtain ⟨W, hW, hWle, hWmap⟩ := ParabPrime.exists_perfect_map_eq π hker hN₀
    (by rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]; exact le_top)
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hx⟩ with hσ
  have hcen : ∀ a ∈ W, a⁻¹ * σ a ∈ Subgroup.center ↥L := by
    intro a ha
    have haN : π a ∈ N₀ := hWmap ▸ Subgroup.mem_map_of_mem π ha
    have h1 : π (σ a) = π a := by
      have := hfix _ haN
      rwa [hπ, QuotientGroup.mk'_apply, centerQuotientConj_mk] at this
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, σ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a ha b hb
    have e1 : σ a = a * (a⁻¹ * σ a) := by group
    have e2 : σ b = b * (b⁻¹ * σ b) := by group
    rw [map_commutatorElement, e1, e2, ParabPrime.commutatorElement_mul_central (hcen a ha)
      (hcen b hb)]
  refine ⟨W, hW, hWmap, fun w hw => ?_⟩
  have hwW : w ∈ ⁅W, W⁆ := by rw [hW]; exact hw
  have hle : ⁅W, W⁆ ≤ MonoidHom.eqLocus (σ : ↥L →* ↥L) (MonoidHom.id ↥L) :=
    Subgroup.commutator_le.2 fun a ha b hb => hcomm a ha b hb
  have hfixw : σ w = w := hle hwW
  have := congrArg (fun l : ↥L => (l : Y)) hfixw
  simpa [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this

@[expose] def quotImage {Y : Type} [Group Y] (L J : Subgroup Y) :
    Subgroup (↥L ⧸ Subgroup.center ↥L) :=
  (J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))

theorem mem_quotImage {Y : Type} [Group Y] {L J : Subgroup Y}
    {y : ↥L ⧸ Subgroup.center ↥L} :
    y ∈ quotImage L J ↔
      ∃ l : L, (l : Y) ∈ J ∧ (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = y := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

theorem le_quotImage_of_centralizer_le {Y : Type} [Group Y] (L J : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y))
    {N₀ : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hN₀ : ⁅N₀, N₀⁆ = N₀)
    (hfix : ∀ y ∈ N₀, centerQuotientConj L ⟨x, hx⟩ y = y)
    (hJ : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) : N₀ ≤ quotImage L J := by
  obtain ⟨W, -, hWmap, hWfix⟩ := exists_perfect_centralizer_lift L hx hN₀ hfix
  intro y hy
  rw [← hWmap] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact mem_quotImage.2 ⟨w, hJ w w.2 (hWfix w hw), rfl⟩

theorem center_le_of_normalizer_le {Y : Type} [Group Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) {z : L}
    (hz : z ∈ Subgroup.center ↥L) : (z : Y) ∈ J := by
  refine hJ ⟨z.2, ?_⟩
  show (z : Y) ∈ Subgroup.normalizer (T : Set Y)
  have hc : ∀ n : Y, n ∈ L → (z : Y) * n * (z : Y)⁻¹ = n := fun n hn => by
    have h1 := Subgroup.mem_center_iff.1 hz ⟨n, hn⟩
    have h2 : (z : Y) * n = n * z := congrArg Subtype.val h1.symm
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hc n (hT.1 hn)]
    exact hn
  · intro hn
    have hnL : n ∈ L := by
      have h1 : (z : Y)⁻¹ * ((z : Y) * n * (z : Y)⁻¹) * z ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem z.2) (hT.1 hn)) z.2
      simpa [mul_assoc] using h1
    rwa [hc n hnL] at hn

@[expose] noncomputable def barSylow {Y : Type} [Group Y] {L T : Subgroup Y}
    (hT : IsSylowTwoOf T L) [Finite Y] : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
  Sylow.mapSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) (sylowOfIsSylowTwoOf hT)

theorem coe_barSylow {Y : Type} [Group Y] [Finite Y] {L T : Subgroup Y} (hT : IsSylowTwoOf T L) :
    (barSylow hT : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (T.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := rfl

theorem normalizer_barSylow_le_quotImage {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) :
    Subgroup.normalizer ((barSylow hT : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
      Set (↥L ⧸ Subgroup.center ↥L)) ≤ quotImage L J := by
  intro g hg
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  have hl := mem_normalizer_of_mem_normalizer_map (sylowOfIsSylowTwoOf hT) (g := l) hg
  have hl' : l ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup L) : Set L) := hl
  rw [← Subgroup.subgroupOf_normalizer_eq hT.1] at hl'
  exact mem_quotImage.2 ⟨l, hJ ⟨l.2, Subgroup.mem_subgroupOf.1 hl'⟩, rfl⟩

theorem quotImage_ne_top {Y : Type} [Group Y] {L T J : Subgroup Y} (hT : IsSylowTwoOf T L)
    (hJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) (hJL : J ≤ L) (hne : J ≠ L) :
    quotImage L J ≠ ⊤ := by
  intro htop
  apply hne
  refine le_antisymm hJL fun y hy => ?_
  have hy' : (QuotientGroup.mk (⟨y, hy⟩ : L) : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 hy'
  have hz : l⁻¹ * ⟨y, hy⟩ ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl,
      inv_mul_cancel]
  have hzJ := center_le_of_normalizer_le hT hJ hz
  have : y = (l : Y) * ((l⁻¹ * ⟨y, hy⟩ : L) : Y) := by simp
  rw [this]
  exact J.mul_mem hlJ hzJ

end CFSG.AGLEmbedding.LieOut
