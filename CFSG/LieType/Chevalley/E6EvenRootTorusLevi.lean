module

public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public noncomputable section

namespace CFSG.LieType.Chevalley.E6EvenRootTorus

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.Assembly.LowTwoRank Matrix

theorem sl6_quot_facts {F : Type} [Field F] [Finite F] {L : Type} [Group L]
    (ψ : SpecialLinearGroup (Fin (5 + 1)) F →* L) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ g, ψ g ≠ 1) (hodd : Odd (Nat.card Fˣ)) :
    commutator L = ⊤ ∧ CFSG.Open.IsQuasisimple L ∧ Odd (Nat.card (center L)) ∧
      Nonempty (L ⧸ center L ≃* StatedProj (StatedSL 6 F)) := by
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 F (by norm_num)
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1
  have hcomm : commutator L = ⊤ := by
    rw [commutator_def, ← MonoidHom.range_eq_top.2 hψ, MonoidHom.range_eq_map, ← map_commutator,
      ← commutator_def, hq.1.commutator_eq_top]
  let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hψ hker
  have := hq.2.1
  have hcen : (center (SpecialLinearGroup (Fin (5 + 1)) F)).map ψ = center L := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hq.1 ψ hψ hker,
      map_comap_eq_self_of_surjective hψ]
  refine ⟨hcomm, ⟨hcomm, e.symm.isSimpleGroup⟩, ?_, ⟨e.symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj (5 + 1) F)⟩⟩
  refine Odd.of_dvd_nat hodd ?_
  rw [← hcen]
  refine (card_map_dvd _ ψ).trans ?_
  rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity'
    (⟨0, by decide⟩ : Fin (5 + 1))).toEquiv]
  exact card_subgroup_dvd_card _

theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, f = i + 1 := ⟨f - 1, by omega⟩
  refine ⟨2 ^ i - 1, ?_⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

theorem subsystemGroup_facts
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) :
    commutator ↥((subsystemGroup TwistTag.E6.tag k setA).subgroupOf
        (adjointGroup TwistTag.E6.tag k)) = ⊤ ∧
      CFSG.Open.IsQuasisimple ↥((subsystemGroup TwistTag.E6.tag k setA).subgroupOf
        (adjointGroup TwistTag.E6.tag k)) ∧
      Odd (Nat.card (center ↥((subsystemGroup TwistTag.E6.tag k setA).subgroupOf
        (adjointGroup TwistTag.E6.tag k)))) ∧
      Nonempty (↥((subsystemGroup TwistTag.E6.tag k setA).subgroupOf
          (adjointGroup TwistTag.E6.tag k)) ⧸ center ↥((subsystemGroup TwistTag.E6.tag k
          setA).subgroupOf (adjointGroup TwistTag.E6.tag k)) ≃* StatedProj (StatedSL 6 k)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hmem : ∀ B, realize h2 B ∈ subsystemGroup TwistTag.E6.tag k setA := fun B => by
    rw [← range_realize h2]
    exact ⟨B, rfl⟩
  let ψ : SpecialLinearGroup (Fin (5 + 1)) k →* ↥((subsystemGroup TwistTag.E6.tag k
      setA).subgroupOf (adjointGroup TwistTag.E6.tag k)) :=
    ((realize h2).codRestrict (adjointGroup TwistTag.E6.tag k)
      fun B => subsystemGroup_le_adjointGroup (hmem B)).codRestrict _
        fun B => mem_subgroupOf.2 (hmem B)
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨y, hyG⟩, hy⟩
    have hy' : y ∈ (realize h2).range := (range_realize h2).symm ▸ mem_subgroupOf.1 hy
    obtain ⟨B, rfl⟩ := hy'
    exact ⟨B, rfl⟩
  have hψ1 : ∃ B, ψ B ≠ 1 := by
    refine ⟨SpecialLinearGroup.transvection (castSucc_ne_succ 0) 1, fun h => ?_⟩
    have h1 : realize h2 (SpecialLinearGroup.transvection (castSucc_ne_succ 0) 1) = 1 :=
      congrArg (fun y : ↥((subsystemGroup TwistTag.E6.tag k setA).subgroupOf
        (adjointGroup TwistTag.E6.tag k)) =>
          ((y : ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k)) h
    rw [realize_x h2, ← pinnedX_single,
      ← pinnedX_zero (R := k) TwistTag.E6.tag (Pi.single (pathIdx 0) 1)] at h1
    exact one_ne_zero (pinnedX_injective _ _ _ h1)
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units, hk]
    exact odd_two_pow_sub_one hf
  exact sl6_quot_facts ψ hψ hψ1 hodd

theorem centralizer_thetaRankOneGroup
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) :
    adjointGroup TwistTag.E6.tag k ⊓
        centralizer (thetaRankOneGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) =
      subsystemGroup TwistTag.E6.tag k setA := by
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  set L := GaloisField 2 (2 * f)
  have hL : Nat.card L = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hL
  let _ : Algebra k L := ι.toAlgebra
  obtain ⟨⟨-, -, -, -, hcomm, huniq, -⟩, -⟩ :=
    even_E6_graph_root_SL2_normalizer f hf k L hk hL (iterateFrobenius L 2 f)
      (fun c => iterateFrobenius_def (p := 2) f c)
  have hLG : subsystemGroup TwistTag.E6.tag k setA ≤ adjointGroup TwistTag.E6.tag k :=
    subsystemGroup_le_adjointGroup
  refine le_antisymm (fun g hg => ?_) fun l hl =>
    mem_inf.2 ⟨hLG hl, mem_centralizer_iff.2 fun y hy => hcomm y hy l ⟨hl, hLG hl⟩⟩
  obtain ⟨hgG, hgC⟩ := mem_inf.1 hg
  obtain ⟨⟨x, l⟩, ⟨hx, hl, hgxl⟩, -⟩ := huniq g ⟨centralizer_le_normalizer _ hgC, hgG⟩
  dsimp only at hx hl hgxl
  subst hgxl
  have hlC : l ∈ centralizer (thetaRankOneGroup (RingHom.id k) :
      Set (ModGL TwistTag.E6.tag k)) := mem_centralizer_iff.2 fun y hy => hcomm y hy l hl
  have hxC : x ∈ centralizer (thetaRankOneGroup (RingHom.id k) :
      Set (ModGL TwistTag.E6.tag k)) := by
    have e : x = (x * l) * l⁻¹ := by group
    rw [e]
    exact mul_mem hgC (inv_mem hlC)
  have hx1 : x = 1 := by
    have h0 := E6GraphRootSL2.thetaRankOneGroup_inf_eq_bot h2 (RingHom.id k)
      (C := centralizer (thetaRankOneGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k))) le_rfl
    have h1 : x ∈ thetaRankOneGroup (RingHom.id k) ⊓ centralizer
        (thetaRankOneGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) := mem_inf.2 ⟨hx, hxC⟩
    rw [h0] at h1
    exact mem_bot.1 h1
  rw [hx1, one_mul]
  exact (mem_inf.1 hl).1

theorem commutator_thetaRankOneGroup
    {k : Type} [Field k] [Finite k] (h2 : (2 : k) = 0)
    (hk4 : 4 ≤ Nat.card k) :
    ⁅thetaRankOneGroup (RingHom.id k), thetaRankOneGroup (RingHom.id k)⁆ =
      thetaRankOneGroup (RingHom.id k) := by
  have hp := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk4
  rw [thetaRankOneGroup_eq_range h2, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    hp.commutator_eq_top]

theorem thetaTorus_le_thetaRankOneGroup
    {k : Type} [Field k] (h2 : (2 : k) = 0) :
    thetaTorus (RingHom.id k) ≤ thetaRankOneGroup (RingHom.id k) := by
  rw [thetaRankOneGroup_eq_range h2]
  rintro _ ⟨a, rfl⟩
  refine ⟨HSL a, ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, thetaTorusHom_eq_thetaSL2]
  congr 1

theorem card_thetaTorus
    {k : Type} [Field k] (h2 : (2 : k) = 0) :
    Nat.card (thetaTorus (RingHom.id k)) = Nat.card kˣ := by
  have hinj : Function.Injective ((thetaTorusHom k).comp (Units.map (RingHom.id k).toMonoidHom)) :=
    (thetaTorusHom_injective h2).comp fun a b h => Units.ext (by simpa using congrArg Units.val h)
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG.LieType.Chevalley.E6EvenRootTorus
