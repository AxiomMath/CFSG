module

public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Frame
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Cover
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Burn
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Z
public import CFSG.CGT.PushingUpLit.CGT6X.End4Cover
public import CFSG.CGT.PushingUpLit.CGT6X.End4Core
public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg
public import CFSG.CGT.PushingUpLit.CGT6X.K7aBridge
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.StronglyEmbedded.BenderUnitaryCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.CGT.PushingUpLit.CGT6X.K7a CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.Quasithin
  CFSG.CGT.PushingUpLit.CGT6 CFSG.SL2MinimalFaithful CFSG.LocalAnalysis
  CFSG.ComponentClassification.CatalogueBGraphForm CFSG.CGT.PushingUpLit.CGT6M
open CFSG.Open (StatedClassicalModel)

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem end411_l34
    (hV : ∀ v : V, v ^ 2 = 1) {G L Y : Subgroup (MulAut V)} (hYL : Y ≤ L)
    [Group.IsPerfect ↥L] (hSQ : SimpleQuot Y) (hgen : CommGen Y)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hirr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) {t : MulAut V}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (ht2 : t ^ 2 = 1)
    (htY : ∀ y ∈ Y, t * y = y * t)
    (hτout : ∀ x : ↥L ⧸ Subgroup.center ↥L,
      centerAutHom ↥L (conjOn L t htN) ≠ MulAut.conj x)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (hYF : Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hU : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y))
    (hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2) : False := by
  have hF2 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  set Y' : Subgroup ↥L := Y.subgroupOf L with hY'def
  obtain ⟨φ⟩ := hYF
  let φ' : ↥Y' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hYL).trans φ
  have hτ2 : conjOn L t htN ^ 2 = 1 := conjOn_sq L t htN ht2
  have hYτ : ∀ y ∈ Y', conjOn L t htN y = y := fun y hy =>
    conjOn_fixes L t htN y (htY y hy)
  obtain ⟨K, _, _, hK, e, H, hHτ, hHY⟩ :=
    K7a_linear_model (L := ↥L) (by norm_num) hmod (conjOn L t htN) hτ2 hτout Y' hF2 ⟨φ'⟩ hYτ
  have hcharK : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcH
  let e' : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL 3 K := e.trans cH⁻¹
  have he'τ : ∀ y : ↥L, e' (QuotientGroup.mk (conjOn L t htN y)) =
      dualAut 3 K (e' (QuotientGroup.mk y)) := by
    intro y
    have h1 := hHτ (QuotientGroup.mk y)
    rw [centerAutHom_mk] at h1
    show cH⁻¹ (e (QuotientGroup.mk (conjOn L t htN y))) =
      dualAut 3 K (cH⁻¹ (e (QuotientGroup.mk y)))
    rw [h1]
    simp [MulAut.mul_apply]
  have hO : ∀ y ∈ Y', ∃ o ∈ orthSL K, e' (QuotientGroup.mk y) = proj 3 K o := by
    intro y hy
    have h1 : e (QuotientGroup.mk y) ∈
        (orthProj K).map (cH : MulAut (projectiveSL 3 K)).toMonoidHom := by
      rw [← hHY]
      exact ⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h1
    obtain ⟨o, ho, rfl⟩ := mem_orthProj.mp hx
    refine ⟨o, ho, ?_⟩
    show cH⁻¹ (e (QuotientGroup.mk y)) = _
    rw [← hxy]
    simp
  obtain ⟨ρ, hρ⟩ := exists_cover_l34 hmod hK4 e' hodd
  have hMperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
  have hint := cover_intertwine e' (proj 3 K) ρ hρ (conjOn L t htN).toMonoidHom
    (dualAut 3 K).toMonoidHom (slGraphAut 3 K).toMonoidHom he'τ
    (fun m => (dualAut_proj m).symm)
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]⟩
  have hY'perf : Group.IsPerfect ↥Y' := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      LinearGroups.special_linear_dimension_two_perfect hF4
    exact Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have hcardY : Nat.card (orthSL K) ≤ Nat.card ↥Y' := by
    calc Nat.card (orthSL K) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := card_orthSL_le
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [card_specialLinearGroup_fin_two, card_specialLinearGroup_fin_two, hF2, hK]
      _ = Nat.card ↥Y' := (Nat.card_congr φ'.toEquiv).symm
  have hYO' : Y' = (orthSL K).map ρ :=
    eq_map_of_perfect e' (proj 3 K) ρ hρ Y' Subgroup.commutator_eq_self (orthSL K) hO hcardY
  have hρsurj : Function.Surjective ρ := by
    have h1 : (⊤ : Subgroup ↥L) ≤ (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)).map ρ := by
      refine le_map_of_perfect_cover e' (proj 3 K) ρ hρ ⊤ ?_ ⊤ ?_
      · exact Group.IsPerfect.commutator_eq_top
      · intro y _
        obtain ⟨g, hg⟩ := proj_surjective 3 K (e' (QuotientGroup.mk y))
        exact ⟨g, Subgroup.mem_top _, hg.symm⟩
    intro l
    obtain ⟨g, -, hg⟩ := h1 (Subgroup.mem_top l)
    exact ⟨g, hg⟩
  have hzρ : ∀ z ∈ Subgroup.center ↥L, ∃ g ∈ scalars 3 K, ρ g = z := by
    intro z hz
    obtain ⟨g, rfl⟩ := hρsurj z
    refine ⟨g, ?_, rfl⟩
    have h1 : e' (QuotientGroup.mk (ρ g)) = 1 := by
      rw [(QuotientGroup.eq_one_iff _).mpr hz, map_one]
    rw [hρ] at h1
    rw [← ker_proj]
    exact h1
  have hγscalar : ∀ g ∈ scalars 3 K, slGraphAut 3 K g = g⁻¹ := by
    intro g hg
    have hg' : g⁻¹ ∈ scalars 3 K := inv_mem hg
    obtain ⟨c, -, hc⟩ := hg'
    show (g⁻¹).transpose = g⁻¹
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_transpose, hc]
    simp [Matrix.scalar_apply, Matrix.diagonal_transpose]
  have hinv : ∀ z ∈ Subgroup.center ↥L, t * (z : MulAut V) * t⁻¹ = (z : MulAut V)⁻¹ := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := hzρ z hz
    have h1 := congrArg
      (fun φ : SpecialLinearGroup (Fin 3) K →* ↥L => ((φ g : ↥L) : MulAut V)) hint
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conjOn_apply] at h1
    rw [h1, hγscalar g hg, map_inv]
    rfl
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_inverted hV hSQ hgen hYL hGL ht2 htY hodd hinv hirr
  have hkill : ∀ g ∈ scalars 3 K, ρ g = 1 := by
    intro g hg
    have h1 : e' (QuotientGroup.mk (ρ g)) = 1 := by
      rw [hρ, ← ker_proj] at *
      exact hg
    have h2 : (QuotientGroup.mk (ρ g) : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      apply e'.injective
      rw [h1, map_one]
    have h3 : ρ g ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).mp h2
    rw [hZ] at h3
    exact Subgroup.mem_bot.mp h3
  have hker : ∀ g, ρ g = 1 → g ∈ scalars 3 K := by
    intro g hg
    have h1 := hρ g
    rw [hg] at h1
    rw [← ker_proj]
    have h2 : e' (QuotientGroup.mk (1 : ↥L)) = 1 := by simp
    rw [h2] at h1
    exact h1.symm
  obtain ⟨g0, hg0⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord0 : orderOf g0 = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg0, Nat.card_units, hK4]
  obtain ⟨ω, hωdef⟩ : ∃ ω : K, ω = (g0 : K) := ⟨_, rfl⟩
  have hω3 : ω ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one g0
    rw [hord0] at h1
    have h2 := congrArg Units.val h1
    rw [hωdef]
    simpa using h2
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : g0 = 1 := Units.ext (by rw [← hωdef, h]; rfl)
    rw [h1, orderOf_one] at hord0
    omega
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  set ρ' : SpecialLinearGroup (Fin 3) K →* MulAut V := L.subtype.comp (ρ.comp (phiFr 0)) with hρ'
  have hρ'ker : ∀ g ∈ scalars 3 K, ρ' g = 1 := by
    intro g hg
    obtain ⟨c, hc3, hc⟩ := hg
    have hgs : g = scalarElement c hc3 := Subtype.ext hc
    have h1 : phiFr (0 : K) g = g := by rw [hgs]; exact phiFr_scalar 0 hc3
    have h2 : ρ g = 1 := hkill g ⟨c, hc3, hc⟩
    show ((ρ (phiFr (0 : K) g) : ↥L) : MulAut V) = 1
    rw [h1, h2]
    rfl
  have hconj : ∀ x y z : SpecialLinearGroup (Fin 3) K, x * y = z * x →
      ρ' x * ρ' y * (ρ' x)⁻¹ = ρ' z := by
    intro x y z h
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, h]
  set d := l34dSL hω with hd
  set om := (l34omSL : SpecialLinearGroup (Fin 3) K) with hom
  have hoi : ρ' (l34oiSL : SpecialLinearGroup (Fin 3) K) = (ρ' om)⁻¹ := by
    rw [l34_oi, map_inv]
  have hdi : ρ' (l34diSL hω) = (ρ' d)⁻¹ := by
    rw [l34_di, map_inv]
  have hα3 : (ρ' d) ^ 3 = 1 := by rw [← map_pow, l34_d3, map_one]
  have hβ3 : (ρ' om) ^ 3 = 1 := by rw [← map_pow, l34_o3, map_one]
  have hcomm : Commute (ρ' d) (ρ' om) := by
    have h1 : ρ' om * ρ' d = ρ' (l34zSL hω) * ρ' (d * om) := by
      rw [← map_mul, ← map_mul, l34_rel_d hω]
    rw [hρ'ker _ (l34_z_mem hω), one_mul, map_mul] at h1
    exact h1.symm
  have h1 : ρ' (l34fSL hω) * ρ' d * (ρ' (l34fSL hω))⁻¹ = (ρ' om)⁻¹ := by
    rw [hconj _ _ _ (l34_rel_a hω), hoi]
  have h2 : ρ' (l34f1SL hω) * ρ' d * (ρ' (l34f1SL hω))⁻¹ = (ρ' d * ρ' om)⁻¹ := by
    rw [hconj _ _ _ (l34_rel_b hω), map_mul, hdi, hoi, _root_.mul_inv_rev, hcomm.inv_inv.eq]
  have h3 : ρ' (l34f2SL hω) * ρ' d * (ρ' (l34f2SL hω))⁻¹ = ρ' d * (ρ' om)⁻¹ := by
    rw [hconj _ _ _ (l34_rel_c hω), map_mul, hoi]
  have hα1 : ρ' d ≠ 1 := by
    intro h
    have h' : ρ (phiFr (0 : K) d) = 1 := Subtype.ext h
    exact l34_phi_d_not_scalar hω (hker _ h')
  have hαY : ρ' d ∈ Y := by
    have h4 : ρ (phiFr (0 : K) d) ∈ Y' := by
      rw [hYO']
      exact ⟨phiFr (0 : K) d, l34_phi_d_mem_orth hω, rfl⟩
    exact h4
  have hr := card_le_sixteen_fixSub_odd hV Y hαY (m := 3) (by decide) hα3 hU
  exact false_of_l34_config hV hα3 hβ3 hcomm h1 h2 h3 hα1 hr

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End4
