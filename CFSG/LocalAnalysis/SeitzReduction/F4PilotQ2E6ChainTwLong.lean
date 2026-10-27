module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainTw
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainLong

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear pairEmbed)
open CFSG.SeitzReduction.SymplecticPilot (zThreeSL)
open CFSG.Timmesfeld.LieEmbed (c3ToF4 c3ToF4_single)
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)

local instance f4PilotQ2E6ChainTwLongNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ChainTwLongNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section SLField

variable {F : Type} [Field F] [CharP F 2] {n : ℕ} {a b : Fin n}

theorem mul_apply_row_of_commute_pairEmbed (hab : a ≠ b) {w : SpecialLinearGroup (Fin n) F}
    (hw : Commute w (pairEmbed hab (zThreeSL (K := F)))) (v : Matrix (Fin n) (Fin n) F)
    (j : Fin n) :
    ((w : Matrix (Fin n) (Fin n) F) * v) a j =
      (w : Matrix (Fin n) (Fin n) F) a a * v a j + (w : Matrix (Fin n) (Fin n) F) a b * v b j := by
  obtain ⟨hoff, -, -⟩ := SymplecticPilot.entries_of_commute_pairEmbed_zThree hab hw.eq
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab
    (fun u _ hu => by rw [(hoff u hu.1 hu.2).2.2.1, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ b) h)]

theorem mul_apply_comm_of_commute_pairEmbed (hab : a ≠ b) {x y : SpecialLinearGroup (Fin n) F}
    (hx : Commute x (pairEmbed hab (zThreeSL (K := F))))
    (hy : Commute y (pairEmbed hab (zThreeSL (K := F)))) :
    ((x : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) a a =
        ((y : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F)) a a ∧
      ((x : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) a b =
        ((y : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F)) a b := by
  obtain ⟨-, hx10, hx11⟩ := SymplecticPilot.entries_of_commute_pairEmbed_zThree hab hx.eq
  obtain ⟨-, hy10, hy11⟩ := SymplecticPilot.entries_of_commute_pairEmbed_zThree hab hy.eq
  rw [mul_apply_row_of_commute_pairEmbed hab hx, mul_apply_row_of_commute_pairEmbed hab hy,
    mul_apply_row_of_commute_pairEmbed hab hx, mul_apply_row_of_commute_pairEmbed hab hy,
    hx10, hy10, hx11, hy11]
  constructor <;> ring

theorem commutator_mem_blockCompl_of_commute' (hab : a ≠ b) {x y : SpecialLinearGroup (Fin n) F}
    (hx : Commute x (pairEmbed hab (zThreeSL (K := F))))
    (hy : Commute y (pairEmbed hab (zThreeSL (K := F)))) :
    x * y * x⁻¹ * y⁻¹ ∈ blockSpecialLinear ({a, b} : Finset (Fin n))ᶜ := by
  have hz : x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
  have hw := hx.mul_left hy
  have hw' := hy.mul_left hx
  have hzc := hw.mul_left hw'.inv_left
  obtain ⟨hoff, h10, h11⟩ := SymplecticPilot.entries_of_commute_pairEmbed_zThree hab hzc.eq
  have hxy : ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (x : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) := rfl
  have hyx : ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (y : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) := rfl
  obtain ⟨eaa, eab⟩ := mul_apply_comm_of_commute_pairEmbed hab hx hy
  rw [← hxy, ← hyx] at eaa eab
  have hm : ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
    congrArg Subtype.val (mul_inv_cancel (y * x))
  have e1 : ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a a *
        (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a a +
      ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a b *
        (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) b a = 1 := by
    have h := congrFun (congrFun hm a) a
    rw [mul_apply_row_of_commute_pairEmbed hab hw'] at h
    simpa only [Matrix.one_apply_eq] using h
  have e2 : ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a a *
        (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a b +
      ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a b *
        (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) b b = 0 := by
    have h := congrFun (congrFun hm a) b
    rw [mul_apply_row_of_commute_pairEmbed hab hw'] at h
    simpa only [Matrix.one_apply_ne hab] using h
  set Z : Matrix (Fin n) (Fin n) F :=
    (((x * y) * (y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) with hZ
  have hZ' : Z = ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((y * x)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
  have h1 : Z a a = 1 := by
    rw [hZ', mul_apply_row_of_commute_pairEmbed hab hw, eaa, eab, e1]
  have h2 : Z a b = 0 := by
    rw [hZ', mul_apply_row_of_commute_pairEmbed hab hw, eaa, eab, e2]
  have hba : Z b a = 0 := by rw [h10, h2, neg_zero]
  have hbb : Z b b = 1 := by rw [h11, h1, h2, sub_zero]
  rw [hz, LinearPilot.mem_blockSpecialLinear]
  intro i j hij
  have hij' : (i = a ∨ i = b) ∨ (j = a ∨ j = b) := by
    simpa only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_not] using hij
  change Z i j = (1 : Matrix (Fin n) (Fin n) F) i j
  rcases hij' with (rfl | rfl) | (rfl | rfl)
  · by_cases hja : j = i
    · subst hja; rw [h1, Matrix.one_apply_eq]
    by_cases hjb : j = b
    · subst hjb; rw [h2, Matrix.one_apply_ne hab]
    rw [(hoff j hja hjb).2.2.1, Matrix.one_apply_ne (Ne.symm hja)]
  · by_cases hja : j = a
    · subst hja; rw [hba, Matrix.one_apply_ne (Ne.symm hab)]
    by_cases hjb : j = i
    · subst hjb; rw [hbb, Matrix.one_apply_eq]
    rw [(hoff j hja hjb).2.2.2, Matrix.one_apply_ne (Ne.symm hjb)]
  · by_cases hia : i = j
    · subst hia; rw [h1, Matrix.one_apply_eq]
    by_cases hib : i = b
    · subst hib; rw [hba, Matrix.one_apply_ne (Ne.symm hab)]
    rw [(hoff i hia hib).1, Matrix.one_apply_ne hia]
  · by_cases hia : i = a
    · subst hia; rw [h2, Matrix.one_apply_ne hab]
    by_cases hib : i = j
    · subst hib; rw [hbb, Matrix.one_apply_eq]
    rw [(hoff i hia hib).2.1, Matrix.one_apply_ne hib]

end SLField

section Perfect


variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

open CFSG.LieType.Steinberg.TwistedE6 (nd) in
include hθ in
theorem commutator_twLevi_two_chainTw {t : kˣ} (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅twLevi k θ {2}, twLevi k θ {2}⁆ = twLevi k θ {2} := by
  rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
  exact commutator_rankOne_pair θ hθ (a := nd 2) (b := nd 4) (by decide) (by decide) rfl
    (by decide) (exists_mem_hHat_two θ hθ) ht

end Perfect

section Overlap


variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)
  {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def chainSU6
    (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G) : uGroup6 h →* G :=
  ΦX.comp (twParamEquiv h).toMonoidHom

theorem chainSU6_apply (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G)
    (m : uGroup6 h) : chainSU6 h ΦX m = ΦX (twParamEquiv h m) :=
  rfl

theorem mem_center_of_chainSU6_eq_one
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    {m : uGroup6 h} (hm : chainSU6 h ΦX m = 1) : m ∈ center (uGroup6 h) := by
  have hc : twParamEquiv h m ∈ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :=
    hker (MonoidHom.mem_ker.2 hm)
  rw [mem_center_iff]
  intro y
  apply (twParamEquiv h).injective
  rw [map_mul, map_mul]
  exact mem_center_iff.1 hc _

theorem exists_chainSU6_eq_of_mem_centralizerPerfectCore {e : L ≃* adjointGroup .F4 K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    {a b : Fin 6} (hab : a ≠ b) {Z : Subgroup G} {c' : uGroup6 h}
    (hc' : gramSUToSL h _ c' = pairEmbed hab (zThreeSL (K := F)))
    (hcZ : chainSU6 h ΦX c' ∈ Z) :
    ∀ y ∈ centralizerPerfectCore (subgroupToG e X₀ ⊔ Z), ∃ m : uGroup6 h,
      chainSU6 h ΦX m = y ∧ gramSUToSL h _ m ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
  set E := centralizerPerfectCore (subgroupToG e X₀ ⊔ Z) with hE
  have hEle : E ≤ (chainSU6 h ΦX).range := by
    intro y hy
    have hy' : y ∈ ΦX.range := by
      rw [hr]
      exact centralizerPerfectCore_anti le_sup_left hy
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨(twParamEquiv h).symm x, by rw [chainSU6_apply, MulEquiv.apply_symm_apply]⟩
  set P := E.comap (chainSU6 h ΦX) with hP
  have hPE : P.map (chainSU6 h ΦX) = E := Subgroup.map_comap_eq_self hEle
  have hcen : ∀ m ∈ P, m * c' * m⁻¹ * c'⁻¹ ∈ center (uGroup6 h) := by
    intro m hm
    refine mem_center_of_chainSU6_eq_one h hker ?_
    have h1 : chainSU6 h ΦX m ∈ centralizer (Z : Set G) :=
      centralizerPerfectCore_le_centralizer_of_le le_sup_right (Subgroup.mem_comap.1 hm)
    have h2 : chainSU6 h ΦX c' * chainSU6 h ΦX m = chainSU6 h ΦX m * chainSU6 h ΦX c' :=
      mem_centralizer_iff.1 h1 _ hcZ
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
    group
  have hP1 : ⁅P, P⁆ ≤ centralizer ({c'} : Set (uGroup6 h)) :=
    commutator_le_centralizer_of_conj_mem_center hcen
  have hP2 : ⁅⁅P, P⁆, ⁅P, P⁆⁆ ≤
      (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).comap (gramSUToSL h _) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    rw [Subgroup.mem_comap, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hcu : Commute u c' := mem_centralizer_singleton_iff.1 (hP1 hu)
    have hcv : Commute v c' := mem_centralizer_singleton_iff.1 (hP1 hv)
    have hcu' := hcu.map (gramSUToSL h _)
    have hcv' := hcv.map (gramSUToSL h _)
    rw [hc'] at hcu' hcv'
    exact commutator_mem_blockCompl_of_commute' hab hcu' hcv'
  have hEE : ⁅E, E⁆ = E := commutator_centralizerPerfectCore _
  have hEq : E = (⁅⁅P, P⁆, ⁅P, P⁆⁆).map (chainSU6 h ΦX) := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hPE, hEE, hEE]
  intro y hy
  rw [hEq] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨m, rfl, hP2 hm⟩

theorem levi6Hom_chainFrame_of {F' : Type} [Field F'] (ε : F' ≃+* K)
    (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K) (s : StatedSp 3 F') :
    levi6Hom (chainFrame e w) ε s =
      ((e.symm w : L) : G)⁻¹ * levi6Hom e ε s * ((e.symm w : L) : G) := by
  simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  exact coe_chainFrame_symm e w _

@[expose] noncomputable def conjParamU (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G) :
    twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G :=
  (MulAut.conj ((e.symm w : L) : G)⁻¹).toMonoidHom.comp ΦX

theorem conjParamU_apply (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G)
    (x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
    conjParamU h e w ΦX x = ((e.symm w : L) : G)⁻¹ * ΦX x * ((e.symm w : L) : G) := by
  rw [conjParamU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem isLeviNormalizedU_conjParamU {e : L ≃* adjointGroup .F4 K} {ε : h.fixedField ≃+* K}
    (w : adjointGroup .F4 K)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hn : IsLeviNormalizedU h ε e ΦX) :
    IsLeviNormalizedU h ε (chainFrame e w) (conjParamU h e w ΦX) := by
  intro s
  rw [conjParamU_apply, hn s, levi6Hom_chainFrame_of]

theorem range_conjParamU {e : L ≃* adjointGroup .F4 K} (w : adjointGroup .F4 K)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀)) :
    (conjParamU h e w ΦX).range = centralizerPerfectCore (subgroupToG (chainFrame e w) X₀) := by
  rw [conjParamU, MonoidHom.range_comp, hr, map_centralizerPerfectCore,
    subgroupToG_chainFrame_eq_map]

theorem ker_conjParamU_le {e : L ≃* adjointGroup .F4 K} (w : adjointGroup .F4 K)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes)) :
    (conjParamU h e w ΦX).ker ≤
      center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) := by
  intro x hx
  refine hker (MonoidHom.mem_ker.2 ?_)
  have h1 := MonoidHom.mem_ker.1 hx
  rw [conjParamU_apply] at h1
  have h2 : ΦX x = ((e.symm w : L) : G) * 1 * ((e.symm w : L) : G)⁻¹ := by
    rw [← h1]
    group
  rw [h2, mul_one, mul_inv_cancel]

theorem commute_rootSL2_centralizerPerfectCore_chainTw {e : L ≃* adjointGroup .F4 K}
    {ε : h.fixedField ≃+* K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hn : IsLeviNormalizedU h ε e ΦX) {a b : Fin 6} (hab : a ≠ b)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) {τ : Fin 3 → ℤ} (hτβ : c3ToF4 τ = β)
    (hτ : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField τ d)) =
      SpecialLinearGroup.transvection hab (d : F))
    (hτ' : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-τ) d)) =
      SpecialLinearGroup.transvection hab.symm (d : F)) :
    ∀ l ∈ rootSL2 K β, ∀ y ∈ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))),
      Commute ((e.symm l : L) : G) y := by
  have hx : ∀ c : K, chainSU6 h ΦX (uEmbed6 h (Sp.x 3 h.fixedField τ (ε.symm c))) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G) := by
    intro c
    rw [chainSU6_apply, hn, levi6Hom_x_alignTw, hτβ, ε.apply_symm_apply]
  have hx' : ∀ c : K, chainSU6 h ΦX (uEmbed6 h (Sp.x 3 h.fixedField (-τ) (ε.symm c))) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G) := by
    intro c
    rw [chainSU6_apply, hn, levi6Hom_x_alignTw, map_neg, hτβ, ε.apply_symm_apply]
  set B := (blockSpecialLinear ({a, b} : Finset (Fin 6))).comap (gramSUToSL h
    ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) with hB
  have hJ : subgroupToG e (rootSL2 K β) ≤ B.map (chainSU6 h ΦX) := by
    rw [rootSL2_eq_sup hβ, subgroupToG, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff hβ l).1 hl
      refine ⟨_, ?_, hx c⟩
      show gramSUToSL h _ _ ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))
      rw [hτ]
      exact LinearPilot.transvection_mem_blockSpecialLinear hab (by simp) (by simp) _
    · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (IsRoot.neg hβ) l).1 hl
      refine ⟨_, ?_, hx' c⟩
      show gramSUToSL h _ _ ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))
      rw [hτ']
      exact LinearPilot.transvection_mem_blockSpecialLinear hab.symm (by simp) (by simp) _
  set c' := uEmbed6 h (Sp.x 3 h.fixedField τ 1 * Sp.x 3 h.fixedField (-τ) 1) with hc'def
  have hc' : gramSUToSL h _ c' = pairEmbed hab (zThreeSL (K := F)) := by
    rw [hc'def, map_mul, map_mul, hτ, hτ', OneMemClass.coe_one, pairEmbed_zThreeSL_eq]
  have hcZ : chainSU6 h ΦX c' ∈ subgroupToG e (zpowers (chainZ K β)) := by
    have e1 : chainSU6 h ΦX c' = ((e.symm (chainZ K β) : L) : G) := by
      rw [hc'def, map_mul, map_mul, show (1 : h.fixedField) = ε.symm 1 from (map_one _).symm,
        hx, hx', chainZ, map_mul, Subgroup.coe_mul]
    rw [e1]
    exact ⟨_, ⟨chainZ K β, mem_zpowers _, rfl⟩, rfl⟩
  intro l hl y hy
  obtain ⟨m', hm'B, hm'⟩ := hJ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  obtain ⟨m, rfl, hmB⟩ :=
    exists_chainSU6_eq_of_mem_centralizerPerfectCore h hr hker hab hc' hcZ y hy
  have hc1 : Commute (gramSUToSL h _ m') (gramSUToSL h _ m) :=
    LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right hm'B hmB
  have hc2 : Commute m' m := by
    refine gramSUToSL_injective h _ ?_
    rw [map_mul, map_mul]
    exact hc1.eq
  have hm'' : chainSU6 h ΦX m' = ((e.symm l : L) : G) := hm'
  rw [← hm'']
  exact hc2.map _

omit [Finite G] in
theorem card_zpowers_chainZ_of_sp {a b : Fin 6} (hab : a ≠ b) {β : Fin (Tag.rank .F4) → ℤ}
    {τ : Fin 3 → ℤ} (hτβ : c3ToF4 τ = β)
    (hτ : ∀ d : K, sp6ToSL6 (Sp.x 3 K τ d) = SpecialLinearGroup.transvection hab d)
    (hτ' : ∀ d : K, sp6ToSL6 (Sp.x 3 K (-τ) d) = SpecialLinearGroup.transvection hab.symm d) :
    Nat.card (zpowers (chainZ K β)) = 3 := by
  have hz : chainZ K β = c3LeviHom K (Sp.x 3 K τ 1 * Sp.x 3 K (-τ) 1) := by
    rw [map_mul, c3LeviHom_x, c3LeviHom_x, map_neg, hτβ, chainZ]
  have hs : sp6ToSL6 (Sp.x 3 K τ 1 * Sp.x 3 K (-τ) 1) = pairEmbed hab (zThreeSL (K := K)) := by
    rw [map_mul, hτ, hτ', pairEmbed_zThreeSL_eq]
  rw [Nat.card_zpowers, hz, orderOf_injective _ c3LeviHom_injective,
    ← orderOf_injective sp6ToSL6 sp6ToSL6_injective (Sp.x 3 K τ 1 * Sp.x 3 K (-τ) 1), hs,
    orderOf_injective _ (LinearPilot.pairEmbed_injective hab), SymplecticPilot.orderOf_zThreeSL]

theorem commute_rootSL2_rootR_centralizerPerfectCore_chainTw (hK : Nat.card K = 2)
    {e : L ≃* adjointGroup .F4 K} {ε : h.fixedField ≃+* K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)} (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hn : IsLeviNormalizedU h ε e ΦX) {a b : Fin 6} (hab : a ≠ b)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) {τ : Fin 3 → ℤ} (hτβ : c3ToF4 τ = β)
    (hτ : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField τ d)) =
      SpecialLinearGroup.transvection hab (d : F))
    (hτ' : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-τ) d)) =
      SpecialLinearGroup.transvection hab.symm (d : F))
    (hZ3 : Nat.card (zpowers (chainZ K β)) = 3)
    (ω : List ℕ) (hω₁ : wordAct ω rootR = β) (hω₂ : wordAct ω β = rootR) :
    ∀ l ∈ rootSL2 K rootR, ∀ y ∈ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))),
      Commute ((e.symm l : L) : G) y := by
  set w := wRep K ω with hw
  have hθβ : (rootSL2 K rootR).map (MulAut.conj w).toMonoidHom = rootSL2 K β := by
    rw [hw, map_wRep_rootSL2 ω isRoot_rootR, hω₁]
  have hβθ : (rootSL2 K β).map (MulAut.conj w).toMonoidHom = rootSL2 K rootR := by
    rw [hw, map_wRep_rootSL2 ω hβ, hω₂]
  set Z := zpowers (chainZ K β) with hZdef
  have hZle : Z ≤ rootSL2 K β := zpowers_chainZ_le hβ
  have hX' : X₀.map (MulAut.conj w⁻¹).toMonoidHom = Z := by
    refine eq_of_le_rootSL2 hK hβ ?_ hZle ?_ hZ3
    · rw [← map_conj_inv_eq_of_map_conj_eq_chain hβθ]
      exact Subgroup.map_mono hXr
    · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, hX₀]
  have hZ' : Z.map (MulAut.conj w⁻¹).toMonoidHom = X₀ := by
    refine eq_of_le_rootSL2 hK isRoot_rootR ?_ hXr ?_ hX₀
    · rw [← map_conj_inv_eq_of_map_conj_eq_chain hθβ]
      exact Subgroup.map_mono hZle
    · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, hZ3]
  have H := commute_rootSL2_centralizerPerfectCore_chainTw h (range_conjParamU h w hr)
    (ker_conjParamU_le h w hker) (isLeviNormalizedU_conjParamU h w hn) hab hβ hτβ hτ hτ'
  rw [subgroupToG_chainFrame, subgroupToG_chainFrame, hX', hZ', sup_comm] at H
  intro l hl y hy
  have hl' : w * l * w⁻¹ ∈ rootSL2 K β := by
    rw [← hθβ]
    exact ⟨l, hl, rfl⟩
  have hcomm := H _ hl' y hy
  rwa [chainFrame_symm_apply, show w⁻¹ * (w * l * w⁻¹) * w = l by group] at hcomm

theorem range_twLeviRestrict_le_centralizerPerfectCore {e : L ≃* adjointGroup .F4 K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ AmalgamNeighbour.X.nodes)
    (hperf : ⁅twLevi F h.barEquiv.toRingHom J, twLevi F h.barEquiv.toRingHom J⁆ =
      twLevi F h.barEquiv.toRingHom J)
    {Y : Subgroup (adjointGroup .F4 K)}
    (hY : Y ≤ alignedSubgroup e (twLeviRestrict ΦX hJ).range) :
    (twLeviRestrict ΦX hJ).range ≤ centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e Y) := by
  refine le_centralizerPerfectCore_sup (commutator_range_of_commutator_eq hperf _) ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have hx : twLeviRestrict ΦX hJ x ∈ ΦX.range := ⟨_, rfl⟩
    rw [hr] at hx
    exact centralizerPerfectCore_le_centralizer _ hx
  · rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact (mem_centralizer_iff.1 (hY hl) _ ⟨x, rfl⟩).symm

omit [Finite G] in
theorem gramSUToSL_uEmbed6_x_single_two (d : h.fixedField) :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 2 1) d)) =
      SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) (d : F) := by
  rw [gramSUToSL_uEmbed6, sp6ToSL6_x_single_two, map_transvection]
  rfl

omit [Finite G] in
theorem gramSUToSL_uEmbed6_x_neg_single_two (d : h.fixedField) :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-Pi.single 2 1) d)) =
      SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide).symm (d : F) := by
  rw [gramSUToSL_uEmbed6, sp6ToSL6_x_neg_single_two, map_transvection]
  rfl

omit [Finite G] in
theorem gramSUToSL_uEmbed6_x_root221 (d : h.fixedField) :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField ![2, 2, 1] d)) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) (d : F) := by
  have := fixedField_finite h
  have := fixedField_charP h
  rw [gramSUToSL_uEmbed6, sp6ToSL6_x_root221, map_transvection]
  rfl

omit [Finite G] in
theorem gramSUToSL_uEmbed6_x_neg_root221 (d : h.fixedField) :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-![2, 2, 1]) d)) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide).symm (d : F) := by
  have := fixedField_finite h
  have := fixedField_charP h
  rw [gramSUToSL_uEmbed6, sp6ToSL6_x_neg_root221, map_transvection]
  rfl

omit [Finite G] in
theorem c3ToF4_single_two_chainTw : c3ToF4 (Pi.single 2 1) = Pi.single 1 1 := by
  rw [c3ToF4_single]
  rfl

omit [Finite G] in
include h in
theorem exists_unit_zpow_two_ne_one_chainTw : ∃ t : Fˣ, ((t ^ (2 : ℤ) : Fˣ) : F) ≠ 1 := by
  have h4 : 4 ≤ Nat.card F := by
    rw [h.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)
  obtain ⟨t, ht⟩ := exists_units_sq_ne_one_of_four_le (F := F) h4
  refine ⟨t, fun h1 => ht ?_⟩
  rw [zpow_two] at h1
  rw [sq]
  exact Units.ext h1

variable {e : L ≃* adjointGroup .F4 K}
  {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
  {X₀ : Subgroup (adjointGroup .F4 K)}

theorem f4RootPairAlign_rootR_le_alignedTw_three (hK : Nat.card K = 2) (ε : h.fixedField ≃+* K)
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hn : IsLeviNormalizedU h ε e ΦX) :
    f4RootPairAlign K rootR ≤ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range := by
  obtain ⟨t, ht⟩ := exists_unit_zpow_two_ne_one_chainTw h
  have hperf := commutator_twLevi_three h.barEquiv.toRingHom h.bar_bar ht
  have hY : zpowers (chainZ K (Pi.single 1 1)) ≤
      alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range := by
    refine (zpowers_chainZ_le (isRoot_single _ 1)).trans ?_
    rw [← f4RootPairAlign_eq_rootSL2 (isRoot_single _ 1)]
    exact f4RootPairAlign_a2_le_alignedTw_three h ε hn
  have hZ3 := card_zpowers_chainZ_of_sp (K := K) (show (2 : Fin 6) ≠ 5 by decide)
    c3ToF4_single_two_chainTw sp6ToSL6_x_single_two sp6ToSL6_x_neg_single_two
  rw [f4RootPairAlign_eq_rootSL2 isRoot_rootR]
  intro l hl
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro y hy
  have hy' := range_twLeviRestrict_le_centralizerPerfectCore h hr three_subset_X hperf hY hy
  exact (commute_rootSL2_rootR_centralizerPerfectCore_chainTw h hK hXr hX₀ hr hker hn
    (show (2 : Fin 6) ≠ 5 by decide) (isRoot_single _ 1) c3ToF4_single_two_chainTw
    (gramSUToSL_uEmbed6_x_single_two h) (gramSUToSL_uEmbed6_x_neg_single_two h) hZ3
    _ wordAct_rootR_a2.1 wordAct_rootR_a2.2 l hl y hy').symm.eq

theorem f4RootPairAlign_rootR_le_alignedTw_two (hK : Nat.card K = 2) (ε : h.fixedField ≃+* K)
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hn : IsLeviNormalizedU h ε e ΦX) :
    f4RootPairAlign K rootR ≤ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range := by
  obtain ⟨t, ht⟩ := exists_unit_zpow_two_ne_one_chainTw h
  have hperf := commutator_twLevi_two_chainTw h.barEquiv.toRingHom h.bar_bar ht
  have hY : zpowers (chainZ K rootE1mE2Align) ≤
      alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range := by
    refine (zpowers_chainZ_le isRoot_rootE1mE2Align).trans ?_
    rw [← f4RootPairAlign_eq_rootSL2 isRoot_rootE1mE2Align]
    exact f4RootPairAlign_e1e2_le_alignedTw_two h ε hn
  have hZ3 := card_zpowers_chainZ_of_sp (K := K) (show (0 : Fin 6) ≠ 3 by decide)
    c3ToF4_root221 sp6ToSL6_x_root221 sp6ToSL6_x_neg_root221
  rw [f4RootPairAlign_eq_rootSL2 isRoot_rootR]
  intro l hl
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro y hy
  have hy' := range_twLeviRestrict_le_centralizerPerfectCore h hr two_subset_X hperf hY hy
  exact (commute_rootSL2_rootR_centralizerPerfectCore_chainTw h hK hXr hX₀ hr hker hn
    (show (0 : Fin 6) ≠ 3 by decide) isRoot_rootE1mE2Align c3ToF4_root221
    (gramSUToSL_uEmbed6_x_root221 h) (gramSUToSL_uEmbed6_x_neg_root221 h) hZ3
    _ wordAct_rootR_e1e2.1 wordAct_rootR_e1e2.2 l hl y hy').symm.eq

end Overlap

end CFSG.SeitzReduction.F4Pilot
