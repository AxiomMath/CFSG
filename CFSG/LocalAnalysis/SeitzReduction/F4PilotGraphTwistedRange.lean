module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedNorm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup nHat nHatE nd)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

local instance f4PilotGraphTwistedRangeNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Tori


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem centralizer_neighbourTorusG_X_inf_Y_le (e : L ≃* adjointGroup .F4 K) :
    centralizer (neighbourTorusG e .X : Set G) ⊓ centralizer (neighbourTorusG e .Y : Set G) ≤
      centralizer (leviTorusG e {1, 2} : Set G) := by
  rintro g ⟨hgX, hgY⟩
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨y, hyT, rfl⟩ := (mem_modelToG e).1 hx
  obtain ⟨b, hb, hby⟩ := mem_leviTorus.1 hyT
  set b₁ : Fin (Tag.rank .F4) → Kˣ := fun i => if i = 0 then b i else 1 with hb₁
  set b₂ : Fin (Tag.rank .F4) → Kˣ := fun i => if i = 0 then 1 else b i with hb₂
  have hb12 : b = b₁ * b₂ := funext fun i => by
    by_cases hi : i = 0
    · simp [hb₁, hb₂, hi]
    · simp [hb₁, hb₂, hi]
  have h1 : rootDiagUnit .F4 b₁ ∈ torusLineR K := by
    rw [torusLineR_eq_leviTorus]
    refine rootDiagUnit_mem_leviTorus fun j hj => ?_
    have : j ≠ 0 := by
      revert j
      decide
    simp [hb₁, this]
  have h2 : rootDiagUnit .F4 b₂ ∈ torusLineS K := by
    refine rootDiagUnit_mem_leviTorus fun j hj => ?_
    by_cases hj0 : j = 0
    · simp [hb₂, hj0]
    · have hj12 : j ∈ ({1, 2} : Finset (Fin (Tag.rank .F4))) := by
        revert j
        decide
      simp [hb₂, hj0, hb j hj12]
  set y₁ : adjointGroup .F4 K := ⟨_, leviTorus_le_adjointGroup _
    (show rootDiagUnit .F4 b₁ ∈ leviTorus K {1, 2, 3} from torusLineR_eq_leviTorus (K := K) ▸ h1)⟩
  set y₂ : adjointGroup .F4 K := ⟨_, leviTorus_le_adjointGroup _ h2⟩
  have hy : y = y₁ * y₂ := Subtype.ext (by
    change (y : ModGL .F4 K) = rootDiagUnit .F4 b₁ * rootDiagUnit .F4 b₂
    rw [← hby, hb12, rootDiagUnit_mul])
  have c1 := mem_centralizer_iff.1 hgX _ (symm_mem_modelToG e (H := torusLineR K) (x := y₁) h1)
  have c2 := mem_centralizer_iff.1 hgY _ (symm_mem_modelToG e (H := torusLineS K) (x := y₂) h2)
  rw [hy, map_mul, L.coe_mul]
  change ((e.symm y₁ : L) : G) * g = g * ((e.symm y₁ : L) : G) at c1
  change ((e.symm y₂ : L) : G) * g = g * ((e.symm y₂ : L) : G) at c2
  rw [mul_assoc, c2, ← mul_assoc, c1, mul_assoc]

theorem le_pieceCore_one_two_of_le (e : L ≃* adjointGroup .F4 K) {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) (hX : H ≤ neighbourCore e .X) (hY : H ≤ neighbourCore e .Y) :
    H ≤ pieceCore e {1, 2} :=
  le_centralizerPerfectCore hH ((le_inf (hX.trans (centralizerPerfectCore_le_centralizer _))
    (hY.trans (centralizerPerfectCore_le_centralizer _))).trans
      (centralizer_neighbourTorusG_X_inf_Y_le e))

end Tori

section Aux

theorem commutator_range_of_commutator_eq {M : Type} [Group M] {S : Subgroup M}
    (hS : ⁅S, S⁆ = S) {G : Type} [Group G] (φ : S →* G) : ⁅φ.range, φ.range⁆ = φ.range := by
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hS]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]


variable {k : Type} [Field k] (θ : k →+* k)

theorem conj_nHat_three_two_mem {x : fixedGroup k θ} (hx : x ∈ rankOne (twistedRootGroup k θ) 3) :
    (nHat θ 3 * nHat θ 2) * x * (nHat θ 3 * nHat θ 2)⁻¹ ∈ rankOne (twistedRootGroup k θ) 2 := by
  have key : ∀ β : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 β → ∀ y ∈ twistedRootGroup k θ β,
      (nHat θ 3 * nHat θ 2) * y * (nHat θ 3 * nHat θ 2)⁻¹ ∈
        twistedRootGroup k θ (reflect .F4 3 (reflect .F4 2 β)) := by
    intro β hβ y hy
    have h1 := CFSG.LieType.Steinberg.TwistedE6.nHat_conj_mem θ 2 hβ hy
    have h2 := CFSG.LieType.Steinberg.TwistedE6.nHat_conj_mem θ 3 (hβ.reflect 2) h1
    have e : (nHat θ 3 * nHat θ 2) * y * (nHat θ 3 * nHat θ 2)⁻¹ =
        nHat θ 3 * (nHat θ 2 * y * (nHat θ 2)⁻¹) * (nHat θ 3)⁻¹ := by group
    rw [e]
    exact h2
  have hle : rankOne (twistedRootGroup k θ) 3 ≤ (rankOne (twistedRootGroup k θ) 2).comap
      (MulAut.conj (nHat θ 3 * nHat θ 2)).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have h := key _ (isRoot_single _ 3) y hy
      rw [show reflect .F4 3 (reflect .F4 2 (Pi.single 3 1)) = Pi.single 2 1 by decide] at h
      exact le_sup_left (a := twistedRootGroup k θ (Pi.single 2 1)) h
    · have h := key _ (isRoot_neg_single _ 3) y hy
      rw [show reflect .F4 3 (reflect .F4 2 (-Pi.single 3 1)) = -Pi.single 2 1 by decide] at h
      exact le_sup_right (b := twistedRootGroup k θ (-Pi.single 2 1)) h
  exact hle hx

end Aux

section AuxSigma


variable {k : Type} [Field k] (θ : k →+* k)

theorem sigmaHat_sigmaHat (x : fixedGroup k θ) : sigmaHat θ (sigmaHat θ x) = x :=
  Subtype.ext (CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id k) (fun _ => rfl)
    (x : e6Data_valid.minGroup k))

theorem sigmaHat_nHat (i : Fin (Tag.rank .F4)) : sigmaHat θ (nHat θ i) = nHat θ i :=
  Subtype.ext (CFSG.LieType.Steinberg.TwistedE6.sigma_nHatE (RingHom.id k) i)

theorem sigmaHat_eq_of_mem_twLevi_zero {x : fixedGroup k θ} (hx : x ∈ twLevi k θ {0}) :
    sigmaHat θ x = x := by
  have hfix : ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single (nd 1) 1 ∨ γ = -Pi.single (nd 1) 1) →
      CFSG.LieType.Steinberg.TwistedE6.rho γ = γ := by
    rintro γ (rfl | rfl)
    · rw [CFSG.LieType.Steinberg.TwistedE6.rho_single]
      rfl
    · rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single]
      rfl
  have key : ∀ γ : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 γ →
      (γ = Pi.single (nd 1) 1 ∨ γ = -Pi.single (nd 1) 1) →
      twistedRootGroup k θ (CFSG.LieType.Steinberg.TwistedE6.proj γ) ≤
        MonoidHom.eqLocus (sigmaHat θ) (MonoidHom.id _) := by
    intro γ hγ hγ' y hy
    obtain ⟨c, -, hyc⟩ := (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed θ
      hγ rfl (hfix γ hγ') y).1 hy
    apply Subtype.ext
    change CFSG.LieType.Steinberg.TwistedE6.sigma k (RingHom.id k) (y : e6Data_valid.minGroup k) =
      (y : e6Data_valid.minGroup k)
    rw [hyc, CFSG.LieType.Steinberg.TwistedE6.sigma_xm (RingHom.id k) hγ, hfix γ hγ',
      CFSG.LieType.Steinberg.TwistedE6.twistSign_of_rho_eq hγ (hfix γ hγ'), Int.cast_one, one_mul,
      RingHom.id_apply]
  have hle : twLevi k θ {0} ≤ MonoidHom.eqLocus (sigmaHat θ) (MonoidHom.id _) := by
    rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
    refine sup_le ?_ ?_
    · have h := key _ (isRoot_single _ (nd 1)) (.inl rfl)
      rwa [CFSG.LieType.Steinberg.TwistedE6.proj_single] at h
    · have h := key _ (isRoot_neg_single _ (nd 1)) (.inr rfl)
      rwa [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single] at h
  exact hle hx

variable {θ} in
theorem range_twLeviRestrict_eq {G : Type} [Group G]
    {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G} {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G}
    (htw : (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY one_two_subset_Y x) ∨
      (∀ x y : twLevi k θ {1, 2}, (y : fixedGroup k θ) = sigmaHat θ x →
        twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y)) :
    (twLeviRestrict ΦX one_two_subset_X).range = (twLeviRestrict ΦY one_two_subset_Y).range := by
  rcases htw with h | h
  · rw [MonoidHom.ext h]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨⟨sigmaHat θ x, sigmaHat_mem_twLevi x.2⟩, (h x _ rfl).symm⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨⟨sigmaHat θ y, sigmaHat_mem_twLevi y.2⟩, h _ y (sigmaHat_sigmaHat θ y).symm⟩

end AuxSigma

section Generation


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit
  [Finite G] [Finite K] [CharP K 2] in
theorem range_twLeviRestrict_le_pieceCore (e : L ≃* adjointGroup .F4 K) {k : Type} [Field k]
    {θ : k →+* k} {N₁ N₂ : AmalgamNeighbour} (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X))
    {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G} {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G}
    (hrX : ΦX.range = neighbourCore e N₁) (hrY : ΦY.range = neighbourCore e N₂)
    (htw : (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY one_two_subset_Y x) ∨
      (∀ x y : twLevi k θ {1, 2}, (y : fixedGroup k θ) = sigmaHat θ x →
        twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y))
    (hP : ⁅twLevi k θ {1, 2}, twLevi k θ {1, 2}⁆ = twLevi k θ {1, 2}) :
    (twLeviRestrict ΦX one_two_subset_X).range ≤ pieceCore e {1, 2} ∧
      (twLeviRestrict ΦY one_two_subset_Y).range ≤ pieceCore e {1, 2} := by
  have hR := commutator_range_of_commutator_eq hP (twLeviRestrict ΦX one_two_subset_X)
  have heq := range_twLeviRestrict_eq htw
  have h1 : (twLeviRestrict ΦX one_two_subset_X).range ≤ neighbourCore e N₁ := by
    rw [← hrX]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have h2 : (twLeviRestrict ΦX one_two_subset_X).range ≤ neighbourCore e N₂ := by
    rw [heq, ← hrY]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hle : (twLeviRestrict ΦX one_two_subset_X).range ≤ pieceCore e {1, 2} := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_pieceCore_one_two_of_le e hR h1 h2
    · exact le_pieceCore_one_two_of_le e hR h2 h1
  exact ⟨hle, heq ▸ hle⟩

omit [Finite G] [Finite K] [CharP K 2]
  in
theorem pieceCore_one_two_le_pieceSpan (e : L ≃* adjointGroup .F4 K) :
    pieceCore e {1, 2} ≤ pieceSpan e :=
  le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
    ⟨{1, 2}, by decide⟩

omit [Finite G] in
theorem neighbourCore_le_pieceSpan_of_twParamX (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .F4 K)
    {e₁ : L ≃* adjointGroup .F4 K} {N₁ : AmalgamNeighbour} {f : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {h : UnitaryFieldData 2 f F} {ε : h.fixedField ≃+* K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hr : ΦX.range = neighbourCore e N₁) (hn : IsLeviNormalizedU h ε e₁ ΦX)
    (hM : (twLeviRestrict ΦX one_two_subset_X).range ≤ pieceSpan e) :
    neighbourCore e N₁ ≤ pieceSpan e := by
  have hθ : ∀ c, h.barEquiv.toRingHom (h.barEquiv.toRingHom c) = c := h.bar_bar
  set S : Subgroup (fixedGroup F h.barEquiv.toRingHom) :=
    ((pieceSpan e).comap ΦX).map
      (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype with hS
  have hS12 : twLevi F h.barEquiv.toRingHom {1, 2} ≤ S := fun y hy =>
    ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_X hy⟩, hM ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  set n : fixedGroup F h.barEquiv.toRingHom :=
    nHat h.barEquiv.toRingHom 3 * nHat h.barEquiv.toRingHom 2 with hn_def
  have hnX : n ∈ twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
    mul_mem (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)
        (CFSG.LieType.Steinberg.TwistedE6.nHat_mem_rankOne h.barEquiv.toRingHom hθ 3))
      (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)
        (CFSG.LieType.Steinberg.TwistedE6.nHat_mem_rankOne h.barEquiv.toRingHom hθ 2))
  have hσn : sigmaHat h.barEquiv.toRingHom n = n := by
    rw [hn_def, map_mul, sigmaHat_nHat, sigmaHat_nHat]
  have hfixn : (twParamEquiv h).symm ⟨n, hnX⟩ ∈ fixedSubgroup (barSU6 h) :=
    (twParamEquiv_symm_of_sigmaHat h (x := ⟨n, hnX⟩) (y := ⟨n, hnX⟩) hσn.symm).symm
  rw [fixedSubgroup_barSU6 h] at hfixn
  obtain ⟨s, hs⟩ := hfixn
  have hnL : ΦX ⟨n, hnX⟩ ∈ L := by
    have e1 : (⟨n, hnX⟩ : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) =
        twParamEquiv h (uEmbed6 h s) := by
      rw [hs, MulEquiv.apply_symm_apply]
    rw [e1, hn s]
    have hmem : levi6Hom e₁ ε s ∈ (levi6Hom e₁ ε).range := ⟨s, rfl⟩
    rw [range_levi6Hom] at hmem
    exact Subgroup.map_subtype_le _ hmem
  have hnS : n ∈ S := ⟨⟨n, hnX⟩, le_pieceSpan hq e hnL, rfl⟩
  have hS3 : rankOne (twistedRootGroup F h.barEquiv.toRingHom) 3 ≤ S := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ S := hS12 (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)
      (conj_nHat_three_two_mem h.barEquiv.toRingHom hy))
    have e2 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [e2]
    exact mul_mem (mul_mem (inv_mem hnS) h1) hnS
  have htop : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes ≤ S := by
    refine iSup₂_le fun j hj => ?_
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by
      revert j
      decide
    rcases hj' with rfl | rfl | rfl
    · exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)).trans hS12
    · exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)).trans hS12
    · exact hS3
  rw [← hr]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', hx', hxx'⟩ := htop x.2
  have hx'x : x' = x := Subtype.ext hxx'
  rw [← hx'x]
  exact hx'

omit [CharP K 2] in
theorem neighbourCore_le_pieceSpan_of_twParamY {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N₂ : AmalgamNeighbour} (hN₂ : N₂ = .X ∨ N₂ = .Y)
    {k : Type} [Field k] {θ : k →+* k}
    {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G} (hr : ΦY.range = neighbourCore e N₂)
    (hc : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y)
    (hP0 : ⁅twLevi k θ {0}, twLevi k θ {0}⁆ = twLevi k θ {0})
    (hM : (twLeviRestrict ΦY one_two_subset_Y).range ≤ pieceSpan e) :
    neighbourCore e N₂ ≤ pieceSpan e := by
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set P := (twLeviRestrict ΦY zero_subset_Y).range with hP
  have hPp : ⁅P, P⁆ = P := commutator_range_of_commutator_eq hP0 _
  have hPE : P ≤ neighbourCore e N₂ := by
    rw [← hr]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hPt : P ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := hc ⟨x, CFSG.LieType.CurtisTits.levi_mono _ zero_subset_Y x.2⟩
      ⟨x, CFSG.LieType.CurtisTits.levi_mono _ zero_subset_Y x.2⟩
      (sigmaHat_eq_of_mem_twLevi_zero θ x.2).symm
    rw [twLeviRestrict_apply]
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcore : P ≤ perfectCore (neighbourCore e N₂ ⊓ centralizer ({t} : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hPE hPt) hPp
  have hPL : P ≤ L := by
    refine hcore.trans ?_
    rcases hN₂ with rfl | rfl
    · rw [perfectCore_neighbourCore_inf_centralizer_X hw hf e]
      exact modelToG_le e _
    · have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
      rw [neighbourCore_Y_eq_X, perfectCore_neighbourCore_inf_centralizer_X hw hf]
      exact modelToG_le _ _
  set S : Subgroup (fixedGroup k θ) :=
    ((pieceSpan e).comap ΦY).map (twLevi k θ AmalgamNeighbour.Y.nodes).subtype with hS
  have hS12 : twLevi k θ {1, 2} ≤ S := fun y hy =>
    ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_Y hy⟩, hM ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  have hS0 : twLevi k θ {0} ≤ S := fun y hy =>
    ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ zero_subset_Y hy⟩,
      le_pieceSpan hq e (hPL ⟨⟨y, hy⟩, rfl⟩), rfl⟩
  have htop : twLevi k θ AmalgamNeighbour.Y.nodes ≤ S := by
    refine iSup₂_le fun j hj => ?_
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      revert j
      decide
    rcases hj' with rfl | rfl | rfl
    · exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)).trans hS0
    · exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)).trans hS12
    · exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (by decide)).trans hS12
  rw [← hr]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', hx', hxx'⟩ := htop x.2
  have hx'x : x' = x := Subtype.ext hxx'
  rw [← hx'x]
  exact hx'

end Generation

end CFSG.SeitzReduction.F4Pilot
