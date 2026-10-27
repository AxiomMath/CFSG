module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerClass
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerM1

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.E6SecondGraphFixed (SecondGraphFixedSubgroup)
open CFSG.SeitzReduction.E6Pilot (corootTuple)

local instance f4PilotXiCaseLRowsNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotXiCaseLRowsNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotXiCaseLRowsNeZeroE6' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

theorem natCard_fixSubgroup_of_secondGraph {Gm : Type*} [Group Gm] {C J : Subgroup Gm}
    {P t : Gm} {H : Type*} [Group H] {e : J ≃* H} (hsec : SecondGraphFixedSubgroup C J P t e)
    {η : MulAut C} (hη : ∀ g : C, (η g : Gm) = P * g * P⁻¹) (hx : t ∈ C) :
    ∃ htJ : t ∈ J, Nat.card (E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η)) =
      Nat.card (centralizer ({e ⟨t, htJ⟩} : Set H)) := by
  obtain ⟨htJ, hJC, η₀, hη₀, huniq, -, -, hfix, -, -, hiff1, hiff2⟩ := hsec
  have hηη₀ : η = η₀ := huniq η hη
  subst hηη₀
  refine ⟨htJ, ?_⟩
  set s := e ⟨t, htJ⟩ with hs
  set φ : H →* C := (J.subgroupOf C).subtype.comp
    ((subgroupOfEquivOfLe hJC).symm.toMonoidHom.comp e.symm.toMonoidHom) with hφ
  have hφe : ∀ x : J, ((φ (e x) : C) : Gm) = x := fun x => by
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    have h1 := congrArg Subtype.val hab
    rw [hφe, hφe] at h1
    rw [Subtype.ext h1]
  have hfixeq : E6Pilot.fixSubgroup (MulAut.conj (⟨t, hx⟩ : C) * η) =
      (centralizer ({s} : Set H)).map φ := by
    ext g
    constructor
    · intro hg
      have hg' : (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) g = g := hg
      obtain ⟨hgJ, -⟩ := (hfix g).1 hg'
      refine ⟨e ⟨g, hgJ⟩, ?_, Subtype.ext (hφe _)⟩
      exact mem_centralizer_singleton_iff.2 ((hiff1 ⟨g, hgJ⟩).1 ⟨g.2, hg'⟩)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, ⟨hxC, hxfix⟩, rfl⟩ := (hiff2 y).1 (mem_centralizer_singleton_iff.1 hy)
      have h1 : φ (e x) = ⟨x, hxC⟩ := Subtype.ext (hφe x)
      change (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) (φ (e x)) = φ (e x)
      rw [h1]
      exact hxfix
  rw [hfixeq, card_map_of_injective hφinj]

theorem permLattice_rhoE6_single_two :
    permLattice rhoE6 (Pi.single (2 : Fin (Tag.rank .E6)) (1 : ℤ)) = Pi.single 4 1 := by
  decide +kernel

section RowE6


theorem exists_xiCaseLModel_E6 {f : ℕ} (hf : 2 ≤ f) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ f) {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K') :
    ∃ (J : Subgroup (ModGL TwistTag.E6.tag K')) (eJ : J ≃* adjointGroup .F4 K'),
      XiCaseLModel (adjointGroup TwistTag.E6.tag K') J η eJ ⊤ ⟨_, hx⟩ := by
  have hf1 : 1 ≤ f := by omega
  have := charP_two_of_natCard_eq_two_pow hK'
  have h2 : (2 : K') = 0 := CharP.cast_eq_zero K' 2
  have hM' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf1 hK' hM'
  let _ : Algebra K' (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hσM : ∀ c : GaloisField 2 (2 * f), iterateFrobenius (GaloisField 2 (2 * f)) 2 f c =
      c ^ 2 ^ f := fun c => iterateFrobenius_def (p := 2) f c
  obtain ⟨⟨hcan, -⟩, -⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf1 K' (GaloisField 2 (2 * f)) hK' hM' _
      hσM
  obtain ⟨ht, -, -, -, ⟨eJ, heJ1, heJ2, hsec⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf1 K' (GaloisField 2 (2 * f)) hK' hM' _ hσM
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, -⟩ := hcan
  have hηη₀ : η = η₀ := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη₀ h).symm)
  subst hηη₀
  have hq : 4 ≤ Nat.card K' := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hmemJ : ∀ g ∈ twistedFixedGroup TwistTag.E6 K' (RingHom.id K'),
      g ∈ (twistedFixedGroup TwistTag.E6 K' (RingHom.id K')).map (baseChangeGL (RingHom.id K')) :=
    fun g hg => ⟨g, hg, baseChangeGL_id K' g⟩
  have heJΨ : ∀ (g : ModGL TwistTag.E6.tag K') (hg : g ∈ twistedFixedGroup TwistTag.E6 K'
      (RingHom.id K')), (eJ ⟨g, hmemJ g hg⟩ : ModGL .F4 K') = e6FixedToF4 K' ⟨g, hg⟩ :=
    fun g hg => heJ1 ⟨g, hg⟩ ⟨g, hmemJ g hg⟩ (baseChangeGL_id K' g).symm
  refine ⟨_, eJ, ⟨le_rfl, h2, hη, hJC, hfix₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    rw [Subgroup.card_top, Nat.card_units]
    omega
  ·
    intro δ hδ c _
    refine ⟨hmemJ _ (rootDiagUnit_corootTuple_mem_twistedFixedGroup hδ c), ?_⟩
    rw [heJΨ]
    exact e6FixedToF4_corootTuple_mem_leviTorus hδ c
  ·
    intro a _
    have hg₂ := f4OrbitXUnit_mem (K := K') 2 a
    refine ⟨⟨_, hmemJ _ hg₂⟩, ?_, ⟨_, pinnedX_mem_adjointGroup (Pi.single 2 1) a⟩, ?_⟩
    · rw [heJΨ _ hg₂, e6FixedToF4_f4OrbitXUnit h2, pinnedX_single]
    · rw [conj_pinnedX_mul_eta_E6 h2 hη (isRoot_single _ 2) a]
      congr 2
      apply Subtype.ext
      change pinnedX TwistTag.E6.tag K' (Pi.single 2 1) a *
          pinnedX TwistTag.E6.tag K' (permLattice TwistTag.E6.perm (Pi.single 2 1)) a =
        f4OrbitXUnit K' 2 a
      have hρ : permLattice TwistTag.E6.perm (Pi.single (2 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) =
          Pi.single 4 1 := permLattice_rhoE6_single_two
      rw [hρ, pinnedX_single, pinnedX_single, E6Pilot.f4OrbitXUnit_two]
      rfl
  ·
    exact not_conj_eta_xi_E6 hf1 hK' hη hx
  ·
    obtain ⟨htJ, hJC', η', hη', huniq, -, -, hfix, -⟩ := hsec
    have hηη' : η = η' := huniq η hη
    subst hηη'
    intro g hg
    exact ((hfix g).1 hg).1
  ·
    obtain ⟨htJ, hcard⟩ := natCard_fixSubgroup_of_secondGraph hsec hη hx
    rw [hcard]
    obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
    have h1 : (⟨c, hcC⟩ : adjointGroup .F4 K') * eJ ⟨_, htJ⟩ * (⟨c, hcC⟩ : adjointGroup .F4 K')⁻¹ =
        yRep K' .t := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heJ2 htJ]
      exact hc
    rw [← h1, natCard_centralizer_conj]
  ·
    exact xiFixPerfectE6Input_holds f K' hf hK' η hη hx

end RowE6

section RowTwistedE6


theorem exists_xiCaseLModel_twistedE6 {f : ℕ} (hf : 2 ≤ f) {K₂ : Type} [Field K₂] [Finite K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ) :
    ∃ (J : Subgroup (ModGL TwistTag.E6.tag K₂))
      (eJ : J ≃* adjointGroup .F4 (GaloisField 2 f)) (A : Subgroup K₂ˣ),
      XiCaseLModel (graphFixedRootGroup TwistTag.E6 K₂ σ) J η eJ A ⟨_, hx⟩ := by
  have hf1 : 1 ≤ f := by omega
  have := TwistedE6Pilot.charP_two_of_card hf1 hK₂
  have h2 : (2 : K₂) = 0 := CharP.cast_eq_zero K₂ 2
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have := charP_two_of_natCard_eq_two_pow hk
  have : Finite (GaloisField 2 f) := finite_of_natCard_eq_two_pow hk
  have h2k : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero _ 2
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf1 hk hK₂
  let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
  have hι : ∀ c, algebraMap (GaloisField 2 f) K₂ c = ι c := fun _ => rfl
  obtain ⟨-, ⟨hcan, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf1 (GaloisField 2 f) K₂ hk hK₂ σ hσ
  obtain ⟨ht, -, -, -, -, ⟨eJ, heJ1, heJ2, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf1 (GaloisField 2 f) K₂ hk hK₂ σ hσ
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, -⟩ := hcan
  have hηη₀ : η = η₀ := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη₀ h).symm)
  subst hηη₀
  have hσσ : ∀ c, σ (σ c) = c := TwistedE6Pilot.apply_apply_eq hK₂ hσ
  obtain ⟨e₁, he₁⟩ := TwistedE6Pilot.exists_apply_ne hf1 hK₂ hσ
  have hσι : ∀ a : GaloisField 2 f, σ (ι a) = ι a := by
    intro a
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    rw [hσ, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hmemJ : ∀ g ∈ twistedFixedGroup TwistTag.E6 (GaloisField 2 f) (RingHom.id _),
      baseChangeGL (algebraMap (GaloisField 2 f) K₂) g ∈
        (twistedFixedGroup TwistTag.E6 (GaloisField 2 f) (RingHom.id _)).map
          (baseChangeGL (algebraMap (GaloisField 2 f) K₂)) :=
    fun g hg => ⟨g, hg, rfl⟩
  have heJΨ : ∀ (g : ModGL TwistTag.E6.tag (GaloisField 2 f))
      (hg : g ∈ twistedFixedGroup TwistTag.E6 (GaloisField 2 f) (RingHom.id _)),
      (eJ ⟨_, hmemJ g hg⟩ : ModGL .F4 (GaloisField 2 f)) = e6FixedToF4 _ ⟨g, hg⟩ :=
    fun g hg => heJ1 ⟨g, hg⟩ ⟨_, hmemJ g hg⟩ rfl
  have hιinj : Function.Injective (Units.map (algebraMap (GaloisField 2 f) K₂).toMonoidHom) :=
    fun a b hab => Units.ext ((algebraMap (GaloisField 2 f) K₂).injective
      (congrArg Units.val hab))
  refine ⟨_, eJ, (⊤ : Subgroup (GaloisField 2 f)ˣ).map
    (Units.map (algebraMap (GaloisField 2 f) K₂).toMonoidHom),
    ⟨graphFixedRootGroup_E6_le_adjointGroup σ, h2, hη, hJC, hfix₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    rw [card_map_of_injective hιinj, Subgroup.card_top, Nat.card_units, hk]
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  ·
    rintro δ hδ _ ⟨c₀, -, rfl⟩
    have hd : rootDiagUnit TwistTag.E6.tag (corootTuple δ
        (Units.map (algebraMap (GaloisField 2 f) K₂).toMonoidHom c₀)) =
        baseChangeGL (algebraMap (GaloisField 2 f) K₂)
          (rootDiagUnit TwistTag.E6.tag (corootTuple δ c₀)) := by
      refine Eq.trans ?_ (baseChangeGL_rootDiagUnit (algebraMap (GaloisField 2 f) K₂)
        (τ := TwistTag.E6.tag) (corootTuple δ c₀)).symm
      congr 1
      funext i
      simp only [corootTuple, map_zpow]
    rw [hd]
    refine ⟨hmemJ _ (rootDiagUnit_corootTuple_mem_twistedFixedGroup hδ c₀), ?_⟩
    rw [heJΨ]
    exact e6FixedToF4_corootTuple_mem_leviTorus hδ c₀
  ·
    intro a _
    have hg₂ := f4OrbitXUnit_mem (K := GaloisField 2 f) 2 a
    have hz : baseChangeGL (algebraMap (GaloisField 2 f) K₂) (f4OrbitXUnit (GaloisField 2 f) 2 a) =
        twistedE6PairX σ (Pi.single 2 1) (ι a) := by
      have hρ : permLattice TwistTag.E6.perm (Pi.single (2 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) =
          Pi.single 4 1 := permLattice_rhoE6_single_two
      have h1 : f4OrbitXUnit (GaloisField 2 f) 2 a =
          xUnit TwistTag.E6.tag (GaloisField 2 f) 2 a * xUnit TwistTag.E6.tag (GaloisField 2 f) 4 a :=
        E6Pilot.f4OrbitXUnit_two a
      have h3 : twistedE6PairX σ (Pi.single 2 1) (ι a) =
          pinnedX TwistTag.E6.tag K₂ (Pi.single 2 1) (ι a) *
            pinnedX TwistTag.E6.tag K₂ (permLattice TwistTag.E6.perm (Pi.single 2 1)) (σ (ι a)) :=
        rfl
      rw [h1, map_mul, baseChangeGL_xUnit, baseChangeGL_xUnit, h3, hρ, hσι, pinnedX_single,
        pinnedX_single, hι]
    refine ⟨⟨_, hmemJ _ hg₂⟩, ?_, ?_⟩
    · rw [heJΨ _ hg₂, e6FixedToF4_f4OrbitXUnit h2k, pinnedX_single]
    · obtain ⟨g, hg⟩ := exists_conj_eq_twistedE6PairX_mul_eta hσσ he₁ hη (isRoot_single _ 2)
        (hσι a)
      refine ⟨g, hg.trans ?_⟩
      congr 2
      exact Subtype.ext hz.symm
  ·
    exact not_conj_eta_xi_twistedE6 hf1 hK₂ hσ hη hx
  ·
    obtain ⟨htJ, hJC', η', hη', huniq, -, -, hfix, -⟩ := hsec
    have hηη' : η = η' := huniq η hη
    subst hηη'
    intro g hg
    exact ((hfix g).1 hg).1
  ·
    obtain ⟨htJ, hcard⟩ := natCard_fixSubgroup_of_secondGraph hsec hη hx
    rw [hcard]
    obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
    have h1 : (⟨c, hcC⟩ : adjointGroup .F4 (GaloisField 2 f)) * eJ ⟨_, htJ⟩ *
        (⟨c, hcC⟩ : adjointGroup .F4 (GaloisField 2 f))⁻¹ = yRep (GaloisField 2 f) .t := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heJ2 htJ]
      exact hc
    rw [← h1, natCard_centralizer_conj]
  ·
    exact xiFixPerfectTwistedE6Input_holds f K₂ σ hf hK₂ hσ η hη hx

end RowTwistedE6

end CFSG.SeitzReduction.F4Pilot
