module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7S
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InInner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.ComponentClassification.Burgoyne.E2.TwE6In
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem eq_rootDiagUnit_of_commute_orbitGroups_two_e6
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hq : 3 ≤ D.q)
    (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    {z : ModGL .E6 k} (hzG : z ∈ adjointGroup .E6 k)
    (hz : ∀ J' : Set.range D.classOrbit, ∀ w ∈ (D.withOrbit J').orbitGroup, z * w = w * z) :
    ∃ b : Fin (Tag.rank .E6) → kˣ, z = rootDiagUnit .E6 b ∧
      ∀ j : Fin 6, j ≠ 1 → b (CatLeafProof.e6Node j) = 1 := by
  have hcard : ∀ J' : Set.range D.classOrbit,
      ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 :=
    fun J' => orbitCard_of_two (D.withOrbit J') hχ hθ
  have hΔ : simpleUnion D.χ = Set.range e6A5Root ∪ {hiE6} := by
    rw [hχ, simpleUnion_e6_two]
  have hmem : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, ∀ A : SL2 k,
      z * rootSL2 .E6 k β A = rootSL2 .E6 k β A * z := fun β hβ A =>
    commute_rootSL2_of_commute_orbitGroups (by decide) D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, IsRoot .E6 β := by
    rintro β (⟨i, rfl⟩ | hβ)
    · exact isRoot_single _ _
    · rw [Set.mem_singleton_iff] at hβ
      rw [hβ]
      exact isRoot_hiE6
  have hT := TwE7.mem_torusGroup_of_commute_rootTorus p (Or.inl rfl) hzG e6TwGamma2
    (fun y hy => hroot _ (e6TwGamma2_mem y hy))
    (fun y hy s => hmem y.1 (e6TwGamma2_mem y hy) (HSL s)) 23
    (fun α hα => e6TwGamma2_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, rootChar b β = 1 := fun β hβ =>
    TwE7.rootChar_eq_one_of_commute (hroot β hβ) (hmem β hβ (uSL 1))
  refine ⟨b, rfl, fun j hj => ?_⟩
  have hj' : ∃ i : Fin 5, e6A5Root i = Pi.single (CatLeafProof.e6Node j) 1 := by
    fin_cases j
    · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
    · exact absurd rfl hj
    · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨i, hi⟩ := hj'
  have h := hχb _ (Or.inl ⟨i, hi⟩)
  rwa [rootChar_piSingle_eq_coord] at h

theorem centModel_twE6_t2
    {f : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (K : Type) [Field K] [Finite K]
    [Algebra K k] [IsAlgClosure K k] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) (h w : ModGL TwistTag.E6.tag k)
    (hhT : h ∈ torusGroup TwistTag.E6.tag k)
    (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2) (hDe : D.e = f)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
    (hDF : ∀ y : adjointGroup TwistTag.E6.tag k, (D.F y : ModGL TwistTag.E6.tag k) =
      frobTwistGL TwistTag.E6.tag k p f (h * diagramMap TwistTag.E6 k) y)
    (hcent : (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) ⊓
          Subgroup.centralizer {baseChangeGL (algebraMap K k) (t : ModGL TwistTag.E6.tag K)}).map
          (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype) :
    CentModel (fixedSubgroup (MulAut.conj t)) := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hder, -⟩ := twE6_lift_facts (p := p) (k := k) hf hodd K hK σ hσ
  set F := frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set ι := algebraMap K k with hι
  set x := baseChangeGL ι (t : ModGL TwistTag.E6.tag K) with hx
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := fun γ =>
    (hDθ γ).trans (congrArg toReal (thetaMap_e6_nil_apply γ).symm)
  have hq5 : 5 ≤ D.q := by
    change 5 ≤ p ^ D.e
    rw [hDe]
    exact h5
  have hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) ⊓
        Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom := by
    intro J'
    have hle := twE6_orbitGroups_le D h w hhT hDe hDF hcent (Or.inr ⟨h5, hDχ, hDθ⟩) J'
    rwa [hder] at hle
  set H := fixedSubgroup (MulAut.conj t) with hHdef
  set ψ : H →* ModGL TwistTag.E6.tag k := (MulAut.conj w).toMonoidHom.comp
    (((baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype).comp
      H.subtype) with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj w).injective.comp
    ((baseChangeGL_injective ι).comp (Subtype.val_injective.comp Subtype.val_injective))
  have hψrange : ψ.range = ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL ι) ⊓ Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom := by
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (mem_lift_inf_centralizer_iff σ rfl t).2 ⟨y.1, y.2, rfl⟩, rfl⟩
    · rintro ⟨v', hv', rfl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_lift_inf_centralizer_iff σ rfl t).1 hv'
      exact ⟨⟨y, hy⟩, rfl⟩
  have hψX : ∀ y : H, ∃ y' : adjointGroup TwistTag.E6.tag k, y' ∈ D.totalFixedGroup ∧
      (y' : ModGL TwistTag.E6.tag k) = ψ y := by
    intro y
    have hmem : ψ y ∈ (R ⊓ Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom := by
      have hmem0 : ψ y ∈ ψ.range := ⟨y, rfl⟩
      rw [hψrange] at hmem0
      obtain ⟨v', hv', hv'e⟩ := hmem0
      rw [← hder] at hv'
      exact ⟨v', ⟨hRsub (Subgroup.mem_inf.1 hv').1, (Subgroup.mem_inf.1 hv').2⟩, hv'e⟩
    rw [hcent] at hmem
    obtain ⟨y', hy', hy'e⟩ := hmem
    exact ⟨y', hy', hy'e⟩
  have hCψ : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ ψ.range :=
    fun J' => hψrange ▸ hCY J'
  have hS : ∀ J : {J' : Set.range D.classOrbit // IsQuasisimple (D.withOrbit J').orbitGroup},
      IsComponent (((D.withOrbit J.1).orbitGroup).comap ψ) := by
    rintro ⟨J', hqJ⟩
    refine ⟨(isQuasisimple_congr ((((D.withOrbit J').orbitGroup.comap ψ).equivMapOfInjective ψ
      hψinj).trans (MulEquiv.subgroupCongr (map_comap_eq_self (hCψ J'))))).2 hqJ, ?_⟩
    refine Subgroup.Normal.isSubnormal ⟨fun q hq y => ?_⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    obtain ⟨y', hy', hy'e⟩ := hψX y
    rw [← hy'e]
    exact conj_mem_orbitGroup_withOrbit D hqJ hy' hq
  have hdiag : ∀ y : H, (∀ J : {J' : Set.range D.classOrbit //
        IsQuasisimple (D.withOrbit J').orbitGroup},
        ∀ s ∈ ((D.withOrbit J.1).orbitGroup).comap ψ, s * y = y * s) →
      ∃ b : Fin TwistTag.E6.tag.rank → kˣ, ψ y = rootDiagUnit TwistTag.E6.tag b ∧
        ∀ j, j ≠ CatLeafProof.e6Node 1 → b j = 1 := by
    intro y hy
    have hcomm : ∀ J' : Set.range D.classOrbit, ∀ c ∈ (D.withOrbit J').orbitGroup,
        ψ y * c = c * ψ y := by
      intro J' c hc
      rcases orbitGroup_two_cases D hq5 hDχ hθ J' with hbot | ⟨hqJ, -⟩
      · have hbot' : (D.withOrbit J').orbitGroup = ⊥ := hbot
        rw [hbot', Subgroup.mem_bot] at hc
        rw [hc, mul_one, one_mul]
      · obtain ⟨q, rfl⟩ := hCψ J' hc
        have h1 := hy ⟨J', hqJ⟩ q hc
        rw [← map_mul, ← map_mul, h1]
    have hψG : ψ y ∈ adjointGroup TwistTag.E6.tag k := by
      obtain ⟨y', -, hy'e⟩ := hψX y
      rw [← hy'e]
      exact y'.2
    obtain ⟨b, hb, hbj⟩ := eq_rootDiagUnit_of_commute_orbitGroups_two_e6 D
      (le_trans (by norm_num) hq5) hDχ hθ hψG hcomm
    refine ⟨b, hb, fun j hj => ?_⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin 6, CatLeafProof.e6Node j' = j := ⟨j, rfl⟩
    exact hbj j' fun h1 => hj (by rw [h1])
  refine ⟨{J' : Set.range D.classOrbit // IsQuasisimple (D.withOrbit J').orbitGroup},
    fun J => ((D.withOrbit J.1).orbitGroup).comap ψ, hS,
    fun J => Burgoyne.even_card_of_isQuasisimple (hS J).1, fun y y' hy hy' => ?_,
    fun y y' hy hy' hy2 hy2' hy1 hy1' => ?_⟩
  · obtain ⟨b, hb, -⟩ := hdiag y hy
    obtain ⟨b', hb', -⟩ := hdiag y' hy'
    refine hψinj ?_
    rw [map_mul, map_mul, hb, hb', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · obtain ⟨b, hb, hbj⟩ := hdiag y hy
    obtain ⟨b', hb', hbj'⟩ := hdiag y' hy'
    refine hψinj ?_
    rw [hb, hb']
    refine rootDiagUnit_eq_of_single hbj hbj' ?_ ?_ ?_ ?_
    · rw [← hb, ← map_mul, hy2, map_one]
    · rw [← hb', ← map_mul, hy2', map_one]
    · rw [← hb]
      exact fun h1 => hy1 (hψinj (h1.trans (map_one ψ).symm))
    · rw [← hb']
      exact fun h1 => hy1' (hψinj (h1.trans (map_one ψ).symm))

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
