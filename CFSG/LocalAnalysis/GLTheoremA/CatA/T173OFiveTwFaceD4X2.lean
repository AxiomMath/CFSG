module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4X

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.E6SignedGraph

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


private theorem d4Witness_rootChar_eq_one_of_mem_pair {F : Type} [Field F] {ω : Fˣ}
    {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : v ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) :
    rootChar (d4TorusParam ω) v = 1 := by
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]; exact rootChar_d4TorusParam_eq_one_of_coord_eq ω (by decide)
  · rw [Finset.mem_singleton.1 h]
    exact rootChar_d4TorusParam_eq_one_of_coord_eq ω (by decide)

private theorem d4Witness_rootChar_neg_eq_one_of_mem_pair {F : Type} [Field F] {ω : Fˣ}
    {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : v ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) :
    rootChar (d4TorusParam ω) (-v) = 1 :=
  rootChar_d4TorusParam_eq_one_of_coord_eq ω (by
    rcases Finset.mem_insert.1 hv with h | h
    · rw [h]; decide
    · rw [Finset.mem_singleton.1 h]; decide)

private theorem d4_two_eq_zero_and_four_le_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) :
    (2 : F) = 0 ∧ 4 ≤ Nat.card F := by
  haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hn hF
  refine ⟨CharP.cast_eq_zero F 2, ?_⟩
  rw [hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left
        (by simpa using Nat.pow_le_pow_right (by norm_num) hn) 2

private theorem d4_orbitField_top_and_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {a : Fin TwistTag.E6.foldedTag.rank} (hcard : (TwistTag.E6.orbit a).card = 2) :
    orbitField TwistTag.E6 F σ.toRingHom a = ⊤ ∧
      Nat.card (orbitField TwistTag.E6 F σ.toRingHom a) = Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  have hσ2 : ∀ c : F, σ (σ c) = c := by
    intro c
    rw [hσ, hσ, ← pow_mul]
    have : (2 : ℕ) ^ n * 2 ^ n = Nat.card F := by rw [hF]; ring
    rw [this, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have htop : orbitField TwistTag.E6 F σ.toRingHom a = ⊤ := by
    ext c
    simp only [Subfield.mem_top, iff_true]
    exact mem_orbitField.2 (by rw [hcard]; simpa [pow_two] using hσ2 c)
  exact ⟨htop, by rw [htop]; exact Nat.card_congr (Subfield.topEquiv (K := F)).toEquiv⟩

private theorem exists_d4Beta_diagramOrbit_data :
    ∃ (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank),
      w ∈ relWeylTwist TwistTag.E6 ∧
        (TwistTag.E6.orbit a).card = 2 ∧
          TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a ∧
            (∀ k ∈ TwistTag.E6.orbit a,
              w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈
                ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) := by
  obtain ⟨w, hw, a, hO⟩ := TwistTag.exists_diagramOrbit_eq (t := TwistTag.E6) isRoot_d4Beta
  have hinj : Function.Injective (fun k : Fin TwistTag.E6.tag.rank =>
      w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) :=
    TwistTag.injective_smul_single TwistTag.E6 w
  have hcard2 : (TwistTag.E6.orbit a).card = 2 := by
    have hc := congrArg Finset.card hO
    rw [diagramOrbit_d4Beta, Finset.card_image_of_injective _ hinj,
      Finset.card_pair d4Beta_ne_d4BetaRho] at hc
    omega
  have hpair := (orbit_pair_or_single a).resolve_right (by
    rintro ⟨-, hsingle, -⟩
    rw [hsingle] at hcard2
    simp at hcard2)
  obtain ⟨hji, -, -⟩ := hpair
  refine ⟨w, a, hw, hcard2, hji, ?_⟩
  intro k hk
  have hk' : w • (Pi.single k 1) ∈ TwistTag.E6.diagramOrbit d4Beta := by
    rw [hO]
    exact Finset.mem_image_of_mem _ hk
  rwa [diagramOrbit_d4Beta] at hk'

private noncomputable def d4ConjOrbitHom {F : Type} [Field F] (σ : F ≃+* F)
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    SL2 (orbitField TwistTag.E6 F σ.toRingHom a) →* Γ₂ F :=
  (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)).toMonoidHom.comp
    (orbitRankOneHom TwistTag.E6 F σ.toRingHom a)

private noncomputable def d4ConjOrbitGroup {F : Type} [Field F] (σ : F ≃+* F)
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) : Subgroup (Γ₂ F) :=
  (d4ConjOrbitHom σ w a).range

private theorem d4Witness_conj_orbitX_uSL {F : Type} [Field F] {σ : F →+* F} {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (hcard : (TwistTag.E6.orbit a).card = 2)
    (hχi : rootChar (d4TorusParam ω) (w • Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ)) = 1)
    (hχj : rootChar (d4TorusParam ω)
      (w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ)) = 1)
    (c : orbitField TwistTag.E6 F σ a) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (orbitX TwistTag.E6 F σ a c : Γ₂ F) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (orbitX TwistTag.E6 F σ a c : Γ₂ F) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
  rw [coe_orbitX_of_card_two hcard c]
  have h1 := d4Witness_commute_conj_xUnit hχi (c : F)
  have h2 := d4Witness_commute_conj_xUnit hχj (σ (c : F))
  calc d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      d4Witness ω * ((canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹)) := by
        congr 1; group
    _ = ((canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹)) * d4Witness ω :=
        Commute.mul_right h1 h2
    _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
        congr 1; group

private theorem d4Witness_conj_orbitY_uSL {F : Type} [Field F] {σ : F →+* F} {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (hcard : (TwistTag.E6.orbit a).card = 2)
    (hχi : rootChar (d4TorusParam ω) (w • -(Pi.single (TwistTag.E6.orbitMin a) 1)) = 1)
    (hχj : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)) = 1)
    (c : orbitField TwistTag.E6 F σ a) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (orbitY TwistTag.E6 F σ a c : Γ₂ F) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (orbitY TwistTag.E6 F σ a c : Γ₂ F) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
  rw [coe_orbitY_of_card_two hcard c]
  have h1 := d4Witness_commute_conj_yUnit hχi (c : F)
  have h2 := d4Witness_commute_conj_yUnit hχj (σ (c : F))
  calc d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (yUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          yUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      d4Witness ω * ((canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          yUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          yUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹)) := by
        congr 1; group
    _ = ((canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          yUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
          yUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹)) * d4Witness ω :=
        Commute.mul_right h1 h2
    _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        (yUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
          yUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
            (σ (c : F))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
        congr 1; group

private theorem d4Witness_conj_range {F : Type} [Field F] (σ : F ≃+* F) {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (hcard : (TwistTag.E6.orbit a).card = 2)
    (hχi : rootChar (d4TorusParam ω) (w • Pi.single (TwistTag.E6.orbitMin a) 1) = 1)
    (hχj : rootChar (d4TorusParam ω)
      (w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) = 1)
    (hχineg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.orbitMin a) 1)) = 1)
    (hχjneg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)) = 1)
    (M : SL2 (orbitField TwistTag.E6 F σ.toRingHom a)) :
    d4Witness ω * d4ConjOrbitHom σ w a M =
      d4ConjOrbitHom σ w a M * d4Witness ω := by
  have hgen : Subgroup.closure
      (Set.range (sl2Upper (orbitField TwistTag.E6 F σ.toRingHom a)) ∪
        Set.range (sl2Lower (orbitField TwistTag.E6 F σ.toRingHom a))) = ⊤ :=
    sl2_closure_upper_lower
  have hM : M ∈ Subgroup.closure
      (Set.range (sl2Upper (orbitField TwistTag.E6 F σ.toRingHom a)) ∪
        Set.range (sl2Lower (orbitField TwistTag.E6 F σ.toRingHom a))) := by
    rw [hgen]; trivial
  induction hM using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · have hx' : (sl2Upper (orbitField TwistTag.E6 F σ.toRingHom a) c :
            SL2 (orbitField TwistTag.E6 F σ.toRingHom a)) = uSL c := rfl
        rw [hx']
        show d4Witness ω * (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w))
            (orbitRankOneHom TwistTag.E6 F σ.toRingHom a (uSL c)) =
          (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w))
            (orbitRankOneHom TwistTag.E6 F σ.toRingHom a (uSL c)) * d4Witness ω
        rw [orbitRankOneHom_uSL, MulAut.conj_apply,
          d4Witness_conj_orbitX_uSL hcard hχi hχj c]
      · have hx' : (sl2Lower (orbitField TwistTag.E6 F σ.toRingHom a) c :
            SL2 (orbitField TwistTag.E6 F σ.toRingHom a)) = vSL c := rfl
        rw [hx']
        show d4Witness ω * (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w))
            (orbitRankOneHom TwistTag.E6 F σ.toRingHom a (vSL c)) =
          (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w))
            (orbitRankOneHom TwistTag.E6 F σ.toRingHom a (vSL c)) * d4Witness ω
        rw [orbitRankOneHom_vSL, MulAut.conj_apply,
          d4Witness_conj_orbitY_uSL hcard hχineg hχjneg c]
  | one => rw [map_one]; exact Commute.one_right _
  | mul x y hx hy ihx ihy => rw [map_mul]; exact Commute.mul_right ihx ihy
  | inv x hx ih => rw [map_inv]; exact Commute.inv_right ih

private theorem d4ConjOrbitGroup_le_centralizer {F : Type} [Field F]
    (σ : F ≃+* F) {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (hcard : (TwistTag.E6.orbit a).card = 2)
    (hχi : rootChar (d4TorusParam ω) (w • Pi.single (TwistTag.E6.orbitMin a) 1) = 1)
    (hχj : rootChar (d4TorusParam ω)
      (w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) = 1)
    (hχineg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.orbitMin a) 1)) = 1)
    (hχjneg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)) = 1) :
    d4ConjOrbitGroup σ w a ≤
      Subgroup.centralizer ({d4Witness ω} : Set (Γ₂ F)) := by
  rintro x ⟨M, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (d4Witness_conj_range σ hcard hχi hχj hχineg hχjneg M).symm

private theorem d4ConjOrbitGroup_le_graphFixedRootGroup {F : Type} [Field F]
    (σ : F ≃+* F) (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (hw : w ∈ relWeylTwist TwistTag.E6) :
    d4ConjOrbitGroup σ w a ≤ graphFixedRootGroup TwistTag.E6 F σ.toRingHom := by
  rintro x ⟨M, rfl⟩
  change canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
      (orbitRankOneHom TwistTag.E6 F σ.toRingHom a M : Γ₂ F) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹ ∈
    graphFixedRootGroup TwistTag.E6 F σ.toRingHom
  have hMmem : (orbitRankOneHom TwistTag.E6 F σ.toRingHom a M : Γ₂ F) ∈
      orbitRankOneGroup TwistTag.E6 F σ.toRingHom a := by
    rw [orbitRankOneGroup, ← orbitRankOneHom_range]
    exact ⟨M, rfl⟩
  have hM := CFSG.LieType.SeitzGeneration.ExcHigh.orbitRankOneGroup_le_graphFixedRootGroup'
    σ.toRingHom a hMmem
  have hnC : canonicalRep (coxeterSystem TwistTag.E6.tag) F w ∈
      graphFixedRootGroup TwistTag.E6 F σ.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup hw
  exact mul_mem (mul_mem hnC hM) (inv_mem hnC)

private theorem d4ConjOrbitGroup_perfect {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (hcardL : Nat.card (orbitField TwistTag.E6 F σ.toRingHom a) = Nat.card F)
    (h4F : 4 ≤ Nat.card F) :
    ⁅d4ConjOrbitGroup σ w a, d4ConjOrbitGroup σ w a⁆ = d4ConjOrbitGroup σ w a := by
  haveI : Finite (orbitField TwistTag.E6 F σ.toRingHom a) := Subtype.finite
  have hperfSL : Group.IsPerfect (SL2 (orbitField TwistTag.E6 F σ.toRingHom a)) := by
    apply CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
    rw [hcardL]
    exact h4F
  haveI : Group.IsPerfect (SL2 (orbitField TwistTag.E6 F σ.toRingHom a)) := hperfSL
  have hperfX : Group.IsPerfect (d4ConjOrbitGroup σ w a) :=
    Group.IsPerfect.ofSurjective (f := (d4ConjOrbitHom σ w a).rangeRestrict)
      (d4ConjOrbitHom σ w a).rangeRestrict_surjective
  haveI : Group.IsPerfect (d4ConjOrbitGroup σ w a) := hperfX
  exact Subgroup.commutator_eq_self

private theorem d4ConjOrbitHom_uSL_one_eq {F : Type} [Field F] (σ : F ≃+* F)
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (h2 : (2 : F) = 0) (hcard : (TwistTag.E6.orbit a).card = 2) :
    d4ConjOrbitHom σ w a (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) =
      pinnedX TwistTag.E6.tag F (w • Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ)) 1 *
        pinnedX TwistTag.E6.tag F
          (w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ)) 1 := by
  dsimp [d4ConjOrbitHom]
  change (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) F w))
    (orbitRankOneHom TwistTag.E6 F σ.toRingHom a
      (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a))) = _
  rw [orbitRankOneHom_uSL, MulAut.conj_apply,
    coe_orbitX_of_card_two hcard (1 : orbitField TwistTag.E6 F σ.toRingHom a)]
  have e : canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
      (xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a)
          ((1 : orbitField TwistTag.E6 F σ.toRingHom a) : F) *
        xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          (σ.toRingHom ((1 : orbitField TwistTag.E6 F σ.toRingHom a) : F))) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹ =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a)
          ((1 : orbitField TwistTag.E6 F σ.toRingHom a) : F) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          (σ.toRingHom ((1 : orbitField TwistTag.E6 F σ.toRingHom a) : F)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) := by group
  rw [e, conj_canonicalRep_xUnit_eq_of_two_eq_zero h2,
    conj_canonicalRep_xUnit_eq_of_two_eq_zero h2]
  simp

private theorem d4ConjOrbitHom_uSL_one_mem_parabolicRadical {F : Type} [Field F]
    (σ : F ≃+* F) {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (h2 : (2 : F) = 0) (hcard : (TwistTag.E6.orbit a).card = 2)
    (hwi : w • Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)))
    (hwj : w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) :
    d4ConjOrbitHom σ w a (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ∈
      parabolicRadical TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4) := by
  rw [d4ConjOrbitHom_uSL_one_eq σ h2 hcard]
  rcases Finset.mem_insert.1 hwi with hwiβ | hwiρ
  · rcases Finset.mem_insert.1 hwj with hwjβ | hwjρ
    · rw [hwiβ, hwjβ]
      exact mul_mem (pinnedX_d4Beta_mem_parabolicRadical 1)
        (pinnedX_d4Beta_mem_parabolicRadical 1)
    · rw [hwiβ, Finset.mem_singleton.1 hwjρ]
      exact mul_mem (pinnedX_d4Beta_mem_parabolicRadical 1)
        (pinnedX_d4BetaRho_mem_parabolicRadical 1)
  · rcases Finset.mem_insert.1 hwj with hwjβ | hwjρ
    · rw [Finset.mem_singleton.1 hwiρ, hwjβ]
      exact mul_mem (pinnedX_d4BetaRho_mem_parabolicRadical 1)
        (pinnedX_d4Beta_mem_parabolicRadical 1)
    · rw [Finset.mem_singleton.1 hwiρ, Finset.mem_singleton.1 hwjρ]
      exact mul_mem (pinnedX_d4BetaRho_mem_parabolicRadical 1)
        (pinnedX_d4BetaRho_mem_parabolicRadical 1)

private theorem isRoot_and_height_of_mem_d4Beta_pair
    {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : v ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) :
    IsRoot TwistTag.E6.tag v ∧ 0 < height v := by
  refine ⟨?_, by rw [height_of_mem_d4Beta_pair hv]; norm_num⟩
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]; exact isRoot_d4Beta
  · rw [Finset.mem_singleton.1 h]; exact isRoot_d4BetaRho

private theorem d4ConjOrbitHom_uSL_one_ne_one {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (h2 : (2 : F) = 0) (hcard : (TwistTag.E6.orbit a).card = 2)
    (hwi : w • Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)))
    (hwj : w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)))
    (hinj : Function.Injective (fun k : Fin TwistTag.E6.tag.rank =>
      w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)))
    (hji : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) :
    d4ConjOrbitHom σ w a (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ≠ 1 := by
  intro hone
  set γ : Fin TwistTag.E6.tag.rank → ℤ :=
    w • (Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ) :
      Fin TwistTag.E6.tag.rank → ℤ) with hγdef
  set δ : Fin TwistTag.E6.tag.rank → ℤ :=
    w • (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ) :
      Fin TwistTag.E6.tag.rank → ℤ) with hδdef
  have hγmem : γ ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)) := by
    simpa only [hγdef] using hwi
  have hδmem : δ ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)) := by
    simpa only [hδdef] using hwj
  have hφ := d4ConjOrbitHom_uSL_one_eq (w := w) (a := a) σ h2 hcard
  rw [← hγdef, ← hδdef] at hφ
  have hprod : pinnedX TwistTag.E6.tag F γ 1 * pinnedX TwistTag.E6.tag F δ 1 = 1 := by
    rw [← hφ]
    exact hone
  have hγ := isRoot_and_height_of_mem_d4Beta_pair hγmem
  have hδ := isRoot_and_height_of_mem_d4Beta_pair hδmem
  have hheight : height δ = height γ := by
    rw [height_of_mem_d4Beta_pair hδmem, height_of_mem_d4Beta_pair hγmem]
  have hne : δ ≠ γ := by
    intro h
    exact hji (hinj (by simpa only [hγdef, hδdef] using h))
  have hcoord : rootCoord hγ (pinnedX TwistTag.E6.tag F γ 1 *
      pinnedX TwistTag.E6.tag F δ 1) = 1 := by
    rw [rootCoord_mul hγ (pinnedX_mem_heightSeries_height hγ 1)
      (by rw [← hheight]; exact pinnedX_mem_heightSeries_height hδ 1),
      rootCoord_self hγ,
      rootCoord_pinnedX_of_ne hγ hδ (le_of_eq hheight.symm) hne, add_zero]
  rw [hprod, rootCoord_one hγ] at hcoord
  norm_num at hcoord

private theorem d4ConjOrbitGroup_not_le_levi {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (h2 : (2 : F) = 0) (hcard : (TwistTag.E6.orbit a).card = 2)
    (hwi : w • Pi.single (TwistTag.E6.orbitMin a) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)))
    (hwj : w • Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (1 : ℤ) ∈
      ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ)))
    (hinj : Function.Injective (fun k : Fin TwistTag.E6.tag.rank =>
      w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)))
    (hji : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) :
    ¬ d4ConjOrbitGroup σ w a ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 := by
  intro hXL
  have hmem : d4ConjOrbitHom σ w a (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ∈
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 :=
    hXL ⟨uSL 1, rfl⟩
  have hrad : d4ConjOrbitHom σ w a
      (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ∈
      parabolicRadical TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4) :=
    d4ConjOrbitHom_uSL_one_mem_parabolicRadical σ h2 hcard hwi hwj
  have hlevi : d4ConjOrbitHom σ w a
      (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ∈
      parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4) :=
    (inf_le_left : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 ≤
      parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4)) hmem
  have hbot : d4ConjOrbitHom σ w a
      (uSL (1 : orbitField TwistTag.E6 F σ.toRingHom a)) ∈ (⊥ : Subgroup (Γ₂ F)) := by
    rw [← parabolicRadical_inf_parabolicLevi (J := TwistTag.E6.orbitUnion twE6MaxD4)]
    exact ⟨hrad, hlevi⟩
  exact d4ConjOrbitHom_uSL_one_ne_one σ h2 hcard hwi hwj hinj hji
    (Subgroup.mem_bot.1 hbot)

theorem exists_perfect_le_centralizer_d4Witness {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {ω : Fˣ} :
    ∃ X : Subgroup (Γ₂ F), X ≤ twistedE6RootGroup F σ ∧
      X ≤ Subgroup.centralizer ({d4Witness ω} : Set (Γ₂ F)) ∧ ⁅X, X⁆ = X ∧
      ¬ X ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have h1 : Nat.card F = 1 := by simpa using hF
      exact absurd h1 (Finite.one_lt_card (α := F)).ne'
    · exact h0
  obtain ⟨h2, h4F⟩ := d4_two_eq_zero_and_four_le_card hF hn
  obtain ⟨w, a, hw, hcard2, hji, hmem⟩ := exists_d4Beta_diagramOrbit_data
  have hwi := hmem (TwistTag.E6.orbitMin a) (TwistTag.E6.orbitMin_mem a)
  have hwj := hmem (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
    (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a))
  have hinj : Function.Injective (fun k : Fin TwistTag.E6.tag.rank =>
      w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) :=
    TwistTag.injective_smul_single TwistTag.E6 w
  have hχi := d4Witness_rootChar_eq_one_of_mem_pair (ω := ω) hwi
  have hχj := d4Witness_rootChar_eq_one_of_mem_pair (ω := ω) hwj
  have hχineg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.orbitMin a) 1)) = 1 := by
    rw [smul_neg]; exact d4Witness_rootChar_neg_eq_one_of_mem_pair (ω := ω) hwi
  have hχjneg : rootChar (d4TorusParam ω)
      (w • -(Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)) = 1 := by
    rw [smul_neg]; exact d4Witness_rootChar_neg_eq_one_of_mem_pair (ω := ω) hwj
  obtain ⟨hLtop, hcardL⟩ := d4_orbitField_top_and_card hF σ hσ hcard2
  refine ⟨d4ConjOrbitGroup σ w a, ?_, ?_, ?_, ?_⟩
  · exact d4ConjOrbitGroup_le_graphFixedRootGroup σ w a hw
  · exact d4ConjOrbitGroup_le_centralizer σ hcard2 hχi hχj hχineg hχjneg
  · exact d4ConjOrbitGroup_perfect σ w a hcardL h4F
  · exact d4ConjOrbitGroup_not_le_levi σ h2 hcard2 hwi hwj hinj hji

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
