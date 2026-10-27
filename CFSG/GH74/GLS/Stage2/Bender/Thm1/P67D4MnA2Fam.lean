module

public import CFSG.RankThree.PartOne.KGD.D4T36Family
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

@[expose] def d4LongA2 : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {![0, 0, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 1],
    ![0, 0, -1, 0], ![-1, -1, -1, -1], ![-1, -1, -2, -1]}

@[expose] def d4LongVec (a c : ℤ) : Fin TwistTag.D4.tag.rank → ℤ := ![a, a, c, a]

theorem d4LongVec_add (a c a' c' : ℤ) :
    d4LongVec a c + d4LongVec a' c' = d4LongVec (a + a') (c + c') := by
  funext i
  fin_cases i <;> rfl

theorem d4LongVec_neg (a c : ℤ) : -d4LongVec a c = d4LongVec (-a) (-c) := by
  funext i
  fin_cases i <;> rfl

theorem permLattice_d4LongVec (a c : ℤ) :
    permLattice TwistTag.D4.perm (d4LongVec a c) = d4LongVec a c := by
  funext i
  fin_cases i <;> rfl

theorem d4LongA2_eq : d4LongA2 = {d4LongVec 0 1, d4LongVec 1 1, d4LongVec 1 2,
    d4LongVec 0 (-1), d4LongVec (-1) (-1), d4LongVec (-1) (-2)} := rfl

theorem d4LongA2_wordValues :
    (([0, 2, 1, 3] : List (Fin TwistTag.D4.tag.rank)).foldr (reflect TwistTag.D4.tag)
      (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1) ∧
    (([0, 2, 1, 3] : List (Fin TwistTag.D4.tag.rank)).foldr (reflect TwistTag.D4.tag)
      (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 1 1) := by
  decide +kernel

theorem d4_long_values (v : WeylGroup TwistTag.D4.tag)
    (hv0 : v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1)
    (hv2 : v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 1 1) :
    v • d4Chain 0 1 = d4LongVec 0 1 ∧ v • d4Chain 1 2 = d4LongVec 1 1 ∧
      v • d4Chain 0 2 = d4LongVec 1 2 ∧ v • d4Chain 1 0 = d4LongVec 0 (-1) ∧
      v • d4Chain 2 1 = d4LongVec (-1) (-1) ∧ v • d4Chain 2 0 = d4LongVec (-1) (-2) := by
  obtain ⟨c01, c12, c10, c21⟩ := d4Chain_values
  have c02 : d4Chain 0 2 = Pi.single 0 1 + Pi.single 2 1 := by
    rw [← d4Chain_add 0 1 2, c01, c12]
  have c20 : d4Chain 2 0 = -(Pi.single 0 1 + Pi.single 2 1) := by
    rw [d4Chain_swap 0 2, c02]
  refine ⟨by rw [c01, hv0], by rw [c12, hv2], ?_, ?_, ?_, ?_⟩
  · rw [c02, smul_add, hv0, hv2, d4LongVec_add]
    rfl
  · rw [c10, smul_neg, hv0, d4LongVec_neg]
    rfl
  · rw [c21, smul_neg, hv2, d4LongVec_neg]
  · rw [c20, smul_neg, smul_add, hv0, hv2, d4LongVec_add, d4LongVec_neg]
    rfl

theorem exists_smul_d4LongA2 :
    ∃ v : WeylGroup TwistTag.D4.tag,
      v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1 ∧
      v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 1 1 := by
  refine ⟨(coxeterSystem TwistTag.D4.tag).wordProd [0, 2, 1, 3], ?_, ?_⟩
  · rw [wordProd_smul]
    exact d4LongA2_wordValues.1
  · rw [wordProd_smul]
    exact d4LongA2_wordValues.2

theorem d4Q_a2_family {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ] [IsAlgClosed L]
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hq2 : 2 < ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL TwistTag.D4.tag L) (hnm : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ • x = -x) :
    ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L d4LongA2 ∧
      P ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2,
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2,
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ u ∈ P, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) d4LongA2) ∧
      (∃ U : Subgroup (ModGL TwistTag.D4.tag L), U ≤ P ∧ IsPGroup ℓ U ∧
        Nat.card U = (ℓ ^ f) ^ 3) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨v, hv0, hv2⟩ := exists_smul_d4LongA2
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set ρ : SL(3, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
      (d4rhoStd L) with hρ
  set σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ := fun a b => v • d4Chain a b with hσ'
  have hframe : IsA2Frame ρ σ' := (d4Std_frame' L).transport v
  obtain ⟨s01, s12, s02, s10, s21, s20⟩ := d4_long_values v hv0 hv2
  have hperm : ∀ a b : Fin 3, a ≠ b → permLattice TwistTag.D4.perm (σ' a b) = σ' a b := by
    intro a b hab
    match a, b, hab with
    | 0, 0, h => exact absurd rfl h
    | 0, 1, _ => exact (congrArg _ s01).trans ((permLattice_d4LongVec _ _).trans s01.symm)
    | 0, 2, _ => exact (congrArg _ s02).trans ((permLattice_d4LongVec _ _).trans s02.symm)
    | 1, 0, _ => exact (congrArg _ s10).trans ((permLattice_d4LongVec _ _).trans s10.symm)
    | 1, 1, h => exact absurd rfl h
    | 1, 2, _ => exact (congrArg _ s12).trans ((permLattice_d4LongVec _ _).trans s12.symm)
    | 2, 0, _ => exact (congrArg _ s20).trans ((permLattice_d4LongVec _ _).trans s20.symm)
    | 2, 1, _ => exact (congrArg _ s21).trans ((permLattice_d4LongVec _ _).trans s21.symm)
    | 2, 2, h => exact absurd rfl h
  have hS3eq : {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ' a b} = d4LongA2 := by
    ext r
    rw [d4LongA2_eq]
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      match a, b, hab with
      | 0, 0, h => exact absurd rfl h
      | 0, 1, _ => exact Or.inl s01
      | 0, 2, _ => exact Or.inr (Or.inr (Or.inl s02))
      | 1, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inl s10)))
      | 1, 1, h => exact absurd rfl h
      | 1, 2, _ => exact Or.inr (Or.inl s12)
      | 2, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr s20))))
      | 2, 1, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl s21))))
      | 2, 2, h => exact absurd rfl h
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, 1, by decide, s01.symm⟩
      · exact ⟨1, 2, by decide, s12.symm⟩
      · exact ⟨0, 2, by decide, s02.symm⟩
      · exact ⟨1, 0, by decide, s10.symm⟩
      · exact ⟨2, 1, by decide, s21.symm⟩
      · exact ⟨2, 0, by decide, s20.symm⟩
  have hS3 : ∀ r ∈ d4LongA2, IsRoot TwistTag.D4.tag r := by
    intro r hr
    rw [← hS3eq] at hr
    obtain ⟨a, b, hab, rfl⟩ := hr
    exact hframe.isRoot a b hab
  choose! ε₀ hε₀ using fun (a b : Fin 3) (hab : a ≠ b) => hframe.transv a b hab
  have htor : ∀ b : Fin TwistTag.D4.tag.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit TwistTag.D4.tag b * ρ A * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
        ρ (conjDiagn d A) := fun b =>
    ⟨fun a => rootChar b (σ' a 0), fun A => hframe.torus b A⟩
  have hrange : ρ.range = rootSpan TwistTag.D4.tag L d4LongA2 := by
    rw [hframe.range, hS3eq]
  set Q : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L with hQ
  have hconj_gen : ∀ (tg : Fin 3 → Fin 3 → Fin 3 × Fin 3),
      (∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) = σ' (tg a b).1 (tg a b).2) →
      ∀ a b : Fin 3, a ≠ b → ∃ β : Lˣ, ∀ c : L,
        (n * Q) * pinnedX TwistTag.D4.tag L (σ' a b) c * (n * Q)⁻¹ =
          pinnedX TwistTag.D4.tag L (σ' (tg a b).1 (tg a b).2) ((β : L) * c) := by
    intro tg htg a b hab
    have hα : IsRoot TwistTag.D4.tag (σ' a b) := hframe.isRoot a b hab
    obtain ⟨e, hee, he⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.D4 hα
    have hρα : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (σ' a b)) :=
      hα.permLattice TwistTag.D4.cartan_perm
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm hρα
    refine ⟨μ * ⟨e, e, hee, hee⟩, fun c => ?_⟩
    have e1 : (n * Q) * pinnedX TwistTag.D4.tag L (σ' a b) c * (n * Q)⁻¹ =
        n * (Q * pinnedX TwistTag.D4.tag L (σ' a b) c * Q⁻¹) * n⁻¹ := by group
    rw [e1, he c, hμ (e * c), htg a b hab]
    congr 1
    simp only [Units.val_mul]
    ring
  have hW : ∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
      permLattice TwistTag.D4.perm (σ' a b) =
        σ' ((fun a b => (b, a)) a b).1 ((fun a b => (b, a)) a b).2 := by
    intro a b hab
    rw [hnW, hperm a b hab]
    exact (hframe.neg a b).symm
  obtain ⟨Φ', hΦ', β, hshape⟩ := exists_aut_of_rootData_n (τ := TwistTag.D4.tag) (ν := 3) ρ
    hframe.injective σ' ε₀ hε₀ Fr hFrbij (n * Q) (fun a b => (b, a))
    (fun a b hab => hab.symm) (fun a b hab => ⟨b, a, hab.symm, rfl⟩) (hconj_gen _ hW)
  have hshape' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single b a ((β a b : L) * t ^ ℓ ^ f) :=
    fun a b hab t => by rw [hshape a b hab t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inr hq2) (by norm_num) hS3 ρ
    hframe.injective hrange htor hframe.diag Fr (n * Q) Φ' hΦ' (Equiv.refl (Fin 3)) β hshape'
  obtain ⟨U, hUle, hUp, hUcard⟩ :=
    sl3_unitary_fixed_card_dvd hℓ hf hk hq2 (Equiv.refl (Fin 3)) Φ' β hshape'
  obtain ⟨hfin, hq, hQ', hR, hadj, hnorm, hcent⟩ := hP
  refine ⟨P (), hfin (), hq (), hQ' (), ?_, hadj (), ?_, ?_, ?_⟩
  · rw [twistedFixedPoints_twist_D4]
    exact hR ()
  · intro y hy hyR u hu
    rw [twistedFixedPoints_twist_D4] at hyR
    exact hnorm () y hy hyR u hu
  · intro y hy hyR hcomm
    rw [twistedFixedPoints_twist_D4] at hyR
    rw [subtorusSigma_twist_D4]
    exact hcent y hy hyR (fun _ => hcomm)
  · refine ⟨U.map ρ, ?_, hUp.map ρ, ?_⟩
    · rw [hP2]
      exact Subgroup.map_mono hUle
    · rw [Subgroup.card_map_of_injective hframe.injective, hUcard]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
