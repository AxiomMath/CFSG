module

public import CFSG.RankThree.PartOne.D4RC.RxOrder
public import CFSG.RankThree.PartOne.KGD.D4T36Family

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ}

theorem d4phi_family_iso [Fact ℓ.Prime] (hf : 1 ≤ f) {L : Type} [Field L]
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : ε = 1 ∨ 2 < ℓ ^ f)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL TwistTag.D4.tag L)
    (hnm : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    (i : Fin 4) (v : WeylGroup TwistTag.D4.tag)
    (hv0 : v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4U i)
    (hv2 : v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4T36A *ᵥ d4U i)
    (hvS : (fun x => v • x) '' d4StdA2 = d4Sigma i) :
    ∃ (ρ : SL(3, L) →* ModGL TwistTag.D4.tag L)
      (σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ)
      (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L)),
      IsA2Frame ρ σ' ∧ {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ' a b} = d4Sigma i ∧
      (∀ X, n * twistHom TwistTag.D4 L Fr (ρ X) * n⁻¹ = ρ (Φ' X)) ∧
      IsSigmaFamily (n * diagramMap TwistTag.D4 L) Fr (d4Sigma i)
        (fun _ : Unit => (fixSubgroup Φ').map ρ) ∧
      (ε = 1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔
        ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∧
      (ε = -1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (ε = -1 → ∃ (π : Equiv.Perm (Fin 3)) (β : Fin 3 → Fin 3 → Lˣ),
        ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single (π b) (π a) ((β a b : L) * t ^ ℓ ^ f)) ∧
      (ε = -1 → Nat.card (fixSubgroup Φ') = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1)) ∧
      ρ = (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
        (d4rhoStd L) ∧ ∀ a b, σ' a b = v • d4Chain a b := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set ρ : SL(3, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
      (d4rhoStd L) with hρ
  set σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ := fun a b => v • d4Chain a b with hσ'
  have hframe : IsA2Frame ρ σ' := (d4Std_frame' L).transport v
  have hS3eq : {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ' a b} = d4Sigma i := by
    rw [← hvS]
    ext r
    obtain ⟨c01, c12, c10, c21⟩ := d4Chain_values
    have c02 : d4Chain 0 2 = Pi.single 0 1 + Pi.single 2 1 := by
      rw [← d4Chain_add 0 1 2, c01, c12]
    have c20 : d4Chain 2 0 = -(Pi.single 0 1 + Pi.single 2 1) := by
      rw [d4Chain_swap 0 2, c02]
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      refine ⟨d4Chain a b, ?_, rfl⟩
      rcases d4Chain_cases a b hab with h | h | h | h | h | h <;> rw [h] <;>
        simp [d4StdA2]
    · rintro ⟨x, hx, rfl⟩
      simp only [d4StdA2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, 1, by decide, by simp only [hσ', c01]⟩
      · exact ⟨1, 2, by decide, by simp only [hσ', c12]⟩
      · exact ⟨0, 2, by decide, by simp only [hσ', c02]⟩
      · exact ⟨1, 0, by decide, by simp only [hσ', c10]⟩
      · exact ⟨2, 1, by decide, by simp only [hσ', c21]⟩
      · exact ⟨2, 0, by decide, by simp only [hσ', c20]⟩
  have hS3 : ∀ r ∈ d4Sigma i, IsRoot TwistTag.D4.tag r := fun r hr => isRoot_of_mem_d4Sigma hr
  choose! ε₀ hε₀ using fun (a b : Fin 3) (hab : a ≠ b) => hframe.transv a b hab
  have htor : ∀ b : Fin TwistTag.D4.tag.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit TwistTag.D4.tag b * ρ A * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
        ρ (conjDiagn d A) := fun b =>
    ⟨fun a => rootChar b (σ' a 0), fun A => hframe.torus b A⟩
  have hrange : ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
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

  have main : ∃ (P : Unit → Subgroup (ModGL TwistTag.D4.tag L)) (Φ' : SL(3, L) ≃* SL(3, L))
      (H : SL(3, L)), IsSigmaFamily (n * Q) Fr (d4Sigma i) P ∧
      P () = (fixSubgroup Φ').map ρ ∧
      (∀ X, (n * Q) * Units.map (entrywiseHom Fr) (ρ X) * (n * Q)⁻¹ = ρ (Φ' X)) ∧
      (ε = 1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔
        ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∧
      (ε = -1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (ε = -1 → ∃ (π : Equiv.Perm (Fin 3)) (β : Fin 3 → Fin 3 → Lˣ),
        ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single (π b) (π a) ((β a b : L) * t ^ ℓ ^ f)) := by
    rcases hε with rfl | rfl
    · obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), ∀ a b : Fin 3, a ≠ b →
          d4T36M 1 *ᵥ σ' a b = σ' (π a) (π b) := by
        refine ⟨finRotate 3, fun a b hab => ?_⟩
        rw [d4T36M, one_smul]
        exact d4T36_perm i v hv0 hv2 a b hab
      have hW : ∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) =
            σ' ((fun a b => (π a, π b)) a b).1 ((fun a b => (π a, π b)) a b).2 := by
        intro a b hab
        rw [hnW, CFSG.RankThree.PartOne.KGD.permLattice_symm_permLattice, hπ a b hab]
      obtain ⟨Φ', hΦ', β, hshape⟩ := exists_aut_of_rootData_n (τ := TwistTag.D4.tag) (ν := 3) ρ
        hframe.injective σ' ε₀ hε₀ Fr hFrbij (n * Q) (fun a b => (π a, π b))
        (fun a b hab => π.injective.ne hab)
        (fun a b hab => ⟨π.symm a, π.symm b, π.symm.injective.ne hab, by simp⟩)
        (hconj_gen _ hW)
      have hshape' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + single (π a) (π b) ((β a b : L) * t ^ ℓ ^ f) :=
        fun a b hab t => by rw [hshape a b hab t, hFr]
      obtain ⟨P, hP, hP1, hP2⟩ := an_family_split hℓ hf hk (by norm_num) hS3 ρ hframe.injective
        hrange htor hframe.diag Fr (n * Q) Φ' hΦ' π β hshape'
      obtain ⟨-, ⟨H, hH⟩, -⟩ := CFSG.RankThree.Classical2.sln_root_permuting_frobenius_fixed_split
        hℓ hf hk (by norm_num) π Φ' β hshape'
      exact ⟨P, Φ', H, hP, hP2, hΦ', fun _ => hH, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num)⟩
    · have hq3 : 2 < ℓ ^ f := hq2.resolve_left (by norm_num)
      obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), ∀ a b : Fin 3, a ≠ b →
          d4T36M (-1) *ᵥ σ' a b = σ' (π b) (π a) := by
        refine ⟨finRotate 3, fun a b hab => ?_⟩
        have h1 := d4T36_perm i v hv0 hv2 a b hab
        rw [d4T36M, neg_smul, one_smul, Matrix.neg_mulVec, hσ']
        simp only [] at h1 ⊢
        rw [h1, d4Chain_swap (finRotate 3 b) (finRotate 3 a), smul_neg, neg_neg]
      have hW : ∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) =
            σ' ((fun a b => (π b, π a)) a b).1 ((fun a b => (π b, π a)) a b).2 := by
        intro a b hab
        rw [hnW, CFSG.RankThree.PartOne.KGD.permLattice_symm_permLattice, hπ a b hab]
      obtain ⟨Φ', hΦ', β, hshape⟩ := exists_aut_of_rootData_n (τ := TwistTag.D4.tag) (ν := 3) ρ
        hframe.injective σ' ε₀ hε₀ Fr hFrbij (n * Q) (fun a b => (π b, π a))
        (fun a b hab => (π.injective.ne hab).symm)
        (fun a b hab => ⟨π.symm b, π.symm a, (π.symm.injective.ne hab).symm, by simp⟩)
        (hconj_gen _ hW)
      have hshape' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + single (π b) (π a) ((β a b : L) * t ^ ℓ ^ f) :=
        fun a b hab t => by rw [hshape a b hab t, hFr]
      obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inr hq3) (by norm_num) hS3 ρ
        hframe.injective hrange htor hframe.diag Fr (n * Q) Φ' hΦ' π β hshape'
      obtain ⟨-, ⟨H, hH⟩, -⟩ :=
        CFSG.RankThree.Classical2.sln_root_permuting_frobenius_fixed_unitary hℓ hf hk
          (by norm_num) π Φ' β hshape'
      exact ⟨P, Φ', H, hP, hP2, hΦ', fun h => absurd h (by norm_num), fun _ => hH,
        fun _ => ⟨π, β, hshape'⟩⟩
  obtain ⟨P, Φ', H, hP, hP2, hΦ', hsplit, hunit, hshape⟩ := main
  have hΦ'' : ∀ X, n * twistHom TwistTag.D4 L Fr (ρ X) * n⁻¹ = ρ (Φ' X) := by
    intro X
    rw [← hΦ' X, twistHom_apply, ← hQ]
    group
  have hPfam : IsSigmaFamily (n * Q) Fr (d4Sigma i)
      (fun _ : Unit => (fixSubgroup Φ').map ρ) := by
    have h : P = fun _ => (fixSubgroup Φ').map ρ := funext fun u => hP2
    rwa [h] at hP

  refine ⟨ρ, σ', Φ', H, hframe, hS3eq, hΦ'', hPfam, hsplit, hunit, hshape, fun h => ?_, rfl,
    fun _ _ => rfl⟩
  exact CFSG.RankThree.PartOne.D4RC.rcl_card_fix_unitary hℓ hf hk Φ' H (hunit h)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
