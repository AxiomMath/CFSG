module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Orbit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum


section Torus

variable {τ : Tag} {M : Type} [Field M]

theorem torusRootChar_rootTorusSL2 {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Mˣ)
    (j : Fin τ.rank) :
    torusRootChar (rootTorusSL2 τ M β c) (Pi.single j 1) =
      ((c ^ corootPair β (Pi.single j 1) : Mˣ) : M) := by
  obtain ⟨-, -, -, -, h5, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ M hβ
  exact torusRootChar_eq_of_apply (isRoot_single τ j) ((h5 c).2 _ (isRoot_single τ j))

theorem exists_commute_rootTorus_prod {x : ModGL τ M} (ζ : Mˣ)
    (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (hΓ : ∀ y ∈ Γ, IsRoot τ y.1)
    (h : ∀ y ∈ Γ, ∀ s : Mˣ, Commute x (rootTorusSL2 τ M y.1 s)) :
    ∃ P ∈ torusGroup τ M, Commute x P ∧ ∀ j : Fin τ.rank,
      torusRootChar P (Pi.single j 1) = ((ζ ^ regCoweight Γ j : Mˣ) : M) := by
  induction Γ with
  | nil =>
    refine ⟨1, one_mem _, Commute.one_right x, fun j => ?_⟩
    rw [torusRootChar_one]
    simp [regCoweight]
  | cons y Γ ih =>
    obtain ⟨P, hPT, hxP, hPχ⟩ := ih (fun y' hy' => hΓ y' (List.mem_cons_of_mem y hy'))
      fun y' hy' => h y' (List.mem_cons_of_mem y hy')
    have hy := hΓ y List.mem_cons_self
    obtain ⟨-, hQT, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ M hy
    refine ⟨rootTorusSL2 τ M y.1 (ζ ^ y.2) * P, mul_mem (hQT _) hPT,
      (h y List.mem_cons_self _).mul_right hxP, fun j => ?_⟩
    rw [torusRootChar_mul (torusGroup_le_diagonalGroup (hQT _))
      (torusGroup_le_diagonalGroup hPT), hPχ j, torusRootChar_rootTorusSL2 hy]
    simp only [regCoweight, List.map_cons, List.sum_cons, zpow_add, ← zpow_mul, Units.val_mul]

end Torus

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

variable (p) in
include p in
theorem mem_torusGroup_of_commute_rootTorus {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {z : ModGL τ k} (hz : z ∈ adjointGroup τ k) (Γ : List ((Fin τ.rank → ℤ) × ℤ))
    (hΓ : ∀ y ∈ Γ, IsRoot τ y.1) (h : ∀ y ∈ Γ, ∀ s : kˣ, Commute z (rootTorusSL2 τ k y.1 s))
    (B : ℕ) (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < B) :
    z ∈ torusGroup τ k := by
  classical
  have hpp : p.Prime := Fact.out
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (B + p + 8)
  have hℓ7 : 7 < ℓ := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h0
    have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff k p ℓ).1 h0
    have := (Nat.prime_dvd_prime_iff_eq hpp hℓ).1 hdvd
    omega
  have : NeZero (ℓ : k) := ⟨hℓk⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k ℓ
  set ζ : kˣ := (hζ₀.isUnit hℓ.ne_zero).unit with hζdef
  have hζ : orderOf ζ = ℓ := (IsPrimitiveRoot.coe_units_iff.1 hζ₀).eq_orderOf.symm
  obtain ⟨P, hPT, hxP, hPχ⟩ := exists_commute_rootTorus_prod ζ Γ hΓ h
  set zc := regCoweight Γ with hzc
  have hdz : rootDiagUnit τ (fun j => ζ ^ zc j) ∈ torusGroup τ k := by
    obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift τ k (fun j => ζ ^ zc j)
    rw [ht]
    refine Subgroup.list_prod_mem _ fun q hq => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
    exact torusElt_mem_torusGroup j _
  have hPeq : P = rootDiagUnit τ (fun j => ζ ^ zc j) := eq_of_torusRootChar_single hPT hdz
    fun j => by rw [hPχ j, torusRootChar_rootDiagUnit _ (isRoot_single τ j), rootChar_single']
  rw [← toralCentralizer_eq_torusGroup_of_regular hτ hℓ hℓ7 hζ zc fun α hα hdvd => ?_]
  · refine Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hPeq]
    exact hxP.eq
  · obtain ⟨hne, hlt⟩ := hreg α hα
    have h1 : ℓ ∣ (∑ j, zc j * α j).natAbs := Int.natCast_dvd.1 hdvd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
    omega

omit
  [IsAlgClosed k] [Fact p.Prime]
  [CharP k p] in
theorem rootChar_eq_one_of_commute {τ : Tag} {b : Fin τ.rank → kˣ} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h : Commute (rootDiagUnit τ b) (rootSL2 τ k β (uSL 1))) :
    rootChar b β = 1 := by
  rw [rootSL2_uSL_eq] at h
  have h1 := rootDiagUnit_conj_pinnedX b hβ ((pinnedData τ β).2.2 • (1 : k))
  rw [h.eq, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective τ k β h1
  have hε : ((pinnedData τ β).2.2 • (1 : k)) ≠ 0 := by
    rcases pinnedSign_eq (τ := τ) β with he | he <;> rw [he] <;> simp
  apply Units.ext
  have h3 : ((rootChar b β : kˣ) : k) * ((pinnedData τ β).2.2 • (1 : k)) =
      1 * ((pinnedData τ β).2.2 • (1 : k)) := by rw [one_mul, ← h2]
  exact mul_right_cancel₀ hε h3

section Datum

variable (D : OrthogonalSemilinearFixedRootDatum .E7 p k)

theorem simpleRootsJ_eq_simpleUnion [Subsingleton (KernelComponent D.χ)] :
    D.simpleRootsJ = simpleUnion D.χ := by
  rw [D.simpleRootsJ_eq]
  ext β
  simp only [unionSimpleRoots, simpleUnion, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    refine ⟨i, ?_, h⟩
    obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
    obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i₀
    have hα₀K : α₀.1 ∈ componentRoots D.χ i₀ := ⟨α₀.2, by rw [← hα₀]⟩
    have hi₀ : i₀ ∈ D.J := by
      rw [hJ]
      exact ⟨0, α₀.1, hα₀K, α₀.1, hα₀K, by simp⟩
    rwa [Subsingleton.elim i i₀]

theorem commute_rootSL2_of_commute_orbitGroup (hq : 3 ≤ D.q)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) {z : ModGL .E7 k}
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : β ∈ D.simpleRootsJ) (A : SL2 k) :
    z * rootSL2 .E7 k β A = rootSL2 .E7 k β A * z := by
  have hO : thetaOrbit D.θ β ∈ D.orbits := ⟨β, hβ, rfl⟩
  obtain ⟨j, hj, hjβ⟩ := D.exists_orbitVec_eq hO (self_mem_thetaOrbit D.θ β)
  have hτ : Tag.E7 ≠ .G2 := by decide
  have hX : ∀ c, (z : Module.End k (RootModule .E7 k)) * (D.orbitX (thetaOrbit D.θ β) c :
      Module.End k (RootModule .E7 k)) = (D.orbitX (thetaOrbit D.θ β) c :
        Module.End k (RootModule .E7 k)) * z := fun c =>
    congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inl rfl⟩))
  have hY : ∀ c, (z : Module.End k (RootModule .E7 k)) * (D.orbitY (thetaOrbit D.θ β) c :
      Module.End k (RootModule .E7 k)) = (D.orbitY (thetaOrbit D.θ β) c :
        Module.End k (RootModule .E7 k)) * z := fun c =>
    congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inr rfl⟩))
  have hu := fun t => commute_uSL_of_commute_orbitX D hτ hq hO (hcard _ hO) hX hj t
  have hv := fun t => commute_vSL_of_commute_orbitY D hτ hq hO (hcard _ hO) hY hj t
  rw [hjβ] at hu hv
  have hle : (⊤ : Subgroup (SL2 k)) ≤
      (Subgroup.centralizer ({z} : Set (ModGL .E7 k))).comap (rootSL2 .E7 k β) := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    · exact Units.ext (hu t).symm
    · exact Units.ext (hv t).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top A))).symm

theorem orbitCard_of_e7Word {m : ℕ} (hm : m = 2 ∨ m = 3) (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ)) :
    ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2 := by
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties 1 2 D.χ (ToralSign.wordElt .E7 e7Word2_1) := by
    rw [hχ]
    rcases hm with rfl | rfl
    · exact h7.theta ⟨2, 36, 2, e7OmegaWords2⟩ (by simp [e7SignDiagramReps]) e7Word2_1
        (by simp [e7OmegaWords2])
    · exact h7.theta ⟨3, 28, 2, e7OmegaWords3⟩ (by simp [e7SignDiagramReps]) e7Word3_1
        (by simp [e7OmegaWords3])
  exact fun O hO => orbitCard_eq_of_thetaProperties D hθp hθ hO

end Datum

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
