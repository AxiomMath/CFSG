module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Signs

variable {τ : Tag} {K : Type} [Field K]

@[expose] def torusWordSigns (l : List (Fin τ.rank)) : Fin τ.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ (l.map fun i => τ.cartan i j).sum

theorem list_prod_torusElt_neg_one
    (l : List (Fin τ.rank)) :
    (l.map fun i => torusElt τ K i (-1)).prod = rootDiagUnit τ (torusWordSigns l) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, ← rootDiagUnit_one]
    congr 1
    funext j
    simp [torusWordSigns]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ih, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [torusWordSigns, Pi.mul_apply, List.map_cons, List.sum_cons, zpow_add]

@[expose] def IsRigidTuple (b : Fin τ.rank → Kˣ) : Prop :=
  ∀ (δ : K →+* K) (j : Fin τ.rank), Units.map δ.toMonoidHom (b j) = b j

theorem isRigidTuple_one : IsRigidTuple (1 : Fin τ.rank → Kˣ) := fun _ _ => map_one _

theorem IsRigidTuple.mul {b c : Fin τ.rank → Kˣ} (hb : IsRigidTuple b) (hc : IsRigidTuple c) :
    IsRigidTuple (b * c) := fun δ j => by
  rw [Pi.mul_apply, map_mul, hb δ j, hc δ j]

theorem isRigidTuple_torusWordSigns (l : List (Fin τ.rank)) :
    IsRigidTuple (torusWordSigns (K := K) l) := fun δ j => by
  rw [torusWordSigns, map_zpow]
  congr 1
  ext
  simp

theorem torusWordSigns_mul_self (l : List (Fin τ.rank)) :
    torusWordSigns (K := K) l * torusWordSigns l = 1 := by
  funext j
  rw [Pi.mul_apply, torusWordSigns, ← zpow_add, ← two_mul, Pi.one_apply]
  exact (even_two_mul _).neg_one_zpow

theorem torusWordSigns_of_odd {l : List (Fin τ.rank)} {j : Fin τ.rank}
    (h : (l.map fun i => τ.cartan i j).sum % 2 = 1) : torusWordSigns (K := K) l j = -1 :=
  (Int.odd_iff.2 h).neg_one_zpow

theorem torusWordSigns_of_even {l : List (Fin τ.rank)} {j : Fin τ.rank}
    (h : (l.map fun i => τ.cartan i j).sum % 2 = 0) : torusWordSigns (K := K) l j = 1 :=
  (Int.even_iff.2 h).neg_one_zpow

theorem entrywise_rootDiag_of_isRigidTuple {b : Fin τ.rank → Kˣ} (hb : IsRigidTuple b)
    (δ : K →+* K) : entrywise δ (rootDiag b) = rootDiag b := by
  rw [entrywise_rootDiag]
  simp only [hb δ]

theorem rootDiag_mul_comm (a b : Fin τ.rank → Kˣ) :
    rootDiag a * rootDiag b = rootDiag b * (rootDiag a : Module.End K (RootModule τ K)) := by
  rw [rootDiag_mul_rootDiag, rootDiag_mul_rootDiag, mul_comm]

theorem units_neg_one_ne_one (hK : ringChar K ≠ 2) : (-1 : Kˣ) ≠ 1 := fun h =>
  Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h)

end Signs

theorem coe_orbitH_neg_one
    (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    (a : Fin t.foldedTag.rank) :
    (orbitH t K σ a (-1) : ModGL t.tag K) =
      ((t.orbitWord a).map fun j => torusElt t.tag K j (-1)).prod := by
  rw [coe_orbitH_eq]
  refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin ((t.mem_orbitWord).1 hj)
  rw [orbitUnitParam_pow t σ _ hk]
  congr 1
  ext
  simp [orbitFieldUnit]

theorem exists_orbit_sign_rows (t : TwistTag) :
    ∃ (a b : Fin t.foldedTag.rank) (k₁ k₂ : Fin t.tag.rank),
      ((t.orbitWord a).map fun i => t.tag.cartan i k₁).sum % 2 = 1 ∧
      ((t.orbitWord b).map fun i => t.tag.cartan i k₁).sum % 2 = 0 ∧
      ((t.orbitWord b).map fun i => t.tag.cartan i k₂).sum % 2 = 1 := by
  cases t
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩, by decide,
      by decide, by decide⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩, by decide,
      by decide, by decide⟩

theorem odd_diagram_coordinate_fields_fixed_four_group
    (t : TwistTag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) (σ : K →+* K) :
    ∃ A : Subgroup (ModGL t.tag K), A ≤ graphFixedRootGroup t K σ ∧
      CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 4 ∧
      (∀ δ : K →+* K, ∀ g ∈ A, entrywise δ (g : Module.End K (RootModule t.tag K)) = g) ∧
      (∀ g ∈ A, diagramMap t K * g = g * diagramMap t K) ∧
      ∀ b : Fin t.tag.rank → Kˣ, ∀ g ∈ A,
        rootDiag b * (g : Module.End K (RootModule t.tag K)) = g * rootDiag b := by
  obtain ⟨a₁, a₂, k₁, k₂, h₁, h₂, h₃⟩ := exists_orbit_sign_rows t
  set b₁ := torusWordSigns (K := K) (t.orbitWord a₁)
  set b₂ := torusWordSigns (K := K) (t.orbitWord a₂)
  have hs : (orbitH t K σ a₁ (-1) : ModGL t.tag K) = rootDiagUnit t.tag b₁ := by
    rw [coe_orbitH_neg_one, list_prod_torusElt_neg_one]
  have hu : (orbitH t K σ a₂ (-1) : ModGL t.tag K) = rootDiagUnit t.tag b₂ := by
    rw [coe_orbitH_neg_one, list_prod_torusElt_neg_one]
  have hsC := orbitH_mem_graphFixedRootGroup t σ a₁ (-1)
  have huC := orbitH_mem_graphFixedRootGroup t σ a₂ (-1)
  rw [hs] at hsC
  rw [hu] at huC
  have hsq : ∀ l : List (Fin t.tag.rank),
      rootDiagUnit t.tag (torusWordSigns (K := K) l) *
        rootDiagUnit t.tag (torusWordSigns l) = 1 := fun l => by
    rw [← rootDiagUnit_mul, torusWordSigns_mul_self, rootDiagUnit_one]
  have hcomm : rootDiagUnit t.tag b₁ * rootDiagUnit t.tag b₂ =
      rootDiagUnit t.tag b₂ * rootDiagUnit t.tag b₁ := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hne1 := units_neg_one_ne_one hK
  have hs1 : rootDiagUnit t.tag b₁ ≠ 1 := fun h => hne1 (by
    rw [← rootDiagUnit_one] at h
    rw [← torusWordSigns_of_odd h₁, ← Pi.one_apply (M := fun _ => Kˣ) k₁]
    exact congrFun (rootDiagUnit_injective h) k₁)
  have hu1 : rootDiagUnit t.tag b₂ ≠ 1 := fun h => hne1 (by
    rw [← rootDiagUnit_one] at h
    rw [← torusWordSigns_of_odd h₃, ← Pi.one_apply (M := fun _ => Kˣ) k₂]
    exact congrFun (rootDiagUnit_injective h) k₂)
  have hsu : rootDiagUnit t.tag b₁ ≠ rootDiagUnit t.tag b₂ := fun h => hne1 (by
    rw [← torusWordSigns_of_odd h₁, ← torusWordSigns_of_even (K := K) h₂]
    exact congrFun (rootDiagUnit_injective h) k₁)
  obtain ⟨A, hAmem, hAle, hA, hAcard⟩ := FourGroup.exists_kleinFour (hsq _) (hsq _) hcomm hs1 hu1
    hsu
  have hrigid : ∀ g ∈ A, ∃ c : Fin t.tag.rank → Kˣ, IsRigidTuple c ∧
      g = rootDiagUnit t.tag c := by
    intro g hg
    rcases hAmem g hg with rfl | rfl | rfl | rfl
    · exact ⟨1, isRigidTuple_one, rootDiagUnit_one.symm⟩
    · exact ⟨b₁, isRigidTuple_torusWordSigns _, rfl⟩
    · exact ⟨b₂, isRigidTuple_torusWordSigns _, rfl⟩
    · exact ⟨b₁ * b₂, (isRigidTuple_torusWordSigns _).mul (isRigidTuple_torusWordSigns _),
        (rootDiagUnit_mul _ _).symm⟩
  have hfix : ∀ δ : K →+* K, ∀ g ∈ A,
      entrywise δ (g : Module.End K (RootModule t.tag K)) = g := by
    intro δ g hg
    obtain ⟨c, hc, rfl⟩ := hrigid g hg
    exact entrywise_rootDiag_of_isRigidTuple hc δ
  have hAC : A ≤ graphFixedRootGroup t K σ := hAle _ hsC huC
  refine ⟨A, hAC, hA, hAcard, hfix, fun g hg => ?_, fun b g hg => ?_⟩
  · have hF : twistHom t K σ g = g :=
      (Subgroup.mem_inf.1 (graphFixedRootGroup_le t K σ (hAC hg))).2
    have hσg : Units.map (entrywiseHom σ) g = g := Units.ext (hfix σ g hg)
    rw [twistHom_apply, hσg] at hF
    calc diagramMap t K * g = diagramMap t K * g * (diagramMap t K)⁻¹ * diagramMap t K := by
          group
      _ = g * diagramMap t K := by rw [hF]
  · obtain ⟨c, -, rfl⟩ := hrigid g hg
    exact rootDiag_mul_comm b c

end CFSG.LieType.Chevalley
