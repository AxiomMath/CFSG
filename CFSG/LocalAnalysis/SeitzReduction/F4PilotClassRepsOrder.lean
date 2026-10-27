module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassReps

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps

variable {K : Type} [Field K]

namespace ClassReps

@[expose] def u0Roots : Set (Fin Tag.F4.rank → ℤ) :=
  {γ | ∃ p ∈ f4CentListV, orbitCertRoot .F4 p = γ}

@[expose] def u0Omitted : List (Fin Tag.F4.rank → ℤ) :=
  [![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0], ![1, 1, 0, 0]]

theorem u0Roots_check :
    (∀ p ∈ f4CentListV, 24 ≤ p ∧ p ≤ 47) ∧
      (∀ p ∈ f4CentListV, ∀ i : Fin Tag.F4.rank, 0 ≤ orbitCertRoot .F4 p i) ∧
      (f4CentListV.map (orbitCertRoot .F4)).toFinset.card = 20 ∧
      (∀ γ ∈ rootFinset .F4, 0 < height γ → γ ∉ u0Omitted →
        ∃ p ∈ f4CentListV, orbitCertRoot .F4 p = γ) ∧
      (∀ p ∈ f4CentListV, ∀ q ∈ f4CentListV, ∀ ε ∈ u0Omitted,
        (∀ i, orbitCertRoot .F4 p i ≤ ε i) → (∀ i, orbitCertRoot .F4 q i ≤ ε i) →
          ∃ i, orbitCertRoot .F4 p i = 0 ∧ orbitCertRoot .F4 q i = 0 ∧ ε i ≠ 0) := by
  decide +kernel

theorem u0Roots_eq : u0Roots = ↑(f4CentListV.map (orbitCertRoot .F4)).toFinset := by
  ext γ
  simp only [u0Roots, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]

theorem ncard_u0Roots : u0Roots.ncard = 20 := by
  rw [u0Roots_eq, Set.ncard_coe_finset]
  exact u0Roots_check.2.2.1

section Roots


theorem u0Roots_pos : ∀ α ∈ u0Roots, IsRoot .F4 α ∧ 0 < height α := by
  rintro _ ⟨p, hp, rfl⟩
  exact f4_isRoot_pos (u0Roots_check.1 p hp)

theorem u0Roots_closed : ∀ α ∈ u0Roots, ∀ β ∈ u0Roots, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot .F4 (a • α + b • β) → a • α + b • β ∈ u0Roots := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hroot
  obtain ⟨-, hnn, -, hcov, hbelow⟩ := u0Roots_check
  have hαpos := (f4_isRoot_pos (u0Roots_check.1 p hp)).2
  have hβpos := (f4_isRoot_pos (u0Roots_check.1 q hq)).2
  have hcoord : ∀ i, (a • orbitCertRoot .F4 p + b • orbitCertRoot .F4 q) i =
      (a : ℤ) * orbitCertRoot .F4 p i + (b : ℤ) * orbitCertRoot .F4 q i := fun i => by
    simp [Pi.add_apply, nsmul_eq_mul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine hcov _ (mem_rootFinset.2 hroot) ?_ ?_
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · intro hmem
    obtain ⟨i, hαi, hβi, hεi⟩ := hbelow p hp q hq _ hmem
      (fun i => by
        rw [hcoord i]
        nlinarith [hnn p hp i, hnn q hq i])
      (fun i => by
        rw [hcoord i]
        nlinarith [hnn p hp i, hnn q hq i])
    apply hεi
    rw [hcoord i, hαi, hβi]
    ring

variable (K) in
@[expose] noncomputable def u0 : Subgroup (ModGL .F4 K) := rootSpan .F4 K u0Roots

theorem natCard_u0 : Nat.card (u0 K) = Nat.card K ^ 20 := by
  rw [u0, card_rootSpan u0Roots_pos u0Roots_closed, ncard_u0Roots]

theorem u0_le_posUnipotent : u0 K ≤ posUnipotent .F4 K :=
  iSup₂_le fun α hα => le_iSup₂_of_le (f := fun γ (_ : IsRoot .F4 γ ∧ 0 < height γ) =>
    rootSubgroup .F4 K γ) α (u0Roots_pos α hα) le_rfl

theorem u0_le_adjointGroup : u0 K ≤ adjointGroup .F4 K :=
  u0_le_posUnipotent.trans posUnipotent_le_adjointGroup

theorem u0_le_centralizer_frameRep [CharP K 2] {w : adjointGroup .F4 K}
    (hw : w ∈ frameReps K) :
    u0 K ≤ centralizer ({(w : ModGL .F4 K)} : Set (ModGL .F4 K)) := by
  simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact f4x_central (Or.inr rfl) 1 (u0_le_posUnipotent hx)
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact f4x_central (Or.inl rfl) 1 (u0_le_posUnipotent hx)
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    have h47 := f4x_central (Or.inr rfl) 1 (u0_le_posUnipotent hx)
    have h44 := f4x_central (Or.inl rfl) 1 (u0_le_posUnipotent hx)
    change x * (f4x K 47 1 * f4x K 44 1) = f4x K 47 1 * f4x K 44 1 * x
    calc x * (f4x K 47 1 * f4x K 44 1) = (x * f4x K 47 1) * f4x K 44 1 := by group
      _ = f4x K 47 1 * (x * f4x K 44 1) := by rw [h47]; group
      _ = f4x K 47 1 * f4x K 44 1 * x := by rw [h44]; group
  · rw [u0, rootSpan_eq_closure, closure_le]
    rintro _ ⟨β, ⟨p, hp, rfl⟩, d, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact f4x_commute_classV hp d

end Roots

theorem exists_isPGroup_le_centralizer [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : orderOf y = 2) :
    ∃ P : Subgroup (adjointGroup .F4 K),
      P ≤ centralizer ({y} : Set (adjointGroup .F4 K)) ∧ IsPGroup 2 P ∧
        Nat.card P = Nat.card K ^ 20 := by
  obtain ⟨g, hg⟩ := exists_conj_mem_frameReps hy
  set w := g * y * g⁻¹ with hw
  set P₀ : Subgroup (adjointGroup .F4 K) := (u0 K).subgroupOf (adjointGroup .F4 K) with hP₀
  have hP₀card : Nat.card P₀ = Nat.card K ^ 20 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe u0_le_adjointGroup).toEquiv).trans natCard_u0
  refine ⟨P₀.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1
      (u0_le_centralizer_frameRep hg (Subgroup.mem_subgroupOf.1 hx))
    have hxw' : x * w = w * x := Subtype.ext (by simpa using hxw)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : y = g⁻¹ * w * g := by rw [hw]; group
    rw [e]
    calc g⁻¹ * x * g * (g⁻¹ * w * g) = g⁻¹ * (x * w) * g := by group
      _ = g⁻¹ * (w * x) * g := by rw [hxw']
      _ = g⁻¹ * w * g * (g⁻¹ * x * g) := by group
  · have hcard : Nat.card (P₀.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card K ^ 20 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP₀card]
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    refine IsPGroup.of_card (n := n * 20) ?_
    rw [hcard, Nat.card_eq_fintype_card, hn, ← pow_mul]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP₀card]

theorem pow_twenty_dvd_card_centralizer [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : orderOf y = 2) :
    Nat.card K ^ 20 ∣ Nat.card (centralizer ({y} : Set (adjointGroup .F4 K))) := by
  obtain ⟨P, hP, -, hcard⟩ := exists_isPGroup_le_centralizer hy
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hP

end ClassReps

end CFSG.SeitzReduction.F4Pilot
