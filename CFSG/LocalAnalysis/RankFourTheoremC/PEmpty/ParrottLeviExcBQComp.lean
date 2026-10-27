module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.TitsSimplicity.Levi
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

namespace ParrottPA3

theorem levi_empty {ι G : Type*} [DecidableEq ι] [Group G] (X : (ι → ℤ) → Subgroup G) :
    levi X (∅ : Finset ι) = ⊥ := by
  simp [levi]

theorem levi_union {ι G : Type*} [DecidableEq ι] [Group G] (X : (ι → ℤ) → Subgroup G)
    (A B : Finset ι) : levi X (A ∪ B) = levi X A ⊔ levi X B :=
  Finset.iSup_union

theorem levi_le_centralizer {ι G : Type*} [DecidableEq ι] [Group G]
    {X : (ι → ℤ) → Subgroup G} {A B : Finset ι}
    (h : ∀ i ∈ A, ∀ j ∈ B, ∀ u ∈ rankOne X i, ∀ v ∈ rankOne X j, u * v = v * u) :
    levi X A ≤ Subgroup.centralizer (levi X B : Set G) :=
  iSup₂_le fun i hi => Subgroup.le_centralizer_iff.mpr <| iSup₂_le fun j hj v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => h i hi j hj u hu v hv

theorem exists_ssubset_of_not_isIndecomposable {N k : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    {e : Fin k → Fin N} (he : Function.Injective e)
    (hA : ¬ IsIndecomposable (A.submatrix e e)) :
    ∃ J₁ J₂ : Finset (Fin N), J₁ ⊂ Finset.univ.image e ∧ J₂ ⊂ Finset.univ.image e ∧
      J₁ ∪ J₂ = Finset.univ.image e ∧ ∀ i ∈ J₁, ∀ j ∈ J₂, i ≠ j ∧ A i j = 0 := by
  obtain ⟨I₁, I₂, hI₁, hI₂, hd, hu, h0⟩ := not_not.mp hA
  have hnot : ∀ {S T : Finset (Fin k)}, Disjoint S T → ∀ b ∈ T, e b ∉ S.image e := by
    intro S T hST b hb hmem
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hmem
    exact Finset.disjoint_left.mp hST ha (by rwa [he hab])
  have hss : ∀ {S T : Finset (Fin k)}, Disjoint S T → T.Nonempty →
      S.image e ⊂ Finset.univ.image e := by
    rintro S T hST ⟨b, hb⟩
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.image_subset_image (Finset.subset_univ _), fun heq => hnot hST b hb ?_⟩
    rw [heq]
    exact Finset.mem_image_of_mem e (Finset.mem_univ b)
  refine ⟨I₁.image e, I₂.image e, hss hd hI₂, hss hd.symm hI₁, by rw [← Finset.image_union, hu],
    fun i hi j hj => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨fun hab => Finset.disjoint_left.mp hd ha (by rwa [he hab]),
    by simpa only [Matrix.submatrix_apply] using h0 a ha b hb⟩

end ParrottPA3

theorem exists_indecomposable_dvd_card_levi [Finite K]
    (hcomm : ∀ i j, i ≠ j → D.cartan i j = 0 → ∀ u ∈ rankOne D.rootGroup i,
      ∀ v ∈ rankOne D.rootGroup j, u * v = v * u)
    {p : ℕ} (hp : p.Prime) (I : Finset (Fin D.rank)) (h : p ∣ Nat.card (levi D.rootGroup I)) :
    ∃ C ⊆ I, C.Nonempty ∧
      IsIndecomposable (D.cartan.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)) ∧
      p ∣ Nat.card (levi D.rootGroup C) := by
  induction I using Finset.strongInduction with
  | H I ih =>
    have hIne : I.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      rw [ParrottPA3.levi_empty, Subgroup.card_bot] at h
      exact hp.one_lt.ne' (Nat.dvd_one.mp h)
    by_cases hA : IsIndecomposable
        (D.cartan.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl))
    · exact ⟨I, subset_rfl, hIne, hA, h⟩
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hU, h0⟩ :=
      ParrottPA3.exists_ssubset_of_not_isIndecomposable (I.orderEmbOfFin rfl).injective hA
    rw [Finset.image_orderEmbOfFin_univ] at hJ₁ hJ₂ hU
    have hcard : Nat.card (levi D.rootGroup I) ∣
        Nat.card (levi D.rootGroup J₁) * Nat.card (levi D.rootGroup J₂) := by
      rw [← hU, ParrottPA3.levi_union]
      exact CFSG.AGLEmbedding.ParabPrime.card_sup_dvd_mul _ _
        ((ParrottPA3.levi_le_centralizer fun i hi j hj =>
          hcomm i j (h0 i hi j hj).1 (h0 i hi j hj).2).trans
          (Subgroup.centralizer_le_normalizer _))
    rcases hp.dvd_mul.mp (h.trans hcard) with h₁ | h₂
    · obtain ⟨C, hC, hCne, hCA, hCp⟩ := ih J₁ hJ₁ h₁
      exact ⟨C, hC.trans hJ₁.subset, hCne, hCA, hCp⟩
    · obtain ⟨C, hC, hCne, hCA, hCp⟩ := ih J₂ hJ₂ h₂
      exact ⟨C, hC.trans hJ₂.subset, hCne, hCA, hCp⟩

theorem isQuasisimple_levi (hdiv : D.divisible = ∅)
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (hE : RootGroupCommutators D) (C : Finset (Fin D.rank))
    (hA : IsIndecomposable (D.cartan.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)))
    (hperf : Group.IsPerfect ↥(levi D.rootGroup C)) [Nontrivial ↥(levi D.rootGroup C)] :
    CFSG.IsQuasisimple ↥(levi D.rootGroup C) := by
  rw [← leviC_orderEmbOfFin] at hperf ⊢
  have : Nontrivial ↥(leviC D (C.orderEmbOfFin rfl)) := by
    rw [leviC_orderEmbOfFin]
    infer_instance
  exact isQuasisimple_leviC hdiv hct hext hBU hE hA hperf

theorem center_levi_le (hdiv : D.divisible = ∅)
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (hE : RootGroupCommutators D) (C : Finset (Fin D.rank)) :
    (center ↥(levi D.rootGroup C)).map (levi D.rootGroup C).subtype ≤ ⨆ i, H i := by
  rw [← leviC_orderEmbOfFin]
  exact (center_leviC_le (e := C.orderEmbOfFin rfl) hdiv hct hext hBU).trans
    (iSup_comp_le H _)

theorem isPerfect_levi_of_le_commutator (hdiv : D.divisible = ∅)
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (C : Finset (Fin D.rank))
    (h : ∀ j ∈ C, D.rootGroup (Pi.single j 1) ≤ ⁅levi D.rootGroup C, levi D.rootGroup C⁆) :
    Group.IsPerfect ↥(levi D.rootGroup C) := by
  rw [← leviC_orderEmbOfFin] at h ⊢
  have he : Function.Injective (C.orderEmbOfFin rfl) := (C.orderEmbOfFin rfl).injective
  refine isPerfect_of_rootGroup_single_le_commutator (restrict_isCTGroupDatum he hdiv hct)
    (fun γ hγ h2 => absurd h2 (two_smul_notMem_roots (D := restrict D he) rfl hγ))
    fun (i : Fin C.card) x hx => ?_
  have hx₀ : x ∈ (D.rootGroup (Restrict.ext (C.orderEmbOfFin rfl) (Pi.single i 1))).subgroupOf
      (leviC D (C.orderEmbOfFin rfl)) := hx
  rw [Restrict.ext_single he, Subgroup.mem_subgroupOf] at hx₀
  have hmem := h _ (C.orderEmbOfFin_mem rfl i) hx₀
  rw [← Subgroup.map_subtype_commutator] at hmem
  exact (Subgroup.mem_map_iff_mem (x := x) (Subgroup.subtype_injective _)).mp hmem

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ
