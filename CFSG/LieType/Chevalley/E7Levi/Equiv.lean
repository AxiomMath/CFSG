module

public import CFSG.LieType.Chevalley.E7Levi.Inj

public noncomputable section

namespace CFSG.LieType.Chevalley.E7Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T

variable {τ : Tag} [E7Sub τ] {K : Type} [Field K]

theorem range_nuE7 :
    (nuE7 τ K).range = adjointGroup Tag.E7 K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := hx
    have hle : ∀ g (hg : g ∈ subsystemGroup τ K (e7Set τ)),
        nuE7 τ K ⟨g, hg⟩ ∈ adjointGroup Tag.E7 K := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g hg =>
        nuE7 τ K ⟨g, hg⟩ ∈ adjointGroup Tag.E7 K) ?_ ?_ ?_ ?_ hg
      · rintro x ⟨i, hi, c, rfl | rfl⟩
        · obtain ⟨k, rfl⟩ := exists_e7Idx_eq hi
          have hmem : xUnit τ K (e7Idx k) c ∈ subsystemGroup τ K (e7Set τ) :=
            xUnit_mem_subsystemGroup k.2 c
          have hnu : nuE7 τ K ⟨xUnit τ K (e7Idx k) c, hmem⟩ = xUnit Tag.E7 K k c := by
            rw [nuE7]
            exact e7Res_xUnit (A := e7Set τ) (fun _ hi => hi) k k.2 c
          have heq : (⟨xUnit τ K (e7Idx k) c, _⟩ : subsystemGroup τ K (e7Set τ)) =
              ⟨xUnit τ K (e7Idx k) c, hmem⟩ := Subtype.ext rfl
          rw [heq, hnu]
          exact xUnit_mem_adjointGroup k c
        · obtain ⟨k, rfl⟩ := exists_e7Idx_eq hi
          have hmem : yUnit τ K (e7Idx k) c ∈ subsystemGroup τ K (e7Set τ) :=
            yUnit_mem_subsystemGroup k.2 c
          have hnu : nuE7 τ K ⟨yUnit τ K (e7Idx k) c, hmem⟩ = yUnit Tag.E7 K k c := by
            rw [nuE7]
            exact e7Res_yUnit (A := e7Set τ) (fun _ hi => hi) k k.2 c
          have heq : (⟨yUnit τ K (e7Idx k) c, _⟩ : subsystemGroup τ K (e7Set τ)) =
              ⟨yUnit τ K (e7Idx k) c, hmem⟩ := Subtype.ext rfl
          rw [heq, hnu]
          exact yUnit_mem_adjointGroup k c
      · rw [show (⟨1, one_mem _⟩ : subsystemGroup τ K (e7Set τ)) = 1 from Subtype.ext rfl,
          map_one]
        exact one_mem _
      · intro x y hx hy ihx ihy
        have heq : (⟨x * y, mul_mem hx hy⟩ : subsystemGroup τ K (e7Set τ)) =
            ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact mul_mem ihx ihy
      · intro x hx ih
        have heq : (⟨x⁻¹, inv_mem hx⟩ : subsystemGroup τ K (e7Set τ)) =
            ⟨x, hx⟩⁻¹ := Subtype.ext rfl
        rw [heq, map_inv]
        exact inv_mem ih
    exact hle g g.2
  · refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hx | hx⟩
    · have hg' : g = xUnit Tag.E7 K i c :=
        Units.ext (hx.trans (coe_xUnit (τ := Tag.E7) (R := K) i c).symm)
      rw [hg']
      refine MonoidHom.mem_range.2 ⟨⟨xUnit τ K (e7Idx i) c,
        xUnit_mem_subsystemGroup i.2 c⟩, ?_⟩
      rw [nuE7]
      exact e7Res_xUnit (A := e7Set τ) (fun _ hi => hi) i i.2 c
    · have hg' : g = yUnit Tag.E7 K i c :=
        Units.ext (hx.trans (coe_yUnit (τ := Tag.E7) (R := K) i c).symm)
      rw [hg']
      refine MonoidHom.mem_range.2 ⟨⟨yUnit τ K (e7Idx i) c,
        yUnit_mem_subsystemGroup i.2 c⟩, ?_⟩
      rw [nuE7]
      exact e7Res_yUnit (A := e7Set τ) (fun _ hi => hi) i i.2 c

@[expose] noncomputable def e7LeviGL (τ : Tag) [E7Sub τ] (K : Type) [Field K] [CharP K 2] :
    subsystemGroup τ K (e7Set τ) ≃* adjointGroup Tag.E7 K :=
  (MonoidHom.ofInjective (nuE7_injective (τ := τ) (K := K))).trans
    (MulEquiv.subgroupCongr range_nuE7)

theorem coe_e7LeviGL [CharP K 2] (g : subsystemGroup τ K (e7Set τ)) :
    ((e7LeviGL τ K g : adjointGroup Tag.E7 K) : ModGL Tag.E7 K) = nuE7 τ K g :=
  rfl

theorem coe_e7LeviGL_symm_pinnedX [CharP K 2]
    {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot Tag.E7 γ) (c : K) :
    (((e7LeviGL τ K).symm ⟨pinnedX Tag.E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ :
      subsystemGroup τ K (e7Set τ)) : ModGL τ K) = pinnedX τ K (e7Lat τ γ) c := by
  obtain ⟨ε, hε, hsign⟩ := exists_sign_pinnedX_comp_e7Emb (τ := τ) hγ
  have hεK : (ε : K) = 1 := by
    rcases hε with rfl | rfl
    · norm_num
    · rw [Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero]
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc (1 : K) + 1 = 2 := by ring
        _ = 0 := h2
  set g : subsystemGroup τ K (e7Set τ) :=
    (e7LeviGL τ K).symm ⟨pinnedX Tag.E7 K γ c, pinnedX_mem_adjointGroup γ c⟩
  have hg : e7LeviGL τ K g = ⟨pinnedX Tag.E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ :=
    MulEquiv.apply_symm_apply _ _
  have hnu : nuE7 τ K g = pinnedX Tag.E7 K γ c := by
    rw [← coe_e7LeviGL g, hg]
  have hmem : pinnedX τ K (e7Lat τ γ) c ∈ subsystemGroup τ K (e7Set τ) :=
    rootSubgroup_le_subsystemGroup
      (mem_parabolicRoots_e7Set_iff.2 ⟨γ, ⟨hγ, fun i hi => absurd (Set.mem_univ i) hi⟩, rfl⟩)
      (Subgroup.subset_closure ⟨c, rfl⟩)
  have hnx : nuE7 τ K ⟨pinnedX τ K (e7Lat τ γ) c, hmem⟩ = pinnedX Tag.E7 K γ c := by
    rw [nuE7]
    have hres := e7Res_eq (A := e7Set τ) (fun _ hi => hi)
      (g := ⟨pinnedX τ K (e7Lat τ γ) c, hmem⟩)
      (g' := pinnedX Tag.E7 K γ ((ε : K) * c))
      (fun v => by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun (hsign K c) v)
    rw [hres, hεK, one_mul]
  have hg_eq : g = ⟨pinnedX τ K (e7Lat τ γ) c, hmem⟩ := by
    apply nuE7_injective
    rw [hnu, hnx]
  change (g : ModGL τ K) = pinnedX τ K (e7Lat τ γ) c
  rw [hg_eq]

end CFSG.LieType.Chevalley.E7Levi
