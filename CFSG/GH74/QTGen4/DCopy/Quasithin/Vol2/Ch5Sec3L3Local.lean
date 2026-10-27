module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3Local
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3Model
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

theorem sec53S_le_inf_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ sec53G1 M L H B ⊓ sec53G2 M L H D := by
  rw [← L3Model.pCoreOf_inf_F4 h527 hyp]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

namespace L3Model

omit [Finite F] in

theorem subImg_U_F4 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) (h527 : Stmt5_2_7_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    subImg Mo.b₁ (projUnitriangular 3 F) = sec53S T L := by
  ext x
  rw [mem_subImg_b₁]
  have hUN : projUnitriangular 3 F ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := by
    rw [normalizer_inf_normalizer Mo.data]
    exact Subgroup.le_normalizer
  constructor
  · rintro ⟨h, hU⟩
    have h2 := Mo.mem_G2_of_mem_normalizer ⟨x, h⟩ (Subgroup.mem_inf.mp (hUN hU)).2
    have := (Mo.mem_S_iff_F4 h527 hyp ⟨x, Subgroup.mem_inf.mpr ⟨h, h2⟩⟩).mpr
    rw [coe_isoφ12_eq_φ1] at this
    exact this hU
  · intro hx
    have hxI := sec53S_le_inf_F4 h527 hyp hx
    refine ⟨(Subgroup.mem_inf.mp hxI).1, ?_⟩
    have := (Mo.mem_S_iff_F4 h527 hyp ⟨x, hxI⟩).mp hx
    rwa [coe_isoφ12_eq_φ1] at this

omit [Finite F] in

theorem subImg_Z_F4 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) (h527 : Stmt5_2_7_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    subImg Mo.b₁ (centerOf (projUnitriangular 3 F)) = sec53ZS T L := by
  have hU : projUnitriangular 3 F ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Subgroup.le_normalizer.trans Mo.data.borel.lt₁.le
  rw [← subImg_centerOf Mo.b₁_injective hU, Mo.subImg_U_F4 h527 hyp]

end L3Model

theorem frame_sec53_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    Frame (sec53S T L) (pCoreOf 2 L) (pCoreOf 2 (oTwoUpper H)) := by
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  have hU : projUnitriangular 3 F ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Subgroup.le_normalizer.trans Mo.data.borel.lt₁.le
  have := Frame.transport Mo.b₁ Mo.data.frame hU Mo.b₁_injective
  rwa [Mo.subImg_U_F4 h527 hyp, Mo.subImg_R₁ hyp, Mo.subImg_R₂ hyp hty] at this

theorem sup_sec53_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    pCoreOf 2 L ⊔ pCoreOf 2 (oTwoUpper H) = sec53S T L := by
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  have h1 : Mo.R₁ ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Subgroup.le_normalizer
  have h2 : Mo.R₂ ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Mo.data.borel.le₂.trans (Subgroup.le_normalizer.trans Mo.data.borel.lt₁.le)
  rw [← Mo.subImg_R₁ hyp, ← Mo.subImg_R₂ hyp hty, ← Mo.subImg_U_F4 h527 hyp, ← Mo.data.borel.sup]
  unfold subImg
  rw [Subgroup.subgroupOf_sup h1 h2, Subgroup.map_sup]

theorem l3facts_two_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    IsElemAbelian 2 (pCoreOf 2 L) ∧ IsElemAbelian 2 (pCoreOf 2 (oTwoUpper H)) ∧
      pCoreOf 2 L ⊔ pCoreOf 2 (oTwoUpper H) = sec53S T L ∧
      pCoreOf 2 L ⊓ pCoreOf 2 (oTwoUpper H) = sec53ZS T L ∧
      ⁅sec53S T L, sec53S T L⁆ ≤ sec53ZS T L := by
  have hF := frame_sec53_F4 h527 hyp hty hf
  exact ⟨hF.Q₁_ea, hF.Q₂_ea, sup_sec53_F4 h527 hyp hty hf, hF.inter, frame_commutator_le hF⟩

theorem l3facts_three_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    (∀ A : Subgroup G, A ≤ sec53S T L → IsElemAbelian 2 A →
        A ≤ pCoreOf 2 L ∨ A ≤ pCoreOf 2 (oTwoUpper H)) ∧
      (∀ A : Subgroup G, sec53ZS T L < A → A ≤ pCoreOf 2 L →
        sec53S T L ⊓ Subgroup.centralizer (A : Set G) = pCoreOf 2 L) ∧
      ∀ A : Subgroup G, sec53ZS T L < A → A ≤ pCoreOf 2 (oTwoUpper H) →
        sec53S T L ⊓ Subgroup.centralizer (A : Set G) = pCoreOf 2 (oTwoUpper H) := by
  have hF := frame_sec53_F4 h527 hyp hty hf
  exact ⟨fun A hA hAe => frame_le_or_le hF hA hAe,
    fun A hZA hA => frame_inf_centralizer_eq₁ hF hZA hA,
    fun A hZA hA => frame_inf_centralizer_eq₂ hF hZA hA⟩

omit [Finite F] in

theorem L3Model.mem_centerOf_U_F4 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {z : G} (hz : z ∈ sec53ZS T L) :
    ∃ h : z ∈ sec53G1 M L H B,
      ((isoφ1 Mo.iso ⟨z, h⟩ : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ centerOf (projUnitriangular 3 F) := by
  rw [← Mo.subImg_Z_F4 h527 hyp] at hz
  exact Mo.mem_subImg_b₁.mp hz

omit [Finite F] in

theorem L3Model.exists_inf_conj_F4 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {z z' : G} (hz : z ∈ sec53ZS T L)
    (hz1 : z ≠ 1) (hz' : z' ∈ sec53ZS T L) (hz1' : z' ≠ 1) :
    ∃ g ∈ sec53G1 M L H B ⊓ sec53G2 M L H D, g * z * g⁻¹ = z' := by
  obtain ⟨h, hw⟩ := Mo.mem_centerOf_U_F4 h527 hyp hz
  obtain ⟨h', hw'⟩ := Mo.mem_centerOf_U_F4 h527 hyp hz'
  obtain ⟨c, hc, hcw⟩ :=
    Mo.data.trans _ hw (Mo.coe_iso_ne_one h hz1) _ hw' (Mo.coe_iso_ne_one h' hz1')
  have hcN : c ∈ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := by
    rw [normalizer_inf_normalizer Mo.data]
    exact Mo.data.B₀_le hc
  set g : G := Mo.b₁ ⟨c, (Subgroup.mem_inf.mp hcN).1⟩ with hg
  have hgG₁ : g ∈ sec53G1 M L H B := ((isoφ1 Mo.iso).symm ⟨c, _⟩).2
  have hgc : isoφ1 Mo.iso ⟨g, hgG₁⟩ = ⟨c, (Subgroup.mem_inf.mp hcN).1⟩ := by
    show isoφ1 Mo.iso ((isoφ1 Mo.iso).symm ⟨c, _⟩) = _
    rw [MulEquiv.apply_symm_apply]
  have hgG₂ : g ∈ sec53G2 M L H D := Mo.mem_G2_of_mem_normalizer ⟨g, hgG₁⟩ (by
    rw [hgc]
    exact (Subgroup.mem_inf.mp hcN).2)
  refine ⟨g, Subgroup.mem_inf.mpr ⟨hgG₁, hgG₂⟩, ?_⟩
  have hmem : g * z * g⁻¹ ∈ sec53G1 M L H B :=
    (sec53G1 M L H B).mul_mem ((sec53G1 M L H B).mul_mem hgG₁ h) ((sec53G1 M L H B).inv_mem hgG₁)
  have key : isoφ1 Mo.iso ⟨g * z * g⁻¹, hmem⟩ = isoφ1 Mo.iso ⟨z', h'⟩ := by
    have e : (⟨g * z * g⁻¹, hmem⟩ : ↥(sec53G1 M L H B)) =
        ⟨g, hgG₁⟩ * ⟨z, h⟩ * (⟨g, hgG₁⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hgc]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcw
  exact congrArg Subtype.val ((isoφ1 Mo.iso).injective key)

theorem l3facts_four_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    ∀ z ∈ sec53ZS T L, z ≠ 1 → ∀ z' ∈ sec53ZS T L, z' ≠ 1 →
      ∃ g ∈ sec53M12 L H, g * z * g⁻¹ = z' := by
  intro z hz hz1 z' hz' hz1'
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  obtain ⟨g, hg, hgz⟩ := Mo.exists_inf_conj_F4 h527 hyp hz hz1 hz' hz1'
  exact ⟨g, inf_le_sec53M12 hyp hg, hgz⟩

theorem l3facts_five_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    ∀ z ∈ sec53ZS T L, z ≠ 1 →
      sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H ∧
        sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H := by
  intro z hz hz1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, ⟨hN, -, -⟩, hM1, hM2⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  have hZn : ∀ y ∈ sec53M12 L H, y * z * y⁻¹ ∈ sec53ZS T L := by
    intro y hy
    rw [← hN] at hy
    exact conj_mem_centerOf hy hz
  have hZne : ∀ y : G, y * z * y⁻¹ ≠ 1 := fun y h => hz1 (by
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this)
  have hNU : ∀ p ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)), p ∈ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ∧
        p ∈ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := fun p hp => by
    rw [← normalizer_inf_normalizer Mo.data] at hp
    exact Subgroup.mem_inf.mp hp
  obtain ⟨hzG₁, hw⟩ := Mo.mem_centerOf_U_F4 h527 hyp hz
  have hw1 := Mo.coe_iso_ne_one hzG₁ hz1
  have hzS : z ∈ sec53S T L := (inf_le_left : centerOf (sec53S T L) ≤ sec53S T L) hz
  have hzI : z ∈ sec53G1 M L H B ⊓ sec53G2 M L H D := sec53S_le_inf_F4 h527 hyp hzS
  have hzG₂ : z ∈ sec53G2 M L H D := (Subgroup.mem_inf.mp hzI).2
  have hw2 : ((isoφ2 Mo.iso ⟨z, hzG₂⟩ : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
      projectiveSL 3 F) ∈ centerOf (projUnitriangular 3 F) := by
    rw [← Mo.coe_iso_agree z hzG₁ hzG₂]
    exact hw
  have hw21 : ((isoφ2 Mo.iso ⟨z, hzG₂⟩ :
      ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) : projectiveSL 3 F) ≠ 1 := by
    rw [← Mo.coe_iso_agree z hzG₁ hzG₂]
    exact hw1
  have hM12M1 : sec53M12 L H ≤ Subgroup.normalizer (L : Set G) := inf_le_left
  have hM12M2 : sec53M12 L H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := inf_le_right
  constructor
  · intro m hm'
    obtain ⟨hm, hmc⟩ := Subgroup.mem_inf.mp hm'
    rw [← hM1] at hm
    obtain ⟨l, hl, k, hk, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hM12M1).mp hm
    have hlG₁ : l ∈ sec53G1 M L H B := (le_sup_left.trans le_sup_left : L ≤ _) hl
    obtain ⟨g, hgI, hgz⟩ := Mo.exists_inf_conj_F4 h527 hyp hz hz1 (hZn k hk) (hZne k)
    have hgG₁ := (Subgroup.mem_inf.mp hgI).1
    have hlg : l * g ∈ sec53G1 M L H B := (sec53G1 M L H B).mul_mem hlG₁ hgG₁
    have hcomm : (l * g) * z * (l * g)⁻¹ = z := by
      have h1 : (l * k) * z * (l * k)⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hmc
        rw [hmc]
        group
      calc (l * g) * z * (l * g)⁻¹ = l * (g * z * g⁻¹) * l⁻¹ := by group
        _ = l * (k * z * k⁻¹) * l⁻¹ := by rw [hgz]
        _ = (l * k) * z * (l * k)⁻¹ := by group
        _ = z := h1
    have hU := mem_normalizer_U_of_commute Mo.data (isoφ1 Mo.iso) hzG₁ hlg hw hw1 hcomm
    have hlgG₂ := Mo.mem_G2_of_mem_normalizer ⟨l * g, hlg⟩ (hNU _ hU).2
    have hlI : l ∈ sec53G1 M L H B ⊓ sec53G2 M L H D := by
      refine Subgroup.mem_inf.mpr ⟨hlG₁, ?_⟩
      have : l = (l * g) * g⁻¹ := by group
      rw [this]
      exact (sec53G2 M L H D).mul_mem hlgG₂ ((sec53G2 M L H D).inv_mem (Subgroup.mem_inf.mp hgI).2)
    exact (sec53M12 L H).mul_mem (inf_le_sec53M12 hyp hlI) hk
  · intro m hm'
    obtain ⟨hm, hmc⟩ := Subgroup.mem_inf.mp hm'
    rw [← hM2] at hm
    obtain ⟨l, hl, k, hk, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hM12M2).mp hm
    have hlG₂ : l ∈ sec53G2 M L H D := (le_sup_right : oTwoUpper H ≤ _) hl
    obtain ⟨g, hgI, hgz⟩ := Mo.exists_inf_conj_F4 h527 hyp hz hz1 (hZn k hk) (hZne k)
    have hgG₂ := (Subgroup.mem_inf.mp hgI).2
    have hlg : l * g ∈ sec53G2 M L H D := (sec53G2 M L H D).mul_mem hlG₂ hgG₂
    have hcomm : (l * g) * z * (l * g)⁻¹ = z := by
      have h1 : (l * k) * z * (l * k)⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hmc
        rw [hmc]
        group
      calc (l * g) * z * (l * g)⁻¹ = l * (g * z * g⁻¹) * l⁻¹ := by group
        _ = l * (k * z * k⁻¹) * l⁻¹ := by rw [hgz]
        _ = (l * k) * z * (l * k)⁻¹ := by group
        _ = z := h1
    have hU := mem_normalizer_U_of_commute Mo.data (isoφ2 Mo.iso) hzG₂ hlg hw2 hw21 hcomm
    have hlgG₁ := Mo.mem_G1_of_mem_normalizer ⟨l * g, hlg⟩ (hNU _ hU).1
    have hlI : l ∈ sec53G1 M L H B ⊓ sec53G2 M L H D := by
      refine Subgroup.mem_inf.mpr ⟨?_, hlG₂⟩
      have : l = (l * g) * g⁻¹ := by group
      rw [this]
      exact (sec53G1 M L H B).mul_mem hlgG₁ ((sec53G1 M L H B).inv_mem (Subgroup.mem_inf.mp hgI).1)
    exact (sec53M12 L H).mul_mem (inf_le_sec53M12 hyp hlI) hk

end CFSG.Quasithin.H13.Sec53L3
