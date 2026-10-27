module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open scoped commutatorElement

variable {Ω : Type} [Group Ω]

@[expose] def csIn (S D : Subgroup Ω) : Subgroup ↥S :=
  (S ⊓ Subgroup.centralizer (D : Set Ω)).subgroupOf S

theorem mem_csIn {S D : Subgroup Ω} {s : ↥S} :
    s ∈ csIn S D ↔ ∀ d ∈ D, d * (s : Ω) = (s : Ω) * d := by
  simp only [csIn, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

@[expose] def csImg (D : Subgroup Ω) : Subgroup G₀ := (csIn S D).map M.π

theorem mem_csImg {D : Subgroup Ω} {g : G₀} :
    g ∈ M.csImg D ↔ ∃ s : ↥S, s ∈ csIn S D ∧ M.π s = g := by
  simp only [csImg, Subgroup.mem_map]

theorem csImg_le_centralizer_img (D : Subgroup Ω) :
    M.csImg D ≤ Subgroup.centralizer (M.img D : Set G₀) := by
  intro g hg
  obtain ⟨s, hs, rfl⟩ := M.mem_csImg.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨b, hbD, rfl⟩ := M.mem_img.1 hh
  have hbs : M.conjHom b s = s := by
    apply Subtype.ext
    rw [coe_conjHom]
    have := mem_csIn.1 hs b hbD
    calc (b : Ω) * s * (b : Ω)⁻¹ = (s : Ω) * b * (b : Ω)⁻¹ := by rw [this]
      _ = s := by group
  have h1 := M.π_conjHom b s
  rw [hbs] at h1
  calc M.β b * M.π s = M.β b * M.π s * (M.β b)⁻¹ * M.β b := by group
    _ = M.π s * M.β b := by rw [← h1]

theorem conjHom_mul_inv_mem_center {D : Subgroup Ω} {s : ↥S}
    (hs : M.π s ∈ Subgroup.centralizer (M.img D : Set G₀)) {b : ↥B} (hb : (b : Ω) ∈ D) :
    M.conjHom b s * s⁻¹ ∈ Subgroup.center ↥S := by
  rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, M.π_conjHom b s]
  have h : M.β b * M.π s = M.π s * M.β b :=
    Subgroup.mem_centralizer_iff.1 hs (M.β b) (M.mem_img.2 ⟨b, hb, rfl⟩)
  rw [h]
  group

theorem commutator_mem_csIn {D : Subgroup Ω} (hDB : D ≤ B) {a c : ↥S}
    (ha : M.π a ∈ Subgroup.centralizer (M.img D : Set G₀))
    (hc : M.π c ∈ Subgroup.centralizer (M.img D : Set G₀)) : ⁅a, c⁆ ∈ csIn S D := by
  rw [mem_csIn]
  intro d hd
  have hza := M.conjHom_mul_inv_mem_center ha (b := ⟨d, hDB hd⟩) hd
  have hzc := M.conjHom_mul_inv_mem_center hc (b := ⟨d, hDB hd⟩) hd
  have hconj : M.conjHom ⟨d, hDB hd⟩ ⁅a, c⁆ = ⁅a, c⁆ := by
    rw [map_commutatorElement]
    obtain ⟨za, hza', ea⟩ : ∃ z ∈ Subgroup.center ↥S, M.conjHom ⟨d, hDB hd⟩ a = z * a :=
      ⟨_, hza, by group⟩
    obtain ⟨zc, hzc', ec⟩ : ∃ z ∈ Subgroup.center ↥S, M.conjHom ⟨d, hDB hd⟩ c = z * c :=
      ⟨_, hzc, by group⟩
    rw [ea, ec, CFSG.LocalAnalysis.GLTheoremA.I142N.comm_central_mul_left hza',
      CFSG.LocalAnalysis.GLTheoremA.I142N.comm_central_mul_right hzc']
  have h2 := congrArg Subtype.val hconj
  rw [coe_conjHom] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem conj_mem_csIn {D : Subgroup Ω} (hDB : D ≤ B) {a x : ↥S}
    (ha : M.π a ∈ Subgroup.centralizer (M.img D : Set G₀)) (hx : x ∈ csIn S D) :
    a * x * a⁻¹ ∈ csIn S D := by
  have hxC : M.π x ∈ Subgroup.centralizer (M.img D : Set G₀) :=
    M.csImg_le_centralizer_img D (M.mem_csImg.2 ⟨x, hx, rfl⟩)
  have hcomm := M.commutator_mem_csIn hDB ha hxC
  have e : a * x * a⁻¹ = ⁅a, x⁆ * x := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ hcomm hx

theorem csImg_normal {D : Subgroup Ω} (hDB : D ≤ B) :
    ((M.csImg D).subgroupOf (Subgroup.centralizer (M.img D : Set G₀))).Normal := by
  refine ⟨fun y hy g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  obtain ⟨x, hx, hxy⟩ := M.mem_csImg.1 hy
  obtain ⟨a, ha⟩ := M.surj (g : G₀)
  have haC : M.π a ∈ Subgroup.centralizer (M.img D : Set G₀) := by
    rw [ha]
    exact g.2
  refine M.mem_csImg.2 ⟨a * x * a⁻¹, M.conj_mem_csIn hDB haC hx, ?_⟩
  rw [map_mul, map_mul, map_inv, ha, hxy]
  rfl

theorem commutator_centralizer_img_le {D : Subgroup Ω} (hDB : D ≤ B) :
    ⁅Subgroup.centralizer (M.img D : Set G₀), Subgroup.centralizer (M.img D : Set G₀)⁆ ≤
      M.csImg D := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨a, rfl⟩ := M.surj g
  obtain ⟨c, rfl⟩ := M.surj h
  rw [← map_commutatorElement]
  exact M.mem_csImg.2 ⟨⁅a, c⁆, M.commutator_mem_csIn hDB hg hh, rfl⟩

end S172Model

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
