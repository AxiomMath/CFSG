module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HOutDiagLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem hod_central_hom_trivial {H : Type} [Group H] (hH : commutator H = ⊤) (c : H → H)
    (hc : ∀ y, c y ∈ Subgroup.center H) (hmul : ∀ y z, c (y * z) = c y * c z) (y : H) :
    c y = 1 := by
  have h1 : c 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h' : c 1 * 1 = c 1 * c 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have hinv : ∀ y, c y⁻¹ = (c y)⁻¹ := by
    intro y
    have h := hmul y y⁻¹
    rw [mul_inv_cancel, h1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let T : Subgroup H :=
    { carrier := {y | c y = 1}
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = 1
        rw [hmul, show c a = 1 from ha, show c b = 1 from hb, one_mul]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = 1
        rw [hinv, show c a = 1 from ha, inv_one] }
  have hcomm : ∀ x z : H, ⁅x, z⁆ ∈ T := by
    intro x z
    show c ⁅x, z⁆ = 1
    have hxz : c x * c z = c z * c x := (Subgroup.mem_center_iff.1 (hc x) (c z)).symm
    rw [commutatorElement_def, hmul, hmul, hmul, hinv, hinv, hxz]
    group
  have htop : (⊤ : Subgroup H) ≤ T := by
    have h2 : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ T :=
      Subgroup.commutator_le.2 (fun g _ h _ => hcomm g h)
    rw [← hH]
    exact h2
  exact htop (Subgroup.mem_top y)

theorem hod_inducesInner {G : Type} [Group G] (L : Subgroup G) (b : G)
    (hL : commutator ↥L = ⊤) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (φ : MulAut R)
    (hφ : φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    InducesInnerMod 3 L b := by
  obtain ⟨r, hr⟩ := hφ
  obtain ⟨l₁, hl₁⟩ := QuotientGroup.mk_surjective (θ.symm r)
  have hθl : θ (QuotientGroup.mk l₁) = r := by
    rw [hl₁]
    exact θ.apply_symm_apply r
  have hαmem : ∀ y : ↥L, b⁻¹ * (y : G) * b ∈ L := fun y =>
    (Subgroup.mem_normalizer_iff.1 hbN (b⁻¹ * (y : G) * b)).mpr
      (by rw [show b * (b⁻¹ * (y : G) * b) * b⁻¹ = (y : G) by group]; exact y.2)
  let α : ↥L → ↥L := fun y => ⟨b⁻¹ * (y : G) * b, hαmem y⟩
  let β : ↥L → ↥L := fun y => l₁ * y * l₁⁻¹
  let ψ : ↥L →* R := (θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : ∀ x : ↥L, ψ x = θ (QuotientGroup.mk x) := fun x => rfl
  have hψl : ψ l₁ = r := by rw [hψ]; exact hθl
  have hkey : ∀ y : ↥L, ψ (α y) = ψ (β y) := by
    intro y
    have h1 : φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y)) := hind y (α y) rfl
    have h2 : φ (θ (QuotientGroup.mk y)) = r * ψ y * r⁻¹ := by
      rw [← hr, MulAut.conj_apply]
      try rfl
    have h3 : ψ (β y) = r * ψ y * r⁻¹ := by
      simp only [β, map_mul, map_inv, hψl]
    calc ψ (α y) = θ (QuotientGroup.mk (α y)) := hψ _
      _ = φ (θ (QuotientGroup.mk y)) := h1.symm
      _ = r * ψ y * r⁻¹ := h2
      _ = ψ (β y) := h3.symm
  have hc : ∀ y : ↥L, (β y)⁻¹ * α y ∈ Subgroup.center ↥L := by
    intro y
    have hmk : (QuotientGroup.mk (β y) : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk (α y) := by
      apply θ.injective
      exact (hkey y).symm
    exact QuotientGroup.eq.1 hmk
  have hβmul : ∀ y z : ↥L, β (y * z) = β y * β z := by
    intro y z
    show l₁ * (y * z) * l₁⁻¹ = (l₁ * y * l₁⁻¹) * (l₁ * z * l₁⁻¹)
    group
  have hαmul : ∀ y z : ↥L, α (y * z) = α y * α z := by
    intro y z
    apply Subtype.ext
    simp only [α, Subgroup.coe_mul]
    group
  have hmul : ∀ y z : ↥L, (β (y * z))⁻¹ * α (y * z) = ((β y)⁻¹ * α y) * ((β z)⁻¹ * α z) := by
    intro y z
    have hcu := Subgroup.mem_center_iff.1 (hc y) ((β z)⁻¹)
    rw [hβmul, hαmul, mul_inv_rev]
    calc (β z)⁻¹ * (β y)⁻¹ * (α y * α z) = (β z)⁻¹ * ((β y)⁻¹ * α y) * α z := by group
      _ = ((β y)⁻¹ * α y) * (β z)⁻¹ * α z := by rw [hcu]
      _ = ((β y)⁻¹ * α y) * ((β z)⁻¹ * α z) := by group
  have hcy1 : ∀ y : ↥L, (β y)⁻¹ * α y = 1 :=
    fun y => hod_central_hom_trivial hL (fun y => (β y)⁻¹ * α y) hc hmul y
  refine ⟨(l₁ : G)⁻¹, L.inv_mem l₁.2, fun y hy => ?_⟩
  have e1 : (((β ⟨y, hy⟩)⁻¹ * α ⟨y, hy⟩ : ↥L) : G) = 1 := by
    rw [hcy1 ⟨y, hy⟩]
    rfl
  have e2 : (((β ⟨y, hy⟩)⁻¹ * α ⟨y, hy⟩ : ↥L) : G) =
      (((l₁ : G)⁻¹)⁻¹ * y * (l₁ : G)⁻¹)⁻¹ * (b⁻¹ * y * b) := by
    simp only [β, α, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, inv_inv]
    try group
  have e3 : (((l₁ : G)⁻¹)⁻¹ * y * (l₁ : G)⁻¹)⁻¹ * (b⁻¹ * y * b) = 1 := e2 ▸ e1
  rw [e3]
  exact Subgroup.one_mem _

section Cert


theorem I171OutDiagFact_holds : I171OutDiagFact := by
  intro G _ _ L b hL hcat hB
  unfold InnerDiagMarking at hB
  obtain ⟨hcomm, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hB
  have hMX : CFSG.StandardType.MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
    obtain ⟨R, inst, I, F, -, -, θ, -, hm⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    exact CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm
  have hcase : lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.D, 4, 1⟩ := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    rcases hi with hi | hi
    · left
      obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU5two
        (⟨i, hi, ⟨e⟩⟩ : CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥L ⧸ Subgroup.center ↥L)
          CFSG.LocalAnalysis.GLTheoremA.S9.isU5two)
      obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
        (s := 1) (by norm_num) (hq.trans (by norm_num))
      have hm := CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' 4 q hv e'
      rw [h1, h2] at hm
      exact hod_lab_u5 (hm.toBlueprint (by decide)) hMX
    · right
      obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two
        (⟨i, hi, ⟨e⟩⟩ : CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥L ⧸ Subgroup.center ↥L)
          CFSG.LocalAnalysis.GLTheoremA.S9.isD4two)
      obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
        (s := 1) (by norm_num) (hq.trans (by norm_num))
      have hm := CFSG.Models.lieModel_D 4 q hv e'
      rw [h1, h2] at hm
      exact hod_lab_d4 (hm.toBlueprint (by decide)) hMX
  rcases hcase with rfl | rfl
  · obtain ⟨R, inst, I, F, ⟨-, -, θ, hP, -⟩, hI⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists (hod_rk2_twA41 _ hraw)
    obtain ⟨φ, hφI, hind⟩ := hP.2 b (Subgroup.mem_zpowers b)
    exact hod_inducesInner L b hcomm (hP.1 (Subgroup.mem_zpowers b)) θ φ (hI hφI) hind
  · obtain ⟨R, inst, I, F, ⟨-, -, θ, hP, -⟩, hI⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists
        (CFSG.LocalAnalysis.GLTheoremA.rk2_inndiag_subset_inn_of_notDerived hlab
          (by decide) (by decide) (by decide) (by decide) _ hraw)
    obtain ⟨φ, hφI, hind⟩ := hP.2 b (Subgroup.mem_zpowers b)
    exact hod_inducesInner L b hcomm (hP.1 (Subgroup.mem_zpowers b)) θ φ (hI hφI) hind

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S171

end
