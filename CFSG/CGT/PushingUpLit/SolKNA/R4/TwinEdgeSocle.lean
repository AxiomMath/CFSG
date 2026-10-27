module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Assembly.Subnormal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open

section Socle

variable {G : Type} [Group G] [Finite G]

abbrev socleOf (L₀ : Subgroup G) : Subgroup (G ⧸ Subgroup.center G) :=
  L₀.map (QuotientGroup.mk' (Subgroup.center G))

instance socleOf_normal {L₀ : Subgroup G} [L₀.Normal] : (socleOf L₀).Normal :=
  Subgroup.Normal.map ‹L₀.Normal› _ (QuotientGroup.mk'_surjective _)

theorem ker_domRestrict_socle {L₀ : Subgroup G}
    (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G) :
    ((QuotientGroup.mk' (Subgroup.center G)).domRestrict L₀).ker = Subgroup.center ↥L₀ := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx y.1)
  · intro hx
    have : (x : G) ∈ Subgroup.centralizer (L₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
    rwa [hC] at this

theorem nonempty_socle_equiv {L₀ : Subgroup G}
    (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G) :
    Nonempty (↥(socleOf L₀) ≃* ↥L₀ ⧸ Subgroup.center ↥L₀) :=
  ⟨(((QuotientGroup.quotientMulEquivOfEq (ker_domRestrict_socle hC)).symm.trans
    (QuotientGroup.quotientKerEquivRange _)).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))).symm⟩

theorem isSimpleGroup_socle {L₀ : Subgroup G} (hQ : CFSG.IsQuasisimple ↥L₀)
    (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G) :
    IsSimpleGroup ↥(socleOf L₀) := by
  obtain ⟨e⟩ := nonempty_socle_equiv hC
  have := hQ.2.1
  exact e.isSimpleGroup

theorem exists_ne_comm_socle {L₀ : Subgroup G} (hQ : CFSG.IsQuasisimple ↥L₀)
    (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G) :
    ∃ a b : ↥(socleOf L₀), a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_socle_equiv hC
  obtain ⟨a, b, hab⟩ := hQ.2.2
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem centralizer_socle_eq_bot {L₀ : Subgroup G} (hQ : CFSG.IsQuasisimple ↥L₀)
    (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G) :
    Subgroup.centralizer ((socleOf L₀ : Subgroup (G ⧸ Subgroup.center G)) :
      Set (G ⧸ Subgroup.center G)) = ⊥ := by
  rw [eq_bot_iff]
  intro ybar hy
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) ybar
  have hcen : ∀ ℓ : ↥L₀, y * ℓ * y⁻¹ * (ℓ : G)⁻¹ ∈ Subgroup.center G := by
    intro ℓ
    have h1 := Subgroup.mem_centralizer_iff.mp hy (QuotientGroup.mk' (Subgroup.center G) ℓ)
      (Subgroup.mem_map_of_mem _ ℓ.2)
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h1]
    group
  let ψ : ↥L₀ →* ↥(Subgroup.center G) :=
    { toFun := fun ℓ => ⟨y * ℓ * y⁻¹ * (ℓ : G)⁻¹, hcen ℓ⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.mp (hcen b) ((a : G)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc y * ((a : G) * b) * y⁻¹ * ((b : G)⁻¹ * (a : G)⁻¹)
            = y * a * y⁻¹ * ((y * b * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = y * a * y⁻¹ * ((a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹)) := by rw [hb]
          _ = y * a * y⁻¹ * (a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹) := by group }
  have hker : commutator ↥L₀ ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hp : commutator ↥L₀ = ⊤ := hQ.1.commutator_eq_top
  rw [hp] at hker
  have hyC : y ∈ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have h1 : ψ ⟨ℓ, hℓ⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
    have h2 : y * ℓ * y⁻¹ * ℓ⁻¹ = 1 := congrArg Subtype.val h1
    calc ℓ * y = (y * ℓ * y⁻¹ * ℓ⁻¹)⁻¹ * (y * ℓ) := by group
      _ = y * ℓ := by rw [h2, inv_one, one_mul]
  rw [hC] at hyC
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hyC

end Socle

section SubnormalComponent

variable {G : Type} [Group G]

theorem eq_top_or_le_center_of_isSubnormal' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {P : Subgroup Q} (hP : P.IsSubnormal) : P = ⊤ ∨ P ≤ Subgroup.center Q := by
  induction hP with
  | top => exact Or.inl rfl
  | step H K hHK _ hN ih =>
    rcases ih with rfl | hK
    · have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN))
      exact CFSG.LocalCores.quasisimple_normal_subgroups hQ hHn
    · exact Or.inr (hHK.trans hK)

theorem le_of_mem_isSubnormal {L₀ W : Subgroup G} (hL : CFSG.IsQuasisimple ↥L₀)
    (hW : IsSubnormal W ⊤) {z : G} (hzL : z ∈ L₀) (hzW : z ∈ W)
    (hz : (⟨z, hzL⟩ : ↥L₀) ∉ Subgroup.center ↥L₀) : L₀ ≤ W := by
  have h1 : IsSubnormal (W ⊓ L₀) L₀ := hW.inf_of_le le_top
  rcases eq_top_or_le_center_of_isSubnormal' hL h1.subgroupOf with h | h
  · intro x hx
    have : (⟨x, hx⟩ : ↥L₀) ∈ (W ⊓ L₀).subgroupOf L₀ := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp this).1
  · exact absurd (h (show (⟨z, hzL⟩ : ↥L₀) ∈ (W ⊓ L₀).subgroupOf L₀ from
      Subgroup.mem_inf.mpr ⟨hzW, hzL⟩)) hz

end SubnormalComponent

end CFSG.CGT.PushingUpLit.SolKNA.R4
