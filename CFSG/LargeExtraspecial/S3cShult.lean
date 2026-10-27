module

public import CFSG.LargeExtraspecial.S3cFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)
open TauCeti.QuadraticMap (orthogonalGroup)

universe u

section Generic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem apply_eq_of_commute_of_isTypeC {x m : V ≃ₗ[ZMod 2] V} (hx : IsTypeC q x 2)
    (hm : m ∈ orthogonalGroup q) (hxm : m * x = x * m) {a : V} (ha : a ∈ commSpace x)
    (ha0 : a ≠ 0) (haq : q a = 0) : m a = a := by
  obtain ⟨w, ⟨hw, hw0, hwq⟩, huniq⟩ := existsUnique_singular_of_isTypeC hx
  have hma : m a ∈ commSpace x := by
    obtain ⟨v, rfl⟩ := mem_commSpace.mp ha
    refine mem_commSpace.mpr ⟨m v, ?_⟩
    rw [map_sub, ← LinearEquiv.mul_apply, ← hxm, LinearEquiv.mul_apply]
  have hm0 : m a ≠ 0 := fun h => ha0 (by simpa using congrArg m.symm h)
  have hmq : q (m a) = 0 := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hm a, haq]
  rw [huniq _ ⟨hma, hm0, hmq⟩, huniq _ ⟨ha, ha0, haq⟩]

theorem finrank_le_of_totallySingular (hq : q.polarBilin.Nondegenerate) {n : ℕ}
    (hV : finrank (ZMod 2) V = 2 * n) {X : Submodule (ZMod 2) V} (hX : ∀ x ∈ X, q x = 0) :
    finrank (ZMod 2) X ≤ n := by
  have hle : X ≤ LinearMap.BilinForm.orthogonal q.polarBilin X := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [polarBilin_apply_apply, polar, hX _ (X.add_mem hy hx), hX _ hy, hX _ hx]
    simp
  have h1 := LinearMap.BilinForm.finrank_orthogonal hq X
  have h2 := Submodule.finrank_mono hle
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem conj_mem_pointRadical {m t : V ≃ₗ[ZMod 2] V} (hm : m ∈ orthogonalGroup q) {a : V}
    (ht : t ∈ pointRadical q a) : m * t * m⁻¹ ∈ pointRadical q (m a) :=
  mem_pointRadical_of_intertwine m (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hm)
    (fun v => by simp [LinearEquiv.mul_apply]) ht

end Generic

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem isTypeC_of_mem_Lbar_pointRadical {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {s : S.O} (hs : s ∈ S.Lbar g)
    (hs1 : s ≠ 1) (hsN : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))) :
    IsTypeC S.q (s : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      S.cl (g * S.z * g⁻¹) ∈ commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      ∃ u, polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 ∧ u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ∧
        (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = eichler S.q (S.cl (g * S.z * g⁻¹)) u := by
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  obtain ⟨u, hau, hsu⟩ := (mem_pointRadical_iff S.q_nondegenerate ha0 haq).mp hsN
  have hs1' : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hu : u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro hu
    apply hs1'
    rw [hsu, (eichler_eq_one_iff S.q_nondegenerate ha0 haq hau).mpr hu]
  have htypes := eichler_type_of_not_mem_span S.q_nondegenerate ha0 haq hau hu
  have hq1 := S.q_eq_one_of_mem_LbarLin_of_eq_eichler haQ hne hno (S.coe_mem_LbarLin hs) hs1'
    hau hsu
  refine ⟨hsu ▸ htypes.2.2 hq1, ?_, u, hau, hu, hsu⟩
  rw [hsu, htypes.1]
  exact Submodule.subset_span (Set.mem_insert _ _)

theorem fixes_of_commute_mem_pointRadical {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {s : S.O} (hs : s ∈ S.Lbar g)
    (hs1 : s ≠ 1) (hsN : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    {m : S.O} (hms : m * s = s * m) :
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  obtain ⟨hC, ha, -⟩ := S.isTypeC_of_mem_Lbar_pointRadical haQ hne hno hs hs1 hsN
  exact apply_eq_of_commute_of_isTypeC hC m.2 (congrArg Subtype.val hms) ha
    (S.cl_conj_z_ne_zero haQ hne) (S.q_cl_conj_z haQ)

theorem Lbar_mul_eq_of_fix {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hh : h ∈ S.M)
    (hfix : (S.ρ ⟨h, hh⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    S.Lbar (h * g) = S.Lbar g := by
  rw [S.ρ_cl _ haQ] at hfix
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG hh haQ)).mp hfix.symm with h1 | h1
  · exact S.Lbar_eq_of_conj_eq (by rw [← h1]; group)
  · exact S.Lbar_eq_of_conj_eq_mul_z haQ hne (by rw [← h1]; group)

theorem mem_Qa_of_fix (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g h : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) (hh : h ∈ S.M) {s : S.O} (hs : s ∈ S.Lbar g) (hs1 : s ≠ 1)
    (hsN : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hsb : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹)) :
    (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g := by
  by_contra hbQa
  obtain ⟨hC, ha, -⟩ := S.isTypeC_of_mem_Lbar_pointRadical haQ hne hno hs hs1 hsN
  obtain ⟨y, -, rfl⟩ := S.mem_Lbar_iff.mp hs
  obtain ⟨-, -, -, hX, hXdim⟩ := S.lemma_3_10_iii haQ hne hh hbQa y.2 hC ha hsb
  have hcard := ((S.lemma_3_11_two hTI hn haQ hne hno).resolve_left hirr).2.1
  have hWb := S.finrank_clSub_QG_inf_Qa (S.conj_mul_mem_QG hh haQ) (S.conj_mul_ne_z hh hne)
    (by rw [S.card_QG_inf_Qa_mul hh]; exact hcard)
  have := finrank_le_of_totallySingular S.q_nondegenerate S.finrank_Qt_eq_two_mul_width hX
  omega

end Setting

end CFSG.LargeExtraspecial
