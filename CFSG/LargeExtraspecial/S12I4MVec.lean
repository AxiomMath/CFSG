module

public import CFSG.LargeExtraspecial.S3bTenB
public import CFSG.LargeExtraspecial.S12I4MGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12I4M

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial (Setting IsTypeA)

theorem finrank_sup_span_singleton {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V} {x : V} (hx : x ∉ U) :
    finrank (ZMod 2) (U ⊔ (ZMod 2 ∙ x) : Submodule (ZMod 2) V) = finrank (ZMod 2) U + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ U.zero_mem)
  have hinf : U ⊓ (ZMod 2 ∙ x) = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyU, hyx⟩
    rcases mem_span_singleton_iff.mp hyx with h | h
    · exact h
    · exact absurd (h ▸ hyU) hx
  have e := Submodule.finrank_sup_add_finrank_inf_eq U (ZMod 2 ∙ x)
  rw [hinf, finrank_bot, finrank_span_singleton hx0] at e
  omega

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem sub_mem_clSub_of_polar (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {s : S.O} (hs : s ∈ S.Lbar g) {w : S.Qt} (hw : polar S.q w (S.cl (g * S.z * g⁻¹)) = 0) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨v, hvQ, rfl⟩ := S.exists_cl w
  exact S.sub_mem_clSub_of_mem_Lbar haQ hne hs hvQ ((S.polar_cl_eq_zero_iff hvQ haQ).mp hw)

theorem false_of_le_clSub (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hw : S.width = 4) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hle : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.clSub (S.QG ⊓ S.Qa g))
    (h4 : 4 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))) : False := by
  set E := S.QG ⊓ S.Qa g with hE
  set Et := S.clSub E with hEt
  have hiso : ∀ v ∈ Et, ∀ w ∈ Et, polar S.q v w = 0 := by
    intro v hv w hw'
    obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw'
    exact (S.polar_cl_eq_zero_iff hxQ hyQ).mpr (S.QG_inf_Qa_comm hne hx hy)
  have hfix : ∀ v ∈ Et, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    apply_eq_of_polar S.q_nondegenerate htA fun x hx => hiso v hv x (hle hx)
  obtain ⟨y, hyL, rfl⟩ := S.mem_Lbar_iff.mp ht
  have hyC : (y : G) ∈ S.CQa g := S.mem_CQa_of_fix hne hyL fun w hw =>
    hfix _ (S.cl_mem_clSub hw hw.1)
  have hyA : S.ρ y ∈ S.Abar g := S.mem_Abar_iff.mpr ⟨y, hyC, rfl⟩
  have hzE : S.z ∈ E := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  have hcardE : Nat.card E = 2 * 2 ^ finrank (ZMod 2) Et := by
    rw [← S.card_submodule, ← S.card_clPre, S.clPre_clSub inf_le_left hzE]
  have h32 : 32 ≤ Nat.card E := by
    rw [hcardE]
    have : 2 ^ 4 ≤ 2 ^ finrank (ZMod 2) Et := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have h1 := S.card_CQa_mul haQ
  have h2 := S.card_Abar_mul haQ hne
  rw [← hE] at h1 h2
  rw [hw, ← h2] at h1
  have hA1 : Nat.card (S.Abar g) ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 * 32 * 32 ≤ Nat.card (S.Abar g) * Nat.card E * Nat.card E :=
      Nat.mul_le_mul (Nat.mul_le_mul hc h32) h32
    norm_num at h1
    omega
  rw [(Subgroup.card_le_one_iff_eq_bot _).mp hA1, Subgroup.mem_bot] at hyA
  exact htA.2.1 (by rw [hyA]; rfl)

theorem le_clSub_and_four_le (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hat : S.cl (g * S.z * g⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    {E₄ E₅ h : S.O} (h4 : IsTypeA S.q (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (h5 : IsTypeA S.q (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hρ : E₄ * E₅ ∈ S.Lbar g) (hρ' : h * (E₄ * E₅) * h⁻¹ ∈ S.Lbar g)
    (hh : (h : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hd45 : commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (ho45 : ∀ x ∈ commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      ∀ y ∈ commSpace (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt), polar S.q x y = 0)
    (hd4 : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hd5 : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hle : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hopp : commSpace ((h * E₄ * h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
        ⊥) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.clSub (S.QG ⊓ S.Qa g) ∧
      4 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := by
  set ã := S.cl (g * S.z * g⁻¹) with hã
  set ℓ := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hℓ
  set ℓ₄ := commSpace (E₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hℓ₄
  set ℓ₅ := commSpace (E₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hℓ₅
  set Et := S.clSub (S.QG ⊓ S.Qa g) with hEt
  have hq := S.q_nondegenerate
  have hã0 : ã ≠ 0 := fun e => by
    rcases (S.cl_eq_zero_iff haQ).mp e with h1 | h1
    · exact (S.conjBy g).z_ne_one h1
    · exact hne h1
  have hℓ2 : finrank (ZMod 2) ℓ = 2 := htA.2.2.2.1
  have hlt : (ZMod 2 ∙ ã) < ℓ := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hat) fun e => ?_
    have := finrank_span_singleton_le ã
    rw [e, hℓ2] at this
    omega
  obtain ⟨b, hbℓ, hb⟩ := IsConcreteLE.exists_of_lt hlt
  have hb0 : b ≠ 0 := fun e => hb (e ▸ Submodule.zero_mem _)
  have hba : b ≠ ã := fun e => hb (by rw [e]; exact Submodule.mem_span_singleton_self ã)
  have hspan : Submodule.span (ZMod 2) {ã, b} = ℓ :=
    span_pair_eq hℓ2 hat hbℓ hã0 hb0 (Ne.symm hba)
  obtain ⟨a₄, ha₄, a₅, ha₅, hae⟩ := Submodule.mem_sup.mp (hle hat)
  obtain ⟨c₄, hc₄, c₅, hc₅, hce⟩ := Submodule.mem_sup.mp (hle hbℓ)
  have hnot4 : ∀ x ∈ ℓ, x ∈ ℓ₄ → x = 0 := fun x hx hx4 => by
    have : x ∈ ℓ ⊓ ℓ₄ := ⟨hx, hx4⟩
    rwa [hd4, Submodule.mem_bot] at this
  have hnot5 : ∀ x ∈ ℓ, x ∈ ℓ₅ → x = 0 := fun x hx hx5 => by
    have : x ∈ ℓ ⊓ ℓ₅ := ⟨hx, hx5⟩
    rwa [hd5, Submodule.mem_bot] at this
  have ha₄0 : a₄ ≠ 0 := fun e => hã0 (hnot5 ã hat (by rw [← hae, e, zero_add]; exact ha₅))
  have ha₅0 : a₅ ≠ 0 := fun e => hã0 (hnot4 ã hat (by rw [← hae, e, add_zero]; exact ha₄))
  have hc₄0 : c₄ ≠ 0 := fun e => hb0 (hnot5 b hbℓ (by rw [← hce, e, zero_add]; exact hc₅))
  have hc₅0 : c₅ ≠ 0 := fun e => hb0 (hnot4 b hbℓ (by rw [← hce, e, add_zero]; exact hc₄))
  have hab0 : ã + b ≠ 0 := fun e => hba (by
    calc b = ã + b + ã := by rw [add_comm ã b, add_assoc, vec_add_self, add_zero]
      _ = ã := by rw [e, zero_add])
  have hac₄ : a₄ ≠ c₄ := fun e => hab0 (hnot5 _ (ℓ.add_mem hat hbℓ) (by
    rw [← hae, ← hce, e, show c₄ + a₅ + (c₄ + c₅) = (c₄ + c₄) + (a₅ + c₅) by abel, vec_add_self,
      zero_add]
    exact ℓ₅.add_mem ha₅ hc₅))
  have hac₅ : a₅ ≠ c₅ := fun e => hab0 (hnot4 _ (ℓ.add_mem hat hbℓ) (by
    rw [← hae, ← hce, e, show a₄ + c₅ + (c₄ + c₅) = (a₄ + c₄) + (c₅ + c₅) by abel, vec_add_self,
      add_zero]
    exact ℓ₄.add_mem ha₄ hc₄))
  obtain ⟨v₁, hv₁, hv₁e⟩ := exists_sub_eq_add hq h4 h5 hd45 ho45 ha₄ hc₄ ha₅ hc₅ ha₄0 hc₄0
    ha₅0 hc₅0 hac₄ hac₅
  rw [hae] at hv₁
  rw [hce] at hv₁e
  obtain ⟨v₂, hv₂, hv₂e⟩ := exists_sub_eq_left hq h4 h5 hd45 ha₄ hc₄ ha₅ ha₄0 hc₄0 hac₄
  rw [hae] at hv₂
  have hbE : b ∈ Et := by
    have := sub_mem_clSub_of_polar haQ hne hρ hv₁
    rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, hv₁e] at this
  have ha₄E : a₄ ∈ Et := by
    have := sub_mem_clSub_of_polar haQ hne hρ hv₂
    rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, hv₂e] at this
  have hinvh : ∀ x, ((h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((h : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = x :=
    fun x => by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
  have hhv : polar S.q ((h : S.Qt ≃ₗ[ZMod 2] S.Qt) v₂) ã = 0 := by
    rw [← hh, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup h.2]
    exact hv₂
  have hha₄E : (h : S.Qt ≃ₗ[ZMod 2] S.Qt) a₄ ∈ Et := by
    have := sub_mem_clSub_of_polar haQ hne hρ' hhv
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hinvh, Subgroup.coe_mul, LinearEquiv.mul_apply, ← map_sub, hv₂e] at this
  have hãE : ã ∈ Et := S.cl_mem_clSub ⟨haQ, (S.conjBy g).z_mem_QG⟩ haQ
  have hℓE : ℓ ≤ Et := by
    rw [← hspan, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hãE
    · exact hbE
  have ha₄ℓ : a₄ ∉ ℓ := fun e => ha₄0 (hnot4 a₄ e ha₄)
  have hU3 := finrank_sup_span_singleton ha₄ℓ
  have hU3le : ℓ ⊔ (ZMod 2 ∙ a₄) ≤ ℓ₄ ⊔ ℓ₅ :=
    sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_sup_left ha₄))
  have hconj : ∀ x ∈ ℓ₄, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈
      commSpace ((h * E₄ * h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro x hx
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hx
    have := sub_mem_commSpace ((h * E₄ * h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((h : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hinvh, ← map_sub] at this
  have horth : ∀ x ∈ ℓ₄ ⊔ ℓ₅, x ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin ℓ₄ := by
    intro x hx
    obtain ⟨x₄, hx₄, x₅, hx₅, rfl⟩ := Submodule.mem_sup.mp hx
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_
    rw [polarBilin_apply_apply, polar_add_right, polar_eq_zero_of_isTypeA h4 hu hx₄,
      ho45 u hu x₅ hx₅, add_zero]
  have hha₄ : (h : S.Qt ≃ₗ[ZMod 2] S.Qt) a₄ ∉ ℓ ⊔ (ZMod 2 ∙ a₄) := by
    intro hmem
    have hbot : (h : S.Qt ≃ₗ[ZMod 2] S.Qt) a₄ ∈
        commSpace ((h * E₄ * h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
          LinearMap.BilinForm.orthogonal S.q.polarBilin ℓ₄ :=
      ⟨hconj a₄ ha₄, horth _ (hU3le hmem)⟩
    rw [hopp, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at hbot
    exact ha₄0 hbot
  have hU4 := finrank_sup_span_singleton hha₄
  have hU4le : ℓ ⊔ (ZMod 2 ∙ a₄) ⊔ (ZMod 2 ∙ (h : S.Qt ≃ₗ[ZMod 2] S.Qt) a₄) ≤ Et :=
    sup_le (sup_le hℓE ((Submodule.span_singleton_le_iff_mem _ _).mpr ha₄E))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hha₄E)
  refine ⟨hℓE, ?_⟩
  have := Submodule.finrank_mono hU4le
  omega

end CFSG.LargeExtraspecial.S12I4M
