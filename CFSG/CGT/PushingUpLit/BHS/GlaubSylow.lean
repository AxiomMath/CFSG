module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.BHS.Glauberman

open CFSG.RankThree.PartOne

variable {Γ : Type*} [Group Γ]

theorem exists_isSylowOf_ge [Finite Γ] {K Q : Subgroup Γ} (hQ : IsPGroup 2 Q) (hQK : Q ≤ K) :
    ∃ S : Subgroup Γ, IsSylowOf 2 S K ∧ Q ≤ S := by
  obtain ⟨S₀, hS₀⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S₀ : Subgroup K).map K.subtype, ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, ?_⟩,
    fun x hx => ⟨⟨x, hQK hx⟩, hS₀ (show (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K from hx), rfl⟩⟩
  have h : ((S₀ : Subgroup K).map K.subtype).subgroupOf K = (S₀ : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have := S₀.not_dvd_index
  rwa [← h] at this

theorem le_of_isSylowOf_of_le [Finite Γ] {T N R : Subgroup Γ} (hT : IsSylowOf 2 T N)
    (hR : IsPGroup 2 R) (hTR : T ≤ R) (hRN : R ≤ N) : R ≤ T := by
  obtain ⟨k, hk⟩ := hR.index (T.subgroupOf R)
  have hk' : T.relIndex R = 2 ^ k := hk
  have h1 := Subgroup.relIndex_mul_relIndex T R N hTR hRN
  by_contra hRT
  have hne : T.relIndex R ≠ 1 := fun h => hRT (Subgroup.relIndex_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by rw [hk', pow_zero])
  exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left (hk' ▸ dvd_pow_self 2 hk0) _)

theorem exists_conj_le_of_isSylowOf [Finite Γ] {K T R : Subgroup Γ} (hT : IsSylowOf 2 T K)
    (hR : IsPGroup 2 R) (hRK : R ≤ K) :
    ∃ k ∈ K, R.map (MulAut.conj k).toMonoidHom ≤ T := by
  have hTp : IsPGroup 2 (T.subgroupOf K) := hT.2.1.comap_subtype (K := K)
  have hRp : IsPGroup 2 (R.subgroupOf K) := hR.comap_subtype (K := K)
  obtain ⟨S, hS⟩ := hRp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥K (hTp.toSylow hT.2.2) S
  refine ⟨(h : Γ)⁻¹, (h⁻¹).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (⟨x, hRK hx⟩ : K) ∈ (S : Subgroup K) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hxS2 : ((MulAut.conj h)⁻¹ • (⟨x, hRK hx⟩ : K)) ∈ T.subgroupOf K := hxS
  have hmem : (h⁻¹ * ⟨x, hRK hx⟩ * h : K) ∈ T.subgroupOf K := by
    simpa [MulAut.inv_def, MulAut.conj_symm_apply] using hxS2
  have hmem' := Subgroup.mem_subgroupOf.mp hmem
  simpa [MulAut.conj_apply] using hmem'

theorem exists_mem_normalizer_mul [Finite Γ] {K D T : Subgroup Γ}
    (hKD : K ≤ Subgroup.normalizer (D : Set Γ)) (hTK : T ≤ K) (hTp : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.relIndex K) {g : Γ} (hg : g ∈ K) :
    ∃ x ∈ Subgroup.normalizer ((T ⊓ D : Subgroup Γ) : Set Γ), x ∈ K ∧ ∃ y ∈ D, g = x * y := by
  have hD : (D.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKD
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf K) (⊤ : Subgroup ↥K) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, hTp.comap_subtype, by rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨Q, hQ⟩ := hS.inf_of_le_normalizer (N := D.subgroupOf K) le_top
    (Subgroup.normalizer_eq_top (H := D.subgroupOf K)).ge
  have hfr := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfr
  have hg' : (⟨g, hg⟩ : K) ∈
      Subgroup.normalizer ((T.subgroupOf K ⊓ D.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔
        D.subgroupOf K := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hg'
  have hxN : (x : Γ) ∈ Subgroup.normalizer ((T ⊓ D : Subgroup Γ) : Set Γ) := by
    have h1 : x ∈ Subgroup.normalizer (((T ⊓ D).subgroupOf K : Subgroup ↥K) : Set ↥K) := hx
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_left.trans hTK)] at h1
    exact h1
  have hyD : (y : Γ) ∈ D := hy
  exact ⟨x, hxN, x.2, y, hyD, congrArg Subtype.val hxy.symm⟩

end CFSG.CGT.PushingUpLit.BHS.Glauberman
