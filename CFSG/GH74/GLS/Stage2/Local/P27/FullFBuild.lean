module

public import CFSG.GH74.GLS.Stage2.Local.P27.DatumPlus
public import CFSG.GH74.GLS.Stage2.Local.P27.S45E
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def FullFT1 (z x : G) (T : Subgroup G) : Prop :=
  ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ x ∈ T₁ ∧ z ∈ T₁ ∧
    IsDihedral ↥T₁

theorem fullFT1_of_complement {z x : G} {T D₂ T₁s : Subgroup G}
    (hle : T₁s ≤ T) (hdih : IsDihedral ↥T₁s) (hx : x ∈ T₁s) (hz : z ∈ T₁s)
    (hinf : T₁s ⊓ D₂ = ⊥) (hsup : D₂ ⊔ T₁s = T) (hTJ : T ⊓ Jx x = D₂) : FullFT1 z x T := by
  refine ⟨T₁s, hle, by rw [hTJ]; exact hsup, ?_, hx, hz, hdih⟩
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  have : g ∈ T₁s ⊓ D₂ := ⟨hg1, by rw [← hTJ]; exact ⟨hle hg1, hg2⟩⟩
  rw [hinf] at this
  exact this

theorem fullFT1_of_extra {z x t' : G} {T D₁ D₂ U : Subgroup G} {n : ℕ}
    (hsyl : Syl z x T D₁ D₂ U n t') (hex : Extra z x T D₁ D₂ U t') : FullFT1 z x T := by
  obtain ⟨T₁s, hle, hdih, hD₁, hinf, hsup⟩ := hex.compl
  exact fullFT1_of_complement hle hdih (hD₁ hsyl.x_mem) (hD₁ hsyl.z_mem) hinf hsup hex.T_inf_J

theorem Jx_conj [Finite G] (x g : G) : Jx (g * x * g⁻¹) = cmap g (Jx x) := by
  unfold Jx
  rw [← Stage1.Thm2.Recip.map_centralizer_singleton_conj x g]
  exact pLayerOf_cmap g _

theorem exists_conj_le_of_isSylowOf [Finite G] {K T R : Subgroup G} (hT : IsSylowOf 2 T K) (hRK : R ≤ K)
    (hR : IsPGroup 2 ↥R) : ∃ k ∈ K, ∀ y ∈ R, k⁻¹ * y * k ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  have hR' : IsPGroup 2 ↥(R.subgroupOf K) := hR.comap_subtype
  obtain ⟨Q', hQ'⟩ := hR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q Q'
  refine ⟨(g : G), g.2, fun y hy => ?_⟩
  have hyK : y ∈ K := hRK hy
  have h1 : (⟨y, hyK⟩ : ↥K) ∈ (Q' : Subgroup ↥K) := hQ' hy
  rw [← hg] at h1
  have h2 : g⁻¹ * (⟨y, hyK⟩ : ↥K) * g ∈ (Q : Subgroup ↥K) := by
    change (⟨y, hyK⟩ : ↥K) ∈ MulAut.conj g • (Q : Subgroup ↥K) at h1
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at h1
    exact h1
  rw [hQ] at h2
  exact h2

@[expose] def DihQuot (x : G) : Prop :=
  x ∉ Jx x ∧ ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) → IsPGroup 2 ↥R → R ⊓ Jx x = ⊥ →
    IsCyclic ↥R ∨ IsDihedral ↥R

section Quot

variable [Finite G]

theorem dihQuot_of_T1 {x : G} {T T₁ : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hxJ : x ∉ Jx x) (hT₁ : T₁ ≤ T) (hsup : (T ⊓ Jx x) ⊔ T₁ = T) (hinf : T₁ ⊓ Jx x = ⊥)
    (hdih : IsDihedral ↥T₁) : DihQuot x := by
  refine ⟨hxJ, fun R hRC hR2 hRJ => ?_⟩
  obtain ⟨k, hk, hkR⟩ := exists_conj_le_of_isSylowOf hT hRC hR2
  have hJn : ∀ c ∈ centralizer ({x} : Set G), ∀ j : G, j ∈ Jx x ↔ c * j * c⁻¹ ∈ Jx x := fun c hc j =>
    Subgroup.mem_normalizer_iff.1 (S45.mem_normalizer_Jx hc) j
  have hAT : cmap k⁻¹ R ≤ T := by
    intro a ha
    have h1 : k * a * k⁻¹ ∈ R := by simpa using (mem_cmap.1 ha)
    have h2 := hkR _ h1
    simpa [mul_assoc] using h2
  have hAN : cmap k⁻¹ R ⊓ (T ⊓ Jx x) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, -, haJ⟩
    have h1 : k * a * k⁻¹ ∈ R := by simpa using (mem_cmap.1 ha)
    have h2 : k * a * k⁻¹ ∈ Jx x := (hJn k hk a).1 haJ
    have h3 : k * a * k⁻¹ ∈ R ⊓ Jx x := ⟨h1, h2⟩
    rw [hRJ, Subgroup.mem_bot] at h3
    have : a = 1 := by
      have e : a = k⁻¹ * (k * a * k⁻¹) * k := by group
      rw [e, h3]; group
    rw [this]
    exact Subgroup.one_mem _
  have hnorm : T ≤ normalizer ((T ⊓ Jx x : Subgroup G) : Set G) := by
    intro g hg
    have hgC : g ∈ centralizer ({x} : Set G) := hT.le hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hT' : h ∈ T ↔ g * h * g⁻¹ ∈ T := by
      constructor
      · intro hh
        exact T.mul_mem (T.mul_mem hg hh) (T.inv_mem hg)
      · intro hh
        have := T.mul_mem (T.mul_mem (T.inv_mem hg) hh) hg
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    exact and_congr hT' (hJn g hgC h)
  have hinfN : (T ⊓ Jx x) ⊓ T₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨-, hgJ⟩, hgT⟩
    have : g ∈ T₁ ⊓ Jx x := ⟨hgT, hgJ⟩
    rw [hinf] at this
    exact this
  obtain ⟨φ, hφ⟩ := S45.exists_injective_hom_to_complement inf_le_left hnorm hT₁ hsup hinfN hAT hAN
  have hp : IsPGroup 2 ↥T₁ := hT.isPGroup.to_le hT₁
  have hAcd := S45.cyclic_or_dihedral_of_injective hdih hp φ hφ
  let e : ↥R ≃* ↥(cmap k⁻¹ R) :=
    Subgroup.equivMapOfInjective R (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective
  exact S45.cyclic_or_dihedral_congr e.symm hAcd

theorem DihQuot.conj {x : G} (h : DihQuot x) (g : G) : DihQuot (g * x * g⁻¹) := by
  refine ⟨?_, fun R' hRC hR2 hRJ => ?_⟩
  · rw [Jx_conj, mem_cmap]
    simpa [mul_assoc] using h.1
  · let e : ↥R' ≃* ↥(cmap g⁻¹ R') :=
      Subgroup.equivMapOfInjective R' (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    have hmem : ∀ y : G, y ∈ cmap g⁻¹ R' ↔ g * y * g⁻¹ ∈ R' := fun y => by
      rw [mem_cmap]; simp
    have hRx : cmap g⁻¹ R' ≤ centralizer ({x} : Set G) := by
      intro y hy
      have h1 := hRC ((hmem y).1 hy)
      rw [mem_centralizer_singleton_iff] at h1 ⊢
      have e1 : (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      have e2 : (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      rw [e1, e2] at h1
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    have hR2' : IsPGroup 2 ↥(cmap g⁻¹ R') := hR2.of_surjective e.toMonoidHom e.surjective
    have hRJ' : cmap g⁻¹ R' ⊓ Jx x = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      have h1 : g * y * g⁻¹ ∈ R' := (hmem y).1 hy1
      have h2 : g * y * g⁻¹ ∈ Jx (g * x * g⁻¹) := by
        rw [Jx_conj, mem_cmap]; simpa [mul_assoc] using hy2
      have h3 : g * y * g⁻¹ ∈ R' ⊓ Jx (g * x * g⁻¹) := ⟨h1, h2⟩
      rw [hRJ, Subgroup.mem_bot] at h3
      have : y = 1 := by
        have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [e, h3]; group
      rw [this]
      exact Subgroup.one_mem _
    exact S45.cyclic_or_dihedral_congr e.symm (h.2 _ hRx hR2' hRJ')

theorem dihQuot_of_datumPlus {z x : G} (h : DatumPlus z x) : DihQuot x := by
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr, hex⟩ := h
  obtain ⟨T₁s, hle, hsup, hinf, -, -, hdih⟩ := fullFT1_of_extra hS hex
  exact dihQuot_of_T1 hC.T_syl (not_mem_Jx_of_parts hC hS hTr) hle hsup hinf hdih

end Quot

end CFSG.GH74.GLS.Stage2.Local.P27
