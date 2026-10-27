module

public import CFSG.ClassicalInvolution.Asc77.AscT7U1
public import CFSG.ClassicalInvolution.Asc77.AscT7TC15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7U

section Quat

variable {G : Type} [Group G] [Finite G] {R N V : Subgroup G} {z : G}

theorem sq_mem_sup (hR : IsQuatSub R) (hz : IsUniqueInvolution R z) (hRN : R ≤ N) (hNV : N ≤ V)
    (hV2 : IsPGroup 2 ↥V) (hVR : ∀ y ∈ V, conjSub y R = R) (hF : ∀ y ∈ N, ¬ IsFAut R y) {v : G}
    (hv : v ∈ V) (hvN : v * v ∈ N) :
    v * v ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) := by
  obtain ⟨a, b, n, c, hinv⟩ := T7F2.exists_coord hR hz hV2 hVR
  have sV : T7F2.Out.Setting R V a b n := ⟨c, hRN.trans hNV, hVR, hinv⟩
  have sN : T7F2.Out.Setting R N a b n :=
    ⟨c, hRN, fun y hy => hVR y (hNV hy), fun y hy => hinv y (hNV hy)⟩
  obtain ⟨i, j, hi, hia, hjb⟩ := sV.coord_of_mem hv
  have hb : (v * v) * b * (v * v)⁻¹ = b * a ^ (j + i * j) :=
    T7F2.Out.coord_mul_b hia hjb hjb
  have hev : Even (j + i * j) := by
    have : j + i * j = (1 + i) * j := by ring
    rw [this]
    exact (Odd.add_odd odd_one hi).mul_right j
  exact T7F2.Out.Hsub_le_sup sN hF (hV2.to_le hNV)
    ((T7F2.Out.mem_Hsub sN).mpr ⟨hvN, j + i * j, hev, hb⟩)

end Quat

section Residual

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C25_16sqR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a ∈ R → ¬ IsFAut R' a

end Residual

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem no_isFAut_of_centralizes (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : C25_11 p f) (hres : C25_16sqR p f) {s : G} (hs : s ∈ T7F2.Csub S R') :
    ¬ IsFAut R s := by
  intro hF
  obtain ⟨hsS, hsc⟩ := T7F2.mem_Csub.mp hs
  have hss : s * s ∈ Subgroup.zpowers z := by
    have hmem : s * s ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      refine ⟨Subgroup.mul_mem _ hsS hsS, ?_⟩
      have hle : R ⊔ R' ≤ Subgroup.centralizer ({s * s} : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.2.1 x hx).symm
        · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          have hx' := hsc x hx
          calc x * (s * s) = (x * s) * s := by group
            _ = (s * x) * s := by rw [hx']
            _ = s * (x * s) := by group
            _ = s * (s * x) := by rw [hx']
            _ = (s * s) * x := by group
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    rw [h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp] at hmem
    exact hmem
  have hF' : IsFAut R' (t' * s * t'⁻¹) := by
    have := T7U.isFAut_conjSub hF t'
    rwa [h.ht'R] at this
  have hs'S : t' * s * t'⁻¹ ∈ (S : Subgroup G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ h.ht'S hsS) (Subgroup.inv_mem _ h.ht'S)
  have hzt : t' * z * t'⁻¹ = z := by
    have := h.hyp.hzS t' h.ht'S
    calc t' * z * t'⁻¹ = (z * t') * t'⁻¹ := by rw [this]
      _ = z := by group
  have hs'sq : (t' * s * t'⁻¹) * (t' * s * t'⁻¹) ∈ R := by
    have e : (t' * s * t'⁻¹) * (t' * s * t'⁻¹) = t' * (s * s) * t'⁻¹ := by group
    rw [e]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hss
    rw [← hk, T7T.conj_zpow hzt]
    exact R.zpow_mem h.hzR.mem k
  exact hres G Ω K K' W S R R' z t u₁ u₂ h.hyp _ hs'S hs'sq hF'

theorem sq_mem_of_isFAut (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : C25_11 p f) (hres : C25_16sqR p f) {a : G} (haS : a ∈ (S : Subgroup G))
    (hF : IsFAut R' a) : a * a ∈ R := by
  have hnorm : conjSub a R' = R' := mem_normalizer_iff_conjSub_eq.mp hF.1
  have haN : a ∈ T7F2.Nsub S R := h.mem_N_of_conj_R' haS hnorm
  have hMN : T7F2.Csub S R' ≤ T7F2.Nsub S R := h.C'_le_N
  have hVN : T7F2.Csub S R' ⊔ Subgroup.zpowers a ≤ T7F2.Nsub S R :=
    sup_le hMN (Subgroup.zpowers_le.mpr haN)
  have hVS : T7F2.Csub S R' ⊔ Subgroup.zpowers a ≤ (S : Subgroup G) := hVN.trans inf_le_left
  have hV2 : IsPGroup 2 ↥(T7F2.Csub S R' ⊔ Subgroup.zpowers a) := S.isPGroup'.to_le hVS
  have hVR : ∀ y ∈ T7F2.Csub S R' ⊔ Subgroup.zpowers a, conjSub y R = R := fun y hy =>
    (T7F2.mem_Nsub.mp (hVN hy)).2
  have hF1 : ∀ y ∈ T7F2.Csub S R', ¬ IsFAut R y := fun y hy =>
    no_isFAut_of_centralizes h h11 hres hy
  have hv : a ∈ T7F2.Csub S R' ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hvN : a * a ∈ T7F2.Csub S R' := by
    refine T7F2.mem_Csub.mpr ⟨Subgroup.mul_mem _ haS haS, fun r hr => ?_⟩
    exact (hF.2.1 r hr).symm
  have hmain := sq_mem_sup h.hqR h.hzR h.R_le_C' le_sup_left hV2 hVR hF1 hv hvN
  refine (sup_le le_rfl ?_ : R ⊔ (T7F2.Csub S R' ⊓ Subgroup.centralizer (R : Set G)) ≤ R) hmain
  intro x hx
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxS, hxc⟩ := T7F2.mem_Csub.mp hxM
  have hxcR : ∀ r ∈ R, r * x = x * r := Subgroup.mem_centralizer_iff.mp hxC
  have hmem : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    refine ⟨hxS, ?_⟩
    have hle : R ⊔ R' ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxcR r hr))
        (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxc r hr))
    exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hr)
  rw [h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← hk]
  exact R.zpow_mem h.hzR.mem k

theorem c25_16_of_sqR (h11 : C25_11 p f) (hres : C25_16sqR p f) : C25_16 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  exact hres G Ω K K' W S R R' z t u₁ u₂ hyp a haS (sq_mem_of_isFAut h h11 hres haS hF) hF

end Main

end T7U

end CFSG.ClassicalInvolution.Asc77
