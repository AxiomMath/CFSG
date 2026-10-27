module

public import CFSG.ClassicalInvolution.Asc77.AscT7U2
public import CFSG.ClassicalInvolution.Asc77.AscT7U3
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M5

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
in
theorem exists_hyp25T (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  exact ⟨t', hyp, ht'S, ht'2, hconj⟩
end T7T
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
section Quat
variable {G : Type} [Group G] [Finite G] {R N V : Subgroup G} {z : G}

theorem mem_or_mul_mem_of_mem_sup {R : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (R : Set G)) (ha2 : a * a ∈ R) {y : G}
    (hy : y ∈ R ⊔ Subgroup.zpowers a) : y ∈ R ∨ y * a ∈ R := by
  obtain ⟨h, hh, j, rfl⟩ := T7F2.exists_mul_zpow_of_mem_sup haN hy
  have hpow : ∀ m : ℤ, a ^ (2 * m) ∈ R := fun m => by
    have : a ^ (2 * m) = (a * a) ^ m := by rw [zpow_mul, zpow_two]
    rw [this]; exact R.zpow_mem ha2 m
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' j
  · left
    rw [hm]; exact R.mul_mem hh (hpow m)
  · right
    rw [hm]
    have : h * a ^ (2 * m + 1) * a = h * a ^ (2 * (m + 1)) := by
      rw [mul_assoc, ← zpow_add_one]; congr 2; ring
    rw [this]
    exact R.mul_mem hh (hpow (m + 1))

theorem exists_mul_of_mem_sup_not_mem {R : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (R : Set G)) (ha2 : a * a ∈ R) {y : G}
    (hy : y ∈ R ⊔ Subgroup.zpowers a) (hyR : y ∉ R) : ∃ r' ∈ R, y = a * r' := by
  rcases mem_or_mul_mem_of_mem_sup haN ha2 hy with h | h
  · exact absurd h hyR
  · refine ⟨a⁻¹ * y, ?_, by group⟩
    have h1 : a⁻¹ * (y * a) * a ∈ R := by
      have := inv_conj_mem_of_mem_normalizer haN h
      simpa [mul_assoc] using this
    have h2 : (a * a)⁻¹ ∈ R := R.inv_mem ha2
    have : a⁻¹ * y = (a⁻¹ * (y * a) * a) * (a * a)⁻¹ := by group
    rw [this]
    exact R.mul_mem h1 h2

end Quat
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
theorem no_isFAut_of_centralizes (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (hres : ∀ a ∈ (S : Subgroup G), a * a ∈ R → ¬ IsFAut R' a) {s : G}
          (hs : s ∈ T7F2.Csub S R') :
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
    rw [h11] at hmem
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
  exact hres _ hs'S hs'sq hF'
theorem sq_mem_of_isFAut (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (hres : ∀ a ∈ (S : Subgroup G), a * a ∈ R → ¬ IsFAut R' a) {a : G}
          (haS : a ∈ (S : Subgroup G))
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
  rw [h11] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← hk]
  exact R.zpow_mem h.hzR.mem k
end Main
end T7U
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
theorem exists_sq_mem_zpowers_of_isFAut (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {a : G} (haS : a ∈ (S : Subgroup G)) (hF : IsFAut R' a) (haR : a * a ∈ R) :
    ∃ a₁ ∈ (S : Subgroup G), a₁ * a₁ ∈ Subgroup.zpowers z ∧ IsFAut R' a₁ := by
  have hnorm : conjSub a R' = R' := mem_normalizer_iff_conjSub_eq.mp hF.1
  have haN : a ∈ T7F2.Nsub S R := h.mem_N_of_conj_R' haS hnorm
  have haNR : a ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T7F2.mem_Nsub.mp haN).2
  have hVN : R ⊔ Subgroup.zpowers a ≤ T7F2.Nsub S R :=
    sup_le h.R_le_N (Subgroup.zpowers_le.mpr haN)
  have hVS : R ⊔ Subgroup.zpowers a ≤ (S : Subgroup G) := hVN.trans inf_le_left
  have hV2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers a) := S.isPGroup'.to_le hVS
  have hVR : ∀ y ∈ R ⊔ Subgroup.zpowers a, conjSub y R = R := fun y hy =>
    (T7F2.mem_Nsub.mp (hVN hy)).2
  have haV : a ∈ R ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hRV : R ≤ R ⊔ Subgroup.zpowers a := le_sup_left
  have hcenter : ∀ x : G, x ∈ R → (∀ r ∈ R, r * x = x * r) → x ∈ Subgroup.zpowers z :=
    fun x hxR hxc =>
    T7U.inf_centralizer_le_zpowers h.hqR h.hzR (Subgroup.mem_inf.mpr
      ⟨hxR, Subgroup.mem_centralizer_iff.mpr hxc⟩)
  have hFmul : ∀ r' ∈ R, IsFAut R' (a * r') := fun r' hr' =>
    isFAut_mul_of_centralizes (fun x hx => ((T7F2.mem_Csub.mp (h.R_le_C' hr')).2 x hx).symm) hF
  have hsqR : ∀ r' ∈ R, (a * r') * (a * r') ∈ R := fun r' hr' => by
    have e : (a * r') * (a * r') = (a * r' * a⁻¹) * (a * a) * r' := by group
    rw [e]
    exact R.mul_mem (R.mul_mem (conj_mem_of_mem_normalizer haNR hr') haR) hr'
  by_cases hcase : a ∈ R ⊔ (R ⊔ Subgroup.zpowers a) ⊓ Subgroup.centralizer (R : Set G)
  ·
    obtain ⟨r, hr, c, hc, hrc⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
      (A := R) (B := (R ⊔ Subgroup.zpowers a) ⊓ Subgroup.centralizer (R : Set G))
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx) hcase
    obtain ⟨hcV, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcc : ∀ x ∈ R, x * c = c * x := Subgroup.mem_centralizer_iff.mp hcC
    have hcS : c ∈ (S : Subgroup G) := hVS hcV
    have hcr : c = a * (a⁻¹ * r⁻¹ * a) := by
      have : c = r⁻¹ * a := by rw [hrc]; group
      rw [this]; group
    have hr'' : a⁻¹ * r⁻¹ * a ∈ R := inv_conj_mem_of_mem_normalizer haNR (R.inv_mem hr)
    refine ⟨c, hcS, ?_, hcr ▸ hFmul _ hr''⟩
    refine hcenter _ ?_ (fun x hx => ?_)
    · rw [hcr]; exact hsqR _ hr''
    · calc x * (c * c) = (x * c) * c := by group
        _ = (c * x) * c := by rw [hcc x hx]
        _ = c * (x * c) := by group
        _ = c * (c * x) := by rw [hcc x hx]
        _ = (c * c) * x := by group
  · by_cases hex : ∃ y ∈ R ⊔ Subgroup.zpowers a, IsFAut R y
    ·
      obtain ⟨y, hyV, hyF⟩ := hex
      have hyR : y ∉ R := fun hyR => not_isFAut_of_mem h.hqR h.hzR hyR hyF
      obtain ⟨r', hr', hy⟩ := exists_mul_of_mem_sup_not_mem haNR haR hyV hyR
      refine ⟨y, hVS hyV, ?_, hy ▸ hFmul r' hr'⟩
      refine hcenter _ (hy ▸ hsqR r' hr') (fun x hx => ?_)
      exact (hyF.2.1 x hx).symm
    ·
      push Not at hex
      have haR' : a ∉ R := fun haR' => hcase (Subgroup.mem_sup_left haR')
      obtain ⟨r, hr, hnt⟩ := T7G2.exists_comm_not_mem h.hqR h.hzR hRV hV2 hVR hex haV hcase
      have hidx : Nat.card ↥(R ⊔ Subgroup.zpowers a) = 2 * Nat.card ↥R := by
        have hrel : R.relIndex (R ⊔ Subgroup.zpowers a) = 2 := by
          unfold Subgroup.relIndex
          rw [Subgroup.index_eq_two_iff]
          refine ⟨⟨a, haV⟩, fun y => ?_⟩
          obtain ⟨y, hy⟩ := y
          rcases mem_or_mul_mem_of_mem_sup haNR haR hy with h1 | h1
          · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr h1, fun hya => ?_⟩
            have hya' : y * a ∈ R := hya
            exact haR' (by simpa using R.mul_mem (R.inv_mem h1) hya')
          · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr h1, fun hyR => ?_⟩
            have hyR' : y ∈ R := hyR
            exact haR' (by simpa using R.mul_mem (R.inv_mem hyR') h1)
        have h1 := Subgroup.relIndex_mul_card R (R ⊔ Subgroup.zpowers a)
        rw [inf_eq_left.mpr hRV, hrel] at h1
        omega
      have hl : IsQuaternionSub (R ⊔ Subgroup.zpowers a) ∨
          IsSemidihedral (R ⊔ Subgroup.zpowers a) :=
        l3_12 hV2 hRV hidx h.hqR h.hzR ⟨a, haV, r, hr, hnt⟩
      obtain ⟨s, hsV, hsR, hss⟩ := exists_sq_mem_zpowers hRV hidx hV2 h.hzR hl
      obtain ⟨r', hr', hs⟩ := exists_mul_of_mem_sup_not_mem haNR haR hsV hsR
      exact ⟨s, hVS hsV, hss, hs ▸ hFmul r' hr'⟩
end Main
end T7U
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
