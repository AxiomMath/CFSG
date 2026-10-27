module

public import CFSG.ClassicalInvolution.Asc77.AscT7U2
public import CFSG.ClassicalInvolution.Asc77.AscT7U3
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7U

section Residual

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C25_16sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G),
      a * a ∈ Subgroup.zpowers z → ¬ IsFAut R' a

end Residual

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


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

theorem exists_sq_mem_zpowers_of_isFAut (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
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

theorem c25_16sqR_of_sq (hres : C25_16sq p f) : C25_16sqR p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS haR hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  obtain ⟨a₁, ha₁S, ha₁sq, ha₁F⟩ := exists_sq_mem_zpowers_of_isFAut h haS hF haR
  exact hres G Ω K K' W S R R' z t u₁ u₂ hyp a₁ ha₁S ha₁sq ha₁F

theorem c25_16_of_sq (h11 : C25_11 p f) (hres : C25_16sq p f) : C25_16 p f :=
  c25_16_of_sqR h11 (c25_16sqR_of_sq hres)

end Main

end T7U

end CFSG.ClassicalInvolution.Asc77
