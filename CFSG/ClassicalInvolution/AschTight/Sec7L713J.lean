module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713I
public import CFSG.ClassicalInvolution.AschTight.Sec7L713F
public import CFSG.ClassicalInvolution.AschTight.Sec7L713H

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_odd_conj {W R T L J₁ : Subgroup G} {u v r a : G}
    (hrN : r ∈ Subgroup.normalizer (W : Set G)) (haW : a ∈ Subgroup.normalizer (W : Set G))
    (hconj : conjSub r L = conjSub a J₁) (hLW : L ⊓ W = T ⊓ W) (hJ₁W : J₁ ⊓ W = R ⊓ W)
    (hu : Subgroup.zpowers u = R ⊓ W) (hv : Subgroup.zpowers v = T ⊓ W)
    (hrv : r * v * r⁻¹ = v * u) (h2u : 2 ∣ orderOf u) :
    ∃ i : ℤ, Odd i ∧ a * u * a⁻¹ = (v * u) ^ i := by
  have hzp : Subgroup.zpowers (v * u) = Subgroup.zpowers (a * u * a⁻¹) := by
    have e1 : conjSub r (L ⊓ W) = conjSub a (J₁ ⊓ W) := by
      rw [conjSub_inf, conjSub_inf, hconj, mem_normalizer_iff_conjSub_eq.mp hrN,
        mem_normalizer_iff_conjSub_eq.mp haW]
    rw [hLW, hJ₁W, ← hv, ← hu, AscL62.conjSub_zpowers_eq, AscL62.conjSub_zpowers_eq, hrv] at e1
    exact e1
  have hmem : a * u * a⁻¹ ∈ Subgroup.zpowers (v * u) := hzp ▸ Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hovu : orderOf (v * u) = orderOf u := by
    rw [← Nat.card_zpowers, hzp, ← AscL62.conjSub_zpowers_eq, natCard_conjSub, Nat.card_zpowers]
  exact ⟨i, odd_of_zpowers_eq hzp (by rw [hovu]; exact h2u) hi, hi.symm⟩

theorem exists_conj_eq_mul (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) (h67 : RCommute Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Ω)
    (hRJ₁ : R ≤ J₁) {a t r u : G} (haW : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    (htN : t ∈ Subgroup.normalizer (W : Set G)) (hrR : r ∈ R) (hrW : r ∉ W)
    (hu : Subgroup.zpowers u = R ⊓ W) (hx : bar (hR.2 hrR) * bar (hR.2 hrR) = 1)
    (h3 : (bar (hR.2 hrR) * (bar haW * bar (hR.2 hrR) * (bar haW)⁻¹)) ^ 3 = 1)
    (hα : bar haW * bar haW = 1)
    (hbt : bar htN = bar (hR.2 hrR) * (bar haW * bar (hR.2 hrR) * (bar haW)⁻¹) * bar (hR.2 hrR)) :
    ∃ j : ℤ, ∃ x₁ ∈ OCW W, r * (a * t) * r⁻¹ = a * t * (u ^ j * x₁) := by
  have hW2 := isPGroup_of_mem_WSet hW
  have hrN := hR.2 hrR
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hRa : conjSub a R ∈ DSet Ω W := ⟨RSet.conj hΩ.conjInvariant hR.1 a, by
    have := conjSub_le_normalizer hR.2 a
    rwa [mem_normalizer_iff_conjSub_eq.mp haW] at this⟩
  have hsRa : a * r * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hrR
  have hsW : a * r * a⁻¹ ∉ W := by
    intro h
    apply hrW
    have h' : a * r * a⁻¹ ∈ conjSub a W := by
      rw [mem_normalizer_iff_conjSub_eq.mp haW]
      exact h
    rw [mem_conjSub_iff] at h'
    simpa [mul_assoc] using h'
  have hy : (bar haW * bar hrN * (bar haW)⁻¹) * (bar haW * bar hrN * (bar haW)⁻¹) = 1 := by
    calc _ = bar haW * (bar hrN * bar hrN) * (bar haW)⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have htiN : t⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ htN
  have hconj : conjSub t⁻¹ (conjSub a J₁) = J₁ := by
    refine conjSub_eq_of_bar hp hΩ h611 habel h67 hW hRa hR htiN hsRa hsW hrR ?_
      (hΩ.conjInvariant a J₁ hJ₁) hJ₁ (conjSub_mono hRJ₁) hRJ₁
    change (bar htN)⁻¹ * (bar haW * bar hrN * (bar haW)⁻¹) * (bar htN)⁻¹⁻¹ = bar hrN
    rw [hbt]
    exact s3_conj_inv hx hy h3
  have hga : t⁻¹ * a ∈ Subgroup.normalizer (W : Set G) := Subgroup.mul_mem _ htiN haW
  have hR₂J₁ : conjSub (t⁻¹ * a) R ≤ J₁ :=
    calc conjSub (t⁻¹ * a) R ≤ conjSub (t⁻¹ * a) J₁ := conjSub_mono hRJ₁
      _ = J₁ := by rw [conjSub_mul, hconj]
  have hR₂ : conjSub (t⁻¹ * a) R ∈ DSet Ω W := ⟨RSet.conj hΩ.conjInvariant hR.1 _, by
    have := conjSub_le_normalizer hR.2 (t⁻¹ * a)
    rwa [mem_normalizer_iff_conjSub_eq.mp hga] at this⟩
  have hkey := keyOn_strong hp hq hΩ habel h611 hW hR hR₂ hJ₁ hRJ₁ hR₂J₁
  have hmem : (t⁻¹ * a) * r * (t⁻¹ * a)⁻¹ ∈ conjSub (t⁻¹ * a) R := conj_mem_conjSub hrR
  have e2 : (a * t)⁻¹ * r * (a * t) = (t⁻¹ * a) * r * (t⁻¹ * a)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hai]
  have hh1 : (a * t)⁻¹ * r * (a * t) * r⁻¹ ∈ R ⊔ OCW W := by
    rw [e2]
    exact Subgroup.mul_mem _ (hkey hmem) (Subgroup.mem_sup_left (R.inv_mem hrR))
  have hcN : a * t ∈ Subgroup.normalizer (W : Set G) := Subgroup.mul_mem _ haW htN
  have hhN : (a * t)⁻¹ * r * (a * t) * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hrN) hcN)
      (Subgroup.inv_mem _ hrN)
  have hh2 : (a * t)⁻¹ * r * (a * t) * r⁻¹ ∈ W ⊔ OCW W := by
    apply (bar_eq_one_iff hhN).mp
    change (bar haW * bar htN)⁻¹ * bar hrN * (bar haW * bar htN) * (bar hrN)⁻¹ = 1
    rw [hbt]
    exact s3_cent hx hy h3 rfl hα
  obtain ⟨j, x₁, hx₁, hjx⟩ := exists_zpow_mul hW2 (isPGroup_of_mem_RSet hR.1) hR.2 hu hh1 hh2
  exact ⟨j, x₁, hx₁, by rw [← hjx]; group⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
