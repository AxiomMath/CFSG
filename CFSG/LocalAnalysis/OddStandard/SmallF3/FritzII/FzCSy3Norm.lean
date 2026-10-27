module

public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3Cos

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem fzc_rho_sq_eq_inv {rho : G} (hrho : rho ^ 3 = 1) : rho ^ 2 = rho⁻¹ := by
  have h : rho ^ 2 * rho = 1 := by rw [← pow_succ, hrho]
  exact mul_eq_one_iff_eq_inv.mp h

private theorem fzc_conj_inv_eq {rho w : G} (hrho : rho ^ 3 = 1) :
    rho * (rho * w * rho⁻¹) * rho⁻¹ = rho⁻¹ * w * rho := by
  have h2 := fzc_rho_sq_eq_inv hrho
  calc rho * (rho * w * rho⁻¹) * rho⁻¹
      = rho ^ 2 * w * (rho ^ 2)⁻¹ := by rw [pow_two]; group
    _ = rho⁻¹ * w * (rho⁻¹)⁻¹ := by rw [h2]
    _ = rho⁻¹ * w * rho := by group

private theorem fzc_conj_three {rho w : G} (hrho : rho ^ 3 = 1) :
    rho * (rho * (rho * w * rho⁻¹) * rho⁻¹) * rho⁻¹ = w := by
  have h : rho * rho * rho = 1 := by rw [← pow_two, ← pow_succ, hrho]
  calc rho * (rho * (rho * w * rho⁻¹) * rho⁻¹) * rho⁻¹
      = (rho * rho * rho) * w * (rho * rho * rho)⁻¹ := by group
    _ = w := by rw [h]; group

private theorem fzc_comm_sq_eq {rho r : G} :
    ⁅r, rho ^ 2⁆ = r * (rho * rho) * r⁻¹ * (rho * rho)⁻¹ := by
  rw [commutatorElement_def, pow_two]

private theorem fzc_zpowers_rho_cases {rho s : G} (hrho : rho ^ 3 = 1)
    (hs : s ∈ zpowers rho) : s = 1 ∨ s = rho ∨ s = rho ^ 2 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hred : rho ^ k = rho ^ (k % (3 : ℤ)) := zpow_eq_zpow_emod' k hrho
  rw [← hk, hred]
  have h0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have h1 : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hc : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hc with h | h | h <;> rw [h]
  · left; rw [zpow_zero]
  · right; left; rw [zpow_one]
  · right; right; norm_num

theorem fzc_sy3_norm {R N : Subgroup G} {rho : G} (hNR : N ≤ R)
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hrR : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R)
    (hrN : ∀ n ∈ N, rho * n * rho⁻¹ ∈ N) (hab : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hrho : rho ^ 3 = 1) :
    ∀ x ∈ ⁅R, zpowers rho⁆, x * (rho * x * rho⁻¹) * (rho⁻¹ * x * rho) ∈ N := by
  haveI hNnorm : (N.subgroupOf R).Normal := ⟨fun n hn g => by
    simp only [Subgroup.mem_subgroupOf] at hn ⊢
    exact hRN (g : G) g.2 (n : G) hn⟩
  letI hQcomm : CommGroup (↥R ⧸ N.subgroupOf R) :=
    { (inferInstance : Group (↥R ⧸ N.subgroupOf R)) with
      mul_comm := by
        intro a b
        refine Quotient.inductionOn₂' a b ?_
        intro x y
        change ((x * y : ↥R) : ↥R ⧸ N.subgroupOf R) =
          ((y * x : ↥R) : ↥R ⧸ N.subgroupOf R)
        rw [QuotientGroup.eq]
        simp only [Subgroup.mem_subgroupOf]
        have h := hab (y : G)⁻¹ (R.inv_mem y.2) (x : G)⁻¹ (R.inv_mem x.2)
        simpa [mul_inv_rev, mul_assoc] using h }
  let φ : ↥R →* ↥R :=
    { toFun := fun r => ⟨rho * (r : G) * rho⁻¹, hrR (r : G) r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group }
  have hφN : N.subgroupOf R ≤ (N.subgroupOf R).comap φ := by
    intro n hn
    have hnN : (n : G) ∈ N := hn
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hrN (n : G) hnN
  let φbar : (↥R ⧸ N.subgroupOf R) →* (↥R ⧸ N.subgroupOf R) :=
    QuotientGroup.map (N.subgroupOf R) (N.subgroupOf R) φ hφN
  have hφbar_mk : ∀ r : ↥R, φbar (QuotientGroup.mk r) = QuotientGroup.mk (φ r) :=
    fun r => rfl
  have hφ3elem : ∀ r : ↥R, φ (φ (φ r)) = r := by
    intro r
    apply Subtype.ext
    exact fzc_conj_three hrho
  have hφbar3elem : ∀ q, φbar (φbar (φbar q)) = q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro r
    rw [hφbar_mk, hφbar_mk, hφbar_mk, hφ3elem r]
  let ν : (↥R ⧸ N.subgroupOf R) →* (↥R ⧸ N.subgroupOf R) :=
    (MonoidHom.id (↥R ⧸ N.subgroupOf R)) * φbar * (φbar.comp φbar)
  have hν_apply : ∀ q, ν q = q * φbar q * φbar (φbar q) := by
    intro q
    simp [ν, MonoidHom.mul_apply]
  have hνφ : ∀ q, ν (φbar q) = ν q := by
    intro q
    rw [hν_apply, hν_apply, hφbar3elem q]
    ac_rfl
  have hνφ2 : ∀ q, ν (φbar (φbar q)) = ν q := by
    intro q
    rw [hνφ, hνφ]
  have hRinv : ∀ r ∈ R, rho⁻¹ * r * rho ∈ R := by
    intro r hr
    rw [← fzc_conj_inv_eq hrho]
    exact hrR _ (hrR r hr)
  have hnormmem : ∀ r : ↥R,
      (r : G) * (rho * (r : G) * rho⁻¹) * (rho⁻¹ * (r : G) * rho) ∈ R :=
    fun r => R.mul_mem (R.mul_mem r.2 (hrR _ r.2)) (hRinv _ r.2)
  have hνnorm : ∀ r : ↥R, ν (QuotientGroup.mk r) =
      (QuotientGroup.mk (⟨(r : G) * (rho * (r : G) * rho⁻¹) * (rho⁻¹ * (r : G) * rho),
        hnormmem r⟩ : ↥R) : ↥R ⧸ N.subgroupOf R) := by
    intro r
    rw [hν_apply, hφbar_mk, hφbar_mk]
    change (QuotientGroup.mk ((r : ↥R) * φ r * φ (φ r)) : ↥R ⧸ N.subgroupOf R) =
      (QuotientGroup.mk (⟨(r : G) * (rho * (r : G) * rho⁻¹) * (rho⁻¹ * (r : G) * rho),
        hnormmem r⟩ : ↥R) : ↥R ⧸ N.subgroupOf R)
    congr 1
    apply Subtype.ext
    change (r : G) * (rho * (r : G) * rho⁻¹) * (rho * (rho * (r : G) * rho⁻¹) * rho⁻¹) =
      (r : G) * (rho * (r : G) * rho⁻¹) * (rho⁻¹ * (r : G) * rho)
    rw [fzc_conj_inv_eq hrho]
  have key : ⁅R, zpowers rho⁆ ≤
      ((ν.comp (QuotientGroup.mk' (N.subgroupOf R))).ker).map R.subtype := by
    rw [Subgroup.commutator_le]
    intro r hr s hs
    rw [Subgroup.mem_map]
    rcases fzc_zpowers_rho_cases hrho hs with h1 | h2 | h3
    · subst s
      have hmem : ⁅r, (1 : G)⁆ ∈ R := by simp
      refine ⟨⟨⁅r, (1 : G)⁆, hmem⟩, ?_, rfl⟩
      change ν (QuotientGroup.mk (⟨⁅r, (1 : G)⁆, hmem⟩ : ↥R)) = 1
      have hone : (⟨⁅r, (1 : G)⁆, hmem⟩ : ↥R) = 1 := by ext; simp
      rw [hone]
      simp
    · subst s
      have hmem : ⁅r, rho⁆ ∈ R := by
        have h := R.mul_mem hr (hrR (r⁻¹) (R.inv_mem hr))
        simpa [commutatorElement_def, mul_assoc] using h
      refine ⟨⟨⁅r, rho⁆, hmem⟩, ?_, rfl⟩
      change ν (QuotientGroup.mk (⟨⁅r, rho⁆, hmem⟩ : ↥R)) = 1
      have hq : QuotientGroup.mk (⟨⁅r, rho⁆, hmem⟩ : ↥R) =
          QuotientGroup.mk (⟨r, hr⟩ : ↥R) *
            (φbar (QuotientGroup.mk (⟨r, hr⟩ : ↥R)))⁻¹ := by
        rw [hφbar_mk]
        change (QuotientGroup.mk (⟨⁅r, rho⁆, hmem⟩ : ↥R) : ↥R ⧸ N.subgroupOf R) =
          (QuotientGroup.mk ((⟨r, hr⟩ : ↥R) * (φ (⟨r, hr⟩ : ↥R))⁻¹) :
            ↥R ⧸ N.subgroupOf R)
        congr 1
        apply Subtype.ext
        change r * rho * r⁻¹ * rho⁻¹ = r * (rho * r * rho⁻¹)⁻¹
        group
      rw [hq, map_mul, map_inv, hνφ]
      simp
    · subst s
      have hmem : ⁅r, rho ^ 2⁆ ∈ R := by
        have h : r * (rho * (rho * r⁻¹ * rho⁻¹) * rho⁻¹) ∈ R :=
          R.mul_mem hr (hrR _ (hrR (r⁻¹) (R.inv_mem hr)))
        rwa [show r * (rho * (rho * r⁻¹ * rho⁻¹) * rho⁻¹) =
            r * (rho * rho) * r⁻¹ * (rho * rho)⁻¹ by
              simp only [mul_inv_rev, inv_inv]; group,
          ← fzc_comm_sq_eq] at h
      refine ⟨⟨⁅r, rho ^ 2⁆, hmem⟩, ?_, rfl⟩
      change ν (QuotientGroup.mk (⟨⁅r, rho ^ 2⁆, hmem⟩ : ↥R)) = 1
      have hq : QuotientGroup.mk (⟨⁅r, rho ^ 2⁆, hmem⟩ : ↥R) =
          QuotientGroup.mk (⟨r, hr⟩ : ↥R) *
            (φbar (φbar (QuotientGroup.mk (⟨r, hr⟩ : ↥R))))⁻¹ := by
        rw [hφbar_mk, hφbar_mk]
        change (QuotientGroup.mk (⟨⁅r, rho ^ 2⁆, hmem⟩ : ↥R) : ↥R ⧸ N.subgroupOf R) =
          (QuotientGroup.mk ((⟨r, hr⟩ : ↥R) * (φ (φ (⟨r, hr⟩ : ↥R)))⁻¹) :
            ↥R ⧸ N.subgroupOf R)
        congr 1
        apply Subtype.ext
        change r * rho ^ 2 * r⁻¹ * (rho ^ 2)⁻¹ =
          r * (rho * (rho * r * rho⁻¹) * rho⁻¹)⁻¹
        rw [← commutatorElement_def, fzc_comm_sq_eq]
        simp only [mul_inv_rev, inv_inv]
        group
      rw [hq, map_mul, map_inv, hνφ2]
      simp
  intro x hx
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp (key hx)
  have hνk : ν (QuotientGroup.mk k) = 1 := by
    have h := MonoidHom.mem_ker.mp hkK
    simpa using h
  have hnormk : (k : G) * (rho * (k : G) * rho⁻¹) * (rho⁻¹ * (k : G) * rho) ∈ N := by
    rw [hνnorm k] at hνk
    have hmemmem : ((⟨(k : G) * (rho * (k : G) * rho⁻¹) * (rho⁻¹ * (k : G) * rho),
        hnormmem k⟩ : ↥R) : ↥R ⧸ N.subgroupOf R) = 1 := hνk
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmemmem)
  rw [show (k : G) = x from hkx] at hnormk
  exact hnormk

theorem fzc_sy3_norm_fix {R N : Subgroup G} {rho : G} (hNR : N ≤ R)
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hrR : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R)
    (hrN : ∀ n ∈ N, rho * n * rho⁻¹ ∈ N) (hab : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hrho : rho ^ 3 = 1) {x : G} (hx : x ∈ ⁅R, zpowers rho⁆) (hxr : rho * x = x * rho) :
    x ^ 3 ∈ N := by
  have h := fzc_sy3_norm hNR hRN hrR hrN hab hrho x hx
  have e₁ : rho * x * rho⁻¹ = x := by rw [hxr]; group
  have e₂ : rho⁻¹ * x * rho = x := by
    calc rho⁻¹ * x * rho = rho⁻¹ * (x * rho) := by group
      _ = rho⁻¹ * (rho * x) := by rw [hxr]
      _ = x := by group
  rw [e₁, e₂] at h
  simpa [pow_succ, pow_zero, one_mul, mul_assoc] using h

end CFSG.OddStandard.SmallF3.FritzII
