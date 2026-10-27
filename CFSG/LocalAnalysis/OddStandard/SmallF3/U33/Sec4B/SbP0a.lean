module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma p0_conj_zpow_inv {ρ lam : G} (hlam : lam * ρ * lam⁻¹ = ρ⁻¹) (k : ℤ) :
    lam * ρ ^ k * lam⁻¹ = ρ ^ (-k) := by
  rw [← conj_zpow, hlam, inv_zpow']

private lemma p0_mem_normalizer_zpowers_of_inv {ρ lam : G} (hlam2 : lam ^ 2 = 1)
    (hlam : lam * ρ * lam⁻¹ = ρ⁻¹) :
    lam ∈ Subgroup.normalizer ((zpowers ρ : Subgroup G) : Set G) := by
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hlam2)
  refine (Subgroup.mem_normalizer_iff).mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    rw [← hk, p0_conj_zpow_inv hlam k]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    calc ρ ^ (-k) = lam * ρ ^ k * lam⁻¹ := (p0_conj_zpow_inv hlam k).symm
      _ = lam⁻¹ * ρ ^ k * lam := by rw [hlinv]
      _ = h := by rw [hk]; group

theorem p0_ncard_tM (hc : Ctx8 t L S x₁ x₂ lam rho tau) :
    (conjIn (ctxM t tau x₁ x₂) t).ncard = 8 := by
  have hV : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
    change Nat.card ↥(fourGrp x₁ x₂) = 4
    exact (hc.wreath.fourGrp_eq_omega).2.2
  have hdisj : Disjoint (t • (fourGrp x₁ x₂ : Set G))
      ((t * tau) • (fourGrp x₁ x₂ : Set G)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_smul_set] at hu hu'
    obtain ⟨v, hv, rfl⟩ := hu
    obtain ⟨v', hv', hEq⟩ := hu'
    have h2 : tau * v' = v := by
      have hEq' : t * (tau * v') = t * v := by simpa [mul_assoc] using hEq
      exact mul_left_cancel hEq'
    have htauV : tau ∈ fourGrp x₁ x₂ := by
      have h3 : tau = v * v'⁻¹ := by rw [← h2]; group
      rw [h3]
      exact mul_mem hv (inv_mem hv')
    exact l12_tau_not_mem_V hc.toCtx10.toCtx4 htauV
  rw [hc.tM, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_smul_set, Set.ncard_smul_set, hV]

theorem p0_CMt_eq (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) =
      ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := by
  simpa [invCent, inf_comm] using S4A.normalizer_X_of hc.toCtx hc.l43 hc.l44.1

theorem p0_card_rho_lam_le (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(closure ({rho, lam} : Set G)) ≤ 6 := by
  have hset : ({rho, lam} : Set G) = ({rho} : Set G) ∪ ({lam} : Set G) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  have hsup : closure ({rho, lam} : Set G) = zpowers rho ⊔ zpowers lam := by
    simp only [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
  rw [hsup]
  have hlamN : lam ∈ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) :=
    p0_mem_normalizer_zpowers_of_inv
      (by simpa [hc.wreath.ord_lam] using pow_orderOf_eq_one lam) hc.lam_rho
  have hlep : zpowers lam ≤ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hlamN
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ zpowers rho, k * h * k⁻¹ ∈ zpowers rho := by
    intro k hk h hh
    exact (Subgroup.mem_normalizer_iff.mp (hlep hk) h).mp hh
  have hsurj : Function.Surjective
      (fun p : ↥(zpowers rho) × ↥(zpowers lam) =>
        (⟨(p.1 : G) * (p.2 : G),
          Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(zpowers rho ⊔ zpowers lam))) := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ :=
      (mem_sup_iff_of_normalizes (H := zpowers rho) (K := zpowers lam) hnorm).mp x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at hle
  calc Nat.card ↥(zpowers rho ⊔ zpowers lam)
      ≤ Nat.card ↥(zpowers rho) * Nat.card ↥(zpowers lam) := hle
    _ = 3 * 2 := by rw [Nat.card_zpowers, Nat.card_zpowers, hc.ord_rho, hc.wreath.ord_lam]
    _ = 6 := by norm_num

theorem p0_card_CMt_le (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) ≤ 384 := by
  set N0 : Subgroup G := ctxW t x₁ x₂ ⊔ zpowers tau with hN0
  set A : Subgroup G := closure ({rho, lam} : Set G) with hA
  have hCeq : ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) = N0 ⊔ A := by
    rw [p0_CMt_eq hc]
    show ctxW t x₁ x₂ ⊔ closure ({tau, rho, lam} : Set G) = N0 ⊔ A
    have hcl : closure ({tau, rho, lam} : Set G) = zpowers tau ⊔ A := by
      have hset : ({tau, rho, lam} : Set G) = ({tau} : Set G) ∪ ({rho, lam} : Set G) := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure, hA]
    rw [hcl, ← sup_assoc, hN0]
  have hA_norm : ∀ k ∈ A, ∀ h ∈ N0, k * h * k⁻¹ ∈ N0 := by
    intro k hk h hh
    have hkC : k ∈ invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [hc.norm_baseGrp]
      exact Subgroup.mem_sup_right
        (Subgroup.closure_mono (by
          intro a ha
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
          tauto) hk)
    exact hc.normal_norm.2 k hkC h hh
  have hsurj : Function.Surjective
      (fun p : ↥N0 × ↥A =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(N0 ⊔ A))) := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ :=
      (mem_sup_iff_of_normalizes (H := N0) (K := A) hA_norm).mp x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at hle
  have hcardN0 : Nat.card ↥N0 = 2 ^ 6 := by rw [hN0]; exact l12_card_W_tau hc
  have hcardA : Nat.card ↥A ≤ 6 := by rw [hA]; exact p0_card_rho_lam_le hc
  calc Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G))
      = Nat.card ↥(N0 ⊔ A) := by rw [hCeq]
    _ ≤ Nat.card ↥N0 * Nat.card ↥A := hle
    _ ≤ 2 ^ 6 * 6 := Nat.mul_le_mul (le_of_eq hcardN0) hcardA
    _ = 384 := by norm_num

theorem p0_dvd_CMt (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    384 ∣ Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) := by
  have hSle : S ≤ ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) := by
    rw [p0_CMt_eq hc, hc.S_eq]
    apply sup_le
    · exact (le_sup_left : twoCore t ≤ ctxW t x₁ x₂).trans le_sup_left
    rw [m12Grp]
    refine (Subgroup.closure_le
      (K := ctxW t x₁ x₂ ⊔ closure ({tau, rho, lam} : Set G))).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hScard : Nat.card ↥S = 2 ^ 7 := by
    rw [hc.card_S, hc.l43, Nat.card_zpowers, hc.hyp.ord_t]
    norm_num
  have h2dvd : 2 ^ 7 ∣ Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSle
  have hrhoC : rho ∈ ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) := by
    rw [p0_CMt_eq hc]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have h3dvd : 3 ∣ Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) := by
    have h := Subgroup.orderOf_dvd_natCard (ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) hrhoC
    rwa [hc.ord_rho] at h
  have hcop : Nat.Coprime (2 ^ 7) 3 := by decide
  have h := hcop.mul_dvd_of_dvd_of_dvd h2dvd h3dvd
  norm_num at h
  exact h

theorem p0_card_CMt (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) = 384 := by
  have hle := p0_card_CMt_le hc
  have hdvd := p0_dvd_CMt hc
  have hpos : 0 < Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) := Nat.card_pos
  exact le_antisymm hle (Nat.le_of_dvd hpos hdvd)

theorem p0_card_M (hc : Ctx8 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxM t tau x₁ x₂) = 3 * 2 ^ 10 := by
  have h := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) t
  rw [p0_ncard_tM hc, p0_card_CMt hc.toCtx10.toCtx4] at h
  rw [h]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
