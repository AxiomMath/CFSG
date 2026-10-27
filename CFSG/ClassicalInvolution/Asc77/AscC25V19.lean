module

public import CFSG.ClassicalInvolution.Asc77.AscC25V12
public import CFSG.ClassicalInvolution.Asc77.AscC25V18

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Strong

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem fieldChar_eq_one_of_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set G)) : fieldChar hp hq e ⟨k, hkN⟩ = 1 := by
  have h := normalizerToPGammaL2Mod_mem_range_inl_of_mem e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 hk hkN
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at h
  exact h

theorem exists_strong_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) {R : Subgroup G} (hR : IsSylow2In R K) :
    ∃ R₁ : Subgroup G, IsSylow2In R₁ K ∧ conjSub b R₁ = R₁ ∧ IsFAut R₁ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hQuat, hcard⟩ := fs_sylow_fixed hp hq h9 e hbN hb2 hσ1 hR
  have hQK : Q ≤ K := fun x hx => (hQ.1 hx).1
  have hQc : ∀ q ∈ Q, q * b = b * q := fun q hq' =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 hq').2
  have hb2g : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_two_zpowers_of_sq hb2
  have hbQ : conjSub b Q = Q := T7F2.conjSub_eq_of_centralizes hQc
  have hbnQ : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_iff_conjSub_eq.mpr hbQ
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers b ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' hb2g hQ.2.1 hbnQ
  have hWK : (Subgroup.zpowers b ⊔ Q) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hbN) (hQK.trans Subgroup.le_normalizer)
  obtain ⟨R₁, hR₁, hR₁W⟩ := exists_sylow_normalized hW2 hWK
  have hb₁ : conjSub b R₁ = R₁ := hR₁W b
    ((le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ Q) (Subgroup.mem_zpowers b))
  have hQR₁ : Q ≤ R₁ := by
    have hQn : Q ≤ Subgroup.normalizer (R₁ : Set G) := fun q hq' =>
      mem_normalizer_iff_conjSub_eq.mpr (hR₁W q ((le_sup_right : Q ≤ Subgroup.zpowers b ⊔ Q) hq'))
    have hP := IsPGroup.to_sup_of_normal_right' hQ.2.1 hR₁.2.1 hQn
    have hle : Q ⊔ R₁ ≤ K := sup_le hQK hR₁.1
    have := hR₁.2.2 (Q ⊔ R₁) hle hP le_sup_right
    rw [← this]
    exact le_sup_left
  have hQeq : R₁ ⊓ Subgroup.centralizer ({b} : Set G) = Q := by
    refine hQ.2.2 _ (inf_le_inf_right _ hR₁.1) (hR₁.2.1.to_le inf_le_left) ?_
    exact le_inf hQR₁ (fun x hx => (hQ.1 hx).2)
  refine ⟨R₁, hR₁, hb₁, ?_⟩
  refine ⟨mem_normalizer_iff_conjSub_eq.mpr hb₁, fun k _ => by rw [hb2, one_mul, mul_one],
    Q, R₁, ?_, hQuat, ⟨le_rfl, hR₁.2.1, fun V' hV'R _ hRV' => le_antisymm hV'R hRV'⟩, ?_⟩
  · rw [hQeq]
    exact ⟨le_rfl, hQ.2.1, fun V' hV'Q _ hQV' => le_antisymm hV'Q hQV'⟩
  · rw [hR₁.natCard_eq hR]
    exact hcard

end Strong

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]


theorem fieldStrong25 : FieldStrong25 p f := by
  intro h9 G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hp hq haK e hσ1
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hfix := fix_of_isFAut h haS hF'
  have haKn : a ∉ K := fun haKm => hσ1 (fieldChar_eq_one_of_mem hp hq e haKm haK)
  have hKa : conjSub a K = K := mem_normalizer_iff_conjSub_eq.mp haK
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj : ∀ {A : Subgroup G}, conjSub a A = A → ∀ x ∈ A, a * x * a ∈ A := by
    intro A hA x hx
    have := conj_mem_conjSub (n := a) hx
    rw [hA, hai] at this
    exact this
  obtain ⟨R₁, hR₁, hR₁a, hF₁⟩ := exists_strong_sylow hp hq h9 e haK ha2 hσ1 h.hRsyl
  obtain ⟨g, hgR, r, hr, hgar⟩ := exists_twist_of_sylow ha2 haKn (hconj hKa) h.hRsyl hR₁
    (hconj hfix.1) (hconj hR₁a)
  refine ⟨r, hr, ?_, ?_⟩
  · calc a * r * (a * r) = (g * a * g⁻¹) * (g * a * g⁻¹) := by rw [hgar]
      _ = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  · have := T7U.isFAut_conjSub hF₁ g
    rw [hgR, hgar] at this
    exact this

theorem mix25_of_ne_nine (h9 : p ^ f ≠ 9) (hfus : Fus25 p f) : Mix25 p f :=
  mix25_of_fusion p f h9 hfus fieldStrong25

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
