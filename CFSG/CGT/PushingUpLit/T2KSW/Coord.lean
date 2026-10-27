module

public import CFSG.CGT.PushingUpLit.T2KR.MMCoord

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

abbrev Qc (L M : Subgroup G) : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G)

structure CoordData (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ) where
  D : NatData L n
  nat : NatBlock L n
  le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)

namespace CoordData

variable {L M : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem n_ne_zero : n ≠ 0 := by have := H.nat.two_le; omega

include H in
theorem hcard : Fintype.card (Fq n) = 2 ^ n := card_Fq H.n_ne_zero

include H in
theorem two_lt_card : 2 < Fintype.card (Fq n) := by
  rw [H.hcard]
  have := H.nat.two_le
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

@[expose] noncomputable def twist (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    CoordData G L M n :=
  { H with D := NatData.twist H.D x₀ }

theorem twist_φ (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (l : ↥L) :
    (H.twist x₀).D.φ l = x₀⁻¹ * H.D.φ l * x₀ := by
  show (MulAut.conj x₀⁻¹) (H.D.φ l) = _
  rw [MulAut.conj_apply, inv_inv]

theorem exists_decomp {u : G} (hu : u ∈ Qc L M) :
    ∃ p : (Fin 2 → Fq n) × Fq n, ∀ g, kap H.D u g =
      coboundaryA (mu2 (F := Fq n)) p.1 g + p.2 • f0 g := by
  obtain ⟨B, hB⟩ := exists_sub_mem_B1A (a := n) H.hcard (by have := H.nat.two_le; omega)
    (kappa_mem_Z1A H.nat H.D H.le H.normal hu)
  obtain ⟨w, hw⟩ := hB
  refine ⟨(w, B), fun g => ?_⟩
  have := congrFun hw g
  simp only [Pi.sub_apply, Pi.smul_apply] at this
  show _ = coboundaryA (mu2 (F := Fq n)) w g + B • f0 g
  rw [this]
  abel

include H in
theorem decomp_unique {w w' : Fin 2 → Fq n} {B B' : Fq n}
    (h : ∀ g, coboundaryA (mu2 (F := Fq n)) w g + B • f0 g =
      coboundaryA (mu2 (F := Fq n)) w' g + B' • f0 g) : w = w' ∧ B = B' := by
  have h1 : (B - B') • (f0 : SL2 (Fq n) → Fin 2 → Fq n) ∈ B1A (mu2 (F := Fq n)) := by
    refine ⟨w' - w, ?_⟩
    funext g
    have := h g
    simp only [map_sub, sub_smul, Pi.smul_apply, coboundaryA_apply] at this ⊢
    linear_combination (norm := module) (-1 : Fq n) • this
  have hB : B - B' = 0 := eq_zero_of_smul_f0_mem_B1A H.two_lt_card h1
  have hBB : B = B' := sub_eq_zero.1 hB
  subst hBB
  refine ⟨?_, rfl⟩
  have h2 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (Fq n), g • (w - w') = w - w' := by
    intro g
    have := h g
    simp only [coboundaryA_apply, mu2_apply] at this
    show (g : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec (w - w') = w - w'
    rw [Matrix.mulVec_sub]
    linear_combination (norm := module) this
  exact sub_eq_zero.1 (eq_zero_of_forall_smul_eq h2)

@[expose] noncomputable def decomp (u : ↥(Qc L M)) : (Fin 2 → Fq n) × Fq n :=
  Classical.choose (H.exists_decomp u.2)

@[expose] noncomputable def vco (u : ↥(Qc L M)) : Fin 2 → Fq n := (H.decomp u).1

@[expose] noncomputable def theta (u : ↥(Qc L M)) : Fq n := (H.decomp u).2

theorem kap_eq (u : ↥(Qc L M)) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    kap H.D u g = coboundaryA (mu2 (F := Fq n)) (H.vco u) g + H.theta u • f0 g :=
  Classical.choose_spec (H.exists_decomp u.2) g

theorem vco_mul (u u' : ↥(Qc L M)) : H.vco (u * u') = H.vco u + H.vco u' ∧
    H.theta (u * u') = H.theta u + H.theta u' := by
  refine H.decomp_unique (fun g => ?_)
  rw [← H.kap_eq, map_add, Pi.add_apply, add_smul]
  have h1 : kap H.D ((u * u' : ↥(Qc L M)) : G) g = kap H.D u g + kap H.D u' g :=
    kappa_mul_left H.nat H.D H.normal u.2 u'.2 g
  rw [h1, H.kap_eq u, H.kap_eq u']
  abel

include H in
theorem blockU_le_Qc : blockU L ≤ Qc L M := fun v hv =>
  ⟨H.le (blockU_le L hv), Subgroup.mem_centralizer_iff.2 fun w hw => H.nat.blockU_comm w hw v hv⟩

theorem vco_blockU {v : G} (hv : v ∈ blockU L) :
    H.vco ⟨v, H.blockU_le_Qc hv⟩ = H.D.ψe v ∧ H.theta ⟨v, H.blockU_le_Qc hv⟩ = 0 := by
  refine H.decomp_unique (fun g => ?_)
  rw [← H.kap_eq, zero_smul, add_zero]
  exact kappa_blockU H.D hv g

theorem coords_eq_zero_iff (u : ↥(Qc L M)) :
    (H.vco u = 0 ∧ H.theta u = 0) ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [← kappa_eq_zero_iff H.nat H.D H.le H.normal u.2]
  constructor
  · rintro ⟨h1, h2⟩
    funext g
    rw [H.kap_eq u g, h1, h2]
    simp [coboundaryA_apply]
  · intro h0
    refine H.decomp_unique (w := H.vco u) (B := H.theta u) (w' := 0) (B' := 0) (fun g => ?_)
    rw [← H.kap_eq u g, h0]
    simp [coboundaryA_apply]

theorem coords_eq_of_mul_inv_mem {u u' : ↥(Qc L M)}
    (h : (u : G) * (u' : G)⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    H.vco u = H.vco u' ∧ H.theta u = H.theta u' := by
  have h0 := (H.coords_eq_zero_iff (u * u'⁻¹)).2 (by simpa using h)
  have hm := H.vco_mul (u * u'⁻¹) u'
  rw [inv_mul_cancel_right] at hm
  constructor
  · have := hm.1
    rw [h0.1, zero_add] at this
    exact this
  · have := hm.2
    rw [h0.2, zero_add] at this
    exact this

theorem kap_uMat (u : ↥(Qc L M)) (s : Fq n) :
    kap H.D u (uMat s) = ![s * H.vco u 1 + H.theta u * sqrtF s, 0] := by
  rw [H.kap_eq, f0_uMat]
  funext i
  fin_cases i
  · simp [coboundaryA_apply, mu2_apply, uMat_coe, dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]
  · simp [coboundaryA_apply, mu2_apply, uMat_coe, dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

theorem ψe_delta_uMat (u : ↥(Qc L M)) {x : G} (hx : x ∈ L) {s : Fq n}
    (hφ : H.D.φ ⟨x, hx⟩ = uMat s) :
    H.D.ψe (delta (u : G) x) = ![s * H.vco u 1 + H.theta u * sqrtF s, 0] := by
  rw [← kappa_apply H.nat H.D H.le H.normal u.2 hx, hφ, H.kap_uMat]

theorem ψe_delta_one {u : G} (hu : u ∈ Qc L M) {x : G} (hx : x ∈ L) {s : Fq n}
    (hφ : H.D.φ ⟨x, hx⟩ = uMat s) : H.D.ψe (delta u x) 1 = 0 := by
  have := H.ψe_delta_uMat ⟨u, hu⟩ hx hφ
  rw [this]
  rfl

theorem exists_blockU_of_theta_eq_zero (u : ↥(Qc L M)) (hθ : H.theta u = 0) :
    ∃ v ∈ blockU L, H.D.ψe v = H.vco u ∧ (u : G) * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨v, hv, hψ⟩ := H.D.exists_ψe (H.vco u)
  refine ⟨v, hv, hψ, ?_⟩
  have hvQ : v⁻¹ ∈ Qc L M := (Qc L M).inv_mem (H.blockU_le_Qc hv)
  have hv' := H.vco_blockU (inv_mem hv)
  have hm := H.vco_mul u ⟨v⁻¹, hvQ⟩
  refine (H.coords_eq_zero_iff (u * ⟨v⁻¹, hvQ⟩)).1 ⟨?_, ?_⟩
  · rw [hm.1, hv'.1, H.D.ψe_inv hv, hψ]
    abel
  · rw [hm.2, hv'.2, hθ, add_zero]

theorem theta_eq_zero_iff (u : ↥(Qc L M)) :
    H.theta u = 0 ↔ ∃ v ∈ blockU L, (u : G) * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro hθ
    obtain ⟨v, hv, -, hc⟩ := H.exists_blockU_of_theta_eq_zero u hθ
    exact ⟨v, hv, hc⟩
  · rintro ⟨v, hv, hc⟩
    have hvQ : v ∈ Qc L M := H.blockU_le_Qc hv
    have h1 := H.coords_eq_of_mul_inv_mem (u := u) (u' := ⟨v, hvQ⟩) hc
    rw [h1.2]
    exact (H.vco_blockU hv).2

theorem exists_blockU_of_two_roots (u : ↥(Qc L M)) {x₁ x₂ : G} (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L)
    {s₁ s₂ : Fq n} (hφ₁ : H.D.φ ⟨x₁, hx₁⟩ = uMat s₁) (hφ₂ : H.D.φ ⟨x₂, hx₂⟩ = uMat s₂)
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h12 : s₁ ≠ s₂) (hc₁ : H.D.ψe (delta (u : G) x₁) = 0)
    (hc₂ : H.D.ψe (delta (u : G) x₂) = 0) :
    ∃ v ∈ blockU L, H.D.ψe v 1 = 0 ∧ (u : G) * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have e₁ := congrFun ((H.ψe_delta_uMat u hx₁ hφ₁).symm.trans hc₁) 0
  have e₂ := congrFun ((H.ψe_delta_uMat u hx₂ hφ₂).symm.trans hc₂) 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at e₁ e₂
  obtain ⟨hw, hθ⟩ := two_roots_algebra h₁ h₂ h12 e₁ e₂
  obtain ⟨v, hv, hψ, hc⟩ := H.exists_blockU_of_theta_eq_zero u hθ
  exact ⟨v, hv, by rw [hψ]; exact hw, hc⟩

end CoordData

namespace Aux

omit [Finite G] in
theorem uMat_mul_self {n : ℕ} (s : Fq n) : uMat s * uMat s = 1 := by
  rw [uMat_mul, add_self_F, uMat_zero]

theorem exists_rootGrp_of_isPGroup {F : Type} [Field F] [Finite F] {f : ℕ}
    (hf : Nat.card F = 2 ^ f) {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hXp : IsPGroup 2 X) : ∃ p : ℙ F (Fin 2 → F), X ≤ rootGrp p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf1 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hf
    omega
  have hP : Nat.card P.toSubgroup = Nat.card F := by
    rw [P.card_eq_multiplicity, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hf]
    have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf1) two_ne_zero
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf1)
      nlinarith
    have hodd : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by omega
    have hne : (2 ^ f) ^ 2 - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  obtain ⟨p, hp⟩ := exists_point_eq_rootGrp Nat.prime_two hf (P := P.toSubgroup) hP
  exact ⟨p, hXP.trans hp.le⟩

end Aux

open Aux

namespace CoordData

variable {L M : Subgroup G} {n : ℕ}

abbrev Adapted (H : CoordData G L M n) (T : Subgroup G) : Prop :=
  ∀ r (hr : r ∈ L), r ∈ T → ∃ s : Fq n, H.D.φ ⟨r, hr⟩ = uMat s

theorem sq_mem_oTwoIn_of_utri (H : CoordData G L M n) {r : G} (hr : r ∈ L) {s : Fq n}
    (hs : H.D.φ ⟨r, hr⟩ = uMat s) : r ^ 2 ∈ oTwoIn L := by
  have e : (⟨r ^ 2, L.pow_mem hr 2⟩ : ↥L) = ⟨r, hr⟩ * ⟨r, hr⟩ := Subtype.ext (pow_two r)
  refine (H.D.φ_ker ⟨r ^ 2, L.pow_mem hr 2⟩).1 ?_
  rw [e, map_mul, hs, uMat_mul_self]

end CoordData

theorem exists_utri_coord {L M T : Subgroup G} {n : ℕ} (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    ∃ H : CoordData G L M n, H.Adapted T := by
  let H₀ : CoordData G L M n := ⟨h.natData, h, hLM, hMN⟩
  have hn : n ≠ 0 := H₀.n_ne_zero
  have hXp : IsPGroup 2 (((T ⊓ L).subgroupOf L).map H₀.D.φ) :=
    ((hT.isPGroup.to_le (inf_le_left : T ⊓ L ≤ T)).comap_subtype (K := L)).map H₀.D.φ
  obtain ⟨p, hp⟩ := exists_rootGrp_of_isPGroup (f := n) (GaloisField.card 2 n hn) hXp
  obtain ⟨g, rfl⟩ := exists_smul_pt0 p
  refine ⟨H₀.twist g, fun r hr hrT => ?_⟩
  have h1 : H₀.D.φ ⟨r, hr⟩ ∈ rootGrp (g • (pt0 : ℙ (Fq n) (Fin 2 → Fq n))) :=
    hp ⟨⟨r, hr⟩, Subgroup.mem_subgroupOf.2 ⟨hrT, hr⟩, rfl⟩
  rw [mem_rootGrp_smul_iff, rootGrp_pt0] at h1
  obtain ⟨t, ht⟩ := h1
  refine ⟨Multiplicative.toAdd t, ?_⟩
  rw [H₀.twist_φ]
  exact ht.symm

end CFSG.CGT.PushingUpLit.T2KSW
