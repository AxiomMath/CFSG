module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11P
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4S9
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9d

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem card_centralizer_conj_nine {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.LieModel Y .PSL 2 3 2) (y₀ : Y) (hy₀ : orderOf y₀ = 2) :
    Nat.card (centralizer ({MulAut.conj y₀} : Set (MulAut Y))) = 32 := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hY
  have hodd := AutL2Facts.isOddPrimePower_of Nat.prime_three (by norm_num) (by norm_num) hF
  have hsq := AutL2Facts.isSquare_neg_one_of_card_sq (f := 1) Nat.prime_three (by norm_num) hF
  obtain ⟨φ⟩ := AutL2Facts.nonempty_stabilizer_equiv e hodd hsq y₀ hy₀
  have h2 := AutL2Facts.two_ne_zero_of_isOddPrimePower hodd
  have heq : centralizer ({MulAut.conj y₀} : Set (MulAut Y)) =
      MulAction.stabilizer (MulAut Y) y₀ := by
    ext α
    rw [CatFactsL4U4.Cat81.mem_centralizer_conj_iff e, MulAction.mem_stabilizer_iff,
      MulAut.smul_def]
  rw [heq, Nat.card_congr φ.toEquiv, AutL2Facts.card_centralizer_tor_neg_one h2,
    Nat.card_units, hF, AutL2Facts.card_ringAut F Nat.prime_three hF]
  norm_num

theorem X11.two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A < B) : 2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAB.le
  have hlt := Subgroup.card_lt_of_lt hAB
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases k with _ | _ | k
  · rw [hk] at hlt
    omega
  · rw [hk] at hlt
    omega
  · rw [hk]
    nlinarith

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem rhoS_z_eq : rhoS (h.toHyp52.D_le_S d.z_D) =
    MulAut.conj (((⟨d.z, d.z_mem_J⟩ : ↥h.J) : ↥h.J ⧸ pPrimeCore 2 ↥h.J)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H l => rfl

noncomputable abbrev rhoHom (h : Hyp59 H) : ↥h.S →* MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
  (Eight.oddBarAction h.J).comp (Subgroup.inclusion h.toHyp52.S_le_normalizer)

include d in
theorem card_S_le (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2) :
    Nat.card h.S ≤ 32 * Nat.card h.P := by
  set zb : ↥h.J ⧸ pPrimeCore 2 ↥h.J := ((⟨d.z, d.z_mem_J⟩ : ↥h.J) : ↥h.J ⧸ pPrimeCore 2 ↥h.J)
    with hzb
  have hker : (rhoHom h).ker = h.P.subgroupOf h.S := by
    ext ⟨s, hs⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact rho_eq_one_iff hs
  have hrange : (rhoHom h).range ≤
      centralizer ({MulAut.conj zb} : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, hzb, ← rhoS_z_eq d]
    show rhoS hs * rhoS (h.toHyp52.D_le_S d.z_D) = rhoS (h.toHyp52.D_le_S d.z_D) * rhoS hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.comm_z_of_mem_S hs)
  have h1 := Subgroup.card_le_of_le hrange
  rw [card_centralizer_conj_nine hJ _ d.orderOf_zbar] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (rhoHom h).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (rhoHom h)).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : h.P ≤ h.S)).toEquiv] at h2
  rw [h2]
  exact Nat.mul_le_mul_right _ h1

variable {d}

variable {v : H} (hv : d.IsV v) (I : In81) (hst : d.Stage7 v)
include hv I hst

theorem four_mul_card_le_card_S :
    4 * (Nat.card h.P * Nat.card h.P) ≤ Nat.card h.S := by
  have F := hst.facts
  have hσF := sigma_mem_F I F
  have hvF : v ∈ normalizer (h.F32 : Set H) := h.normalizer_S_le_normalizer_F32 hv.mem_N
  have hPvF : conjugate h.P v ≤ h.F32 := fun q hq =>
    (mem_normalizer_iff.mp hvF q).mpr (hst.P_le_F (mem_conjugate_iff.mp hq))
  have hPPvF : h.PPv v ≤ h.F32 := sup_le hst.P_le_F hPvF
  have hσ : d.sigma ∉ h.PPv v := fun hσ =>
    asigma_not_mem_PPv hv I hst (mul_mem (mem_sup_left h.toHyp52.a_mem_P) hσ)
  have h1 : h.PPv v < h.PPv v ⊔ zpowers d.sigma :=
    lt_of_le_of_ne le_sup_left fun he => hσ (he ▸ mem_sup_right (mem_zpowers _))
  have h2 : h.PPv v ⊔ zpowers d.sigma ≤ h.F32 := sup_le hPPvF (zpowers_le.mpr hσF)
  obtain ⟨y, hyS, -, -, hyσ, -, -⟩ := hst.y
  have hyF : y ∉ h.F32 := by
    intro hyF
    have hc := mem_centralizer_singleton_iff.mp (d.F32_le_centralizer_sigma I.rk I.j I.c I.b1
      I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F hyF)
    have : y⁻¹ * d.sigma * y = d.sigma := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [hyσ] at this
    apply d.z_ne_a
    have hz := d.z_mul_self
    calc d.z = d.z * (h.a * d.z * d.sigma * d.sigma⁻¹) := by
          rw [this, mul_inv_cancel, mul_one]
      _ = d.z * (h.a * d.z) := by rw [mul_inv_cancel_right]
      _ = h.a := by rw [← mul_assoc, d.z_comm_a, mul_assoc, hz, mul_one]
  have h3 : h.F32 < h.F32 ⊔ zpowers y :=
    lt_of_le_of_ne le_sup_left fun he => hyF (he ▸ mem_sup_right (mem_zpowers _))
  have h4 : h.F32 ⊔ zpowers y ≤ h.S := sup_le h.F32_le_S (zpowers_le.mpr hyS)
  have c1 := X11.two_mul_card_le_of_lt h1
  have c2 := Subgroup.card_le_of_le h2
  have c3 := X11.two_mul_card_le_of_lt h3
  have c4 := Subgroup.card_le_of_le h4
  rw [card_PPv hv] at c1
  omega

theorem card_P_eq_and_card_S (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2) :
    Nat.card h.P = 8 ∧ Nat.card h.S = 4 * (Nat.card h.P * Nat.card h.P) := by
  have h1 := four_mul_card_le_card_S hv I hst
  have h2 := card_S_le d hJ
  have h3 := H₁.eight_le
  have h4 : Nat.card h.P ≤ 8 := by nlinarith
  have h5 : Nat.card h.P = 8 := le_antisymm h4 h3
  refine ⟨h5, ?_⟩
  rw [h5] at h1 h2 ⊢
  omega

theorem commutator_mem_PPv (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2)
    {s t : H} (hs : s ∈ h.S) (ht : t ∈ h.S) : s * t * s⁻¹ * t⁻¹ ∈ h.PPv v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥h.S := (h.PPv v).subgroupOf h.S with hM
  have hMn : M.Normal := ⟨fun x hx g => by
    rw [hM, mem_subgroupOf] at hx ⊢
    exact conj_mem_PPv hv g.2 hx⟩
  obtain ⟨hP8, hS⟩ := card_P_eq_and_card_S hv I hst hJ
  have hcardM : Nat.card M = Nat.card h.P * Nat.card h.P := by
    rw [hM, Nat.card_congr (subgroupOfEquivOfLe (PPv_le_S hv)).toEquiv, card_PPv hv]
  have hQ : Nat.card (↥h.S ⧸ M) = 2 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    rw [hcardM, hS, hP8] at h1
    rw [hP8] at hcardM
    omega
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm
    (QuotientGroup.mk (⟨s, hs⟩ : ↥h.S)) (QuotientGroup.mk (⟨t, ht⟩ : ↥h.S))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
  rw [hM, mem_subgroupOf] at hcomm
  have e : (((⟨s, hs⟩ * ⟨t, ht⟩ : ↥h.S)⁻¹ * (⟨t, ht⟩ * ⟨s, hs⟩) : ↥h.S) : H) =
      (s * t)⁻¹ * (t * s) := rfl
  rw [e] at hcomm
  have h2 := conj_mem_PPv hv (mul_mem hs ht) (inv_mem hcomm)
  rwa [show s * t * ((s * t)⁻¹ * (t * s))⁻¹ * (s * t)⁻¹ = s * t * s⁻¹ * t⁻¹ by group] at h2

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
