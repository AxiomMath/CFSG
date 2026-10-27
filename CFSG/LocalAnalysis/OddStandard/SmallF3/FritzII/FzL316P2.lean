module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma fzl_mem_normalizer_of_conj {Q : Subgroup G} {x : G}
    (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro q
  refine ⟨hx q, ?_⟩
  intro hq
  have h2 : x * (x * q * x⁻¹) * x⁻¹ ∈ Q := hx _ hq
  have h3 : x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ ∈ Q := hx _ h2
  have hx' : x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = q := by
    have h : x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * q * (x * x * x)⁻¹ := by
      group
    rw [h, ← pow_three', hx3]
    group
  rwa [hx'] at h3

private lemma fzl_zpow_conj_mem {Q : Subgroup G} {x : G}
    (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hx3 : x ^ 3 = 1) (k : ℤ) :
    ∀ q ∈ Q, x ^ k * q * (x ^ k)⁻¹ ∈ Q := by
  have hmem : x ∈ Subgroup.normalizer (Q : Set G) := fzl_mem_normalizer_of_conj hx hx3
  have hkmem : x ^ k ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).zpow_mem hmem k
  intro q hq
  exact (Subgroup.mem_set_normalizer_iff.mp hkmem q).mp hq

private lemma fzl_Q_map_conj_eq {Q T : Subgroup G} {x : G} (hx : x ∈ T)
    (hnrm : ∀ g ∈ T, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    Q.map (MulAut.conj x) = Q := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hnrm x hx q hq
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨(↑(MulAut.conj x⁻¹) : G →* G) y, ?_, ?_⟩
    · simpa [MulAut.conj_apply] using hnrm x⁻¹ (T.inv_mem hx) y hy
    · change x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y
      group

private lemma fzl_D_map_conj_tau {rho tau : G} (h : tau * rho = rho * tau) :
    (zpowers rho).map (MulAut.conj tau) = zpowers rho := by
  rw [MonoidHom.map_zpowers]
  have hconj : (↑(MulAut.conj tau) : G →* G) rho = rho := by
    change tau * rho * tau⁻¹ = rho
    rw [h]; group
  rw [hconj]

private lemma fzl_D_map_conj_lam {rho lam : G} (h : lam * rho * lam⁻¹ = rho⁻¹) :
    (zpowers rho).map (MulAut.conj lam) = zpowers rho := by
  rw [MonoidHom.map_zpowers]
  have hconj : (↑(MulAut.conj lam) : G →* G) rho = rho⁻¹ := by
    change lam * rho * lam⁻¹ = rho⁻¹
    exact h
  rw [hconj, Subgroup.zpowers_inv]

private lemma fzl_mem_normalizer_P_of_maps {Q D P : Subgroup G} {x : G} (hPd : P = ⁅Q, D⁆)
    (hQx : Q.map (MulAut.conj x) = Q) (hDx : D.map (MulAut.conj x) = D) :
    x ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hPd, Subgroup.map_commutator, hQx, hDx]

structure FzPFacts (t tau rho : G) (E W Q T P : Subgroup G) : Prop where
  card_P : Nat.card P = 64
  PQ : P ≤ Q
  EP : E ≤ P
  PW : ∀ p ∈ P, p ∈ W → p ∈ E
  Q_eq : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P
  nrm_P_rho : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P
  rho_fpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1
  P_sq : ∀ p ∈ P, p ^ 2 ∈ E
  P_comm : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ E
  nrm_P : ∀ g ∈ T, ∀ p ∈ P, g * p * g⁻¹ ∈ P
  nrm_E : ∀ g ∈ T, ∀ e ∈ E, g * e * g⁻¹ ∈ E
  tau_sq1 : tau ^ 2 = 1

theorem fzl_pfacts {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {P : Subgroup G} (hPd : P = ⁅Q, zpowers rho⁆)
    (htP : t ∉ P) : FzPFacts t tau rho E W Q T P := by
  have hPQ : P ≤ Q := by
    rw [hPd]
    refine Subgroup.commutator_le.mpr ?_
    intro q hq g hg
    rw [Subgroup.mem_zpowers_iff] at hg
    obtain ⟨k, rfl⟩ := hg
    have hconj : rho ^ k * q⁻¹ * (rho ^ k)⁻¹ ∈ Q :=
      fzl_zpow_conj_mem h.rho_nrm_Q h.rho_ord k q⁻¹ (Q.inv_mem hq)
    rw [commutatorElement_def]
    have hmul := Q.mul_mem hq hconj
    simpa [mul_assoc] using hmul
  have hEP : E ≤ P := by
    rw [← h.E_rho, hPd]
    exact Subgroup.commutator_mono h.WQ le_rfl
  have hPW : ∀ p ∈ P, p ∈ W → p ∈ E := by
    intro p hp hpW
    rcases h.W_split p hpW with hE | hE
    · exact hE
    · exfalso
      have ht' : (t * p) * p⁻¹ ∈ P := P.mul_mem (hEP hE) (P.inv_mem hp)
      have htP' : t ∈ P := by simpa [mul_assoc] using ht'
      exact htP htP'
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h.t_sq)
  have hQ_eq : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P := by
    intro q hq
    obtain ⟨c, hcQ, hcfix, hcq⟩ :=
      fzl_coprime_decomp (Q := Q) (rho := rho) (h.pgroup_T.to_le (h.QR.trans h.RT))
        h.rho_ord h.rho_nrm_Q hq
    rw [← hPd] at hcq
    rcases h.rho_Q c hcQ hcfix with hc1 | hct
    · left
      simpa [hc1] using hcq
    · right
      simpa [hct, htinv] using hcq
  have hcard_P : Nat.card P = 64 := by
    have hPidx : P.relIndex Q = 2 :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := P) (K := Q)).mpr
        ⟨t, h.WQ h.t_mem, htP,
          fun b hb => (hQ_eq b hb).elim (fun hbP => Or.inr hbP) (fun hbP => Or.inl hbP)⟩
    have hmul := Subgroup.relIndex_mul_card P Q
    rw [hPidx, inf_eq_left.2 hPQ, h.card_Q] at hmul
    omega
  have hQn : Q ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPd]
    exact Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := zpowers rho)
  have htau_n : tau ∈ Subgroup.normalizer (P : Set G) :=
    fzl_mem_normalizer_P_of_maps (Q := Q) (D := zpowers rho) (P := P) (x := tau) hPd
      (fzl_Q_map_conj_eq (T := T) (h.RT h.tau_R) h.nrm_Q)
      (fzl_D_map_conj_tau h.tau_rho)
  have hlam_n : lam ∈ Subgroup.normalizer (P : Set G) :=
    fzl_mem_normalizer_P_of_maps (Q := Q) (D := zpowers rho) (P := P) (x := lam) hPd
      (fzl_Q_map_conj_eq (T := T) h.lam_T h.nrm_Q)
      (fzl_D_map_conj_lam h.lam_rho)
  have hlamtau_n : lam * tau ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).mul_mem hlam_n htau_n
  have hnrm_P : ∀ g ∈ T, ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro g hg p hp
    have hgn : g ∈ Subgroup.normalizer (P : Set G) := by
      rcases fzl_T_gen h g hg with hgQ | hgQ | hgQ | hgQ
      · exact hQn hgQ
      · have hg' : g = tau * (tau⁻¹ * g) := by group
        rw [hg']
        exact (Subgroup.normalizer (P : Set G)).mul_mem htau_n (hQn hgQ)
      · have hg' : g = lam * (lam⁻¹ * g) := by group
        rw [hg']
        exact (Subgroup.normalizer (P : Set G)).mul_mem hlam_n (hQn hgQ)
      · have hg' : g = (lam * tau) * ((lam * tau)⁻¹ * g) := by group
        rw [hg']
        exact (Subgroup.normalizer (P : Set G)).mul_mem hlamtau_n (hQn hgQ)
    exact (Subgroup.mem_set_normalizer_iff.mp hgn p).mp hp
  have hnrm_P_rho : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P := by
    intro p hp
    have hrho_n : rho ∈ Subgroup.normalizer (P : Set G) := by
      rw [hPd]
      exact Subgroup.normalizer_commutator_ge_right (H₁ := Q) (H₂ := zpowers rho)
        (Subgroup.mem_zpowers rho)
    exact (Subgroup.mem_set_normalizer_iff.mp hrho_n p).mp hp
  have hrho_fpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1 := by
    intro p hp hfix
    rcases h.rho_Q p (hPQ hp) hfix with hp1 | hpt
    · exact hp1
    · exfalso
      exact htP (hpt ▸ hp)
  have hP_sq : ∀ p ∈ P, p ^ 2 ∈ E := by
    intro p hp
    have hp2P : p ^ 2 ∈ P := by rw [pow_two]; exact P.mul_mem hp hp
    have hp2W : p ^ 2 ∈ W := h.R_sq p (h.QR (hPQ hp))
    exact hPW (p ^ 2) hp2P hp2W
  have hP_comm : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ E := by
    intro p hp q hq
    have hpqP : ⁅p, q⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp)) (P.inv_mem hq)
    have hpqW : ⁅p, q⁆ ∈ W := h.R_comm p (h.QR (hPQ hp)) q (h.QR (hPQ hq))
    exact hPW ⁅p, q⁆ hpqP hpqW
  exact
    { card_P := hcard_P
      PQ := hPQ
      EP := hEP
      PW := hPW
      Q_eq := hQ_eq
      nrm_P_rho := hnrm_P_rho
      rho_fpf := hrho_fpf
      P_sq := hP_sq
      P_comm := hP_comm
      nrm_P := hnrm_P
      nrm_E := fzl_nrm_E h
      tau_sq1 := fzl_tau_sq h }

end CFSG.OddStandard.SmallF3.FritzII
