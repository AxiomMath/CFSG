module

public import CFSG.GH74.Uniqueness.Section17Assembly
public import CFSG.GH74.Uniqueness.Section171Group

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.not_mem_Z_of_mem_dGrp (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) {y : X}
    (hy : y ∈ M ⊓ conjugate M t) : y ∉ Z := by
  intro hyZ
  have h1 : y ∈ zHull Z (M ⊓ conjugate M t) := Subgroup.subset_closure ⟨hyZ, hy⟩
  rw [S.zHull_dGrp_eq_bot htM, Subgroup.mem_bot] at h1
  have h2 := S.invariant.1 y hyZ
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem ZDSetup.exists_conj_of_involution_dGrp (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M)
    (c : Conf16 Z M) {y : X} (hy : y ∈ c.D) (hy2 : orderOf y = 2) :
    IsConj c.u y ∧ ∃ d ∈ c.D, y = d⁻¹ * c.u * d := by
  obtain ⟨-, -, ⟨-, hcl⟩, -, he⟩ := h166 c
  have hyu : IsConj c.u y := by
    rcases hcl y hy2 with h | h
    · exact absurd (S.invariant.isConj_mem c.hz h.symm) (S.not_mem_Z_of_mem_dGrp c.htM hy)
    · exact h
  refine ⟨hyu, ?_⟩
  obtain ⟨-, hcyc⟩ := he c.D (S.zHull_dGrp_eq_bot c.htM)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let u' : ↥c.D := ⟨c.u, c.hu⟩
  let y' : ↥c.D := ⟨y, hy⟩
  have hu'2 : orderOf u' = 2 := by rw [← Subgroup.orderOf_coe]; exact c.hu2
  have hy'2 : orderOf y' = 2 := by rw [← Subgroup.orderOf_coe]; exact hy2
  have hpg : ∀ a : ↥c.D, orderOf a = 2 → IsPGroup 2 (Subgroup.zpowers a) := fun a ha =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨Su, hSu⟩ := IsPGroup.exists_le_sylow (hpg u' hu'2)
  obtain ⟨Sy, hSy⟩ := IsPGroup.exists_le_sylow (hpg y' hy'2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥c.D Su Sy
  have hgSu : g * u' * g⁻¹ ∈ (Sy : Subgroup ↥c.D) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u', hSu (Subgroup.mem_zpowers u'), by simp [MulAut.conj_apply]⟩
  have hySy : y' ∈ (Sy : Subgroup ↥c.D) := hSy (Subgroup.mem_zpowers y')
  have := hcyc Sy
  have heq : (⟨g * u' * g⁻¹, hgSu⟩ : (Sy : Subgroup ↥c.D)) = ⟨y', hySy⟩ := by
    apply eq_of_orderOf_eq_two_of_isCyclic
    · rw [Subgroup.orderOf_mk]
      exact orderOf_conj_eq hu'2 g
    · rw [Subgroup.orderOf_mk]
      exact hy'2
  have heq' : g * u' * g⁻¹ = y' := congrArg Subtype.val heq
  have h1 := congrArg (fun a : ↥c.D => (a : X)) heq'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hy_eq : y = (g : X) * c.u * (g : X)⁻¹ := h1.symm
  refine ⟨((g⁻¹ : ↥c.D) : X), (g⁻¹).2, ?_⟩
  rw [hy_eq, Subgroup.coe_inv, inv_inv]

theorem ZDSetup.conf_t_sq (S : ZDSetup X Z M) (c : Conf16 Z M) : c.t * c.t = 1 :=
  S.invariant.mul_self_eq_one c.ht

theorem Conf16.u_sq (c : Conf16 Z M) : c.u * c.u = 1 := mul_self_of_orderOf_eq_two c.hu2

theorem Conf16.t_mul_u_comm (c : Conf16 Z M) : c.t * c.u = c.u * c.t :=
  Subgroup.mem_centralizer_singleton_iff.mp c.ht_B

theorem ZDSetup.conf_tu_sq (S : ZDSetup X Z M) (c : Conf16 Z M) :
    (c.t * c.u) * (c.t * c.u) = 1 := by
  calc (c.t * c.u) * (c.t * c.u) = c.t * (c.u * c.t) * c.u := by group
    _ = c.t * (c.t * c.u) * c.u := by rw [← c.t_mul_u_comm]
    _ = (c.t * c.t) * (c.u * c.u) := by group
    _ = 1 := by rw [S.conf_t_sq c, c.u_sq, one_mul]

theorem ZDSetup.conf_tu_orderOf (S : ZDSetup X Z M) (c : Conf16 Z M) :
    orderOf (c.t * c.u) = 2 := by
  have hne : c.t * c.u ≠ 1 := by
    intro h
    apply c.htM
    have : c.t = c.u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact M.inv_mem (Subgroup.mem_inf.mp c.hu).1
  exact orderOf_eq_prime (by rw [pow_two]; exact S.conf_tu_sq c) hne

theorem ZDSetup.isConj_u_tu (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) : IsConj c.u (c.t * c.u) := by
  obtain ⟨-, -, ⟨-, hcl⟩, -, -⟩ := h166 c
  rcases hcl _ (S.conf_tu_orderOf c) with h | h
  swap
  · exact h
  exfalso
  have htuZ : c.t * c.u ∈ Z := S.invariant.isConj_mem c.hz h.symm
  have htB : c.t ∈ centralizer ({c.u} : Set X) := c.ht_B
  have htuB : c.t * c.u ∈ centralizer ({c.u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c.t * c.u * c.u = c.u * c.t * c.u := by rw [c.t_mul_u_comm]
      _ = c.u * (c.t * c.u) := by group
  have hct : c.t ∈ cenHull Z c.u := Subgroup.subset_closure ⟨c.ht, htB⟩
  have hctu : c.t * c.u ∈ cenHull Z c.u := Subgroup.subset_closure ⟨htuZ, htuB⟩
  have hu_mem : c.u ∈ cenHull Z c.u := by
    have h1 := (cenHull Z c.u).mul_mem hct hctu
    have e1 : c.t * (c.t * c.u) = c.u := by rw [← mul_assoc, S.conf_t_sq c, one_mul]
    rwa [e1] at h1
  have hcen : (⟨c.u, hu_mem⟩ : ↥(cenHull Z c.u)) ∈ center ↥(cenHull Z c.u) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgc : (g : X) ∈ centralizer ({c.u} : Set X) :=
      Cor713.zHull_le (Z := Z) (centralizer ({c.u} : Set X)) g.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hgc
  have hcore : c.u ∈ pPrimeCoreIn (cenHull Z c.u) := by
    rw [hB.core]
    exact ⟨_, hcen, rfl⟩
  have hodd := odd_card_pPrimeCoreIn (cenHull Z c.u)
  have hdvd : orderOf c.u ∣ Nat.card (pPrimeCoreIn (cenHull Z c.u)) :=
    Subgroup.orderOf_dvd_natCard _ hcore
  rw [c.hu2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem ZDSetup.exists_conj_of_involution_dt (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M)
    (c : Conf16 Z M) {v : X} (hv2 : orderOf v = 2) (hvD : v * c.t⁻¹ ∈ c.D)
    (hvu : IsConj c.u v) : ∃ d ∈ c.D, v = d⁻¹ * (c.t * c.u) * d := by
  classical
  obtain ⟨-, -, -, -, he⟩ := h166 c
  obtain ⟨⟨N, hND, hNn, hNodd, k, hk⟩, hcyc⟩ := he c.D (S.zHull_dGrp_eq_bot c.htM)
  have ht2 : c.t * c.t = 1 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hvv : v * v = 1 := mul_self_of_orderOf_eq_two hv2
  have htD : c.t ∈ normalizer (c.D : Set X) := mem_normalizer_inf_conjugate ht2
  have hZst := S.prodDisc.isZStarIn_inf_conjugate_sup S.invariant c.ht c.htM
  have hcomm : ∀ d ∈ c.D, d * c.t * d⁻¹ * c.t⁻¹ ∈ pPrimeCoreIn c.D := fun d hd =>
    commutator_mem_pPrimeCoreIn hZst htD hd
  have hNnorm : c.D ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mp hNn
  have hNle : N ≤ pPrimeCoreIn c.D := le_pPrimeCoreIn hND hNnorm hNodd
  have hEdvd : Nat.card (pPrimeCoreIn c.D) ∣ Nat.card N := by
    have h1 : Nat.card (pPrimeCoreIn c.D) ∣ Nat.card c.D :=
      Subgroup.card_dvd_of_le (pPrimeCoreIn_le c.D)
    rw [hk] at h1
    have hc : Nat.Coprime (Nat.card (pPrimeCoreIn c.D)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_left.mpr (odd_card_pPrimeCoreIn c.D)).symm
    exact hc.dvd_of_dvd_mul_right h1
  have hNE : N = pPrimeCoreIn c.D :=
    Subgroup.eq_of_le_of_card_ge hNle (Nat.le_of_dvd Nat.card_pos hEdvd)
  subst hNE
  set E : Subgroup X := pPrimeCoreIn c.D with hE
  have hEn : ∀ x ∈ c.D, ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun x hx e he =>
    (Subgroup.mem_normalizer_iff.mp (pPrimeCoreIn_normalizes c.D hx) e).mp he
  have hEcard : Nat.card ↥(E.subgroupOf c.D) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv
  have hQcyc : IsCyclic (↥c.D ⧸ E.subgroupOf c.D) := by
    refine isCyclic_quotient_of_normal_complement (E.subgroupOf c.D) ?_ (k := k) ?_ hcyc
    · rw [hEcard]
      exact hNodd
    · rw [hEcard]
      exact hk
  have hu_notE : c.u ∉ E := by
    intro huE
    have h1 := Subgroup.orderOf_dvd_natCard E huE
    rw [c.hu2] at h1
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h1)
  have hd : v * c.t⁻¹ ∈ c.D := hvD
  have hvd : v = (v * c.t⁻¹) * c.t := by rw [mul_assoc, inv_mul_cancel, mul_one]
  generalize v * c.t⁻¹ = d at hd hvd
  have hinv : c.t * d * c.t⁻¹ = d⁻¹ := by
    have h := hvv
    rw [hvd] at h
    calc c.t * d * c.t⁻¹ = c.t * d * c.t := by rw [hti]
      _ = d⁻¹ * (d * c.t * (d * c.t)) := by group
      _ = d⁻¹ := by rw [h, mul_one]
  have hdsq : d * d ∈ E := by
    have h1 := hcomm d hd
    have e1 : d * c.t * d⁻¹ * c.t⁻¹ = d * d := by
      calc d * c.t * d⁻¹ * c.t⁻¹ = d * (c.t * d * c.t⁻¹)⁻¹ := by group
        _ = d * d := by rw [hinv, inv_inv]
    rwa [e1] at h1
  have hcase : d ∈ E ∨ d⁻¹ * c.u ∈ E := by
    have : IsCyclic (↥c.D ⧸ E.subgroupOf c.D) := hQcyc
    by_cases h1 : (QuotientGroup.mk (⟨d, hd⟩ : ↥c.D) : ↥c.D ⧸ E.subgroupOf c.D) = 1
    · left
      have h2 : (⟨d, hd⟩ : ↥c.D) ∈ E.subgroupOf c.D :=
        (QuotientGroup.eq_one_iff (N := E.subgroupOf c.D) _).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    · right
      have hsq : (QuotientGroup.mk (⟨d, hd⟩ : ↥c.D) : ↥c.D ⧸ E.subgroupOf c.D) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
        exact hdsq
      have hord1 := orderOf_eq_prime hsq h1
      have hu1 : (QuotientGroup.mk (⟨c.u, c.hu⟩ : ↥c.D) : ↥c.D ⧸ E.subgroupOf c.D) ≠ 1 := by
        intro h
        have h2 : (⟨c.u, c.hu⟩ : ↥c.D) ∈ E.subgroupOf c.D :=
          (QuotientGroup.eq_one_iff (N := E.subgroupOf c.D) _).mp h
        exact hu_notE (Subgroup.mem_subgroupOf.mp h2)
      have hu_sq : (QuotientGroup.mk (⟨c.u, c.hu⟩ : ↥c.D) : ↥c.D ⧸ E.subgroupOf c.D) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
        show c.u * c.u ∈ E
        rw [c.u_sq]
        exact E.one_mem
      have hord2 := orderOf_eq_prime hu_sq hu1
      have heq := eq_of_orderOf_eq_two_of_isCyclic hord1 hord2
      exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp heq)
  have hdodd : ∀ x ∈ E, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard E hx)
  rcases hcase with hdE | hdu
  ·
    exfalso
    obtain ⟨n, hn⟩ := exists_pow_conj_of_inverted (hdodd d hdE) hinv ht2
    have hvt : IsConj c.t v := by
      rw [isConj_iff]
      exact ⟨d ^ n, by rw [hvd, hn]⟩
    have hvZ : v ∈ Z := S.invariant.isConj_mem c.ht hvt.symm
    exact S.not_mem_Z_of_mem_dGrp c.htM c.hu (S.invariant.isConj_mem hvZ hvu)
  ·
    have he1 : d * c.u⁻¹ ∈ E := by
      have h1 := hEn c.u c.hu _ (E.inv_mem hdu)
      have e1 : c.u * (d⁻¹ * c.u)⁻¹ * c.u⁻¹ = d * c.u⁻¹ := by group
      rwa [e1] at h1
    have hvw : v = (d * c.u⁻¹) * (c.t * c.u) := by
      rw [hvd]
      calc d * c.t = d * c.u⁻¹ * (c.u * c.t) := by group
        _ = d * c.u⁻¹ * (c.t * c.u) := by rw [c.t_mul_u_comm]
    have hwsq := S.conf_tu_sq c
    have hwinv : (c.t * c.u) * (d * c.u⁻¹) * (c.t * c.u)⁻¹ = (d * c.u⁻¹)⁻¹ := by
      have hw' : (c.t * c.u)⁻¹ = c.t * c.u := inv_eq_of_mul_eq_one_right hwsq
      have h := hvv
      rw [hvw] at h
      rw [hw']
      calc c.t * c.u * (d * c.u⁻¹) * (c.t * c.u)
          = (d * c.u⁻¹)⁻¹ * ((d * c.u⁻¹) * (c.t * c.u) * ((d * c.u⁻¹) * (c.t * c.u))) := by group
        _ = (d * c.u⁻¹)⁻¹ := by rw [h, mul_one]
    obtain ⟨n, hn⟩ := exists_pow_conj_of_inverted (hdodd _ he1) hwinv hwsq
    refine ⟨((d * c.u⁻¹) ^ n)⁻¹, c.D.inv_mem (c.D.pow_mem (c.D.mul_mem hd (c.D.inv_mem c.hu)) n),
      ?_⟩
    rw [inv_inv, hvw, hn]

end CFSG.GH74.Uniqueness
