module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPhiZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWGrp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RL2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open Subgroup CFSG.EvenSporadicStandard.Fin76b.LiftRL

section Clauses

variable {M : Type*} [Group M] [Finite M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t z : M}
  {eltE : ℕ → M} {N : Subgroup M}

structure PartIData (D E : Subgroup M) [(D ⊔ E).Normal] (eD : D ≃* DihedralGroup 4) (t : M)
    (eltE : ℕ → M) (N : Subgroup M) (z : M) : Prop where
  ctx : DECtx D E eD t eltE
  oddN : ∀ n ∈ N, Odd (orderOf n)
  ker : Subgroup.centralizer ((D ⊔ E : Subgroup M) : Set M) = N ⊔ Subgroup.zpowers t
  surj : ∀ α : MulAut ↥(D ⊔ E), ∃ m : M, MulAut.conjNormal m = α
  z_sq : z * z = 1
  z_E : ∀ e ∈ E, z * e = e * z
  z_a : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹
  z_b : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4

theorem htF_Pg : ∀ c ∈ Pg, c tF = tF := fun c hc => by
  have h := permVal_tC (pg_le_autC hc)
  rw [permVal_eq _ tC_lt] at h
  exact Fin.ext h

theorem delta_repPg (j : Fin 9) :
    delta (repPg j) = if (j : ℕ) = 4 ∨ (j : ℕ) = 7 ∨ (j : ℕ) = 8 then (-1 : ℤˣ) else 1 :=
  delta_rep j j.2 (repPerm j) (repPerm_mem j.2) (repPerm_rep j.2) (repPerm_sq j.2)

theorem class_lift {Φ : M →* ↥Pg} (hsurj : Function.Surjective Φ) {y : M} (hy2 : y * y = 1)
    (hy1 : Φ y ≠ 1) :
    ∃ (j : Fin 9) (m : M), Φ (m⁻¹ * y * m) = repPg j := by
  have h2 : Φ y * Φ y = 1 := by rw [← map_mul, hy2, map_one]
  obtain ⟨j, c, hjc⟩ := invol_classes pg_le_autC htF_Pg (Φ y) h2 hy1
  obtain ⟨m, hm⟩ := hsurj c
  refine ⟨j, m, ?_⟩
  rw [map_mul, map_mul, map_inv, hm, hjc]
  group

theorem delta_conj (c r : ↥Pg) : delta (c * r * c⁻¹) = delta r := by
  rw [map_mul, map_mul, map_inv, mul_comm (delta c) (delta r), mul_assoc, mul_inv_cancel,
    mul_one]

theorem two_pow_dvd_centTab : ∀ j : Fin 9, (j : ℕ) ≠ 4 → (j : ℕ) ≠ 7 → (j : ℕ) ≠ 8 →
    2 ^ 10 ∣ centTab[(j : ℕ)]! := by decide +kernel

namespace PartIData

variable [hW : (D ⊔ E).Normal] [hN : N.Normal] (h : PartIData D E eD t eltE N z)

include h

theorem Phi_ker : h.ctx.Phi.ker = N ⊔ zpowers t := by rw [h.ctx.Phi_ker]; exact h.ker

theorem Phi_surj : Function.Surjective h.ctx.Phi := h.ctx.Phi_surj h.surj

theorem Phi_z : h.ctx.Phi z = repPg 8 := h.ctx.Phi_z h.z_E h.z_a h.z_b

theorem no_class7 {y' : M} (hy2 : y' * y' = 1) (hΦ : h.ctx.Phi y' = repPg 7) : False := by
  have ht2 := h.ctx.t_sq
  have ht1 := h.ctx.t_ne
  have htc := h.ctx.t_central
  have hzb := h.ctx.Phi_zb h.z_E h.z_a h.z_b
  set b0 := b0Elt eD eltE with hb0
  have hk : (z * b0)⁻¹ * y' ∈ N ⊔ zpowers t := by
    rw [← h.Phi_ker, MonoidHom.mem_ker, map_mul, map_inv, hzb, hΦ, inv_mul_cancel]
  have hy : (z * b0 * ((z * b0)⁻¹ * y')) * (z * b0 * ((z * b0)⁻¹ * y')) = 1 := by
    have e : z * b0 * ((z * b0)⁻¹ * y') = y' := by group
    rw [e]
    exact hy2
  have hNb : ∀ n ∈ N, b0 * n = n * b0 := by
    intro n hn
    have hn' : n ∈ Subgroup.centralizer ((D ⊔ E : Subgroup M) : Set M) := by
      rw [h.ker]
      exact Subgroup.mem_sup_left hn
    exact Subgroup.mem_centralizer_iff.1 hn' b0 (h.ctx.b0_mem)
  exact twist_contra h.oddN ht2 ht1 htc h.z_sq (h.ctx.z_b0 h.z_E h.z_a h.z_b) (h.ctx.b0_sq) hNb hk hy

theorem no_class4 [Fact (Nat.Prime 2)] {y m' : M} (hy2 : y * y = 1)
    (hΦ : h.ctx.Phi (m'⁻¹ * y * m') = repPg 4) {Q : Subgroup M} (hQ : IsPGroup 2 Q)
    (hcard : 512 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set M))) : False := by
  have ht2 := h.ctx.t_sq
  have ht1 := h.ctx.t_ne
  have htc := h.ctx.t_central
  set y' := m'⁻¹ * y * m' with hy'
  have hy'2 : y' * y' = 1 := by
    have : y' * y' = m'⁻¹ * (y * y) * m' := by rw [hy']; group
    rw [this, hy2]
    group
  have hpy : ((h.ctx.Phi y' : ↥Pg) : Equiv.Perm (Fin 128)) = repPerm 4 := by
    rw [hΦ]
    rfl
  obtain ⟨w, hw, hyw⟩ := h.ctx.fus_conj (j := 4) (Or.inl rfl) (by norm_num) hpy
  set w' := m' * w * m'⁻¹ with hw'
  have hyw' : y * w' * y⁻¹ = w' * t := by
    have e1 : y = m' * y' * m'⁻¹ := by rw [hy']; group
    calc y * w' * y⁻¹ = m' * (y' * w * y'⁻¹) * m'⁻¹ := by rw [e1, hw']; group
      _ = m' * (w * t) * m'⁻¹ := by rw [hyw]
      _ = (m' * w * m'⁻¹) * (m' * t * m'⁻¹) := by group
      _ = w' * t := by rw [h.ctx.Phi_t m']
  have hd : w'⁻¹ * y * w'⁻¹⁻¹ = y * t := by
    have h1 : y * w' = w' * t * y := by
      calc y * w' = y * w' * y⁻¹ * y := by group
        _ = w' * t * y := by rw [hyw']
    calc w'⁻¹ * y * w'⁻¹⁻¹ = w'⁻¹ * (y * w') := by group
      _ = w'⁻¹ * (w' * t * y) := by rw [h1]
      _ = t * y := by group
      _ = y * t := (htc y).symm
  have hlift := (lift_cent_dvd h.ctx.Phi h.Phi_surj h.oddN ht2 ht1 htc h.Phi_ker hy2 9).2
    ⟨w'⁻¹, hd⟩
  have hpg : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer ({y} : Set M)) := hQ.to_inf_left
  obtain ⟨a, ha⟩ := hpg.exists_card_eq
  have h9 : 9 ≤ a := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ a ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha] at hcard
    omega
  have hdvd : 2 ^ 9 ∣ Nat.card (Subgroup.centralizer ({y} : Set M)) := by
    have h1 : 2 ^ 9 ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set M)) := by
      rw [ha]
      exact Nat.pow_dvd_pow 2 h9
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hdvd2 := hlift hdvd
  have hΦy : h.ctx.Phi y = (h.ctx.Phi m') * repPg 4 * (h.ctx.Phi m')⁻¹ := by
    rw [← hΦ, map_mul, map_mul, map_inv]
    group
  rw [hΦy, card_centralizer_conj, card_cent (4 : Fin 9)] at hdvd2
  revert hdvd2
  decide +kernel

theorem class8_conj {y' : M} (hy2 : y' * y' = 1) (hΦ : h.ctx.Phi y' = repPg 8) :
    ∃ m : M, y' = m * z * m⁻¹ := by
  have ht2 := h.ctx.t_sq
  have ht1 := h.ctx.t_ne
  have htc := h.ctx.t_central
  have hk : z⁻¹ * y' ∈ N ⊔ zpowers t := by
    rw [← h.Phi_ker, MonoidHom.mem_ker, map_mul, map_inv, h.Phi_z, hΦ, inv_mul_cancel]
  have hpz : ((h.ctx.Phi z : ↥Pg) : Equiv.Perm (Fin 128)) = repPerm 8 := by
    rw [h.Phi_z]
    rfl
  obtain ⟨w, hw, hzw⟩ := h.ctx.fus_conj (j := 8) (Or.inr (Or.inr rfl)) (by norm_num) hpz
  have hy : (z * (z⁻¹ * y')) * (z * (z⁻¹ * y')) = 1 := by
    have e : z * (z⁻¹ * y') = y' := by group
    rw [e]
    exact hy2
  obtain ⟨m, hm⟩ := invol_coset_z_conj ht2 ht1 htc h.oddN h.z_sq hzw hk hy
  refine ⟨m, ?_⟩
  have e : z * (z⁻¹ * y') = y' := by group
  rw [← e]
  exact hm

end PartIData

theorem hom_conj_units {G : Type*} [Group G] (f : G →* ℤˣ) (m y : G) : f (m⁻¹ * y * m) = f y := by
  rw [map_mul, map_mul, map_inv, mul_comm (f m)⁻¹ (f y), mul_assoc, inv_mul_cancel, mul_one]

namespace PartIData

variable [hW : (D ⊔ E).Normal] [hN : N.Normal] (h : PartIData D E eD t eltE N z)

include h

theorem clauses : ∃ Q' P : Subgroup M, IsPGroup 2 Q' ∧ ¬ 2 ∣ Q'.index ∧ z ∈ Q' ∧ P ≤ Q' ∧
    P.relIndex Q' = 2 ∧ z ∉ P ∧
    (∃ R : Subgroup M, IsPGroup 2 R ∧ R ≤ Subgroup.centralizer ({z} : Set M) ∧
      Nat.card R = 512) ∧
    (∀ η ∈ P, η * η = 1 → η ≠ 1 → ∃ R : Subgroup M, IsPGroup 2 R ∧
      R ≤ Subgroup.centralizer ({η} : Set M) ∧ 1024 ≤ Nat.card R) ∧
    (∀ y ∈ Q', y * y = 1 → y ∉ P → 512 ≤ Nat.card ↥(Q' ⊓ Subgroup.centralizer ({y} : Set M)) →
      ∃ m : M, y = m * z * m⁻¹) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := h.ctx.Phi with hΦdef
  have hsurj : Function.Surjective Φ := h.Phi_surj
  have hker : Φ.ker = N ⊔ zpowers t := h.Phi_ker
  have ht2 := h.ctx.t_sq
  have ht1 := h.ctx.t_ne
  have htc := h.ctx.t_central
  have hz2 := h.z_sq
  have hzp : IsPGroup 2 (zpowers z) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  obtain ⟨Qs, hzQ⟩ := hzp.exists_le_sylow
  set Q' : Subgroup M := (Qs : Subgroup M) with hQ'
  have hQ2 : IsPGroup 2 Q' := Qs.isPGroup'
  have hzQ' : z ∈ Q' := hzQ (mem_zpowers z)
  let δ' : M →* ℤˣ := delta.comp Φ
  have hδz : δ' z = -1 := by
    show delta (Φ z) = -1
    rw [h.Phi_z, delta_repPg]
    simp
  let P : Subgroup M := Q' ⊓ δ'.ker
  have hzP : z ∉ P := by
    intro hp
    have h1 : δ' z = 1 := hp.2
    rw [hδz] at h1
    exact absurd h1 (by decide)
  have hrel : P.relIndex Q' = 2 := by
    have hsub : P.subgroupOf Q' = (δ'.comp Q'.subtype).ker := by
      ext x
      simp [P, Subgroup.mem_subgroupOf, x.2]
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    have hrange : (δ'.comp Q'.subtype).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨⟨z, hzQ'⟩, hδz⟩
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  refine ⟨Q', P, hQ2, Qs.not_dvd_index, hzQ', inf_le_left, hrel, hzP, ?_, ?_, ?_⟩
  · obtain ⟨R, hR2, hRc, hRcard⟩ := exists_two_subgroup_cent Φ hsurj h.oddN ht2 ht1 htc hker hz2
      (k := 9) (by
        rw [h.Phi_z, card_cent (8 : Fin 9)]
        decide +kernel)
    exact ⟨R, hR2, hRc, by rw [hRcard]; norm_num⟩
  · intro η hηP hη2 hη1
    have hηδ : δ' η = 1 := hηP.2
    by_cases hηk : η ∈ Φ.ker
    · have hηt : η = t := invol_ker_eq_t h.oddN ht2 ht1 htc (hker ▸ hηk) hη2 hη1
      refine ⟨Q', hQ2, ?_, ?_⟩
      · intro x _
        rw [hηt, Subgroup.mem_centralizer_singleton_iff]
        exact htc x
      · have hcard : Nat.card Q' = 2 ^ (Nat.card M).factorization 2 := Qs.card_eq_multiplicity
        have hdvd : 2 ^ 13 ∣ Nat.card M := by
          have h1 : Nat.card ↥Pg ∣ Nat.card M := Subgroup.card_dvd_of_surjective hsurj
          rw [card_Pg] at h1
          exact (by norm_num : 2 ^ 13 ∣ 3317760).trans h1
        have h13 : 13 ≤ (Nat.card M).factorization 2 :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
        rw [hcard]
        calc 1024 = 2 ^ 10 := by norm_num
          _ ≤ 2 ^ 13 := by norm_num
          _ ≤ 2 ^ (Nat.card M).factorization 2 := Nat.pow_le_pow_right (by norm_num) h13
    · have hΦη2 : Φ η * Φ η = 1 := by rw [← map_mul, hη2, map_one]
      have hΦη1 : Φ η ≠ 1 := fun h1 => hηk (MonoidHom.mem_ker.2 h1)
      obtain ⟨j, c, hjc⟩ := invol_classes pg_le_autC htF_Pg (Φ η) hΦη2 hΦη1
      have hδj : delta (repPg j) = 1 := by
        have h1 : delta (Φ η) = 1 := hηδ
        rw [hjc, delta_conj] at h1
        exact h1
      rw [delta_repPg] at hδj
      have hj4 : (j : ℕ) ≠ 4 ∧ (j : ℕ) ≠ 7 ∧ (j : ℕ) ≠ 8 := by
        by_contra hcon
        have hc : (j : ℕ) = 4 ∨ (j : ℕ) = 7 ∨ (j : ℕ) = 8 := by omega
        rw [if_pos hc] at hδj
        exact absurd hδj (by decide)
      obtain ⟨R, hR2, hRc, hRcard⟩ := exists_two_subgroup_cent Φ hsurj h.oddN ht2 ht1 htc hker
        hη2 (k := 10) (by
          rw [hjc, card_centralizer_conj, card_cent j]
          exact two_pow_dvd_centTab j hj4.1 hj4.2.1 hj4.2.2)
      exact ⟨R, hR2, hRc, by rw [hRcard]; norm_num⟩
  · intro y hyQ hy2 hyP hcard
    have hyδ : δ' y ≠ 1 := fun h1 => hyP ⟨hyQ, h1⟩
    have hyδ' : δ' y = -1 := (Int.units_eq_one_or _).resolve_left hyδ
    have hΦy1 : Φ y ≠ 1 := by
      intro h1
      apply hyδ
      show delta (Φ y) = 1
      rw [h1, map_one]
    obtain ⟨j, m', hm'⟩ := class_lift hsurj hy2 hΦy1
    have hδj : delta (repPg j) = -1 := by
      rw [← hm']
      show δ' (m'⁻¹ * y * m') = -1
      rw [hom_conj_units, hyδ']
    have hjδ : (j : ℕ) = 4 ∨ (j : ℕ) = 7 ∨ (j : ℕ) = 8 := by
      by_contra hcon
      rw [delta_repPg, if_neg hcon] at hδj
      exact absurd hδj (by decide)
    set y' := m'⁻¹ * y * m' with hy'
    have hy'2 : y' * y' = 1 := by
      have : y' * y' = m'⁻¹ * (y * y) * m' := by rw [hy']; group
      rw [this, hy2]
      group
    rcases hjδ with h4 | h7 | h8
    · exfalso
      have hj : j = 4 := Fin.ext h4
      rw [hj] at hm'
      exact h.no_class4 hy2 hm' hQ2 hcard
    · exfalso
      have hj : j = 7 := Fin.ext h7
      rw [hj] at hm'
      exact h.no_class7 hy'2 hm'
    · have hj : j = 8 := Fin.ext h8
      rw [hj] at hm'
      obtain ⟨m'', hm''⟩ := h.class8_conj hy'2 hm'
      refine ⟨m' * m'', ?_⟩
      calc y = m' * y' * m'⁻¹ := by rw [hy']; group
        _ = m' * (m'' * z * m''⁻¹) * m'⁻¹ := by rw [← hm'']
        _ = (m' * m'') * z * (m' * m'')⁻¹ := by group

end PartIData

end Clauses

end CFSG.EvenSporadicStandard.Fin76b.W16
