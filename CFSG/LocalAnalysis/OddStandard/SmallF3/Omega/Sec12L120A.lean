module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12ED

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

private theorem sec120_mem_P_iff {p : G} :
    p ∈ secCMB t S L ↔ p ∈ secM t S L ∧ p ∈ centralizer (secB S L : Set G) := by
  rw [secCMB, Subgroup.mem_inf]

theorem sec120_t_not_mem_L (F : Sec12Frame t L S) : t ∉ L := by
  intro htL
  have hmem : t ∈ L ⊓ centralizer (L : Set G) := ⟨htL, F.htC⟩
  rw [F.hLC] at hmem
  have ht1 : t = 1 := Subgroup.mem_bot.mp hmem
  have hord : orderOf t = 1 := by rw [ht1, orderOf_one]
  have h2 : (2 : ℕ) = 1 := by rw [← F.ht2, hord]
  exact absurd h2 (by decide)

theorem sec120_unique (F : Sec12Frame t L S) {E Q : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) (hQ : IsSylow2Of Q (secCMB t S L)) : Q = E := by
  obtain ⟨a, haP, ha⟩ := IsSylow2Of.exists_conj_mem hE hQ
  have haM : a ∈ secM t S L := (sec120_mem_P_iff.mp haP).1
  have hnorm : a⁻¹ ∈ normalizer (E : Set G) :=
    sec12E_sylow_normal F hE ((secM t S L).inv_mem haM)
  have ha' : ∀ x : G, x ∈ E ↔ a⁻¹ * x * a ∈ E := by
    intro x
    simpa using (Subgroup.mem_normalizer_iff.mp hnorm) x
  ext x
  exact (ha x).trans (ha' x).symm

theorem sec120_two_le_E (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {p : G} (hp : p ∈ secCMB t S L)
    (h2 : ∃ k : ℕ, p ^ (2 ^ k) = 1) : p ∈ E := by
  obtain ⟨k, hk⟩ := h2
  have hP2 : IsPGroup 2 (zpowers p : Subgroup G) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hzp : (zpowers p : Subgroup G) ≤ secCMB t S L := by
    rw [Subgroup.zpowers_le]
    exact hp
  obtain ⟨Q, hQ, hle⟩ := exists_isSylow2Of_ge hP2 hzp
  have hQE : Q = E := sec120_unique F hE hQ
  have hpQ : p ∈ Q := hle (Subgroup.mem_zpowers p)
  rwa [hQE] at hpQ

theorem sec120_P_eq_ER (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {p : G} (hp : p ∈ secCMB t S L) :
    ∃ e ∈ E, ∃ r ∈ secR t, p = e * r := by
  obtain ⟨e, m, hm, hm0⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p).ne'
  have hcop : Nat.Coprime m (2 ^ e) := hm.coprime_two_right.pow_right e
  obtain ⟨x, y, hxy⟩ := hcop.isCoprime
  let u : G := p ^ (x * (m : ℤ))
  let v : G := p ^ (y * ((2 ^ e : ℕ) : ℤ))
  have huP : u ∈ secCMB t S L := (secCMB t S L).zpow_mem hp (x * (m : ℤ))
  have hvP : v ∈ secCMB t S L := (secCMB t S L).zpow_mem hp (y * ((2 ^ e : ℕ) : ℤ))
  have huv : u * v = p := by
    change p ^ (x * (m : ℤ)) * p ^ (y * ((2 ^ e : ℕ) : ℤ)) = p
    rw [← zpow_add, hxy, zpow_one]
  have hu2 : u ^ (2 ^ e) = 1 := by
    change (p ^ (x * (m : ℤ))) ^ (2 ^ e) = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hint : (x * (m : ℤ)) * ((2 ^ e : ℕ) : ℤ) = x * (orderOf p : ℤ) := by
      rw [hm0, Nat.cast_mul]; ring
    rw [hint, zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hv : v ^ m = 1 := by
    change (p ^ (y * ((2 ^ e : ℕ) : ℤ))) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hint : (y * ((2 ^ e : ℕ) : ℤ)) * (m : ℤ) = y * (orderOf p : ℤ) := by
      rw [hm0, Nat.cast_mul]; ring
    rw [hint, zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have huE : u ∈ E := sec120_two_le_E F hE huP ⟨e, hu2⟩
  have hoddv : Odd (orderOf v) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hv)
  have hcop4 : Nat.Coprime (orderOf v) 4 := by
    simpa using hoddv.coprime_two_right.pow_right 2
  have hvR : v ∈ secR t := by
    obtain ⟨a, b, hab⟩ := hcop4.symm.isCoprime
    have hv4R : v ^ 4 ∈ secR t := sec12E_pow_four F hvP
    have hv_eq : v = (v ^ 4) ^ a := by
      have h4 : v ^ ((4 : ℕ) : ℤ) = v ^ (4 : ℕ) := zpow_natCast v 4
      have hord : v ^ ((orderOf v : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast]; exact pow_orderOf_eq_one v
      calc v = v ^ (1 : ℤ) := by rw [zpow_one]
        _ = v ^ (a * ((4 : ℕ) : ℤ) + b * ((orderOf v : ℕ) : ℤ)) := by rw [hab.symm]
        _ = v ^ (a * ((4 : ℕ) : ℤ)) * v ^ (b * ((orderOf v : ℕ) : ℤ)) := by
              rw [zpow_add]
        _ = (v ^ ((4 : ℕ) : ℤ)) ^ a * (v ^ ((orderOf v : ℕ) : ℤ)) ^ b := by
              rw [zpow_mul', zpow_mul']
        _ = (v ^ 4) ^ a * 1 ^ b := by rw [h4, hord]
        _ = (v ^ 4) ^ a := by rw [one_zpow, mul_one]
    rw [hv_eq]
    exact (secR t).zpow_mem hv4R a
  exact ⟨u, huE, v, hvR, huv.symm⟩

theorem sec120_A_le_E (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) : secA t S L ≤ E := by
  intro a ha
  exact sec120_two_le_E F hE (sec12E_A_le_P F ha)
    ⟨1, by rw [pow_one, pow_two, sec12E_A_sq F ha]⟩

theorem sec120_E_inf_C (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) :
    E ⊓ centralizer (secA t S L : Set G) = secA t S L := by
  apply le_antisymm
  · intro e he
    obtain ⟨heE, heC⟩ := Subgroup.mem_inf.mp he
    obtain ⟨k, hk⟩ := hE.2.1 ⟨e, heE⟩
    exact sec12E_two_C F heC ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro a ha
    exact Subgroup.mem_inf.mpr
      ⟨sec120_A_le_E F hE ha,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => sec12E_A_comm F hx ha)⟩

theorem sec120_f_eq_one_iff (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {e : G} (he : e ∈ E) :
    sec12f t e = 1 ↔ e ∈ secA t S L := by
  rw [sec12E_f_eq_one F (hE.1 he)]
  constructor
  · intro hC
    have hmem : e ∈ E ⊓ centralizer (secA t S L : Set G) :=
      Subgroup.mem_inf.mpr ⟨he, hC⟩
    rw [sec120_E_inf_C F hE] at hmem
    exact hmem
  · intro heA
    have hmem : e ∈ E ⊓ centralizer (secA t S L : Set G) := by
      rw [sec120_E_inf_C F hE]
      exact heA
    exact hmem.2

theorem sec120_f_surj_E (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {b : G} (hb : b ∈ secB S L) :
    ∃ e ∈ E, sec12f t e = b := by
  obtain ⟨p, hpP, hfp⟩ := sec12E_f_surj F hb
  obtain ⟨e, heE, r, hr, hpe⟩ := sec120_P_eq_ER F hE hpP
  refine ⟨e, heE, ?_⟩
  have heP : e ∈ secCMB t S L := hE.1 heE
  have hrC : r ∈ centralizer (secA t S L : Set G) := sec12E_R_le_C F hr
  have hrP : r ∈ secCMB t S L := sec12E_C_le_P F hrC
  have hmul : sec12f t p = sec12f t e * sec12f t r := by
    rw [hpe, sec12E_f_mul F heP hrP]
  have hfr : sec12f t r = 1 := (sec12E_f_eq_one F hrP).mpr hrC
  rw [← hfp, hmul, hfr, mul_one]

theorem sec120_inv_mul_mem_A (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {e e' : G} (he : e ∈ E) (he' : e' ∈ E)
    (h : sec12f t e = sec12f t e') : e⁻¹ * e' ∈ secA t S L := by
  have heP : e ∈ secCMB t S L := hE.1 he
  have he'P : e' ∈ secCMB t S L := hE.1 he'
  have hinvP : e⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem heP
  have hinv : sec12f t e⁻¹ = (sec12f t e)⁻¹ := by
    have hm := sec12E_f_mul F hinvP heP
    have h1 : sec12f t e⁻¹ * sec12f t e = 1 := by
      rw [← hm, inv_mul_cancel]
      simp [sec12f]
    exact eq_inv_of_mul_eq_one_left h1
  have hmemE : e⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem he) he'
  apply (sec120_f_eq_one_iff F hE hmemE).mp
  rw [sec12E_f_mul F hinvP he'P, hinv, h, inv_mul_cancel]

theorem sec120_sq_mem_B (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {e : G} (he : e ∈ E) : e * e ∈ secB S L := by
  have heP : e ∈ secCMB t S L := hE.1 he
  have heeE : e * e ∈ E := E.mul_mem he he
  have heeP : e * e ∈ secCMB t S L := hE.1 heeE
  have hfe : sec12f t e ∈ secB S L := sec12E_f_mem F heP
  have hf : sec12f t (e * e) = 1 := by
    rw [sec12E_f_mul F heP heP, sec12E_B_sq F hfe]
  have heeA : e * e ∈ secA t S L := (sec120_f_eq_one_iff F hE heeE).mp hf
  rcases (sec12E_mem_A F).mp heeA with hB | ⟨b, hb, hb_eq⟩
  · exact hB
  · exfalso
    have heB : e ∈ centralizer (secB S L : Set G) := (sec120_mem_P_iff.mp heP).2
    have h1 : e * (t * b) = (t * b) * e := by rw [← hb_eq]; group
    have hbe : b * e = e * b := (Subgroup.mem_centralizer_iff.mp heB) b hb
    have het : e * t = t * e := by
      apply mul_right_cancel
      calc e * t * b = e * (t * b) := by group
        _ = (t * b) * e := h1
        _ = t * (b * e) := by group
        _ = t * (e * b) := by rw [hbe]
        _ = t * e * b := by group
    have heC : e ∈ centralizer (secA t S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rcases (sec12E_mem_A F).mp ha with haB | ⟨b', hb', rfl⟩
      · exact (Subgroup.mem_centralizer_iff.mp heB) a haB
      · have hb'e : b' * e = e * b' := (Subgroup.mem_centralizer_iff.mp heB) b' hb'
        calc (t * b') * e = t * (b' * e) := by group
          _ = t * (e * b') := by rw [hb'e]
          _ = (t * e) * b' := by group
          _ = (e * t) * b' := by rw [het]
          _ = e * (t * b') := by group
    have heEA : e ∈ secA t S L := by
      have hmem : e ∈ E ⊓ centralizer (secA t S L : Set G) := ⟨he, heC⟩
      rw [sec120_E_inf_C F hE] at hmem
      exact hmem
    have htb : t * b = 1 := by rw [← hb_eq, sec12E_A_sq F heEA]
    have htL : t ∈ L := by
      have hb_inv : b⁻¹ ∈ secB S L := (secB S L).inv_mem hb
      have ht : t = b⁻¹ := eq_inv_of_mul_eq_one_left htb
      rw [ht]
      exact F.bdata.1 hb_inv
    exact sec120_t_not_mem_L F htL

theorem sec120_comm_mem_B (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) {e e' : G} (he : e ∈ E) (he' : e' ∈ E) :
    e * e' * e⁻¹ * e'⁻¹ ∈ secB S L := by
  have hee'E : e * e' ∈ E := E.mul_mem he he'
  have hu : e * e ∈ secB S L := sec120_sq_mem_B F hE he
  have hv : e' * e' ∈ secB S L := sec120_sq_mem_B F hE he'
  have hw : (e * e') * (e * e') ∈ secB S L := sec120_sq_mem_B F hE hee'E
  have hmu : (e * e)⁻¹ ∈ secB S L := (secB S L).inv_mem hu
  have hmv : (e' * e')⁻¹ ∈ secB S L := (secB S L).inv_mem hv
  have he'B : e' ∈ centralizer (secB S L : Set G) := (sec120_mem_P_iff.mp (hE.1 he')).2
  have hc : e' * (e * e)⁻¹ = (e * e)⁻¹ * e' :=
    (((Subgroup.mem_centralizer_iff.mp he'B) ((e * e)⁻¹)) ((secB S L).inv_mem hu)).symm
  have heq : (e * e') * (e * e') * (e * e)⁻¹ * (e' * e')⁻¹
      = e * e' * e⁻¹ * e'⁻¹ := by
    calc (e * e') * (e * e') * (e * e)⁻¹ * (e' * e')⁻¹
        = e * e' * e * (e' * (e * e)⁻¹) * (e' * e')⁻¹ := by group
      _ = e * e' * e * ((e * e)⁻¹ * e') * (e' * e')⁻¹ := by rw [hc]
      _ = e * e' * e * ((e⁻¹ * e⁻¹) * e') * (e'⁻¹ * e'⁻¹) := by
            rw [show (e * e)⁻¹ = e⁻¹ * e⁻¹ by group,
                show (e' * e')⁻¹ = e'⁻¹ * e'⁻¹ by group]
      _ = e * e' * e⁻¹ * e'⁻¹ := by group
  have hprod : (e * e') * (e * e') * (e * e)⁻¹ * (e' * e')⁻¹ ∈ secB S L :=
    (secB S L).mul_mem ((secB S L).mul_mem hw hmu) hmv
  rw [heq] at hprod
  exact hprod

end CFSG.OddStandard.SmallF3.Omega
