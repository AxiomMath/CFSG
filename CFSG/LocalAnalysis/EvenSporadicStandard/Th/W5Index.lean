module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Gamma
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Vanish
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Sylow

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem ThLocalIn2.b_not_mem_centralizer (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) :
    b ∉ centralizer (Aa : Set G) := fun hb => by
  obtain ⟨x, hx, hx2⟩ := W2.exists_sq_ne_one W
  have h1 : x * b = b * x := mem_centralizer_iff.1 hb x hx
  apply hx2
  have h2 : b * x * b⁻¹ = x := by
    rw [← h1]
    group
  have hxi : x⁻¹ = x := (W2.b_inv x hx).symm.trans h2
  calc x ^ 2 = x * x := sq x
    _ = x * x⁻¹ := by rw [hxi]
    _ = 1 := mul_inv_cancel x

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.exists_sqPsi_pow {r : G} (hr : r ∈ Bp A t) :
    ∃ e : ℕ, ∀ a ∈ A, sqPsi W2 r a = a ^ e := by
  have hrA : ∀ a ∈ A, r * a = a * r := fun a ha => (mem_centralizer_iff.1 hr.1 a ha).symm
  have hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa := H.Aa_normal W W2 hr.2
  by_cases h1 : theta t r = 1
  · exact sqPsi_centralizer_W5 H W W2 ((H.theta_eq_one_iff W hr).1 h1)
  · refine endo_eq_pow_of_stabilizer (K := L) W.A_comm W.A_sq W.A_card W.surj (sqPsi W2 r)
      (fun a ha => sqPsi_mem W W2 hrA hrAa ha)
      (fun a ha c hc => sqPsi_mul W W2 hrA hrAa ha hc) (H.theta_mem_A W hr) h1 ?_
    intro n hnL hnA hna₀
    have hnN : n ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
      H.mem_normalizer_W5_of_L W hnL hnA
    have hr' : n * r * n⁻¹ ∈ Bp A t := H.Bp_normal W hnN hr
    have hr'A : ∀ a ∈ A, n * r * n⁻¹ * a = a * (n * r * n⁻¹) := fun a ha =>
      (mem_centralizer_iff.1 hr'.1 a ha).symm
    have hr'Aa : ∀ x ∈ Aa, n * r * n⁻¹ * x * (n * r * n⁻¹)⁻¹ ∈ Aa := H.Aa_normal W W2 hr'.2
    have hnAa : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa := W2.conj_mem_of_mem_L W hnL hnA
    have hnt1 : n⁻¹ * t * n = t := by
      rw [← H.comm_of_mem_L (L.inv_mem hnL)]
      group
    have hnt2 : n⁻¹ * t⁻¹ * n = t⁻¹ := by
      calc n⁻¹ * t⁻¹ * n = (n⁻¹ * t * n)⁻¹ := by group
        _ = t⁻¹ := by rw [hnt1]
    have hθ' : theta t (n * r * n⁻¹) = theta t r := by
      calc theta t (n * r * n⁻¹) = n * (r * (n⁻¹ * t * n) * r⁻¹) * n⁻¹ * t⁻¹ := by
            simp only [theta]
            group
        _ = n * (r * t * r⁻¹ * (n⁻¹ * t⁻¹ * n)) * n⁻¹ := by rw [hnt1]; group
        _ = n * (r * t * r⁻¹ * t⁻¹) * n⁻¹ := by rw [hnt2]
        _ = n * theta t r * n⁻¹ := rfl
        _ = theta t r := hna₀
    have hr't : n * r * n⁻¹ * t * (n * r * n⁻¹)⁻¹ = theta t r * t := by
      have : theta t (n * r * n⁻¹) * t = n * r * n⁻¹ * t * (n * r * n⁻¹)⁻¹ := by
        simp only [theta]
        group
      rw [← this, hθ']
    have hrt : r * t * r⁻¹ = theta t r * t := by
      simp only [theta]
      group
    have hy1 : theta t (r⁻¹ * (n * r * n⁻¹)) = 1 := by
      calc theta t (r⁻¹ * (n * r * n⁻¹))
          = r⁻¹ * (n * r * n⁻¹ * t * (n * r * n⁻¹)⁻¹) * r * t⁻¹ := by
            simp only [theta]
            group
        _ = r⁻¹ * (r * t * r⁻¹) * r * t⁻¹ := by rw [hr't, hrt]
        _ = 1 := by group
    have hyBp : r⁻¹ * (n * r * n⁻¹) ∈ Bp A t := (Bp A t).mul_mem ((Bp A t).inv_mem hr) hr'
    obtain ⟨e, he⟩ := sqPsi_centralizer_W5 H W W2 ((H.theta_eq_one_iff W hyBp).1 hy1)
    refine ⟨e, fun a ha => ?_⟩
    have ha' : n⁻¹ * a * n ∈ A := conj_inv_mem_of_conj_mem hnA ha
    have hconj := sqPsi_conj W W2 hrA hrAa hr'A hr'Aa hnAa hnA ha'
    have e1 : n * (n⁻¹ * a * n) * n⁻¹ = a := by group
    rw [e1] at hconj
    rw [← hconj]
    have hyA : ∀ a ∈ A, r⁻¹ * (n * r * n⁻¹) * a = a * (r⁻¹ * (n * r * n⁻¹)) := fun a ha =>
      (mem_centralizer_iff.1 hyBp.1 a ha).symm
    have hyAa := H.Aa_normal W W2 hyBp.2
    have hmul := sqPsi_mul_left W W2 hrA hrAa hyA hyAa ha
    rw [mul_inv_cancel_left] at hmul
    rw [hmul, he a ha]
    exact W.A_comm _ (A.pow_mem ha e) _ (sqPsi_mem W W2 hrA hrAa ha)

theorem ThCyc.psi_dichotomy {r : G} (hr : r ∈ Bp A t) :
    (∀ x ∈ Aa, psi r x = 1) ∨ (∀ x ∈ Aa, psi r x = x ^ 2) := by
  obtain ⟨e, he⟩ := H.exists_sqPsi_pow W W2 hr
  have hrA : ∀ a ∈ A, r * a = a * r := fun a ha => (mem_centralizer_iff.1 hr.1 a ha).symm
  have hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa := H.Aa_normal W W2 hr.2
  have hx : ∀ x ∈ Aa, psi r x = (x ^ 2) ^ e := fun x hx => by
    rw [← he (x ^ 2) (W2.sq_mem_A hx), sqPsi_eq W W2 hrA hrAa (W2.sq_mem_A hx) hx rfl]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · left
    intro x hxA
    have : (x ^ 2) ^ (2 * k) = (x ^ 4) ^ k := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hx x hxA, hk, this, W2.Aa_exp x hxA, one_pow]
  · right
    intro x hxA
    have : (x ^ 2) ^ (2 * k) = (x ^ 4) ^ k := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hx x hxA, hk, pow_succ, this, W2.Aa_exp x hxA, one_pow, one_mul]

theorem ThCyc.b_mem_Bp : b ∈ Bp A t := by
  have : b ∈ centralizer ((W5 A t : Subgroup G) : Set G) :=
    (H.mem_centralizer_W5_iff W).2 ⟨b, W2.b_mem, 0, by simp⟩
  exact centralizer_W5_le_Bp A t this

theorem ThCyc.exists_mem_inf_centralizer_Aa {r : G} (hr : r ∈ Bp A t) :
    ∃ c ∈ Bp A t ⊓ centralizer (Aa : Set G), r = c ∨ r = c * b := by
  rcases H.psi_dichotomy W W2 hr with h | h
  · refine ⟨r, ⟨hr, mem_centralizer_iff.2 fun x hx => ?_⟩, Or.inl rfl⟩
    have h0 := h x hx
    simp only [psi] at h0
    have h1 : r * x * r⁻¹ = x := mul_inv_eq_one.1 h0
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · have hbBp := H.b_mem_Bp W W2
    refine ⟨r * b, ⟨(Bp A t).mul_mem hr hbBp, mem_centralizer_iff.2 fun x hx => ?_⟩,
      Or.inr (by rw [mul_assoc, ← sq, W2.b_sq, mul_one])⟩
    have hpsi := h x hx
    have h1 : r * x * r⁻¹ = x ^ 2 * x := by
      rw [← hpsi]
      simp only [psi]
      group
    have h2 : x ^ 2 * x * x = 1 := by
      calc x ^ 2 * x * x = x ^ 4 := by group
        _ = 1 := W2.Aa_exp x hx
    have h3 : r * b * x * (r * b)⁻¹ = x := by
      calc r * b * x * (r * b)⁻¹ = r * (b * x * b⁻¹) * r⁻¹ := by group
        _ = r * x⁻¹ * r⁻¹ := by rw [W2.b_inv x hx]
        _ = (r * x * r⁻¹)⁻¹ := by group
        _ = (x ^ 2 * x)⁻¹ := by rw [h1]
        _ = x := inv_eq_of_mul_eq_one_right h2
    calc x * (r * b) = (r * b * x * (r * b)⁻¹) * (r * b) := by rw [h3]
      _ = r * b * x := by group

theorem ThCyc.natCard_Bp_inf_centralizer_Aa :
    Nat.card ↥(Bp A t ⊓ centralizer (Aa : Set G)) = 2 ^ 13 := by
  set C := Bp A t ⊓ centralizer (Aa : Set G) with hC
  have hCle : C ≤ Bp A t := inf_le_left
  have hbBp := H.b_mem_Bp W W2
  have hbC : b ∉ C := fun hb => W2.b_not_mem_centralizer W hb.2
  have hidx : (C.subgroupOf (Bp A t)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b, hbBp⟩, fun r => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hrC : (r : G) ∈ C
    · right
      refine ⟨hrC, fun h => hbC ?_⟩
      have := C.mul_mem (C.inv_mem hrC) h
      simpa using this
    · left
      refine ⟨?_, hrC⟩
      obtain ⟨c, hc, hrc⟩ := H.exists_mem_inf_centralizer_Aa W W2 r.2
      rcases hrc with h | h
      · exact absurd (h ▸ hc) hrC
      · have e : (r : G) * b = c := by
          rw [h, mul_assoc, ← sq, W2.b_sq, mul_one]
        rw [e]
        exact hc
  have h := Subgroup.card_mul_index (C.subgroupOf (Bp A t))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv, H.natCard_Bp_eq W] at h
  omega

theorem ThCyc.Aa_le_inf_centralizer_Aa : Aa ≤ Bp A t ⊓ centralizer (Aa : Set G) := fun x hx =>
  ⟨centralizer_W5_le_Bp A t ((H.mem_centralizer_W5_iff W).2 ⟨x, W2.Aa_le hx, 0, by simp⟩),
    mem_centralizer_iff.2 fun y hy => W2.Aa_comm y hy x hx⟩

theorem ThCyc.t_mem_inf_centralizer_Aa : t ∈ Bp A t ⊓ centralizer (Aa : Set G) :=
  ⟨centralizer_W5_le_Bp A t ((H.mem_centralizer_W5_iff W).2 ⟨1, B.one_mem, 1, by simp⟩),
    mem_centralizer_iff.2 fun y hy => (H.comm_of_mem_L (W.B_le (W2.Aa_le hy))).symm⟩

theorem ThCyc.conj_mem_inf_centralizer_Aa {r : G}
    (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ Bp A t ⊓ centralizer (Aa : Set G)) :
    r * c * r⁻¹ ∈ Bp A t ⊓ centralizer (Aa : Set G) := by
  refine ⟨H.Bp_normal W hr hc.1, mem_centralizer_iff.2 fun x hx => ?_⟩
  have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ Aa := H.Aa_normal W W2 ((normalizer _).inv_mem hr) x hx
  have h1 : r⁻¹ * x * r * c = c * (r⁻¹ * x * r) := by
    have := mem_centralizer_iff.1 hc.2 _ (by simpa using hx')
    exact this
  calc x * (r * c * r⁻¹) = r * ((r⁻¹ * x * r) * c) * r⁻¹ := by group
    _ = r * (c * (r⁻¹ * x * r)) * r⁻¹ := by rw [h1]
    _ = r * c * r⁻¹ * x := by group

theorem ThCyc.mem_centralizer_W5_inf_centralizer_Aa_iff {y : G} :
    y ∈ centralizer ((W5 A t : Subgroup G) : Set G) ⊓ centralizer (Aa : Set G) ↔
      ∃ x ∈ Aa, ∃ k : ℤ, y = x * t ^ k := by
  have hcomm : ∀ x ∈ Aa, ∀ k : ℤ, t ^ k * x = x * t ^ k := fun x hx k =>
    (((show Commute x t from (H.comm_of_mem_L (W.B_le (W2.Aa_le hx))).symm).zpow_right k).eq).symm
  constructor
  · rintro ⟨hyW, hyAa⟩
    obtain ⟨b'', hb'', k, rfl⟩ := (H.mem_centralizer_W5_iff W).1 hyW
    have hb''Aa : b'' ∈ centralizer (Aa : Set G) := mem_centralizer_iff.2 fun x hx => by
      have h1 := mem_centralizer_iff.1 hyAa x hx
      calc x * b'' = (x * (b'' * t ^ k)) * (t ^ k)⁻¹ := by group
        _ = ((b'' * t ^ k) * x) * (t ^ k)⁻¹ := by rw [h1]
        _ = b'' * (t ^ k * x) * (t ^ k)⁻¹ := by group
        _ = b'' * (x * t ^ k) * (t ^ k)⁻¹ := by rw [hcomm x hx k]
        _ = b'' * x := by group
    rcases W2.mem_Aa_or_mul_b W hb'' with h | h
    · exact ⟨b'', h, k, rfl⟩
    · exfalso
      refine W2.b_not_mem_centralizer W ?_
      have hxc : b'' * b ∈ centralizer (Aa : Set G) :=
        mem_centralizer_iff.2 fun y hy => W2.Aa_comm y hy _ h
      have hbinv : b⁻¹ ∈ centralizer (Aa : Set G) := by
        have e : b⁻¹ = (b'' * b)⁻¹ * b'' := by group
        rw [e]
        exact (centralizer (Aa : Set G)).mul_mem ((centralizer (Aa : Set G)).inv_mem hxc) hb''Aa
      simpa using (centralizer (Aa : Set G)).inv_mem hbinv
  · rintro ⟨x, hx, k, rfl⟩
    refine ⟨(H.mem_centralizer_W5_iff W).2 ⟨x, W2.Aa_le hx, k, rfl⟩,
      mem_centralizer_iff.2 fun y hy => ?_⟩
    calc y * (x * t ^ k) = (y * x) * t ^ k := by rw [mul_assoc]
      _ = (x * y) * t ^ k := by rw [W2.Aa_comm y hy x hx]
      _ = x * (y * t ^ k) := by rw [mul_assoc]
      _ = x * (t ^ k * y) := by rw [hcomm y hy k]
      _ = x * t ^ k * y := by rw [mul_assoc]

theorem ThCyc.centralizer_W5_inf_centralizer_Aa_eq :
    centralizer ((W5 A t : Subgroup G) : Set G) ⊓ centralizer (Aa : Set G) = Aa ⊔ zpowers t := by
  have hc : zpowers t ≤ centralizer (Aa : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => (H.comm_of_mem_L (W.B_le (W2.Aa_le hy))).symm
  ext y
  rw [H.mem_centralizer_W5_inf_centralizer_Aa_iff W W2]
  constructor
  · rintro ⟨x, hx, k, rfl⟩
    exact mul_mem (mem_sup_left hx) (mem_sup_right (zpow_mem (mem_zpowers t) k))
  · intro hy
    obtain ⟨x, hx, r, hr, rfl⟩ := exists_mul_of_mem_sup hc hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact ⟨x, hx, k, rfl⟩

theorem ThCyc.exists_theta_eq_of_mem_inf_centralizer_Aa {a : G} (ha : a ∈ A) :
    ∃ c ∈ Bp A t ⊓ centralizer (Aa : Set G), theta t c = a := by
  obtain ⟨r, hr⟩ := H.thetaHom_surjective W ⟨a, ha⟩
  have hra : theta t r = a := by
    have := congrArg Subtype.val hr
    simpa [thetaHom] using this
  obtain ⟨c, hc, hrc⟩ := H.exists_mem_inf_centralizer_Aa W W2 r.2
  refine ⟨c, hc, ?_⟩
  rcases hrc with h | h
  · rw [← h]
    exact hra
  · have hbBp := H.b_mem_Bp W W2
    have hb1 : theta t b = 1 := (H.theta_eq_one_iff W hbBp).2
      ((H.mem_centralizer_W5_iff W).2 ⟨b, W2.b_mem, 0, by simp⟩)
    have hmul := H.theta_mul W hc.1 hbBp
    rw [hb1, mul_one, ← h] at hmul
    rw [← hmul]
    exact hra

end

end CFSG.EvenSporadicStandard.ThStd
