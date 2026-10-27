module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C7Adj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B5Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Au
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B3Abar

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

private lemma pow_two_pow_eq_one_of_sq_eq_one {M : Type} [Group M] {x : M}
    (hx : x * x = 1) {a : ℕ} (ha : 1 ≤ a) : x ^ (2 ^ a) = 1 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
  rw [show 2 ^ (b + 1) = 2 * 2 ^ b by rw [pow_succ, mul_comm],
    pow_mul, show x ^ 2 = 1 by rw [sq]; exact hx, one_pow]

private theorem two_part_mem_B (F : Sec8T84Base) (hE : Sec8E G t L S z g B E)
    {m₀ : G} (hm₀L : m₀ ∈ L) (hm₀B : m₀ ∈ normalizer (B : Set G))
    {a₀ : MulAut ↥E} (ha₀ : a₀ = B89.rhoG hE m₀) (h1 : a₀ ≠ 1) (h2 : a₀ * a₀ = 1) :
    ∃ m₁ : G, m₁ ∈ L ∧ m₁ ∈ normalizer (B : Set G) ∧ m₁ ∈ Nsub8 t B ∧
      m₁ * m₁ ∈ B ∧ B89.rhoG hE m₁ = a₀ := by
  have hLt : L ≤ centralizer ({t} : Set G) := hE.ctx.toSec3SettingLB.component.le
  have hm₀t : m₀ * t = t * m₀ := Subgroup.mem_centralizer_singleton_iff.mp (hLt hm₀L)
  have hm₀N : m₀ ∈ Nsub8 t B := B89.mem_N_of_comm hm₀t hm₀B
  obtain ⟨k, q, hqodd, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m₀).ne'
  have h2' : a₀ ^ 2 = 1 := by rw [sq]; exact h2
  have hm₁L : m₀ ^ q ∈ L := L.pow_mem hm₀L q
  have hm₁B : m₀ ^ q ∈ normalizer (B : Set G) := (normalizer (B : Set G)).pow_mem hm₀B q
  have hm₁N : m₀ ^ q ∈ Nsub8 t B := (Nsub8 t B).pow_mem hm₀N q
  have hm₁pow : (m₀ ^ q) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm q (2 ^ k), ← horder, pow_orderOf_eq_one]
  have hρ : B89.rhoG hE (m₀ ^ q) = a₀ := by
    rw [B89.rhoG_pow hE hm₀N q, ← ha₀]
    obtain ⟨j, hj⟩ := hqodd
    rw [hj, pow_succ, pow_mul, h2', one_pow, one_mul]
  have hm₁ne : m₀ ^ q ≠ 1 := by
    intro h
    rw [h, B89.rhoG_one] at hρ
    exact h1 hρ.symm
  have hk : 1 ≤ k := by
    by_contra hlt
    have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp hlt)
    exact hm₁ne (by simpa [hk0] using hm₁pow)
  have hρsq : B89.rhoG hE ((m₀ ^ q) * (m₀ ^ q)) = 1 := by
    rw [B89.rhoG_mul hE hm₁N hm₁N, hρ, h2]
  have hcent : ∀ b ∈ B, b * ((m₀ ^ q) * (m₀ ^ q)) = ((m₀ ^ q) * (m₀ ^ q)) * b := by
    intro b hb
    have h := B89.rhoG_B hE F.h8B ((Nsub8 t B).mul_mem hm₁N hm₁N)
      (⟨b, B89.B_le_E hE hb⟩ : ↥E) hb
    rw [hρsq, MulAut.one_apply] at h
    simp only [Subtype.coe_mk] at h
    calc b * ((m₀ ^ q) * (m₀ ^ q))
        = (((m₀ ^ q) * (m₀ ^ q)) * b * ((m₀ ^ q) * (m₀ ^ q))⁻¹) *
            ((m₀ ^ q) * (m₀ ^ q)) := by rw [h.symm]
      _ = ((m₀ ^ q) * (m₀ ^ q)) * b := by group
  have hm₁sq_inf : ((m₀ ^ q) * (m₀ ^ q)) ∈ L ⊓ centralizer (B : Set G) :=
    ⟨L.mul_mem hm₁L hm₁L, Subgroup.mem_centralizer_iff.mpr hcent⟩
  have hmem : ((m₀ ^ q) * (m₀ ^ q)) ∈ B ⊔ centerIn L := by
    rw [← (A3.aut_B_of F hE.ctx).2.2]
    exact hm₁sq_inf
  have hcomm_BC : ∀ x ∈ B, ∀ y ∈ centerIn L, x * y = y * x := by
    intro x hx y hy
    exact (((sec4_mem_centerIn_iff y).mp hy).2 x (hE.ctx.B_le hx).1).symm
  obtain ⟨b', hb', c', hc', hbc⟩ := A3.exists_mul_of_comm hcomm_BC hmem
  have hc'O : c' ∈ oddCoreIn (Nsub8 t B) :=
    A3.centerIn_le_oddCoreIn_N F.h8A hE.ctx (A3.isOm6M_ctx hE.ctx) hc'
  have hc'odd : Odd (orderOf c') :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hc'O)
  have hm₁sq_pow : ((m₀ ^ q) * (m₀ ^ q)) ^ (2 ^ k) = 1 := by
    rw [← sq, ← pow_mul, mul_comm 2 (2 ^ k), pow_mul, hm₁pow, one_pow]
  have hb'sq : b' * b' = 1 := B89.E_sq hE (B89.B_le_E hE hb')
  have hb'_pow : b' ^ (2 ^ k) = 1 := pow_two_pow_eq_one_of_sq_eq_one hb'sq hk
  have hbc_pow : (b' * c') ^ (2 ^ k) = 1 := by rw [← hbc]; exact hm₁sq_pow
  have hc'pow : c' ^ (2 ^ k) = 1 := by
    have h := hbc_pow
    rw [Commute.mul_pow (hcomm_BC b' hb' c' hc'), hb'_pow, one_mul] at h
    exact h
  have hc'1 : c' = 1 := by
    refine orderOf_eq_one_iff.mp ?_
    have hdvd : orderOf c' ∣ 2 ^ k := (orderOf_dvd_iff_pow_eq_one).mpr hc'pow
    have hcop : Nat.Coprime (2 ^ k) (orderOf c') := (Nat.coprime_two_left.mpr hc'odd).pow_left k
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd dvd_rfl
  have hm₁sq_B : (m₀ ^ q) * (m₀ ^ q) ∈ B := by
    rw [hbc, hc'1, mul_one]
    exact hb'
  exact ⟨m₀ ^ q, hm₁L, hm₁B, hm₁N, hm₁sq_B, hρ⟩

private theorem card_fix_conjAut (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {m₁ : G}
    (hm₁N : m₁ ∈ Nsub8 t B) (hm₁B : m₁ ∈ normalizer (B : Set G))
    {a₀ : MulAut ↥E} (hrho : B89.rhoG hE m₁ = a₀)
    (h4 : Nat.card {e : ↥E // (e : G) ∈ B ∧ a₀ e = e} = 4) :
    Nat.card ↥B = Nat.card {v : ↥B // sec1011_conjAut B m₁ hm₁B v = v} ^ 2 := by
  have hfix4 : Nat.card {v : ↥B // sec1011_conjAut B m₁ hm₁B v = v} = 4 := by
    let e : {v : ↥B // sec1011_conjAut B m₁ hm₁B v = v} ≃
        {e : ↥E // (e : G) ∈ B ∧ a₀ e = e} :=
      { toFun := fun v =>
          ⟨⟨(v.1 : G), B89.B_le_E hE v.1.2⟩,
            ⟨v.1.2, by
              apply Subtype.ext
              show ((a₀ ⟨(v.1 : G), B89.B_le_E hE v.1.2⟩ : ↥E) : G) = (v.1 : G)
              rw [← hrho, B89.rhoG_B hE F.h8B hm₁N
                  ⟨(v.1 : G), B89.B_le_E hE v.1.2⟩ v.1.2,
                ← sec1011_conjAut_apply B hm₁B v.1, v.2]⟩⟩
        invFun := fun e =>
          ⟨⟨(e.1 : G), e.2.1⟩, by
            apply Subtype.ext
            show ((sec1011_conjAut B m₁ hm₁B ⟨(e.1 : G), e.2.1⟩ : ↥B) : G) = (e.1 : G)
            rw [sec1011_conjAut_apply B hm₁B,
              ← B89.rhoG_B hE F.h8B hm₁N e.1 e.2.1, hrho]
            exact congrArg Subtype.val e.2.2⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
    rw [Nat.card_congr e, h4]
  rw [hfix4, hE.ctx.B_e16.2]
  norm_num

theorem exists_involution_lift (F : Sec8T84Base) (hE : Sec8E G t L S z g B E)
    {a₀ : MulAut ↥E} (ha₀ : a₀ ∈ B89.Abar hE) (h1 : a₀ ≠ 1) (h2 : a₀ * a₀ = 1)
    (h4 : Nat.card {e : ↥E // (e : G) ∈ B ∧ a₀ e = e} = 4) :
    ∃ m ∈ L, m ∈ normalizer (B : Set G) ∧ m * m = 1 ∧ B89.rhoG hE m = a₀ := by
  classical
  obtain ⟨m₀, hm₀L, hm₀B, ha₀eq⟩ := B89.exists_of_mem_Abar hE ha₀
  obtain ⟨m₁, hm₁L, hm₁B, hm₁N, hm₁sq_B, hrho⟩ :=
    two_part_mem_B F hE hm₀L hm₀B ha₀eq h1 h2
  letI : CommGroup ↥B :=
    { (inferInstance : Group ↥B) with
      mul_comm := fun a b =>
        Subtype.ext (B89.E_comm hE (B89.B_le_E hE a.2) (B89.B_le_E hE b.2)) }
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hE.ctx.B_e16.2]; norm_num)
  have hsq : ∀ v : ↥B, v * v = 1 := fun v => Subtype.ext (B89.E_sq hE (B89.B_le_E hE v.2))
  have hcard : Nat.card ↥B = Nat.card {v : ↥B // sec1011_conjAut B m₁ hm₁B v = v} ^ 2 :=
    card_fix_conjAut F hE hm₁N hm₁B hrho h4
  have hα2 : sec1011_conjAut B m₁ hm₁B * sec1011_conjAut B m₁ hm₁B = 1 := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    show ((sec1011_conjAut B m₁ hm₁B (sec1011_conjAut B m₁ hm₁B v) : ↥B) : G) = (v : G)
    rw [sec1011_conjAut_apply, sec1011_conjAut_apply]
    have hcomm : (m₁ * m₁) * (v : G) = (v : G) * (m₁ * m₁) :=
      B89.E_comm hE (B89.B_le_E hE hm₁sq_B) (B89.B_le_E hE v.2)
    have h1' : m₁ * (m₁ * (v : G) * m₁⁻¹) * m₁⁻¹ =
        (m₁ * m₁) * (v : G) * (m₁ * m₁)⁻¹ := by group
    rw [h1', hcomm]
    group
  let c₀ : ↥B := ⟨m₁ * m₁, hm₁sq_B⟩
  have hc₀ : sec1011_conjAut B m₁ hm₁B c₀ = c₀ := by
    apply Subtype.ext
    show ((sec1011_conjAut B m₁ hm₁B c₀ : ↥B) : G) = (c₀ : G)
    rw [sec1011_conjAut_apply B hm₁B]
    show m₁ * (m₁ * m₁) * m₁⁻¹ = m₁ * m₁
    group
  obtain ⟨b, hb⟩ := exists_apply_mul_eq hsq (sec1011_conjAut B m₁ hm₁B) hα2 hcard hc₀
  refine ⟨m₁ * (b : G), ?_, ?_, ?_, ?_⟩
  · exact L.mul_mem hm₁L (hE.ctx.B_le b.2).1
  · exact (normalizer (B : Set G)).mul_mem hm₁B (Subgroup.le_normalizer b.2)
  · have hαb : ((sec1011_conjAut B m₁ hm₁B b : ↥B) : G) = m₁ * (b : G) * m₁⁻¹ :=
      sec1011_conjAut_apply B hm₁B b
    have hαbB : ((sec1011_conjAut B m₁ hm₁B b * b : ↥B) : G) = (c₀ : G) :=
      congrArg Subtype.val hb
    have hc₀G : (c₀ : G) = m₁ * m₁ := rfl
    show (m₁ * (b : G)) * (m₁ * (b : G)) = 1
    calc (m₁ * (b : G)) * (m₁ * (b : G))
        = ((m₁ * (b : G) * m₁⁻¹) * (m₁ * m₁)) * (b : G) := by group
      _ = ((sec1011_conjAut B m₁ hm₁B b : ↥B) : G) * (m₁ * m₁) * (b : G) := by rw [← hαb]
      _ = ((sec1011_conjAut B m₁ hm₁B b : ↥B) : G) * ((m₁ * m₁) * (b : G)) := by group
      _ = ((sec1011_conjAut B m₁ hm₁B b : ↥B) : G) * ((b : G) * (m₁ * m₁)) := by
            rw [B89.E_comm hE (B89.B_le_E hE hm₁sq_B) (B89.B_le_E hE b.2)]
      _ = (((sec1011_conjAut B m₁ hm₁B b : ↥B) : G) * (b : G)) * (m₁ * m₁) := by group
      _ = (m₁ * m₁) * (m₁ * m₁) := by rw [← Subgroup.coe_mul, hαbB, hc₀G]
      _ = 1 := B89.E_sq hE (B89.B_le_E hE hm₁sq_B)
  · rw [B89.rhoG_mul hE hm₁N (sec8t84a1_A_le_N (sec8t84a1_B_le_A b.2)),
      hrho, B89.rhoG_of_mem_E hE (B89.B_le_E hE b.2), mul_one]

end C10

end CFSG.OddStandard.SmallF3.Omega
