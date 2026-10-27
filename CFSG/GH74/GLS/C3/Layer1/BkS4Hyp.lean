module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Gen
public import CFSG.GH74.GLS.C3.Layer1.BkS4K6
public import CFSG.GH74.GLS.C3.Layer1.BkD6

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

section A6

theorem exists_noncomm_of_equiv_A6 {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 6)) :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => by
    have h := congrArg e (hcon (e.symm a) (e.symm b))
    simpa using h⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
  simp at h3

theorem factorization_threeSixty : (360 : ℕ).factorization 2 = 3 := by
  have h : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_two_card_of_equiv_A6 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (e : kBar K ≃* alternatingGroup (Fin 6)) : (Nat.card ↥K).factorization 2 = 3 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have h2 : Nat.card (kBar K) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hne : Nat.card (pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h3 : Nat.card ↥K = 360 * Nat.card (pPrimeCore 2 ↥K) := by
    rw [h1]
    show Nat.card (kBar K) * _ = _
    rw [h2]
  rw [h3, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply, factorization_threeSixty,
    Setup91.factorization_two_of_odd hodd]

end A6

theorem sec4Core_of_hyp9
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x : G} {K M T Q : Subgroup G}
    (hh : Hyp9 x K K M T Q) (p91 : Prop91Concl K M T Q)
    (e0 : kBar K ≃* alternatingGroup (Fin 6)) (hTS : ¬ IsSylowOf 2 T ⊤) :
    ∃ (a : G) (S : Subgroup G), Sec4Core a (T ⊓ K) Q T S ∧
      Nat.card ↥(T ⊓ centralizer ((T ⊓ K : Subgroup G) : Set G)) ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hh.a
  have hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K := hA.L_normal.2
  have hTM : T ≤ M := hA.sylowTM.le
  have hT2 : IsPGroup 2 ↥T := hA.sylowT.isPGroup
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (kBar K) := e0.isSimpleGroup
  have hn := exists_noncomm_of_equiv_A6 e0
  obtain ⟨-, hPQcomm, hPQ⟩ := hA.R_eq hs hn
  have hQT : Q ≤ T := Setup91.Q_le_T hA
  have hQeq : T ⊓ CMK M K = Q :=
    hA.sylowQ.eq_of_le (le_inf hQT hA.sylowQ.le) inf_le_right hT2.to_inf_left
  have hPT : T ⊓ K ≤ T := inf_le_left
  have hPM : T ⊓ K ≤ M := hPT.trans hTM
  set ψ : ↥M →* MulAut (kBar K) := Back.actHom hLn with hψ
  have hψker : ∀ m : ↥M, ψ m = 1 ↔ (m : G) ∈ CMK M K := by
    intro m
    have h := Subgroup.ext_iff.1 (Back.actHom_ker hLn) m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at h
    exact h
  let χ : ↥(T ⊓ K) →* MulAut (kBar K) := ψ.comp (Subgroup.inclusion hPM)
  have hχinj : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro p hp
    have hp1 : χ p = 1 := hp
    have hpC : (p : G) ∈ CMK M K := (hψker (Subgroup.inclusion hPM p)).1 hp1
    have hpQ : (p : G) ∈ Q := by
      rw [← hQeq]; exact ⟨p.2.1, hpC⟩
    have : (p : G) ∈ (T ⊓ K) ⊓ Q := ⟨p.2, hpQ⟩
    rw [hPQ, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hχinn : χ.range ≤ IVK.innAut (kBar K) := by
    rintro _ ⟨p, rfl⟩
    show ψ (Subgroup.inclusion hPM p) ∈ IVK.innAut (kBar K)
    have := Back.actHom_of_mem hLn p.2.2 (hPM p.2)
    rw [show Subgroup.inclusion hPM p = ⟨(p : G), hPM p.2⟩ from rfl, hψ, this]
    exact ⟨_, rfl⟩
  have hPcard : Nat.card ↥(T ⊓ K) = 8 := by
    rw [(Setup91.inf_isSylowOf hA).card_eq, factorization_two_card_of_equiv_A6 e0]
    norm_num
  have hXcard : Nat.card ↥χ.range = 8 := by
    rw [← hPcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  obtain ⟨hD8, hC4⟩ := a6_sylow_package e0 χ.range hχinn hXcard
  have hPD8 : IsD8 (T ⊓ K) := by
    obtain ⟨d⟩ := hD8
    exact ⟨(MonoidHom.ofInjective hχinj).trans d⟩
  have hK4 : Nat.card ↥(T ⊓ centralizer ((T ⊓ K : Subgroup G) : Set G)) ≤ 16 := by
    set C : Subgroup G := T ⊓ centralizer ((T ⊓ K : Subgroup G) : Set G) with hC
    have hCM : C ≤ M := inf_le_left.trans hTM
    let φ : ↥C →* MulAut (kBar K) := ψ.comp (Subgroup.inclusion hCM)
    have hrange : φ.range ≤ centralizer (χ.range : Set (MulAut (kBar K))) := by
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨p, rfl⟩
      show ψ (Subgroup.inclusion hPM p) * ψ (Subgroup.inclusion hCM c) =
        ψ (Subgroup.inclusion hCM c) * ψ (Subgroup.inclusion hPM p)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 c.2.2 (p : G) p.2
    have hker : (φ.ker).map C.subtype ≤ Q := by
      rintro _ ⟨c, hc, rfl⟩
      have hc1 : φ c = 1 := hc
      have hcC : ((c : ↥C) : G) ∈ CMK M K := (hψker (Subgroup.inclusion hCM c)).1 hc1
      rw [← hQeq]
      exact ⟨c.2.1, hcC⟩
    have h1 : Nat.card ↥(φ.ker) ≤ 4 := by
      have := Subgroup.card_le_of_le hker
      rw [Subgroup.card_map_of_injective C.subtype_injective, p91.1.2] at this
      exact this
    have h2 : Nat.card ↥φ.range ≤ 4 :=
      (Subgroup.card_le_of_le hrange).trans hC4
    have h3 := Subgroup.card_ker_mul_card_range φ
    calc Nat.card ↥C = Nat.card ↥φ.ker * Nat.card ↥φ.range := h3.symm
      _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2
  obtain ⟨a, S, hcore⟩ := sec4Core_gen hG hh p91 hs hn hTS hPD8
  exact ⟨a, S, hcore, hK4⟩

theorem b_L42c_six_proof : B_L42c_six := by
  intro G _ _ hG x K M T Q hh p91 he6 hTS _
  obtain ⟨e0⟩ := he6
  obtain ⟨a, S, hcore, hK4⟩ := sec4Core_of_hyp9 hG hh p91 e0 hTS
  exact hcore.T_le_closure_involutions p91.1.1 hK4

theorem b_prop43c_six_proof :
    B_prop43c_six :=
  b_prop43c_six_of_42c b_L42c_six_proof

end CFSG.GH74.GLS.C3.Layer1.Bk
