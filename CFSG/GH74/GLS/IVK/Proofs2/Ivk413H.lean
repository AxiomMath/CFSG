module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011C413Stmt
public import CFSG.GH74.GLS.IVK.Proofs2.OddOutG2Stmt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413AutSp
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413AutLin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413AutUni
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Phi
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Ratio

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GorensteinWalter
  CFSG.GH74.GLS.IVK
open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem pPrimeCoreOf_centralizer_eq_bot_G2 (hG2 : OddOutG2) {H : Type} [Group H]
    [Finite H] (K : Subgroup H) [K.Normal] (hC : centralizer (K : Set H) = ⊥) {p f q : ℕ}
    (hp : p.Prime) (hqpf : q = p ^ f) (hqodd : Odd q) (hq3 : 3 < q)
    (hLie : LieModel ↥K .G2 0 p f) {z : H} (hz : z ∈ K) (hz2 : orderOf z = 2) :
    pPrimeCoreOf 2 (centralizer ({z} : Set H)) = ⊥ := by
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_pow hqpf hqodd hq3
  have hz' : orderOf (⟨z, hz⟩ : ↥K) = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hz
  obtain ⟨F, _, _, Sh, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hLie ⟨z, hz⟩ hz'
  have hodd : Odd (Nat.card F) := by rw [hcard, ← hqpf]; exact hqodd
  have h3 : 3 ≤ Nat.card F := by rw [hcard, ← hqpf]; omega
  have hbotK : pPrimeCoreOf 2 (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) = ⊥ := by
    have h := Ivk413.pPrimeCore_shape_eq_bot Sh hodd h3 hodd h3
    show (pPrimeCore 2 ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K))).map _ = ⊥
    rw [h, Subgroup.map_bot]
  have hbot : pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K) = ⊥ := by
    rw [Ivk413.pPrimeCoreOf_inf_eq_map K hz, hbotK, Subgroup.map_bot]
  have hYK : pPrimeCoreOf 2 (centralizer ({z} : Set H)) ⊓ K ≤
      pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K) := by
    refine Ivk413.le_pPrimeCoreOf_of_normal_odd (inf_le_inf_right K (pPrimeCoreOf_le _)) ?_
      (Odd.of_dvd_nat (odd_card_pPrimeCoreOf _) (Subgroup.card_dvd_of_le inf_le_left))
    intro x hx n hn
    exact ⟨pPrimeCoreOf_conj (Subgroup.mem_inf.1 hx).1 hn.1,
      Subgroup.Normal.conj_mem inferInstance n hn.2 x⟩
  rw [hbot] at hYK
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreOf _) (Subgroup.orderOf_dvd_natCard _ hy)
  have hcomm : ∀ x : ↥K, x ∈ centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K) → y * (x : H) = (x : H) * y := by
    intro x hx
    have hxC : (x : H) ∈ centralizer ({z} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx)
    have hmem : y * (x : H) * y⁻¹ * (x : H)⁻¹ ∈
        pPrimeCoreOf 2 (centralizer ({z} : Set H)) ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 := pPrimeCoreOf_conj hxC ((pPrimeCoreOf 2 _).inv_mem hy)
        have e : y * (x : H) * y⁻¹ * (x : H)⁻¹ = y * ((x : H) * y⁻¹ * (x : H)⁻¹) := by group
        rw [e]
        exact (pPrimeCoreOf 2 _).mul_mem hy h1
      · exact K.mul_mem (Subgroup.Normal.conj_mem inferInstance (x : H) x.2 y) (K.inv_mem x.2)
    have h0 := hYK hmem
    rw [Subgroup.mem_bot] at h0
    have := congrArg (· * ((x : H) * y)) h0
    simp only [one_mul] at this
    calc y * (x : H) = y * (x : H) * y⁻¹ * (x : H)⁻¹ * ((x : H) * y) := by group
      _ = (x : H) * y := this
  let α : MulAut ↥K := MulAut.conjNormal y
  have hαfix : ∀ x ∈ centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K), α x = x := by
    intro x hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := hcomm x hx
    rw [this]
    group
  have hαodd : Odd (orderOf α) :=
    Odd.of_dvd_nat hyodd (orderOf_map_dvd (MulAut.conjNormal : H →* MulAut ↥K) y)
  have hα1 : α = 1 := hG2 ↥K p f hp hp2 hLie (by rw [← hqpf]; exact hq3) ⟨z, hz⟩ hz' α hαodd hαfix
  have hcen : y ∈ centralizer (K : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun a : MulAut ↥K => ((a ⟨k, hk⟩ : ↥K) : H)) hα1
    simp only [α, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * y = (y * k * y⁻¹) * y := by rw [this]
      _ = y * k := by group
  rw [hC, Subgroup.mem_bot] at hcen
  exact hcen


theorem ivk_4_13_H_main
    (hG2 : OddOutG2) : Stage2.Final.Thm6.L2011.IVK413H := by
  intro H _ _ K q hKN hqodd hq3 hK hC z hz hS hne
  have : K.Normal := hKN
  obtain ⟨S, hzS, hz2, hSc⟩ := hS
  rcases hK with ⟨p, f, hp, hqpf, hLie⟩ | hPSp | ⟨hn8, hL⟩ | ⟨hn8, hU⟩
  ·
    exact absurd (pPrimeCoreOf_centralizer_eq_bot_G2 hG2 K hC hp hqpf hqodd hq3 hLie hz hz2) hne
  ·
    exfalso
    obtain ⟨F, _, _, hcardF, ⟨e⟩⟩ := hPSp
    have hodd : Odd (Nat.card F) := by rw [hcardF]; exact hqodd
    have h2 : (2 : F) ≠ 0 := L5U5.two_ne_zero_of_odd_card hodd
    have h5 : 5 ≤ Nat.card F := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hG := goodModel_sp h2 h5
    obtain ⟨Φ, hΦ⟩ := Ivk413.exists_Phi hG K (e.trans (ModelSp.spEquiv F)) hz S hzS hz2 hSc
    apply hne
    show pPrimeCoreOf 2 (centralizer ({z} : Set H)) = ⊥
    rw [← Ivk413.clause3 hG (Ivk413.autInner_sp h2 hG) K hC hz Φ hΦ]
    exact Ivk413.pPrimeCoreOf_inf_eq_bot_of_Phi K hz Φ hΦ (Ivk413.pPrimeCoreOf_sp_eq_bot h2 h5)
  ·
    have hL' := hL
    rcases hL with ⟨-, F, _, _, hcardF, ⟨e⟩⟩ | ⟨h, -⟩
    · have hodd : Odd (Nat.card F) := by rw [hcardF]; exact hqodd
      have h2 : (2 : F) ≠ 0 := L5U5.two_ne_zero_of_odd_card hodd
      have h5 : 5 ≤ Nat.card F := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have hodd2 : Nat.card F % 2 = 1 := Nat.odd_iff.1 hodd
      have hq8 : Nat.card F % 8 ≠ 1 := by
        rw [hcardF]
        intro h
        apply hn8
        unfold Int.ModEq
        omega
      have hG := goodModel_lin h2 h5
      have e' : ↥K ≃* PG (ModelData.lin F) := e
      have hcc := Ivk413.core_clauses hG (Ivk413.autInner_lin hG)
        (Ivk413.ratio_lin h2 h5 hodd2 hq8) K hC e' hz S hzS hz2 hSc
      refine ⟨⟨1, Or.inl rfl, hn8, hL'⟩, hcc.1, hcc.2.1, hcc.2.2, ?_⟩
      rw [← hcc.2.1]
      exact (Subgroup.map_subtype_le _).trans inf_le_right
    · exact absurd h (by norm_num)
  ·
    have hU' := hU
    rcases hU with ⟨h, -⟩ | ⟨-, F, _, _, hcardF, ⟨e⟩⟩
    · exact absurd h (by norm_num)
    · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_uni_params hcardF
      have hp2 : p ≠ 2 := prime_ne_two_of_odd_pow rfl hqodd hq3
      have h5 : 5 ≤ p ^ f := by
        obtain ⟨k, hk⟩ := hqodd
        omega
      have hodd2 : p ^ f % 2 = 1 := Nat.odd_iff.1 hqodd
      have hq8 : p ^ f % 8 ≠ 7 := by
        intro h
        apply hn8
        unfold Int.ModEq
        omega
      have hG := goodModel_uni hcardF hp2 h5
      have e' : ↥K ≃* PG (ModelData.uni hcardF) := e
      have hcc := Ivk413.core_clauses hG (Ivk413.autInner_uni hcardF hp2 hG)
        (Ivk413.ratio_uni hcardF hp2 h5 hodd2 hq8) K hC e' hz S hzS hz2 hSc
      refine ⟨⟨-1, Or.inr rfl, hn8, hU'⟩, hcc.1, hcc.2.1, hcc.2.2, ?_⟩
      rw [← hcc.2.1]
      exact (Subgroup.map_subtype_le _).trans inf_le_right

end CFSG.GH74.GLS.IVK.Proofs2
