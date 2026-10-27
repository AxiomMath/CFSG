module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Slp
public import CFSG.Sporadic.Schreier.J4SSylow
public import Certificates.Certificate12610

public noncomputable section

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_mem_of_orderOf_prime {G : Type*} [Group G] [Finite G] (p n : ℕ)
    [hp : Fact p.Prime] (Q : Subgroup G) (hQ : Nat.card Q = p ^ n)
    (hG : ¬ p ^ (n + 1) ∣ Nat.card G) {g : G} (hg : orderOf g = p) :
    ∃ h : G, h⁻¹ * g * h ∈ Q := by
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card G).factorization p = n := by
    have h3 : p ^ n ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mp h3
    have b : ¬ n + 1 ≤ (Nat.card G).factorization p := fun h =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mpr h)
    omega
  let P₀ : Sylow p G := Sylow.ofCard Q (by rw [hQ, hfac])
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; simp)
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P'
  refine ⟨h, ?_⟩
  have hgP' : g ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers g)
  have : (P' : Subgroup G) = (h • P₀ : Sylow p G) := by rw [hh]
  rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgP'
  exact hgP'

section Main

theorem threeOK_true : threeOK = true := Certificates.certificate12610

theorem threeOK_parts :
    threeProg.all (Instr.lt threeN) = true ∧ cEOK = true ∧ O.eq (eP 0).1 O.one = true ∧
    (List.range 27).all (fun k => (List.range 27).all fun l =>
      (List.range 27).any fun m => O.eq (mulP (eP k) (eP l)).1 (eP m).1) = true ∧
    (List.range 27).all (fun k => (List.range 27).any fun m =>
      O.eq (invP (eP k)).1 (eP m).1) = true ∧
    (List.range 27).all (fun k => (List.range 27).all fun l =>
      k == l || neOK (eP k).1 (eP l).1) = true ∧
    (List.range 27).all (fun k => k == 0 ||
      O.eq (mulP (mulP (gP k) (eP k)) (invP (gP k))).1 cEr) = true := by
  have h := threeOK_true
  unfold threeOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

@[expose] def tE (r : ℕ) : J := slpRegs threeProg r

theorem rep_threeReg {r : ℕ} (hr : r < threeN) : Rep Sp φ (tE r) threeRegs[r]! :=
  rep_slpRegs (n := threeN) threeOK_parts.1 hr

theorem rep_eK {k : ℕ} (hk : k < 27) : Rep Sp φ (tE (70 + k)) (eP k) :=
  rep_threeReg (by unfold threeN; omega)

theorem rep_gK {k : ℕ} (hk : k < 27) : Rep Sp φ (tE (110 + k)) (gP k) :=
  rep_threeReg (by unfold threeN; omega)

theorem e0_eq_one : tE 70 = 1 := by
  have h : tE (70 + 0) = tE 70 := rfl
  exact eq_of_rep (rep_eK (k := 0) (by norm_num)) rep_oneP threeOK_parts.2.2.1

theorem e_mul_mem {k l : ℕ} (hk : k < 27) (hl : l < 27) :
    ∃ m < 27, tE (70 + k) * tE (70 + l) = tE (70 + m) := by
  have h := threeOK_parts.2.2.2.1
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨m, hm, hm'⟩ := h k hk l hl
  exact ⟨m, hm, eq_of_rep (rep_mulP (rep_eK hk) (rep_eK hl)) (rep_eK hm) hm'⟩

theorem e_inv_mem {k : ℕ} (hk : k < 27) : ∃ m < 27, (tE (70 + k))⁻¹ = tE (70 + m) := by
  have h := threeOK_parts.2.2.2.2.1
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨m, hm, hm'⟩ := h k hk
  exact ⟨m, hm, eq_of_rep (rep_invP (rep_eK hk)) (rep_eK hm) hm'⟩

theorem e_injective {k l : ℕ} (hk : k < 27) (hl : l < 27) (h : tE (70 + k) = tE (70 + l)) :
    k = l := by
  by_contra hne
  have h6 := threeOK_parts.2.2.2.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h6
  rcases h6 k hk l hl with e | e
  · exact hne e
  · have hr1 := rep_eK hk
    have hr2 := rep_eK hl
    refine ne_of_neOK hr1.1 hr2.1 e ?_
    rw [hr1.2.2.1, hr2.2.2.1, h]

theorem g_conj {k : ℕ} (hk : k < 27) (hk0 : k ≠ 0) :
    tE (110 + k) * tE (70 + k) * (tE (110 + k))⁻¹ = cE := by
  have h := threeOK_parts.2.2.2.2.2.2
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h k hk with e | e
  · exact absurd e hk0
  · exact eq_of_rep (rep_mulP (rep_mulP (rep_gK hk) (rep_eK hk)) (rep_invP (rep_gK hk)))
      (rep_cE_of threeOK_parts.2.1) e

@[expose] def eEl (k : Fin 27) : J := tE (70 + k.val)

theorem eEl_injective : Function.Injective eEl := fun k l h =>
  Fin.ext (e_injective k.2 l.2 h)

@[expose] def Q3J : Subgroup J where
  carrier := Set.range eEl
  mul_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
    obtain ⟨m, hm, e⟩ := e_mul_mem k.2 l.2
    exact ⟨⟨m, hm⟩, e.symm⟩
  one_mem' := ⟨⟨0, by norm_num⟩, e0_eq_one⟩
  inv_mem' := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨m, hm, e⟩ := e_inv_mem k.2
    exact ⟨⟨m, hm⟩, e.symm⟩

theorem card_Q3J : Nat.card Q3J = 3 ^ 3 := by
  have h : Nat.card Q3J = Nat.card (Set.range eEl) := rfl
  rw [h, Nat.card_range_of_injective eEl_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem not_three_pow_four_dvd : ¬ 3 ^ (3 + 1) ∣ Nat.card J := by
  rw [card_J4J]
  norm_num

theorem exists_conj_cE_of_orderThree (b : J) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ g : J, g * b * g⁻¹ = cE := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb hb1
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf_prime 3 3 Q3J card_Q3J not_three_pow_four_dvd hord
  obtain ⟨⟨k, hk⟩, hke⟩ := hh
  change tE (70 + k) = h⁻¹ * b * h at hke
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h0 : tE 70 = h⁻¹ * b * h := hke
    rw [e0_eq_one] at h0
    apply hb1
    have : b = h * (h⁻¹ * b * h) * h⁻¹ := by group
    rw [this, ← h0]; group
  refine ⟨tE (110 + k) * h⁻¹, ?_⟩
  have e1 : tE (110 + k) * h⁻¹ * b * (tE (110 + k) * h⁻¹)⁻¹ =
      tE (110 + k) * (h⁻¹ * b * h) * (tE (110 + k))⁻¹ := by group
  rw [e1, ← hke]
  exact g_conj hk hk0

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
