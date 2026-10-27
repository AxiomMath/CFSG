module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveIrred

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_mulAut_of_card_eq_27 {D : Type} [Group D] [Finite D]
    (hDc : IsMulCommutative D) (hD3 : ∀ x : D, x ^ 3 = 1) (hD : Nat.card D = 27) :
    Nat.card (MulAut D) = 11232 := by
  have hcard3 : Nat.card D = 3 ^ 3 := by rw [hD]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 3) (W := D) (n := 3) (fun a b => hDc.is_comm.comm a b) hD3 hcard3
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 3) e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) 3, Fin.prod_univ_three]
  norm_num

theorem card_range_eq_thirteen_or_isSLType (h67 : SixSeven) {D : Subgroup G}
    (hDab : CFSG.Open.IsElemAbelian 3 D) (hD27 : Nat.card D = 27) {S : Set G}
    (hS13 : ∀ s ∈ S, ∃ n : ℕ, s ^ 13 ^ n = 1) {y : G} (hyS : y ∈ S)
    (hyD : ∃ d ∈ D, y * d * y⁻¹ ≠ d) (φ : ↥(closure S) →* MulAut ↥D)
    (hφ : ∀ (a : ↥(closure S)) (d : ↥D), ((φ a d : ↥D) : G) = (a : G) * d * (a : G)⁻¹) :
    Nat.card φ.range = 13 ∨ IsSLType 3 (ZMod 3) ↥φ.range := by
  have hDc : IsMulCommutative ↥D := hDab.1
  have hD3 : ∀ x : ↥D, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hDab.2 (x : G) x.2
  have hcardAut : Nat.card (MulAut ↥D) = 11232 :=
    card_mulAut_of_card_eq_27 hDc hD3 hD27
  let K := Subgroup.closure S
  let S' : Set ↥K := ((↑) : ↥K → G) ⁻¹' S
  have htop : (⊤ : Subgroup ↥K) = Subgroup.closure S' := by
    rw [show S' = ((↑) : ↥K → G) ⁻¹' S from rfl]
    exact (Subgroup.closure_closure_coe_preimage (k := S)).symm
  have hWS : φ.range = Subgroup.closure (φ '' S') := by
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  have hgen : ∀ x ∈ φ '' S', x ^ 13 = 1 := by
    rintro x ⟨s, hs, rfl⟩
    obtain ⟨n, hn⟩ := hS13 (s : G) hs
    have hsK : (s : ↥K) ^ 13 ^ n = 1 := by
      apply Subtype.ext
      simpa using hn
    have hdvd1 : orderOf (φ s) ∣ 13 ^ n :=
      dvd_trans (orderOf_map_dvd φ s) (orderOf_dvd_of_pow_eq_one hsK)
    have hdvd2 : orderOf (φ s) ∣ 11232 := by
      rw [← hcardAut]
      exact orderOf_dvd_natCard _
    have hcop13 : Nat.Coprime (13 ^ n) 864 :=
      Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 13 864)
    have hcop : Nat.Coprime (orderOf (φ s)) 864 :=
      Nat.Coprime.coprime_dvd_left hdvd1 hcop13
    have hdvd13 : orderOf (φ s) ∣ 13 := by
      have hdvd2' : orderOf (φ s) ∣ 13 * 864 := by
        rwa [show 11232 = 13 * 864 by norm_num] at hdvd2
      exact (Nat.Coprime.dvd_mul_right hcop).mp hdvd2'
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd13
  let y' : ↥K := ⟨y, Subgroup.subset_closure hyS⟩
  have hy'ne : φ y' ≠ 1 := by
    intro h1
    obtain ⟨d, hdD, hdne⟩ := hyD
    have h := hφ y' ⟨d, hdD⟩
    rw [h1] at h
    have h' : d = y * d * y⁻¹ := by simpa using h
    exact hdne h'.symm
  have hy'mem : φ y' ∈ φ '' S' := ⟨y', hyS, rfl⟩
  have horder : orderOf (φ y') = 13 := by
    have hdvd : orderOf (φ y') ∣ 13 :=
      orderOf_dvd_of_pow_eq_one (hgen (φ y') hy'mem)
    rcases (by norm_num : Nat.Prime 13).eq_one_or_self_of_dvd (orderOf (φ y')) hdvd with
      h1 | h13
    · exact absurd (orderOf_eq_one_iff.mp h1) hy'ne
    · exact h13
  have hW : IsIrreducibleAut φ.range :=
    isIrreducibleAut_of_orderOf_eq_thirteen (D := ↥D) hD27
      (MonoidHom.mem_range.mpr ⟨y', rfl⟩) horder
  exact sixSeven_of_pow_thirteen h67 hDc hD3 hD27 hW hgen hWS

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
