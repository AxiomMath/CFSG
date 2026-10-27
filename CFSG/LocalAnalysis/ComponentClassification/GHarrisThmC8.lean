module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.GL42

open Matrix Subgroup

theorem card_GL4 : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_mulAut_A5 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))), Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem toMat_ofMat (M : M4) : (M4c.ofMat M).toMat = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

namespace SylE0

variable {G : Type*} [Group G] [Finite G] (P : SylE0 G)

omit [Finite G] in
theorem card_S_le : Nat.card P.S ≤ 4 := by
  let f : P.S → e0c.toFinset := fun s => ⟨M4c.ofMat (P.mat s), by
    obtain ⟨e, he, hes⟩ := P.exists_e0 s.2
    rw [← hes, M4c.ofMat_toMat]
    exact List.mem_toFinset.mpr he⟩
  have hf : Function.Injective f := fun s t hst => Subtype.ext (P.mat_inj (by
    have h := congrArg (fun x : e0c.toFinset => (x : M4c).toMat) hst
    simpa only [f, toMat_ofMat] using h))
  have h4 : Nat.card e0c.toFinset = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  exact h4 ▸ Nat.card_le_card_of_injective f hf

include P in
theorem not_eight_dvd : ¬ 8 ∣ Nat.card G := by
  intro h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sylow.pow_dvd_card_of_pow_dvd_card (n := 3) P.S (by norm_num; exact h8)
  have := Nat.le_of_dvd Nat.card_pos h
  have := P.card_S_le
  norm_num at *
  omega

omit [Finite G] in
include P in
theorem card_dvd : Nat.card G ∣ 20160 :=
  card_GL4 ▸ Subgroup.card_dvd_of_injective P.ρ P.inj

theorem iso_a5
    (hn : ∃ h : G, ∃ x ∈ P.S, h * x * h⁻¹ ∉ P.S) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  obtain ⟨h₀, k, hk, ws, hk70, hws, hC⟩ := P.exists_orbit hn
  have hCm : ∀ c ∈ conjAt k, ∃ g, P.mat g = c.toMat := fun c hc => by
    obtain ⟨s, -, hs⟩ := hC c hc
    exact ⟨_, hs⟩
  have hmem := P.exists_mat_a5 hk hCm
  set ι := P.a5Hom (a5Idx k) (a5_words hk).1 hmem with hι
  set L := ι.range with hL
  have hLn : L.Normal := P.a5_normal hk hC hmem
  have hιinj : Function.Injective ι := P.a5Hom_injective _ hmem
  let eL : alternatingGroup (Fin 5) ≃* L := ι.ofInjective hιinj
  have hcardL : Nat.card L = 60 := by rw [← Nat.card_congr eL.toEquiv, card_A5]
  have hZL : ∀ l ∈ L, (∀ l' ∈ L, l * l' = l' * l) → l = 1 := by
    rintro _ ⟨p, rfl⟩ hc
    have hp : p ∈ center (alternatingGroup (Fin 5)) := mem_center_iff.mpr fun q =>
      hιinj (by rw [map_mul, map_mul]; exact (hc _ ⟨q, rfl⟩).symm)
    rw [alternatingGroup.center_eq_bot (by simp)] at hp
    rw [mem_bot.mp hp, map_one]
  let κ : G →* MulAut L := MulAut.conjNormal
  have hmemC : ∀ c : G, c ∈ κ.ker ↔ ∀ l ∈ L, c * l = l * c := by
    intro c
    rw [MonoidHom.mem_ker]
    constructor
    · intro hc l hl
      have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) hc
      simp only [κ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc c * l = c * l * c⁻¹ * c := by group
        _ = l * c := by rw [h1]
    · intro hc
      ext l
      simp only [κ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [hc l l.2, mul_inv_cancel_right]
  have hcard : Nat.card G = Nat.card κ.ker * Nat.card κ.range := by
    rw [← index_ker κ, card_mul_index]
  have hrange120 : Nat.card κ.range ∣ 120 := by
    rw [← card_mulAut_A5, Nat.card_congr (MulAut.congr eL).toEquiv]
    exact card_subgroup_dvd_card _
  have hrange60 : 60 ∣ Nat.card κ.range := by
    have hinj : Function.Injective (κ.comp L.subtype) := by
      rw [injective_iff_map_eq_one]
      intro l hl
      have h1 : (l : G) ∈ κ.ker := hl
      exact Subtype.ext (hZL l l.2 fun l' hl' => ((hmemC l).mp h1 l' hl'))
    have h1 : (κ.comp L.subtype).range ≤ κ.range := by
      rintro _ ⟨l, rfl⟩
      exact ⟨l, rfl⟩
    have h2 := card_dvd_of_le h1
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardL] at h2
  have hrange : Nat.card κ.range = 60 := by
    obtain ⟨m, hm⟩ := hrange60
    rw [hm] at hrange120
    have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 60)
      (by rw [show (60 * 2 : ℕ) = 120 by norm_num]; exact hrange120)
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h | h
    · rw [hm, h]
    · exfalso
      apply P.not_eight_dvd
      rw [hcard, hm, h]
      exact Dvd.dvd.mul_left (by norm_num) _
  rw [hrange] at hcard
  set C := κ.ker with hCdef
  have hCdvd : Nat.card C ∣ 336 := by
    have h := P.card_dvd
    rw [hcard, show (20160 : ℕ) = 336 * 60 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
  have hCodd : ¬ 2 ∣ Nat.card C := by
    intro h2
    apply P.not_eight_dvd
    rw [hcard]
    obtain ⟨m, hm⟩ := h2
    rw [hm]
    exact ⟨15 * m, by ring⟩
  have hC7 : ¬ 7 ∣ Nat.card C := by
    intro h7
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hc7 : (P.ρ (c : G)) ^ 7 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
    obtain ⟨v, hv0, hv⟩ := exists_fixed_of_pow_seven hc7
    obtain ⟨l₁, hl₁, hl₁v⟩ := P.a5_transitive hk hk70 hws hCm hmem hv0
    have hfix : ∀ w : Fin 4 → ZMod 2, P.mat c *ᵥ w = w := by
      intro w
      by_cases hw0 : w = 0
      · rw [hw0, mulVec_zero]
      obtain ⟨l₂, hl₂, hl₂w⟩ := P.a5_transitive hk hk70 hws hCm hmem hw0
      have hl : l₂ * l₁⁻¹ ∈ L := mul_mem hl₂ (inv_mem hl₁)
      have hw : w = P.mat (l₂ * l₁⁻¹) *ᵥ v := by
        rw [← hl₁v, mulVec_mulVec, ← P.mat_mul, inv_mul_cancel_right, hl₂w]
      have hcl := (hmemC c).mp c.2 _ hl
      rw [hw, mulVec_mulVec, ← P.mat_mul, hcl, P.mat_mul, ← mulVec_mulVec]
      change P.mat (l₂ * l₁⁻¹) *ᵥ (((P.ρ (c : G) : GL4) : M4) *ᵥ v) = _
      rw [hv]
    have h1 : (c : G) = 1 := P.mat_inj (by rw [eq_one_of_mulVec_eq hfix, P.mat_one])
    have h2 : c = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hC3 : Nat.card C = 1 ∨ Nat.card C = 3 := by
    have hcop2 : Nat.Coprime (Nat.card C) 16 :=
      Nat.Coprime.pow_right 4 ((Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hCodd)))
    have h21 : Nat.card C ∣ 21 :=
      hcop2.dvd_of_dvd_mul_left (by rw [show (16 * 21 : ℕ) = 336 by norm_num]; exact hCdvd)
    have hcop7 : Nat.Coprime (Nat.card C) 7 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hC7)
    have h3 : Nat.card C ∣ 3 :=
      hcop7.dvd_of_dvd_mul_right (by rw [show (3 * 7 : ℕ) = 21 by norm_num]; exact h21)
    exact (Nat.dvd_prime Nat.prime_three).mp h3
  rcases hC3 with h1 | h3
  ·
    left
    rw [h1, one_mul] at hcard
    have hLtop : L = ⊤ := eq_top_of_card_eq L (by rw [hcardL, hcard])
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans eL.symm⟩
  ·
    right
    have hcomm : ∀ (c : C) (l : L), Commute (C.subtype c) (L.subtype l) :=
      fun c l => (hmemC c).mp c.2 l l.2
    let φ : C × L →* G := MonoidHom.noncommCoprod C.subtype L.subtype hcomm
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨c, l⟩ hcl
      change (c : G) * (l : G) = 1 at hcl
      have hcL : (c : G) ∈ L := by
        rw [show (c : G) = (l : G)⁻¹ from eq_inv_of_mul_eq_one_left hcl]
        exact inv_mem l.2
      have hc1 : (c : G) = 1 := hZL _ hcL fun l' hl' => (hmemC c).mp c.2 l' hl'
      have hl1 : (l : G) = 1 := by rw [hc1, one_mul] at hcl; exact hcl
      exact Prod.ext (Subtype.ext hc1) (Subtype.ext hl1)
    have hφbij : Function.Bijective φ := hφinj.bijective_of_nat_card_le (by
      rw [Nat.card_prod, h3, hcardL, hcard, h3])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact ⟨(MulEquiv.ofBijective φ hφbij).symm.trans
      (MulEquiv.prodCongr (mulEquivOfPrimeCardEq h3 hZ3) eL.symm)⟩

end SylE0

end CFSG.ComponentClassification.GHarris.GL42
