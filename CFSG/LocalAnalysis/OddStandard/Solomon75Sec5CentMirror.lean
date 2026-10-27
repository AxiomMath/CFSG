module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseZ
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Mirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

namespace Sec5Data

theorem isSec5Pair_of_mem (h : Sec5Data X n z Z S) {u : X} (hu : u ∈ Z) (hu1 : u ≠ 1) :
    IsSec5Pair X n u Z where
  orderOf_z := h.orderOf_eq_two_of_mem_Z hu hu1
  mem := hu
  sylow := h.pair.isSylowTwoIn_zStar_K0_centralizer h.hypA h.maxdeg (Subgroup.le_normalizer hu)
    (h.orderOf_eq_two_of_mem_Z hu hu1) (h.comm_mem_pPrimeCoreOf hu)

theorem withPair (h : Sec5Data X n z Z S) {u : X} (hu : u ∈ Z) (hu1 : u ≠ 1) :
    Sec5Data X n u Z S :=
  { h with pair := h.isSec5Pair_of_mem hu hu1 }

end Sec5Data

theorem IsSylowTwoIn.exists_conj_eq {W P Q : Subgroup X} (hP : IsSylowTwoIn W P)
    (hQ : IsSylowTwoIn W Q) : ∃ y ∈ W, Q = P.map (MulAut.conj y).toMonoidHom := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPW, hPp, hPidx⟩ := hP
  obtain ⟨hQW, hQp, hQidx⟩ := hQ
  let P' : Sylow 2 ↥W := IsPGroup.toSylow (P := P.subgroupOf W)
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm) hPidx
  let Q' : Sylow 2 ↥W := IsPGroup.toSylow (P := Q.subgroupOf W)
    (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQW).symm) hQidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) P' Q'
  refine ⟨(g : X), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxW : x ∈ W := hQW hx
    have hmem : (⟨x, hxW⟩ : ↥W) ∈ ((g • P' : Sylow 2 ↥W) : Subgroup ↥W) := by
      rw [hg]; exact hx
    rw [mem_smul_sylow_iff] at hmem
    have h2 : (g : X)⁻¹ * x * g ∈ P := hmem
    exact ⟨(g : X)⁻¹ * x * g, h2, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    have hyW : y ∈ W := hPW hy
    have hmem : (⟨(g : X) * y * (g : X)⁻¹, mul_mem (mul_mem g.2 hyW) (inv_mem g.2)⟩ : ↥W) ∈
        ((g • P' : Sylow 2 ↥W) : Subgroup ↥W) := by
      rw [mem_smul_sylow_iff]
      show (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * g ∈ P
      simpa [mul_assoc] using hy
    rw [hg] at hmem
    exact hmem


theorem exists_isSylowTwoIn_normalized {Y B : Subgroup X} (hB : IsPGroup 2 ↥B)
    (hBY : B ≤ normalizer (Y : Set X)) :
    ∃ Zs : Subgroup X, IsSylowTwoIn Y Zs ∧ B ≤ normalizer (Zs : Set X) ∧ B ⊓ Y ≤ Zs := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_normalized hB hBY
  set Zs : Subgroup X := (Q : Subgroup ↥Y).map Y.subtype with hZs
  have hsyl : IsSylowTwoIn Y Zs := by
    refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map Y.subtype, ?_⟩
    show ¬ 2 ∣ (Zs.subgroupOf Y).index
    have : Zs.subgroupOf Y = (Q : Subgroup ↥Y) := by
      rw [hZs, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
    rw [this]
    exact Q.not_dvd_index
  refine ⟨Zs, hsyl, hQ, ?_⟩
  rintro b ⟨hbB, hbY⟩
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  have hbk : orderOf (⟨b, hbB⟩ : ↥B) ∣ 2 ^ k := hk ▸ orderOf_dvd_natCard _
  have hbk' : orderOf (⟨b, hbY⟩ : ↥Y) ∣ 2 ^ k := by
    have : orderOf (⟨b, hbY⟩ : ↥Y) = orderOf (⟨b, hbB⟩ : ↥B) := by
      rw [← Subgroup.orderOf_coe (⟨b, hbY⟩ : ↥Y), ← Subgroup.orderOf_coe (⟨b, hbB⟩ : ↥B)]
    rw [this]; exact hbk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hbk'
  have hP : IsPGroup 2 ↥(Subgroup.zpowers (⟨b, hbY⟩ : ↥Y)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hbn : (⟨b, hbY⟩ : ↥Y) ∈ Subgroup.normalizer ((Q : Subgroup ↥Y) : Set ↥Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hQ hbB) (x : X)
    have e1 : (x : X) ∈ Zs ↔ x ∈ (Q : Subgroup ↥Y) :=
      Subgroup.mem_map_iff_mem (f := Y.subtype) Y.subtype_injective
    have e2 : b * (x : X) * b⁻¹ ∈ Zs ↔ (⟨b, hbY⟩ : ↥Y) * x * (⟨b, hbY⟩ : ↥Y)⁻¹ ∈
        (Q : Subgroup ↥Y) :=
      Subgroup.mem_map_iff_mem (f := Y.subtype) Y.subtype_injective
        (x := (⟨b, hbY⟩ : ↥Y) * x * (⟨b, hbY⟩ : ↥Y)⁻¹)
    exact e1.symm.trans (h1.trans e2)
  have key := hP.inf_normalizer_sylow Q
  have hmem : (⟨b, hbY⟩ : ↥Y) ∈ Subgroup.zpowers (⟨b, hbY⟩ : ↥Y) ⊓ Subgroup.normalizer
      ((Q : Subgroup ↥Y) : Set ↥Y) := ⟨Subgroup.mem_zpowers _, hbn⟩
  have hmem' : (⟨b, hbY⟩ : ↥Y) ∈ Subgroup.zpowers (⟨b, hbY⟩ : ↥Y) ⊓ (Q : Subgroup ↥Y) := by
    rw [← key]; exact hmem
  exact ⟨⟨b, hbY⟩, hmem'.2, rfl⟩


omit [Finite X] in
theorem le_normalizer_zStar_of_le_normalizer {K B : Subgroup X}
    (hB : B ≤ normalizer (K : Set X)) : B ≤ normalizer (zStar K : Set X) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_zStar (hB hb) hx, fun hx => ?_⟩
  have h1 := conj_mem_zStar ((normalizer (K : Set X)).inv_mem (hB hb)) hx
  simpa [mul_assoc] using h1

theorem exists_mirror_sylow_normalized (X : Type) [Group X] [Finite X] (n : ℕ) {s : X}
    {B : Subgroup X} (hB : IsPGroup 2 ↥B) (hBC : B ≤ centralizer ({s} : Set X)) :
    ∃ Zs : Subgroup X, IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Zs ∧
      B ≤ normalizer (Zs : Set X) ∧ B ⊓ zStar (K0 X n (centralizer ({s} : Set X))) ≤ Zs := by
  refine exists_isSylowTwoIn_normalized hB (le_normalizer_zStar_of_le_normalizer ?_)
  intro b hb
  exact mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer (hBC hb)))

namespace Sec5Data

theorem exists_mirror_inv (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) :
    ∃ (g : X) (S₁ : Sylow 2 ↥(normalizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup X) :
      Set X))), g⁻¹ * s * g ∈ Z ∧ g⁻¹ * s * g ≠ 1 ∧
        Sec5Data X n s (Z.map (MulAut.conj g).toMonoidHom) S₁ := by
  obtain ⟨g, hg1, hg2⟩ := hs.conj
  obtain ⟨S₁, -, hS₁⟩ := (h.withPair hg1 hg2).map (MulAut.conj g)
  have hz : (MulAut.conj g) (g⁻¹ * s * g) = s := by simp [MulAut.conj_apply, mul_assoc]
  rw [hz] at hS₁
  exact ⟨g, S₁, hg1, hg2, hS₁⟩

theorem exists_mirror_of_sylow (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {Zs : Subgroup X} (hZs : IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Zs) :
    ∃ (g : X) (S₁ : Sylow 2 ↥(normalizer (Zs : Set X))), Zs = Z.map (MulAut.conj g).toMonoidHom ∧
      g⁻¹ * s * g ∈ Z ∧ g⁻¹ * s * g ≠ 1 ∧ Sec5Data X n s Zs S₁ := by
  obtain ⟨g, S₁, hg1, hg2, hS₁⟩ := h.exists_mirror_inv hs
  obtain ⟨y, hy, hyeq⟩ := hS₁.pair.sylow.exists_conj_eq hZs
  have hyC : y ∈ centralizer ({s} : Set X) := (K0_le n _) hy.1
  have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
  obtain ⟨S₂, -, hS₂⟩ := hS₁.map (MulAut.conj y)
  have hz : (MulAut.conj y) s = s := by
    rw [MulAut.conj_apply, hys]; group
  rw [hz] at hS₂
  have hconj : (y * g)⁻¹ * s * (y * g) = g⁻¹ * s * g := by
    have h1 : y⁻¹ * s * y = s := by rw [mul_assoc, ← hys]; group
    calc (y * g)⁻¹ * s * (y * g) = g⁻¹ * (y⁻¹ * s * y) * g := by group
      _ = g⁻¹ * s * g := by rw [h1]
  subst hyeq
  refine ⟨y * g, S₂, ?_, by rw [hconj]; exact hg1, by rw [hconj]; exact hg2, hS₂⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_comp_centralizer (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) :
    ∃ B : Subgroup X, Sec5Comp X n (centralizer ({s} : Set X)) B ∧ B ≠ ⊥ := by
  obtain ⟨g, S₁, -, -, hS₁⟩ := h.exists_mirror_inv hs
  by_contra hcon
  push Not at hcon
  have h1 : K0 X n (centralizer ({s} : Set X)) = ⊥ := by
    rw [K0_eq_sSup_sec5Comp]
    exact le_bot_iff.1 (sSup_le fun B hB => (hcon B hB).le)
  apply hS₁.K0_ne_bot
  exact le_bot_iff.1 (hS₁.pair.K0_normalizer_le h.hypA h.maxdeg |>.trans h1.le)

end Sec5Data

theorem IsSylowTwoIn.mem_of_mem_normalizer {W P : Subgroup X} (h : IsSylowTwoIn W P) {b : X}
    (hbW : b ∈ W) (hb : IsPGroup 2 ↥(Subgroup.zpowers b)) (hbn : b ∈ normalizer (P : Set X)) :
    b ∈ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPW, hPp, hPidx⟩ := h
  let P' : Sylow 2 ↥W := IsPGroup.toSylow (P := P.subgroupOf W)
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm) hPidx
  have hbn' : (⟨b, hbW⟩ : ↥W) ∈ Subgroup.normalizer ((P' : Subgroup ↥W) : Set ↥W) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.1 hbn (x : X)
  have hP : IsPGroup 2 ↥(Subgroup.zpowers (⟨b, hbW⟩ : ↥W)) := by
    obtain ⟨k, hk⟩ := hb.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← hk, Nat.card_zpowers]
    exact (Subgroup.orderOf_coe (⟨b, hbW⟩ : ↥W)).symm
  have key := hP.inf_normalizer_sylow P'
  have hmem : (⟨b, hbW⟩ : ↥W) ∈ Subgroup.zpowers (⟨b, hbW⟩ : ↥W) ⊓
      Subgroup.normalizer ((P' : Subgroup ↥W) : Set ↥W) := ⟨Subgroup.mem_zpowers _, hbn'⟩
  have hmem' : (⟨b, hbW⟩ : ↥W) ∈ Subgroup.zpowers (⟨b, hbW⟩ : ↥W) ⊓ (P' : Subgroup ↥W) := by
    rw [← key]; exact hmem
  exact hmem'.2


end CFSG.OddStandard.Solomon75
