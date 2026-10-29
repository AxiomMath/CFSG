module

import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitComp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp cjComp_one cjComp_mul mem_cjComp_iff
  mem_cjComp_of_mem layerMul_injective conj_eq_π π π_conj π_ext π_mem π_mul π_pow π_inv
  conj_mem_layer coord)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x : Y}

theorem π_congr' (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (C : ComponentIndex Y) {a b : Y}
    (ha : a ∈ layer Y) (hb : b ∈ layer Y) (h : a = b) : π hZ C a ha = π hZ C b hb := by
  subst h
  rfl

theorem π_conj_of_comm (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {g b : Y}
    (hb : b ∈ layer Y) (hgb : g * b * g⁻¹ = b) (C : ComponentIndex Y) :
    π hZ (cjComp g C) b hb = g * π hZ C b hb * g⁻¹ := by
  rw [← π_conj (hZ := hZ) g C hb]
  exact (π_congr' hZ (cjComp g C) (conj_mem_layer g hb) hb hgb).symm

@[expose] noncomputable def coordHom (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥)
    (C : ComponentIndex Y) : ↥(layer Y) →* Y :=
  C.1.subtype.comp (coord hZ C)

theorem coordHom_mem (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (C : ComponentIndex Y)
    (a : ↥(layer Y)) : coordHom hZ C a ∈ C.1 := (coord hZ C a).2

theorem card_le_of_le_layer (h : SplitCfg p P x) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEl : E ≤ layer Y) : Nat.card E ≤ p ^ p := by
  let Fc : ComponentIndex Y → Subgroup Y := fun C =>
    (E.subgroupOf (layer Y)).map (coordHom h.centre C)
  have hFc : ∀ C : ComponentIndex Y, Nat.card (Fc C) ≤ p := fun C => by
    refine card_le_comp h C ?_ ((hE.subgroupOf (layer Y)).map _)
    rintro _ ⟨a, -, rfl⟩
    exact coordHom_mem h.centre C a
  let ι : ↥E → ∀ C : ComponentIndex Y, ↥(Fc C) := fun e C =>
    ⟨coordHom h.centre C ⟨e, hEl e.2⟩, ⟨⟨e, hEl e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro e e' hee'
    apply Subtype.ext
    refine π_ext (hZ := h.centre) (hEl e.2) (hEl e'.2) fun C => ?_
    have := congrArg Subtype.val (congrFun hee' C)
    exact this
  have h1 := Nat.card_le_card_of_injective ι hι
  rw [Nat.card_pi] at h1
  refine h1.trans ?_
  calc ∏ C, Nat.card (Fc C) ≤ p ^ (Finset.univ : Finset (ComponentIndex Y)).card :=
      Finset.prod_le_pow_card _ _ _ fun C _ => hFc C
    _ = p ^ p := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card_comp]

theorem card_le_sq_of_not_le (h : SplitCfg p P x) (hl : compKer P ≤ layer Y) {E : Subgroup Y}
    (hEP : E ≤ P) (hE : IsElemAbelian p E) {e : Y} (heE : e ∈ E) (hne : e ∉ compKer P) :
    Nat.card E ≤ p * p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hEc, hEp⟩ := (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).mp hE
  have hep : e ^ p = 1 := hEp e heE
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ComponentIndex Y, cjComp e C₁ ≠ C₁ := by
    by_contra hall
    push Not at hall
    exact hne ⟨hEP heE, hall⟩
  letI := compAction Y
  have htr : ∀ α β : ComponentIndex Y, ∃ k : ℕ, cjComp (e ^ k) α = β :=
    cycle_trans (G := Y) (Ω := ComponentIndex Y) h.prime h.card_comp hep (ω := C₁) hC₁
  obtain ⟨L0⟩ : Nonempty (ComponentIndex Y) :=
    Finite.card_pos_iff.mp (by rw [h.card_comp]; exact h.prime.pos)
  let B : Subgroup Y := E ⊓ compKer P
  have hBl : B ≤ layer Y := inf_le_right.trans hl
  let gB : ↥B →* Y := (coordHom h.centre L0).comp (Subgroup.inclusion hBl)
  have hgB : Function.Injective gB := by
    intro b b' hbb'
    apply Subtype.ext
    have hbl : (b : Y) ∈ layer Y := hBl b.2
    have hb'l : (b' : Y) ∈ layer Y := hBl b'.2
    refine π_ext (hZ := h.centre) hbl hb'l fun C => ?_
    obtain ⟨k, rfl⟩ := htr L0 C
    have hek : e ^ k ∈ E := E.pow_mem heE k
    have hc1 : (e ^ k) * (b : Y) * (e ^ k)⁻¹ = b := by
      rw [hEc _ hek b b.2.1, mul_inv_cancel_right]
    have hc2 : (e ^ k) * (b' : Y) * (e ^ k)⁻¹ = b' := by
      rw [hEc _ hek b' b'.2.1, mul_inv_cancel_right]
    rw [π_conj_of_comm h.centre hbl hc1, π_conj_of_comm h.centre hb'l hc2]
    have : π h.centre L0 (b : Y) hbl = π h.centre L0 (b' : Y) hb'l := hbb'
    rw [this]
  have hFB : IsElemAbelian p gB.range := by
    refine (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).mpr ⟨?_, ?_⟩
    · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc b b.2.1 b' b'.2.1)
    · rintro _ ⟨b, rfl⟩
      rw [← map_pow]
      have : b ^ p = 1 := Subtype.ext (by simpa using hEp b b.2.1)
      rw [this, map_one]
  have hFBC : gB.range ≤ L0.1 := by
    rintro _ ⟨b, rfl⟩
    exact coordHom_mem h.centre L0 (Subgroup.inclusion hBl b)
  have hBcard : Nat.card B ≤ p := by
    have h1 := Nat.card_le_card_of_injective (gB.rangeRestrict)
      (MonoidHom.rangeRestrict_injective_iff.mpr hgB)
    exact h1.trans (card_le_comp h L0 hFBC hFB)
  have hsurj : Function.Surjective (fun kg : Fin p × ↥B =>
      (⟨e ^ (kg.1 : ℕ) * (kg.2 : Y), E.mul_mem (E.pow_mem heE _) kg.2.2.1⟩ : ↥E)) := by
    rintro ⟨e', he'⟩
    obtain ⟨k, hk⟩ := htr L0 (cjComp e' L0)
    have hgE : (e ^ k)⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem (E.pow_mem heE k)) he'
    have hgQ : (e ^ k)⁻¹ * e' ∈ compKer P := by
      refine ⟨hEP hgE, fun C => ?_⟩
      obtain ⟨m, rfl⟩ := htr L0 C
      have hL0 : cjComp ((e ^ k)⁻¹ * e') L0 = L0 := by
        rw [cjComp_mul, ← hk, ← cjComp_mul, inv_mul_cancel, cjComp_one]
      have hcomm := hEc _ hgE (e ^ m) (E.pow_mem heE m)
      rw [← cjComp_mul, hcomm, cjComp_mul, hL0]
    refine ⟨(⟨(k % p : ℕ), Nat.mod_lt k h.prime.pos⟩, ⟨(e ^ k)⁻¹ * e', hgE, hgQ⟩), ?_⟩
    apply Subtype.ext
    show e ^ (k % p) * ((e ^ k)⁻¹ * e') = e'
    rw [← pow_eq_pow_mod k hep]
    group
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at h1
  exact h1.trans (Nat.mul_le_mul_left p hBcard)

theorem card_le_of_compKer_le_layer (h : SplitCfg p P x) (hl : compKer P ≤ layer Y)
    {E : Subgroup Y} (hEP : E ≤ P) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ p := by
  by_cases hEQ : E ≤ compKer P
  · exact card_le_of_le_layer h hE (hEQ.trans hl)
  · obtain ⟨e, heE, hne⟩ := Set.not_subset.mp hEQ
    have h1 := card_le_sq_of_not_le h hl hEP hE heE hne
    refine h1.trans ?_
    rw [← sq]
    exact Nat.pow_le_pow_right h.prime.pos (by have := h.five_le; omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
