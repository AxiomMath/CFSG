module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix
open scoped MatrixGroups

section General

variable {G H : Type*} [Group G] [Group H]

theorem centralizer_singleton_prod (g : G) (h : H) :
    centralizer ({(g, h)} : Set (G × H)) = (centralizer {g}).prod (centralizer {h}) := by
  ext ⟨a, b⟩
  simp only [mem_centralizer_singleton_iff, mem_prod, Prod.mk_mul_mk, Prod.ext_iff]

theorem prod_le_normalizer_prod {A S₁ : Subgroup G} {B S₂ : Subgroup H}
    (hA : A ≤ normalizer (S₁ : Set G)) (hB : B ≤ normalizer (S₂ : Set H)) :
    A.prod B ≤ normalizer ((S₁.prod S₂ : Subgroup (G × H)) : Set (G × H)) := by
  rintro ⟨a, b⟩ hab
  rw [mem_prod] at hab
  rw [mem_normalizer_iff]
  rintro ⟨x, y⟩
  simp only [mem_prod, Prod.mk_mul_mk, Prod.inv_mk]
  exact and_congr (mem_normalizer_iff.1 (hA hab.1) x) (mem_normalizer_iff.1 (hB hab.2) y)

theorem prod_inf_centralizer_prod_eq_bot {A S₁ : Subgroup G} {B S₂ : Subgroup H}
    (hA : A ⊓ centralizer (S₁ : Set G) = ⊥) (hB : B ⊓ centralizer (S₂ : Set H) = ⊥) :
    A.prod B ⊓ centralizer ((S₁.prod S₂ : Subgroup (G × H)) : Set (G × H)) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro ⟨a, b⟩ hx
  rw [mem_inf, mem_prod, mem_centralizer_iff] at hx
  obtain ⟨⟨ha, hb⟩, hc⟩ := hx
  have ha1 : a ∈ A ⊓ centralizer (S₁ : Set G) := mem_inf.2 ⟨ha, mem_centralizer_iff.2
    fun s hs => congrArg Prod.fst (hc (s, 1) (mem_prod.2 ⟨hs, one_mem _⟩))⟩
  have hb1 : b ∈ B ⊓ centralizer (S₂ : Set H) := mem_inf.2 ⟨hb, mem_centralizer_iff.2
    fun s hs => congrArg Prod.snd (hc (1, s) (mem_prod.2 ⟨one_mem _, hs⟩))⟩
  rw [hA, mem_bot] at ha1
  rw [hB, mem_bot] at hb1
  rw [mem_bot, ha1, hb1, Prod.mk_one_one]

theorem fst_mem_normalizer_map_fst {S : Subgroup (G × H)} {x : G × H}
    (hx : x ∈ normalizer (S : Set (G × H))) :
    x.1 ∈ normalizer ((S.map (MonoidHom.fst G H) : Subgroup G) : Set G) := by
  have key : ∀ y ∈ normalizer (S : Set (G × H)), ∀ s ∈ S.map (MonoidHom.fst G H),
      y.1 * s * y.1⁻¹ ∈ S.map (MonoidHom.fst G H) := by
    rintro y hy _ ⟨t, ht, rfl⟩
    exact ⟨y * t * y⁻¹, (mem_normalizer_iff.1 hy t).1 ht, rfl⟩
  exact mem_normalizer_of_conj_mem (key x hx) (key x⁻¹ (inv_mem hx))

theorem snd_mem_normalizer_map_snd {S : Subgroup (G × H)} {x : G × H}
    (hx : x ∈ normalizer (S : Set (G × H))) :
    x.2 ∈ normalizer ((S.map (MonoidHom.snd G H) : Subgroup H) : Set H) := by
  have key : ∀ y ∈ normalizer (S : Set (G × H)), ∀ s ∈ S.map (MonoidHom.snd G H),
      y.2 * s * y.2⁻¹ ∈ S.map (MonoidHom.snd G H) := by
    rintro y hy _ ⟨t, ht, rfl⟩
    exact ⟨y * t * y⁻¹, (mem_normalizer_iff.1 hy t).1 ht, rfl⟩
  exact mem_normalizer_of_conj_mem (key x hx) (key x⁻¹ (inv_mem hx))

theorem card_prod_subgroup (A : Subgroup G) (B : Subgroup H) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

end General

variable {k : Type*} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem eq_prod_map_fst_map_snd [Finite k] {S : Subgroup (SL(2, k) × SL(2, k))}
    (hS : Nat.card S = Nat.card k ^ 2) :
    S = (S.map (MonoidHom.fst _ _)).prod (S.map (MonoidHom.snd _ _)) ∧
      Nat.card (S.map (MonoidHom.fst SL(2, k) SL(2, k))) = Nat.card k ∧
      Nat.card (S.map (MonoidHom.snd SL(2, k) SL(2, k))) = Nat.card k := by
  set S₁ := S.map (MonoidHom.fst SL(2, k) SL(2, k))
  set S₂ := S.map (MonoidHom.snd SL(2, k) SL(2, k))
  have hle : S ≤ S₁.prod S₂ := le_prod_iff.2 ⟨le_rfl, le_rfl⟩
  have hq : 0 < Nat.card k := Nat.card_pos
  have hq2 : 1 ≤ Nat.card k ^ 2 := Nat.one_le_pow _ _ hq
  have hcop : Nat.Coprime (Nat.card k) (Nat.card k ^ 2 - 1) := by
    have h : Nat.Coprime (Nat.card k ^ 2 - 1) (Nat.card k ^ 2 - 1 + 1) :=
      Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
    rw [Nat.sub_add_cancel hq2] at h
    exact (h.coprime_dvd_right (dvd_pow_self _ two_ne_zero)).symm
  have hbound : ∀ T : Subgroup SL(2, k), Nat.card T ∣ Nat.card k ^ 2 →
      Nat.card T ≤ Nat.card k := by
    intro T hT
    have h1 : Nat.card T ∣ Nat.card k * (Nat.card k ^ 2 - 1) :=
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two k ▸ T.card_subgroup_dvd_card
    have hg : Nat.gcd (Nat.card k * Nat.card k) (Nat.card k * (Nat.card k ^ 2 - 1)) =
        Nat.card k := by
      rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop, mul_one]
    have := Nat.dvd_gcd (sq (Nat.card k) ▸ hT) h1
    rw [hg] at this
    exact Nat.le_of_dvd hq this
  have h1 := hbound S₁ (hS ▸ S.card_map_dvd (MonoidHom.fst _ _))
  have h2 := hbound S₂ (hS ▸ S.card_map_dvd (MonoidHom.snd _ _))
  have h3 : Nat.card S ≤ Nat.card (S₁.prod S₂) := Subgroup.card_le_of_le hle
  rw [card_prod_subgroup, hS] at h3
  have e1 : Nat.card S₁ = Nat.card k := le_antisymm h1 (by nlinarith)
  have e2 : Nat.card S₂ = Nat.card k := le_antisymm h2 (by nlinarith)
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, e1, e2⟩
  rw [card_prod_subgroup, e1, e2, hS, sq]

theorem torusSL_prod_le_normalizer [Finite k] {S : Subgroup (SL(2, k) × SL(2, k))}
    (hS : Nat.card S = Nat.card k ^ 2) {μ : kˣ} (hμ : μ ≠ 1)
    (hSμ : (diagSL μ, diagSL μ) ∈ normalizer (S : Set (SL(2, k) × SL(2, k)))) :
    (torusSL k).prod (torusSL k) ≤ normalizer (S : Set (SL(2, k) × SL(2, k))) ∧
      (torusSL k).prod (torusSL k) ⊓ centralizer (S : Set (SL(2, k) × SL(2, k))) = ⊥ := by
  obtain ⟨hSeq, h1, h2⟩ := eq_prod_map_fst_map_snd hS
  have hn1 := fst_mem_normalizer_map_fst hSμ
  have hn2 := snd_mem_normalizer_map_snd hSμ
  rw [hSeq]
  exact ⟨prod_le_normalizer_prod (torusSL_le_normalizer h1 hμ hn1)
      (torusSL_le_normalizer h2 hμ hn2),
    prod_inf_centralizer_prod_eq_bot (torusSL_inf_centralizer h1 hμ hn1)
      (torusSL_inf_centralizer h2 hμ hn2)⟩

variable {X : Type*} [Group X]

theorem exists_mulEquiv_map_centralizer_zpowers_prod [Finite k]
    (ψ : X ≃* SL(2, k) × SL(2, k)) {d : X} {g : SL(2, k)} (hψd : ψ d = (g, g)) (hg1 : g ≠ 1)
    (hg : g ^ (Nat.card k - 1) = 1) :
    ∃ (ψ' : X ≃* SL(2, k) × SL(2, k)) (μ : kˣ), μ ≠ 1 ∧ ψ' d = (diagSL μ, diagSL μ) ∧
      (centralizer (zpowers d : Set X)).map ψ'.toMonoidHom =
        (torusSL k).prod (torusSL k) := by
  obtain ⟨x, μ, hμ, hx⟩ := exists_conj_eq_diagSL hg1 hg
  have hψ'd : (ψ.trans (MulAut.conj (x, x))) d = (diagSL μ, diagSL μ) := by
    simp [MulAut.conj_apply, hψd, hx]
  refine ⟨ψ.trans (MulAut.conj (x, x)), μ, hμ, hψ'd, ?_⟩
  rw [centralizer_zpowers, map_equiv_centralizer, Set.image_singleton, hψ'd,
    centralizer_singleton_prod, centralizer_diagSL hμ]

theorem card_centralizer_zpowers_prod [Finite k] (ψ : X ≃* SL(2, k) × SL(2, k)) {d : X}
    {g : SL(2, k)} (hψd : ψ d = (g, g)) (hg1 : g ≠ 1) (hg : g ^ (Nat.card k - 1) = 1) :
    Nat.card (centralizer (zpowers d : Set X)) = (Nat.card k - 1) ^ 2 := by
  obtain ⟨ψ', -, -, -, hC⟩ := exists_mulEquiv_map_centralizer_zpowers_prod ψ hψd hg1 hg
  rw [← Subgroup.card_map_of_injective (f := ψ'.toMonoidHom) ψ'.injective, hC,
    card_prod_subgroup, card_torusSL, sq]

theorem centralizer_zpowers_le_normalizer_and_inf_prod [Finite k]
    (ψ : X ≃* SL(2, k) × SL(2, k)) {d : X} {g : SL(2, k)} (hψd : ψ d = (g, g)) (hg1 : g ≠ 1)
    (hg : g ^ (Nat.card k - 1) = 1) {S : Subgroup X} (hS : Nat.card S = Nat.card k ^ 2)
    (hdS : d ∈ normalizer (S : Set X)) :
    centralizer (zpowers d : Set X) ≤ normalizer (S : Set X) ∧
      centralizer (zpowers d : Set X) ⊓ centralizer (S : Set X) = ⊥ := by
  obtain ⟨ψ', μ, hμ, hψ'd, hC⟩ := exists_mulEquiv_map_centralizer_zpowers_prod ψ hψd hg1 hg
  have hS' : Nat.card (S.map ψ'.toMonoidHom) = Nat.card k ^ 2 := by
    rw [Subgroup.card_map_of_injective ψ'.injective, hS]
  have hdS' : (diagSL μ, diagSL μ) ∈ normalizer ((S.map ψ'.toMonoidHom :
      Subgroup (SL(2, k) × SL(2, k))) : Set (SL(2, k) × SL(2, k))) := by
    rw [← map_equiv_normalizer_eq, ← hψ'd]
    exact ⟨d, hdS, rfl⟩
  obtain ⟨hN, hI⟩ := torusSL_prod_le_normalizer hS' hμ hdS'
  rw [← hC, ← map_equiv_normalizer_eq] at hN
  rw [← hC, coe_map, MulEquiv.coe_toMonoidHom, ← map_equiv_centralizer,
    ← Subgroup.map_inf_eq _ _ _ ψ'.injective] at hI
  exact ⟨(Subgroup.map_le_map_iff_of_injective ψ'.injective).1 hN,
    (Subgroup.map_eq_bot_iff_of_injective _ ψ'.injective).1 hI⟩

theorem card_sylow_two_eq_prod [Finite k] (ψ : X ≃* SL(2, k) × SL(2, k)) (P : Sylow 2 X) :
    Nat.card P = Nat.card k ^ 2 := by
  have : Fintype k := Fintype.ofFinite k
  have : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  rw [← Nat.card_eq_fintype_card] at hn
  have hq : 1 ≤ Nat.card k ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hodd : ¬ 2 ∣ (Nat.card k ^ 2 - 1) ^ 2 := by
    intro h2
    have h2' := Nat.prime_two.dvd_of_dvd_pow h2
    have h4 : 2 ∣ Nat.card k ^ 2 := by
      rw [hn, ← pow_mul]
      exact dvd_pow_self 2 (by positivity)
    omega
  have hX : Nat.card X = 2 ^ (2 * (n : ℕ)) * (Nat.card k ^ 2 - 1) ^ 2 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_prod,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    generalize Nat.card k ^ 2 - 1 = m
    rw [hn]
    ring
  have hne : (Nat.card k ^ 2 - 1) ^ 2 ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  rw [P.card_eq_multiplicity, hX, Nat.factorization_mul (by positivity) hne,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hn, ← pow_mul, mul_comm]

end CFSG.LocalAnalysis.EvenBN.Common
