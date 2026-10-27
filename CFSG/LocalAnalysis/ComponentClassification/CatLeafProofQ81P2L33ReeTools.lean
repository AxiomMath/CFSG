module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.Ree

open CFSG Subgroup
open scoped commutatorElement

theorem fixedPoints_conj {Y : Type} [Group Y] (x : Y) :
    fixedPoints (MulAut.conj x) = centralizer ({x} : Set Y) := by
  ext y
  rw [mem_fixedPoints, MulAut.conj_apply, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem mulAut_congr_conj {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') (q : Q) :
    MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) := by
  ext y
  change e (q * e.symm y * q⁻¹) = e q * y * (e q)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem commutator_eq_top_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hnab : ∃ x y : S, x * y ≠ y * x) : _root_.commutator S = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (_root_.commutator S) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have h1 : ⁅x, y⁆ ∈ _root_.commutator S := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · exact h

theorem commutator_eq_top_of_mulEquiv {X S : Type*} [Group X] [Group S] (e : X ≃* S)
    (hS : _root_.commutator S = ⊤) : _root_.commutator X = ⊤ := by
  have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) hS
  rw [_root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
  rw [_root_.commutator_def]
  exact h1

theorem not_isPGroup_of_perfect_equiv {G S : Type*} [Group G] [Finite G] [Group S]
    {F X : Subgroup G} (hXF : X ≤ F) (e : ↥X ≃* S) (hS : _root_.commutator S = ⊤)
    (heven : 2 ∣ Nat.card S) : ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  apply not_isPGroup_of_perfect hXF _ (by rwa [Nat.card_congr e.toEquiv])
  have h1 := congrArg (Subgroup.map X.subtype) (commutator_eq_top_of_mulEquiv e hS)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  exact h1

theorem not_isPGroup_centralizer {M S : Type*} [Group M] [Group S] {Γ X : Subgroup M}
    [Finite Γ] (x : Γ) (hX : X ≤ Γ ⊓ centralizer ({(x : M)} : Set M)) (e : ↥X ≃* S)
    (hS : _root_.commutator S = ⊤) (heven : 2 ∣ Nat.card S) :
    ¬ IsPGroup 2 (↥(centralizer ({x} : Set Γ)) ⧸ pPrimeCore 2 ↥(centralizer ({x} : Set Γ))) := by
  have hXΓ : X ≤ Γ := hX.trans inf_le_left
  refine not_isPGroup_of_perfect_equiv (X := X.subgroupOf Γ) ?_
    ((subgroupOfEquivOfLe hXΓ).trans e) hS heven
  intro g hg
  have hgC := (mem_inf.mp (hX (mem_subgroupOf.mp hg))).2
  rw [mem_centralizer_singleton_iff] at hgC ⊢
  exact Subtype.ext hgC

theorem isPGroup_centralizer_conj {Y : Type} [Group Y] [Finite Y] (x g : Y)
    (h : IsPGroup 2 (↥(centralizer ({x} : Set Y)) ⧸ pPrimeCore 2 ↥(centralizer ({x} : Set Y)))) :
    IsPGroup 2 (↥(centralizer ({g * x * g⁻¹} : Set Y)) ⧸
      pPrimeCore 2 ↥(centralizer ({g * x * g⁻¹} : Set Y))) := by
  rw [← fixedPoints_conj] at h ⊢
  have h1 := isPGroup_fixedPoints_congr (MulAut.conj g) (MulAut.conj x) h
  rwa [mulAut_congr_conj, MulAut.conj_apply] at h1

theorem not_isPGroup_of_card {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    (hO : pPrimeCore 2 ↥F = ⊥) (hcard : ∀ k : ℕ, Nat.card F ≠ 2 ^ k) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  obtain ⟨k, hk⟩ := (isPGroup_of_pPrimeCore_eq_bot hO hP).exists_card_eq
  exact hcard k hk

theorem not_isPGroup_of_mulEquiv {Y P : Type} [Group Y] [Group P] [Finite Y] [Finite P]
    (e : Y ≃* P)
    (hP : ∀ α : MulAut P, orderOf α = 2 →
      ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)))
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) :=
  fun h => hP _ ((orderOf_congr e a).trans ha) (isPGroup_fixedPoints_congr e a h)

end CFSG.ComponentClassification.HarrisLit.L33.Ree
