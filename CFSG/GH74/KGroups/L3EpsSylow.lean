module

public import CFSG.GH74.KGroups.L3EpsLin
public import CFSG.GH74.KGroups.L3EpsUni
public import CFSG.GH74.KGroups.L3EpsCenter
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem isMaxPGroup_map (e : X ≃* Y) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    IsPGroup 2 (S.map e.toMonoidHom) ∧
      ∀ T : Subgroup Y, IsPGroup 2 T → S.map e.toMonoidHom ≤ T → T ≤ S.map e.toMonoidHom := by
  refine ⟨hS.map e.toMonoidHom, ?_⟩
  intro T hT hST y hy
  have hT' : IsPGroup 2 (T.comap e.toMonoidHom) := hT.comap_of_injective e.toMonoidHom e.injective
  have hST' : S ≤ T.comap e.toMonoidHom := fun s hs => hST ⟨s, hs, rfl⟩
  have h1 := hmax _ hT' hST'
  have hy' : e.symm y ∈ T.comap e.toMonoidHom := by
    show e.toMonoidHom (e.symm y) ∈ T
    simpa using hy
  exact ⟨e.symm y, h1 hy', by simp⟩

theorem key_of_mulEquiv (e : X ≃* Y)
    (hY : ∀ S' : Subgroup Y, IsPGroup 2 S' →
      (∀ T : Subgroup Y, IsPGroup 2 T → S' ≤ T → T ≤ S') →
      ∀ (φ' : MulAut Y) (k : ℕ), φ' ^ 2 ^ k = 1 → (∀ s ∈ S', φ' s = s) →
        ∃ z ∈ S', (∀ s ∈ S', s * z = z * s) ∧ φ' = MulAut.conj z)
    {S : Subgroup X} (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut X} {k : ℕ} (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ z ∈ S, (∀ s ∈ S, s * z = z * s) ∧ φ = MulAut.conj z := by
  obtain ⟨hS', hmax'⟩ := isMaxPGroup_map e hS hmax
  have hφ'k : (MulAut.congr e φ) ^ 2 ^ k = 1 := by rw [← map_pow, hφk, map_one]
  have hφ'S : ∀ s ∈ S.map e.toMonoidHom, MulAut.congr e φ s = s := by
    rintro _ ⟨s, hs, rfl⟩
    rw [MulAut.congr_apply]
    simp [hφS s hs]
  obtain ⟨z', hz'S, hz'c, hz'⟩ := hY _ hS' hmax' _ k hφ'k hφ'S
  obtain ⟨z, hz, rfl⟩ := hz'S
  refine ⟨z, hz, ?_, ?_⟩
  · intro s hs
    have := hz'c (e s) ⟨s, hs, rfl⟩
    exact e.injective (by simpa using this)
  · apply (MulAut.congr e).injective
    rw [hz']
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem center_of_mulEquiv (e : X ≃* Y) {N : ℕ}
    (hY : ∀ S' : Subgroup Y, IsPGroup 2 S' →
      (∀ T : Subgroup Y, IsPGroup 2 T → S' ≤ T → T ≤ S') →
      IsCyclic ↥(S' ⊓ Subgroup.centralizer (S' : Set Y)) ∧
        ∀ z ∈ S' ⊓ Subgroup.centralizer (S' : Set Y), z ^ N = 1)
    {S : Subgroup X} (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    IsCyclic ↥(S ⊓ Subgroup.centralizer (S : Set X)) ∧
      ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), z ^ N = 1 := by
  obtain ⟨hS', hmax'⟩ := isMaxPGroup_map e hS hmax
  obtain ⟨hcyc, hexp⟩ := hY _ hS' hmax'
  have hmem : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X),
      e z ∈ S.map e.toMonoidHom ⊓ Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨⟨z, hz.1, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 hz.2) s hs
    show e s * e z = e z * e s
    rw [← map_mul, ← map_mul, this]
  let ψ : ↥(S ⊓ Subgroup.centralizer (S : Set X)) →*
      ↥(S.map e.toMonoidHom ⊓ Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y)) :=
    (e.toMonoidHom.comp (S ⊓ Subgroup.centralizer (S : Set X)).subtype).codRestrict _
      (fun z => hmem z z.2)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have : e (a : X) = e (b : X) := congrArg Subtype.val hab
    exact Subtype.ext (e.injective this)
  refine ⟨isCyclic_of_injective ψ hψ, fun z hz => ?_⟩
  have := hexp _ (hmem z hz)
  exact e.injective (by rw [map_pow, this, map_one])

end Transport

section Models

variable {X : Type} [Group X]

theorem ringChar_ne_two_of_card {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := h2 ▸ ringChar.charP F
  have h2dvd : (2 : ℕ) ∣ Nat.card F := by
    have := FiniteField.card F 2
    obtain ⟨n, -, hn⟩ := this
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  rw [hF] at h2dvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2dvd)).symm

theorem exists_projectiveSL_equiv {p f : ℕ} (hX : StatedClassicalModel X .PSL 3 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (X ≃* projectiveSL 3 F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hX
  exact ⟨F, inferInstance, inferInstance, hF, ⟨e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).symm)⟩⟩

theorem exists_primeFormP_equiv {p f : ℕ} (hX : StatedClassicalModel X .PSU 3 p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K),
      Nonempty (X ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eT⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := 3) (K := K))
  exact ⟨K, inferInstance, hU, ⟨(e.trans (unitaryPSUEquiv hU (by norm_num)).symm).trans eT.symm⟩⟩

end Models

section Main

variable {X : Type} [Group X]

theorem l3eps_sylow_aut {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hX : StatedClassicalModel X t 3 p f) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) {φ : MulAut X} {k : ℕ}
    (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ z ∈ S, (∀ s ∈ S, s * z = z * s) ∧ φ = MulAut.conj z := by
  rcases ht with rfl | rfl
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
    have hp : p.Prime := hX.1.1
    exact key_of_mulEquiv e (fun S' hS' hmax' φ' k hk hfix =>
      lin_key (ringChar_ne_two_of_card hp hp2 hF) hS' hmax' hk hfix) hS hmax hφk hφS
  · obtain ⟨K, _, hU, ⟨e⟩⟩ := exists_primeFormP_equiv hX
    exact key_of_mulEquiv e (fun S' hS' hmax' φ' k hk hfix =>
      uni_key hU hp2 h5 hS' hmax' hk hfix) hS hmax hφk hφS

theorem l3eps_center_sylow {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X t 3 p f) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    IsCyclic ↥(S ⊓ Subgroup.centralizer (S : Set X)) ∧
      (t = .PSL → ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), z ^ (p ^ f - 1) = 1) ∧
      (t = .PSU → ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), z ^ (p ^ f + 1) = 1) := by
  rcases ht with rfl | rfl
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
    have hp : p.Prime := hX.1.1
    have hN := center_of_mulEquiv e (N := p ^ f - 1) (fun S' hS' hmax' => by
      obtain ⟨h1, h2⟩ := lin_center (ringChar_ne_two_of_card hp hp2 hF) hS' hmax'
      exact ⟨h1, fun z hz => by rw [← hF]; exact h2 z hz⟩) hS hmax
    exact ⟨hN.1, fun _ => hN.2, fun h => absurd h (by decide)⟩
  · obtain ⟨K, _, hU, ⟨e⟩⟩ := exists_primeFormP_equiv hX
    have hN := center_of_mulEquiv e (N := p ^ f + 1) (fun S' hS' hmax' =>
      uni_center hU hp2 hS' hmax') hS hmax
    exact ⟨hN.1, fun h => absurd h (by decide), fun _ => hN.2⟩

end Main

end CFSG.GH74.KGroups.L3Eps
