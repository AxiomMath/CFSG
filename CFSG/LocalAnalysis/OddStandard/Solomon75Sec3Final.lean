module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Local
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Lift
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusNPlus
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.Goldschmidt

open scoped commutatorElement

section Perms

def permA : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def permB : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 6 * swap 5 7

theorem permA_sq : permA * permA = 1 := by decide

theorem permB_sq : permB * permB = 1 := by decide

theorem permA_card : permA.support.card = 8 := by decide

theorem permB_card : permB.support.card = 8 := by decide

theorem permAB_card : (permA * permB).support.card = 4 := by decide

theorem permAB_sq : (permA * permB) * (permA * permB) = 1 := by decide

theorem permA_sign : Perm.sign permA = 1 := by
  simp [permA, Perm.sign_mul]

theorem permB_sign : Perm.sign permB = 1 := by
  simp [permB, Perm.sign_mul]

noncomputable def liftPerm {n : ℕ} (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Perm.viaEmbeddingHom (Fin.castLEEmb hn)

theorem card_support_liftPerm {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    (liftPerm hn σ).support.card = σ.support.card := by
  classical
  have h := Equiv.Perm.card_support_extend_domain
    (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2) (g := σ)
  rw [← h]
  simp only [liftPerm, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  congr

theorem sign_liftPerm {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    Perm.sign (liftPerm hn σ) = Perm.sign σ := by
  classical
  have h := Equiv.Perm.sign_extendDomain σ
    (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2)
  rw [← h]
  simp only [liftPerm, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  congr

end Perms

section Main

theorem ahatNoncommutingInvolutions : AhatNoncommutingInvolutions := by
  intro Q _ _ n hn hQ
  have hcard : Nat.card (center Q) = 2 := hQ.2.1
  obtain ⟨e⟩ := hQ.2.2
  let π : Q →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center Q := by
    ext x
    simp [π]
  let a : alternatingGroup (Fin n) :=
    ⟨liftPerm hn permA, by rw [mem_alternatingGroup, sign_liftPerm, permA_sign]⟩
  let b : alternatingGroup (Fin n) :=
    ⟨liftPerm hn permB, by rw [mem_alternatingGroup, sign_liftPerm, permB_sign]⟩
  obtain ⟨u, hu⟩ := hπs a
  obtain ⟨v, hv⟩ := hπs b
  have hu' : (π u : Perm (Fin n)) = liftPerm hn permA := by rw [hu]
  have hv' : (π v : Perm (Fin n)) = liftPerm hn permB := by rw [hv]
  have huu : u * u = 1 := by
    have h1 : (π u : Perm (Fin n)) * (π u : Perm (Fin n)) = 1 := by
      rw [hu', ← map_mul, permA_sq, map_one]
    rw [sq_eq_one_iff_dvd_of_doubleCover hn hQ π hπs hπk h1, hu', card_support_liftPerm,
      permA_card]
  have hvv : v * v = 1 := by
    have h1 : (π v : Perm (Fin n)) * (π v : Perm (Fin n)) = 1 := by
      rw [hv', ← map_mul, permB_sq, map_one]
    rw [sq_eq_one_iff_dvd_of_doubleCover hn hQ π hπs hπk h1, hv', card_support_liftPerm,
      permB_card]
  have hπuv : (π (u * v) : Perm (Fin n)) = liftPerm hn (permA * permB) := by
    rw [map_mul, Subgroup.coe_mul, hu', hv', map_mul]
  have hπuv2 : (π (u * v) : Perm (Fin n)) * (π (u * v) : Perm (Fin n)) = 1 := by
    rw [hπuv, ← map_mul, permAB_sq, map_one]
  have huv_sq : ¬ (u * v) * (u * v) = 1 := by
    rw [sq_eq_one_iff_dvd_of_doubleCover hn hQ π hπs hπk hπuv2, hπuv, card_support_liftPerm,
      permAB_card]
    decide
  refine ⟨u, v, huu, hvv, ?_, ?_⟩
  · intro h
    apply huv_sq
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← h]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hvv, one_mul]
  · have h2 : (u * v) * (u * v) ∈ center Q := by
      rw [← hπk, MonoidHom.mem_ker]
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hπuv2]
      rfl
    have h3 : orderOf (⟨(u * v) * (u * v), h2⟩ : center Q) ∣ 2 :=
      hcard ▸ orderOf_dvd_natCard _
    have h4 : (⟨(u * v) * (u * v), h2⟩ : center Q) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
    have h5 := congrArg (fun w : center Q => (w : Q)) h4
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h5
    calc (u * v) ^ 4 = ((u * v) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = ((u * v) * (u * v)) ^ 2 := by rw [sq (u * v)]
      _ = 1 := h5

end Main

section Final

variable {X : Type} [Group X] [Finite X]

theorem SolCEx.lemma36_set (h : SolCEx X) (hGold : CoreStatement) {n : ℕ} {z : X}
    {Z : Subgroup X} (hp : IsSec5Pair X n z Z) (S : Sylow 2 X) (hZS : Z ≤ (S : Subgroup X)) :
    {x : X | x ∈ (S : Subgroup X) ∧ ∃ g : X, g⁻¹ * x * g ∈ Z} ≠ (Z : Set X) := by
  have := h.simple
  exact _root_.CFSG.OddStandard.Solomon75.lemma36_set hGold ahatNoncommutingInvolutions
    h.nonabelian hp S hZS

@[expose] def Lemma34K (X : Type) [Group X] [Finite X] (n : ℕ) (Z : Subgroup X) : Prop :=
  ∀ s : X, s ∈ normalizer (Z : Set X) → orderOf s = 2 →
    K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) ≠ ⊥ →
    LPlusIn (centralizer ({s} : Set X)) =
      pPrimeCoreOf 2 (LPlusIn (centralizer ({s} : Set X))) ⊔
        (normalizer (Z : Set X) ⊓ LPlusIn (centralizer ({s} : Set X)))

structure Lemma52 (X : Type) [Group X] [Finite X] (n : ℕ) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))) : Prop where
  a : Lemma33b X n Z
  b : Lemma33a X n Z
  c : Lemma34K X n Z
  d : IsSylowTwoIn (⊤ : Subgroup X)
    ((S : Subgroup ↥(normalizer (Z : Set X))).map (normalizer (Z : Set X)).subtype)
  e : {x : X | x ∈ (S : Subgroup ↥(normalizer (Z : Set X))).map
      (normalizer (Z : Set X)).subtype ∧ ∃ g : X, g⁻¹ * x * g ∈ Z} ≠ (Z : Set X)

@[expose] def Lemma51c (X : Type) [Group X] (n : ℕ) : Prop :=
  ∀ s t : X, orderOf s = 2 → orderOf t = 2 → s * t = t * s → s ≠ t →
    K0 X n (centralizer ({s} : Set X) ⊓ centralizer ({t} : Set X)) ≤
      K0 X n (centralizer ({s} : Set X)) ⊓ K0 X n (centralizer ({t} : Set X))

end Final

end CFSG.OddStandard.Solomon75
