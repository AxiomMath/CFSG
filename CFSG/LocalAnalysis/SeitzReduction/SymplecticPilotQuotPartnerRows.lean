module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotPartner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

section Embedding

variable {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type*} [Group X]

theorem spPartnerShapeOn_of_embedding (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 1 ≤ m)
    {θ α η : MulAut X} (ψ : StatedSp (m + 1) K →* X) (hψ : Function.Injective ψ)
    (p : Fin (m + 1)) (hα : α = MulAut.conj (ψ (siegDiag K p 1)) * η)
    (hηx : η (ψ (siegDiag K p 1)) = ψ (siegDiag K p 1))
    (hβ : ∃ β : MulAut X, β * θ = η * β)
    (hfix : fixedSubgroup α =
      (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).map ψ) :
    SpPartnerShapeOn (m + 1) K θ α := by
  set z := siegDiag K p 1 with hz
  set C := centralizer ({z} : Set (StatedSp (m + 1) K)) with hC
  have hCle : C.map ψ ≤ centralizer ({ψ z} : Set X) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
  refine ⟨ψ z, η, p, hα, hηx, by rw [← map_mul, hz, siegDiag_one_mul_self, map_one], hβ,
    hfix ▸ hCle, ?_, ?_, ?_⟩
  · rw [hfix, ← Subgroup.map_commutator, hC,
      commutator_centralizer_siegDiag (K := K) (m := m) hK hm]
  · rw [hfix, Subgroup.card_map_of_injective hψ]
  · intro T hT hTodd
    rw [hfix] at hT
    set T' : Subgroup (StatedSp (m + 1) K) := T.comap ψ with hT'
    have hT'map : T'.map ψ = T := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
      obtain ⟨c, -, rfl⟩ := hT hy
      exact ⟨c, hy, rfl⟩
    have hT'C : T' ≤ C := by
      intro c hc
      obtain ⟨c', hc', hcc'⟩ := hT hc
      rw [← hψ hcc']
      exact hc'
    have hT'odd : Odd (Nat.card T') := by
      rw [← Subgroup.card_map_of_injective hψ, hT'map]
      exact hTodd
    obtain ⟨P, hPT, hPperf, -, hPz⟩ := exists_perfect_le_centralizer_of_odd hK p hT'C hT'odd
    refine ⟨P.map ψ, ?_, by rw [← Subgroup.map_commutator, hPperf], fun h => hPz ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro τ hτ
      obtain ⟨τ', hτ', rfl⟩ : ∃ τ' ∈ T', ψ τ' = τ := by
        rw [← hT'map] at hτ
        exact hτ
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hPT hy) τ' hτ']
    · intro y hy
      have h1 := mem_centralizer_singleton_iff.1 (h ⟨y, hy, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact mem_centralizer_singleton_iff.2 (hψ h1)

end Embedding

section Inputs

@[expose] def SpGraphCosetInnQuotInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobalQuot e t f κ →
      ∀ htN : t ∈ normalizer (spGlobal e : Set G),
        CosetInnConjInput (centerQuotAction (spGlobal e) ⟨t, htN⟩)

@[expose] def SpGraphCosetCardQuotInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobalQuot e t f κ →
      ∀ htN : t ∈ normalizer (spGlobal e : Set G),
        SpCosetCardOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩)

@[expose] def SpLongPieceQuotInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n), Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobalQuot e t f κ →
        pieceCore e ({⟨n - 1, by omega⟩} : Finset (Fin n)) ≤ centralizer ({t} : Set G)

@[expose] def SpLinearSecondClassShapeQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k .linearEven) → SpOmegaRowGlobalQuot e t f .linearEven →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G))
        (α : MulAut (spGlobal e ⧸ center (spGlobal e))) (F : Type) [Field F] [Finite F],
        Nat.card F = 2 ^ f →
        ∀ (ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F)
          (H : GL (Fin (2 * n)) F),
          MulAut.congr ε α = LinearFlag.conjAut (2 * n) F H * LinearFlag.dualAut (2 * n) F *
              (LinearFlag.conjAut (2 * n) F H)⁻¹ →
            SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) α

@[expose] def SpUnitarySecondClassShapeQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k .unitaryEven) → SpOmegaRowGlobalQuot e t f .unitaryEven →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G))
        (α : MulAut (spGlobal e ⧸ center (spGlobal e)))
        (K' : Type) [Field K'] (h : UnitaryFieldData 2 f K')
        (ψ : spGlobal e ⧸ center (spGlobal e) ≃* primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
        (θ : MulAut (primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))),
          MulAut.congr ψ α =
              θ * primeFormFieldHom h isPrimeFormGram_one (UnitaryPilot.barRingEquiv h) * θ⁻¹ →
            SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) α

end Inputs

section Rows

theorem not_spPartnerShapeQuot_of_rowInputs {κ : Sp2mKind} (hInn : SpGraphCosetInnQuotInput κ)
    (hCard : SpGraphCosetCardQuotInput κ) (hTor : SpLongPieceQuotInput κ) (G : Type) [Group G]
    [Finite G] (L : Subgroup G) (hset : SeitzSetting G L) (n f : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) (t : G) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin n, RootKindSp e t f k κ) (hglob : SpOmegaRowGlobalQuot e t f κ)
    (htN : t ∈ normalizer (spGlobal e : Set G)) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ¬ SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩)
      (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) := by
  intro hsh
  have hTor' := hTor G L hset n f K hn hKc hf e t ht hKt hroot hglob
  have hInn' := hInn G L hset n f K hn hKc hf e t ht hKt hroot hglob htN
  have hCard' := hCard G L hset n f K hn hKc hf e t ht hKt hroot hglob htN
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  have : Group.IsPerfect (spGlobal e) := hglob.1.1.1
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have htZ : t ∉ centralizer (spGlobal e : Set G) := by
    intro htZ
    apply (hglob.2 htN).1
    refine ⟨1, ?_⟩
    rw [map_one]
    exact (EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer (MulEquiv.refl _) htN htZ).symm
  have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hlast : (⟨m + 3 - 1, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) :=
    Fin.ext (by simp)
  rw [hlast] at hTor'
  exact false_of_spPartnerShapeQuot hset hKc hf e ht hKt hLS hZ htN hodd
    (fun h hh γ hγ => mem_normalizer_of_conj_centerQuotAction hset (by omega) hKc hf e ht hKt
      hglob.1.1.1 hZ htN hh γ hγ) hInn' hCard' hTor' hg hsh

theorem spLinearEvenSecondClassQuot_of_partner (hsh : SpLinearSecondClassShapeQuotInput)
    (hInn : SpGraphCosetInnQuotInput .linearEven) (hCard : SpGraphCosetCardQuotInput .linearEven)
    (hTor : SpLongPieceQuotInput .linearEven) : SpLinearEvenSecondClassQuotInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob g hg F _ _ hF ε H he
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  exact not_spPartnerShapeQuot_of_rowInputs hInn hCard hTor G L hset n f K hn hKc hf e t ht hKt
    hroot hglob htN g hg (hsh G L hset n f K hn hKc hf e t ht hKt hroot hglob htN _ F hF ε H he)

theorem spUnitaryEvenSecondClassQuot_of_partner (hsh : SpUnitarySecondClassShapeQuotInput)
    (hInn : SpGraphCosetInnQuotInput .unitaryEven) (hCard : SpGraphCosetCardQuotInput .unitaryEven)
    (hTor : SpLongPieceQuotInput .unitaryEven) : SpUnitaryEvenSecondClassQuotInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob g hg K' _ h ψ θ he
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  exact not_spPartnerShapeQuot_of_rowInputs hInn hCard hTor G L hset n f K hn hKc hf e t ht hKt
    hroot hglob htN g hg (hsh G L hset n f K hn hKc hf e t ht hKt hroot hglob htN _ K' h ψ θ he)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
