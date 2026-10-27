module

public import CFSG.GroupTheory.SteinbergCBFTUpperSeries
public import CFSG.GroupTheory.SteinbergCBFTHall
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman


section Structure

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def coreP (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  coreAbove {q : Nat.Primes | q.val = p} ⊥

@[expose] noncomputable def corePP' (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  coreAbove {q : Nat.Primes | q.val ≠ p} (coreP p G)

@[expose] noncomputable def corePP'P (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  coreAbove {q : Nat.Primes | q.val = p} (corePP' p G)

omit [Finite G] hp in
theorem coreP_le_corePP' : coreP p G ≤ corePP' p G := by
  have : (coreP p G).Normal := coreAbove_normal _ _
  exact le_coreAbove _ _

omit [Finite G] hp in
theorem corePP'_le_corePP'P : corePP' p G ≤ corePP'P p G := by
  have : (corePP' p G).Normal := coreAbove_normal _ _
  exact le_coreAbove _ _

theorem isPGroup_coreP : IsPGroup p (coreP p G) := by
  have h := isPrimeSetNumber_relIndex_coreAbove {q : Nat.Primes | q.val = p} (⊥ : Subgroup G)
  rw [relIndex_bot_left] at h
  rw [IsPGroup.iff_card]
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd =>
    h ⟨d, hd⟩ hdvd⟩

theorem corePP'P_eq_sup (P : Sylow p G) :
    corePP'P p G = corePP' p G ⊔ ((P : Subgroup G) ⊓ corePP'P p G) := by
  set T₂ := corePP' p G
  set T₃ := corePP'P p G
  have hT₂n : T₂.Normal := coreAbove_normal _ _
  have hT₃n : T₃.Normal := coreAbove_normal _ _
  have hle : T₂ ⊔ ((P : Subgroup G) ⊓ T₃) ≤ T₃ := sup_le corePP'_le_corePP'P inf_le_right
  refine le_antisymm ?_ hle
  have h1 : (T₂ ⊔ ((P : Subgroup G) ⊓ T₃)).relIndex T₃ ∣ T₂.relIndex T₃ :=
    relIndex_dvd_of_le_left T₃ le_sup_left
  have h2 : (T₂ ⊔ ((P : Subgroup G) ⊓ T₃)).relIndex T₃ ∣ ((P : Subgroup G) ⊓ T₃).relIndex T₃ :=
    relIndex_dvd_of_le_left T₃ le_sup_right
  have hp1 : IsPrimeSetNumber {q : Nat.Primes | q.val = p}
      ((T₂ ⊔ ((P : Subgroup G) ⊓ T₃)).relIndex T₃) :=
    (isPrimeSetNumber_relIndex_coreAbove _ T₂).dvd h1
  have hp2 : ¬ p ∣ (T₂ ⊔ ((P : Subgroup G) ⊓ T₃)).relIndex T₃ := by
    intro hdvd
    have h3 : ((P : Subgroup G) ⊓ T₃).relIndex T₃ = (P : Subgroup G).relIndex T₃ :=
      inf_relIndex_right _ _
    have h4 := CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer
      (fun x _ => (normalizer_eq_top (H := T₃)).symm ▸ mem_top x :
        (P : Subgroup G) ≤ normalizer (T₃ : Set G))
    exact P.not_dvd_index ((hdvd.trans h2).trans (h3 ▸ h4 ▸ relIndex_dvd_index_of_le le_sup_left))
  have := eq_one_of_isPrimeSetNumber_of_coprime hp1 hp2
  exact relIndex_eq_one.1 this

theorem corePP'_sup_normalizer (P : Sylow p G) :
    corePP' p G ⊔ normalizer (((P : Subgroup G) ⊓ corePP'P p G : Subgroup G) : Set G) = ⊤ := by
  set T₃ := corePP'P p G
  have hT₃n : T₃.Normal := coreAbove_normal _ _
  have hfr := Sylow.normalizer_sup_eq_top (CFSG.QuasiDihedralFusion.sylowInfNormal P T₃)
  rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, subgroupOf_map_subtype] at hfr
  rw [eq_top_iff, ← hfr, sup_comm]
  calc T₃ ⊔ normalizer (((P : Subgroup G) ⊓ T₃ : Subgroup G) : Set G)
      = corePP' p G ⊔ ((P : Subgroup G) ⊓ T₃) ⊔
          normalizer (((P : Subgroup G) ⊓ T₃ : Subgroup G) : Set G) := by
        rw [← corePP'P_eq_sup P]
    _ ≤ _ := sup_le (sup_le le_sup_left (le_normalizer.trans le_sup_right)) le_sup_right

theorem corePP'_eq_top_of_normal (hG : IsPiSeparable {q : Nat.Primes | q.val = p} G)
    (P : Sylow p G)
    (hN : normalizer (((P : Subgroup G) ⊓ corePP'P p G : Subgroup G) : Set G) = ⊤) :
    corePP' p G = ⊤ := by
  have hP₁n : ((P : Subgroup G) ⊓ corePP'P p G).Normal := normalizer_eq_top_iff.1 hN
  have hcPn : (coreP p G).Normal := coreAbove_normal _ _
  have hT₂n : (corePP' p G).Normal := coreAbove_normal _ _
  have hP₁ : (P : Subgroup G) ⊓ corePP'P p G ≤ coreP p G := by
    refine le_coreAbove_of (N' := ⊥) bot_le ?_
    rw [relIndex_bot_left]
    exact isPrimeSetNumber_card_of_isPGroup (P.isPGroup'.to_le inf_le_left)
  have h1 : coreAbove {q : Nat.Primes | q.val = p} (corePP' p G) = corePP' p G := by
    change corePP'P p G = corePP' p G
    rw [corePP'P_eq_sup P]
    exact sup_eq_left.2 (hP₁.trans coreP_le_corePP')
  have h2 : coreAbove {q : Nat.Primes | q.val ≠ p} (corePP' p G) = corePP' p G := by
    refine le_antisymm ?_ (le_coreAbove _ _)
    refine le_coreAbove_of (N := coreP p G) (N' := coreP p G) le_rfl ?_
    rw [← relIndex_mul_relIndex _ _ _ coreP_le_corePP' (le_coreAbove _ _)]
    exact (isPrimeSetNumber_relIndex_coreAbove _ _).mul (isPrimeSetNumber_relIndex_coreAbove _ _)
  exact eq_top_of_coreAbove_eq hG h1 h2

theorem hasPSeries_of_corePP'_eq_top (h : corePP' p G = ⊤) : HasPSeries p G 5 := by
  have hcPn : (coreP p G).Normal := coreAbove_normal _ _
  refine hasPSeries_five (N₁ := ⊥) (N₂ := coreP p G) (N₃ := ⊤) (N₄ := ⊤) bot_le le_top le_rfl
    (by rw [card_bot]; exact isPrimeSetNumber_one _) ?_ ?_
    (by rw [relIndex_self]; exact isPrimeSetNumber_one _)
    (by rw [index_top]; exact isPrimeSetNumber_one _)
  · rw [relIndex_bot_left]
    exact isPrimeSetNumber_card_of_isPGroup isPGroup_coreP
  · rw [← h]
    exact isPrimeSetNumber_relIndex_coreAbove _ _

theorem hasPSeries_sup_corePP' (P : Sylow p G) :
    HasPSeries p ↥((P : Subgroup G) ⊔ corePP' p G) 5 := by
  set K := (P : Subgroup G) ⊔ corePP' p G with hK
  have hcPn : (coreP p G).Normal := coreAbove_normal _ _
  have hT₂n : (corePP' p G).Normal := coreAbove_normal _ _
  have hT₂K : corePP' p G ≤ K := le_sup_right
  have hcPK : coreP p G ≤ K := coreP_le_corePP'.trans hT₂K
  refine hasPSeries_five (N₁ := ⊥) (N₂ := (coreP p G).subgroupOf K)
    (N₃ := (corePP' p G).subgroupOf K) (N₄ := ⊤) bot_le
    (comap_mono coreP_le_corePP') le_top (by rw [card_bot]; exact isPrimeSetNumber_one _)
    ?_ ?_ ?_ (by rw [index_top]; exact isPrimeSetNumber_one _)
  · rw [relIndex_bot_left, Nat.card_congr (subgroupOfEquivOfLe hcPK).toEquiv]
    exact isPrimeSetNumber_card_of_isPGroup isPGroup_coreP
  · rw [relIndex_subgroupOf hT₂K]
    exact isPrimeSetNumber_relIndex_coreAbove _ _
  · rw [relIndex_top_right]
    change IsPrimeSetNumber _ ((corePP' p G).relIndex K)
    rw [hK, relIndex_sup_right]
    exact (isPrimeSetNumber_card_of_isPGroup P.isPGroup').dvd (relIndex_dvd_card _ _)

end Structure

end CFSG.GroupTheory.FT63ChII
