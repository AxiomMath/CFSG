module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviSL2
public import CFSG.LieType.Steinberg.RankTwo.Statement
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.CurtisTits.Recognition
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import Certificates.Certificate115
public import Certificates.Certificate116

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley (WeylGroup canonicalRep coxeterSystem simple torusGroup borelGroup)
open scoped commutatorElement

section Centre

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_torusElt_r_of_radAction_fix
    {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir)
    (hfa : radAction ⟨l, hl⟩ ![1, 0, 0, 0] = ![1, 0, 0, 0])
    (hfb : radAction ⟨l, hl⟩ ![0, 0, 0, 1] = ![0, 0, 0, 1]) :
    ∃ t : Kˣ, t ^ 3 = 1 ∧ l = torusElt .G2 K g2ir t := by
  have hT := radAction_spec ⟨l, hl⟩
  obtain ⟨ρ, -, -, -, -, hrange, -, hcell0, hcell⟩ := g2_rank_one (K := K) g2ir
  have hl' := hl
  rw [← hrange] at hl'
  obtain ⟨g, hg⟩ := hl'
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · obtain ⟨t, b, e⟩ : ∃ (t : Kˣ) (b : K),
        ρ g = torusElt .G2 K g2ir t * pinnedX .G2 K g2r b :=
      ⟨_, _, by rw [hcell0 g hc, xUnit_g2ir]⟩
    have hact : ActsOnRadical l (radDiag t ∘ₗ radMr b) := by
      rw [← hg, e]
      exact (actsOnRadical_torusElt_r t).mul (actsOnRadical_pinnedX_r b)
    have he := hact.unique hT
    have h0 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![1, 0, 0, 0] 0) he
    have h1 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![1, 0, 0, 0] 1) he
    simp only [hfa] at h0 h1
    simp [radDiag, radMr] at h0 h1
    refine ⟨t, Units.ext (by simpa using h0), ?_⟩
    rw [← hg, e, h1, pinnedX_zero, mul_one]
  · exfalso
    obtain ⟨c₁, t, c₂, e⟩ : ∃ (c₁ : K) (t : Kˣ) (c₂ : K), ρ g = pinnedX .G2 K g2r c₁ *
        torusElt .G2 K g2ir t * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r c₂ :=
      ⟨_, _, _, by rw [hcell g hc, xUnit_g2ir, xUnit_g2ir]⟩
    have hact : ActsOnRadical l
        (((radMr c₁ ∘ₗ radDiag t) ∘ₗ radSwap) ∘ₗ radMr c₂) := by
      rw [← hg, e]
      exact (((actsOnRadical_pinnedX_r _).mul (actsOnRadical_torusElt_r _)).mul
        actsOnRadical_weylElt_r).mul (actsOnRadical_pinnedX_r _)
    have he := hact.unique hT
    have h0 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![0, 0, 0, 1] 0) he
    simp only [hfb] at h0
    simp [radDiag, radMr, radSwap] at h0

theorem g2Centralizer_g2LongA2_le :
    g2Centralizer K (g2LongA2 K : Set (ModGL .G2 K)) ≤ g2TorusR K := by
  intro z hz
  obtain ⟨hzC, hzc⟩ := mem_inf.1 hz
  have hz' : ∀ y ∈ g2LongA2 K, z * y = y * z := fun y hy =>
    (mem_centralizer_iff.1 hzc y hy).symm
  obtain ⟨-, -, -, -, hset, -⟩ := even_G2_highest_long_root_centralizer K
  have hzL : z ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) :=
    mem_inf.2 ⟨hzC, mem_centralizer_singleton_iff.2 (hz' _ (pinnedX_c_mem_g2LongA2 1))⟩
  rw [hset] at hzL
  obtain ⟨q, hq, l, hl, hql⟩ := hzL
  beta_reduce at hql
  subst hql
  have hfa : radAction ⟨l, hl⟩ ![1, 0, 0, 0] = ![1, 0, 0, 0] := by
    refine radAction_eq_of_commute hq hl _ ?_
    have h := hz' _ (pinnedX_a_mem_g2LongA2 1)
    rwa [pinnedX_a_eq_g2N] at h
  have hfb : radAction ⟨l, hl⟩ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    refine radAction_eq_of_commute hq hl _ ?_
    have h := hz' _ (pinnedX_b_mem_g2LongA2 1)
    rwa [pinnedX_b_eq_g2N] at h
  obtain ⟨t, ht3, rfl⟩ := eq_torusElt_r_of_radAction_fix hl hfa hfb
  have htc : ∀ y ∈ g2LongA2 K, y * torusElt .G2 K g2ir t = torusElt .G2 K g2ir t * y :=
    fun y hy => mem_centralizer_singleton_iff.1 (g2LongA2_le_centralizer_torusElt ht3 hy)
  have hqc : ∀ y ∈ g2LongA2 K, q * y = y * q := by
    intro y hy
    have h1 := hz' y hy
    calc q * y = q * torusElt .G2 K g2ir t * y * (torusElt .G2 K g2ir t)⁻¹ := by
          rw [mul_assoc q, ← htc y hy]
          group
      _ = y * q := by rw [h1, mul_assoc y, mul_inv_cancel_right]
  refine ⟨t, ?_⟩
  show torusElt .G2 K g2ir t = q * torusElt .G2 K g2ir t
  suffices hq1 : q = 1 by rw [hq1, one_mul]
  obtain ⟨B, C, D, E, F, rfl⟩ := hq
  have hinvol : ∀ y : ModGL .G2 K, y ∈ g2LongA2 K → y * y = 1 →
      y * g2N 0 B C D E F * y = g2N 0 B C D E F := fun y hy hyy => by
    rw [mul_assoc, hqc y hy, ← mul_assoc, hyy, one_mul]
  have hE := hinvol _ (pinnedX_a_mem_g2LongA2 1) (pinnedX_mul_self g2a 1)
  rw [conj_a] at hE
  obtain ⟨-, -, -, -, -, hE'⟩ := g2N_injective hE
  have hE0 : E = 0 := by simpa using hE'
  subst hE0
  have hB := hinvol _ (pinnedX_b_mem_g2LongA2 1) (pinnedX_mul_self g2b 1)
  rw [conj_b] at hB
  obtain ⟨-, -, -, -, -, hB'⟩ := g2N_injective hB
  have hB0 : B = 0 := by simpa using hB'
  subst hB0
  have hna : pinnedX .G2 K g2na 1 ∈ g2LongA2 K := by
    rw [g2na_eq_neg]
    exact pinnedX_na_mem_g2LongA2 1
  have hC : pinnedX .G2 K g2na 1 * g2N 0 0 C D 0 F * (pinnedX .G2 K g2na 1)⁻¹ =
      g2N 0 0 C D 0 F := by
    rw [pinnedX_inv_eq]
    exact hinvol _ hna (pinnedX_mul_self g2na 1)
  rw [conj_na_one_g2N] at hC
  obtain ⟨h1, -, -, -, h5, -⟩ := g2N_injective hC
  subst h1
  have hF0 : F = 0 := by simpa using h5
  subst hF0
  have hnc : canonicalRep (coxeterSystem .G2) K (simple .G2 g2ia *
      (simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia)))) ∈ g2LongA2 K :=
    canonicalRep_mem_g2LongA2_of_weyl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hv : g2N (0 : K) 0 0 D 0 0 = pinnedX .G2 K g2v D := (pinnedX_v_eq_g2N D).symm
  have hcomm := hqc _ hnc
  rw [hv] at hcomm
  have hconj := canonicalRep_conj (K := K) (simple .G2 g2ia *
      (simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia)))) isRoot_g2v D
  rw [show (simple .G2 g2ia * (simple .G2 g2ir * (simple .G2 g2ia *
      (simple .G2 g2ir * simple .G2 g2ia)))) • g2v = -g2u by
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)] at hconj
  rw [← hcomm, mul_inv_cancel_right] at hconj
  have hpos : pinnedX .G2 K g2v D ∈ borelGroup .G2 K := by
    refine posUnipotent_le_borelGroup ?_
    rw [pinnedX_v_eq_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  have hneg : pinnedX .G2 K g2v D ∈ negUnipotent .G2 K := by
    rw [hconj]
    exact pinnedX_neg_mem_negUnipotent (Or.inr (Or.inr (Or.inl rfl))) D
  have h1 : pinnedX .G2 K g2v D = 1 := eq_one_of_mem_borel_of_mem_neg hpos hneg
  have hD0 : D = 0 := pinnedX_injective .G2 K _ (h1.trans (pinnedX_zero .G2 K _).symm)
  subst hD0
  exact g2N_zero

theorem center_g2LongA2
    (hK4 : Nat.card K = 4) :
    (center ↥(g2LongA2 K)).map (g2LongA2 K).subtype = g2TorusR K := by
  have ht3 : ∀ t : Kˣ, t ^ 3 = 1 := fun t => by
    have h := pow_card_eq_one' (x := t)
    rwa [Nat.card_units, hK4] at h
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine g2Centralizer_g2LongA2_le (mem_inf.2 ⟨g2LongA2_le_adjointGroup z.2,
      mem_centralizer_iff.2 fun y hy => ?_⟩)
    exact congrArg Subtype.val (mem_center_iff.1 hz ⟨y, hy⟩)
  · rintro _ ⟨t, rfl⟩
    have hmem : LieType.Chevalley.torusEltHom .G2 K g2ir t ∈ g2LongA2 K :=
      torusGroup_le_g2LongA2 (LieType.Chevalley.torusElt_mem_torusGroup _ _)
    refine ⟨⟨_, hmem⟩, mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_singleton_iff.1 (g2LongA2_le_centralizer_torusElt (ht3 t) y.2)

theorem odd_card_g2Centralizer_sup_g2LongA2 :
    Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ g2LongA2 K : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K)))) := by
  have hHL : g2TorusR K ≤ g2LongA2 K := by
    rintro _ ⟨t, rfl⟩
    exact torusGroup_le_g2LongA2 (LieType.Chevalley.torusElt_mem_torusGroup _ _)
  rw [sup_eq_right.2 hHL]
  obtain ⟨k, hk⟩ := card_dvd_of_le (g2Centralizer_g2LongA2_le (K := K))
  rw [card_g2TorusR] at hk
  exact Nat.Odd.of_mul_left (hk ▸ odd_card_sub_one)

end Centre

section SL3

open scoped Matrix

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

variable {K : Type} [Field K]

theorem mem_rootsA2 {γ : Fin 2 → ℤ} : γ ∈ RA2 ↔
    γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![-1, 0] ∨ γ = ![0, -1] ∨ γ = ![-1, -1] := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  have inj := CFSG.LieType.Universal.SpecialLinear.toStd_injective 2
  constructor
  · rintro ⟨i, j, hij, h⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl (inj (h.trans (by decide)))
    · exact Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide))))))
    · exact absurd rfl hij
    · exact Or.inr (Or.inl (inj (h.trans (by decide))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inj (h.trans (by decide)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))))
    · exact absurd rfl hij
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide⟩
    · exact ⟨1, 0, by decide, by decide⟩
    · exact ⟨2, 1, by decide, by decide⟩
    · exact ⟨2, 0, by decide, by decide⟩

@[expose] def a2Long (γ : Fin 2 → ℤ) : Fin Tag.G2.rank → ℤ :=
  γ 0 • g2a + γ 1 • g2b

abbrev g2sa
    : WeylGroup .G2 := simple .G2 g2ia

abbrev g2sr
    : WeylGroup .G2 := simple .G2 g2ir

theorem commute_pinnedX_self
    (γ : Fin Tag.G2.rank → ℤ) (c d : K) :
    Commute (pinnedX .G2 K γ c) (pinnedX .G2 K γ d) := by
  show _ * _ = _ * _
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

variable [CharP K 2]

theorem comm_weyl_ab
    (w : WeylGroup .G2) (s t : K) :
    ⁅pinnedX .G2 K (w • g2a) s, pinnedX .G2 K (w • g2b) t⁆ = pinnedX .G2 K (w • g2c) (s * t) := by
  have h := congrArg (MulAut.conj (canonicalRep (coxeterSystem .G2) K w)) (comm_a_b s t)
  rw [map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    canonicalRep_conj w isRoot_g2a, canonicalRep_conj w isRoot_g2b,
    canonicalRep_conj w isRoot_g2c] at h
  exact h

theorem comm_weyl_ac
    (w : WeylGroup .G2) (s t : K) :
    ⁅pinnedX .G2 K (w • g2a) s, pinnedX .G2 K (w • g2c) t⁆ = 1 := by
  have h := congrArg (MulAut.conj (canonicalRep (coxeterSystem .G2) K w))
    (commutatorElement_eq_one_iff_commute.2 (commute_a_c s t))
  rw [map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply,
    canonicalRep_conj w isRoot_g2a, canonicalRep_conj w isRoot_g2c, map_one] at h
  exact h

theorem commutator_a2Long
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2)
    (hαβ : α + β ≠ 0) (c d : K) :
    (α + β ∈ RA2 → ⁅pinnedX .G2 K (a2Long α) c, pinnedX .G2 K (a2Long β) d⁆ =
        pinnedX .G2 K (a2Long (α + β)) (c * d)) ∧
      (α + β ∉ RA2 → ⁅pinnedX .G2 K (a2Long α) c, pinnedX .G2 K (a2Long β) d⁆ = 1) := by
  rcases mem_rootsA2.1 hα with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem_rootsA2.1 hβ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (1 : WeylGroup .G2) • g2a = a2Long ![1, 0] := by
      simp only [one_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (1 : WeylGroup .G2) • g2b = a2Long ![0, 1] := by
      simp only [one_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (1 : WeylGroup .G2) • g2c = a2Long (![1, 0] + ![0, 1]) := by
      simp only [one_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (1 : WeylGroup .G2) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (1 : WeylGroup .G2) • g2a = a2Long ![1, 0] := by
      simp only [one_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (1 : WeylGroup .G2) • g2c = a2Long ![1, 1] := by
      simp only [one_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (1 : WeylGroup .G2) c d
    rwa [e1, e3] at h
  · exact absurd (by decide) hαβ
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sr * g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr * g2sa * g2sr) • g2c = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sr * g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sr * g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sr * g2sa * g2sr * g2sa * g2sr) • g2b = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr * g2sa * g2sr) • g2c = a2Long (![1, 0] + ![-1, -1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sr * g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sr) • g2a = a2Long ![0, 1] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sr) • g2b = a2Long ![1, 0] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr) • g2c = a2Long (![0, 1] + ![1, 0]) := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sr) c d
    rwa [e1, e2, e3] at h
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sr) • g2a = a2Long ![0, 1] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr) • g2c = a2Long ![1, 1] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sr) c d
    rwa [e1, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![0, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr) • g2c = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e3] at h
  · exact absurd (by decide) hαβ
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![0, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa * g2sr * g2sa * g2sr) • g2b = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr) • g2c = a2Long (![0, 1] + ![-1, -1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sr * g2sa * g2sr) • g2a = a2Long ![1, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr) • g2c = a2Long ![1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sr * g2sa * g2sr) c d
    rwa [e1, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa * g2sr) • g2a = a2Long ![1, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr) • g2c = a2Long ![0, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa * g2sr) c d
    rwa [e1, e3] at h
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa * g2sr) • g2a = a2Long ![1, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa * g2sr) • g2b = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr) • g2c = a2Long (![1, 1] + ![-1, 0]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa * g2sr) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sr * g2sa * g2sr) • g2a = a2Long ![1, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sr * g2sa * g2sr) • g2b = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr) • g2c = a2Long (![1, 1] + ![0, -1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sr * g2sa * g2sr) c d
    rwa [e1, e2, e3] at h
  · exact absurd (by decide) hαβ
  · exact absurd (by decide) hαβ
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa) • g2a = a2Long ![-1, 0] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa) • g2c = a2Long ![0, 1] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa) c d
    rwa [e1, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa) • g2a = a2Long ![-1, 0] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa) • g2b = a2Long ![1, 1] := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa) • g2c = a2Long (![-1, 0] + ![1, 1]) := by
      simp only [LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa) c d
    rwa [e1, e2, e3] at h
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) • g2b = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) • g2c = a2Long (![-1, 0] + ![0, -1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) • g2a = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) • g2c = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa * g2sr * g2sa * g2sr * g2sa * g2sr) c d
    rwa [e1, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sr * g2sa) • g2a = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa) • g2c = a2Long ![1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sr * g2sa) c d
    rwa [e1, e3] at h
  · exact absurd (by decide) hαβ
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sr * g2sa) • g2a = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sr * g2sa) • g2b = a2Long ![1, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa) • g2c = a2Long (![0, -1] + ![1, 1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sr * g2sa) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr * g2sa) • g2a = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa * g2sr * g2sa * g2sr * g2sa) • g2b = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr * g2sa) • g2c = a2Long (![0, -1] + ![-1, 0]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa * g2sr * g2sa * g2sr * g2sa) c d
    rwa [e1, e2, e3] at h
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa * g2sr * g2sa * g2sr * g2sa) • g2a = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa * g2sr * g2sa) • g2c = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa * g2sr * g2sa * g2sr * g2sa) c d
    rwa [e1, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sr * g2sa * g2sr * g2sa) • g2a = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sr * g2sa * g2sr * g2sa) • g2b = a2Long ![1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr * g2sa) • g2c = a2Long (![-1, -1] + ![1, 0]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sr * g2sa * g2sr * g2sa) c d
    rwa [e1, e2, e3] at h
  · refine ⟨fun _ => ?_, fun h => absurd (mem_rootsA2.2 (by decide)) h⟩
    have e1 : (g2sa * g2sr * g2sa) • g2a = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e2 : (g2sa * g2sr * g2sa) • g2b = a2Long ![0, 1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa) • g2c = a2Long (![-1, -1] + ![0, 1]) := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ab (K := K) (g2sa * g2sr * g2sa) c d
    rwa [e1, e2, e3] at h
  · exact absurd (by decide) hαβ
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sa * g2sr * g2sa) • g2a = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sa * g2sr * g2sa) • g2c = a2Long ![-1, 0] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sa * g2sr * g2sa) c d
    rwa [e1, e3] at h
  · refine ⟨fun h => absurd h (by rw [mem_rootsA2]; decide), fun _ => ?_⟩
    have e1 : (g2sr * g2sa * g2sr * g2sa) • g2a = a2Long ![-1, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have e3 : (g2sr * g2sa * g2sr * g2sa) • g2c = a2Long ![0, -1] := by
      simp only [mul_smul, LieType.Chevalley.simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h := comm_weyl_ac (K := K) (g2sr * g2sa * g2sr * g2sa) c d
    rwa [e1, e3] at h
  · exact ⟨fun h => absurd h (by rw [mem_rootsA2]; decide),
      fun _ => commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_self _ c d)⟩

omit [CharP K 2] in
theorem mem_commOrder_list_iff
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ O.list α β ↔ p = (1, 1) ∧ α + β ∈ RA2 := by
  have hα' : α ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hα
  have hβ' : β ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hβ
  rw [O.mem_iff α hα' β hβ' hαβ p]
  constructor
  · intro hp
    obtain ⟨rfl, -⟩ := (CFSG.LieType.Steinberg.SL.mem_expPairs_iff (F := K) hα hβ hαβ p).1 hp
    obtain ⟨-, -, h⟩ := hp
    rw [CFSG.LieType.Steinberg.SL.Φ_roots] at h
    exact ⟨rfl, by simpa using h⟩
  · rintro ⟨rfl, h⟩
    refine ⟨one_pos, one_pos, ?_⟩
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    simpa using h

omit [CharP K 2] in
theorem commOrder_list_eq_singleton
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∈ RA2) :
    O.list α β = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (O.nodup α β)
    (List.nodup_singleton _)).2 fun p => by
      rw [mem_commOrder_list_iff O hα hβ hαβ, List.mem_singleton, and_iff_left h])

omit [CharP K 2] in
theorem commOrder_list_eq_nil
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∉ RA2) :
    O.list α β = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun p hp => h ((mem_commOrder_list_iff O hα hβ hαβ p).1 hp).2

theorem commutatorFormula_a2Long
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K))) :
    CFSG.LieType.Steinberg.CommutatorFormula (fun γ c => pinnedX .G2 K (a2Long γ) c) O
      (CFSG.LieType.Steinberg.SL.commC (m := 2)) := by
  intro α hα β hβ hαβ c d
  have hc1 : ((CFSG.LieType.Steinberg.SL.commC (m := 2) α β (1, 1) : ℤ) : K) = 1 := by
    have h := CFSG.LieType.Steinberg.SL.commC_natAbs (m := 2) α β (1, 1)
    rcases Int.natAbs_eq (CFSG.LieType.Steinberg.SL.commC (m := 2) α β (1, 1)) with e | e <;>
      rw [e, h] <;> simp [CharTwo.neg_eq]
  have hα' : α ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := K)]; exact hα
  have hβ' : β ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := K)]; exact hβ
  obtain ⟨h1, h2⟩ := commutator_a2Long hα' hβ' hαβ c d
  by_cases h : α + β ∈ RA2
  · rw [commOrder_list_eq_singleton O hα' hβ' hαβ h]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
      pow_one, hc1, one_mul]
    exact h1 h
  · rw [commOrder_list_eq_nil O hα' hβ' hαβ h]
    simp only [List.map_nil, List.prod_nil]
    exact h2 h

theorem a2Long_a : a2Long ![1, 0] = g2a := List.ofFn_injective (by decide +kernel)
theorem a2Long_b : a2Long ![0, 1] = g2b := List.ofFn_injective (by decide +kernel)
theorem a2Long_c : a2Long ![1, 1] = g2c := List.ofFn_injective (by decide +kernel)
theorem a2Long_na : a2Long ![-1, 0] = -g2a := List.ofFn_injective (by decide +kernel)
theorem a2Long_nb : a2Long ![0, -1] = -g2b := List.ofFn_injective (by decide +kernel)
theorem a2Long_nc : a2Long ![-1, -1] = -g2c := List.ofFn_injective (by decide +kernel)

variable [Finite K]

theorem exists_sl3_hom :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K,
      ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
        pinnedX .G2 K (a2Long γ) c := by
  obtain ⟨⟨-, ⟨O⟩, -⟩, -, huniv, -⟩ := CFSG.LieType.Steinberg.RankTwo.sl3_rankTwoPresentation K
  obtain ⟨φ, hφ, -⟩ := huniv O (CFSG.LieType.Steinberg.SL.commC (m := 2))
    (CFSG.LieType.Steinberg.SL.commutatorFormula O) (ModGL .G2 K)
    (fun γ c => pinnedX .G2 K (a2Long γ) c) (fun γ _ c d => pinnedX_add _ _ _ c d)
    (commutatorFormula_a2Long O)
  exact ⟨φ, hφ⟩

omit [CharP K 2] [Finite K] in
theorem pinnedX_a2Long_mem
    {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) (c : K) :
    pinnedX .G2 K (a2Long γ) c ∈ g2LongA2 K := by
  rcases mem_rootsA2.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a2Long_a]
    exact pinnedX_a_mem_g2LongA2 c
  · rw [a2Long_b]
    exact pinnedX_b_mem_g2LongA2 c
  · rw [a2Long_c]
    exact pinnedX_c_mem_g2LongA2 c
  · rw [a2Long_na]
    exact pinnedX_na_mem_g2LongA2 c
  · rw [a2Long_nb]
    exact pinnedX_nb_mem_g2LongA2 c
  · rw [a2Long_nc]
    exact pinnedX_nc_mem_g2LongA2 c

omit [CharP K 2] in
theorem range_sl3_hom
    {φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K}
    (hφ : ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
      pinnedX .G2 K (a2Long γ) c) : φ.range = g2LongA2 K := by
  obtain ⟨⟨hpar, -⟩, hgen, -⟩ := CFSG.LieType.Steinberg.RankTwo.sl3_rankTwoPresentation.{0} K
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    refine (closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg
    obtain ⟨γ, hγ, hgγ⟩ := hg
    obtain ⟨c, rfl⟩ := ((hpar γ hγ).1 g).1 hgγ
    rw [SetLike.mem_coe, hφ γ hγ c]
    exact pinnedX_a2Long_mem hγ c
  · have key : ∀ γ ∈ RA2, ∀ c : K, pinnedX .G2 K (a2Long γ) c ∈ φ.range := fun γ hγ c =>
      ⟨_, hφ γ hγ c⟩
    refine (closure_le _).2 ?_
    rintro _ (((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · exact a2Long_a ▸ key _ (mem_rootsA2.2 (by decide)) x
    · exact a2Long_na ▸ key _ (mem_rootsA2.2 (by decide)) x
    · exact a2Long_b ▸ key _ (mem_rootsA2.2 (by decide)) x
    · exact a2Long_nb ▸ key _ (mem_rootsA2.2 (by decide)) x
    · exact a2Long_c ▸ key _ (mem_rootsA2.2 (by decide)) x
    · exact a2Long_nc ▸ key _ (mem_rootsA2.2 (by decide)) x


omit [CharP K 2] [Finite K] in
theorem exists_basis_of_square_zero' (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (hN0 : N ≠ 0) :
    ∃ v w x : Fin 3 → K, N *ᵥ w = v ∧ N *ᵥ v = 0 ∧ N *ᵥ x = 0 ∧
      LinearIndependent K ![v, w, x] := by
  let L : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin N
  have hL : ∀ u, L u = N *ᵥ u := fun u => rfl
  have hL2 : ∀ u, L (L u) = 0 := fun u => by
    rw [hL, hL, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra hcon
    apply hN0
    ext i j
    have := congrFun (not_not.1 (fun h => hcon ⟨Pi.single j 1, h⟩)) i
    simpa [hL, Matrix.mulVec_single_one] using this
  set v := L w with hvdef
  have hv0 : L v = 0 := hL2 w
  have hrange : LinearMap.range L ≤ LinearMap.ker L := by
    rintro _ ⟨u, rfl⟩
    exact hL2 u
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hle := Submodule.finrank_mono hrange
  have hpos : 0 < Module.finrank K (LinearMap.range L) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, w, rfl⟩, fun h => hw (by simpa using congrArg Subtype.val h)⟩
  have h3 : Module.finrank K (Fin 3 → K) = 3 := by simp
  have hker : Module.finrank K (LinearMap.ker L) = 2 := by omega
  have hspan : Submodule.span K {v} < LinearMap.ker L := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hv0
    · intro h
      have := congrArg (fun S : Submodule K (Fin 3 → K) => Module.finrank K S) h
      rw [finrank_span_singleton hw, hker] at this
      omega
  obtain ⟨x, hxker, hxspan⟩ := IsConcreteLE.exists_of_lt hspan
  have hxL : L x = 0 := hxker
  refine ⟨v, w, x, rfl, hv0, hxL, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h1 := congrArg L hg
  simp only [map_add, map_smul, hv0, hxL, smul_zero, zero_add, add_zero, map_zero] at h1
  have hg1 : g 1 = 0 := by
    have : g 1 • v = 0 := by simpa [hvdef] using h1
    exact (smul_eq_zero.mp this).resolve_right hw
  rw [hg1, zero_smul, add_zero] at hg
  have hg2 : g 2 = 0 := by
    by_contra hne
    apply hxspan
    rw [Submodule.mem_span_singleton]
    refine ⟨-(g 2)⁻¹ * g 0, ?_⟩
    have h5 : g 2 • x = -(g 0 • v) := eq_neg_of_add_eq_zero_right hg
    calc (-(g 2)⁻¹ * g 0) • v = (g 2)⁻¹ • (-(g 0 • v)) := by
          rw [smul_neg, neg_mul, neg_smul, smul_smul]
      _ = (g 2)⁻¹ • (g 2 • x) := by rw [h5]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hg2, zero_smul, add_zero] at hg
  have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hw
  fin_cases i <;> simp [hg0, hg1, hg2]

omit [Finite K] in
theorem exists_conj_sl3_x_of_involution {t : Matrix.SpecialLinearGroup (Fin (2 + 1)) K}
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin (2 + 1)) K,
      g⁻¹ * t * g = CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1 := by
  set M₀ : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 0; 0, 0, 1] with hM₀
  have hx : ((CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1 :
      Matrix.SpecialLinearGroup (Fin (2 + 1)) K) : Matrix (Fin 3) (Fin 3) K) = M₀ := by
    rw [CFSG.LieType.Steinberg.SL.x_eq (i := 0) (j := 1) (by decide) (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM₀, Matrix.SpecialLinearGroup.transvection_coe]
  set T : Matrix (Fin 3) (Fin 3) K := (t : Matrix (Fin 3) (Fin 3) K) with hT
  set N : Matrix (Fin 3) (Fin 3) K := T - 1 with hN
  have hTT : T * T = 1 := by
    simpa using congrArg (fun s : Matrix.SpecialLinearGroup (Fin (2 + 1)) K =>
      (s : Matrix (Fin 3) (Fin 3) K)) ht2
  have hNN : N * N = 0 := by
    have h1 : N * N = T * T - T - T + 1 := by
      rw [hN]
      noncomm_ring
    rw [h1, hTT]
    have h2 : (1 : Matrix (Fin 3) (Fin 3) K) + 1 = 0 := by
      ext i j
      by_cases hij : i = j
      · simp [hij, CharTwo.add_self_eq_zero]
      · simp [hij]
    have h3 : T + T = 0 := by
      ext i j
      simp [CharTwo.add_self_eq_zero]
    calc (1 : Matrix (Fin 3) (Fin 3) K) - T - T + 1 = (1 + 1) - (T + T) := by abel
      _ = 0 := by rw [h2, h3, sub_zero]
  have hN0 : N ≠ 0 := by
    intro h
    apply ht1
    apply Subtype.ext
    rw [hN] at h
    simpa [sub_eq_zero] using h
  obtain ⟨v, w, x, hw, hv, hxN, hli⟩ := exists_basis_of_square_zero' N hNN hN0
  set g0 : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![v, w, x] j i with hg0
  have hcols : LinearIndependent K (fun j => g0.col j) := by
    have : (fun j => g0.col j) = ![v, w, x] := by
      funext j
      ext i
      simp [hg0, Matrix.col_apply]
    rw [this]
    exact hli
  have hunit : IsUnit g0.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)
  set d : K := g0.det with hd
  have hd0 : d ≠ 0 := hunit.ne_zero
  set D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, 1, d⁻¹] with hD
  set g : Matrix (Fin 3) (Fin 3) K := g0 * D with hg
  have hdet : g.det = 1 := by
    rw [hg, Matrix.det_mul, hD, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, hd0, ← hd]
  let G : Matrix.SpecialLinearGroup (Fin (2 + 1)) K := ⟨g, hdet⟩
  have hg0col : ∀ i, g i 0 = v i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal]
  have hg1col : ∀ i, g i 1 = w i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal]
  have hg2col : ∀ i, g i 2 = d⁻¹ * x i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal, mul_comm]
  have hTN : T = N + 1 := by rw [hN]; abel
  have hTv : T *ᵥ v = v := by
    rw [hTN, Matrix.add_mulVec, hv, Matrix.one_mulVec, zero_add]
  have hTw : T *ᵥ w = v + w := by
    rw [hTN, Matrix.add_mulVec, hw, Matrix.one_mulVec]
  have hTx : T *ᵥ (fun k => d⁻¹ * x k) = fun k => d⁻¹ * x k := by
    have e : (fun k => d⁻¹ * x k) = d⁻¹ • x := rfl
    rw [e, Matrix.mulVec_smul, hTN, Matrix.add_mulVec, hxN, Matrix.one_mulVec, zero_add]
  have key : T * g = g * M₀ := by
    ext i j
    fin_cases j
    · show (T * g) i 0 = (g * M₀) i 0
      have h1 : (T * g) i 0 = (T *ᵥ v) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg0col]
      rw [h1, hTv]
      simp [Matrix.mul_apply, Fin.sum_univ_three, hM₀, hg0col]
    · show (T * g) i 1 = (g * M₀) i 1
      have h1 : (T * g) i 1 = (T *ᵥ w) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg1col]
      rw [h1, hTw]
      simp [Matrix.mul_apply, Fin.sum_univ_three, hM₀, hg0col, hg1col]
    · show (T * g) i 2 = (g * M₀) i 2
      have h1 : (T * g) i 2 = (T *ᵥ (fun k => d⁻¹ * x k)) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg2col]
      rw [h1, hTx]
      simp [Matrix.mul_apply, Fin.sum_univ_three, hM₀, hg2col]
  have hG : t * G = G * CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx]
    exact key
  refine ⟨G, ?_⟩
  calc G⁻¹ * t * G = G⁻¹ * (t * G) := by group
    _ = G⁻¹ * (G * CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1) := by rw [hG]
    _ = CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1 := by group

end SL3

section Assembly

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem g2LongA2_sl3
    (hK4 : Nat.card K = 4) :
    ⁅g2LongA2 K, g2LongA2 K⁆ = g2LongA2 K ∧
      StatedClassicalModel (RankTwoStandard.rankTwoQuot (g2LongA2 K)) .PSL 3 2 2 ∧
      ∀ x ∈ g2LongA2 K, x ^ 2 = 1 → x ≠ 1 →
        ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1 := by
  obtain ⟨φ, hφ⟩ := exists_sl3_hom (K := K)
  have hrange := range_sl3_hom hφ
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
  have hmem : ∀ g, φ g ∈ g2LongA2 K := fun g => hrange ▸ ⟨g, rfl⟩
  let ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(g2LongA2 K) := φ.codRestrict _ hmem
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have ha1 : φ (CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1) = pinnedX .G2 K g2a 1 := by
    rw [hφ _ (mem_rootsA2.2 (by decide)), a2Long_a]
  have hψ1 : ∃ k, ψ k ≠ 1 := by
    refine ⟨CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1, fun h => ?_⟩
    have h1 : φ (CFSG.LieType.Steinberg.SL.x 2 K ![1, 0] 1) = 1 := congrArg Subtype.val h
    rw [ha1, ← pinnedX_zero .G2 K g2a] at h1
    exact one_ne_zero (pinnedX_injective .G2 K _ h1)
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrange, MonoidHom.range_eq_map, ← map_commutator]
    congr 1
    exact hq.1.commutator_eq_top
  · refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
      inferInstance, by rw [hK4]; norm_num, ⟨?_⟩⟩
    exact (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hψsurj hker).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (2 + 1) K)
  · intro x hx hx2 hx1
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    have hyy : y * y ∈ center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K) := by
      refine hker ?_
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      show φ (y * y) = 1
      rw [map_mul, ← sq, hx2]
    obtain ⟨r, hr, hry⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hyy
    have hy6 : (y * y) ^ 3 = 1 := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hry, ← map_pow]
      simp only [Fintype.card_fin] at hr
      rw [hr, map_one]
      rfl
    have hy'2 : y ^ 3 * y ^ 3 = 1 := by
      rw [← hy6, ← pow_add, ← sq, ← pow_mul]
    have hy'x : φ (y ^ 3) = φ y := by
      rw [map_pow, show 3 = 2 + 1 by rfl, pow_succ, hx2, one_mul]
    have hy'1 : y ^ 3 ≠ 1 := fun h => hx1 (by rw [← hy'x, h, map_one])
    obtain ⟨g, hg⟩ := exists_conj_sl3_x_of_involution hy'1 hy'2
    have hxg : φ y = φ g * pinnedX .G2 K g2a 1 * (φ g)⁻¹ := by
      rw [← hy'x, ← ha1, ← hg, ← map_inv, ← map_mul, ← map_mul]
      group
    refine ⟨weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * (φ g)⁻¹,
      mul_mem (mul_mem (g2RankOne_le_adjointGroup g2ia (weylElt_mem_g2RankOne g2ia 1))
        (g2RankOne_le_adjointGroup g2ir (weylElt_mem_g2RankOne g2ir 1)))
        (inv_mem (g2LongA2_le_adjointGroup (hmem g))), ?_⟩
    rw [hxg, show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * (φ g)⁻¹ *
        (φ g * pinnedX .G2 K g2a 1 * (φ g)⁻¹) *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * (φ g)⁻¹)⁻¹ =
        weylElt .G2 K g2ia 1 * (weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a 1 *
          (weylElt .G2 K g2ir 1)⁻¹) * (weylElt .G2 K g2ia 1)⁻¹ by group,
      weylElt_r_conj_a, weylElt_a_conj_b]

theorem g2Levi187_four
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : m = 2) :
    ∃ L : Subgroup (ModGL .G2 K), L ≤ adjointGroup .G2 K ∧ rootSubgroup .G2 K g2c ≤ L ∧
      ⁅L, L⁆ = L ∧ L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)) ∧
      (∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
        h⁻¹ * x ∈ L) ∧
      Odd (Nat.card (center ↥L)) ∧
      (if m = 2 then StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 3 2 2
        else StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 2 2 m) ∧
      Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)))) ∧
      (∀ x ∈ L, x ^ 2 = 1 → x ≠ 1 →
        ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1) ∧
      (m = 2 → (center ↥L).map L.subtype = g2TorusR K) := by
  subst hm
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨hperf, hmodel, hinv⟩ := g2LongA2_sl3 hK4
  have heq := g2Centralizer_g2TorusR_eq_g2LongA2 hK4
  have hZ := center_g2LongA2 hK4
  refine ⟨g2LongA2 K, g2LongA2_le_adjointGroup,
    (closure_le _).2 fun _ ⟨x, hx⟩ => hx ▸ pinnedX_c_mem_g2LongA2 x, hperf,
    fun x hx => (mem_inf.1 (heq ▸ hx : x ∈ g2Centralizer K (g2TorusR K :
      Set (ModGL .G2 K)))).2,
    fun x hx => ⟨1, one_mem _, by rw [inv_one, one_mul, ← heq]; exact hx⟩, ?_,
    by simpa using hmodel, odd_card_g2Centralizer_sup_g2LongA2, hinv, fun _ => hZ⟩
  have hc : Nat.card (center ↥(g2LongA2 K)) = Nat.card (g2TorusR K) := by
    rw [← hZ]
    exact (Nat.card_congr (equivMapOfInjective _ _ (g2LongA2 K).subtype_injective).toEquiv)
  rw [hc, card_g2TorusR]
  exact odd_card_sub_one

theorem g2Levi187 :
    G2Levi187 := by
  intro K _ _ _ m hK hm
  rcases eq_or_lt_of_le hm with h | h
  · exact g2Levi187_four hK h.symm
  · exact g2Levi187_of_three_le hK h

end Assembly

end CFSG.ComponentClassification.RankTwoExceptional
