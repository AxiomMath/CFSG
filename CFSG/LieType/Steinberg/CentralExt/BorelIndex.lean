module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LieType.RootSystem.Form

public section

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped Pointwise

namespace CFSG.LieType.Steinberg.CentralExt.BorelIndex

open CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

theorem inversionUnipotent_one : inversionUnipotent D (1 : W) = ⊥ := by
  refine iSup₂_eq_bot.2 fun γ hγ => ?_
  obtain ⟨-, h₁, h₂⟩ := hγ
  rw [map_one, Module.End.one_apply] at h₂
  exact absurd (h₁.trans h₂) (lt_irrefl 0)

theorem exists_rootGroup_le_inversionUnipotent {w : W} (hw : w ≠ 1) :
    ∃ i : Fin D.rank, D.rootGroup (Pi.single i 1) ≤ inversionUnipotent D w := by
  obtain ⟨i, hi⟩ := (cs).exists_rightDescent_of_ne_one hw
  exact ⟨i, rootGroup_le_inversionUnipotent ((RootSystem.ofCartan D.isFiniteType
    D.divisible).single_mem i) (ht_single_pos i) (ht_weylAction_single_neg hi)⟩

include hct in
theorem card_eq_sum [Finite K] [Fintype W] (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) :
    Nat.card K = ∑ w : W, Nat.card (borel D H) * Nat.card (inversionUnipotent D w) := by
  let F : (Σ w : W, borel D H × inversionUnipotent D w) → K :=
    fun q => (q.2.1 : K) * nrep hct q.1 * (q.2.2 : K)
  have hF : Function.Bijective F := by
    refine ⟨fun q q' h => ?_, fun g => ?_⟩
    · obtain ⟨w, b, u⟩ := q
      obtain ⟨w', b', u'⟩ := q'
      have hmem : ∀ (v : W) (c : borel D H) (d : inversionUnipotent D v),
          ((v, (c : K), (d : K)) : W × K × K) ∈
            {q : W × K × K | q.2.1 ∈ borel D H ∧ q.2.2 ∈ inversionUnipotent D q.1} :=
        fun v c d => ⟨c.2, d.2⟩
      have := injOn_bruhat_normalForm hct hext hBU (hmem w b u) (hmem w' b' u') h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, hb, hu⟩ := this
      obtain rfl : b = b' := Subtype.ext hb
      obtain rfl : u = u' := Subtype.ext hu
      rfl
    · obtain ⟨⟨w, b, u⟩, ⟨⟨hb, hu⟩, hg⟩, -⟩ := existsUnique_bruhat_normalForm hct hext hBU g
      exact ⟨⟨w, ⟨b, hb⟩, ⟨u, hu⟩⟩, hg.symm⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_sigma]
  simp only [Nat.card_prod]

include hct in
theorem card_borel [Finite K] (hext : SteinbergExtras D n H) :
    Nat.card (borel D H) = Nat.card (⨆ i, H i : Subgroup K) * Nat.card (posUnipotent D) := by
  let F : (⨆ i, H i : Subgroup K) × posUnipotent D → borel D H :=
    fun q => ⟨(q.1 : K) * q.2, by
      have : (q.1 : K) * q.2 ∈ ((⨆ i, H i : Subgroup K) : Set K) * (posUnipotent D : Set K) :=
        Set.mul_mem_mul q.1.2 q.2.2
      rwa [← coe_borel hct] at this⟩
  have hF : Function.Bijective F := by
    refine ⟨fun q q' h => ?_, fun b => ?_⟩
    · have h' : (q.1 : K) * q.2 = q'.1 * q'.2 := congrArg Subtype.val h
      have hmem : (q'.1 : K)⁻¹ * q.1 ∈ (⨆ i, H i : Subgroup K) ⊓ posUnipotent D := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ q'.1.2) q.1.2, ?_⟩
        have : (q'.1 : K)⁻¹ * q.1 = q'.2 * (q.2 : K)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
        rw [this]
        exact Subgroup.mul_mem _ q'.2.2 (Subgroup.inv_mem _ q.2.2)
      have h0 : (⨆ i, H i : Subgroup K) ⊓ posUnipotent D = ⊥ := hext.torus_inf_posPart
      rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h1 : q.1 = q'.1 := Subtype.ext hmem.symm
      have h2 : q.2 = q'.2 := Subtype.ext (by
        rw [hmem] at h'
        exact mul_left_cancel h')
      exact Prod.ext h1 h2
    · have hb : (b : K) ∈ ((⨆ i, H i : Subgroup K) : Set K) * (posUnipotent D : Set K) := by
        rw [← coe_borel hct]
        exact b.2
      obtain ⟨t, ht, u, hu, htu⟩ := hb
      exact ⟨(⟨t, ht⟩, ⟨u, hu⟩), Subtype.ext htu⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod]

theorem p_dvd_card_inversionUnipotent [Finite K] (hext : SteinbergExtras D n H) {p : ℕ}
    [Fact p.Prime] (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {w : W} (hw : w ≠ 1) :
    p ∣ Nat.card (inversionUnipotent D w) := by
  have hU : IsPGroup p (inversionUnipotent D w) :=
    (isPGroup_iSup_pos hext hX).to_le (inversionUnipotent_le_posUnipotent w)
  obtain ⟨i, hi⟩ := exists_rootGroup_le_inversionUnipotent hw
  have hne : inversionUnipotent D w ≠ ⊥ := fun h => hext.ne_bot _
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (eq_bot_iff.2 (h ▸ hi))
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rcases k with _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hne
  · rw [hk, pow_succ]
    exact dvd_mul_left p _

include hct in
theorem coprime_index_posUnipotent [Finite K] (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) {p : ℕ} [hp : Fact p.Prime]
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hT : p.Coprime (Nat.card (⨆ i, H i : Subgroup K))) : p.Coprime (posUnipotent D).index := by
  classical
  have : Fintype W := @Fintype.ofFinite _ (finite_group D.isFiniteType)
  have hK := card_eq_sum hct hext hBU
  rw [card_borel hct hext] at hK
  set S := ∑ w : W, Nat.card (inversionUnipotent D w)
  have hK' : Nat.card K = Nat.card (posUnipotent D) *
      (Nat.card (⨆ i, H i : Subgroup K) * S) := by
    rw [hK, ← Finset.mul_sum]
    ring
  have hidx : (posUnipotent D).index = Nat.card (⨆ i, H i : Subgroup K) * S := by
    have h := (posUnipotent D).card_mul_index
    rw [hK'] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hS : S % p = 1 := by
    have h1 : S = Nat.card (inversionUnipotent D (1 : W)) +
        ∑ w ∈ Finset.univ.erase (1 : W), Nat.card (inversionUnipotent D w) :=
      (Finset.add_sum_erase Finset.univ (fun w => Nat.card (inversionUnipotent D w))
        (Finset.mem_univ (1 : W))).symm
    have h2 : p ∣ ∑ w ∈ Finset.univ.erase (1 : W), Nat.card (inversionUnipotent D w) :=
      Finset.dvd_sum fun w hw => p_dvd_card_inversionUnipotent hext hX (Finset.ne_of_mem_erase hw)
    obtain ⟨c, hc⟩ := h2
    rw [h1, inversionUnipotent_one, Subgroup.card_bot, hc, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hp.out.one_lt
  rw [hidx]
  refine Nat.Coprime.mul_right hT ?_
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  rw [Nat.mod_eq_zero_of_dvd h] at hS
  exact absurd hS (by norm_num)

end CFSG.LieType.Steinberg.CentralExt.BorelIndex
