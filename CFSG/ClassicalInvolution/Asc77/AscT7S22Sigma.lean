module

public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp51
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire
import CFSG.ClassicalInvolution.Asc77.AscT7AExclude

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace Hyp22Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem not_mu_S3_S4 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) : ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W := by
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hK'Ω : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, h.stand.aEmpty⟩
  obtain ⟨R, R', R₃, hRsyl, hR'syl, hR₃syl, hRR', hRR₃, hR'R₃⟩ :=
    T7B.exists_threeTwinSylow hp hq hΩ hK h.hz h.hK' h.hK₃ h.hne h.hK₃K h.hK₃K'
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := T7A.le_normalizer_of_commutes hRR'.symm
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hRsyl.2.1.to_sup_of_normal_right' hR'syl.2.1 hRn
  have hPn : R ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := sup_le
    (T7A.le_normalizer_of_commutes hRR₃.symm) (T7A.le_normalizer_of_commutes hR'R₃.symm)
  have hQ2 : IsPGroup 2 ↥((R ⊔ R') ⊔ R₃) := hP2.to_sup_of_normal_right' hR₃syl.2.1 hPn
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hRS : R ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR₃S : R₃ ≤ (S : Subgroup G) := le_sup_right.trans hS
  obtain ⟨g, hg⟩ := Thompson.exists_conj_mem_DSet hp hq hΩ hW S
  have hRD : conjSub g R ∈ DSet Ω W := hg R (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : conjSub g R' ∈ DSet Ω W := hg R' (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S
  have hR₃D : conjSub g R₃ ∈ DSet Ω W := hg R₃ (mem_RSet_of_isSylow2In hK₃Ω hR₃syl) hR₃S
  have hKg : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hK'g : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hK₃g : conjSub g K₃ ∈ Ω := hΩ.conjInvariant g K₃ hK₃Ω
  have hRsylg : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hR'sylg : IsSylow2In (conjSub g R') (conjSub g K') := hR'syl.conj g
  have hR₃sylg : IsSylow2In (conjSub g R₃) (conjSub g K₃) := hR₃syl.conj g
  have hTT := Thompson.isTT_muDelta hp hq hΩ hW (thompsonCube G Ω hP W hW)
  obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hRD
  obtain ⟨r', hr', hr'W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hR'D
  obtain ⟨t', ht', ht'W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hR₃D
  obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
  obtain ⟨b, hb, hbeq⟩ := exists_muDelta_eq_piG hR'D hr' hr'W
  obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hR₃D ht' ht'W
  have hKK' : conjSub g K ≠ conjSub g K' := fun e => h.hne.symm ((conjSub_inj g).mp e)
  have hKK₃ : conjSub g K ≠ conjSub g K₃ := fun e => h.hK₃K ((conjSub_inj g).mp e).symm
  have hK'K₃ : conjSub g K' ≠ conjSub g K₃ := fun e => h.hK₃K' ((conjSub_inj g).mp e).symm
  have hab : a ≠ b := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW hRD hR'D hKg hK'g hRsylg hR'sylg hKK' hr hr' hr'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hbeq))
  have hac : a ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW hRD hR₃D hKg hK₃g hRsylg hR₃sylg hKK₃ hr ht' ht'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hbc : b ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW hR'D hR₃D hK'g hK₃g hR'sylg hR₃sylg hK'K₃ hr' ht' ht'W
      (hbeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hab' : a * b = b * a :=
    muGroup_comm_of_comm hRD hR'D hr hr' ((hRR'.conjSub g) r hr r' hr') haeq hbeq
  have hac' : a * c = c * a :=
    muGroup_comm_of_comm hRD hR₃D hr ht' ((hRR₃.conjSub g) r hr t' ht') haeq hceq
  have hbc' : b * c = c * b :=
    muGroup_comm_of_comm hR'D hR₃D hr' ht' ((hR'R₃.conjSub g) r' hr' t' ht') hbeq hceq
  constructor
  · rintro ⟨e⟩
    have hTT3 := T7A.isTT_map_equiv hTT e
    exact T7A.no_two_commuting_perm3 hTT3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      (fun e2 => hab (e.injective e2)) (by rw [← map_mul, ← map_mul, hab'])
  · rintro ⟨e⟩
    have hTT4 := T7A.isTT_map_equiv hTT e
    exact T7A.no_three_commuting_perm4 hTT4 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      (fun e2 => hab (e.injective e2)) (fun e2 => hac (e.injective e2))
      (fun e2 => hbc (e.injective e2))
      (by rw [← map_mul, ← map_mul, hab']) (by rw [← map_mul, ← map_mul, hac'])
      (by rw [← map_mul, ← map_mul, hbc'])

end Hyp22Setting

namespace T7S22

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem perp_of_twin (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = twinSet Ω L := by
  have h1 := (l6_3 p f h.stand.odd h.stand.five G Ω h.stand.hyp K h.stand.mem L hL).1
  rw [← h1, twinSet_eq_of_mem_twinSet h.hz hL]
  exact h.perp

theorem dComp_subset_twinSet (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    dComp Ω K ⊆ twinSet Ω K := by
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  intro J hJ
  have hJ' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    hJ
  clear hJ
  induction hJ' with
  | refl => exact mem_twinSet_self h.stand.mem h.hz
  | @tail M N _ hstep ih =>
    obtain ⟨hNΩ, hadj⟩ := hstep
    have hMΩ : M ∈ Ω := ih.1
    have hpM := perp_of_twin h ih
    have htM : twinSet Ω M = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz ih
    have key : N ∈ omegaNbr Ω M → N ∈ twinSet Ω K := fun hN => by
      have hN' : N ∈ KPerp Ω M := Set.mem_insert_of_mem _ hN
      rwa [hpM, htM] at hN'
    rcases hadj with hN | hM
    · exact key hN
    · exact key (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hNΩ hMΩ hM)

end T7S22

theorem c22_4_sigma_proved (p f : ℕ) [Fact p.Prime] : C22_4_sigma p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ J hJ
  have hs := h.setting
  have hP : PartIHyp p f Ω := ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩
  rcases l7_17_proved (p := p) (f := f) G Ω hP K hs.stand.mem with heq | hWs
  · rw [← heq] at hJ
    exact T7S22.dComp_subset_twinSet hs hJ
  · exfalso
    obtain ⟨h3, h4⟩ := hs.not_mu_S3_S4 hW
    rcases hWs W hW with h1 | h1 | h1
    · exact h3 h1
    · exact h4 h1
    · exact hμ h1

end CFSG.ClassicalInvolution.Asc77
