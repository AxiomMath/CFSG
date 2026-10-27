module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem IsGL3Ext.card_eq {E N : Subgroup G} (h : IsGL3Ext E N) :
    Nat.card E = 168 * Nat.card N := by
  obtain ⟨hNE, hSec⟩ := h
  exact centExt_card_of_secProp_gl32 hNE hSec

theorem IsGL3Ext.le_normalizer {E N : Subgroup G} (h : IsGL3Ext E N) :
    E ≤ normalizer (N : Set G) := by
  obtain ⟨hNE, hN, -⟩ := h
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mp hN

theorem IsGL3Ext.comm_sup_eq {E N : Subgroup G} (h : IsGL3Ext E N) : ⁅E, E⁆ ⊔ N = E := by
  obtain ⟨hNE, hNnorm, hP⟩ := h
  letI := hNnorm
  obtain ⟨e⟩ := hP
  set Q := ↥E ⧸ N.subgroupOf E with hQ
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  have hcardQ : Nat.card Q = 168 :=
    (Nat.card_congr e.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh
  have hna : ¬ IsMulCommutative (⊤ : Subgroup Q) := by
    intro hcomm
    haveI := hcomm
    haveI : IsSimpleGroup (⊤ : Subgroup Q) := (Subgroup.topEquiv (G := Q)).isSimpleGroup
    have hp : (Nat.card (⊤ : Subgroup Q)).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [Subgroup.card_top, hcardQ] at hp
    norm_num at hp
  have hcomm_top : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆) with hb | ht
    · exact absurd (Subgroup.commutator_self_eq_bot_iff.mp hb) hna
    · exact ht
  have hmap : (⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map
      (QuotientGroup.mk' (N.subgroupOf E)) = ⊤ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (N.subgroupOf E)), hcomm_top]
  have hX : (N.subgroupOf E) ⊔ ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ = ⊤ := by
    have hmapX : Subgroup.map (QuotientGroup.mk' (N.subgroupOf E))
        ((N.subgroupOf E) ⊔ ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆) = ⊤ := by
      rw [Subgroup.map_sup, hmap,
        (Subgroup.map_eq_bot_iff (N.subgroupOf E)).mpr (by rw [QuotientGroup.ker_mk'])]
      simp
    have hker := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (N.subgroupOf E))
      (H := (N.subgroupOf E) ⊔ ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
    rw [hmapX, Subgroup.comap_top] at hker
    exact hker.symm
  have hfin : ((N.subgroupOf E) ⊔ ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map E.subtype = E := by
    rw [hX, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.mpr hNE] at hfin
  rwa [sup_comm] at hfin

theorem IsGL3Ext.card_comm {E N : Subgroup G} (h : IsGL3Ext E N) :
    Nat.card ↥⁅E, E⁆ = 168 * Nat.card ↥(⁅E, E⁆ ⊓ N) := by
  have hB : ⁅E, E⁆ ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.commutator_le_of_le (K := E) le_rfl le_rfl).trans h.le_normalizer
  have hprod :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_sup_mul_card_inf (A := N) (B := ⁅E, E⁆) hB
  rw [sup_comm, h.comm_sup_eq, h.card_eq, inf_comm] at hprod
  have hNne : 0 < Nat.card N := Nat.card_pos
  have hgoal : Nat.card N * (168 * Nat.card ↥(⁅E, E⁆ ⊓ N)) = Nat.card N * Nat.card ↥⁅E, E⁆ := by
    rw [← mul_assoc, mul_comm (Nat.card N) 168]
    exact hprod
  exact (Nat.eq_of_mul_eq_mul_left hNne hgoal).symm

private lemma card_eq_factorization_of_isSylowIn {p : ℕ} [Fact p.Prime] {V P : Subgroup G}
    (hP : IsSylowIn p V P) : Nat.card P = p ^ (Nat.card V).factorization p := by
  obtain ⟨hPV, hPgrp, hPndvd⟩ := hP
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥P)).mp hPgrp
  have hcardV : Nat.card V = P.relIndex V * Nat.card P := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := V)
    rw [inf_eq_left.mpr hPV] at h
    exact h.symm
  have hrelne : P.relIndex V ≠ 0 := by
    rintro h0
    have hzero : Nat.card V = 0 := by rw [hcardV, h0, zero_mul]
    exact Nat.card_pos.ne' hzero
  have hPne : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card V).factorization p = n := by
    rw [hcardV, Nat.factorization_mul hrelne hPne, Finsupp.add_apply, hn,
      Nat.factorization_pow_self Fact.out, Nat.factorization_eq_zero_of_not_dvd hPndvd, zero_add]
  rw [hfac, hn]

private lemma gl3Pair_conj_mem {M L1 L2 : Subgroup G} (h : Gl3Pair M L1 L2) {y x : G}
    (hy : y ∈ L2) (hx : x ∈ L1) : y * x * y⁻¹ ∈ L1 := by
  have hc : ⁅y, x⁆ ∈ M := h.comm (by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hy hx)
  have hyx : y * x * y⁻¹ = ⁅y, x⁆ * x := by
    simpa using (conj_eq_commutatorElement_mul (g₁ := y) (g₂ := x))
  rw [hyx]
  exact L1.mul_mem (h.ext1.1 hc) hx

private lemma gl3Pair_L2_le_normalizer_L1 {M L1 L2 : Subgroup G} (h : Gl3Pair M L1 L2) :
    L2 ≤ normalizer (L1 : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => gl3Pair_conj_mem h hy hx, fun hx => by
    have h' := gl3Pair_conj_mem h (L2.inv_mem hy) hx
    simpa [mul_assoc] using h'⟩

theorem Gl3Pair.card_inf_sylow {M L1 L2 P : Subgroup G} (h : Gl3Pair M L1 L2)
    (hP : IsSylowIn 2 (L1 ⊔ L2) P) :
    M ≤ P ∧ Nat.card ↥(L1 ⊓ P) = 8 * Nat.card M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMgrp : IsPGroup 2 M := IsPGroup.of_card (n := 6) h.card
  have hKnorm : L1 ⊔ L2 ≤ Subgroup.normalizer (M : Set G) :=
    sup_le h.ext1.le_normalizer h.ext2.le_normalizer
  have hMleK : M ≤ L1 ⊔ L2 := h.ext1.1.trans le_sup_left
  have hMPgrp : IsPGroup 2 ↥(M ⊔ P) :=
    IsPGroup.to_sup_of_normal_left' hMgrp hP.2.1 (hP.1.trans hKnorm)
  have hPeq : P = M ⊔ P :=
    sylowIn_eq_of_le hP hMPgrp (sup_le hMleK hP.1) le_sup_right
  have hMleP : M ≤ P := by rw [hPeq]; exact le_sup_left
  have hKnormL1 : L1 ⊔ L2 ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (gl3Pair_L2_le_normalizer_L1 h)
  have hPc : Nat.card P = 2 ^ (Nat.card ↥(L1 ⊔ L2)).factorization 2 :=
    card_eq_factorization_of_isSylowIn hP
  have hcard := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_inf_sylow
    (p := 2) (N := L1) (H := L1 ⊔ L2) (P := P) hKnormL1 le_sup_left hP.1 hP.2.1 hPc
  have hfac : (Nat.card L1).factorization 2 = 9 := by
    have h1 : Nat.card L1 = 2 ^ 9 * 21 := by rw [h.ext1.card_eq, h.card]; norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21), add_zero]
  refine ⟨hMleP, ?_⟩
  rw [inf_comm, hcard, hfac, h.card]
  norm_num

theorem y7c_centIn_ne_bot {M D : Subgroup G} (hM : IsPGroup 2 M) (hMne : M ≠ ⊥)
    (hD : IsPGroup 2 D) (hDM : D ≤ normalizer (M : Set G)) : centIn M D ≠ ⊥ := by
  obtain ⟨n, hnM, hn1, hnc⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.exists_fixed_ne_one hD hDM hMne hM
  intro hbot
  have hmem : n ∈ centIn M D := by
    refine ⟨hnM, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hnc g hg
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hn1 hmem

theorem y7c_centIn_sup (M A B : Subgroup G) :
    centIn M (A ⊔ B) = centIn M A ⊓ centIn M B := by
  have hcent : Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_antisymm (le_inf
      (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_left hx)
      (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_right hx)) ?_
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mpr inf_le_left)
      (Subgroup.le_centralizer_iff.mpr inf_le_right)
  simp only [centIn]
  rw [hcent, inf_inf_distrib_left]

private lemma map_centralizer_conj (x : G) (S : Subgroup G) :
    (Subgroup.centralizer S).map (MulAut.conj x).toMonoidHom =
      Subgroup.centralizer (S.map (MulAut.conj x).toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Subgroup.coe_map, Set.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h := Subgroup.mem_centralizer_iff.mp hc t ht
    have h' := congrArg (MulAut.conj x) h
    simpa using h'
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conj x).symm y, ?_, (MulAut.conj x).apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hy' : MulAut.conj x s ∈ S.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hs
    have h := Subgroup.mem_centralizer_iff.mp hy _ hy'
    have h' := congrArg (MulAut.conj x).symm h
    simpa [MulAut.conj_symm_apply, mul_assoc] using h'

theorem y7c_centIn_conjSub {M D : Subgroup G} {x : G} (hx : conjSub x M = M) :
    centIn M (conjSub x D) = conjSub x (centIn M D) := by
  simp only [centIn, conjSub] at hx ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective, map_centralizer_conj, hx]

theorem y7c_conjSub_eq_of_mem_normalizer {M : Subgroup G} {x : G}
    (hx : x ∈ normalizer (M : Set G)) : conjSub x M = M := by
  ext g
  rw [conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact (Subgroup.mem_normalizer_iff''.mp hx g).symm

theorem y7c_card_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hB : B ≤ Subgroup.normalizer (A : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (A : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)
  have h := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_sup_mul_card_inf
    (A := A) (B := B) hB
  simpa [hAB] using h

theorem y7c_isElemAbelian_of_le {A B : Subgroup G} (hB : IsElemAbelian 2 B) (hAB : A ≤ B) :
    IsElemAbelian 2 A := by
  haveI := hB.1
  exact ⟨isMulCommutative_anti hAB, fun x hx => hB.2 x (hAB hx)⟩

end CFSG.OddStandard.HigherRank.YamadaG23
