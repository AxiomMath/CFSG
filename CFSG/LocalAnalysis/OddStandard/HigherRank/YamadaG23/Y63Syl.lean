module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Concl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y63_sylow_of_normalizer_le {B Q : Subgroup G}
    (hQ : IsSylowIn 2 (normalizer (B : Set G)) Q)
    (hN : normalizer (Q : Set G) ≤ normalizer (B : Set G)) : IsSylowIn 2 ⊤ Q := by
  refine ⟨le_top, hQ.2.1, ?_⟩
  obtain ⟨P, hQP⟩ := hQ.2.1.exists_le_sylow
  have hEq : Q = (P : Subgroup G) := by
    by_contra hne
    let Pg : Subgroup G := (P : Subgroup G)
    let H : Subgroup ↥Pg := Q.subgroupOf Pg
    have hQPg : Q ≤ Pg := hQP
    have hHne : H ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm hQPg ?_
      intro y hy
      have hyH : (⟨y, hy⟩ : ↥Pg) ∈ H := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp hyH
    have hHlt : H < ⊤ := lt_of_le_of_ne le_top hHne
    haveI : Group.IsNilpotent ↥Pg := P.isPGroup'.isNilpotent
    have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥Pg)
    obtain ⟨x, hx_norm, hx_not⟩ := SetLike.exists_of_lt (hNC H hHlt)
    have hxG_norm : (x : G) ∈ normalizer (Q : Set G) := by
      have h1 : (x : ↥Pg) ∈ (normalizer (Q : Set G)).subgroupOf Pg := by
        rw [Subgroup.subgroupOf_normalizer_eq hQPg]
        exact hx_norm
      exact Subgroup.mem_subgroupOf.mp h1
    have hxG_not : (x : G) ∉ Q := fun h => hx_not (Subgroup.mem_subgroupOf.mpr h)
    have hxG_NB : (x : G) ∈ normalizer (B : Set G) := hN hxG_norm
    let Q' : Subgroup G := Q ⊔ Subgroup.zpowers (x : G)
    have hQ'P : Q' ≤ Pg := sup_le hQPg (Subgroup.zpowers_le.mpr x.2)
    have hQ'NB : Q' ≤ normalizer (B : Set G) :=
      sup_le hQ.1 (Subgroup.zpowers_le.mpr hxG_NB)
    have hQ'2 : IsPGroup 2 ↥Q' := P.isPGroup'.to_le hQ'P
    have hxQ' : (x : G) ∈ Q' := Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
    have hQneQ' : Q ≠ Q' := by
      intro heq
      have hxQ : (x : G) ∈ Q := by
        have h := hxQ'
        rw [← heq] at h
        exact h
      exact hxG_not hxQ
    have h2dvd : 2 ∣ Q.relIndex Q' := by
      obtain ⟨k, hk⟩ := hQ'2.index (Q.subgroupOf Q')
      change 2 ∣ (Q.subgroupOf Q').index
      have hk0 : k ≠ 0 := by
        intro h0
        have htop : Q.subgroupOf Q' = ⊤ :=
          Subgroup.index_eq_one.mp (by rw [hk, h0, pow_zero])
        apply hQneQ'
        refine le_antisymm le_sup_left ?_
        intro y hy
        have hyH : (⟨y, hy⟩ : ↥Q') ∈ Q.subgroupOf Q' := by rw [htop]; trivial
        exact Subgroup.mem_subgroupOf.mp hyH
      rw [hk]
      exact dvd_pow_self 2 hk0
    have hdvd : Q.relIndex Q' ∣ Q.relIndex (normalizer (B : Set G)) :=
      ⟨Q'.relIndex (normalizer (B : Set G)),
        (Subgroup.relIndex_mul_relIndex (H := Q) (K := Q') (L := normalizer (B : Set G))
          le_sup_left hQ'NB).symm⟩
    exact hQ.2.2 (h2dvd.trans hdvd)
  rw [hEq, Subgroup.relIndex_top_right]
  exact P.not_dvd_index

theorem y63_sylow_of_le {K Q : Subgroup G} (hQ : IsSylowIn 2 ⊤ Q) (hQK : Q ≤ K) :
    IsSylowIn 2 K Q := by
  refine ⟨hQK, hQ.2.1, ?_⟩
  intro h2
  apply hQ.2.2
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hQK]
  exact dvd_mul_of_dvd_left h2 K.index

theorem y63_mem_normalizer_of_conjSub_eq {Y : Subgroup G} {n : G} (h : conjSub n Y = Y) :
    n ∈ normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : n * y * n⁻¹ ∈ conjSub n Y := Sec1Proof.mem_conjSub.mpr ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', h'⟩ := Sec1Proof.mem_conjSub.mp hy
    have hyy : y' = y := by
      refine (MulAut.conj n).injective ?_
      rw [MulAut.conj_apply, MulAut.conj_apply]
      exact h'
    exact hyy ▸ hy'

theorem y63_ZE64_conj {Z U : Subgroup G} (h : Y63ZE64 Z U) {n : G}
    (hn : ∀ z ∈ Z, n * z * n⁻¹ = z) : Y63ZE64 Z (conjSub n U) := by
  rw [Y63ZE64] at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact Sec1Proof.mem_conjSub.mpr ⟨z, h.1 hz, hn z hz⟩
  · change Nat.card ↥(U.map (MulAut.conj n).toMonoidHom) = 2 ^ 7
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact h.2.1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Sec1Proof.mem_conjSub.mp hx
    rw [show (n * y * n⁻¹) ^ 2 = n * y ^ 2 * n⁻¹ by
      rw [show n * y * n⁻¹ = MulAut.conj n y by rw [MulAut.conj_apply],
        ← map_pow (MulAut.conj n) y 2, MulAut.conj_apply],
      hn (y ^ 2) (h.2.2.1 y hy)]
    exact h.2.2.1 y hy
  · have hfixZ : Z.map (MulAut.conj n).toMonoidHom ≤ Z := by
      rintro x ⟨z, hz, rfl⟩
      have hz' : (MulAut.conj n).toMonoidHom z = z := by
        change MulAut.conj n z = z
        rw [MulAut.conj_apply]
        exact hn z hz
      rwa [hz']
    calc ⁅conjSub n U, conjSub n U⁆
        = (⁅U, U⁆).map (MulAut.conj n).toMonoidHom := by
          rw [conjSub]
          exact (Subgroup.map_commutator (f := (MulAut.conj n).toMonoidHom) U U).symm
      _ ≤ Z.map (MulAut.conj n).toMonoidHom := Subgroup.map_mono h.2.2.2
      _ ≤ Z := hfixZ

theorem y63_normalizer_le (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hY : Y63Hyps c)
    (hC : Y63Concl c) : normalizer (y63Q c : Set G) ≤ normalizer (C1 c.e : Set G) := by
  intro n hn
  have hzCen : c.s.fr.z ∈ cen (y63Q c) := by
    rw [hC.cen_eq]
    exact Subgroup.mem_zpowers c.s.fr.z
  have hzQ : c.s.fr.z ∈ y63Q c := (Subgroup.mem_inf.mp hzCen).1
  have hzC : c.s.fr.z ∈ centralizer (y63Q c : Set G) := (Subgroup.mem_inf.mp hzCen).2
  have hzord : orderOf c.s.fr.z = 2 :=
    s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  have hz2 : c.s.fr.z * c.s.fr.z = 1 := by
    have h := pow_orderOf_eq_one c.s.fr.z
    rw [hzord] at h
    simpa [pow_two] using h
  have hz_ne : c.s.fr.z ≠ 1 := y54_z_ne_one (c := c.toCtx5) hH
  have hnzC : n * c.s.fr.z * n⁻¹ ∈ centralizer (y63Q c : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : n⁻¹ * q * n ∈ y63Q c := by
      have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      simpa using h
    have hzc := (Subgroup.mem_centralizer_iff.mp hzC) (n⁻¹ * q * n) hq'
    calc q * (n * c.s.fr.z * n⁻¹)
        = n * ((n⁻¹ * q * n) * c.s.fr.z) * n⁻¹ := by group
      _ = n * (c.s.fr.z * (n⁻¹ * q * n)) * n⁻¹ := by rw [hzc]
      _ = (n * c.s.fr.z * n⁻¹) * q := by group
  have hnzQ : n * c.s.fr.z * n⁻¹ ∈ y63Q c :=
    (Subgroup.mem_normalizer_iff.mp hn c.s.fr.z).mp hzQ
  have hnz : n * c.s.fr.z * n⁻¹ = c.s.fr.z := by
    have hmem : n * c.s.fr.z * n⁻¹ ∈ Subgroup.zpowers c.s.fr.z := by
      rw [← hC.cen_eq]
      exact Subgroup.mem_inf.mpr ⟨hnzQ, hnzC⟩
    rcases Sec1Proof.zpowers_eq_one_or_self hz_ne hz2 hmem with h1 | hz
    · exfalso
      have hz1 : c.s.fr.z = 1 := by
        calc c.s.fr.z = n⁻¹ * (n * c.s.fr.z * n⁻¹) * n := by group
          _ = n⁻¹ * 1 * n := by rw [h1]
          _ = 1 := by group
      exact hz_ne hz1
    · exact hz
  have hfix : ∀ w ∈ Subgroup.zpowers c.s.fr.z, n * w * n⁻¹ = w := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    calc n * c.s.fr.z ^ k * n⁻¹ = MulAut.conj n (c.s.fr.z ^ k) := by
          rw [MulAut.conj_apply]
      _ = (MulAut.conj n c.s.fr.z) ^ k := map_zpow (MulAut.conj n) c.s.fr.z k
      _ = c.s.fr.z ^ k := by
          rw [show MulAut.conj n c.s.fr.z = c.s.fr.z by
            rw [MulAut.conj_apply]; exact hnz]
  have hconj_le : conjSub n (C1 c.e) ≤ y63Q c := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Sec1Proof.mem_conjSub.mp hx
    exact (Subgroup.mem_normalizer_iff.mp hn u).mp (y63_C1_le_Q c hH hu)
  have hZE : Y63ZE64 (Subgroup.zpowers c.s.fr.z) (conjSub n (C1 c.e)) :=
    y63_ZE64_conj (y63_C1_ZE64 c hH) hfix
  exact y63_mem_normalizer_of_conjSub_eq (hC.uniq _ hconj_le hZE)

theorem y63_sylow (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hY : Y63Hyps c) (h61 : c.Fact61)
    (hC : Y63Concl c) : IsSylowIn 2 ⊤ (y63Q c) :=
  y63_sylow_of_normalizer_le h61.2.2.2.2.2.2 (y63_normalizer_le c hH hY hC)

end CFSG.OddStandard.HigherRank.YamadaG23
