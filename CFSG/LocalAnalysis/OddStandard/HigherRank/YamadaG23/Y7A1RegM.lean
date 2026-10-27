module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Reg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma map_pCore_conj_mem (Q : Subgroup (Equiv.Perm (Fin 16)))
    (q : Equiv.Perm (Fin 16)) (hq : q ∈ Q)
    {m : Equiv.Perm (Fin 16)} (hm : m ∈ (CFSG.pCore 2 ↥Q).map Q.subtype) :
    q * m * q⁻¹ ∈ (CFSG.pCore 2 ↥Q).map Q.subtype := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
  have hnorm : (CFSG.pCore 2 ↥Q).Normal := CFSG.pCore_normal
  have hinner : (⟨q, hq⟩ : ↥Q) * b * (⟨q, hq⟩ : ↥Q)⁻¹ ∈ CFSG.pCore 2 ↥Q :=
    hnorm.conj_mem b hb (⟨q, hq⟩ : ↥Q)
  simpa using Subgroup.mem_map_of_mem Q.subtype hinner

theorem y7a_reg16_max (Q : Subgroup (Equiv.Perm (Fin 16)))
    (htrans : ∀ i j : Fin 16, ∃ q ∈ Q, q i = j)
    (hcard : Nat.card Q = 288 ∨ Nat.card Q = 576)
    (hO2 : ∀ N : Subgroup (Equiv.Perm (Fin 16)),
      N ≤ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) →
      (∀ s ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
        ∀ m ∈ N, s * m * s⁻¹ ∈ N) →
      IsPGroup 2 N → N = ⊥) :
    ∃ P : Subgroup (Equiv.Perm (Fin 16)), P ≤ Q ∧ (∀ q ∈ Q, ∀ m ∈ P, q * m * q⁻¹ ∈ P) ∧
      IsPGroup 2 P ∧ Nat.card P = 16 ∧ (∀ i j : Fin 16, ∃ p ∈ P, p i = j) ∧
      ∀ N : Subgroup (Equiv.Perm (Fin 16)), N ≤ Q → (∀ q ∈ Q, ∀ m ∈ N, q * m * q⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ P := by
  let P : Subgroup (Equiv.Perm (Fin 16)) := (CFSG.pCore 2 ↥Q).map Q.subtype
  have hmax : ∀ N : Subgroup (Equiv.Perm (Fin 16)), N ≤ Q →
      (∀ q ∈ Q, ∀ m ∈ N, q * m * q⁻¹ ∈ N) → IsPGroup 2 N → N ≤ P := by
    intro N hNQ hNconj hNP
    have hNnorm : (N.subgroupOf Q).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hNQ]
      intro h k hh hk
      exact hNconj k hk h hh
    have hNpg : IsPGroup 2 (N.subgroupOf Q) := hNP.comap_subtype
    have hle : N.subgroupOf Q ≤ CFSG.pCore 2 ↥Q := by
      rw [CFSG.pCore]
      exact le_sSup ⟨hNnorm, hNpg⟩
    calc N = (N.subgroupOf Q).map Q.subtype := (Subgroup.map_subgroupOf_eq_of_le hNQ).symm
      _ ≤ (CFSG.pCore 2 ↥Q).map Q.subtype := Subgroup.map_mono hle
  obtain ⟨P0, hP0le, hP0conj, hP0pg, hP0card, _⟩ := y7a_reg16 Q htrans hcard hO2
  have hP0leP : P0 ≤ P := hmax P0 hP0le hP0conj hP0pg
  have hInfBot : P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) = ⊥ := by
    apply hO2
    · exact le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) inf_le_right
    · intro s hs m hm
      refine ⟨map_pCore_conj_mem Q s hs.1 hm.1, ?_⟩
      exact (MulAction.stabilizer (Equiv.Perm (Fin 16)) 0).mul_mem
        ((MulAction.stabilizer (Equiv.Perm (Fin 16)) 0).mul_mem hs.2 hm.2)
        ((MulAction.stabilizer (Equiv.Perm (Fin 16)) 0).inv_mem hs.2)
    · exact (IsPGroup.map CFSG.pCore_isPGroup Q.subtype).to_le inf_le_left
  have hker : ∀ x : ↥(CFSG.pCore 2 ↥Q), (x : Equiv.Perm (Fin 16)) 0 = 0 → x = 1 := by
    intro x hx
    have hxmem : (x : Equiv.Perm (Fin 16)) ∈ P := Subgroup.mem_map_of_mem Q.subtype x.2
    have hxstab : (x : Equiv.Perm (Fin 16)) ∈
        MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) := by
      rw [MulAction.mem_stabilizer_iff]
      exact hx
    have hxbot : (x : Equiv.Perm (Fin 16)) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 16))) := by
      rw [← hInfBot]
      exact ⟨hxmem, hxstab⟩
    exact Subtype.ext (by simpa using hxbot)
  have hinj : Function.Injective
      (fun x : ↥(CFSG.pCore 2 ↥Q) => (x : Equiv.Perm (Fin 16)) 0) := by
    intro a b hab
    have h0 : ((a⁻¹ * b : ↥(CFSG.pCore 2 ↥Q)) : Equiv.Perm (Fin 16)) 0 = 0 := by
      have hcoex : ((a⁻¹ * b : ↥(CFSG.pCore 2 ↥Q)) : Equiv.Perm (Fin 16)) =
          (a : Equiv.Perm (Fin 16))⁻¹ * (b : Equiv.Perm (Fin 16)) := by simp
      rw [hcoex]
      change (a : Equiv.Perm (Fin 16))⁻¹ ((b : Equiv.Perm (Fin 16)) 0) = 0
      have hab' : (a : Equiv.Perm (Fin 16)) 0 = (b : Equiv.Perm (Fin 16)) 0 := hab
      rw [← hab']
      simp
    exact inv_mul_eq_one.mp (hker (a⁻¹ * b) h0)
  have hcardPsub_le16 : Nat.card ↥(CFSG.pCore 2 ↥Q) ≤ 16 := by
    have := Nat.card_le_card_of_injective
      (fun x : ↥(CFSG.pCore 2 ↥Q) => (x : Equiv.Perm (Fin 16)) 0) hinj
    simpa [Nat.card_fin] using this
  have hP0suble : P0.subgroupOf Q ≤ CFSG.pCore 2 ↥Q := by
    intro x hx
    obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp (hP0leP hx)
    have hbx : b = x := Q.subtype_injective hbval
    simpa [hbx] using hb
  have hcardP0sub_le : Nat.card ↥(P0.subgroupOf Q) ≤ Nat.card ↥(CFSG.pCore 2 ↥Q) :=
    Nat.card_le_card_of_injective
      (fun x : ↥(P0.subgroupOf Q) =>
        (⟨(x : ↥Q), hP0suble x.2⟩ : ↥(CFSG.pCore 2 ↥Q)))
      (by
        intro a b hab
        exact Subtype.ext (congrArg (fun z : ↥(CFSG.pCore 2 ↥Q) => (z : ↥Q)) hab))
  have hcardP0eq : Nat.card ↥(P0.subgroupOf Q) = Nat.card P0 := by
    have h := Subgroup.card_map_of_injective
      (K := P0.subgroupOf Q) (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hP0le] at h
    exact h.symm
  have h16le : 16 ≤ Nat.card ↥(CFSG.pCore 2 ↥Q) := by
    have hcardP0le : Nat.card P0 ≤ Nat.card ↥(CFSG.pCore 2 ↥Q) := hcardP0eq ▸ hcardP0sub_le
    rwa [hP0card] at hcardP0le
  have hcardPsub : Nat.card ↥(CFSG.pCore 2 ↥Q) = 16 := le_antisymm hcardPsub_le16 h16le
  have hcardP : Nat.card P = 16 := by
    change Nat.card ((CFSG.pCore 2 ↥Q).map Q.subtype) = 16
    rw [Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective, hcardPsub]
  have htransP : ∀ i j : Fin 16, ∃ p ∈ P, p i = j := by
    have hbij : Function.Bijective
        (fun x : ↥(CFSG.pCore 2 ↥Q) => (x : Equiv.Perm (Fin 16)) 0) :=
      hinj.bijective_of_nat_card_le (by rw [hcardPsub]; simp)
    intro i j
    obtain ⟨a, ha⟩ := hbij.surjective i
    obtain ⟨b, hb⟩ := hbij.surjective j
    refine ⟨(b : Equiv.Perm (Fin 16)) * (a : Equiv.Perm (Fin 16))⁻¹, ?_, ?_⟩
    · exact P.mul_mem (Subgroup.mem_map_of_mem Q.subtype b.2)
        (P.inv_mem (Subgroup.mem_map_of_mem Q.subtype a.2))
    · have hai : (a : Equiv.Perm (Fin 16))⁻¹ i = 0 := by
        rw [← ha]
        simp
      change (b : Equiv.Perm (Fin 16)) ((a : Equiv.Perm (Fin 16))⁻¹ i) = j
      rw [hai]
      exact hb
  exact ⟨P, Subgroup.map_subtype_le _, (fun q hq m hm => map_pCore_conj_mem Q q hq hm),
    IsPGroup.map CFSG.pCore_isPGroup Q.subtype, hcardP, htransP, hmax⟩

end CFSG.OddStandard.HigherRank.YamadaG23
