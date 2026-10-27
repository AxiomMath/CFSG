module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Reg9
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegO3
public import CFSG.ClassicalInvolution.Q3.TwinLemmaBasic
public import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma conjNormal_eq_one_iff {Y : Type*} [Group Y] {H : Subgroup Y} [H.Normal] (g : Y) :
    MulAut.conjNormal (H := H) g = 1 ↔ ∀ h : H, g * (h : Y) * g⁻¹ = (h : Y) := by
  constructor
  · intro hg h
    have := congrArg (fun f : MulAut H => ((f h : H) : Y)) hg
    simpa using this
  · intro hg
    ext h
    simpa using hg h

private lemma map_pCore_conj_mem (Q : Subgroup (Equiv.Perm (Fin 16)))
    (q : Equiv.Perm (Fin 16)) (hq : q ∈ Q)
    {m : Equiv.Perm (Fin 16)} (hm : m ∈ (CFSG.pCore 2 ↥Q).map Q.subtype) :
    q * m * q⁻¹ ∈ (CFSG.pCore 2 ↥Q).map Q.subtype := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
  have hnorm : (CFSG.pCore 2 ↥Q).Normal := CFSG.pCore_normal
  have hinner : (⟨q, hq⟩ : ↥Q) * b * (⟨q, hq⟩ : ↥Q)⁻¹ ∈ CFSG.pCore 2 ↥Q :=
    hnorm.conj_mem b hb (⟨q, hq⟩ : ↥Q)
  simpa using Subgroup.mem_map_of_mem Q.subtype hinner

theorem y7a_reg16 (Q : Subgroup (Equiv.Perm (Fin 16)))
    (htrans : ∀ i j : Fin 16, ∃ q ∈ Q, q i = j)
    (hcard : Nat.card Q = 288 ∨ Nat.card Q = 576)
    (hO2 : ∀ N : Subgroup (Equiv.Perm (Fin 16)),
      N ≤ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) →
      (∀ s ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
        ∀ m ∈ N, s * m * s⁻¹ ∈ N) →
      IsPGroup 2 N → N = ⊥) :
    ∃ P : Subgroup (Equiv.Perm (Fin 16)), P ≤ Q ∧ (∀ q ∈ Q, ∀ m ∈ P, q * m * q⁻¹ ∈ P) ∧
      IsPGroup 2 P ∧ Nat.card P = 16 ∧ ∀ i j : Fin 16, ∃ p ∈ P, p i = j := by
  let P : Subgroup (Equiv.Perm (Fin 16)) := (CFSG.pCore 2 ↥Q).map Q.subtype
  have hcardY : Nat.card ↥Q = 288 ∨ Nat.card ↥Q = 576 := hcard
  have hsolv : Group.IsSolvable ↥Q := by
    rcases hcardY with h | h
    · exact TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
        (a := 5) (b := 2) Nat.prime_two Nat.prime_three (by rw [h]; norm_num)
    · exact TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
        (a := 6) (b := 2) Nat.prime_two Nat.prime_three (by rw [h]; norm_num)
  have hO : ∀ N : Subgroup ↥Q, N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hNnorm hodd
    have hdvd : Nat.card N ∣ Nat.card ↥Q := Subgroup.card_subgroup_dvd_card N
    have h9 : Nat.card N ∣ 3 ^ 2 := by
      have hcop2 : Nat.Coprime (Nat.card N) 2 := hodd.coprime_two_right
      rcases hcardY with h | h
      · rw [h] at hdvd
        rw [show (288 : ℕ) = 2 ^ 5 * 3 ^ 2 by norm_num] at hdvd
        have hc : Nat.Coprime (Nat.card N) (2 ^ 5) :=
          (Nat.coprime_pow_right_iff (by norm_num) (Nat.card N) 2).mpr hcop2
        exact hc.dvd_mul_left.mp hdvd
      · rw [h] at hdvd
        rw [show (576 : ℕ) = 2 ^ 6 * 3 ^ 2 by norm_num] at hdvd
        have hc : Nat.Coprime (Nat.card N) (2 ^ 6) :=
          (Nat.coprime_pow_right_iff (by norm_num) (Nat.card N) 2).mpr hcop2
        exact hc.dvd_mul_left.mp hdvd
    have hP3 : IsPGroup 3 N := IsPGroup.of_card_dvd_pow (n := 2) h9
    have hmap3 : IsPGroup 3 (N.map Q.subtype) := hP3.map Q.subtype
    have hle : N.map Q.subtype ≤ Q := Subgroup.map_subtype_le N
    have hnorm : ∀ q ∈ Q, ∀ m ∈ N.map Q.subtype, q * m * q⁻¹ ∈ N.map Q.subtype := by
      intro q hq m hm
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
      have hinner : (⟨q, hq⟩ : ↥Q) * b * (⟨q, hq⟩ : ↥Q)⁻¹ ∈ N :=
        hNnorm.conj_mem b hb (⟨q, hq⟩ : ↥Q)
      simpa using Subgroup.mem_map_of_mem Q.subtype hinner
    have hbot := y7a_normal_pgroup_trivial (n := 16) (p := 3) (by decide) Q
      (N.map Q.subtype) hle hnorm htrans hmap3
    exact (Subgroup.map_eq_bot_iff_of_injective N Q.subtype_injective).mp hbot
  have hC : Subgroup.centralizer (CFSG.pCore 2 ↥Q : Set ↥Q) ≤ CFSG.pCore 2 ↥Q :=
    CFSG.ClassicalInvolution.Q3.Twin.centralizer_pCore_le hsolv hO
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
  let Q3 : Sylow 3 ↥Q := Classical.choice (inferInstance : Nonempty (Sylow 3 ↥Q))
  have hcardQ3 : Nat.card Q3 = 9 := by
    rw [Sylow.card_eq_multiplicity Q3]
    rcases hcardY with h | h <;> rw [h] <;> decide +kernel
  let S3 : Subgroup ↥Q := Q3
  have hcardS3 : Nat.card ↥S3 = 9 := by simpa using hcardQ3
  have hS3bot : S3 ⊓ CFSG.pCore 2 ↥Q = ⊥ := by
    have hdisj : Disjoint S3 (CFSG.pCore 2 ↥Q) :=
      IsPGroup.disjoint_of_coprime Q3.isPGroup' CFSG.pCore_isPGroup (by decide)
    exact disjoint_iff.mp hdisj
  let φ : ↥S3 →* MulAut ↥(CFSG.pCore 2 ↥Q) :=
    (MulAut.conjNormal (H := CFSG.pCore 2 ↥Q)).comp S3.subtype
  have hφ : Function.Injective φ := by
    intro a b hab
    let x : ↥Q := ((a⁻¹ * b : ↥S3) : ↥Q)
    have hconj : (MulAut.conjNormal (H := CFSG.pCore 2 ↥Q)) x = 1 := by
      have h2 : φ (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      simpa [φ, x] using h2
    have hcent : x ∈ Subgroup.centralizer (CFSG.pCore 2 ↥Q : Set ↥Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : x * h * x⁻¹ = h := by
        have := (conjNormal_eq_one_iff (H := CFSG.pCore 2 ↥Q) x).mp hconj ⟨h, hh⟩
        simpa using this
      calc h * x = (x * h * x⁻¹) * x := by rw [hh']
        _ = x * h := by group
    have hmemP : x ∈ CFSG.pCore 2 ↥Q := hC hcent
    have hmemS3 : x ∈ S3 := by
      change ((a⁻¹ * b : ↥S3) : ↥Q) ∈ S3
      exact (a⁻¹ * b).2
    have hx1 : x = 1 := by
      have hbot : x ∈ (⊥ : Subgroup ↥Q) := by
        rw [← hS3bot]
        exact ⟨hmemS3, hmemP⟩
      simpa using hbot
    exact inv_mul_eq_one.mp (Subtype.ext (by simpa [x] using hx1))
  have hcardPsub_gt8 : 8 < Nat.card ↥(CFSG.pCore 2 ↥Q) := by
    by_contra hle
    exact y7a_no_order9_small (P := ↥(CFSG.pCore 2 ↥Q)) (Q := ↥S3)
      CFSG.pCore_isPGroup (le_of_not_gt hle) hcardS3 φ hφ
  have hcardPsub : Nat.card ↥(CFSG.pCore 2 ↥Q) = 16 := by
    have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥Q) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hkgt : 3 < k := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp
      (by rw [← hk]; simpa using hcardPsub_gt8)
    have hkle : k ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp
      (by rw [← hk]; simpa using hcardPsub_le16)
    have hk4 : k = 4 := le_antisymm hkle (Nat.succ_le_of_lt hkgt)
    rw [hk, hk4]
    norm_num
  refine ⟨P, Subgroup.map_subtype_le _, ?_, IsPGroup.map CFSG.pCore_isPGroup Q.subtype, ?_, ?_⟩
  · intro q hq m hm
    exact map_pCore_conj_mem Q q hq hm
  · change Nat.card ((CFSG.pCore 2 ↥Q).map Q.subtype) = 16
    rw [Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective]
    exact hcardPsub
  · intro i j
    have hbij : Function.Bijective
        (fun x : ↥(CFSG.pCore 2 ↥Q) => (x : Equiv.Perm (Fin 16)) 0) :=
      hinj.bijective_of_nat_card_le (by rw [hcardPsub]; simp)
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

end CFSG.OddStandard.HigherRank.YamadaG23
