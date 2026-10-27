module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PerfectCover
open groupHomology
open scoped commutatorElement

section Multiplier

@[expose] def M22CoverCyclic : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Group.IsPerfect K →
    ∀ p : K →* NativeSporadic.Carrier .M22, Function.Surjective p →
      p.ker ≤ Subgroup.center K → IsElemAbelian 2 p.ker → Nat.card p.ker ≤ 2

theorem isPerfect_carrier_m22
    : Group.IsPerfect (NativeSporadic.Carrier .M22) := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  rw [Group.isPerfect_def]
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (NativeSporadic.Carrier .M22)) with h | h
  · exfalso
    have hc : ∀ a b : NativeSporadic.Carrier .M22, a * b = b * a := fun a b => by
      have h1 : ⁅a, b⁆ ∈ commutator (NativeSporadic.Carrier .M22) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    let _ : CommGroup (NativeSporadic.Carrier .M22) :=
      { (inferInstance : Group (NativeSporadic.Carrier .M22)) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Carrier .M22)
    have hcard : Nat.card (NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    rw [hcard] at hp
    norm_num at hp
  · exact h

end Multiplier

section Count

variable {G : Type} [Group G] [Finite G]

theorem false_of_m22_cover
    (hcyc : M22CoverCyclic) {K U Z : Subgroup G} {N : Subgroup ↥K} [N.Normal]
    {n : ℕ} (hn : 1 < n) [hperf : Group.IsPerfect ↥K]
    (e : (↥K ⧸ N) ≃* NativeSporadic.Carrier .M22) (hNc : N ≤ Subgroup.center ↥K) (hUK : U ≤ K)
    (hUel : IsElemAbelian 2 U) (hUcard : Nat.card U = 2 ^ (3 * n)) (hZU : Z ≤ U)
    (hZel : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ n)
    (hNZ : ∀ k : ↥K, k ∈ N → (k : G) ∈ Z) : False := by
  classical
  set p : ↥K →* NativeSporadic.Carrier .M22 := e.toMonoidHom.comp (QuotientGroup.mk' N) with hp
  have hpsurj : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : p.ker = N := by
    ext k
    simp [hp]
  have hNel : IsElemAbelian 2 N :=
    ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hNc a.2) b).symm)⟩⟩,
      fun x hx => Subtype.ext (hZel.2 _ (hNZ x hx))⟩
  have hN2 : Nat.card N ≤ 2 := by
    have := hcyc ↥K hperf p hpsurj (hker ▸ hNc) (hker ▸ hNel)
    rwa [hker] at this
  set UK : Subgroup ↥K := U.subgroupOf K with hUKdef
  have hmemUK : ∀ k : ↥K, k ∈ UK ↔ (k : G) ∈ U := fun k => Subgroup.mem_subgroupOf
  have hcardUK : Nat.card UK = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
  set B : Subgroup (NativeSporadic.Carrier .M22) := UK.map p with hB
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact IsElemAbelian.comm hUel ((hmemUK a).1 ha) ((hmemUK b).1 hb)
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hUel.2 _ ((hmemUK a).1 ha))
    rw [this, map_one]
  have hBcard : Nat.card B ≤ 2 ^ 4 := CFSG.QuasithinUnique.Setup.X1.m22_rank_le B hBcomm hBsq
  have hkerUK : p.ker ≤ UK := by
    rw [hker]
    intro k hk
    exact (hmemUK k).2 (hZU (hNZ k hk))
  have hcardU : Nat.card U = Nat.card N * Nat.card B := by
    have h1 := Subgroup.card_mul_index (p.ker.subgroupOf UK)
    have h2 : (p.ker.subgroupOf UK).index = Nat.card B := Subgroup.relIndex_ker UK p
    have h3 : Nat.card (p.ker.subgroupOf UK) = Nat.card p.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerUK).toEquiv
    rw [h2, h3, hker] at h1
    rw [← hcardUK, ← h1]
  have hNcard : Nat.card N ≤ 2 ^ n := by
    have hZK : Z ≤ K := hZU.trans hUK
    have hNZ' : N ≤ Z.subgroupOf K := fun k hk => Subgroup.mem_subgroupOf.2 (hNZ k hk)
    have := Subgroup.card_le_of_le hNZ'
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZcard] at this
  have hle : 2 ^ (3 * n) ≤ 2 ^ (n + 4) := by
    calc 2 ^ (3 * n) = Nat.card N * Nat.card B := hUcard ▸ hcardU
      _ ≤ 2 ^ n * 2 ^ 4 := Nat.mul_le_mul hNcard hBcard
      _ = 2 ^ (n + 4) := (pow_add 2 n 4).symm
  have hn2 : n = 2 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
    omega
  subst hn2
  have hN4 : Nat.card N = 4 := by
    have h1 : 64 ≤ Nat.card N * 16 := by
      have : Nat.card N * Nat.card B ≤ Nat.card N * 16 := Nat.mul_le_mul le_rfl hBcard
      calc 64 = 2 ^ (3 * 2) := by norm_num
        _ = Nat.card N * Nat.card B := hUcard ▸ hcardU
        _ ≤ Nat.card N * 16 := this
    omega
  omega

end Count

end CFSG.QuasithinUnique.Lin2
