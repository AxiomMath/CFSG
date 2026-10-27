module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem lit_two_mem_of_central [Finite G] {A C : Subgroup G} (hAC : A ≤ C)
    (hcent : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hA : IsPGroup 2 A)
    (hidx : ¬ 2 ∣ A.relIndex C) {c : G} (hc : c ∈ C) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c ∈ A := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let A' : Subgroup ↥C := A.subgroupOf C
  have hA' : IsPGroup 2 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  haveI hA'norm : A'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hcent (n : G) hn (g : G) g.2
    have hgoal : ((g * n * g⁻¹ : ↥C) : G) = (n : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← h]
      group
    rwa [hgoal]⟩
  have hidx' : ¬ 2 ∣ A'.index := by simpa [A', Subgroup.relIndex] using hidx
  let S : Sylow 2 ↥C := hA'.toSylow hidx'
  let c' : ↥C := ⟨c, hc⟩
  have hc' : c' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using hk
  have hzp : IsPGroup 2 (Subgroup.zpowers c') :=
    IsPGroup.of_card_dvd_pow (by
      rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
      exact hc')
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hScoeeq : (S : Subgroup ↥C) = A' := IsPGroup.toSylow_coe hA' hidx'
  have hA'leQ : A' ≤ (Q : Subgroup ↥C) := IsPGroup.le_sylow_of_normal hA' Q
  have hQeq : (Q : Subgroup ↥C) = A' := by
    have h := S.is_maximal' Q.isPGroup' (by rw [hScoeeq]; exact hA'leQ)
    rwa [hScoeeq] at h
  have hcQ : c' ∈ (Q : Subgroup ↥C) := hQ (Subgroup.mem_zpowers c')
  have : c' ∈ A' := hQeq ▸ hcQ
  exact Subgroup.mem_subgroupOf.mp this

theorem lit_inf_ne_bot_of_sylow [Finite G] {M U L : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 2 U)
    (hidx : ¬ 2 ∣ U.relIndex M) (hLM : L ≤ M) (hL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLeven : Even (Nat.card L)) : U ⊓ L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Finite (Sylow 2 ↥M) := by
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥M))
    exact Sylow.finite_of_finiteIndex P
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (even_iff_two_dvd.mp hLeven)
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  let x' : ↥M := ⟨(x : G), hLM x.2⟩
  have hx' : orderOf x' = 2 := by
    rw [← Subgroup.orderOf_coe x']
    exact hxG
  have hx'1 : x' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx'
    omega
  have hzp : IsPGroup 2 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx']; norm_num)
  have hU' : IsPGroup 2 (U.subgroupOf M) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
  have hidx' : ¬ 2 ∣ (U.subgroupOf M).index := by simpa [Subgroup.relIndex] using hidx
  let S : Sylow 2 ↥M := hU'.toSylow hidx'
  have hScoe : (S : Subgroup ↥M) = U.subgroupOf M := IsPGroup.toSylow_coe hU' hidx'
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) S Q
  have hxmemQ : x' ∈ (Q : Subgroup ↥M) := hQ (Subgroup.mem_zpowers x')
  have hxmemQS : x' ∈ MulAut.conj m • (S : Subgroup ↥M) := by
    have h1 : x' ∈ (m • S : Sylow 2 ↥M) := by rw [hm]; exact hxmemQ
    exact h1
  let y : ↥M := m⁻¹ * x' * m
  have hyS : y ∈ (S : Subgroup ↥M) := by
    have h2 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hxmemQS
    simpa only [y, MulAut.smul_def, MulAut.conj_inv_apply] using h2
  have hyU : (y : G) ∈ U :=
    Subgroup.mem_subgroupOf.mp (by rw [← hScoe]; exact hyS)
  have hyL : (y : G) ∈ L := by
    have h := hL (m : G)⁻¹ (M.inv_mem m.2) (x : G) x.2
    simpa only [y, x', Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h
  have hy1 : (y : G) ≠ 1 := by
    intro h
    apply hx'1
    have hy : y = 1 := Subtype.ext h
    have hxeq : x' = m * y * m⁻¹ := by
      simp only [y]
      group
    rw [hxeq, hy]
    simp
  intro hbot
  have hy : (y : G) ∈ U ⊓ L := ⟨hyU, hyL⟩
  rw [hbot, Subgroup.mem_bot] at hy
  exact hy1 hy

theorem lit_normal_inf_center [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ z ∈ N, z ≠ 1 ∧ ∀ t ∈ T, z * t = t * z := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  haveI hNnorm : (N.subgroupOf T).Normal := ⟨fun n hn t => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN (t : G) t.2 (n : G) hn⟩
  have hne' : N.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro n hn
    have hmem : (⟨n, hNT hn⟩ : ↥T) ∈ N.subgroupOf T := hn
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext_iff.mp hmem
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥T) (H := N.subgroupOf T) hne')
  refine ⟨((z : ↥T) : G), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp z.2.1
  · intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  · intro t ht
    have hz := Subgroup.mem_center_iff.mp z.2.2 (⟨t, ht⟩ : ↥T)
    simpa using congrArg Subtype.val hz.symm

theorem lit_inf_normal_sylow [Finite G] (T : Sylow 2 G) (M : Subgroup G) [M.Normal] :
    IsPGroup 2 (M ⊓ (T : Subgroup G) : Subgroup G) ∧
      ¬ 2 ∣ (M ⊓ (T : Subgroup G)).relIndex M := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Finite (Sylow 2 G) := by
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
    exact Sylow.finite_of_finiteIndex P
  haveI : Finite (Sylow 2 ↥M) := by
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥M))
    exact Sylow.finite_of_finiteIndex P
  let N : Subgroup G := M ⊓ (T : Subgroup G)
  refine ⟨T.isPGroup'.to_inf_right, ?_⟩
  change ¬ 2 ∣ N.relIndex M
  have hNmP : IsPGroup 2 (N.subgroupOf M) :=
    (T.isPGroup'.to_inf_right).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ M)).symm
  obtain ⟨S, hNmS⟩ := hNmP.exists_le_sylow
  let SG : Subgroup G := (S : Subgroup ↥M).map M.subtype
  have hSGp : IsPGroup 2 SG := (S.isPGroup').map M.subtype
  obtain ⟨Q, hSGQ⟩ := hSGp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  have hSG_conjT : SG ≤ MulAut.conj g • (T : Subgroup G) := by
    have hQeq : (Q : Subgroup G) = MulAut.conj g • (T : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    exact hSGQ.trans (le_of_eq hQeq)
  have hSGM : SG ≤ M := Subgroup.map_subtype_le (S : Subgroup ↥M)
  have hSG_le : SG ≤ MulAut.conj g • N := by
    intro s hs
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsM : s ∈ M := hSGM hs
    have hsT : (MulAut.conj g)⁻¹ • s ∈ (T : Subgroup G) := by
      have h := hSG_conjT hs
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    refine ⟨?_, hsT⟩
    have hconj : (MulAut.conj g)⁻¹ • s = (g : G)⁻¹ * s * g := by
      simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    rw [hconj]
    simpa using (inferInstance : M.Normal).conj_mem s hsM g⁻¹
  have hcardSG : Nat.card SG = Nat.card (S : Subgroup ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have hcardConj : Nat.card (MulAut.conj g • N : Subgroup G) = Nat.card N := by
    rw [Subgroup.pointwise_smul_def]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardNm : Nat.card N = Nat.card (N.subgroupOf M) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ M)).toEquiv).symm
  have hle1 : Nat.card (S : Subgroup ↥M) ≤ Nat.card (N.subgroupOf M) :=
    calc Nat.card (S : Subgroup ↥M) = Nat.card SG := hcardSG.symm
      _ ≤ Nat.card (MulAut.conj g • N : Subgroup G) := Subgroup.card_le_of_le hSG_le
      _ = Nat.card N := hcardConj
      _ = Nat.card (N.subgroupOf M) := hcardNm
  have hle2 : Nat.card (N.subgroupOf M) ≤ Nat.card (S : Subgroup ↥M) :=
    Subgroup.card_le_of_le hNmS
  have hSeq : N.subgroupOf M = (S : Subgroup ↥M) :=
    Subgroup.eq_of_le_of_card_ge hNmS hle1
  have hrel : N.relIndex M = (S : Subgroup ↥M).index := by
    change (N.subgroupOf M).index = (S : Subgroup ↥M).index
    rw [hSeq]
  exact fun h => (Sylow.not_dvd_index S) (hrel ▸ h)

end CFSG.OddStandard.HigherRank.YamadaG23