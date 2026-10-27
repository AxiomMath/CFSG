module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalDefs
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup
open scoped Pointwise

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_of_normal_of_isCyclic_sylow (hO : CFSG.oddCore Γ = ⊥) {H Q : Subgroup Γ} [H.Normal]
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) (hi : ¬ 2 ∣ Q.relIndex H) (hc : IsCyclic Q) :
    H = Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  let S : Sylow 2 H := hQ'.toSylow hi
  have hS : IsCyclic S := by
    have h : IsCyclic (Q.subgroupOf H) := (subgroupOfEquivOfLe hQH).isCyclic.2 hc
    exact h
  have hSeq : (S : Subgroup H) = Q.subgroupOf H := IsPGroup.toSylow_coe hQ' hi
  obtain ⟨-, hmul, -, ⟨-, hodd, -, -⟩, hchar⟩ := cyclic_sylow_normal_odd_complement S hS
  have := hchar
  have hnormal : ((pPrimeCore 2 H).map H.subtype).Normal := inferInstance
  have hle : (pPrimeCore 2 H).map H.subtype ≤ CFSG.oddCore Γ :=
    le_sSup ⟨hnormal, by rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hodd⟩
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at hle
  refine le_antisymm (fun x hx => ?_) hQH
  have hx1 : (⟨x, hx⟩ : H) ∈ (pPrimeCore 2 H : Set H) * (S : Set H) := by
    rw [hmul]
    trivial
  obtain ⟨a, ha, s, hs, has⟩ := hx1
  have ha1 : a = 1 := by
    have : a ∈ (pPrimeCore 2 H) := ha
    rw [hle] at this
    exact this
  have hsx : s = ⟨x, hx⟩ := by
    rw [ha1] at has
    simpa using has
  have : s ∈ (S : Subgroup H) := hs
  rw [hSeq] at this
  rw [hsx] at this
  exact this

end Generic

section Centralizer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_mem_isCyclic {Q : Subgroup G} (hc : IsCyclic Q) {z : G} (hz : z ∈ Q) :
    Q ≤ centralizer ({z} : Set G) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have := (IsCyclic.isMulCommutative (α := Q)).is_comm.comm ⟨w, hz⟩ ⟨q, hq⟩
  exact congrArg Subtype.val this

theorem inf_centralizer_eq {K Q : Subgroup G} {z : G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q)
    (hi : ¬ 2 ∣ Q.relIndex K) (hc : IsCyclic Q) (hz : z ∈ Q)
    (hnorm : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hO : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    K ⊓ centralizer ({z} : Set G) = Q := by
  set C := centralizer ({z} : Set G) with hC
  have hQC : Q ≤ C := le_centralizer_of_mem_isCyclic hc hz
  have hQH : Q ≤ K ⊓ C := le_inf hQK hQC
  refine le_antisymm ?_ hQH
  have hKC : (K ⊓ C) ≤ C := inf_le_right
  have : ((K ⊓ C).subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hKC]
    exact fun x hx => inf_normalizer_le_normalizer_inf ⟨hnorm hx, le_normalizer hx⟩
  have hQ0 : Q.subgroupOf C ≤ (K ⊓ C).subgroupOf C := fun x hx => hQH hx
  have hQ0p : IsPGroup 2 (Q.subgroupOf C) := hQ.of_equiv (subgroupOfEquivOfLe hQC).symm
  have hQ0c : IsCyclic (Q.subgroupOf C) := (subgroupOfEquivOfLe hQC).isCyclic.2 hc
  have hQ0i : ¬ 2 ∣ (Q.subgroupOf C).relIndex ((K ⊓ C).subgroupOf C) := by
    rw [relIndex_subgroupOf hKC]
    intro h2
    apply hi
    exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q (K ⊓ C) K hQH inf_le_left))
  have heq := eq_of_normal_of_isCyclic_sylow hO hQ0 hQ0p hQ0i hQ0c
  intro x hx
  have hxC : x ∈ C := hx.2
  have : (⟨x, hxC⟩ : C) ∈ (K ⊓ C).subgroupOf C := hx
  rw [heq] at this
  exact this

end Centralizer

section Complement

variable {G : Type*} [Group G] [Finite G]

@[expose] def oddPart (K : Subgroup G) : Subgroup G := (pPrimeCore 2 K).map K.subtype

theorem oddPart_spec {K Q : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q)
    (hi : ¬ 2 ∣ Q.relIndex K) (hc : IsCyclic Q) :
    oddPart K ≤ K ∧ (∀ k ∈ K, ∀ x ∈ oddPart K, k * x * k⁻¹ ∈ oddPart K) ∧
      Odd (Nat.card (oddPart K)) ∧ oddPart K ⊓ Q = ⊥ ∧
      ∀ k ∈ K, ∃ x ∈ oddPart K, ∃ q ∈ Q, k = x * q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.of_equiv (subgroupOfEquivOfLe hQK).symm
  let S : Sylow 2 K := hQ'.toSylow hi
  have hS : IsCyclic S := by
    have h : IsCyclic (Q.subgroupOf K) := (subgroupOfEquivOfLe hQK).isCyclic.2 hc
    exact h
  have hSeq : (S : Subgroup K) = Q.subgroupOf K := IsPGroup.toSylow_coe hQ' hi
  obtain ⟨-, hmul, hdisj, ⟨hnormal, hodd, -, -⟩, -⟩ := cyclic_sylow_normal_odd_complement S hS
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hnormal.conj_mem y hy ⟨k, hk⟩, ?_⟩
    simp
  · unfold oddPart
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hodd
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx1
    have hy2 : y ∈ (S : Subgroup K) := by
      rw [hSeq]
      exact hx2
    have : y ∈ pPrimeCore 2 K ⊓ (S : Subgroup K) := ⟨hy, hy2⟩
    rw [hdisj] at this
    have hy1 : y = 1 := this
    simp [hy1]
  · intro k hk
    have h1 : (⟨k, hk⟩ : K) ∈ (pPrimeCore 2 K : Set K) * (S : Set K) := by
      rw [hmul]
      trivial
    obtain ⟨a, ha, s, hs, has⟩ := h1
    refine ⟨(a : G), Subgroup.mem_map.2 ⟨a, ha, rfl⟩, (s : G), ?_, ?_⟩
    · have : s ∈ (S : Subgroup K) := hs
      rw [hSeq] at this
      exact this
    · have := congrArg Subtype.val has
      simpa using this.symm

end Complement

section Std

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem Setting.isStandard (h : Setting G L n) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup L := h.std.standard

theorem Setting.normalizer_eq (h : Setting G L n) :
    normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) :=
  h.std.standard.2.2.2.1

theorem Setting.even_card (h : Setting G L n) : Even (Nat.card (centralizer (L : Set G))) :=
  h.std.standard.2.1

@[expose] def sylowSub (S : Sylow 2 (centralizer (L : Set G))) : Subgroup G :=
  (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype

omit [Finite G] in
theorem card_sylowSub (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card (sylowSub S) = Nat.card S :=
  Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem Cyc.of_sylow (h : Setting G L n) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) : ∃ z, Cyc L (sylowSub S) z := by
  have h2 : 2 ∣ Nat.card (sylowSub S) := by
    rw [card_sylowSub]
    exact two_dvd_card_sylow h.even_card S
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := sylowSub S) 2 h2
  refine ⟨(x : G), Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, ?_, ?_, x.2⟩
  · have : (sylowSub S).relIndex (centralizer (L : Set G)) =
        (S : Subgroup (centralizer (L : Set G))).index := by
      unfold Subgroup.relIndex sylowSub
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    rw [this]
    exact S.not_dvd_index
  · exact (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).isCyclic.1 hS
  · rw [Subgroup.orderOf_coe]
    exact hx

theorem centralizer_le_normalizer (h : Setting G L n) (d : Cyc L Q z) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
  (standard_involution_centralizer_normality h.isStandard (d.le d.mem) d.order).1

theorem le_centralizer_single (h : Setting G L n) (d : Cyc L Q z) :
    L ≤ centralizer ({z} : Set G) :=
  (standard_involution_centralizer_normality h.isStandard (d.le d.mem) d.order).2.1

theorem cent_inf_eq (h : Setting G L n) (d : Cyc L Q z) :
    centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q :=
  inf_centralizer_eq d.le d.pgroup d.odd_index d.cyclic d.mem
    (by rw [h.normalizer_eq]; exact centralizer_le_normalizer h d) (h.bal z d.order)

theorem exists_conj_of_involution (d : Cyc L Q z) {w : G} (hw : w ∈ centralizer (L : Set G))
    (hw2 : orderOf w = 2) : ∃ k ∈ centralizer (L : Set G), k * z * k⁻¹ = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hK
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := d.pgroup.of_equiv (subgroupOfEquivOfLe d.le).symm
  let S : Sylow 2 K := hQ'.toSylow d.odd_index
  have hSeq : (S : Subgroup K) = Q.subgroupOf K := IsPGroup.toSylow_coe hQ' d.odd_index
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨w, hw⟩ : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hw2, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S
  have hwP : (⟨w, hw⟩ : K) ∈ (P : Subgroup K) := hP (Subgroup.mem_zpowers _)
  have hgw : g * (⟨w, hw⟩ : K) * g⁻¹ ∈ (S : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hwP, by simp [MulAut.conj_apply]⟩
  rw [hSeq] at hgw
  have hgwQ : (g : G) * w * (g : G)⁻¹ ∈ Q := hgw
  have hord : orderOf ((g : G) * w * (g : G)⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw2]
  have heq := eq_of_orderOf_eq_two_of_isCyclic d.cyclic hgwQ d.mem hord d.order
  refine ⟨(g : G)⁻¹, Subgroup.inv_mem _ g.2, ?_⟩
  rw [← heq]
  group

theorem Cyc.mul_self (d : Cyc L Q z) : z * z = 1 := by
  rw [← sq, ← d.order]
  exact pow_orderOf_eq_one z

end Std

end CFSG.OddStandard.AltStdBal
