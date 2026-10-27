module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDich

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

structure WeakShape {X : Type} [Group X] (t : X) (A : Subgroup X) (m : ℕ) : Prop where
  order : orderOf t = 2
  iso : Nonempty (A ≃* alternatingGroup (Fin m))
  le_cent : A ≤ centralizer ({t} : Set X)
  cent_le_norm : centralizer ({t} : Set X) ≤ normalizer (A : Set X)
  two_mem : ∀ y ∈ centralizer (A : Set X) ⊓ centralizer ({t} : Set X), ∀ k : ℕ, y ^ 2 ^ k = 1 →
    y ∈ zpowers t

section Basic

variable {X : Type} [Group X] {t : X} {A : Subgroup X} {m : ℕ}

theorem mem_centralizer_of_weakShape (h : WeakShape t A m) : t ∈ centralizer (A : Set X) := by
  rw [mem_centralizer_iff]
  intro a ha
  exact mem_centralizer_singleton_iff.1 (h.le_cent ha)

theorem mem_inf_of_weakShape (h : WeakShape t A m) :
    t ∈ centralizer (A : Set X) ⊓ centralizer ({t} : Set X) :=
  ⟨mem_centralizer_of_weakShape h, mem_centralizer_singleton_iff.2 rfl⟩

theorem WeakShape.exactShape_of_le (h : WeakShape t A m)
    (hle : centralizer (A : Set X) ⊓ centralizer ({t} : Set X) ≤ zpowers t) :
    ExactShape t A m :=
  ⟨h.order, h.iso, h.le_cent, h.cent_le_norm,
    le_antisymm hle (zpowers_le.2 (mem_inf_of_weakShape h))⟩

theorem WeakShape.exactShape_of_card_le_four [Finite X] (h : WeakShape t A m)
    (hcard : Nat.card (centralizer (A : Set X) ⊓ centralizer ({t} : Set X) : Subgroup X) ≤ 4) :
    ExactShape t A m := by
  set D := centralizer (A : Set X) ⊓ centralizer ({t} : Set X) with hD
  have htD : t ∈ D := mem_inf_of_weakShape h
  have h2 : 2 ∣ Nat.card D := by
    have h1 := orderOf_dvd_natCard (⟨t, htD⟩ : D)
    rwa [Subgroup.orderOf_mk, h.order] at h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card D = 2 ^ k := by
    obtain ⟨c, hc⟩ := h2
    have hc2 : c = 1 ∨ c = 2 := by omega
    rcases hc2 with rfl | rfl
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  refine h.exactShape_of_le (fun y hy => h.two_mem y hy k ?_)
  have h1 : (⟨y, hy⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
  rw [hk] at h1
  simpa using congrArg Subtype.val h1

end Basic

section Cyc

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem cyc_of_weakShape (h : WeakShape t A m) : AltStdBal.Cyc A (zpowers t) t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set X) with hK
  have htK : t ∈ K := mem_centralizer_of_weakShape h
  let t' : K := ⟨t, htK⟩
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact h.order
  have hzp : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hPeq : (P : Subgroup K) = zpowers t' := by
    by_contra hne
    have hnil : Group.IsNilpotent (P : Subgroup K) := P.isPGroup'.isNilpotent
    have hlt : (zpowers t').subgroupOf (P : Subgroup K) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne ?_
      refine le_antisymm ?_ hP
      intro s hs
      have : (⟨s, hs⟩ : (P : Subgroup K)) ∈ (zpowers t').subgroupOf (P : Subgroup K) := by
        rw [htop]; trivial
      exact this
    have hgrow := Group.normalizerCondition_of_isNilpotent (G := (P : Subgroup K))
      ((zpowers t').subgroupOf (P : Subgroup K)) hlt
    obtain ⟨⟨y, hyP⟩, hyN, hyH⟩ := IsConcreteLE.exists_of_lt hgrow
    apply hyH
    have hyt : y * t' * y⁻¹ ∈ zpowers t' :=
      (mem_normalizer_iff.1 hyN ⟨t', hP (mem_zpowers t')⟩).1 (mem_zpowers t')
    have hord : orderOf (y * t' * y⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact ht'2
    have hyt2 : y * t' * y⁻¹ = t' :=
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic
        (inferInstance : IsCyclic (zpowers t')) hyt (mem_zpowers t') hord ht'2
    have hcomm : y * t' = t' * y := by
      have := congrArg (· * y) hyt2
      simpa [mul_assoc] using this
    have hyC : (y : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hcomm
    have hyz : (y : X) ∈ zpowers t := by
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hyP⟩
      refine h.two_mem _ ⟨y.2, hyC⟩ k ?_
      have h1 := congrArg (fun w : (P : Subgroup K) => ((w : K) : X)) hk
      simpa using h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyz
    refine mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    simpa using hk
  have hsub : (zpowers t).subgroupOf K = zpowers t' := by
    ext x
    simp only [mem_subgroupOf, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨zpowers_le.2 htK, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order, pow_one]),
    ?_, inferInstance, h.order, mem_zpowers t⟩
  show ¬ 2 ∣ ((zpowers t).subgroupOf K).index
  rw [hsub, ← hPeq]
  exact P.not_dvd_index

theorem solvable_centralizer_of_cyc (d : AltStdBal.Cyc A (zpowers t) t) :
    Group.IsSolvable ↥(centralizer (A : Set X)) := by
  classical
  set K := centralizer (A : Set X) with hK
  obtain ⟨hNK, hNconj, hNodd, hNQ, hNmul⟩ :=
    AltStdBal.oddPart_spec d.le d.pgroup d.odd_index d.cyclic
  set N := AltStdBal.oddPart K with hN
  have htK : t ∈ K := d.le d.mem
  let N' : Subgroup ↥K := N.subgroupOf K
  have hN'normal : N'.Normal := by
    refine ⟨fun n hn k => ?_⟩
    exact hNconj k k.2 n hn
  have hN'solv : Group.IsSolvable ↥N' := by
    have : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNK).injective
  let t' : ↥K := ⟨t, htK⟩
  let g : ↥(zpowers t') →* ↥K ⧸ N' := (QuotientGroup.mk' N').comp (zpowers t').subtype
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx, q, hq, hkxq⟩ := hNmul k k.2
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    refine ⟨⟨t' ^ j, mem_zpowers_iff.2 ⟨j, rfl⟩⟩, ?_⟩
    have hxN' : (⟨x, hNK hx⟩ : ↥K) ∈ N' := hx
    have hkeq : k = ⟨x, hNK hx⟩ * t' ^ j := Subtype.ext (by simpa using hkxq)
    show QuotientGroup.mk' N' (t' ^ j) = (k : ↥K ⧸ N')
    rw [hkeq, QuotientGroup.mk_mul]
    have : ((⟨x, hNK hx⟩ : ↥K) : ↥K ⧸ N') = 1 := (QuotientGroup.eq_one_iff _).2 hxN'
    rw [this, one_mul]
    rfl
  have hcyc : IsCyclic (↥K ⧸ N') := isCyclic_of_surjective g hg
  have hqsolv : Group.IsSolvable (↥K ⧸ N') :=
    Group.isSolvable_of_comm (fun a b => hcyc.isMulCommutative.is_comm.comm a b)
  exact Group.isSolvable_of_ker_le_range N'.subtype (QuotientGroup.mk' N') (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem solvable_centralizer_of_weakShape (h : WeakShape t A m) :
    Group.IsSolvable ↥(centralizer (A : Set X)) :=
  solvable_centralizer_of_cyc (cyc_of_weakShape h)

omit [Finite X] in
theorem isComponent_subgroupOf_centralizer_of_weakShape (h : WeakShape t A m) (hm : 5 ≤ m) :
    CFSG.IsComponent (A.subgroupOf (centralizer ({t} : Set X))) := by
  obtain ⟨e⟩ := h.iso
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.le_cent).symm (isQuasisimple_cfsg_of_alt hm e)
  · have hnorm : (A.subgroupOf (centralizer ({t} : Set X))).Normal :=
      (normal_subgroupOf_iff_le_normalizer h.le_cent).2 h.cent_le_norm
    exact hnorm.isSubnormal

end Cyc

end CFSG.OddStandard.AltStdSec
