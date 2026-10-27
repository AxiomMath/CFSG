module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Quat

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Cls

variable {Y : Type} [Group Y]

@[expose] noncomputable def cls (C : Subgroup Y) (x : Y) : ↥C ⧸ classicalInvolutionOddCore ↥C := by
  classical
  exact if hx : x ∈ C then QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨x, hx⟩ else 1

variable {C : Subgroup Y} {x y : Y}

theorem cls_of_mem (hx : x ∈ C) :
    cls C x = QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨x, hx⟩ := by
  unfold cls
  rw [dif_pos hx]

theorem cls_mul (hx : x ∈ C) (hy : y ∈ C) : cls C (x * y) = cls C x * cls C y := by
  rw [cls_of_mem (C.mul_mem hx hy), cls_of_mem hx, cls_of_mem hy, ← map_mul]
  rfl

theorem cls_inv (hx : x ∈ C) : cls C x⁻¹ = (cls C x)⁻¹ := by
  rw [cls_of_mem (C.inv_mem hx), cls_of_mem hx, ← map_inv]
  rfl

theorem cls_one : cls C (1 : Y) = 1 := by
  rw [cls_of_mem C.one_mem]
  exact map_one _

theorem cls_eq_iff (hx : x ∈ C) (hy : y ∈ C) : cls C x = cls C y ↔ x⁻¹ * y ∈ oddCoreIn C := by
  rw [cls_of_mem hx, cls_of_mem hy, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = (⟨x, hx⟩ : ↥C)⁻¹ * ⟨y, hy⟩ := Subtype.ext hzx
    rwa [this] at hz

theorem cls_eq_one_iff (hx : x ∈ C) : cls C x = 1 ↔ x ∈ oddCoreIn C := by
  rw [← cls_one (C := C), cls_eq_iff hx C.one_mem, mul_one]
  exact ⟨fun h => by simpa using (oddCoreIn C).inv_mem h, fun h => (oddCoreIn C).inv_mem h⟩

end Cls

section Abstract

variable {G : Type*} [Group G]

theorem uv_cases {B B' T U V : G} (hBB : B * B' = B' * B) (hB : B * B = T) (hB' : B' * B' = T)
    (hT : T * T = 1)
    (h : ((U = B ∨ U = B⁻¹) ∧ (V = B' ∨ V = B'⁻¹)) ∨ ((U = B' ∨ U = B'⁻¹) ∧ (V = B ∨ V = B⁻¹))) :
    U * V⁻¹ = B * B'⁻¹ ∨ U * V⁻¹ = T * (B * B'⁻¹) := by
  have hBi : B⁻¹ = B * T := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hB, hT])
  have hB'i : B'⁻¹ = B' * T := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hB', hT])
  have hTB : T * B = B * T := by rw [← hB]; group
  have hTB' : T * B' = B' * T := by rw [← hB']; group
  have hBB' : B' * B = B * B' := hBB.symm
  have r1 : ∀ w : G, T * (B * w) = B * (T * w) := fun w => by rw [← mul_assoc, hTB, mul_assoc]
  have r2 : ∀ w : G, T * (B' * w) = B' * (T * w) := fun w => by rw [← mul_assoc, hTB', mul_assoc]
  have r3 : ∀ w : G, B' * (B * w) = B * (B' * w) := fun w => by rw [← mul_assoc, ← hBB, mul_assoc]
  have r4 : ∀ w : G, B * (B * w) = T * w := fun w => by rw [← mul_assoc, hB]
  have r5 : ∀ w : G, B' * (B' * w) = T * w := fun w => by rw [← mul_assoc, hB']
  have r6 : ∀ w : G, T * (T * w) = w := fun w => by rw [← mul_assoc, hT, one_mul]
  rcases h with ⟨hU | hU, hV | hV⟩ | ⟨hU | hU, hV | hV⟩
  · rw [hU, hV]; left; rfl
  · rw [hU, hV, inv_inv]; right
    simp only [hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV]; right
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV, inv_inv]; left
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV]; left
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV, inv_inv]; right
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV]; right
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]
  · rw [hU, hV, inv_inv]; left
    simp only [hBi, hB'i, mul_assoc, r1, r2, r3, r4, r5, r6, hTB, hTB', hBB', hB, hB', hT, mul_one]

end Abstract

section Member


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem sq_rel_of_member (h : PerpHypR r n Y R S t) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {t' : Y} (ht'L : t' ∈ L)
    (ht'2 : t' * t' = 1) (ht'1 : t' ≠ 1) {x y p q : Y} (hx : x ∈ L) (hy : y ∈ L)
    (hp : p = x * x) (hq : q = y * y) (hp2 : p * p = t') (hq2 : q * q = t') :
    q⁻¹ * p ∈ oddCoreIn L ∨ q * p ∈ oddCoreIn L := by
  obtain ⟨φ⟩ := h.quotEquiv hL
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  set N : Subgroup ↥L := classicalInvolutionOddCore ↥L with hN
  have hpL : p ∈ L := hp ▸ L.mul_mem hx hx
  have hqL : q ∈ L := hq ▸ L.mul_mem hy hy
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hp' : (⟨p, hpL⟩ : ↥L) = ⟨x, hx⟩ * ⟨x, hx⟩ := Subtype.ext hp
  have hq' : (⟨q, hqL⟩ : ↥L) = ⟨y, hy⟩ * ⟨y, hy⟩ := Subtype.ext hq
  have hpp : (⟨p, hpL⟩ : ↥L) * ⟨p, hpL⟩ = ⟨t', ht'L⟩ := Subtype.ext hp2
  have hqq : (⟨q, hqL⟩ : ↥L) * ⟨q, hqL⟩ = ⟨t', ht'L⟩ := Subtype.ext hq2
  have hT2 : (⟨t', ht'L⟩ : ↥L) * ⟨t', ht'L⟩ = 1 := Subtype.ext ht'2
  have h4 : ((⟨p, hpL⟩ : ↥L) * ⟨p, hpL⟩) * ((⟨p, hpL⟩ : ↥L) * ⟨p, hpL⟩) ∈ N := by
    rw [hpp, hT2]
    exact N.one_mem
  have h2 : (⟨p, hpL⟩ : ↥L) * ⟨p, hpL⟩ ∉ N := by
    rw [hpp]
    intro hmem
    have hord : orderOf (⟨t', ht'L⟩ : ↥L) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hT2) (fun h1 => ht'1 (congrArg Subtype.val h1))
    have hdvd : orderOf (⟨t', ht'L⟩ : ↥L) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hpq : ((⟨q, hqL⟩ : ↥L) * ⟨q, hqL⟩)⁻¹ * ((⟨p, hpL⟩ : ↥L) * ⟨p, hpL⟩) ∈ N := by
    rw [hpp, hqq]
    simp
  rcases sq_rel_of_mulEquiv φ hp' hq' h4 h2 hpq with h1 | h1
  · left
    exact ⟨⟨q, hqL⟩⁻¹ * ⟨p, hpL⟩, h1, rfl⟩
  · right
    exact ⟨⟨q, hqL⟩ * ⟨p, hpL⟩, h1, rfl⟩

theorem cls_rel (h : PerpHypR r n Y R S t) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hLC : L ≤ Subgroup.centralizer ({t} : Set Y))
    (hOL : oddCoreIn L ≤ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) (htL : t ∈ L)
    {x y p q : Y} (hx : x ∈ L) (hy : y ∈ L) (hp : p = x * x) (hq : q = y * y) (hp2 : p * p = t)
    (hq2 : q * q = t) :
    cls (Subgroup.centralizer ({t} : Set Y)) q = cls (Subgroup.centralizer ({t} : Set Y)) p ∨
      cls (Subgroup.centralizer ({t} : Set Y)) q =
        (cls (Subgroup.centralizer ({t} : Set Y)) p)⁻¹ := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hz2 : t * t = 1 := hU.sq
  have hz1 : t ≠ 1 := hU.ne_one
  have hpL : p ∈ L := hp ▸ L.mul_mem hx hx
  have hqL : q ∈ L := hq ▸ L.mul_mem hy hy
  rcases sq_rel_of_member h hL htL hz2 hz1 hx hy hp hq hp2 hq2 with h1 | h1
  · left
    exact (cls_eq_iff (hLC hqL) (hLC hpL)).mpr (hOL h1)
  · right
    have h2 : cls (Subgroup.centralizer ({t} : Set Y)) (q * p) = 1 :=
      (cls_eq_one_iff (Subgroup.mul_mem _ (hLC hqL) (hLC hpL))).mpr (hOL h1)
    rw [cls_mul (hLC hqL) (hLC hpL)] at h2
    exact eq_inv_of_mul_eq_one_left h2

theorem conj_mem_sup (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) {x y b b' : Y} (hx : x ∈ tightCore R) (hy : y ∈ K') (hb : b = x * x)
    (hb' : b' = y * y) (hbt : b * b = t) (hb't : b' * b' = t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    c * (b * b'⁻¹) * c⁻¹ ∈
      Subgroup.closure ({t, b * b'⁻¹} : Set Y) ⊔ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hKΩ : K ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hΩ : HypOmegaGen Ω := h.core.hyp
  have hK'Ω : K' ∈ Ω := hK'.1
  have hpair : twinSet Ω K = {K, K'} := TwinPerp.twinSet_eq_pair h2 hK' hne
  have hz : IsUniqueInvolution K t := Inner.isUniqueInvolution_core h.core.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hK'
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  have hKC : K ≤ C := CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz
  have hK'C : K' ≤ C := CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz'
  have hsubK : IsSubnormal K C := h.partIHypG.cls.isSubnormal_of_uniqueInvolution hKΩ hz
  have hsubK' : IsSubnormal K' C := h.partIHypG.cls.isSubnormal_of_uniqueInvolution hK'Ω hz'
  have hOK : oddCoreIn K ≤ oddCoreIn C := oddCoreIn_le_of_isSubnormal hsubK
  have hOK' : oddCoreIn K' ≤ oddCoreIn C := oddCoreIn_le_of_isSubnormal hsubK'
  have hcommK : ∀ a ∈ K, ∀ b ∈ K', a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn K := by
    have h4 := hΩ.omega4 K hKΩ K' hK'Ω hne.symm
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := t) ⟨hz.mem, hz'.mem⟩
      rwa [hord] at this
    have hpos : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
      one_le_padicValNat_of_dvd hpos hdvd
    have h5 := h4.2 (le_antisymm h4.1 h1)
    intro a ha b hb
    have hm : ⁅a, b⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator ha hb
    have := (h5 hm).1
    rwa [commutatorElement_def] at this
  have hbK : b ∈ K := hb ▸ K.mul_mem hx hx
  have hb'K' : b' ∈ K' := hb' ▸ K'.mul_mem hy hy
  have hbC : b ∈ C := hKC hbK
  have hb'C : b' ∈ C := hK'C hb'K'
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hjC : b * b'⁻¹ ∈ C := C.mul_mem hbC (C.inv_mem hb'C)
  have hBB : cls C b * cls C b' = cls C b' * cls C b := by
    have h1 : b * b' * b⁻¹ * b'⁻¹ ∈ oddCoreIn C := hOK (hcommK b hbK b' hb'K')
    have h2' := (cls_eq_one_iff (C.mul_mem (C.mul_mem (C.mul_mem hbC hb'C) (C.inv_mem hbC))
      (C.inv_mem hb'C))).mpr h1
    rw [cls_mul (C.mul_mem (C.mul_mem hbC hb'C) (C.inv_mem hbC)) (C.inv_mem hb'C),
      cls_mul (C.mul_mem hbC hb'C) (C.inv_mem hbC), cls_mul hbC hb'C, cls_inv hbC,
      cls_inv hb'C] at h2'
    exact mul_inv_eq_one.mp (by simpa [mul_assoc] using h2')
  have hB : cls C b * cls C b = cls C t := by rw [← cls_mul hbC hbC, hbt]
  have hB' : cls C b' * cls C b' = cls C t := by rw [← cls_mul hb'C hb'C, hb't]
  have hT : cls C t * cls C t = 1 := by rw [← cls_mul htC htC, hz2, cls_one]
  have hct : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * t * c⁻¹ = t * c * c⁻¹ := by rw [this]
      _ = t := by group
  have hcC : c⁻¹ ∈ C := C.inv_mem hc
  have hcbsq : (c * b * c⁻¹) * (c * b * c⁻¹) = t := by
    calc (c * b * c⁻¹) * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = t := by rw [hbt, hct]
  have hcb'sq : (c * b' * c⁻¹) * (c * b' * c⁻¹) = t := by
    calc (c * b' * c⁻¹) * (c * b' * c⁻¹) = c * (b' * b') * c⁻¹ := by group
      _ = t := by rw [hb't, hct]
  have hcb : c * b * c⁻¹ = (c * x * c⁻¹) * (c * x * c⁻¹) := by rw [hb]; group
  have hcb' : c * b' * c⁻¹ = (c * y * c⁻¹) * (c * y * c⁻¹) := by rw [hb']; group
  have hLK : conjSub c K ∈ twinSet Ω K := h.conj_mem_twinSet hKtw hc
  have hLK' : conjSub c K' ∈ twinSet Ω K := h.conj_mem_twinSet hK' hc
  rw [hpair] at hLK hLK'
  have hinj : conjSub c K ≠ conjSub c K' := fun heq => hne (by
    have h1 := congrArg (conjSub c⁻¹) heq
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1
    exact h1.symm)
  have htK : t ∈ K := hz.mem
  have htK' : t ∈ K' := hz'.mem
  have hcases : ((cls C (c * b * c⁻¹) = cls C b ∨ cls C (c * b * c⁻¹) = (cls C b)⁻¹) ∧
        (cls C (c * b' * c⁻¹) = cls C b' ∨ cls C (c * b' * c⁻¹) = (cls C b')⁻¹)) ∨
      ((cls C (c * b * c⁻¹) = cls C b' ∨ cls C (c * b * c⁻¹) = (cls C b')⁻¹) ∧
        (cls C (c * b' * c⁻¹) = cls C b ∨ cls C (c * b' * c⁻¹) = (cls C b)⁻¹)) := by
    rcases hLK with hL | hL
    ·
      have hL' : conjSub c K' = K' := by
        rcases hLK' with hL' | hL'
        · exact absurd (hL.trans hL'.symm) hinj
        · exact hL'
      left
      have hxc : c * x * c⁻¹ ∈ K := by
        have := conj_mem_conjSub (n := c) hx
        rwa [hL] at this
      have hyc : c * y * c⁻¹ ∈ K' := by
        have := conj_mem_conjSub (n := c) hy
        rwa [hL'] at this
      exact ⟨cls_rel h hKΩ hKC hOK htK hx hxc hb hcb hbt hcbsq,
        cls_rel h hK'Ω hK'C hOK' htK' hy hyc hb' hcb' hb't hcb'sq⟩
    · have hL : conjSub c K = K' := Set.mem_singleton_iff.mp hL
      have hL' : conjSub c K' = K := by
        rcases hLK' with hL' | hL'
        · exact hL'
        · exact absurd (hL.trans (Set.mem_singleton_iff.mp hL').symm) hinj
      right
      have hxc : c * x * c⁻¹ ∈ K' := by
        have := conj_mem_conjSub (n := c) hx
        rwa [hL] at this
      have hyc : c * y * c⁻¹ ∈ K := by
        have := conj_mem_conjSub (n := c) hy
        rwa [hL'] at this
      exact ⟨cls_rel h hK'Ω hK'C hOK' htK' hy hxc hb' hcb hb't hcbsq,
        cls_rel h hKΩ hKC hOK htK hx hyc hb hcb' hbt hcb'sq⟩
  have hU := uv_cases hBB hB hB' hT hcases
  set j := b * b'⁻¹ with hj
  have hcbC : c * b * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hbC) hcC
  have hcb'C : c * b' * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hb'C) hcC
  have hcjC : c * j * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hjC) hcC
  have hcj : cls C (c * j * c⁻¹) = cls C (c * b * c⁻¹) * (cls C (c * b' * c⁻¹))⁻¹ := by
    have e : c * j * c⁻¹ = (c * b * c⁻¹) * (c * b' * c⁻¹)⁻¹ := by rw [hj]; group
    rw [e, cls_mul hcbC (C.inv_mem hcb'C), cls_inv hcb'C]
  have hJ : cls C j = cls C b * (cls C b')⁻¹ := by
    rw [hj, cls_mul hbC (C.inv_mem hb'C), cls_inv hb'C]
  have hjE : j ∈ Subgroup.closure ({t, j} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htE : t ∈ Subgroup.closure ({t, j} : Set Y) := Subgroup.subset_closure (Set.mem_insert _ _)
  rcases hU with h1 | h1
  · have h1' : cls C j = cls C (c * j * c⁻¹) := by rw [hcj, h1, hJ]
    have hmem := (cls_eq_iff hjC hcjC).mp h1'
    have e : c * j * c⁻¹ = j * (j⁻¹ * (c * j * c⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hjE hmem
  · have h1' : cls C (t * j) = cls C (c * j * c⁻¹) := by
      rw [hcj, h1, cls_mul htC hjC, hJ]
    have hmem := (cls_eq_iff (C.mul_mem htC hjC) hcjC).mp h1'
    have e : c * j * c⁻¹ = (t * j) * ((t * j)⁻¹ * (c * j * c⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ htE hjE) hmem

end Member

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
