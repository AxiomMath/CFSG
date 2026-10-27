module

public import CFSG.Fischer.Classification.Recognition.Fischer
public import CFSG.Fischer.Classification.Basic.Local
public import CFSG.Fischer.Classification.Unitary.Model
import CFSG.Fischer.Classification.Recognition.CaseR3
import CFSG.Fischer.Classification.Unitary.Mu
import CFSG.Timmesfeld.Transvection.QTwoFischer
import CFSG.Walter.Bender1970.S2.Inner
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Fischer.Classification.Pinned

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement
open Pointwise

theorem transvections_nonempty {H : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian H) :
    (Transvections H).Nonempty := by
  obtain ⟨iso, hiso⟩ := exists_psu_equiv hH
  let v : Fin 6 → K := Unitary.isoVec (m := 6) (by norm_num)
  have hv0 : v ≠ 0 := Unitary.isoVec_ne_zero (by norm_num)
  have hv : CFSG.ClassicalGroups.Unitary.herm Unitary.frob v v = 0 :=
    Unitary.isoVec_isotropic (by norm_num)
  have hDU : Unitary.tqU v ∈ Unitary.DU 6 := Unitary.tqU_mem_DU hv0 hv
  have hmem : Unitary.tqU v ∈ CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2 ''
      Transvections (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2_image]
    exact hDU
  obtain ⟨x, hx, hxeq⟩ := hmem
  have hx' : x = CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2.symm (Unitary.tqU v) := by
    rw [← hxeq, MulEquiv.symm_apply_apply]
  refine ⟨iso (CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2.symm (Unitary.tqU v)), ?_⟩
  rw [← hiso]
  exact ⟨_, hx' ▸ hx, rfl⟩

theorem F22.localClass_nonempty {X : Type} [Group X] {E : Set X} (h : F22 X E) {e : X}
    (he : e ∈ E) : (LocalClass E e).Nonempty := by
  obtain ⟨H, hH, iso, hiso⟩ := F22_local h he
  have hne : (Transvections H).Nonempty := transvections_nonempty hH
  rw [← hiso] at hne
  obtain ⟨q, hq⟩ := hne
  rw [Set.mem_image] at hq
  obtain ⟨f, hf, -⟩ := hq
  simp only [LocalImages, Set.mem_setOf_eq] at hf
  obtain ⟨l, hl, -⟩ := hf
  exact ⟨l, hl⟩

theorem F23.localClass_nonempty {X : Type} [Group X] {E : Set X} (h : F23 X E) {e : X}
    (he : e ∈ E) : (LocalClass E e).Nonempty := by
  have h22 : F22 (LocalQuotient E e) (LocalImages E e) := F23_local h he
  obtain ⟨q, hq⟩ := Pair.nonempty h22.1
  obtain ⟨x, hx⟩ := F22.localClass_nonempty h22 hq
  have hxmem : x ∈ LocalImages E e := hx.1
  simp only [LocalImages, Set.mem_setOf_eq] at hxmem
  obtain ⟨l, hl, -⟩ := hxmem
  exact ⟨l, hl⟩

theorem F24.localClass_nonempty {X : Type} [Group X] {E : Set X} (h : F24 X E) {e : X}
    (he : e ∈ E) : (LocalClass E e).Nonempty := by
  have h23 : F23 (LocalQuotient E e) (LocalImages E e) := F24_local h he
  obtain ⟨q, hq⟩ := Pair.nonempty h23.1
  obtain ⟨x, hx⟩ := F23.localClass_nonempty h23 hq
  have hxmem : x ∈ LocalImages E e := hx.1
  simp only [LocalImages, Set.mem_setOf_eq] at hxmem
  obtain ⟨l, hl, -⟩ := hxmem
  exact ⟨l, hl⟩

theorem HasType.localClass_nonempty {k : Fin 3} {X : Type} [Group X] {E : Set X}
    (h : HasType k X E) {e : X} (he : e ∈ E) : (LocalClass E e).Nonempty := by
  obtain ⟨_ | _ | n, hk⟩ := k
  · exact F22.localClass_nonempty h he
  · exact F23.localClass_nonempty h he
  · exact F24.localClass_nonempty h he

theorem F22.exists_mulEquiv_U2 {X : Type} [Group X] {E : Set X} (h : F22 X E) {e : X}
    (he : e ∈ E) :
    ∃ iso : LocalQuotient E e ≃* Unitary.U2 6, iso '' LocalImages E e = Unitary.DU 6 := by
  obtain ⟨H, hH, φ, hφ⟩ := F22_local h he
  obtain ⟨ψ, hψ⟩ := exists_psu_equiv hH
  refine ⟨φ.trans (ψ.symm.trans CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2), ?_⟩
  rw [MulEquiv.coe_trans, Set.image_comp, MulEquiv.coe_trans, Set.image_comp, hφ, ← hψ,
    image_symm_image, CFSG.Timmesfeld.Transvection.QTwo.psuOneEquivU2_image]

theorem nonabelianCommutator_U2_six :
    ∃ a b : commutator (Unitary.U2 6), a * b ≠ b * a := by
  obtain ⟨a, b, -, -, -, -, hab⟩ := Unitary.exists_tq_not_commute (m := 6) (by norm_num)
  have htop : commutator (Unitary.U2 6) = ⊤ := commutator_U2 (by norm_num)
  refine ⟨⟨(Unitary.u2Equiv 6).symm (Unitary.tq a), htop ▸ Subgroup.mem_top _⟩,
    ⟨(Unitary.u2Equiv 6).symm (Unitary.tq b), htop ▸ Subgroup.mem_top _⟩, ?_⟩
  intro h
  apply hab
  have := congrArg (fun x : commutator (Unitary.U2 6) =>
    (Unitary.u2Equiv 6) (x : Unitary.U2 6)) h
  simpa using this

theorem hasType_localQuotient_simple_zero {X : Type} [Group X] {E : Set X} (h : F22 X E) :
    ∀ d ∈ E, IsSimpleGroup (commutator (LocalQuotient E d)) ∧
      ∃ a b : commutator (LocalQuotient E d), a * b ≠ b * a := by
  intro d hd
  obtain ⟨iso, -⟩ := F22.exists_mulEquiv_U2 h hd
  have htop : commutator (LocalQuotient E d) = ⊤ :=
    (commutator_eq_top_congr iso).2 (commutator_U2 (by norm_num))
  have hsimple : IsSimpleGroup (commutator (LocalQuotient E d)) :=
    @Recognition.R3.isSimpleGroup_commutator_of_mulEquiv (Unitary.U2 6) (LocalQuotient E d) _ _
      iso.symm (isSimpleGroup_commutator_U2 (by norm_num))
  obtain ⟨a, b, hab⟩ := nonabelianCommutator_U2_six
  refine ⟨hsimple, ⟨⟨iso.symm a, htop ▸ Subgroup.mem_top _⟩,
    ⟨iso.symm b, htop ▸ Subgroup.mem_top _⟩, ?_⟩⟩
  intro h
  apply hab
  exact Subtype.ext (by
    have := congrArg (fun x : commutator (LocalQuotient E d) =>
      iso (x : LocalQuotient E d)) h
    simpa using this)

theorem swap_commute_eq {a b c e : Fin 3} (hab : a ≠ b) (hce : c ≠ e)
    (h : Equiv.swap a b * Equiv.swap c e = Equiv.swap c e * Equiv.swap a b) :
    Equiv.swap a b = Equiv.swap c e := by
  revert a b c e
  decide

theorem hasType_nonabelianCommutator {X : Type} [Group X] {E : Set X} (hH : Hyp X E)
    {k : Fin 3} (hk : HasType k X E) : NonabelianCommutator X := by
  by_contra hna
  simp only [NonabelianCommutator, not_exists, not_not] at hna
  obtain ⟨φ, hφ⟩ := Pair.exists_mulEquiv_perm_three hH.pair hH.center hH.simple hna
  have hk' : HasType k (Equiv.Perm (Fin 3)) (φ '' E) := hasType_map hk φ
  obtain ⟨d, hd⟩ := Pair.nonempty hH.pair
  have hd' : φ d ∈ φ '' E := ⟨d, hd, rfl⟩
  obtain ⟨f, hf⟩ := HasType.localClass_nonempty hk' hd'
  have hE : φ '' E = {σ : Equiv.Perm (Fin 3) | σ.IsSwap} := by
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).1 hg
    · intro hσ
      exact ⟨φ.symm σ, (hφ (φ.symm σ)).2 (by simpa using hσ), φ.apply_symm_apply σ⟩
  have hf_swap : f.IsSwap := by
    have : f ∈ φ '' E := hf.1
    rwa [hE] at this
  have hd_swap : (φ d).IsSwap := (hφ d).1 hd
  obtain ⟨a, b, hab, rfl⟩ := hf_swap
  obtain ⟨c, e, hce, hde⟩ := hd_swap
  rw [hde] at hf
  exact hf.2.1 (swap_commute_eq hab hce hf.2.2)

theorem hasType_tripleProperty_zero {X : Type} [Group X] {E : Set X} (hH : Hyp X E)
    (h : F22 X E) : TripleProperty E := by
  obtain ⟨e, he⟩ := Pair.nonempty hH.pair
  have hcomm : ∃ e f, e ∈ E ∧ f ∈ E ∧ e ≠ f ∧ e * f = f * e := by
    obtain ⟨f, hf⟩ := F22.localClass_nonempty h he
    exact ⟨e, f, he, hf.1, hf.2.1.symm, hf.2.2.symm⟩
  have hconn : (commGraph E).Connected := Pair.connected_of_simple hH.pair hH.simple hcomm
  obtain ⟨iso, hiso⟩ := F22.exists_mulEquiv_U2 h he
  have hT : TripleProperty (LocalImages E e) := by
    refine (tripleProperty_congr iso hiso).2 ?_
    exact tripleProperty_DU (by norm_num)
  exact Pair.tripleProperty_of_localImages hH.pair hconn he
    (Pair.starImage_injective_of_simple hH.pair hH.center hH.simple he) hT

theorem hasType_tripleProperty_of_local {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    {k : Fin 3} (hk : HasType k Y F)
    (hloc : ∀ d ∈ F, TripleProperty (LocalImages F d)) : TripleProperty F := by
  have hna : NonabelianCommutator Y := hasType_nonabelianCommutator hH hk
  obtain ⟨d, hd⟩ := Pair.nonempty hH.pair
  have hconn : (commGraph F).Connected := by
    obtain ⟨f, hf⟩ := Pair.localClass_nonempty hH.pair hH.simple hna hd
    exact Pair.connected_of_simple hH.pair hH.simple ⟨d, f, hd, hf.1, hf.2.1.symm, hf.2.2.symm⟩
  exact Pair.tripleProperty_of_localImages hH.pair hconn hd
    (Pair.starImage_injective_of_simple hH.pair hH.center hH.simple hd) (hloc d hd)

section Certificates


theorem localGroup_eq_centralizer_of_fi23 {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F)
    (ψ : Y ≃* Carrier 1) {d : Y} (hd : d ∈ F) (hk : HasType 1 Y F) :
    LocalGroup F d = Subgroup.centralizer ({d} : Set Y) := by
  have hfinY : Finite Y := Pair.finite hP
  have hLC : LocalGroup F d ≤ Subgroup.centralizer ({d} : Set Y) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_localGroup' hl
  have hLnormal : ((LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLC]
    intro l c hl hc
    have hcd : c * d * c⁻¹ = d := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hmap : (LocalGroup F d).map (MulAut.conj c).toMonoidHom = LocalGroup F d := by
      change Subgroup.map (↑(MulAut.conj c) : Y →* Y) (LocalGroup F d) = LocalGroup F d
      rw [← localGroup_map (MulAut.conj c) F d,
        CFSG.Fischer.Classification.Unitary.Pair.image_conj hP c, MulAut.conj_apply, hcd]
    simpa [MulAut.conj_apply] using
      hmap ▸ Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hl
  have hMnormal : (((LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y))).map
      (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y))))).Normal :=
    hLnormal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨f, hf⟩ := HasType.localClass_nonempty hk hd
  have hfL : f ∈ LocalGroup F d := mem_localGroup hf
  have hfC : f ∈ Subgroup.centralizer ({d} : Set Y) := hLC hfL
  have hdC : d ∈ Subgroup.centralizer ({d} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hdZ : (⟨d, hdC⟩ : Subgroup.centralizer ({d} : Set Y)) ∈
      Subgroup.center (Subgroup.centralizer ({d} : Set Y)) := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hd_order : orderOf d = 2 := hP.2.2.1 d hd
  have hdC_order : orderOf (⟨d, hdC⟩ : Subgroup.centralizer ({d} : Set Y)) = 2 := by
    rw [Subgroup.orderOf_mk, hd_order]
  obtain ⟨hcommC, -, hcard_center⟩ :=
    Recognition.centralizer_perfect_center hP (k := 1) (by norm_num) ψ hd
  have hzC : Subgroup.zpowers (⟨d, hdC⟩ :
        Subgroup.centralizer ({d} : Set Y)) =
      Subgroup.center (Subgroup.centralizer ({d} : Set Y)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr hdZ
    · rw [Nat.card_zpowers, hdC_order, hcard_center]
  have hf_not_center : (⟨f, hfC⟩ : Subgroup.centralizer ({d} : Set Y)) ∉
      Subgroup.center (Subgroup.centralizer ({d} : Set Y)) := by
    intro hfZ
    have hmem : (⟨f, hfC⟩ : Subgroup.centralizer ({d} : Set Y)) ∈
        Subgroup.zpowers (⟨d, hdC⟩ : Subgroup.centralizer ({d} : Set Y)) := by
      rw [hzC]
      exact hfZ
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hdC_order).1 hmem with h | h
    · exact Pair.ne_one hP hf.1 (congrArg Subtype.val h)
    · exact hf.2.1 (congrArg Subtype.val h)
  have hMne : (((LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y))).map
      (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y))))) ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk (⟨f, hfC⟩ : Subgroup.centralizer ({d} : Set Y)) ∈
        ((LocalGroup F d).subgroupOf (Subgroup.centralizer ({d} : Set Y))).map
          (QuotientGroup.mk' (Subgroup.center
            (Subgroup.centralizer ({d} : Set Y)))) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hfL)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hf_not_center ((QuotientGroup.eq_one_iff _).1 hmem)
  obtain ⟨e⟩ := Recognition.centralizer_quotient_of_fi23 hP (k := 1) rfl ψ hd
  have hQsimple : IsSimpleGroup (Subgroup.centralizer ({d} : Set Y) ⧸
      Subgroup.center (Subgroup.centralizer ({d} : Set Y))) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
  have : (((LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y))).map
      (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y))))).Normal :=
    hMnormal
  have hMtop : (((LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y))).map
      (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y))))) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((LocalGroup F d).subgroupOf (Subgroup.centralizer ({d} : Set Y))).map
        (QuotientGroup.mk' (Subgroup.center
          (Subgroup.centralizer ({d} : Set Y))))) with h | h
    · exact absurd h hMne
    · exact h
  have hsup : (LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y)) ⊔
      Subgroup.center (Subgroup.centralizer ({d} : Set Y)) = ⊤ := by
    have hmap_top : (⊤ : Subgroup (Subgroup.centralizer ({d} : Set Y))).map
        (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y)))) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hmap_eq : ((LocalGroup F d).subgroupOf
        (Subgroup.centralizer ({d} : Set Y))).map
        (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y)))) =
        (⊤ : Subgroup (Subgroup.centralizer ({d} : Set Y))).map
        (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer ({d} : Set Y)))) := by
      rw [hmap_top]
      exact hMtop
    simpa [QuotientGroup.ker_mk'] using (Subgroup.map_eq_map_iff.mp hmap_eq)
  have hLtop : (LocalGroup F d).subgroupOf
      (Subgroup.centralizer ({d} : Set Y)) = ⊤ :=
    CFSG.Walter.eq_top_of_sup_center_eq_top hcommC hsup
  exact le_antisymm hLC (Subgroup.subgroupOf_eq_top.mp hLtop)

theorem hasType_localQuotient_simple_one {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    (hk : HasType 1 Y F) :
    ∀ d ∈ F, IsSimpleGroup (commutator (LocalQuotient F d)) ∧
      ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a := by
  intro d hd
  obtain ⟨ψ, -⟩ := exists_mulEquiv_carrier hH 1 hk
  have hLC : LocalGroup F d = Subgroup.centralizer ({d} : Set Y) :=
    localGroup_eq_centralizer_of_fi23 hH.pair ψ hd hk
  obtain ⟨e⟩ := Recognition.centralizer_quotient_of_fi23 hH.pair (k := 1) rfl ψ hd
  have iso : LocalQuotient F d ≃* Carrier 0 :=
    (Recognition.quotientCenterEquiv (MulEquiv.subgroupCongr hLC)).trans
      (show Subgroup.centralizer ({d} : Set Y) ⧸
          Subgroup.center (Subgroup.centralizer ({d} : Set Y)) ≃* Carrier 0 from e)
  obtain ⟨hZ0, hS0, D0, hD0, -, -, -⟩ :=
    CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 0
  have hHyp0 : Hyp (Carrier 0) D0 := ⟨pair_of_hasType hD0, hZ0, hS0⟩
  obtain ⟨a, b, hab⟩ := hasType_nonabelianCommutator hHyp0 hD0
  have hab' : (a : Carrier 0) * (b : Carrier 0) ≠ (b : Carrier 0) * (a : Carrier 0) :=
    fun h => hab (Subtype.ext h)
  have : IsSimpleGroup (Carrier 0) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  have hcommTop : commutator (Carrier 0) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (Carrier 0)) with h | h
    · exfalso
      exact hab' ((commutator_eq_bot_iff (Carrier 0)).1 h |>.is_comm.comm _ _)
    · exact h
  have hsimple : IsSimpleGroup (commutator (LocalQuotient F d)) :=
    Recognition.R3.isSimpleGroup_commutator_of_mulEquiv
      (A := Carrier 0) (B := LocalQuotient F d) iso.symm
  let eComm : commutator (Carrier 0) ≃* commutator (LocalQuotient F d) :=
    ((commutator (Carrier 0)).equivMapOfInjective
      (iso.symm : Carrier 0 →* LocalQuotient F d) iso.symm.injective).trans
      (MulEquiv.subgroupCongr (by
        change Subgroup.map (iso.symm : Carrier 0 →* LocalQuotient F d)
          ⁅(⊤ : Subgroup (Carrier 0)), ⊤⁆ = commutator (LocalQuotient F d)
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ iso.symm.surjective]
        rfl))
  refine ⟨hsimple, ⟨eComm a, eComm b, ?_⟩⟩
  intro h
  apply hab
  apply eComm.injective
  rw [map_mul, map_mul]
  exact h

theorem fi24_B_le_localGroup {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F)
    {d : Y} (hd : d ∈ F) (hk : HasType 2 Y F) {B : Subgroup Y}
    (eB : B ≃* Carrier 1)
    (hC : Subgroup.centralizer ({d} : Set Y) = Subgroup.zpowers d ⊔ B)
    (hinf : Subgroup.zpowers d ⊓ B = ⊥)
    (hdL : Subgroup.zpowers d ≤ Subgroup.centralizer (B : Set Y)) :
    B ≤ LocalGroup F d := by
  set C : Subgroup Y := Subgroup.centralizer ({d} : Set Y) with hCdef
  set A : Subgroup Y := Subgroup.zpowers d with hAdef
  have hC' : C = A ⊔ B := by simpa [C, A] using hC
  have hinf' : A ⊓ B = ⊥ := by simpa [A] using hinf
  have hdL' : A ≤ Subgroup.centralizer (B : Set Y) := by simpa [A] using hdL
  have hLC : LocalGroup F d ≤ C := by
    simpa [C] using Recognition.R3.localGroup_le_centralizer (E := F) d
  have hLnormal : ((LocalGroup F d).subgroupOf C).Normal := by
    simpa [C] using Recognition.R3.normal_localGroup_subgroupOf hP d
  have hdC : d ∈ C := by rw [Subgroup.mem_centralizer_singleton_iff]
  have hAC : A ≤ C := by rw [hC']; exact le_sup_left
  have hBC : B ≤ C := by rw [hC']; exact le_sup_right
  have hBnormal : (B.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hBC]
    intro b c hb hc
    have hCnorm : C ≤ Subgroup.normalizer (B : Set Y) := by
      rw [hC']
      exact sup_le (hdL'.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    exact (Subgroup.mem_normalizer_iff.1 (hCnorm hc) b).1 hb
  have hMnormal : ((LocalGroup F d ⊓ B).subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h b hh hb
    have hbC : b ∈ C := hBC hb
    exact ⟨(Subgroup.normal_subgroupOf_iff hLC).1 hLnormal h b hh.1 hbC,
      (Subgroup.normal_subgroupOf_iff hBC).1 hBnormal h b hh.2 hbC⟩
  have : IsSimpleGroup (Carrier 1) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have : IsSimpleGroup B := MulEquiv.isSimpleGroup (G := B) (H := Carrier 1) eB
  have : ((LocalGroup F d ⊓ B).subgroupOf B).Normal := hMnormal
  have hZB : Subgroup.center B = ⊥ := by
    have hZCarrier : Subgroup.center (Carrier 1) = ⊥ :=
      (CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 1).1
    have hmap := Subgroup.map_center_eq eB
    rw [hZCarrier] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eB.injective).1 hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((LocalGroup F d ⊓ B).subgroupOf B)
    with hbot | htop
  · exfalso
    have hMB : LocalGroup F d ⊓ B = ⊥ := by
      have hdisj : Disjoint (LocalGroup F d ⊓ B) B := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [← inf_eq_left.mpr inf_le_right]
      exact hdisj.eq_bot
    have hLnormC := (Subgroup.normal_subgroupOf_iff hLC).1 hLnormal
    have hBnormC := (Subgroup.normal_subgroupOf_iff hBC).1 hBnormal
    have hcomm : ∀ l ∈ LocalGroup F d, ∀ b ∈ B, l * b = b * l := by
      intro l hl b hb
      have hbC : b ∈ C := hBC hb
      have hmemL : ⁅l, b⁆ ∈ LocalGroup F d := by
        rw [commutatorElement_def]
        have hbL : b * l⁻¹ * b⁻¹ ∈ LocalGroup F d :=
          hLnormC (h := l⁻¹) (k := b) (inv_mem hl) hbC
        simpa [mul_assoc] using (LocalGroup F d).mul_mem hl hbL
      have hmemB : ⁅l, b⁆ ∈ B := by
        rw [commutatorElement_def]
        exact B.mul_mem (hBnormC (h := b) (k := l) hb (hLC hl)) (B.inv_mem hb)
      have hmem : ⁅l, b⁆ ∈ LocalGroup F d ⊓ B := ⟨hmemL, hmemB⟩
      rw [hMB, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    have hAc_le_center : A.subgroupOf C ≤ Subgroup.center C := by
      have hACent : ∀ c ∈ C, A ≤ Subgroup.centralizer ({c} : Set Y) := by
        intro c hc
        rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp (hACent c c.2 hx)).symm
    have hAc_normal : (A.subgroupOf C).Normal := Subgroup.normal_of_le_center hAc_le_center
    have hAcBc_top : A.subgroupOf C ⊔ B.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hAC hBC, hC', Subgroup.subgroupOf_self]
    have hL_le_A : LocalGroup F d ≤ A := by
      intro l hl
      have hlC : l ∈ C := hLC hl
      let lc : C := ⟨l, hlC⟩
      have hmem : lc ∈ A.subgroupOf C ⊔ B.subgroupOf C := by
        rw [hAcBc_top]
        exact Subgroup.mem_top lc
      obtain ⟨ac, hac, bc, hbc, hlc_eq⟩ := (Subgroup.mem_sup_of_normal_left).1 hmem
      have hlc_eqY : (ac : Y) * (bc : Y) = l := congrArg Subtype.val hlc_eq
      have hbc_center : (⟨(bc : Y), hbc⟩ : B) ∈ Subgroup.center B := by
        rw [Subgroup.mem_center_iff]
        intro b
        refine Subtype.ext ?_
        have hb_ac : (b : Y) * (ac : Y) = (ac : Y) * (b : Y) :=
          Subgroup.mem_centralizer_iff.mp (hdL' hac) b b.2
        have hb_ac_inv : (b : Y) * (ac : Y)⁻¹ = (ac : Y)⁻¹ * (b : Y) :=
          (Commute.inv_right (show Commute (b : Y) (ac : Y) from hb_ac)).eq
        have hb_l : (b : Y) * l = l * (b : Y) := (hcomm l hl b b.2).symm
        have hbc_eq : (bc : Y) = (ac : Y)⁻¹ * l := by
          rw [← hlc_eqY]
          group
        calc (b : Y) * bc = (b : Y) * ((ac : Y)⁻¹ * l) := by rw [hbc_eq]
          _ = ((b : Y) * (ac : Y)⁻¹) * l := by group
          _ = ((ac : Y)⁻¹ * (b : Y)) * l := by rw [hb_ac_inv]
          _ = (ac : Y)⁻¹ * ((b : Y) * l) := by group
          _ = (ac : Y)⁻¹ * (l * (b : Y)) := by rw [hb_l]
          _ = ((ac : Y)⁻¹ * l) * (b : Y) := by group
          _ = bc * (b : Y) := by rw [← hbc_eq]
      have hbc_bot : (bc : Y) = 1 := by
        have h := hbc_center
        rw [hZB, Subgroup.mem_bot] at h
        exact congrArg Subtype.val h
      rw [← hlc_eqY, hbc_bot, mul_one]
      exact hac
    obtain ⟨f, hf⟩ := HasType.localClass_nonempty hk hd
    have hfL : f ∈ LocalGroup F d := mem_localGroup hf
    have hfA : f ∈ A := hL_le_A hfL
    have hfA' : f ∈ Subgroup.zpowers d := by simpa [A] using hfA
    have hd_order : orderOf d = 2 := hP.2.2.1 d hd
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hd_order).1 hfA' with h | h
    · exact Pair.ne_one hP hf.1 h
    · exact hf.2.1 h
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left

theorem fi24_localQuotient_equiv {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F)
    {d : Y} (hd : d ∈ F) (hk : HasType 2 Y F) {B : Subgroup Y}
    (eB : B ≃* Carrier 1)
    (hC : Subgroup.centralizer ({d} : Set Y) = Subgroup.zpowers d ⊔ B)
    (hinf : Subgroup.zpowers d ⊓ B = ⊥)
    (hdL : Subgroup.zpowers d ≤ Subgroup.centralizer (B : Set Y)) :
    Nonempty (LocalQuotient F d ≃* Carrier 1) := by
  set L : Subgroup Y := LocalGroup F d with hLdef
  set A : Subgroup Y := Subgroup.zpowers d with hAdef
  set C : Subgroup Y := Subgroup.centralizer ({d} : Set Y) with hCdef
  have hC' : C = A ⊔ B := by simpa [C, A] using hC
  have hdL' : A ≤ Subgroup.centralizer (B : Set Y) := by simpa [A] using hdL
  have hLC : L ≤ C := by
    simpa [L, C] using Recognition.R3.localGroup_le_centralizer (E := F) d
  have hBL : B ≤ L := fi24_B_le_localGroup hP hd hk eB hC hinf hdL
  have hL_eq : L = (L ⊓ A) ⊔ B := by
    have hAnorm : A ≤ Subgroup.normalizer (B : Set Y) :=
      hdL'.trans (Subgroup.centralizer_le_normalizer _)
    have h := Subgroup.inf_sup_assoc_of_le (H := A) (K := L) (N := B) hAnorm hBL
    rw [← hC', inf_eq_left.mpr hLC] at h
    exact h.symm
  have hA'_le_center : A.subgroupOf L ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro l
    have hx' : (x : Y) ∈ A := hx
    have hlC : (l : Y) ∈ C := hLC l.2
    have hAl : A ≤ Subgroup.centralizer ({(l : Y)} : Set Y) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hlC).symm
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hAl hx')).symm
  have hsub : ((L ⊓ A) ⊔ B).subgroupOf L = ⊤ := by
    rw [← hL_eq, Subgroup.subgroupOf_self]
  have hsupAB : A.subgroupOf L ⊔ B.subgroupOf L = ⊤ := by
    rw [← Subgroup.inf_subgroupOf_left A L,
      ← Subgroup.subgroupOf_sup inf_le_left hBL, hsub]
  have hsup : B.subgroupOf L ⊔ Subgroup.center L = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup L) = A.subgroupOf L ⊔ B.subgroupOf L := hsupAB.symm
      _ ≤ Subgroup.center L ⊔ B.subgroupOf L :=
        sup_le (hA'_le_center.trans le_sup_left) le_sup_right
      _ = B.subgroupOf L ⊔ Subgroup.center L := sup_comm _ _
  have hZB : Subgroup.center B = ⊥ := by
    have hZCarrier : Subgroup.center (Carrier 1) = ⊥ :=
      (CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 1).1
    have hmap := Subgroup.map_center_eq eB
    rw [hZCarrier] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eB.injective).1 hmap
  have hdisj : B.subgroupOf L ⊓ Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxB : (x : Y) ∈ B := hx.1
    have hxZ : x ∈ Subgroup.center L := hx.2
    have hx_center_B : (⟨(x : Y), hxB⟩ : B) ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      show ((b : B) : Y) * (x : Y) = (x : Y) * ((b : B) : Y)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨(b : Y), hBL b.2⟩)
    rw [hZB, Subgroup.mem_bot] at hx_center_B
    have hxY : (x : Y) = 1 := congrArg Subtype.val hx_center_B
    exact Subtype.ext (by simpa using hxY)
  have hmul : ((B.subgroupOf L : Subgroup L) : Set L) *
      ((Subgroup.center L : Subgroup L) : Set L) = Set.univ := by
    rw [← Subgroup.mul_normal (B.subgroupOf L) (Subgroup.center L), hsup]
    rfl
  have hcompl : (B.subgroupOf L).IsComplement' (Subgroup.center L) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (by rw [disjoint_iff]; exact hdisj) hmul
  exact ⟨hcompl.QuotientMulEquiv.trans
    ((Subgroup.subgroupOfEquivOfLe hBL).trans eB)⟩

theorem hasType_localQuotient_simple_two {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    (hk : HasType 2 Y F) :
    ∀ d ∈ F, IsSimpleGroup (commutator (LocalQuotient F d)) ∧
      ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a := by
  intro d hd
  obtain ⟨ψ, -⟩ := exists_mulEquiv_carrier hH 2 hk
  obtain ⟨B, ⟨eBraw⟩, hC, hinf, hdL⟩ :=
    Recognition.centralizer_of_fi24 hH.pair (k := 2) rfl ψ hd
  let eB : B ≃* Carrier 1 := eBraw
  obtain ⟨iso⟩ := fi24_localQuotient_equiv hH.pair hd hk eB hC hinf hdL
  obtain ⟨hZ1, hS1, D1, hD1, -, -, -⟩ :=
    CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 1
  have hHyp1 : Hyp (Carrier 1) D1 := ⟨pair_of_hasType hD1, hZ1, hS1⟩
  obtain ⟨a, b, hab⟩ := hasType_nonabelianCommutator hHyp1 hD1
  have hab' : (a : Carrier 1) * (b : Carrier 1) ≠ (b : Carrier 1) * (a : Carrier 1) :=
    fun h => hab (Subtype.ext h)
  have : IsSimpleGroup (Carrier 1) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hcommTop : commutator (Carrier 1) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (Carrier 1)) with h | h
    · exfalso
      exact hab' ((commutator_eq_bot_iff (Carrier 1)).1 h |>.is_comm.comm _ _)
    · exact h
  have eComm : commutator (Carrier 1) ≃* commutator (LocalQuotient F d) :=
    ((commutator (Carrier 1)).equivMapOfInjective
      (iso.symm : Carrier 1 →* LocalQuotient F d) iso.symm.injective).trans
      (MulEquiv.subgroupCongr (by
        change Subgroup.map (iso.symm : Carrier 1 →* LocalQuotient F d)
          ⁅(⊤ : Subgroup (Carrier 1)), ⊤⁆ = commutator (LocalQuotient F d)
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ iso.symm.surjective]
        rfl))
  have : IsSimpleGroup (commutator (Carrier 1)) := hS1
  have hsimple : IsSimpleGroup (commutator (LocalQuotient F d)) :=
    Recognition.R3.isSimpleGroup_commutator_of_mulEquiv
      (A := Carrier 1) (B := LocalQuotient F d) iso.symm
  refine ⟨hsimple, ⟨eComm a, eComm b, ?_⟩⟩
  intro h
  apply hab
  apply eComm.injective
  rw [map_mul, map_mul]
  exact h

theorem hasType_localQuotient_simple {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    {k : Fin 3} (hk : HasType k Y F) :
    ∀ d ∈ F, IsSimpleGroup (commutator (LocalQuotient F d)) ∧
      ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a := by
  obtain ⟨_ | _ | n, hk'⟩ := k
  · exact hasType_localQuotient_simple_zero hk
  · exact hasType_localQuotient_simple_one hH hk
  · exact hasType_localQuotient_simple_two hH hk

theorem hasType_tripleProperty_one {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    (hk : HasType 1 Y F) : TripleProperty F := by
  refine hasType_tripleProperty_of_local hH hk ?_
  intro d hd
  have h22 : F22 (LocalQuotient F d) (LocalImages F d) := F23_local hk hd
  have hZH : Subgroup.center (LocalQuotient F d) = ⊥ :=
    Pair.center_localQuotient hH.pair hH.center hH.simple hd
  have hSH : IsSimpleGroup (commutator (LocalQuotient F d)) :=
    (hasType_localQuotient_simple_one hH hk d hd).1
  exact hasType_tripleProperty_zero ⟨h22.1, hZH, hSH⟩ h22

theorem hasType_tripleProperty_two {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    (hk : HasType 2 Y F) : TripleProperty F := by
  refine hasType_tripleProperty_of_local hH hk ?_
  intro d hd
  have h23 : F23 (LocalQuotient F d) (LocalImages F d) := F24_local hk hd
  have hZH : Subgroup.center (LocalQuotient F d) = ⊥ :=
    Pair.center_localQuotient hH.pair hH.center hH.simple hd
  have hSH : IsSimpleGroup (commutator (LocalQuotient F d)) :=
    (hasType_localQuotient_simple_two hH hk d hd).1
  exact hasType_tripleProperty_one ⟨h23.1, hZH, hSH⟩ h23

theorem hasType_tripleProperty {Y : Type} [Group Y] {F : Set Y} (hH : Hyp Y F)
    {k : Fin 3} (hk : HasType k Y F) : TripleProperty F := by
  obtain ⟨_ | _ | n, hk'⟩ := k
  · exact hasType_tripleProperty_zero hH hk
  · exact hasType_tripleProperty_one hH hk
  · exact hasType_tripleProperty_two hH hk

end Certificates

end CFSG.Fischer.Classification
