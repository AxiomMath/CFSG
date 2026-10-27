module

public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_mul_two_pow_finrank_fix (H : Hyp4 S g) (C : Cons311 S g) {K : Subgroup S.O}
    (hK : K ≤ S.Lbar g) :
    Nat.card K * 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) =
      2 ^ S.width := by
  have hdim := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have haP : S.cl (g * S.z * g⁻¹) ∈ P := cl_mem_clSub_self H.conj_mem
  have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ P :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr haP
  have hinv : ∀ (x : K) u, u ∈ P →
      ((S.O.subtype.comp K.subtype) x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ P := by
    intro x u hu
    have h1 := hspan (Lbar_apply_sub_mem_span' H.conj_mem hu (hK x.2))
    have e : ((S.O.subtype.comp K.subtype) x : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
        ((((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) + u) := by
      change ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = _
      abel
    rw [e]
    exact add_mem h1 hu
  set ψ := restrictHom (S.O.subtype.comp K.subtype) P hinv with hψ
  have hψc : ∀ x (u : P), ψ x u - u ∈ (ZMod 2) ∙ (⟨S.cl (g * S.z * g⁻¹), haP⟩ : P) := by
    intro x u
    rw [mem_span_singleton_subtype]
    exact Lbar_apply_sub_mem_span' H.conj_mem u.2 (hK x.2)
  have hKp : IsPGroup 2 K := (isPGroup_Lbar S H.conj_mem).to_le hK
  obtain ⟨h1, -⟩ := card_range_of_transvections hKp ψ _ hψc
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψ, restrictHom_eq_one_iff] at hx
    exact Subtype.ext (C.faithful _ (hK x.2) fun v hv => hx v hv)
  have hcard : Nat.card ψ.range = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfix : (fixSpaceOf ψ.range).map P.subtype = P ⊓ fixSub S K := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      change u ∈ fixSpaceOf ψ.range at hu
      rw [mem_fixSpaceOf_range] at hu
      refine ⟨u.2, fun x hx => ?_⟩
      exact congrArg Subtype.val (hu ⟨x, hx⟩)
    · rintro ⟨hvP, hvK⟩
      refine ⟨⟨v, hvP⟩, ?_, rfl⟩
      change _ ∈ fixSpaceOf ψ.range
      rw [mem_fixSpaceOf_range]
      intro x
      exact Subtype.ext (hvK x x.2)
  have hf := Submodule.finrank_map_subtype_eq P (fixSpaceOf ψ.range)
  rw [hfix] at hf
  have hle : finrank (ZMod 2) (fixSpaceOf ψ.range) ≤ finrank (ZMod 2) P :=
    Submodule.finrank_le _
  rw [← hcard, h1, hf, ← pow_add]
  congr 1
  omega

@[expose] def RadBound (S : Setting G) (g : G) (t : S.O) : Prop :=
  Nat.card (S.Lbar g) ≤
    2 ^ (finrank (ZMod 2) (Vt S g t) - 2) * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O)

section Pair

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)

omit [Finite G] in
theorem cl_not_mem_clSub_of_not_mem {g' x : G} (hz : S.z ∈ S.Qa g') (hxQ : x ∈ S.QG)
    (hx : x ∉ S.Qa g') : S.cl x ∉ S.clSub (S.QG ⊓ S.Qa g') := by
  intro hmem
  obtain ⟨y, hy, hyQ, hyx⟩ := S.mem_clSub_iff.mp hmem
  rcases (S.cl_eq_cl_iff hyQ hxQ).mp hyx with rfl | rfl
  · exact hx hy.2
  · exact hx ((S.Qa g').mul_mem hy.2 hz)

include H ht hh in
theorem mem_Lbar_of_pair : t ∈ S.Lbar ((h : G) * g) := mem_Lbar_mul_of_mem_Rbar H ht hh

include H hb in
theorem cl_b_not_mem : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa g) :=
  cl_not_mem_clSub_of_not_mem (S.z_mem_Qa H.conj_mem H.conj_ne) (conj_mem_QG' S h.2 H.conj_mem)
    hb

include H hb in
theorem cl_a_not_mem : S.cl (g * S.z * g⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) :=
  S.cl_not_mem_clSub_of_not_mem_Qa H.conj_mem H.conj_ne h.2 hb

include H ht hh hb in
theorem two_le_finrank_Vt' : 2 ≤ finrank (ZMod 2) (Vt S g t) := by
  have hth := mem_Lbar_of_pair H ht hh
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have hlt : P ⊓ Vt S g t < Vt S g t :=
    lt_of_le_of_ne inf_le_right fun heq => cl_b_not_mem H hb (heq ▸ cl_mem_Vt hth).1
  have hne : P ⊓ Vt S g t ≠ ⊥ := by
    intro h0
    have : S.cl (g * S.z * g⁻¹) ∈ P ⊓ Vt S g t := ⟨cl_mem_clSub_self H.conj_mem, cl_a_mem_Vt ht⟩
    rw [h0, Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 0 < finrank (ZMod 2) ↥(P ⊓ Vt S g t) :=
    Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  omega

include H ht hh hb in
theorem fix_of_mem_inf {k : S.O} (hk : k ∈ S.Lbar g ⊓ Nbar S g t) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g))) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hth := mem_Lbar_of_pair H ht hh
  have h1 := Lbar_apply_sub_mem_span' H.conj_mem hv.1 hk.1
  have h2 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) :=
    sub_mem (Nbar_apply_mem_clSub (conj_mem_QG' S h.2 H.conj_mem) (conj_ne_z' S h.2 H.conj_ne)
      (cl_mem_Vt hth) hk.2 hv.2) hv.2
  rcases mem_span_cl_iff.mp h1 with h0 | ha
  · exact sub_eq_zero.mp h0
  · exact absurd (ha ▸ h2) (cl_a_not_mem H hb)

include H C ht ht1 hVQ hh hb in
theorem clSub_inf_clSub_le_Vt (hR : RadBound S g t) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t := by
  have h1 := card_mul_two_pow_finrank_fix H C
    (inf_le_left : S.Lbar g ⊓ Nbar S g t ≤ S.Lbar g)
  have h2 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have h3 := two_le_finrank_Vt' H ht hh hb
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set K := S.Lbar g ⊓ Nbar S g t with hK
  have hL := C.card_Lbar
  have hn := H.two_lt_width
  have hle : P ⊓ Vt S g t ≤ P ⊓ fixSub S K := fun v hv =>
    ⟨hv.1, fun k hk => (mem_Nbar.mp hk.2).2 v hv.2⟩
  have hdim : finrank (ZMod 2) ↥(P ⊓ fixSub S K) ≤ finrank (ZMod 2) ↥(P ⊓ Vt S g t) := by
    have hR' : 2 ^ (S.width - 1) ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) * Nat.card K := by
      rw [← hL]
      exact hR
    by_contra hcon
    push Not at hcon
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h4 : 2 ^ (S.width - 1) * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S K) ≤
        2 ^ (finrank (ZMod 2) (Vt S g t) - 2) * 2 ^ S.width := by
      rw [← h1]
      calc 2 ^ (S.width - 1) * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S K)
          ≤ (2 ^ (finrank (ZMod 2) (Vt S g t) - 2) * Nat.card K) *
              2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S K) := Nat.mul_le_mul_right _ hR'
        _ = _ := by ring
    rw [← pow_add, ← pow_add] at h4
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
    omega
  have heq : P ⊓ Vt S g t = P ⊓ fixSub S K := Submodule.eq_of_le_of_finrank_le hle hdim
  intro v hv
  have : v ∈ P ⊓ fixSub S K := ⟨hv.1, fun k hk => fix_of_mem_inf H ht hh hb hk hv⟩
  rw [← heq] at this
  exact this.2

theorem apply_sub_mem_clSub_of_mem_Wt {g' : G} (C' : Cons311 S g') {t : S.O}
    (hbV : S.cl (g' * S.z * g'⁻¹) ∈ Vt S g t) (hbQ : g' * S.z * g'⁻¹ ∈ S.QG) {w : S.Qt}
    (hw : w ∈ Wt S g t) {k : S.O} (hk : k ∈ S.Lbar g') :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa g') := by
  obtain ⟨w', hw'Q, rfl⟩ := S.exists_cl w
  have hpol := mem_Wt.mp hw _ hbV
  have hc := (S.polar_cl_eq_zero_iff hbQ hw'Q).mp hpol
  exact C'.comm_le w' ⟨hw'Q, mem_centralizer_singleton_iff.mpr hc.symm⟩ k hk

theorem apply_sub_mem_Vt_of_decomp {g₁ g₂ : G} (C₁ : Cons311 S g₁) {t : S.O}
    (h1Q : g₁ * S.z * g₁⁻¹ ∈ S.QG) (h1V : S.cl (g₁ * S.z * g₁⁻¹) ∈ Vt S g t)
    (h2Q : g₂ * S.z * g₂⁻¹ ∈ S.QG) (h2z : g₂ * S.z * g₂⁻¹ ≠ S.z)
    (h2V : S.cl (g₂ * S.z * g₂⁻¹) ∈ Vt S g t)
    (hdec : (S.clSub (S.QG ⊓ S.Qa g₁) ⊓ Wt S g t) ⊔ (S.clSub (S.QG ⊓ S.Qa g₂) ⊓ Wt S g t) =
      Wt S g t)
    (hP : S.clSub (S.QG ⊓ S.Qa g₁) ⊓ S.clSub (S.QG ⊓ S.Qa g₂) ≤ Vt S g t)
    {k : S.O} (hk : k ∈ S.Lbar g₁ ⊓ Nbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  rw [← hdec] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add, show (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x + (k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - (x + y) =
    ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) by abel]
  refine add_mem ?_ (hP ⟨apply_sub_mem_clSub_of_mem_Wt C₁ h1V h1Q hy.2 hk.1,
    sub_mem (Nbar_apply_mem_clSub h2Q h2z h2V hk.2 hy.1) hy.1⟩)
  have h1 := Lbar_apply_sub_mem_span' h1Q hx.1 hk.1
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr h1V h1

end Pair

theorem finrank_sup_Vt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) = S.width := by
  have h1 := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have h2 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) (Vt S g t)
  have e : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊓ Vt S g t = S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t :=
    by rw [inf_assoc, inf_eq_right.mpr (Vt_le_Wt H ht1)]
  rw [e] at h3
  omega

section Pair2

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include H C ht ht1 hVQ hh hb

theorem sup_eq_Wt
    (hP : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t) :
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) =
      Wt S g t := by
  have hth := mem_Lbar_of_pair H ht hh
  have d1 := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have d2 := finrank_clSub_inf_Wt (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
  rw [Wt_mul] at d2
  have e := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have fW := finrank_Wt (S := S) (g := g) (t := t)
  have fQ := S.finrank_Qt_eq_two_mul_width
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t)
  have hlt : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) < S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    refine lt_of_le_of_ne (fun v hv => ⟨hv.1.1, hP ⟨hv.1.1, hv.2.1⟩⟩) fun heq => ?_
    have ha : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t :=
      ⟨cl_mem_clSub_self H.conj_mem, cl_a_mem_Vt ht⟩
    rw [← heq] at ha
    exact cl_a_not_mem H hb ha.2.1
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  refine Submodule.eq_of_le_of_finrank_le (sup_le inf_le_right inf_le_right) ?_
  omega

theorem apply_sub_mem_Vt_a
    (hP : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t)
    {k : S.O} (hk : k ∈ S.Lbar g ⊓ Nbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t :=
  apply_sub_mem_Vt_of_decomp C H.conj_mem (cl_a_mem_Vt ht) (conj_mem_QG' S h.2 H.conj_mem)
    (conj_ne_z' S h.2 H.conj_ne) (cl_mem_Vt (mem_Lbar_of_pair H ht hh))
    (sup_eq_Wt H C ht ht1 hVQ hh hb hP) (hP) hk hw

theorem apply_sub_mem_Vt_b
    (hP : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t) {k : S.O}
    (hk : k ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t :=
  apply_sub_mem_Vt_of_decomp (C.mul h) (conj_mem_QG' S h.2 H.conj_mem)
    (cl_mem_Vt (mem_Lbar_of_pair H ht hh)) H.conj_mem H.conj_ne (cl_a_mem_Vt ht)
    (by rw [sup_comm]; exact sup_eq_Wt H C ht ht1 hVQ hh hb hP)
    (by rw [inf_comm]; exact hP) hk hw

theorem sup_Vt_inf_sup_Vt
    (hP : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t) :
    ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊓
      ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) = Vt S g t := by
  have hth := mem_Lbar_of_pair H ht hh
  have d1 := finrank_sup_Vt H C ht ht1 hVQ
  have d2 := finrank_sup_Vt (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
  rw [Wt_mul, Vt_mul] at d2
  have fW := finrank_Wt (S := S) (g := g) (t := t)
  have fQ := S.finrank_Qt_eq_two_mul_width
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb hP
  have hsup : ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊔
      ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) = Wt S g t := by
    refine le_antisymm (sup_le (sup_le inf_le_right (Vt_le_Wt H ht1))
      (sup_le inf_le_right (Vt_le_Wt H ht1))) ?_
    conv_lhs => rw [← hdec]
    exact sup_le_sup le_sup_left le_sup_left
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t)
    ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t)
  rw [hsup] at hsum
  refine (Submodule.eq_of_le_of_finrank_le (le_inf le_sup_right le_sup_right) ?_).symm
  omega

end Pair2

end CFSG.LargeExtraspecial.S6
