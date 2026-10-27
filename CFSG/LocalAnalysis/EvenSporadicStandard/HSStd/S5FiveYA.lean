module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYM12Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSideT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveHarada

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_mem_of_sup_zpowers {L : Subgroup G} {t : G}
    (ht : ∀ x ∈ L, x * t = t * x) {x y : G} (hx : x ∈ L ⊔ zpowers t)
    (hy : y ∈ L ⊔ zpowers t) : ⁅x, y⁆ ∈ L := by
  have hc : ∀ h ∈ L, ∀ k ∈ zpowers t, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute h t from ht h hh) m).eq
  obtain ⟨l₁, hl₁, a, ha, rfl⟩ := mem_sup_of_commute hc hx
  obtain ⟨l₂, hl₂, b, hb, rfl⟩ := mem_sup_of_commute hc hy
  have ha2 : Commute a l₂ := (show Commute l₂ a from hc l₂ hl₂ a ha).symm
  have hb1 : Commute b l₁⁻¹ := (Commute.inv_left (show Commute l₁ b from hc l₁ hl₁ b hb)).symm
  have hab : Commute a b := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact Commute.zpow_zpow_self t m n
  have e1 : a * (l₂ * b) * a⁻¹ = l₂ * b := by
    rw [(ha2.mul_right hab).eq, mul_inv_cancel_right]
  have e2 : b * l₁⁻¹ * b⁻¹ = l₁⁻¹ := by
    rw [hb1.eq, mul_inv_cancel_right]
  have : ⁅l₁ * a, l₂ * b⁆ = ⁅l₁, l₂⁆ := by
    calc ⁅l₁ * a, l₂ * b⁆ = l₁ * (a * (l₂ * b) * a⁻¹) * l₁⁻¹ * (l₂ * b)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = l₁ * (l₂ * b) * l₁⁻¹ * (l₂ * b)⁻¹ := by rw [e1]
      _ = l₁ * l₂ * (b * l₁⁻¹ * b⁻¹) * l₂⁻¹ := by group
      _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [e2]
      _ = ⁅l₁, l₂⁆ := by rw [commutatorElement_def]
  rw [this, commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)

@[expose] def qHom (r t : G) :
    ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G)) →* HSFiveBar G r :=
  (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer ({r} : Set G)))).comp
    (Subgroup.inclusion (inf_le_right : centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) ≤
      centralizer ({r} : Set G)))

theorem qHom_apply (r t : G) (x : ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G))) :
    qHom r t x = QuotientGroup.mk (⟨(x : G), x.2.2⟩ : ↥(centralizer ({r} : Set G))) := rfl

theorem card_omega :
    Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) = 1200 := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Fintype.card_perm, Fintype.card_fin, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)),
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 5)), Fintype.card_multiplicative,
    Fintype.card_multiplicative, ZMod.card, ZMod.card]
  rfl

theorem card_z2_s5 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) = 240 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Fintype.card_perm, Fintype.card_fin, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)),
    Fintype.card_multiplicative, ZMod.card]
  rfl

section Main

variable [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}

theorem u₁_mem_commutator
    (M : HS100Model)
    (h : HSOuterSetup G L t S z n v s) {r u₁ u₂ : G} (tr : FiveTriple L v r u₁ u₂) :
    ∃ hu : u₁ ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G),
      (⟨u₁, hu⟩ : ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G))) ∈
        commutator ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G)) := by
  classical
  obtain ⟨eQ⟩ := centralizer_five_t M h tr
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have htL : t ∉ L := by
    intro htl
    have hZ : center L = ⊥ := M.center_eq_bot L h.setting.2.1
    have h1 : (⟨t, htl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (htcomm g g.2)
    rw [hZ, mem_bot] at h1
    exact h.t_ne_one (congrArg Subtype.val h1)
  have htr : t ∈ centralizer ({r} : Set G) :=
    mem_centralizer_singleton_iff.2 (htcomm r tr.r_mem).symm
  have htQ : t ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 rfl, htr⟩
  have hrQ : r ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 (htcomm r tr.r_mem), mem_centralizer_singleton_iff.2 rfl⟩
  have hu : u₁ ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 (htcomm u₁ tr.u₁_mem),
      mem_centralizer_singleton_iff.2 tr.u₁_r⟩
  have hvQ : v ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 h.t_comm_v.symm,
      mem_centralizer_singleton_iff.2 tr.r_comm.symm⟩
  refine ⟨hu, ?_⟩
  set Q : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) with hQ
  have hcard : Nat.card ↥Q = 1200 := (Nat.card_congr eQ.toEquiv).trans card_omega
  let ι₃ : Equiv.Perm (Fin 5) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 5) ×
      Equiv.Perm (Fin 5) :=
    (MonoidHom.inr _ _).comp (MonoidHom.inr _ _)
  have hι₃ : Function.Injective ι₃ := fun a b hab => by simpa [ι₃] using hab
  let f : Equiv.Perm (Fin 5) →* ↥Q := eQ.symm.toMonoidHom.comp ι₃
  have hf : Function.Injective f := eQ.symm.injective.comp hι₃
  have htc : (⟨t, htQ⟩ : ↥Q) ∈ center ↥Q := by
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.1 q.2.1)
  have hrc : (⟨r, hrQ⟩ : ↥Q) ∈ center ↥Q := by
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.1 q.2.2)
  have hidx : ((L ⊔ zpowers t).subgroupOf Q).index = 2 := by
    have hle : (L ⊔ zpowers t).relIndex Q ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := L ⊔ zpowers t)
        (inf_le_left : Q ≤ centralizer ({t} : Set G)) (by rw [h.index]; norm_num)
      rwa [h.index] at this
    have hne1 : (L ⊔ zpowers t).relIndex Q ≠ 1 := by
      intro h1
      exact h.ctx.v_outer (Subgroup.relIndex_eq_one.1 h1 hvQ)
    have hne0 : (L ⊔ zpowers t).relIndex Q ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (L ⊔ zpowers t) Q) Nat.card_pos).ne'
    show (L ⊔ zpowers t).relIndex Q = 2
    omega
  refine mem_commutator_of_index_two (QL := L.subgroupOf Q) hcard f hf htc (Subtype.ext h.t_sq)
    (fun h1 => h.t_ne_one (congrArg Subtype.val h1)) hrc
    ((Subgroup.orderOf_mk r hrQ).trans tr.r_ord) hidx ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact mem_subgroupOf.2 (mem_sup_right (mem_zpowers t))
  · exact mem_subgroupOf.2 (mem_sup_left tr.r_mem)
  · intro x hx
    exact mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx))
  · exact fun hh => htL (mem_subgroupOf.1 hh)
  · intro x hx y hy
    exact mem_subgroupOf.2 (commutator_mem_of_sup_zpowers htcomm (mem_subgroupOf.1 hx)
      (mem_subgroupOf.1 hy))
  · exact mem_subgroupOf.2 tr.u₁_mem
  · exact Subtype.ext tr.u₁_sq

theorem exists_conj_t_tu
    (M : HS100Model) (h : HSOuterSetup G L t S z n v s) {r u₁ u₂ : G}
    (tr : FiveTriple L v r u₁ u₂) (hM12 : IsSporadic (HSFiveBar G r) .M12) :
    ∃ g : G, g * t * g⁻¹ = t * u₁ := by
  classical
  obtain ⟨hu, hcomm⟩ := u₁_mem_commutator M h tr
  obtain ⟨Ct⟩ := centralizer_five_t M h tr
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have htr : t ∈ centralizer ({r} : Set G) :=
    mem_centralizer_singleton_iff.2 (htcomm r tr.r_mem).symm
  have hu1r : u₁ ∈ centralizer ({r} : Set G) := mem_centralizer_singleton_iff.2 tr.u₁_r
  have htu : t * u₁ = u₁ * t := (htcomm u₁ tr.u₁_mem).symm
  have htu1r : t * u₁ ∈ centralizer ({r} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc t * u₁ * r = t * (u₁ * r) := by rw [mul_assoc]
      _ = t * (r * u₁) := by rw [tr.u₁_r]
      _ = (t * r) * u₁ := by rw [mul_assoc]
      _ = (r * t) * u₁ := by rw [(htcomm r tr.r_mem).symm]
      _ = r * (t * u₁) := by rw [mul_assoc]
  obtain ⟨e⟩ := good_bar tr.r_ord htr h.t_sq h.t_ne_one Ct
  obtain ⟨φ⟩ := hM12
  let φ' : HSFiveBar G r ≃* ↥NativeSporadic.M12 := φ
  set tb : HSFiveBar G r := fiveBar htr with htb
  set ub : HSFiveBar G r := fiveBar hu1r with hub
  have htb2 : tb * tb = 1 := by
    rw [htb, fiveBar, ← QuotientGroup.mk_mul]
    have : (⟨t, htr⟩ * ⟨t, htr⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext h.t_sq
    rw [this, QuotientGroup.mk_one]
  have hub2 : ub * ub = 1 := by
    rw [hub, fiveBar, ← QuotientGroup.mk_mul]
    have : (⟨u₁, hu1r⟩ * ⟨u₁, hu1r⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext tr.u₁_sq
    rw [this, QuotientGroup.mk_one]
  have htbne : tb ≠ 1 := fun h1 => by
    have := orderOf_fiveBar htr h.t_sq h.t_ne_one
    rw [← htb, h1, orderOf_one] at this
    omega
  have hmap : (commutator ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G))).map
      (qHom r t) ≤ ⁅centralizer ({tb} : Set (HSFiveBar G r)),
        centralizer ({tb} : Set (HSFiveBar G r))⁆ := by
    have hrange : (qHom r t).range ≤ centralizer ({tb} : Set (HSFiveBar G r)) := by
      rintro _ ⟨x, rfl⟩
      rw [mem_centralizer_singleton_iff, qHom_apply, htb, fiveBar, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1)
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top]
    exact commutator_mono hrange hrange
  have hubC : ub ∈ ⁅centralizer ({tb} : Set (HSFiveBar G r)),
      centralizer ({tb} : Set (HSFiveBar G r))⁆ :=
    hmap (Subgroup.mem_map_of_mem (qHom r t) hcomm)
  have hC : Nat.card ↥(centralizer ({φ' tb} : Set ↥NativeSporadic.M12)) = 240 := by
    rw [← Nat.card_congr (centralizerSingletonEquiv φ' tb).toEquiv,
      Nat.card_congr e.toEquiv, card_z2_s5]
  have hbC : φ' ub ∈ ⁅centralizer ({φ' tb} : Set ↥NativeSporadic.M12),
      centralizer ({φ' tb} : Set ↥NativeSporadic.M12)⁆ := by
    have := Subgroup.mem_map_of_mem φ'.toMonoidHom hubC
    rwa [Subgroup.map_commutator, map_centralizer_equiv] at this
  have hconj := m12_fusion (a := φ' tb) (b := φ' ub) (by rw [← map_mul, htb2, map_one])
    (fun h1 => htbne (φ'.injective (h1.trans (map_one φ').symm))) hC hbC
    (by rw [← map_mul, hub2, map_one])
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hmk : (QuotientGroup.mk (⟨t * u₁, htu1r⟩ : ↥(centralizer ({r} : Set G))) :
      HSFiveBar G r) = tb * ub := by
    rw [htb, hub, fiveBar, fiveBar, ← QuotientGroup.mk_mul]
    rfl
  have hx2 : (⟨t, htr⟩ * ⟨t, htr⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext h.t_sq
  have hx2' : (⟨t * u₁, htu1r⟩ * ⟨t * u₁, htu1r⟩ : ↥(centralizer ({r} : Set G))) = 1 := by
    apply Subtype.ext
    show t * u₁ * (t * u₁) = 1
    calc t * u₁ * (t * u₁) = t * (u₁ * t) * u₁ := by group
      _ = t * (t * u₁) * u₁ := by rw [← htu]
      _ = (t * t) * (u₁ * u₁) := by group
      _ = 1 := by rw [h.t_sq, tr.u₁_sq, one_mul]
  obtain ⟨g, hg⟩ := exists_conj_of_mk_conj hx2 hx2' ⟨(φ'.symm c)⁻¹, by
    rw [hmk]
    have h1 : φ' (φ'.symm c * (tb * ub) * (φ'.symm c)⁻¹) = φ' tb := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_mul]
      exact hc
    have h2 := φ'.injective h1
    calc (φ'.symm c)⁻¹ * tb * (φ'.symm c)⁻¹⁻¹ = (φ'.symm c)⁻¹ *
          (φ'.symm c * (tb * ub) * (φ'.symm c)⁻¹) * φ'.symm c := by rw [h2, inv_inv]
      _ = tb * ub := by group⟩
  exact ⟨(g : G), congrArg Subtype.val hg⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.FiveY
