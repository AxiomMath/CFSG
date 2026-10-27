module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusP42Perm
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CentCard
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42

open Equiv Subgroup AltStdCycTwo AltStdBal MulAction

section Elements

variable {G : Type} [Group G] {L : Subgroup G} (θ : L ≃* alternatingGroup (Fin 9))

@[expose] def bL (k : Fin 16) : L := θ.symm ⟨bEl k, bEl_mem_alternatingGroup k⟩

@[expose] def bG (k : Fin 16) : G := (bL θ k : G)

theorem bG_mem (k : Fin 16) : bG θ k ∈ L := (bL θ k).2

theorem bL_mul (k l : Fin 16) : bL θ k * bL θ l = bL θ (bxor k l) := by
  unfold bL
  rw [← map_mul]
  congr 1
  exact Subtype.ext (bEl_mul k l)

theorem bG_mul (k l : Fin 16) : bG θ k * bG θ l = bG θ (bxor k l) := by
  unfold bG
  rw [← Subgroup.coe_mul, bL_mul]

theorem bG_zero : bG θ 0 = 1 := by
  unfold bG bL
  rw [show (⟨bEl 0, bEl_mem_alternatingGroup 0⟩ : alternatingGroup (Fin 9)) = 1 from
    Subtype.ext bEl_zero, map_one, Subgroup.coe_one]

theorem theta_bL (k : Fin 16) :
    ((θ (bL θ k) : alternatingGroup (Fin 9)) : Perm (Fin 9)) = bEl k := by
  simp [bL]

theorem bG_injective : Function.Injective (bG θ) := by
  intro k l h
  have h1 : bL θ k = bL θ l := Subtype.ext h
  apply bEl_injective
  rw [← theta_bL θ k, ← theta_bL θ l, h1]

theorem eq_bL_of_mem {l : L} (h : ((θ l : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ bBar) :
    ∃ k, bL θ k = l := by
  obtain ⟨k, hk⟩ := mem_bBar_iff.1 h
  refine ⟨k, θ.injective (Subtype.ext ?_)⟩
  rw [theta_bL, hk]

theorem mem_bSub_iff {y : G} : y ∈ bSub θ ↔ ∃ k, bG θ k = y := by
  constructor
  · intro hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hl
    obtain ⟨k, hk⟩ := mem_bBar_iff.1 (Subgroup.mem_comap.1 ha)
    have h1 : a = ⟨bEl k, bEl_mem_alternatingGroup k⟩ := Subtype.ext hk.symm
    subst h1
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact Subgroup.mem_map.2 ⟨bL θ k, Subgroup.mem_map.2
      ⟨⟨bEl k, bEl_mem_alternatingGroup k⟩, Subgroup.mem_comap.2 (bEl_mem_bBar k), rfl⟩, rfl⟩

theorem w_eq_bG : w θ le89 = bG θ 5 := by
  unfold w bG bL
  congr 2
  apply Subtype.ext
  rw [coe_wBar, tr_one_eq_bEl]

end Elements

section Config

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin 9)}
  {z : G}

theorem bG_comm (c : Config G L Q 9 θ z) (k : Fin 16) : bG θ k * z = z * bG θ k :=
  mem_centralizer_singleton_iff.1 (le_cent_single c.ot.std c.ot.cyc (bG_mem θ k))

theorem z_mul_z (c : Config G L Q 9 θ z) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [c.ot.cyc.order, sq] at h

theorem z_not_mem_L (c : Config G L Q 9 θ z) : z ∉ L := by
  have h := not_conj_mem_L c.ot.std θ le89 c.ot.cyc c.ot.card 1
  simpa using h

variable (θ z) in
@[expose] def vElt (ω : Om) : G := bG θ ω.1 * cond ω.2 z 1

theorem vElt_false (k : Fin 16) : vElt θ z (k, false) = bG θ k := by
  simp [vElt]

theorem vElt_true (k : Fin 16) : vElt θ z (k, true) = bG θ k * z := by
  simp [vElt]

theorem vElt_mem (ω : Om) : vElt θ z ω ∈ vSub θ z := by
  obtain ⟨k, b⟩ := ω
  have hb : bG θ k ∈ vSub θ z := mem_sup_left ((mem_bSub_iff θ).2 ⟨k, rfl⟩)
  cases b
  · rw [vElt_false]
    exact hb
  · rw [vElt_true]
    exact mul_mem hb (mem_sup_right (mem_zpowers z))

theorem conj_vElt {g : G} {k l : Fin 16} (hk : g * bG θ k * g⁻¹ = bG θ l) (hz : g * z * g⁻¹ = z)
    (b : Bool) : g * vElt θ z (k, b) * g⁻¹ = vElt θ z (l, b) := by
  cases b
  · rw [vElt_false, vElt_false, hk]
  · rw [vElt_true, vElt_true]
    calc g * (bG θ k * z) * g⁻¹ = (g * bG θ k * g⁻¹) * (g * z * g⁻¹) := by group
      _ = bG θ l * z := by rw [hk, hz]

private theorem vElt_mul_mem (c : Config G L Q 9 θ z) (ω ω' : Om) :
    ∃ ω'' : Om, vElt θ z ω * vElt θ z ω' = vElt θ z ω'' := by
  obtain ⟨k, a⟩ := ω
  obtain ⟨l, b⟩ := ω'
  have hc := bG_comm c l
  have hzz := z_mul_z c
  cases a <;> cases b
  · exact ⟨(bxor k l, false), by rw [vElt_false, vElt_false, vElt_false, bG_mul]⟩
  · exact ⟨(bxor k l, true), by rw [vElt_false, vElt_true, vElt_true, ← mul_assoc, bG_mul]⟩
  · refine ⟨(bxor k l, true), ?_⟩
    rw [vElt_true, vElt_false, vElt_true, ← bG_mul]
    calc bG θ k * z * bG θ l = bG θ k * (z * bG θ l) := by group
      _ = bG θ k * bG θ l * z := by rw [← hc]; group
  · refine ⟨(bxor k l, false), ?_⟩
    rw [vElt_true, vElt_true, vElt_false, ← bG_mul]
    calc bG θ k * z * (bG θ l * z) = bG θ k * (z * bG θ l) * z := by group
      _ = bG θ k * bG θ l * (z * z) := by rw [← hc]; group
      _ = bG θ k * bG θ l := by rw [hzz, mul_one]

private theorem vElt_inv (c : Config G L Q 9 θ z) (ω : Om) : (vElt θ z ω)⁻¹ = vElt θ z ω := by
  obtain ⟨k, b⟩ := ω
  have hbb : bG θ k * bG θ k = 1 := by
    rw [bG_mul, show bxor k k = 0 from Fin.ext (Nat.xor_self _), bG_zero]
  have hbinv : (bG θ k)⁻¹ = bG θ k := inv_eq_of_mul_eq_one_right hbb
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (z_mul_z c)
  cases b
  · rw [vElt_false, hbinv]
  · rw [vElt_true, mul_inv_rev, hbinv, hzinv, bG_comm c k]

theorem mem_vSub_iff (c : Config G L Q 9 θ z) {y : G} : y ∈ vSub θ z ↔ ∃ ω, vElt θ z ω = y := by
  constructor
  · intro hy
    let S : Subgroup G :=
      { carrier := Set.range (vElt θ z)
        mul_mem' := by
          rintro _ _ ⟨ω, rfl⟩ ⟨ω', rfl⟩
          obtain ⟨ω'', h⟩ := vElt_mul_mem c ω ω'
          exact ⟨ω'', h.symm⟩
        one_mem' := ⟨(0, false), by rw [vElt_false, bG_zero]⟩
        inv_mem' := by
          rintro _ ⟨ω, rfl⟩
          exact ⟨ω, (vElt_inv c ω).symm⟩ }
    have hle : vSub θ z ≤ S := by
      refine sup_le ?_ ?_
      · intro b hb
        obtain ⟨k, rfl⟩ := (mem_bSub_iff θ).1 hb
        exact ⟨(k, false), vElt_false k⟩
      · rw [zpowers_le]
        exact ⟨(0, true), by rw [vElt_true, bG_zero, one_mul]⟩
    exact hle hy
  · rintro ⟨ω, rfl⟩
    exact vElt_mem ω

theorem vElt_injective (c : Config G L Q 9 θ z) : Function.Injective (vElt θ z) := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have hzL := z_not_mem_L c
  cases a <;> cases b
  · rw [vElt_false, vElt_false] at h
    rw [bG_injective θ h]
  · rw [vElt_false, vElt_true] at h
    exfalso
    apply hzL
    have h1 : z = (bG θ l)⁻¹ * bG θ k := by rw [h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG_mem θ l)) (bG_mem θ k)
  · rw [vElt_true, vElt_false] at h
    exfalso
    apply hzL
    have h1 : z = (bG θ k)⁻¹ * bG θ l := by rw [← h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG_mem θ k)) (bG_mem θ l)
  · rw [vElt_true, vElt_true] at h
    rw [bG_injective θ (mul_right_cancel h)]

@[expose] noncomputable def vEquiv (c : Config G L Q 9 θ z) : Om ≃ vSub θ z :=
  Equiv.ofBijective (fun ω => ⟨vElt θ z ω, vElt_mem ω⟩)
    ⟨fun ω ω' h => vElt_injective c (congrArg Subtype.val h), fun v => by
      obtain ⟨ω, hω⟩ := (mem_vSub_iff c).1 v.2
      exact ⟨ω, Subtype.ext hω⟩⟩

@[expose] noncomputable def omAct (c : Config G L Q 9 θ z) (g : normalizer (vSub θ z : Set G))
    (ω : Om) : Om :=
  (vEquiv c).symm ⟨(g : G) * vElt θ z ω * (g : G)⁻¹, (mem_normalizer_iff.1 g.2 _).1 (vElt_mem ω)⟩

theorem omAct_eq_iff (c : Config G L Q 9 θ z) (g : normalizer (vSub θ z : Set G)) (ω ω' : Om) :
    omAct c g ω = ω' ↔ (g : G) * vElt θ z ω * (g : G)⁻¹ = vElt θ z ω' := by
  unfold omAct
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  rfl

theorem vElt_omAct (c : Config G L Q 9 θ z) (g : normalizer (vSub θ z : Set G)) (ω : Om) :
    vElt θ z (omAct c g ω) = (g : G) * vElt θ z ω * (g : G)⁻¹ :=
  ((omAct_eq_iff c g ω _).1 rfl).symm

theorem omAct_one (c : Config G L Q 9 θ z) (ω : Om) : omAct c 1 ω = ω := by
  rw [omAct_eq_iff, Subgroup.coe_one, one_mul, inv_one, mul_one]

theorem omAct_mul (c : Config G L Q 9 θ z) (g h : normalizer (vSub θ z : Set G)) (ω : Om) :
    omAct c (g * h) ω = omAct c g (omAct c h ω) := by
  rw [omAct_eq_iff, vElt_omAct, vElt_omAct, Subgroup.coe_mul]
  group

theorem mem_centralizer_of_fix (c : Config G L Q 9 θ z) {g : G}
    (h : ∀ i, isO6 i = true → g * vElt θ z (i, true) * g⁻¹ = vElt θ z (i, true)) :
    g ∈ centralizer (vSub θ z : Set G) := by
  have hmul : ∀ y y' : G, g * y * g⁻¹ = y → g * y' * g⁻¹ = y' → g * (y * y') * g⁻¹ = y * y' := by
    intro y y' hy hy'
    calc g * (y * y') * g⁻¹ = (g * y * g⁻¹) * (g * y' * g⁻¹) := by group
      _ = y * y' := by rw [hy, hy']
  have hzz := z_mul_z c
  have hz : g * z * g⁻¹ = z := by
    have h1 := hmul _ _ (hmul _ _ (h 1 (by decide)) (h 2 (by decide))) (h 3 (by decide))
    have h2 : vElt θ z (1, true) * vElt θ z (2, true) * vElt θ z (3, true) = z := by
      rw [vElt_true, vElt_true, vElt_true]
      calc bG θ 1 * z * (bG θ 2 * z) * (bG θ 3 * z)
          = bG θ 1 * (z * bG θ 2) * z * (bG θ 3 * z) := by group
        _ = bG θ 1 * bG θ 2 * (z * z) * bG θ 3 * z := by rw [← bG_comm c 2]; group
        _ = bG θ 1 * bG θ 2 * bG θ 3 * z := by rw [hzz, mul_one]
        _ = z := by rw [bG_mul, bG_mul, show bxor (bxor 1 2) 3 = 0 by decide, bG_zero, one_mul]
    rwa [h2] at h1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have h6 : ∀ i, i = 0 ∨ isO6 i = true → g * bG θ i * g⁻¹ = bG θ i := by
    rintro i (rfl | hi)
    · rw [bG_zero, mul_one, mul_inv_cancel]
    · have h1 := hmul _ _ (h i hi) (show g * z⁻¹ * g⁻¹ = z⁻¹ by rw [hzinv, hz])
      rwa [vElt_true, mul_inv_cancel_right] at h1
  have hall : ∀ k, g * bG θ k * g⁻¹ = bG θ k := by
    have key : ∀ k : Fin 16, ∃ a b : Fin 16, (a = 0 ∨ isO6 a = true) ∧ (b = 0 ∨ isO6 b = true) ∧
        bxor a b = k := by
      decide
    intro k
    obtain ⟨a, b, ha, hb, rfl⟩ := key k
    rw [← bG_mul]
    exact hmul _ _ (h6 a ha) (h6 b hb)
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub_iff c).1 hv
  have h1 := conj_vElt (hall k) hz b
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem exists_wit_act (c : Config G L Q 9 θ z) (j : Fin 11) :
    ∃ g ∈ normalizer (vSub θ z : Set G), ∀ k b,
      g * vElt θ z (k, b) * g⁻¹ = vElt θ z (piTab j k, b) := by
  set l : L := θ.symm ⟨wit j, wit_mem j⟩
  have hk : ∀ k, (l : G) * bG θ k * (l : G)⁻¹ = bG θ (piTab j k) := by
    intro k
    have h1 : l * bL θ k * l⁻¹ = bL θ (piTab j k) := by
      simp only [l, bL]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (wit_conj j k)
    exact congrArg Subtype.val h1
  have hz : (l : G) * z * (l : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (le_cent_single c.ot.std c.ot.cyc l.2)]
    group
  have hact : ∀ k b, (l : G) * vElt θ z (k, b) * (l : G)⁻¹ = vElt θ z (piTab j k, b) :=
    fun k b => conj_vElt (hk k) hz b
  refine ⟨l, ?_, hact⟩
  apply mem_normalizer_of_forall_conj
  intro v hv
  obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub_iff c).1 hv
  rw [hact]
  exact vElt_mem _

theorem conj_bG_iff (c : Config G L Q 9 θ z) (y : centralizer ({z} : Set G)) (k l : Fin 16) :
    (y : G) * bG θ k * (y : G)⁻¹ = bG θ l ↔ rhoC c y * bEl k * (rhoC c y)⁻¹ = bEl l := by
  have hyN := cent_le_normalizer c.ot.std c.ot.cyc y.2
  have h := rho_conj θ c.hn8 ⟨y, hyN⟩ ⟨bEl k, bEl_mem_alternatingGroup k⟩
  rw [rhoC_apply]
  rw [h]
  constructor
  · intro he
    have h1 : (⟨(y : G) * ((θ.symm ⟨bEl k, bEl_mem_alternatingGroup k⟩ : L) : G) * (y : G)⁻¹,
        (mem_normalizer_iff.mp hyN _).mp (θ.symm ⟨bEl k, bEl_mem_alternatingGroup k⟩).2⟩ : L) =
        bL θ l := Subtype.ext he
    rw [h1, theta_bL]
  · intro he
    have h2 := congrArg Subtype.val (θ.injective (Subtype.ext (he.trans (theta_bL θ l).symm)))
    exact h2

theorem mem_normalizer_vSub_iff (c : Config G L Q 9 θ z) {y : G}
    (hy : y ∈ centralizer ({z} : Set G)) :
    y ∈ normalizer (vSub θ z : Set G) ↔ ∀ k, ∃ l, y * bG θ k * y⁻¹ = bG θ l := by
  have hyz : y * z * y⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 hy]
    group
  constructor
  · intro h k
    have h1 : y * bG θ k * y⁻¹ ∈ vSub θ z :=
      (mem_normalizer_iff.1 h _).1 (by rw [← vElt_false]; exact vElt_mem _)
    obtain ⟨⟨l, b⟩, hl⟩ := (mem_vSub_iff c).1 h1
    cases b
    · exact ⟨l, by rw [← hl, vElt_false]⟩
    · exfalso
      rw [vElt_true] at hl
      apply z_not_mem_L c
      have hyL : y * bG θ k * y⁻¹ ∈ L :=
        (mem_normalizer_iff.1 (cent_le_normalizer c.ot.std c.ot.cyc hy) _).1 (bG_mem θ k)
      have h2 : z = (bG θ l)⁻¹ * (y * bG θ k * y⁻¹) := by rw [← hl]; group
      rw [h2]
      exact mul_mem (inv_mem (bG_mem θ l)) hyL
  · intro h
    apply mem_normalizer_of_forall_conj
    intro v hv
    obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub_iff c).1 hv
    obtain ⟨l, hl⟩ := h k
    rw [conj_vElt hl hyz b]
    exact vElt_mem _

theorem mem_centralizer_vSub_iff (c : Config G L Q 9 θ z) {y : G}
    (hy : y ∈ centralizer ({z} : Set G)) :
    y ∈ centralizer (vSub θ z : Set G) ↔ ∀ k, y * bG θ k * y⁻¹ = bG θ k := by
  have hyz : y * z * y⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 hy]
    group
  rw [mem_centralizer_iff]
  constructor
  · intro h k
    rw [← h _ (by rw [← vElt_false]; exact vElt_mem _), mul_inv_cancel_right]
  · intro h v hv
    obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub_iff c).1 hv
    have h1 := conj_vElt (h k) hyz b
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

theorem relIndex_centralizer_vSub (c : Config G L Q 9 θ z)
    (hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    (centralizer (vSub θ z : Set G)).relIndex
      (normalizer (vSub θ z : Set G) ⊓ centralizer ({z} : Set G)) = 36 := by
  have h1 : (normalizer (vSub θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf
      (centralizer ({z} : Set G)) =
      (normalizer (bBar : Set (Perm (Fin 9)))).comap (rhoC c) := by
    ext y
    rw [mem_subgroupOf, mem_comap, mem_inf, mem_normalizer_vSub_iff c y.2,
      mem_normalizer_bBar_iff]
    simp only [y.2, and_true]
    exact forall_congr' fun k => exists_congr fun l => conj_bG_iff c y k l
  have h2 : (centralizer (vSub θ z : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer (bBar : Set (Perm (Fin 9)))).comap (rhoC c) := by
    ext y
    rw [mem_subgroupOf, mem_comap, mem_centralizer_vSub_iff c y.2, mem_centralizer_bBar_iff]
    exact forall_congr' fun k => conj_bG_iff c y k k
  rw [← relIndex_subgroupOf (inf_le_right : normalizer (vSub θ z : Set G) ⊓
      centralizer ({z} : Set G) ≤ centralizer ({z} : Set G)), h1, h2, relIndex_comap,
    map_comap_eq, range_rhoC_of_inner c hin, inf_comm]
  exact relIndex_centralizer_bBar

end Config

end CFSG.OddStandard.AltStdSmall4.Fus.P42

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup AltStdCycTwo MulAction P42

theorem fusP42_holds : FusP42 := by
  intro G _ _ L Q θ z c hin x hx hxz g hg l hl1 hl2 hgl
  obtain ⟨i, rfl⟩ := eq_bL_of_mem θ hl1
  have hi : isO6 i = true := by
    rw [theta_bL] at hl2
    exact isO6_of_card_support i hl2
  set N := normalizer (vSub θ z : Set G) with hN
  have hcz : vElt θ z (0, true) = z := by rw [vElt_true, bG_zero, one_mul]
  have hKS : (centralizer (vSub θ z : Set G)).subgroupOf N ≤
      (normalizer (vSub θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N := by
    intro y hy
    rw [mem_subgroupOf, mem_centralizer_iff] at hy
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨y.2, (hy z (mem_sup_right (mem_zpowers z))).symm⟩
  have hidx : ((centralizer (vSub θ z : Set G)).subgroupOf N).index =
      36 * ((normalizer (vSub θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N).index := by
    rw [← relIndex_mul_index hKS, relIndex_subgroupOf inf_le_left,
      relIndex_centralizer_vSub c hin]
  refine not_smul_eq_O6 (omAct c) (omAct_one c) (omAct_mul c) (fun j => ?_)
    ((centralizer (vSub θ z : Set G)).subgroupOf N)
    ((normalizer (vSub θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N)
    (fun k hk ω => ?_) (fun g' hg' => ?_) (fun g' => ?_) hidx (fun g' => ?_) (fun g' => ?_) ?_
    ⟨g, hg⟩ i hi ?_
  · obtain ⟨g', hg'N, hg'⟩ := exists_wit_act c j
    exact ⟨⟨g', hg'N⟩, fun k b => (omAct_eq_iff c _ _ _).2 (hg' k b)⟩
  · rw [omAct_eq_iff]
    rw [mem_subgroupOf, mem_centralizer_iff] at hk
    rw [← hk _ (vElt_mem _), mul_inv_cancel_right]
  · rw [mem_subgroupOf]
    exact mem_centralizer_of_fix c fun i hi => (omAct_eq_iff c _ _ _).1 (hg' i hi)
  · rw [omAct_eq_iff, mem_subgroupOf, mem_inf, hcz, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
    simp only [g'.2, true_and]
  · rw [omAct_eq_iff, vElt_false, bG_zero, mul_one, mul_inv_cancel]
  · obtain ⟨⟨k, b⟩, hω⟩ : ∃ ω : Om, omAct c g' (0, true) = ω := ⟨_, rfl⟩
    rw [hω]
    cases b
    · exfalso
      rw [omAct_eq_iff, hcz, vElt_false] at hω
      exact not_conj_mem_L c.ot.std θ le89 c.ot.cyc c.ot.card g' (hω ▸ bG_mem θ k)
    · rfl
  · refine ⟨⟨x, hx⟩, ?_⟩
    rw [omAct_eq_iff, hcz, vElt_true, bG_comm c 5, ← w_eq_bG]
    exact hxz
  · rw [omAct_eq_iff, vElt_false, vElt_false, ← w_eq_bG]
    exact hgl

end CFSG.OddStandard.AltStdSmall4.Fus
