module

public import CFSG.LocalAnalysis.OddStandard.AltStdEvenP42Perm
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42E

open Equiv Subgroup AltStdCycTwo AltStdBal P42

section Elements

variable {G : Type} [Group G] {L : Subgroup G} (θ : L ≃* alternatingGroup (Fin 8))

@[expose] def bL8 (k : Fin 16) : L := θ.symm ⟨bEl8 k, bEl8_mem_alternatingGroup k⟩

@[expose] def bG8 (k : Fin 16) : G := (bL8 θ k : G)

theorem bG8_mem (k : Fin 16) : bG8 θ k ∈ L := (bL8 θ k).2

theorem bL8_mul (k l : Fin 16) : bL8 θ k * bL8 θ l = bL8 θ (bxor k l) := by
  unfold bL8
  rw [← map_mul]
  congr 1
  exact Subtype.ext (bEl8_mul k l)

theorem bG8_mul (k l : Fin 16) : bG8 θ k * bG8 θ l = bG8 θ (bxor k l) := by
  unfold bG8
  rw [← Subgroup.coe_mul, bL8_mul]

theorem bG8_zero : bG8 θ 0 = 1 := by
  unfold bG8 bL8
  rw [show (⟨bEl8 0, bEl8_mem_alternatingGroup 0⟩ : alternatingGroup (Fin 8)) = 1 from
    Subtype.ext bEl8_zero, map_one, Subgroup.coe_one]

theorem theta_bL8 (k : Fin 16) :
    ((θ (bL8 θ k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = bEl8 k := by
  simp [bL8]

theorem bG8_injective : Function.Injective (bG8 θ) := by
  intro k l h
  have h1 : bL8 θ k = bL8 θ l := Subtype.ext h
  apply bEl8_injective
  rw [← theta_bL8 θ k, ← theta_bL8 θ l, h1]

theorem eq_bL8_of_mem {l : L} (h : ((θ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) ∈ bBar8) :
    ∃ k, bL8 θ k = l := by
  obtain ⟨k, hk⟩ := mem_bBar8_iff.1 h
  refine ⟨k, θ.injective (Subtype.ext ?_)⟩
  rw [theta_bL8, hk]

theorem mem_bSub8_iff {y : G} : y ∈ bSub8 θ ↔ ∃ k, bG8 θ k = y := by
  constructor
  · intro hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hl
    obtain ⟨k, hk⟩ := mem_bBar8_iff.1 (Subgroup.mem_comap.1 ha)
    have h1 : a = ⟨bEl8 k, bEl8_mem_alternatingGroup k⟩ := Subtype.ext hk.symm
    subst h1
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact Subgroup.mem_map.2 ⟨bL8 θ k, Subgroup.mem_map.2
      ⟨⟨bEl8 k, bEl8_mem_alternatingGroup k⟩, Subgroup.mem_comap.2 (bEl8_mem_bBar8 k), rfl⟩, rfl⟩

theorem w_eq_bG8 : w θ le88 = bG8 θ 5 := by
  unfold w bG8 bL8
  congr 2
  apply Subtype.ext
  rw [coe_wBar, tr_one_eq_bEl8]

end Elements

section Setting

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin 8)}
  {z : G}

theorem bG8_comm (hS : StandardSetting G L) (d : Cyc L Q z) (k : Fin 16) :
    bG8 θ k * z = z * bG8 θ k :=
  mem_centralizer_singleton_iff.1 (le_cent_single hS d (bG8_mem θ k))

theorem z_not_mem_L8 (θ : L ≃* alternatingGroup (Fin 8)) (hS : StandardSetting G L)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) : z ∉ L := by
  have h := AltStdCycTwo.not_conj_mem_L hS θ le88 d hQ2 1
  simpa using h

variable (θ z) in
@[expose] def vElt8 (ω : Om) : G := bG8 θ ω.1 * cond ω.2 z 1

theorem vElt8_false (k : Fin 16) : vElt8 θ z (k, false) = bG8 θ k := by
  simp [vElt8]

theorem vElt8_true (k : Fin 16) : vElt8 θ z (k, true) = bG8 θ k * z := by
  simp [vElt8]

theorem vElt8_mem (ω : Om) : vElt8 θ z ω ∈ vSub8 θ z := by
  obtain ⟨k, b⟩ := ω
  have hb : bG8 θ k ∈ vSub8 θ z := mem_sup_left ((mem_bSub8_iff θ).2 ⟨k, rfl⟩)
  cases b
  · rw [vElt8_false]
    exact hb
  · rw [vElt8_true]
    exact mul_mem hb (mem_sup_right (mem_zpowers z))

theorem conj_vElt8 {g : G} {k l : Fin 16} (hk : g * bG8 θ k * g⁻¹ = bG8 θ l)
    (hz : g * z * g⁻¹ = z) (b : Bool) : g * vElt8 θ z (k, b) * g⁻¹ = vElt8 θ z (l, b) := by
  cases b
  · rw [vElt8_false, vElt8_false, hk]
  · rw [vElt8_true, vElt8_true]
    calc g * (bG8 θ k * z) * g⁻¹ = (g * bG8 θ k * g⁻¹) * (g * z * g⁻¹) := by group
      _ = bG8 θ l * z := by rw [hk, hz]

private theorem vElt8_mul_mem (hS : StandardSetting G L) (d : Cyc L Q z) (ω ω' : Om) :
    ∃ ω'' : Om, vElt8 θ z ω * vElt8 θ z ω' = vElt8 θ z ω'' := by
  obtain ⟨k, a⟩ := ω
  obtain ⟨l, b⟩ := ω'
  have hc := bG8_comm (θ := θ) hS d l
  have hzz := d.mul_self
  cases a <;> cases b
  · exact ⟨(bxor k l, false), by rw [vElt8_false, vElt8_false, vElt8_false, bG8_mul]⟩
  · exact ⟨(bxor k l, true), by rw [vElt8_false, vElt8_true, vElt8_true, ← mul_assoc, bG8_mul]⟩
  · refine ⟨(bxor k l, true), ?_⟩
    rw [vElt8_true, vElt8_false, vElt8_true, ← bG8_mul]
    calc bG8 θ k * z * bG8 θ l = bG8 θ k * (z * bG8 θ l) := by group
      _ = bG8 θ k * bG8 θ l * z := by rw [← hc]; group
  · refine ⟨(bxor k l, false), ?_⟩
    rw [vElt8_true, vElt8_true, vElt8_false, ← bG8_mul]
    calc bG8 θ k * z * (bG8 θ l * z) = bG8 θ k * (z * bG8 θ l) * z := by group
      _ = bG8 θ k * bG8 θ l * (z * z) := by rw [← hc]; group
      _ = bG8 θ k * bG8 θ l := by rw [hzz, mul_one]

private theorem vElt8_inv (hS : StandardSetting G L) (d : Cyc L Q z) (ω : Om) :
    (vElt8 θ z ω)⁻¹ = vElt8 θ z ω := by
  obtain ⟨k, b⟩ := ω
  have hbb : bG8 θ k * bG8 θ k = 1 := by
    rw [bG8_mul, show bxor k k = 0 from Fin.ext (Nat.xor_self _), bG8_zero]
  have hbinv : (bG8 θ k)⁻¹ = bG8 θ k := inv_eq_of_mul_eq_one_right hbb
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right d.mul_self
  cases b
  · rw [vElt8_false, hbinv]
  · rw [vElt8_true, mul_inv_rev, hbinv, hzinv, bG8_comm hS d k]

theorem mem_vSub8_iff (hS : StandardSetting G L) (d : Cyc L Q z) {y : G} :
    y ∈ vSub8 θ z ↔ ∃ ω, vElt8 θ z ω = y := by
  constructor
  · intro hy
    let S : Subgroup G :=
      { carrier := Set.range (vElt8 θ z)
        mul_mem' := by
          rintro _ _ ⟨ω, rfl⟩ ⟨ω', rfl⟩
          obtain ⟨ω'', h⟩ := vElt8_mul_mem hS d ω ω'
          exact ⟨ω'', h.symm⟩
        one_mem' := ⟨(0, false), by rw [vElt8_false, bG8_zero]⟩
        inv_mem' := by
          rintro _ ⟨ω, rfl⟩
          exact ⟨ω, (vElt8_inv hS d ω).symm⟩ }
    have hle : vSub8 θ z ≤ S := by
      refine sup_le ?_ ?_
      · intro b hb
        obtain ⟨k, rfl⟩ := (mem_bSub8_iff θ).1 hb
        exact ⟨(k, false), vElt8_false k⟩
      · rw [zpowers_le]
        exact ⟨(0, true), by rw [vElt8_true, bG8_zero, one_mul]⟩
    exact hle hy
  · rintro ⟨ω, rfl⟩
    exact vElt8_mem ω

theorem vElt8_injective (hS : StandardSetting G L) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    Function.Injective (vElt8 θ z) := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have hzL := z_not_mem_L8 θ hS d hQ2
  cases a <;> cases b
  · rw [vElt8_false, vElt8_false] at h
    rw [bG8_injective θ h]
  · rw [vElt8_false, vElt8_true] at h
    exfalso
    apply hzL
    have h1 : z = (bG8 θ l)⁻¹ * bG8 θ k := by rw [h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG8_mem θ l)) (bG8_mem θ k)
  · rw [vElt8_true, vElt8_false] at h
    exfalso
    apply hzL
    have h1 : z = (bG8 θ k)⁻¹ * bG8 θ l := by rw [← h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG8_mem θ k)) (bG8_mem θ l)
  · rw [vElt8_true, vElt8_true] at h
    rw [bG8_injective θ (mul_right_cancel h)]

@[expose] noncomputable def vEquiv8 (hS : StandardSetting G L) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) : Om ≃ vSub8 θ z :=
  Equiv.ofBijective (fun ω => ⟨vElt8 θ z ω, vElt8_mem ω⟩)
    ⟨fun ω ω' h => vElt8_injective hS d hQ2 (congrArg Subtype.val h), fun v => by
      obtain ⟨ω, hω⟩ := (mem_vSub8_iff hS d).1 v.2
      exact ⟨ω, Subtype.ext hω⟩⟩

@[expose] noncomputable def omAct8 (hS : StandardSetting G L) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) (g : normalizer (vSub8 θ z : Set G)) (ω : Om) : Om :=
  (vEquiv8 hS d hQ2).symm
    ⟨(g : G) * vElt8 θ z ω * (g : G)⁻¹, (mem_normalizer_iff.1 g.2 _).1 (vElt8_mem ω)⟩

theorem omAct8_eq_iff (hS : StandardSetting G L) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (g : normalizer (vSub8 θ z : Set G)) (ω ω' : Om) :
    omAct8 hS d hQ2 g ω = ω' ↔ (g : G) * vElt8 θ z ω * (g : G)⁻¹ = vElt8 θ z ω' := by
  unfold omAct8
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  rfl

theorem vElt8_omAct8 (hS : StandardSetting G L) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (g : normalizer (vSub8 θ z : Set G)) (ω : Om) :
    vElt8 θ z (omAct8 hS d hQ2 g ω) = (g : G) * vElt8 θ z ω * (g : G)⁻¹ :=
  ((omAct8_eq_iff hS d hQ2 g ω _).1 rfl).symm

theorem omAct8_one (hS : StandardSetting G L) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (ω : Om) :
    omAct8 (θ := θ) hS d hQ2 1 ω = ω := by
  rw [omAct8_eq_iff, Subgroup.coe_one, one_mul, inv_one, mul_one]

theorem omAct8_mul (hS : StandardSetting G L) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (g h : normalizer (vSub8 θ z : Set G)) (ω : Om) :
    omAct8 hS d hQ2 (g * h) ω = omAct8 hS d hQ2 g (omAct8 hS d hQ2 h ω) := by
  rw [omAct8_eq_iff, vElt8_omAct8, vElt8_omAct8, Subgroup.coe_mul]
  group

theorem mem_centralizer_of_fix8 (hS : StandardSetting G L) (d : Cyc L Q z) {g : G}
    (h : ∀ i, isO6 i = true → g * vElt8 θ z (i, true) * g⁻¹ = vElt8 θ z (i, true)) :
    g ∈ centralizer (vSub8 θ z : Set G) := by
  have hmul : ∀ y y' : G, g * y * g⁻¹ = y → g * y' * g⁻¹ = y' →
      g * (y * y') * g⁻¹ = y * y' := by
    intro y y' hy hy'
    calc g * (y * y') * g⁻¹ = (g * y * g⁻¹) * (g * y' * g⁻¹) := by group
      _ = y * y' := by rw [hy, hy']
  have hzz := d.mul_self
  have hz : g * z * g⁻¹ = z := by
    have h1 := hmul _ _ (hmul _ _ (h 1 (by decide)) (h 2 (by decide))) (h 3 (by decide))
    have h2 : vElt8 θ z (1, true) * vElt8 θ z (2, true) * vElt8 θ z (3, true) = z := by
      rw [vElt8_true, vElt8_true, vElt8_true]
      calc bG8 θ 1 * z * (bG8 θ 2 * z) * (bG8 θ 3 * z)
          = bG8 θ 1 * (z * bG8 θ 2) * z * (bG8 θ 3 * z) := by group
        _ = bG8 θ 1 * bG8 θ 2 * (z * z) * bG8 θ 3 * z := by rw [← bG8_comm hS d 2]; group
        _ = bG8 θ 1 * bG8 θ 2 * bG8 θ 3 * z := by rw [hzz, mul_one]
        _ = z := by
          rw [bG8_mul, bG8_mul, show bxor (bxor 1 2) 3 = 0 by decide, bG8_zero, one_mul]
    rwa [h2] at h1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have h6 : ∀ i, i = 0 ∨ isO6 i = true → g * bG8 θ i * g⁻¹ = bG8 θ i := by
    rintro i (rfl | hi)
    · rw [bG8_zero, mul_one, mul_inv_cancel]
    · have h1 := hmul _ _ (h i hi) (show g * z⁻¹ * g⁻¹ = z⁻¹ by rw [hzinv, hz])
      rwa [vElt8_true, mul_inv_cancel_right] at h1
  have hall : ∀ k, g * bG8 θ k * g⁻¹ = bG8 θ k := by
    have key : ∀ k : Fin 16, ∃ a b : Fin 16, (a = 0 ∨ isO6 a = true) ∧
        (b = 0 ∨ isO6 b = true) ∧ bxor a b = k := by
      decide
    intro k
    obtain ⟨a, b, ha, hb, rfl⟩ := key k
    rw [← bG8_mul]
    exact hmul _ _ (h6 a ha) (h6 b hb)
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub8_iff hS d).1 hv
  have h1 := conj_vElt8 (hall k) hz b
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem exists_wit8_act (hS : StandardSetting G L) (d : Cyc L Q z) (j : Fin 11) :
    ∃ g ∈ normalizer (vSub8 θ z : Set G), ∀ k b,
      g * vElt8 θ z (k, b) * g⁻¹ = vElt8 θ z (piTab j k, b) := by
  set l : L := θ.symm ⟨wit8 j, wit8_mem j⟩
  have hk : ∀ k, (l : G) * bG8 θ k * (l : G)⁻¹ = bG8 θ (piTab j k) := by
    intro k
    have h1 : l * bL8 θ k * l⁻¹ = bL8 θ (piTab j k) := by
      simp only [l, bL8]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (wit8_conj j k)
    exact congrArg Subtype.val h1
  have hz : (l : G) * z * (l : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (le_cent_single hS d l.2)]
    group
  have hact : ∀ k b, (l : G) * vElt8 θ z (k, b) * (l : G)⁻¹ = vElt8 θ z (piTab j k, b) :=
    fun k b => conj_vElt8 (hk k) hz b
  refine ⟨l, ?_, hact⟩
  apply mem_normalizer_of_forall_conj
  intro v hv
  obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub8_iff hS d).1 hv
  rw [hact]
  exact vElt8_mem _

variable (θ) in
@[expose] noncomputable def rhoC8 (hS : StandardSetting G L) (d : Cyc L Q z) :
    centralizer ({z} : Set G) →* Perm (Fin 8) :=
  (rho θ le88).comp (Subgroup.inclusion (cent_le_normalizer hS d))

theorem rhoC8_apply (hS : StandardSetting G L) (d : Cyc L Q z) (x : centralizer ({z} : Set G)) :
    rhoC8 θ hS d x = rho θ le88 ⟨x, cent_le_normalizer hS d x.2⟩ := rfl

theorem range_rhoC8_of_inner (hS : StandardSetting G L) (d : Cyc L Q z)
    (hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    (rhoC8 θ hS d).range = alternatingGroup (Fin 8) := by
  apply le_antisymm
  · rintro σ ⟨x, rfl⟩
    exact (mem_evenAct_iff θ le88 (cent_le_normalizer hS d x.2)).1
      (sup_le_evenAct θ le88 (hin x.2))
  · intro σ hσ
    set l : L := θ.symm ⟨σ, hσ⟩ with hl
    refine ⟨⟨l, le_cent_single hS d l.2⟩, ?_⟩
    rw [rhoC8_apply, rho_of_mem θ le88 l]
    simp [hl]

theorem conj_bG8_iff (hS : StandardSetting G L) (d : Cyc L Q z) (y : centralizer ({z} : Set G))
    (k l : Fin 16) :
    (y : G) * bG8 θ k * (y : G)⁻¹ = bG8 θ l ↔
      rhoC8 θ hS d y * bEl8 k * (rhoC8 θ hS d y)⁻¹ = bEl8 l := by
  have hyN := cent_le_normalizer hS d y.2
  have h := rho_conj θ le88 ⟨y, hyN⟩ ⟨bEl8 k, bEl8_mem_alternatingGroup k⟩
  rw [rhoC8_apply]
  rw [h]
  constructor
  · intro he
    have h1 : (⟨(y : G) * ((θ.symm ⟨bEl8 k, bEl8_mem_alternatingGroup k⟩ : L) : G) * (y : G)⁻¹,
        (mem_normalizer_iff.mp hyN _).mp (θ.symm ⟨bEl8 k, bEl8_mem_alternatingGroup k⟩).2⟩ : L) =
        bL8 θ l := Subtype.ext he
    rw [h1, theta_bL8]
  · intro he
    exact congrArg Subtype.val (θ.injective (Subtype.ext (he.trans (theta_bL8 θ l).symm)))

theorem mem_normalizer_vSub8_iff (hS : StandardSetting G L) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) {y : G} (hy : y ∈ centralizer ({z} : Set G)) :
    y ∈ normalizer (vSub8 θ z : Set G) ↔ ∀ k, ∃ l, y * bG8 θ k * y⁻¹ = bG8 θ l := by
  have hyz : y * z * y⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 hy]
    group
  constructor
  · intro h k
    have h1 : y * bG8 θ k * y⁻¹ ∈ vSub8 θ z :=
      (mem_normalizer_iff.1 h _).1 (by rw [← vElt8_false]; exact vElt8_mem _)
    obtain ⟨⟨l, b⟩, hl⟩ := (mem_vSub8_iff hS d).1 h1
    cases b
    · exact ⟨l, by rw [← hl, vElt8_false]⟩
    · exfalso
      rw [vElt8_true] at hl
      apply z_not_mem_L8 θ hS d hQ2
      have hyL : y * bG8 θ k * y⁻¹ ∈ L :=
        (mem_normalizer_iff.1 (cent_le_normalizer hS d hy) _).1 (bG8_mem θ k)
      have h2 : z = (bG8 θ l)⁻¹ * (y * bG8 θ k * y⁻¹) := by rw [← hl]; group
      rw [h2]
      exact mul_mem (inv_mem (bG8_mem θ l)) hyL
  · intro h
    apply mem_normalizer_of_forall_conj
    intro v hv
    obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub8_iff hS d).1 hv
    obtain ⟨l, hl⟩ := h k
    rw [conj_vElt8 hl hyz b]
    exact vElt8_mem _

theorem mem_centralizer_vSub8_iff (hS : StandardSetting G L) (d : Cyc L Q z) {y : G}
    (hy : y ∈ centralizer ({z} : Set G)) :
    y ∈ centralizer (vSub8 θ z : Set G) ↔ ∀ k, y * bG8 θ k * y⁻¹ = bG8 θ k := by
  have hyz : y * z * y⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 hy]
    group
  rw [mem_centralizer_iff]
  constructor
  · intro h k
    rw [← h _ (by rw [← vElt8_false]; exact vElt8_mem _), mul_inv_cancel_right]
  · intro h v hv
    obtain ⟨⟨k, b⟩, rfl⟩ := (mem_vSub8_iff hS d).1 hv
    have h1 := conj_vElt8 (h k) hyz b
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

theorem relIndex_centralizer_vSub8 (hS : StandardSetting G L)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    (centralizer (vSub8 θ z : Set G)).relIndex
      (normalizer (vSub8 θ z : Set G) ⊓ centralizer ({z} : Set G)) = 36 := by
  have h1 : (normalizer (vSub8 θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf
      (centralizer ({z} : Set G)) =
      (normalizer (bBar8 : Set (Perm (Fin 8)))).comap (rhoC8 θ hS d) := by
    ext y
    rw [mem_subgroupOf, mem_comap, mem_inf, mem_normalizer_vSub8_iff hS d hQ2 y.2,
      mem_normalizer_bBar8_iff]
    simp only [y.2, and_true]
    exact forall_congr' fun k => exists_congr fun l => conj_bG8_iff hS d y k l
  have h2 : (centralizer (vSub8 θ z : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer (bBar8 : Set (Perm (Fin 8)))).comap (rhoC8 θ hS d) := by
    ext y
    rw [mem_subgroupOf, mem_comap, mem_centralizer_vSub8_iff hS d y.2, mem_centralizer_bBar8_iff]
    exact forall_congr' fun k => conj_bG8_iff hS d y k k
  rw [← relIndex_subgroupOf (inf_le_right : normalizer (vSub8 θ z : Set G) ⊓
      centralizer ({z} : Set G) ≤ centralizer ({z} : Set G)), h1, h2, relIndex_comap,
    map_comap_eq, range_rhoC8_of_inner hS d hin, inf_comm]
  exact relIndex_centralizer_bBar8

end Setting

end CFSG.OddStandard.AltStdSmall4.Fus.P42E

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup AltStdCycTwo P42 P42E

theorem fusP42Eight_holds : FusP42Eight := by
  intro G _ _ L Q θ z hS d hQ2 hin x hx hxz g hg l hl1 hl2 hgl
  obtain ⟨i, rfl⟩ := eq_bL8_of_mem θ hl1
  have hi : isO6 i = true := by
    rw [theta_bL8] at hl2
    exact isO6_of_card_support8 i hl2
  set N := normalizer (vSub8 θ z : Set G) with hN
  have hcz : vElt8 θ z (0, true) = z := by rw [vElt8_true, bG8_zero, one_mul]
  have hKS : (centralizer (vSub8 θ z : Set G)).subgroupOf N ≤
      (normalizer (vSub8 θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N := by
    intro y hy
    rw [mem_subgroupOf, mem_centralizer_iff] at hy
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨y.2, (hy z (mem_sup_right (mem_zpowers z))).symm⟩
  have hidx : ((centralizer (vSub8 θ z : Set G)).subgroupOf N).index =
      36 * ((normalizer (vSub8 θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N).index := by
    rw [← relIndex_mul_index hKS, relIndex_subgroupOf inf_le_left,
      relIndex_centralizer_vSub8 hS d hQ2 hin]
  refine not_smul_eq_O6 (omAct8 hS d hQ2) (omAct8_one hS d hQ2) (omAct8_mul hS d hQ2)
    (fun j => ?_) ((centralizer (vSub8 θ z : Set G)).subgroupOf N)
    ((normalizer (vSub8 θ z : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf N)
    (fun k hk ω => ?_) (fun g' hg' => ?_) (fun g' => ?_) hidx (fun g' => ?_) (fun g' => ?_) ?_
    ⟨g, hg⟩ i hi ?_
  · obtain ⟨g', hg'N, hg'⟩ := exists_wit8_act (θ := θ) hS d j
    exact ⟨⟨g', hg'N⟩, fun k b => (omAct8_eq_iff hS d hQ2 _ _ _).2 (hg' k b)⟩
  · rw [omAct8_eq_iff]
    rw [mem_subgroupOf, mem_centralizer_iff] at hk
    rw [← hk _ (vElt8_mem _), mul_inv_cancel_right]
  · rw [mem_subgroupOf]
    exact mem_centralizer_of_fix8 hS d fun i hi => (omAct8_eq_iff hS d hQ2 _ _ _).1 (hg' i hi)
  · rw [omAct8_eq_iff, mem_subgroupOf, mem_inf, hcz, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
    simp only [g'.2, true_and]
  · rw [omAct8_eq_iff, vElt8_false, bG8_zero, mul_one, mul_inv_cancel]
  · obtain ⟨⟨k, b⟩, hω⟩ : ∃ ω : Om, omAct8 hS d hQ2 g' (0, true) = ω := ⟨_, rfl⟩
    rw [hω]
    cases b
    · exfalso
      rw [omAct8_eq_iff, hcz, vElt8_false] at hω
      exact AltStdCycTwo.not_conj_mem_L hS θ le88 d hQ2 g' (hω ▸ bG8_mem θ k)
    · rfl
  · refine ⟨⟨x, hx⟩, ?_⟩
    rw [omAct8_eq_iff, hcz, vElt8_true, bG8_comm hS d 5, ← w_eq_bG8]
    exact hxz
  · rw [omAct8_eq_iff, vElt8_false, vElt8_false, ← w_eq_bG8]
    exact hgl

end CFSG.OddStandard.AltStdSmall4.Fus
