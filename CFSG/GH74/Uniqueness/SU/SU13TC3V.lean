module

public import CFSG.GH74.Uniqueness.SU.SU13TC3Ord

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def Vsub (z : G) (s : G)
    (hWc : ∀ a ∈ oc (centralizer ({s} : Set G)), ∀ b ∈ oc (centralizer ({s} : Set G)), a * b = b * a) :
    Subgroup G where
  carrier := {v | v ∈ oc (centralizer ({s} : Set G)) ∧ z * v * z⁻¹ = v⁻¹}
  one_mem' := ⟨(oc (centralizer ({s} : Set G))).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
    refine ⟨(oc (centralizer ({s} : Set G))).mul_mem ha hb, ?_⟩
    calc z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hza, hzb]
      _ = (b * a)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [hWc b hb a ha]
  inv_mem' := by
    rintro a ⟨ha, hza⟩
    refine ⟨(oc (centralizer ({s} : Set G))).inv_mem ha, ?_⟩
    calc z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [hza]

abbrev WAbel (e : Elts G z) : Prop :=
  ∀ a ∈ oc (centralizer ({e.s₁} : Set G)), ∀ b ∈ oc (centralizer ({e.s₁} : Set G)), a * b = b * a

theorem W_eq_sup_V (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) {w : G} (hw : w ∈ oc (centralizer ({e.s₁} : Set G))) :
    ∃ c ∈ zpowers e.s₁, ∃ v ∈ Vsub z e.s₁ hWc, w = c * v := by
  obtain ⟨c, hc, h1⟩ := z_inv_modF hz e f.toFPart hw
  have hcW : c ∈ oc (centralizer ({e.s₁} : Set G)) := zpowers_le_oc e hc
  refine ⟨c, hc, c⁻¹ * w, ⟨(oc (centralizer ({e.s₁} : Set G))).mul_mem
    ((oc (centralizer ({e.s₁} : Set G))).inv_mem hcW) hw, ?_⟩, by group⟩
  have hzc : z * c⁻¹ * z⁻¹ = c⁻¹ := by
    have hcz : c * z = z * c := zpowers_comm_of_mem_centralizer (z_mem_centralizerF e f.toFPart) hc
    calc z * c⁻¹ * z⁻¹ = (z * c * z⁻¹)⁻¹ := by group
      _ = c⁻¹ := by rw [← hcz]; group
  calc z * (c⁻¹ * w) * z⁻¹ = (z * c⁻¹ * z⁻¹) * (z * w * z⁻¹) := by group
    _ = c⁻¹ * (c * c * w⁻¹) := by rw [hzc, h1]
    _ = (c⁻¹ * w)⁻¹ := by
      have := hWc c hcW w hw
      calc c⁻¹ * (c * c * w⁻¹) = c * w⁻¹ := by group
        _ = (w * c⁻¹)⁻¹ := by group
        _ = (c⁻¹ * w)⁻¹ := by
          have h2 : c⁻¹ * w = w * c⁻¹ := (Commute.inv_left (show Commute c w from this)).eq
          rw [h2]

theorem zpowers_inf_V {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) : zpowers e.s₁ ⊓ Vsub z e.s₁ hWc = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxP, hxW, hxz⟩ := (mem_inf.mp hx).1, (mem_inf.mp hx).2.1, (mem_inf.mp hx).2.2
  have hczx : x * z = z * x := zpowers_comm_of_mem_centralizer (z_mem_centralizerF e f.toFPart) hxP
  have h1 : x = x⁻¹ := by
    calc x = z * x * z⁻¹ := by rw [← hczx]; group
      _ = x⁻¹ := hxz
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel x
  exact mem_bot.mpr (eq_one_of_mem_oc_of_sq (zpowers_le_oc e hxP) h2)

omit [Finite G] in
theorem V_invariant {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) : ∀ g ∈ f.F, ∀ v ∈ Vsub z e.s₁ hWc, g * v * g⁻¹ ∈ Vsub z e.s₁ hWc := by
  rintro g hg v ⟨hvW, hzv⟩
  refine ⟨conj_mem_oc (F_le_centralizerF e f.toFPart hg) hvW, ?_⟩
  have hgz : g * z = z * g := f.F_comm g hg
  calc z * (g * v * g⁻¹) * z⁻¹ = g * (z * v * z⁻¹) * g⁻¹ := by
        have : z * g = g * z := hgz.symm
        calc z * (g * v * g⁻¹) * z⁻¹ = (z * g) * v * (z * g)⁻¹ := by group
          _ = (g * z) * v * (g * z)⁻¹ := by rw [this]
          _ = g * (z * v * z⁻¹) * g⁻¹ := by group
    _ = g * v⁻¹ * g⁻¹ := by rw [hzv]
    _ = (g * v * g⁻¹)⁻¹ := by group

theorem W_eq_sup (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) : zpowers e.s₁ ⊔ Vsub z e.s₁ hWc = oc (centralizer ({e.s₁} : Set G)) := by
  apply le_antisymm
  · exact sup_le (zpowers_le_oc e) (fun v hv => hv.1)
  · intro w hw
    obtain ⟨c, hc, v, hv, rfl⟩ := W_eq_sup_V hz f hWc hw
    exact mul_mem (mem_sup_left hc) (mem_sup_right hv)

omit [Finite G] in
theorem zpowers_comm_V {e : Elts G z} (hWc : WAbel e) : ∀ a ∈ zpowers e.s₁, ∀ b ∈ Vsub z e.s₁ hWc, a * b = b * a :=
  fun _ ha _ hb => zpowers_comm_of_mem_centralizer (oc_le _ hb.1) ha

theorem V_card (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Nat.card (Vsub z e.s₁ hWc) = 3 ^ 4 := by
  have := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (zpowers e.s₁) (Vsub z e.s₁ hWc)
    (zpowers_comm_V hWc)).1
  rw [W_eq_sup hz f hWc, zpowers_inf_V f hWc, Subgroup.card_bot, hW5, Nat.card_zpowers,
    e.s₁_ord, mul_one] at this
  norm_num at this
  omega

theorem V_irred (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    {U' : Subgroup G} (hU'V : U' ≤ Vsub z e.s₁ hWc) (hinv : ∀ g ∈ f.F, ∀ u ∈ U', g * u * g⁻¹ ∈ U')
    (hne : U' ≠ ⊥) : U' = Vsub z e.s₁ hWc := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hVc := V_card hz f hWc hW5
  have hdvd : Nat.card U' ∣ 3 ^ 4 := hVc ▸ Subgroup.card_dvd_of_le hU'V
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hjc
      exact hne (Subgroup.eq_bot_of_card_eq _ hjc)
    · exact h0
  by_contra hneV
  have hj4 : j ≠ 4 := by
    intro h4
    exact hneV (Subgroup.eq_of_le_of_card_ge hU'V (by rw [hVc, hjc, h4]))
  have hj3 : j ≤ 3 := by omega
  have hUW : zpowers e.s₁ ⊔ U' ≤ oc (centralizer ({e.s₁} : Set G)) :=
    sup_le (zpowers_le_oc e) (fun v hv => (hU'V hv).1)
  have hcomm : ∀ a ∈ zpowers e.s₁, ∀ b ∈ U', a * b = b * a := fun a ha b hb =>
    zpowers_comm_V hWc a ha b (hU'V hb)
  have hPU : zpowers e.s₁ ⊓ U' = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_V f hWc]
    exact inf_le_inf_left _ hU'V
  have hUcard : Nat.card (zpowers e.s₁ ⊔ U' : Subgroup G) = 3 * 3 ^ j := by
    have := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (zpowers e.s₁) U' hcomm).1
    rw [hPU, Subgroup.card_bot, Nat.card_zpowers, e.s₁_ord, hjc] at this
    simpa using this
  have hUinv : ∀ g ∈ f.F, ∀ u ∈ zpowers e.s₁ ⊔ U', g * u * g⁻¹ ∈ zpowers e.s₁ ⊔ U' := by
    intro g hg u hu
    obtain ⟨c, hc, v, hv, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := U') hcomm hu
    have hgc : g * c * g⁻¹ = c := by
      have : c * g = g * c := zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart hg) hc
      rw [← this]; group
    have : g * (c * v) * g⁻¹ = c * (g * v * g⁻¹) := by
      calc g * (c * v) * g⁻¹ = (g * c * g⁻¹) * (g * v * g⁻¹) := by group
        _ = c * (g * v * g⁻¹) := by rw [hgc]
    rw [this]
    exact mul_mem (mem_sup_left hc) (mem_sup_right (hinv g hg v hv))
  obtain ⟨g, hgF, hg⟩ := F_five9 f
  have hjm : (3 : ℕ) ^ j = 3 ^ j := rfl
  have hU := orbit_stepF hz e f.toFPart (p := 3) (q := 5) (r := 3) (m := j) (U := zpowers e.s₁ ⊔ U')
    le_sup_left hUW hUinv hgF hg hUcard (dvd_refl 3) (by norm_num) (by norm_num)
    (fun k hk hkm => by
      have : k ≤ 3 := by omega
      interval_cases k <;> norm_num)
  have hU'P : U' ≤ zpowers e.s₁ := le_sup_right.trans hU
  have : U' ≤ zpowers e.s₁ ⊓ U' := le_inf hU'P le_rfl
  rw [hPU] at this
  exact hne (eq_bot_iff.mpr this)

theorem V_exp (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    ∀ v ∈ Vsub z e.s₁ hWc, v ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set V := Vsub z e.s₁ hWc with hV
  have hVc := V_card hz f hWc hW5
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hWc a ha.1 b hb.1
  let V3 : Subgroup G :=
    { carrier := {v | v ∈ V ∧ v ^ 3 = 1}
      one_mem' := ⟨V.one_mem, one_pow 3⟩
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨V.mul_mem ha hb, ?_⟩
        rw [(Commute.mul_pow (show Commute a b from hcommV a ha b hb)), ha3, hb3, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        exact ⟨V.inv_mem ha, by rw [inv_pow, ha3, inv_one]⟩ }
  have hV3V : V3 ≤ V := fun v hv => hv.1
  have hinv : ∀ g ∈ f.F, ∀ u ∈ V3, g * u * g⁻¹ ∈ V3 := by
    rintro g hg u ⟨hu, hu3⟩
    exact ⟨V_invariant f hWc g hg u hu, by rw [conj_pow, hu3]; group⟩
  have hne : V3 ≠ ⊥ := by
    have h3 : 3 ∣ Nat.card V := by rw [hVc]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 3 h3
    intro hbot
    have hx3 : (x : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hxV3 : (x : G) ∈ V3 := ⟨x.2, hx3⟩
    rw [hbot, mem_bot] at hxV3
    have : x = 1 := Subtype.ext hxV3
    rw [this, orderOf_one] at hx
    omega
  have := V_irred hz f hWc hW5 hV3V hinv hne
  intro v hv
  have : v ∈ V3 := by rw [this]; exact hv
  exact this.2

theorem V_faithful (hz : orderOf z = 2) {e : Elts G z} (f : FPart9 z e) (hWc : WAbel e) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    ∀ g ∈ f.F, g ≠ 1 → ∃ v ∈ Vsub z e.s₁ hWc, g * v ≠ v * g := by
  intro g hg hg1
  by_contra hcon
  have hcon' : ∀ v ∈ Vsub z e.s₁ hWc, g * v = v * g := fun v hv => by_contra (fun h => hcon ⟨v, hv, h⟩)
  have hW : oc (centralizer ({e.s₁} : Set G)) ≤ zpowers e.s₁ := by
    refine U_le_PF hz e f.toFPart (U := oc (centralizer ({e.s₁} : Set G))) le_rfl
      (fun k hk u hu => conj_mem_oc (F_le_centralizerF e f.toFPart hk) hu) hg hg1 (fun u hu => ?_)
    obtain ⟨c, hc, v, hv, rfl⟩ := W_eq_sup_V hz f hWc hu
    have hgc : c * g = g * c := zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart hg) hc
    calc g * (c * v) = (g * c) * v := by group
      _ = (c * g) * v := by rw [hgc]
      _ = c * (g * v) := by group
      _ = c * (v * g) := by rw [hcon' v hv]
      _ = c * v * g := by group
  have := Subgroup.card_le_of_le hW
  rw [hW5, Nat.card_zpowers, e.s₁_ord] at this
  norm_num at this


end CFSG.GH74.Uniqueness.SU.SU13
