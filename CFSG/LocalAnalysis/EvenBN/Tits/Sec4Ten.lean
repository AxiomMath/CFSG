module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Seven
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.FiveLocal
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] noncomputable def x₅ (d : Data G) : G := d.lift Model.hatX

@[expose] noncomputable def fu₂ (d : Data G) : G := d.lift Model.fiveU₂

omit [Finite G] in
theorem lift_pow (d : Data G) {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) (n : ℕ) :
    d.lift (a ^ n) = d.lift a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, d.lift_one]
  | succ n ih => rw [pow_succ, pow_succ, d.lift_mul (pow_mem ha n) ha, ih]

omit [Finite G] in
theorem orderOf_lift (d : Data G) {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) :
    orderOf (d.lift a) = orderOf a := by
  rw [d.lift_eq ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]

omit [Finite G] in
theorem lift_comm_iff (d : Data G) {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD)
    (hb : b ∈ titsD) : d.lift a * d.lift b = d.lift b * d.lift a ↔ a * b = b * a := by
  constructor
  · intro h
    rw [← d.lift_mul ha hb, ← d.lift_mul hb ha] at h
    exact d.lift_inj (mul_mem ha hb) (mul_mem hb ha) h
  · exact d.lift_comm ha hb

omit [Finite G] in
theorem z_facts
    (d : Data G) : d.z * d.z = 1 ∧ d.z ≠ 1 := by
  obtain ⟨-, hzz⟩ := Model.titsZ_hatX
  refine ⟨?_, fun h => titsZ_ne_one (d.lift_inj titsZ_mem_titsD (one_mem _)
    (by rw [d.lift_titsZ, d.lift_one, h]))⟩
  rw [← d.lift_titsZ, ← d.lift_mul titsZ_mem_titsD titsZ_mem_titsD, hzz, d.lift_one]

omit [Finite G] in
theorem five_facts
    (d : Data G) :
    orderOf d.x₅ = 5 ∧ d.x₅ * d.z = d.z * d.x₅ ∧ d.pv 2 * d.z = d.z * d.pv 2 ∧
      d.pv 2 * d.pv 2 = 1 ∧ d.pv 2 * d.x₅ * (d.pv 2)⁻¹ = d.x₅⁻¹ ∧ d.pv 2 ∈ d.zL ∧
      d.z * d.pv 2 ∈ d.vL ∧ d.fu₂ * d.z = d.z * d.fu₂ ∧ d.fu₂ * d.x₅ * d.fu₂⁻¹ = d.x₅ ^ 3 ∧
      d.fu₂ * d.fu₂ = d.z * d.pv 2 := by
  obtain ⟨hXH, hX5, -, -, -⟩ := Model.hatX_facts
  obtain ⟨hL2, hS2, hinv2, hc2, hv2H, hvv⟩ := Model.parrottV_two_facts
  obtain ⟨hUH, hUx, hUU⟩ := Model.fiveU₂_facts
  obtain ⟨hzx, -⟩ := Model.titsZ_hatX
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  have hv2D : Model.parrottV 2 ∈ titsD := titsH_le_titsD hv2H
  have hUD : Model.fiveU₂ ∈ titsD := titsH_le_titsD hUH
  have hHz : ∀ h ∈ titsH, h * titsZ = titsZ * h := fun h hh => by
    rw [← titsD_centralizer_z] at hh
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hh).2
  have ez : d.lift titsZ = d.z := d.lift_titsZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [x₅, d.orderOf_lift hXD, hX5]
  · rw [x₅, ← ez]
    exact d.lift_comm hXD titsZ_mem_titsD hzx.symm
  · rw [pv, ← ez]
    exact d.lift_comm hv2D titsZ_mem_titsD hc2
  · rw [pv, ← d.lift_mul hv2D hv2D, hvv, d.lift_one]
  · rw [pv, x₅, ← d.lift_conj hv2D hXD, hinv2, d.lift_inv hXD]
  · rw [zL_eq]
    exact ⟨_, ⟨hv2D, hL2⟩, rfl⟩
  · rw [vL_eq, pv, ← ez, ← d.lift_mul titsZ_mem_titsD hv2D]
    exact ⟨_, ⟨mul_mem titsZ_mem_titsD hv2D, hS2⟩, rfl⟩
  · rw [fu₂, ← ez]
    exact d.lift_comm hUD titsZ_mem_titsD (hHz _ hUH)
  · rw [fu₂, x₅, ← d.lift_conj hUD hXD, hUx, d.lift_pow hXD]
  · rw [fu₂, pv, ← ez, ← d.lift_mul hUD hUD, hUU, d.lift_mul titsZ_mem_titsD hv2D]

theorem Hyp.mem_L_of_pow_five
    (hd : d.Hyp) {y : G} (hy : y ∈ centralizer ({d.t} : Set G)) (h5 : y ^ 5 = 1) : y ∈ d.L := by
  have : (d.L.subgroupOf (centralizer ({d.t} : Set G))).Normal := hd.normal
  set q : centralizer ({d.t} : Set G) ⧸ d.L.subgroupOf (centralizer ({d.t} : Set G)) :=
    QuotientGroup.mk ⟨y, hy⟩ with hq
  have hq5 : q ^ 5 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have : (⟨y, hy⟩ : centralizer ({d.t} : Set G)) ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [this, QuotientGroup.mk_one]
  have hdvd5 : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
  have hdvdc := orderOf_dvd_natCard q
  have h1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd5 with h | h
    · exact h
    · exfalso
      rw [h] at hdvdc
      rcases hd.card_quotient with hc | hc <;> rw [hc] at hdvdc <;> norm_num at hdvdc
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem Hyp.conj_t_cases_of_failure
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) {g : G}
    (hg : g * d.t * g⁻¹ ∈ centralizer ({d.t} : Set G)) :
    g * d.t * g⁻¹ = d.t ∨ ∃ m ∈ d.L, g * d.t * g⁻¹ = m * (d.t * d.z) * m⁻¹ := by
  rcases hd.conj_t_cases hg with h | ⟨m, hm, h | h⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hm, h⟩
  · exfalso
    apply hfail
    refine ⟨m⁻¹ * g, ?_⟩
    calc m⁻¹ * g * d.t * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * d.t * g⁻¹) * m := by group
      _ = d.t * d.v := by rw [h]; group

theorem Hyp.thm411
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) {c : G}
    (hc : c ∈ centralizer ({d.t * d.z} : Set G)) : c * d.z * c⁻¹ ≠ d.pv 2 := by
  intro h
  obtain ⟨hzz, -⟩ := z_facts d
  obtain ⟨-, -, -, -, -, -, hzv, -⟩ := five_facts d
  have hct : c * (d.t * d.z) * c⁻¹ = d.t * d.z := by
    rw [mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  have e : c * d.t * c⁻¹ = d.t * (d.z * d.pv 2) := by
    calc c * d.t * c⁻¹ = (c * (d.t * d.z) * c⁻¹) * (c * d.z * c⁻¹) := by
          rw [show c * (d.t * d.z) * c⁻¹ * (c * d.z * c⁻¹) = c * (d.t * (d.z * d.z)) * c⁻¹ by
            group, hzz, mul_one]
      _ = d.t * (d.z * d.pv 2) := by rw [hct, h, mul_assoc]
  exact hfail ((hd.t_mul_mem_tG_iff_of_vL hzv).1 ⟨c, e⟩)

theorem Hyp.ρ_conj_of_conj_lift
    (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G)) {a b : Equiv.Perm (Fin 1755)}
    (ha : a ∈ titsD) (hb : b ∈ titsD) (h : x * d.lift a * x⁻¹ = d.lift b) :
    (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a = b * d.ρ ⟨x, hx⟩ := by
  have h2 : ((d.θ ⟨x * d.lift a * x⁻¹, hd.conj_mem ⟨x, hx⟩ (d.lift_mem a)⟩ : titsD) :
      Equiv.Perm (Fin 1755)) = b := by
    have e : (⟨x * d.lift a * x⁻¹, hd.conj_mem ⟨x, hx⟩ (d.lift_mem a)⟩ : d.L) =
        ⟨d.lift b, d.lift_mem b⟩ := Subtype.ext h
    rw [e, d.θ_lift hb]
  have h1 := hd.θ_conj ⟨x, hx⟩ ⟨d.lift a, d.lift_mem a⟩
  rw [d.θ_lift ha] at h1
  have h3 := h1.symm.trans h2
  rw [← h3, inv_mul_cancel_right]

theorem Hyp.thm412_range
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) : d.ρ.range = ⊤ := by
  rcases hd.range_ρ with hR | hR
  swap
  · exact hR
  exfalso
  obtain ⟨hzz, hz1⟩ := z_facts d
  obtain ⟨hx5, hxz, -, -, -, -, -, huz, hux, huu⟩ := five_facts d
  obtain ⟨hXH, -, -, -, -⟩ := Model.hatX_facts
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  have ht2 := hd.t_mul_self
  have hzL : d.z ∈ d.L := d.z_mem
  have hxL : d.x₅ ∈ d.L := d.lift_mem _
  have huL : d.fu₂ ∈ d.L := d.lift_mem _
  have hLt : ∀ l ∈ d.L, l * d.t = d.t * l := fun l hl => hd.L_comm_t hl
  have hzt := hLt _ hzL
  have htl : ∀ l ∈ d.L, d.t * l * d.t = l := fun l hl => by
    rw [← hLt l hl, mul_assoc, ht2, mul_one]
  have htzC : ∀ l ∈ d.L, l * d.z = d.z * l → l ∈ centralizer ({d.t * d.z} : Set G) := by
    intro l hl hlz
    rw [mem_centralizer_singleton_iff]
    calc l * (d.t * d.z) = l * d.t * d.z := by group
      _ = d.t * l * d.z := by rw [hLt l hl]
      _ = d.t * (l * d.z) := by group
      _ = d.t * (d.z * l) := by rw [hlz]
      _ = d.t * d.z * l := by group
  obtain ⟨g, hg⟩ := hd.exists_conj_eq_t_mul_z
  have hh1 : g⁻¹ * (d.t * d.z) * g = d.t := by rw [← hg]; group
  have htz_comm : d.t * (d.t * d.z) = d.t * d.z * d.t := by rw [mul_assoc d.t d.z d.t, hzt]
  have hsC : g⁻¹ * d.t * g⁻¹⁻¹ ∈ centralizer ({d.t} : Set G) := by
    rw [inv_inv, mem_centralizer_singleton_iff]
    calc g⁻¹ * d.t * g * d.t = g⁻¹ * d.t * g * (g⁻¹ * (d.t * d.z) * g) := by rw [hh1]
      _ = g⁻¹ * (d.t * (d.t * d.z)) * g := by group
      _ = g⁻¹ * (d.t * d.z * d.t) * g := by rw [htz_comm]
      _ = g⁻¹ * (d.t * d.z) * g * (g⁻¹ * d.t * g) := by group
      _ = d.t * (g⁻¹ * d.t * g) := by rw [hh1]
  rcases hd.conj_t_cases_of_failure hfail hsC with hs | ⟨m, hm, hs⟩
  · rw [inv_inv] at hs
    apply hz1
    have e : g⁻¹ * d.z * g = 1 := by
      calc g⁻¹ * d.z * g = (g⁻¹ * d.t * g)⁻¹ * (g⁻¹ * (d.t * d.z) * g) := by group
        _ = 1 := by rw [hs, hh1, inv_mul_cancel]
    calc d.z = g * (g⁻¹ * d.z * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  rw [inv_inv] at hs
  have hmt := hLt m hm
  have hmzL : m * d.z * m⁻¹ ∈ d.L := mul_mem (mul_mem hm hzL) (inv_mem hm)
  have hz' : g⁻¹ * d.z * g = m * d.z * m⁻¹ := by
    calc g⁻¹ * d.z * g = (g⁻¹ * d.t * g) * (g⁻¹ * (d.t * d.z) * g) := by
          rw [show (g⁻¹ * d.t * g) * (g⁻¹ * (d.t * d.z) * g) = g⁻¹ * (d.t * d.t * d.z) * g by
            group, ht2, one_mul]
      _ = m * (d.t * d.z) * m⁻¹ * d.t := by rw [hs, hh1]
      _ = d.t * (m * d.z * m⁻¹) * d.t := by
          rw [show m * (d.t * d.z) * m⁻¹ = (m * d.t) * d.z * m⁻¹ by group, hmt]
          group
      _ = m * d.z * m⁻¹ := htl _ hmzL
  have hxC : d.x₅ ∈ centralizer ({d.t * d.z} : Set G) := htzC _ hxL hxz
  obtain ⟨x'', hx''⟩ : ∃ y : G, y = m⁻¹ * (g⁻¹ * d.x₅ * g) * m := ⟨_, rfl⟩
  have e1 : m⁻¹ * (g⁻¹ * (d.t * d.z) * g) * m = d.t := by
    rw [hh1, mul_assoc, ← hmt, inv_mul_cancel_left]
  have e2 : m⁻¹ * (g⁻¹ * d.z * g) * m = d.z := by rw [hz']; group
  have hx''t : x'' ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hxc := mem_centralizer_singleton_iff.1 hxC
    calc x'' * d.t = x'' * (m⁻¹ * (g⁻¹ * (d.t * d.z) * g) * m) := by rw [e1]
      _ = m⁻¹ * (g⁻¹ * (d.x₅ * (d.t * d.z)) * g) * m := by rw [hx'']; group
      _ = m⁻¹ * (g⁻¹ * ((d.t * d.z) * d.x₅) * g) * m := by rw [hxc]
      _ = (m⁻¹ * (g⁻¹ * (d.t * d.z) * g) * m) * x'' := by rw [hx'']; group
      _ = d.t * x'' := by rw [e1]
  have hx''z : x'' * d.z = d.z * x'' := by
    calc x'' * d.z = x'' * (m⁻¹ * (g⁻¹ * d.z * g) * m) := by rw [e2]
      _ = m⁻¹ * (g⁻¹ * (d.x₅ * d.z) * g) * m := by rw [hx'']; group
      _ = m⁻¹ * (g⁻¹ * (d.z * d.x₅) * g) * m := by rw [hxz]
      _ = (m⁻¹ * (g⁻¹ * d.z * g) * m) * x'' := by rw [hx'']; group
      _ = d.z * x'' := by rw [e2]
  have hx''conj : x'' = (m⁻¹ * g⁻¹) * d.x₅ * (m⁻¹ * g⁻¹)⁻¹ := by rw [hx'']; group
  have hx''o : orderOf x'' = 5 := by
    rw [hx''conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx5]
  have hx''5 : x'' ^ 5 = 1 := by rw [← hx''o]; exact pow_orderOf_eq_one _
  have hx''L : x'' ∈ d.L := hd.mem_L_of_pow_five hx''t hx''5
  obtain ⟨a, haD, hxa⟩ : ∃ a ∈ titsD, d.lift a = x'' :=
    ⟨_, (d.θ ⟨x'', hx''L⟩).2, d.lift_θ ⟨x'', hx''L⟩⟩
  have haz : a * titsZ = titsZ * a := by
    rw [← d.lift_comm_iff haD titsZ_mem_titsD, hxa, d.lift_titsZ]
    exact hx''z
  have haH : a ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨haD, mem_centralizer_singleton_iff.2 haz⟩
  have ha5 : orderOf a = 5 := by rw [← d.orderOf_lift haD, hxa, hx''o]
  obtain ⟨η, hηH, hη⟩ := Model.exists_titsH_conj_hatX haH ha5
  have hηD : η ∈ titsD := titsH_le_titsD hηH
  have hηz : η * titsZ = titsZ * η := by
    rw [← titsD_centralizer_z] at hηH
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hηH).2
  obtain ⟨c, hc⟩ : ∃ c : G, c = d.lift η := ⟨_, rfl⟩
  have hcL : c ∈ d.L := hc ▸ d.lift_mem η
  have hcz : c * d.z = d.z * c := by
    rw [hc, ← d.lift_titsZ]
    exact d.lift_comm hηD titsZ_mem_titsD hηz
  have hcx : c * x'' * c⁻¹ = d.x₅ := by
    rw [hc, ← hxa, ← d.lift_conj hηD haD, hη]
    rfl
  obtain ⟨k, hk⟩ : ∃ k : G, k = c * m⁻¹ * g⁻¹ := ⟨_, rfl⟩
  have hkx : k * d.x₅ * k⁻¹ = d.x₅ := by
    calc k * d.x₅ * k⁻¹ = c * (m⁻¹ * (g⁻¹ * d.x₅ * g) * m) * c⁻¹ := by rw [hk]; group
      _ = d.x₅ := by rw [← hx'', hcx]
  have hkz : k * d.z * k⁻¹ = d.z := by
    calc k * d.z * k⁻¹ = c * (m⁻¹ * (g⁻¹ * d.z * g) * m) * c⁻¹ := by rw [hk]; group
      _ = c * d.z * c⁻¹ := by rw [e2]
      _ = d.z := by rw [hcz, mul_inv_cancel_right]
  have hktz : k * (d.t * d.z) * k⁻¹ = d.t := by
    calc k * (d.t * d.z) * k⁻¹ = c * (m⁻¹ * (g⁻¹ * (d.t * d.z) * g) * m) * c⁻¹ := by
          rw [hk]; group
      _ = c * d.t * c⁻¹ := by rw [e1]
      _ = d.t := by rw [hLt _ hcL, mul_inv_cancel_right]
  have hkx' : k⁻¹ * d.x₅ * k = d.x₅ := by
    calc k⁻¹ * d.x₅ * k = k⁻¹ * (k * d.x₅ * k⁻¹) * k := by rw [hkx]
      _ = d.x₅ := by group
  have huC : d.fu₂ ∈ centralizer ({d.t * d.z} : Set G) := htzC _ huL huz
  obtain ⟨u', hu'⟩ : ∃ u' : G, u' = k * d.fu₂ * k⁻¹ := ⟨_, rfl⟩
  have hu't : u' ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have huc := mem_centralizer_singleton_iff.1 huC
    calc u' * d.t = u' * (k * (d.t * d.z) * k⁻¹) := by rw [hktz]
      _ = k * (d.fu₂ * (d.t * d.z)) * k⁻¹ := by rw [hu']; group
      _ = k * ((d.t * d.z) * d.fu₂) * k⁻¹ := by rw [huc]
      _ = (k * (d.t * d.z) * k⁻¹) * u' := by rw [hu']; group
      _ = d.t * u' := by rw [hktz]
  have hu'z : u' * d.z = d.z * u' := by
    calc u' * d.z = u' * (k * d.z * k⁻¹) := by rw [hkz]
      _ = k * (d.fu₂ * d.z) * k⁻¹ := by rw [hu']; group
      _ = k * (d.z * d.fu₂) * k⁻¹ := by rw [huz]
      _ = (k * d.z * k⁻¹) * u' := by rw [hu']; group
      _ = d.z * u' := by rw [hkz]
  have hu'x : u' * d.lift Model.hatX * u'⁻¹ = d.lift (Model.hatX ^ 3) := by
    rw [d.lift_pow hXD]
    change u' * d.x₅ * u'⁻¹ = d.x₅ ^ 3
    calc u' * d.x₅ * u'⁻¹ = k * (d.fu₂ * (k⁻¹ * d.x₅ * k) * d.fu₂⁻¹) * k⁻¹ := by
          rw [hu']; group
      _ = k * d.x₅ ^ 3 * k⁻¹ := by rw [hkx', hux]
      _ = (k * d.x₅ * k⁻¹) ^ 3 := Model.mul_pow_mul_inv k d.x₅ 3
      _ = d.x₅ ^ 3 := by rw [hkx]
  have hu'u' : u' * u' = d.z * (k * d.pv 2 * k⁻¹) := by
    calc u' * u' = k * (d.fu₂ * d.fu₂) * k⁻¹ := by rw [hu']; group
      _ = k * (d.z * d.pv 2) * k⁻¹ := by rw [huu]
      _ = (k * d.z * k⁻¹) * (k * d.pv 2 * k⁻¹) := by group
      _ = d.z * (k * d.pv 2 * k⁻¹) := by rw [hkz]
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : Equiv.Perm (Fin 1755), a₂ = d.ρ ⟨u', hu't⟩ := ⟨_, rfl⟩
  have ha₂D : a₂ ∈ titsD := by
    have h : d.ρ ⟨u', hu't⟩ ∈ d.ρ.range := ⟨_, rfl⟩
    rw [hR, mem_subgroupOf] at h
    rw [ha₂]
    exact h
  have ha₂z : a₂ * titsZ = titsZ * a₂ := by
    rw [ha₂]
    exact (hd.commute_lift_iff hu't titsZ_mem_titsD).1 (by rw [d.lift_titsZ]; exact hu'z)
  have ha₂H : a₂ ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨ha₂D, mem_centralizer_singleton_iff.2 ha₂z⟩
  have ha₂x : a₂ * Model.hatX * a₂⁻¹ = Model.hatX ^ 3 := by
    have h := hd.ρ_conj_of_conj_lift hu't hXD (pow_mem hXD 3) hu'x
    rw [← ha₂] at h
    rw [h, mul_inv_cancel_right]
  have ha₂sq : a₂ * a₂ * Model.hatX * (a₂ * a₂)⁻¹ = Model.hatX⁻¹ := by
    obtain ⟨-, hX5, -, -, -⟩ := Model.hatX_facts
    have h5 : Model.hatX ^ 5 = 1 := by rw [← hX5]; exact pow_orderOf_eq_one _
    calc a₂ * a₂ * Model.hatX * (a₂ * a₂)⁻¹ = a₂ * (a₂ * Model.hatX * a₂⁻¹) * a₂⁻¹ := by group
      _ = a₂ * Model.hatX ^ 3 * a₂⁻¹ := by rw [ha₂x]
      _ = (a₂ * Model.hatX * a₂⁻¹) ^ 3 := Model.mul_pow_mul_inv a₂ Model.hatX 3
      _ = Model.hatX⁻¹ := by
          rw [ha₂x, ← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ,
            show 3 * 3 + 1 = 5 * 2 by norm_num, pow_mul, h5, one_pow]
  have hlong := Model.isLong_titsZ_mul_sq ha₂H
    (by rw [ha₂x]; exact pow_mem (mem_zpowers _) 3) ha₂sq
  obtain ⟨z₁'', hz₁''⟩ : ∃ y : G, y = k * d.pv 2 * k⁻¹ := ⟨_, rfl⟩
  have hz₁''eq : z₁'' = d.z * (u' * u') := by
    rw [hu'u', ← mul_assoc, hzz, one_mul, hz₁'']
  have hu'sq : u' * u' ∈ d.L := by
    rcases hd.eq_lift_or hu't (by rw [← ha₂]; exact ha₂D) with e | e
    · rw [e]
      exact mul_mem (d.lift_mem _) (d.lift_mem _)
    · rw [e]
      have hl := d.lift_mem (d.ρ ⟨u', hu't⟩ : Equiv.Perm (Fin 1755))
      rw [show d.t * d.lift (d.ρ ⟨u', hu't⟩ : Equiv.Perm (Fin 1755)) *
          (d.t * d.lift (d.ρ ⟨u', hu't⟩ : Equiv.Perm (Fin 1755))) =
          (d.t * d.lift (d.ρ ⟨u', hu't⟩ : Equiv.Perm (Fin 1755)) * d.t) *
            d.lift (d.ρ ⟨u', hu't⟩ : Equiv.Perm (Fin 1755)) by group, htl _ hl]
      exact mul_mem hl hl
  have hz₁''L : z₁'' ∈ d.L := by rw [hz₁''eq]; exact mul_mem hzL hu'sq
  have hρz₁ : (d.ρ ⟨z₁'', hd.L_le hz₁''L⟩ : Equiv.Perm (Fin 1755)) = titsZ * (a₂ * a₂) := by
    have e : (⟨z₁'', hd.L_le hz₁''L⟩ : centralizer ({d.t} : Set G)) =
        ⟨d.lift titsZ, hd.L_le (d.lift_mem _)⟩ * (⟨u', hu't⟩ * ⟨u', hu't⟩) :=
      Subtype.ext (by
        show z₁'' = d.lift titsZ * (u' * u')
        rw [hz₁''eq, d.lift_titsZ])
    rw [e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hd.ρ_lift titsZ_mem_titsD, ← ha₂]
  have hθz : z₁'' = d.lift (titsZ * (a₂ * a₂)) := by
    have h := hd.ρ_eq_θ ⟨z₁'', hz₁''L⟩
    rw [← hρz₁, h, d.lift_θ]
  have hz₁''zL : z₁'' ∈ d.zL := by
    rw [zL_eq, hθz]
    exact ⟨_, ⟨mul_mem titsZ_mem_titsD (mul_mem ha₂D ha₂D), hlong⟩, rfl⟩
  obtain ⟨m', hm'L, hm'⟩ := hz₁''zL
  have hkt : k⁻¹ * d.t * k = d.t * d.z := by
    calc k⁻¹ * d.t * k = k⁻¹ * (k * (d.t * d.z) * k⁻¹) * k := by rw [hktz]
      _ = d.t * d.z := by group
  have hm't := hLt m' hm'L
  apply hd.thm411 hfail (c := k⁻¹ * m' * k)
  · rw [mem_centralizer_singleton_iff]
    calc k⁻¹ * m' * k * (d.t * d.z) = k⁻¹ * m' * (k * (d.t * d.z) * k⁻¹) * k := by group
      _ = k⁻¹ * (m' * d.t) * k := by rw [hktz]; group
      _ = k⁻¹ * (d.t * m') * k := by rw [hm't]
      _ = (k⁻¹ * d.t * k) * (k⁻¹ * m' * k) := by group
      _ = d.t * d.z * (k⁻¹ * m' * k) := by rw [hkt]
  · calc k⁻¹ * m' * k * d.z * (k⁻¹ * m' * k)⁻¹ =
        k⁻¹ * (m' * (k * d.z * k⁻¹) * m'⁻¹) * k := by group
      _ = k⁻¹ * z₁'' * k := by rw [hkz, hm']
      _ = d.pv 2 := by rw [hz₁'']; group

theorem Hyp.thm412_three
    (hd : d.Hyp) {g : G} (hg : g * d.t * g⁻¹ ∈ centralizer ({d.x₅} : Set G)) :
    ∃ c ∈ centralizer ({d.x₅} : Set G), c * d.t * c⁻¹ = g * d.t * g⁻¹ := by
  obtain ⟨hx5, -⟩ := five_facts d
  obtain ⟨hXH, -, -, -, -⟩ := Model.hatX_facts
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  refine manning_conj_centralizer (fun g' hg' => ?_) hg
  have ho : orderOf (g' * d.x₅ * g'⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx5]
  have h5 : (g' * d.x₅ * g'⁻¹) ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hL := hd.mem_L_of_pow_five hg' h5
  obtain ⟨a, haD, hxa⟩ : ∃ a ∈ titsD, d.lift a = g' * d.x₅ * g'⁻¹ :=
    ⟨_, (d.θ ⟨_, hL⟩).2, d.lift_θ ⟨_, hL⟩⟩
  have ha5 : orderOf a = 5 := by rw [← d.orderOf_lift haD, hxa, ho]
  obtain ⟨δ, hδD, hδ⟩ := Model.exists_conj_hatX_of_orderOf_five haD ha5
  refine ⟨d.lift δ, hd.L_le (d.lift_mem δ), ?_⟩
  calc d.lift δ * d.x₅ * (d.lift δ)⁻¹ = d.lift (δ * Model.hatX * δ⁻¹) :=
        (d.lift_conj hδD hXD).symm
    _ = g' * d.x₅ * g'⁻¹ := by rw [hδ, hxa]

theorem Hyp.thm412_two
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) :
    ∃ w : G, ∃ hwt : w ∈ centralizer ({d.t} : Set G),
      (d.ρ ⟨w, hwt⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 ∧
      w ∈ centralizer ({d.x₅} : Set G) ∧ w * w = d.z ∧ orderOf w = 4 ∧
      CFSG.Open.fusionIsSylowIn 2 (closure {d.t, w})
        (centralizer ({d.t} : Set G) ⊓ centralizer ({d.x₅} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzz, hz1⟩ := z_facts d
  obtain ⟨hXH, -, -, h5x, -⟩ := Model.hatX_facts
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  obtain ⟨-, -, s5, -, -⟩ := Model.parrott_squares
  have ho5 := Model.orderOf_parrottV (i := 5) (by norm_num) (by norm_num)
  rw [ite_eq_left (by decide)] at ho5
  obtain ⟨h5S, -, -⟩ := Model.parrottV_five
  have h5A : Model.parrottV 5 ∈ titsA :=
    (Model.twoF4S_le_twoF4H.trans Model.twoF4H_le_titsA) h5S
  set v5 : titsA := ⟨Model.parrottV 5, h5A⟩ with hv5
  have hsurj : Function.Surjective d.ρ := MonoidHom.range_eq_top.1 (hd.thm412_range hfail)
  obtain ⟨⟨w, hwt⟩, hw⟩ := hsurj v5
  have hρw : (d.ρ ⟨w, hwt⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 := by rw [hw]
  have ht2 := hd.t_mul_self
  have hxL : d.x₅ ∈ d.L := d.lift_mem _
  have hzL : d.z ∈ d.L := d.z_mem
  have hwx : w ∈ centralizer ({d.x₅} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (hd.commute_lift_iff hwt hXD).2 (by rw [hρw]; exact h5x)
  have hww : w * w = d.z := by
    have hwwt : w * w ∈ centralizer ({d.t} : Set G) := mul_mem hwt hwt
    have hρ2 : (d.ρ ⟨w * w, hwwt⟩ : Equiv.Perm (Fin 1755)) = titsZ := by
      have e : (⟨w * w, hwwt⟩ : centralizer ({d.t} : Set G)) = ⟨w, hwt⟩ * ⟨w, hwt⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul, hρw, s5, Model.parrottV_twelve]
    rcases hd.eq_lift_or hwwt (by rw [hρ2]; exact titsZ_mem_titsD) with e | e
    · rw [e, hρ2, d.lift_titsZ]
    · exfalso
      rw [hρ2, d.lift_titsZ] at e
      obtain ⟨g, hg⟩ := hd.exists_conj_eq_t_mul_z
      exact hd.mul_self_ne_conj_t w g (by rw [e, hg])
  have hw4 : orderOf w = 4 := by
    have h2 : ¬ w ^ 2 ^ 1 = 1 := by rw [pow_one, sq, hww]; exact hz1
    have h4 : w ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, sq, hww, hzz]
    have := orderOf_eq_prime_pow h2 h4
    norm_num at this
    exact this
  set K : Subgroup G := ((zpowers v5).comap d.ρ).map (centralizer ({d.t} : Set G)).subtype
    with hK
  have hker : ∀ y (hy : y ∈ centralizer ({d.t} : Set G)), d.ρ ⟨y, hy⟩ = 1 → y = 1 ∨ y = d.t := by
    intro y hy h1
    have hk : y ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) :=
      ⟨(hd.ρ_eq_one_iff ⟨y, hy⟩).1 h1, hy⟩
    rw [Model.kernel_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hk
    exact hk
  have htw_mem : ∀ y ∈ K, y ∈ closure {d.t, w} := by
    rintro _ ⟨⟨y, hy⟩, hyK, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (mem_comap.1 hyK)
    have h1 : d.ρ (⟨y, hy⟩ * (⟨w, hwt⟩ ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hw, hj, mul_inv_cancel]
    have hmem : y * (w ^ j)⁻¹ ∈ centralizer ({d.t} : Set G) :=
      mul_mem hy (inv_mem (zpow_mem hwt j))
    have e : y = (y * (w ^ j)⁻¹) * w ^ j := by group
    have hwj : w ^ j ∈ closure {d.t, w} := zpow_mem (subset_closure (by simp)) j
    rcases hker _ hmem (by
      have : (⟨y * (w ^ j)⁻¹, hmem⟩ : centralizer ({d.t} : Set G)) =
          ⟨y, hy⟩ * (⟨w, hwt⟩ ^ j)⁻¹ := Subtype.ext (by simp)
      rw [this]
      exact h1) with h | h
    · change y ∈ closure {d.t, w}
      rw [e, h, one_mul]
      exact hwj
    · change y ∈ closure {d.t, w}
      rw [e, h]
      exact mul_mem (subset_closure (by simp)) hwj
  have hclK : closure {d.t, w} ≤ K := by
    rw [closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]
      refine ⟨⟨d.t, d.t_mem_centralizer⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      have : d.ρ ⟨d.t, d.t_mem_centralizer⟩ = 1 := hd.ρ_t
      rw [this]
      exact one_mem _
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨⟨w, hwt⟩, by rw [SetLike.mem_coe, mem_comap, hw]; exact mem_zpowers _, rfl⟩
  have hKeq : K = closure {d.t, w} := le_antisymm htw_mem hclK
  have hK2 : IsPGroup 2 K := by
    rintro ⟨_, ⟨⟨y, hy⟩, hyK, rfl⟩⟩
    refine ⟨3, ?_⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (mem_comap.1 hyK)
    have hv54 : v5 ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, show (v5 : Equiv.Perm (Fin 1755)) =
        Model.parrottV 5 from rfl, ← ho5, pow_orderOf_eq_one]
    have h1 : d.ρ (⟨y, hy⟩ ^ 4) = 1 := by
      rw [map_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv54,
        one_zpow]
    have hmem : y ^ 4 ∈ centralizer ({d.t} : Set G) := pow_mem hy 4
    have h8 : y ^ 8 = 1 := by
      rcases hker (y ^ 4) hmem (by
        have : (⟨y ^ 4, hmem⟩ : centralizer ({d.t} : Set G)) = ⟨y, hy⟩ ^ 4 :=
          Subtype.ext (by simp)
        rw [this]
        exact h1) with h | h
      · rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, h, one_pow]
      · rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, h, sq, ht2]
    apply Subtype.ext
    simp [h8]
  refine ⟨w, hwt, hρw, hwx, hww, hw4, ?_, ?_, ?_⟩
  ·
    rw [closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]
      exact ⟨d.t_mem_centralizer, mem_centralizer_singleton_iff.2 (hd.L_comm_t hxL).symm⟩
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨hwt, hwx⟩
  · rw [← hKeq]
    exact hK2
  ·
    intro P hPle hP2 hSP
    apply le_antisymm _ hSP
    rw [← hKeq]
    set Q : Subgroup (Equiv.Perm (Fin 1755)) :=
      ((P.subgroupOf (centralizer ({d.t} : Set G))).map d.ρ).map titsA.subtype with hQ
    have hQA : Q ≤ titsA := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hQC : Q ≤ centralizer {Model.hatX} := by
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact ((hd.commute_lift_iff p.2 hXD).1
        (mem_centralizer_singleton_iff.1 (hPle (mem_subgroupOf.1 hp)).2))
    have hQ2 : IsPGroup 2 Q :=
      (((hP2.comap_of_injective (centralizer ({d.t} : Set G)).subtype
        (subtype_injective _))).map d.ρ).map titsA.subtype
    have hQ4 := Model.card_le_four_of_le_centralizer_hatX hQA hQC hQ2
    have hwP : w ∈ P := hSP (subset_closure (by simp))
    have h5Q : Model.parrottV 5 ∈ Q :=
      ⟨d.ρ ⟨w, hwt⟩, ⟨⟨w, hwt⟩, mem_subgroupOf.2 hwP, rfl⟩, hρw⟩
    have hzQ : zpowers (Model.parrottV 5) = Q :=
      eq_of_le_of_card_ge (zpowers_le.2 h5Q) (by rw [Nat.card_zpowers, ho5]; exact hQ4)
    intro p hp
    have hpt : p ∈ centralizer ({d.t} : Set G) := (hPle hp).1
    have hpQ : (d.ρ ⟨p, hpt⟩ : Equiv.Perm (Fin 1755)) ∈ zpowers (Model.parrottV 5) := by
      rw [hzQ]
      exact ⟨d.ρ ⟨p, hpt⟩, ⟨⟨p, hpt⟩, mem_subgroupOf.2 hp, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hpQ
    refine ⟨⟨p, hpt⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_zpowers_iff]
    refine ⟨j, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, show (v5 : Equiv.Perm (Fin 1755)) = Model.parrottV 5 from rfl, hj]

theorem Hyp.secTwoHyp
    (hd : d.Hyp) (hfail : d.t * d.v ∉ d.tG) :
    ∃ w : G, ∃ hwx : w ∈ centralizer ({d.x₅} : Set G), w * w = d.z ∧
      SecTwoHyp (centralizer ({d.x₅} : Set G))
        ⟨d.t, mem_centralizer_singleton_iff.2 (hd.L_comm_t (d.lift_mem _)).symm⟩ ⟨w, hwx⟩ := by
  obtain ⟨w, hwt, -, hwx, hww, hw4, -, hS2, hS3⟩ := hd.thm412_two hfail
  set X := centralizer ({d.x₅} : Set G) with hX
  have htX : d.t ∈ X := mem_centralizer_singleton_iff.2 (hd.L_comm_t (d.lift_mem _)).symm
  set t' : X := ⟨d.t, htX⟩ with ht'
  set w' : X := ⟨w, hwx⟩ with hw'
  have hφ : Function.Injective X.subtype := subtype_injective _
  have hmapS : (secTwoR t' w').map X.subtype = closure {d.t, w} := by
    rw [secTwoR, MonoidHom.map_closure, Set.image_pair]
    rfl
  refine ⟨w, hwx, hww, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Subgroup.orderOf_mk]
    exact hd.t_two
  · rw [Subgroup.orderOf_mk]
    exact hw4
  · exact Subtype.ext (mem_centralizer_singleton_iff.1 hwt).symm
  · intro h
    have h' : w * w = d.t := by
      have := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, sq] at this
    apply hd.t_not_mem
    rw [← h', hww]
    exact d.z_mem
  · refine ⟨?_, ?_, ?_⟩
    · rw [secTwoR, closure_le]
      intro y hy
      rcases hy with h | h
      · rw [h]
        exact mem_centralizer_singleton_iff.2 rfl
      · rw [Set.mem_singleton_iff.1 h, SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hwt)
    · have hle : secTwoR t' w' ≤ (closure {d.t, w}).comap X.subtype := by
        rw [← hmapS]
        exact le_comap_map _ _
      exact (hS2.comap_of_injective X.subtype hφ).to_le hle
    · intro P hPH hP2 hSP
      have hP0 : P.map X.subtype ≤ centralizer ({d.t} : Set G) ⊓ X := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨?_, y.2⟩
        show (y : G) ∈ centralizer ({d.t} : Set G)
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hPH hy))
      have hSP0 : closure {d.t, w} ≤ P.map X.subtype := by
        rw [← hmapS]
        exact map_mono hSP
      have := hS3 (P.map X.subtype) hP0 (hP2.map X.subtype) hSP0
      rw [← hmapS] at this
      exact map_injective hφ this

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
