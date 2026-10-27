module

public import CFSG.Holt.H78.Sec4FinalB

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise


namespace FinConfig

section Cover

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem not_Z_le_Dsub (hS : Sec4Setting G Ω) (hcov : SETwoCoverConj) :
    ¬ ∀ z ∈ C.Z, z ∈ C.Dsub hS := by
  intro hall
  set L := C.Lpre hS with hLdef
  set O : Subgroup G := Subgroup.centralizer (C.Y : Set G) ⊓
    oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) with hOdef
  set N : Subgroup L := O.subgroupOf L with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      C.conj_mem_centralizer_inf_fixCore hS (C.Lpre_le hS g.2) hn⟩
  have hOL : O ≤ L := C.centralizer_inf_fixCore_le_Lpre hS
  have hLv : L ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    (C.Lpre_le hS).trans (C.centralizer_Y_le hS)
  set φ : L →* Equiv.Perm (C.Dv.Ψc C.i) := (C.piM hS).comp (Subgroup.inclusion hLv) with hφ
  have hφapp : ∀ l : L, φ l = C.piM hS ⟨l, hLv l.2⟩ := fun _ => rfl
  have hNφ : N ≤ φ.ker := fun n hn => by
    rw [MonoidHom.mem_ker, hφapp, C.piM_eq_one_iff]
    exact fun ω hω => (mem_fixingSubgroup_iff G).mp (Subgroup.map_subtype_le _
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)).2) ω hω
  set π : L ⧸ N →* Equiv.Perm (C.Dv.Ψc C.i) := QuotientGroup.lift N φ hNφ with hπ
  have hπmk : ∀ l : L, π (l : L ⧸ N) = φ l := fun l => QuotientGroup.lift_mk N hNφ l
  have hker : ∀ e ∈ π.ker, ∃ z ∈ C.Z, ∃ hzL : z ∈ L, e = ((⟨z, hzL⟩ : L) : L ⧸ N) := by
    intro e he
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    rw [MonoidHom.mem_ker, hπmk, hφapp] at he
    have hlP : (l : G) ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
      (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp he)
    obtain ⟨z, hz, hzq⟩ := C.exists_mem_Z_inv_mul_mem hS (C.Lpre_le hS l.2) hlP
    refine ⟨z, hz, C.Z_le_Lpre hS hz, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : z⁻¹ * (l : G) ∈ O := Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem (C.Z_le_centralizer_Y hS hz)) (C.Lpre_le hS l.2), hzq⟩
    simpa using inv_mem h1
  have hcen : π.ker ≤ Subgroup.center (L ⧸ N) := by
    intro e he
    obtain ⟨z, hz, hzL, rfl⟩ := hker e he
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (C.Lpre_le hS l.2) z (C.Z_le_Y hz)).symm)
  have hsq : ∀ e ∈ π.ker, e * e = 1 := by
    intro e he
    obtain ⟨z, hz, hzL, rfl⟩ := hker e he
    rw [← QuotientGroup.mk_mul, show (⟨z, hzL⟩ : L) * ⟨z, hzL⟩ = 1 from
      Subtype.ext (C.mul_self_eq_one_of_mem_Z hS hz), QuotientGroup.mk_one]
  have hZker : ∀ z (hz : z ∈ C.Z), ((⟨z, C.Z_le_Lpre hS hz⟩ : L) : L ⧸ N) ∈ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, hπmk, hφapp, C.piM_eq_one_iff]
    exact fun ω hω => (mem_fixingSubgroup_iff G).mp (C.Z_le_fixingSubgroup hS hz) ω hω
  have hcard : 4 ≤ Nat.card π.ker := by
    refine (C.four_le_card_Z hS).trans (Nat.card_le_card_of_injective
      (fun z : C.Z => (⟨_, hZker z z.2⟩ : π.ker)) fun z₁ z₂ h => ?_)
    have h1 := congrArg Subtype.val h
    simp only [QuotientGroup.eq] at h1
    have h2 : (z₁ : G)⁻¹ * z₂ ∈ C.Z := mul_mem (inv_mem z₁.2) z₂.2
    have h3 : (z₁ : G)⁻¹ * z₂ = 1 := eq_one_of_mem_oddCoreOf (Subgroup.mem_inf.mp h1).2
      (k := 1) (by rw [pow_one, pow_two]; exact C.mul_self_eq_one_of_mem_Z hS h2)
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hrange : π.range = C.Dv.M C.i := by
    ext m
    constructor
    · rintro ⟨e, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
      rw [hπmk, hφapp]
      exact ((C.mem_Lpre hS).mp l.2).2
    · intro hm
      obtain ⟨c, hc, rfl⟩ := C.exists_centralizer_Y_piM_eq hS hm
      exact ⟨((⟨c, (C.mem_Lpre hS).mpr ⟨hc, hm⟩⟩ : L) : L ⧸ N), by rw [hπmk, hφapp]⟩
  have hKO : ∀ k ∈ ⁅L, L⁆, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    C.conj_mem_centralizer_inf_fixCore hS (C.Lpre_le hS (Subgroup.commutator_le_self _ hk)) ho
  have hmkc : ∀ c (hc : c ∈ ⁅L, L⁆), ((⟨c, Subgroup.commutator_le_self _ hc⟩ : L) : L ⧸ N) ∈
      commutator (L ⧸ N) := by
    intro c hc
    obtain ⟨hcL, hc₀⟩ := mem_commutator_of_mem hc
    have h1 : (commutator L).map (QuotientGroup.mk' N) ≤ commutator (L ⧸ N) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h1 ⟨_, hc₀, rfl⟩
  have hperf : commutator (L ⧸ N) = ⊤ := by
    refine eq_top_iff.mpr fun e _ => ?_
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    obtain ⟨d, hd, z, hz, ho⟩ := C.exists_decomp hS l.2
    obtain ⟨d', hd', o', ho', hzd⟩ := exists_mul_of_mem_sup hKO (hall z hz)
    have hdd : d * d' ∈ ⁅L, L⁆ := mul_mem hd hd'
    have hoo : o' * (z⁻¹ * (d⁻¹ * l)) ∈ O := mul_mem ho' ho
    have hl : (l : G) = d * d' * (o' * (z⁻¹ * (d⁻¹ * l))) := by
      rw [← mul_assoc (d * d'), mul_assoc d, ← hzd]
      group
    have hmk : (l : L ⧸ N) = ((⟨d * d', Subgroup.commutator_le_self _ hdd⟩ : L) : L ⧸ N) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 : (d * d')⁻¹ * (l : G) ∈ O := by
        rw [hl, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hoo
      simpa using inv_mem h1
    rw [hmk]
    exact hmkc _ hdd
  obtain ⟨z₀, hz₀, hz₀1⟩ := C.exists_mem_Z_ne_one hS
  have hxL := C.x_mem_Lpre hS
  have hxx : ((⟨C.x, hxL⟩ : L) : L ⧸ N) * ((⟨C.x, hxL⟩ : L) : L ⧸ N) = 1 := by
    rw [← QuotientGroup.mk_mul, show (⟨C.x, hxL⟩ : L) * ⟨C.x, hxL⟩ = 1 from
      Subtype.ext (C.x_mul_self hS), QuotientGroup.mk_one]
  have hxk : ((⟨C.x, hxL⟩ : L) : L ⧸ N) ∉ π.ker := by
    rw [MonoidHom.mem_ker, hπmk, hφapp]
    intro h1
    have h2 := (C.piM_x hS).2.1
    rw [show (⟨C.x, C.x_mem_centralizer hS⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨C.x, hLv hxL⟩
      from rfl, h1, orderOf_one] at h2
    omega
  obtain ⟨g, hg⟩ := hcov (L ⧸ N) (C.Dv.Ψc C.i) π (hrange ▸ C.isNaturalSE_Dv C.i) hcen hsq hcard
    hperf _ hxx hxk _ (hZker z₀ hz₀)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hg
  set w : G := (g : G) * C.x * (g : G)⁻¹ with hw
  set o : G := w⁻¹ * (C.x * z₀) with ho
  have hoQ : Odd (orderOf o) := odd_orderOf_of_mem_oddCoreOf (Subgroup.mem_inf.mp hg).2
  have hww : w * w = 1 := by
    rw [hw, show (g : G) * C.x * (g : G)⁻¹ * ((g : G) * C.x * (g : G)⁻¹) =
      (g : G) * (C.x * C.x) * (g : G)⁻¹ by group, C.x_mul_self hS, mul_one, mul_inv_cancel]
  have hJ := (C.mul_mem_longInvAt hS hz₀ hz₀1).1
  have hxz2 : C.x * z₀ * (C.x * z₀) = 1 := by
    rw [← pow_two, ← hJ.1, pow_orderOf_eq_one]
  have hodd' : Odd (orderOf (w * o * w⁻¹)) := by
    rw [show w * o * w⁻¹ = MulAut.conj w o from rfl, MulEquiv.orderOf_eq]
    exact hoQ
  have hwo : w * o * w⁻¹ * w = C.x * z₀ := by
    rw [ho]
    group
  obtain ⟨p, -, hp⟩ := exists_zpowers_conj_eq_mul hodd' hww (by rw [hwo]; exact hxz2)
  rw [hwo, hw, show p * ((g : G) * C.x * (g : G)⁻¹) * p⁻¹ =
    (p * g) * C.x * (p * g)⁻¹ by group] at hp
  exact C.x_not_mem_longInv hS ((conj_mem_longInv_iff (p * g)).mp (hp ▸ hJ))

theorem exists_splitting (hS : Sec4Setting G Ω) (hcov : SETwoCoverConj) :
    ∃ Mc : Subgroup G, ∃ hMcY : Mc ≤ Subgroup.centralizer (C.Y : Set G),
      Subgroup.centralizer (C.Y : Set G) ⊓
          oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc ∧
      (∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ ∈ C.Dv.M C.i) ∧
      (∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
        C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ = m) ∧
      (∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
        g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) ∧
      (∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
        C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc) ∧
      (∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc) ∧
      (∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) → ∀ c ∈ Mc, h * c * h⁻¹ ∈ Mc) := by
  have hZD : ∀ z ∈ C.Z, z ∈ C.Dsub hS → z = 1 :=
    (C.Dsub_dichotomy hS).resolve_right (C.not_Z_le_Dsub hS hcov)
  have hDL := C.Dsub_le_Lpre hS
  have hOD : Subgroup.centralizer (C.Y : Set G) ⊓
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ C.Dsub hS := le_sup_right
  refine ⟨C.Dsub hS, hDL.trans (C.Lpre_le hS), hOD,
    fun g hg => ((C.mem_Lpre hS).mp (hDL hg)).2, fun m hm => ?_, fun g hg hgP => ?_,
    fun g hg hgM => ?_, fun g hg c hc => C.conj_mem_Dsub hS hg hc,
    fun h hh c hc => C.conj_mem_Dsub_of_normalizes_Y hS hh hc⟩
  · obtain ⟨d, hd, hdm⟩ := C.exists_commutator_piM_eq hS hm
    exact ⟨d, le_sup_left (a := ⁅C.Lpre hS, C.Lpre hS⁆) hd, hdm⟩
  · have hgY := C.Lpre_le hS (hDL hg)
    obtain ⟨z, hz, hzq⟩ := C.exists_mem_Z_inv_mul_mem hS hgY hgP
    have hzO : z⁻¹ * g ∈ Subgroup.centralizer (C.Y : Set G) ⊓
        oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (C.Z_le_centralizer_Y hS hz)) hgY, hzq⟩
    have hzD : z ∈ C.Dsub hS := by
      have h1 := mul_mem hg (inv_mem (hOD hzO))
      rwa [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at h1
    rw [hZD z hz hzD, inv_one, one_mul] at hzq
    exact hzq
  · obtain ⟨d, hd, z, hz, ho⟩ := C.exists_decomp hS ((C.mem_Lpre hS).mpr ⟨hg, hgM⟩)
    refine ⟨z⁻¹, inv_mem hz, ?_⟩
    have hdgY : d⁻¹ * g ∈ Subgroup.centralizer (C.Y : Set G) :=
      mul_mem (inv_mem (C.Lpre_le hS (Subgroup.commutator_le_self _ hd))) hg
    have hc : z⁻¹ * (d⁻¹ * g) = d⁻¹ * g * z⁻¹ :=
      Subgroup.mem_centralizer_iff.mp hdgY z⁻¹ (C.Z_le_Y (inv_mem hz))
    have h1 : d * (z⁻¹ * (d⁻¹ * g)) ∈ C.Dsub hS :=
      mul_mem (le_sup_left (a := ⁅C.Lpre hS, C.Lpre hS⁆) hd) (hOD ho)
    rwa [hc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h1

end Cover

end FinConfig

namespace FinConfig

section F6

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

structure IsSplitting (hS : Sec4Setting G Ω) (Mc : Subgroup G) : Prop where
  le_centralizer : Mc ≤ Subgroup.centralizer (C.Y : Set G)
  fixCore_le : Subgroup.centralizer (C.Y : Set G) ⊓
    oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc
  piM_mem : ∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (le_centralizer hg)⟩ ∈ C.Dv.M C.i
  exists_piM_eq : ∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
    C.piM hS ⟨g, C.centralizer_Y_le hS (le_centralizer hg)⟩ = m
  mem_fixCore : ∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
    g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
  exists_mul_mem : ∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
    C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc
  conj_mem : ∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc
  conj_mem_of_normalizes : ∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) →
    ∀ c ∈ Mc, h * c * h⁻¹ ∈ Mc

variable {C} {hS : Sec4Setting G Ω} {Mc : Subgroup G}

theorem IsSplitting.exists_conj (hMc : C.IsSplitting hS Mc) {zx : G} (hzx : zx ∈ C.Z)
    (hxzx : C.x * zx ∈ Mc) {r : G} (hrY : r ∈ Subgroup.centralizer (C.Y : Set G))
    (hr2 : r * r = 1) (hrM : C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩ ∈ C.Dv.M C.i)
    (hr1 : C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩ ≠ 1) {zr : G} (hzr : zr ∈ C.Z)
    (hrzr : r * zr ∈ Mc) : ∃ h : G, h * (C.x * (zx * zr⁻¹)) * h⁻¹ = r := by
  have hxv := C.x_mem_centralizer hS
  obtain ⟨hx1, hx2, -, -⟩ := C.piM_x hS
  have hro : orderOf (C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩) = 2 := orderOf_eq_prime
    (by rw [pow_two, ← map_mul]; exact (congrArg (C.piM hS) (Subtype.ext hr2)).trans (map_one _))
    hr1
  obtain ⟨⟨m, hm⟩, hmc⟩ := isConj_iff.mp ((C.isNaturalSE_Dv C.i).isConj (x := ⟨_, hx1⟩)
    (y := ⟨_, hrM⟩) (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk]))
  have hmc' : m * C.piM hS ⟨C.x, hxv⟩ * m⁻¹ = C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩ :=
    congrArg Subtype.val hmc
  obtain ⟨n, hn, hnm⟩ := hMc.exists_piM_eq m hm
  have hnY := hMc.le_centralizer hn
  have hZY : ∀ z ∈ C.Z, ∀ g ∈ Subgroup.centralizer (C.Y : Set G), z * g = g * z :=
    fun z hz g hg => Subgroup.mem_centralizer_iff.mp hg z (C.Z_le_Y hz)
  set c := zx * zr⁻¹ with hc
  have hcZ : c ∈ C.Z := mul_mem hzx (inv_mem hzr)
  set w := n * C.x * n⁻¹ * c with hw
  have hwY : w ∈ Subgroup.centralizer (C.Y : Set G) := mul_mem (mul_mem (mul_mem hnY
    (C.x_mem_centralizer_Y hS)) (inv_mem hnY)) (C.Z_le_centralizer_Y hS hcZ)
  have hwzr : w * zr ∈ Mc := by
    have h1 := hMc.conj_mem n hnY _ hxzx
    have h2 : n⁻¹ * zx = zx * n⁻¹ := (hZY zx hzx _ (inv_mem hnY)).symm
    rwa [show w * zr = n * C.x * (n⁻¹ * zx) by rw [hw, hc]; group, h2,
      show n * C.x * (zx * n⁻¹) = n * (C.x * zx) * n⁻¹ by group]
  have hrwY : r⁻¹ * w ∈ Subgroup.centralizer (C.Y : Set G) := mul_mem (inv_mem hrY) hwY
  have hrw : r⁻¹ * w ∈ Mc := by
    have h1 := mul_mem (inv_mem hrzr) hwzr
    have hq := hZY zr hzr _ hrwY
    rwa [show (r * zr)⁻¹ * (w * zr) = zr⁻¹ * (zr * (r⁻¹ * w)) by rw [hq]; group,
      inv_mul_cancel_left] at h1
  have hrwP : r⁻¹ * w ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    refine (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS
      ⟨r⁻¹ * w, C.centralizer_Y_le hS hrwY⟩).mp ?_)
    have hcv := C.centralizer_Y_le hS (C.Z_le_centralizer_Y hS hcZ)
    have hc1 : C.piM hS ⟨c, hcv⟩ = 1 := (C.piM_eq_one_iff hS _).mpr fun ω hω =>
      (mem_fixingSubgroup_iff G).mp (C.Z_le_fixingSubgroup hS hcZ) ω hω
    rw [show (⟨r⁻¹ * w, C.centralizer_Y_le hS hrwY⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        (⟨r, C.centralizer_Y_le hS hrY⟩)⁻¹ * (⟨n, C.centralizer_Y_le hS hnY⟩ * ⟨C.x, hxv⟩ *
          (⟨n, C.centralizer_Y_le hS hnY⟩)⁻¹ * ⟨c, hcv⟩) from rfl,
      map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hnm, hc1, mul_one, hmc',
      inv_mul_cancel]
  have hQ := hMc.mem_fixCore _ hrw hrwP
  have hQ' : w * r⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
    have h1 := conj_mem_fixCore (smul_fixSet_eq_of_mem_centralizer
      (C.centralizer_Y_le hS hrY)) hQ
    rwa [show r * (r⁻¹ * w) * r⁻¹ = w * r⁻¹ by group] at h1
  have hww : w * w = 1 := by
    have h1 : c * (n * C.x * n⁻¹) = n * C.x * n⁻¹ * c := hZY c hcZ _ (mul_mem (mul_mem hnY
      (C.x_mem_centralizer_Y hS)) (inv_mem hnY))
    calc w * w = n * C.x * n⁻¹ * (c * (n * C.x * n⁻¹)) * c := by rw [hw]; group
      _ = n * (C.x * C.x) * n⁻¹ * (c * c) := by rw [h1]; group
      _ = 1 := by rw [C.x_mul_self hS, C.mul_self_eq_one_of_mem_Z hS hcZ]; group
  obtain ⟨p, hp⟩ := exists_conj_eq_of_odd_mul_inv hr2 hww (odd_orderOf_of_mem_oddCoreOf hQ')
  refine ⟨p⁻¹ * n, ?_⟩
  have h1 : n * c = c * n := (hZY c hcZ n hnY).symm
  calc p⁻¹ * n * (C.x * c) * (p⁻¹ * n)⁻¹ = p⁻¹ * (n * C.x * (n⁻¹ * (n * c)) * n⁻¹) * p := by
        group
    _ = p⁻¹ * w * p := by rw [h1, hw]; group
    _ = r := by rw [← hp]; group

theorem IsSplitting.x_mem (hMc : C.IsSplitting hS Mc) : C.x ∈ Mc := by
  obtain ⟨zx, hzx, hxzx⟩ := hMc.exists_mul_mem C.x (C.x_mem_centralizer_Y hS) (C.piM_x hS).1
  by_contra hxM
  have hzx1 : zx ≠ 1 := fun h => hxM (by rwa [h, mul_one] at hxzx)
  obtain ⟨z', hz', hz'1, hz'x⟩ := C.exists_mem_Z_ne_one_ne hS zx
  obtain ⟨h, -, hhY, hhz⟩ := C.exists_conj_eq_of_mem_Z hS hzx hzx1 hz' hz'1
  set r := h * C.x * h⁻¹ with hr
  have hrY : r ∈ Subgroup.centralizer (C.Y : Set G) :=
    conj_mem_centralizer hhY (C.x_mem_centralizer_Y hS)
  have hrz : r * z' ∈ Mc := by
    have h1 := hMc.conj_mem_of_normalizes h hhY _ hxzx
    rwa [show h * (C.x * zx) * h⁻¹ = r * (h * zx * h⁻¹) by rw [hr]; group, hhz] at h1
  have hz'v := C.centralizer_Y_le hS (C.Z_le_centralizer_Y hS hz')
  have hz'1' : C.piM hS ⟨z', hz'v⟩ = 1 := (C.piM_eq_one_iff hS _).mpr fun ω hω =>
    (mem_fixingSubgroup_iff G).mp (C.Z_le_fixingSubgroup hS hz') ω hω
  have hrM : C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩ ∈ C.Dv.M C.i := by
    have h1 := hMc.piM_mem _ hrz
    rwa [show (⟨r * z', C.centralizer_Y_le hS (hMc.le_centralizer hrz)⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨r, C.centralizer_Y_le hS hrY⟩ * ⟨z', hz'v⟩ from rfl, map_mul, hz'1', mul_one] at h1
  have hhΦ := C.smul_fixSet_eq_of_normalizes_Y hS hhY
  have hr1 : C.piM hS ⟨r, C.centralizer_Y_le hS hrY⟩ ≠ 1 := by
    intro h1
    have h2 := (C.piM_eq_one_iff hS _).mp h1
    have hx1 : C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ = 1 := by
      refine (C.piM_eq_one_iff hS _).mpr fun ω hω => ?_
      have hhω : h • ω ∈ fixSet Ω (Subgroup.zpowers v) := by
        rw [← hhΦ]
        exact Set.smul_mem_smul_set hω
      have h3 := h2 _ hhω
      change (h * C.x * h⁻¹) • (h • ω) = h • ω at h3
      rw [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff] at h3
      exact h3
    have h4 := (C.piM_x hS).2.1
    rw [hx1, orderOf_one] at h4
    omega
  have hr2 : r * r = 1 := by
    rw [hr, show h * C.x * h⁻¹ * (h * C.x * h⁻¹) = h * (C.x * C.x) * h⁻¹ by group,
      C.x_mul_self hS, mul_one, mul_inv_cancel]
  obtain ⟨g, hg⟩ := hMc.exists_conj hzx hxzx hrY hr2 hrM hr1 hz' hrz
  have hc1 : zx * z'⁻¹ ≠ 1 := fun h1 => hz'x (mul_inv_eq_one.mp h1).symm
  have hJ := (C.mul_mem_longInvAt hS (mul_mem hzx (inv_mem hz')) hc1).1
  have hrJ : r ∈ longInv G Ω := hg ▸ (conj_mem_longInv_iff g).mpr hJ
  exact C.x_not_mem_longInv hS ((conj_mem_longInv_iff h).mp hrJ)

theorem IsSplitting.piM_mem_stabilizer (hMc : C.IsSplitting hS Mc) {k : G}
    (hk : k ∈ Mc ⊓ stabilizer G (C.γ : Ω)) :
    C.piM hS ⟨k, C.centralizer_Y_le hS (hMc.le_centralizer (Subgroup.mem_inf.mp hk).1)⟩ ∈
      C.Dv.M C.i ⊓ stabilizer (Equiv.Perm (C.Dv.Ψc C.i)) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) :=
  Subgroup.mem_inf.mpr ⟨hMc.piM_mem _ (Subgroup.mem_inf.mp hk).1,
    (C.smul_eq_iff_piM_apply_eq hS _ ⟨C.γ, C.γ_mem⟩).mp (Subgroup.mem_inf.mp hk).2⟩

theorem IsSplitting.exists_piM_eq_stabilizer (hMc : C.IsSplitting hS Mc)
    {m : Equiv.Perm (C.Dv.Ψc C.i)} (hm : m ∈ C.Dv.M C.i)
    (hmγ : m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) :
    ∃ g, ∃ hg : g ∈ Mc, g ∈ stabilizer G (C.γ : Ω) ∧
      C.piM hS ⟨g, C.centralizer_Y_le hS (hMc.le_centralizer hg)⟩ = m := by
  obtain ⟨g, hg, rfl⟩ := hMc.exists_piM_eq m hm
  exact ⟨g, hg, (C.smul_eq_iff_piM_apply_eq hS _ ⟨C.γ, C.γ_mem⟩).mpr hmγ, rfl⟩

theorem IsSplitting.eq_one_of_piM_eq_one (hMc : C.IsSplitting hS Mc) {U : Subgroup G}
    (hU : fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω))) {u : G} (hu : u ∈ U)
    (h1 : C.piM hS ⟨u, C.centralizer_Y_le hS (hMc.le_centralizer
      (Subgroup.mem_inf.mp (hU.1 hu)).1)⟩ = 1) : u = 1 := by
  have huP : u ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)
  have huQ := hMc.mem_fixCore u (Subgroup.mem_inf.mp (hU.1 hu)).1 huP
  obtain ⟨k, hk⟩ := hU.2.1 ⟨u, hu⟩
  exact eq_one_of_mem_oddCoreOf huQ (k := k) (by simpa using congrArg Subtype.val hk)

theorem IsSplitting.piM_mem_seRadical (hMc : C.IsSplitting hS Mc) {U : Subgroup G}
    (hU : fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω))) {u : G} (hu : u ∈ U) :
    C.piM hS ⟨u, C.centralizer_Y_le hS (hMc.le_centralizer (Subgroup.mem_inf.mp (hU.1 hu)).1)⟩ ∈
      seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) := by
  have h1 := Subgroup.mem_inf.mp (hMc.piM_mem_stabilizer (hU.1 hu))
  obtain ⟨k, hk⟩ := hU.2.1 ⟨u, hu⟩
  refine mem_seRadical_of_pow_eq_one h1.1 h1.2 (k := k) ?_
  rw [← map_pow]
  exact (congrArg (C.piM hS) (Subtype.ext (by simpa using congrArg Subtype.val hk))).trans
    (map_one _)

theorem IsSplitting.exists_mem_U_piM_eq (hMc : C.IsSplitting hS Mc) {U : Subgroup G}
    (hU : fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω))) {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) :
    ∃ u, ∃ hu : u ∈ U, C.piM hS ⟨u, C.centralizer_Y_le hS (hMc.le_centralizer
      (Subgroup.mem_inf.mp (hU.1 hu)).1)⟩ = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Mc ⊓ stabilizer G (C.γ : Ω) with hK
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i with hγi
  set Mγ : Subgroup (Equiv.Perm (C.Dv.Ψc C.i)) :=
    C.Dv.M C.i ⊓ stabilizer (Equiv.Perm (C.Dv.Ψc C.i)) γi with hMγ
  have hKv : K ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    fun k hk => C.centralizer_Y_le hS (hMc.le_centralizer (Subgroup.mem_inf.mp hk).1)
  set f : K →* Mγ := ((C.piM hS).comp (Subgroup.inclusion hKv)).codRestrict Mγ
    (fun k => hMc.piM_mem_stabilizer k.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨m', hm'⟩
    obtain ⟨g, hg, hgγ, hgm⟩ := hMc.exists_piM_eq_stabilizer (Subgroup.mem_inf.mp hm').1
      (Subgroup.mem_inf.mp hm').2
    exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hg, hgγ⟩⟩, Subtype.ext hgm⟩
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hU
  set S' : Sylow 2 Mγ := T.mapSurjective hfs with hS'
  have hR : IsPGroup 2 ((seRadical (C.Dv.M C.i) γi).subgroupOf Mγ) :=
    ((C.isNaturalSE_Dv C.i).isPGroup_seRadical γi).comap_of_injective _ Mγ.subtype_injective
  have hle : (S' : Subgroup Mγ) ≤ (seRadical (C.Dv.M C.i) γi).subgroupOf Mγ := by
    rw [hS', Sylow.coe_mapSurjective]
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have htU : (t : G) ∈ U := hT ▸ ⟨t, ht, rfl⟩
    exact hMc.piM_mem_seRadical hU htU
  have heq := S'.is_maximal' hR hle
  have hmγ : m ∈ Mγ := Subgroup.mem_inf.mpr ⟨seRadical_le hm, apply_eq_of_mem_seRadical hm⟩
  have h1 : (⟨m, hmγ⟩ : Mγ) ∈ (S' : Subgroup Mγ) := by
    rw [← heq]
    exact Subgroup.mem_subgroupOf.mpr hm
  rw [hS', Sylow.coe_mapSurjective] at h1
  obtain ⟨t, ht, htm⟩ := h1
  exact ⟨t, hT ▸ ⟨t, ht, rfl⟩, congrArg Subtype.val htm⟩

theorem IsSplitting.exists_normalizer_piM_eq (hMc : C.IsSplitting hS Mc) {U : Subgroup G}
    (hU : fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω))) {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ C.Dv.M C.i)
    (hmγ : m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) :
    ∃ h, ∃ hh : h ∈ Mc, h ∈ stabilizer G (C.γ : Ω) ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
      C.piM hS ⟨h, C.centralizer_Y_le hS (hMc.le_centralizer hh)⟩ = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Mc ⊓ stabilizer G (C.γ : Ω) with hK
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i with hγi
  have hKv : ∀ k ∈ K, k ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    fun k hk => C.centralizer_Y_le hS (hMc.le_centralizer (Subgroup.mem_inf.mp hk).1)
  set W : Subgroup G := K ⊓ ((seRadical (C.Dv.M C.i) γi).comap (C.piM hS)).map
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subtype with hW
  have hmemW : ∀ k (hk : k ∈ K), C.piM hS ⟨k, hKv k hk⟩ ∈ seRadical (C.Dv.M C.i) γi →
      k ∈ W := fun k hk h1 => Subgroup.mem_inf.mpr ⟨hk, ⟨⟨k, hKv k hk⟩, h1, rfl⟩⟩
  have hWK : W ≤ K := inf_le_left
  have hUW : U ≤ W := fun u hu => hmemW u (hU.1 hu) (hMc.piM_mem_seRadical hU hu)
  have hsyl : ∀ U' : Subgroup G, fusionIsSylowIn 2 U' K → U' ≤ W → fusionIsSylowIn 2 U' W :=
    fun U' hU' hU'W => ⟨hU'W, hU'.2.1, fun P hPW hP hle => hU'.2.2 P (hPW.trans hWK) hP hle⟩
  obtain ⟨g, hg, hgγ, hgm⟩ := hMc.exists_piM_eq_stabilizer hm hmγ
  have hgK : g ∈ K := Subgroup.mem_inf.mpr ⟨hg, hgγ⟩
  set U' := U.map (MulAut.conj g).toMonoidHom with hU'
  have hU'K : fusionIsSylowIn 2 U' K := by
    refine fusionIsSylowIn_of_card_eq ?_ (hU.2.1.map _) ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact mul_mem (mul_mem hgK (hU.1 hu)) (inv_mem hgK)
    · rw [hU', Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact card_eq_of_fusionIsSylowIn hU
  have hU'W : U' ≤ W := by
    rintro _ ⟨u, hu, rfl⟩
    have hgu : g * u * g⁻¹ ∈ K := mul_mem (mul_mem hgK (hU.1 hu)) (inv_mem hgK)
    suffices h2 : C.piM hS ⟨g * u * g⁻¹, hKv _ hgu⟩ ∈ seRadical (C.Dv.M C.i) γi from
      hmemW _ hgu h2
    rw [show (⟨g * u * g⁻¹, hKv _ hgu⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨g, hKv g hgK⟩ * ⟨u, hKv u (hU.1 hu)⟩ * (⟨g, hKv g hgK⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv, hgm]
    exact conj_mem_seRadical (Subgroup.le_normalizer hm) hmγ (hMc.piM_mem_seRadical hU hu)
  obtain ⟨w, hwW, hwU⟩ := exists_mem_conj_of_fusionIsSylowIn (hsyl U hU hUW) (hsyl U' hU'K hU'W)
  have hwK := hWK hwW
  have hwR : C.piM hS ⟨w, hKv w hwK⟩ ∈ seRadical (C.Dv.M C.i) γi := by
    obtain ⟨-, ⟨w', hw', hww'⟩⟩ := Subgroup.mem_inf.mp hwW
    have : w' = ⟨w, hKv w hwK⟩ := Subtype.ext hww'
    rw [← this]
    exact hw'
  obtain ⟨u₀, hu₀, hu₀w⟩ := hMc.exists_mem_U_piM_eq hU hwR
  have hu₀K := hU.1 hu₀
  refine ⟨u₀ * w⁻¹ * g, mul_mem (mul_mem (Subgroup.mem_inf.mp hu₀K).1
    (inv_mem (Subgroup.mem_inf.mp hwK).1)) hg, ?_, fun y hy => ?_, ?_⟩
  · exact (mul_mem (mul_mem hu₀K (inv_mem hwK)) hgK |> Subgroup.mem_inf.mp).2
  · have h1 : g * y * g⁻¹ ∈ U' := ⟨y, hy, rfl⟩
    have h2 := (hwU _).mp h1
    have h3 := mul_mem (mul_mem hu₀ h2) (inv_mem hu₀)
    rwa [show u₀ * (w⁻¹ * (g * y * g⁻¹) * w) * u₀⁻¹ = u₀ * w⁻¹ * g * y * (u₀ * w⁻¹ * g)⁻¹ by
      group] at h3
  · rw [show (⟨u₀ * w⁻¹ * g, C.centralizer_Y_le hS (hMc.le_centralizer (mul_mem (mul_mem
        (Subgroup.mem_inf.mp hu₀K).1 (inv_mem (Subgroup.mem_inf.mp hwK).1)) hg))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨u₀, hKv u₀ hu₀K⟩ * (⟨w, hKv w hwK⟩)⁻¹ * ⟨g, hKv g hgK⟩ from rfl,
      map_mul, map_mul, map_inv, hu₀w, mul_inv_cancel, one_mul, hgm]

theorem IsSplitting.exists_conj_x_eq (hMc : C.IsSplitting hS Mc) (hxM : C.x ∈ Mc) {c q : G}
    (hc : c ∈ Mc) (hq : q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))))
    (hcq : orderOf (c * q) = 2) : ∃ h : G, h * C.x * h⁻¹ = c * q := by
  have hcY := hMc.le_centralizer hc
  have hcv := C.centralizer_Y_le hS hcY
  have hcΦ := smul_fixSet_eq_of_mem_centralizer (Ω := Ω) hcv
  have hcΦ' := smul_fixSet_eq_of_mem_centralizer (Ω := Ω) (inv_mem hcv)
  have hqP : q ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := Subgroup.map_subtype_le _ hq
  have hcq2 : c * q * (c * q) = 1 := by rw [← pow_two, ← hcq, pow_orderOf_eq_one]
  have hxv := C.x_mem_centralizer hS
  obtain ⟨hx1, hx2, -, -⟩ := C.piM_x hS
  have hc2 : C.piM hS ⟨c, hcv⟩ * C.piM hS ⟨c, hcv⟩ = 1 := by
    rw [← map_mul, C.piM_eq_one_iff]
    intro ω hω
    have h1 : c * c = (c⁻¹ * q * c⁻¹⁻¹ * q)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc c * c * (c⁻¹ * q * c⁻¹⁻¹ * q) = c * q * (c * q) := by group
        _ = 1 := hcq2
    have h2 : c⁻¹ * q * c⁻¹⁻¹ * q ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
      mul_mem (Subgroup.map_subtype_le _ (conj_mem_fixCore hcΦ' hq)) hqP
    change (c * c) • ω = ω
    rw [h1]
    exact (mem_fixingSubgroup_iff G).mp (inv_mem h2) ω hω
  have hc1 : C.piM hS ⟨c, hcv⟩ ≠ 1 := by
    intro h1
    have hcQ := hMc.mem_fixCore c hc ((mem_fixingSubgroup_iff G).mpr
      ((C.piM_eq_one_iff hS _).mp h1))
    have := odd_orderOf_of_mem_oddCoreOf (mul_mem hcQ hq)
    rw [hcq] at this
    exact Nat.not_odd_iff_even.mpr even_two this
  have hco : orderOf (C.piM hS ⟨c, hcv⟩) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  obtain ⟨⟨m, hm⟩, hmc⟩ := isConj_iff.mp ((C.isNaturalSE_Dv C.i).isConj (x := ⟨_, hx1⟩)
    (y := ⟨_, hMc.piM_mem c hc⟩) (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk]))
  have hmc' : m * C.piM hS ⟨C.x, hxv⟩ * m⁻¹ = C.piM hS ⟨c, hcv⟩ := congrArg Subtype.val hmc
  obtain ⟨n, hn, hnm⟩ := hMc.exists_piM_eq m hm
  have hnv := C.centralizer_Y_le hS (hMc.le_centralizer hn)
  set w := n * C.x * n⁻¹ with hw
  have hwM : w ∈ Mc := hMc.conj_mem n (hMc.le_centralizer hn) _ hxM
  have hcw : c⁻¹ * w ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
    refine hMc.mem_fixCore _ (mul_mem (inv_mem hc) hwM) ((mem_fixingSubgroup_iff G).mpr
      ((C.piM_eq_one_iff hS ⟨c⁻¹ * w, mul_mem (inv_mem hcv) (mul_mem (mul_mem hnv hxv)
        (inv_mem hnv))⟩).mp ?_))
    rw [show (⟨c⁻¹ * w, mul_mem (inv_mem hcv) (mul_mem (mul_mem hnv hxv) (inv_mem hnv))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        (⟨c, hcv⟩)⁻¹ * (⟨n, hnv⟩ * ⟨C.x, hxv⟩ * (⟨n, hnv⟩)⁻¹) from rfl,
      map_mul, map_mul, map_mul, map_inv, map_inv, hnm, hmc', inv_mul_cancel]
  have hww : w * w = 1 := by
    rw [hw, show n * C.x * n⁻¹ * (n * C.x * n⁻¹) = n * (C.x * C.x) * n⁻¹ by group,
      C.x_mul_self hS, mul_one, mul_inv_cancel]
  have hodd : Odd (orderOf (w * (c * q)⁻¹)) := by
    have h1 : (c * q) * ((c * q)⁻¹ * w) * (c * q)⁻¹ ∈
        oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
      have h2 : (c * q)⁻¹ * w = q⁻¹ * (c⁻¹ * w) := by group
      rw [h2, show c * q * (q⁻¹ * (c⁻¹ * w)) * (c * q)⁻¹ = c * (c⁻¹ * w * q⁻¹) * c⁻¹ by group]
      exact conj_mem_fixCore hcΦ (mul_mem hcw (inv_mem hq))
    rw [show (c * q) * ((c * q)⁻¹ * w) * (c * q)⁻¹ = w * (c * q)⁻¹ by group] at h1
    exact odd_orderOf_of_mem_oddCoreOf h1
  obtain ⟨p, hp⟩ := exists_conj_eq_of_odd_mul_inv hcq2 hww hodd
  refine ⟨p⁻¹ * n, ?_⟩
  calc p⁻¹ * n * C.x * (p⁻¹ * n)⁻¹ = p⁻¹ * w * p := by rw [hw]; group
    _ = c * q := by rw [← hp]; group

end F6

section F6Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem x_mem_of_splitting (hS : Sec4Setting G Ω) (Mc : Subgroup G)
    (hMcY : Mc ≤ Subgroup.centralizer (C.Y : Set G))
    (hQ : Subgroup.centralizer (C.Y : Set G) ⊓
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc)
    (hM : ∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ ∈ C.Dv.M C.i)
    (hMonto : ∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
      C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ = m)
    (hP : ∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
      g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))))
    (hL : ∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
      C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc)
    (hnorm : ∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc)
    (hNY : ∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) → ∀ c ∈ Mc, h * c * h⁻¹ ∈ Mc) :
    C.x ∈ Mc ∧
    ∃ U V : Subgroup G, ∃ hUMc : U ≤ Mc,
      V ≤ U ∧ U ≤ stabilizer G (C.γ : Ω) ∧
      fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω)) ∧ C.x ∈ V ∧
      (∀ u ∈ U, u ∈ V ↔ u * u = 1) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = 1 → u = 1) ∧
      (∀ m ∈ seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i), ∃ u, ∃ hu : u ∈ U,
        C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = m) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ ∈
        seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) ∧
      (∀ m ∈ C.Dv.M C.i, m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i →
        ∃ h, ∃ hh : h ∈ Mc, h ∈ stabilizer G (C.γ : Ω) ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
          C.piM hS ⟨h, C.centralizer_Y_le hS (hMcY hh)⟩ = m) ∧
      (∀ r ∈ V, r ≠ 1 → ∃ h ∈ Mc ⊓ stabilizer G (C.γ : Ω), h * C.x * h⁻¹ = r) ∧
      (∀ r ∈ V, ∀ z ∈ C.Z, r ≠ 1 → z ≠ 1 → r * z ∈ longInv G Ω) ∧
      (∀ c ∈ Mc, ∀ q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))),
        orderOf (c * q) = 2 → ∃ h : G, h * C.x * h⁻¹ = c * q) := by
  have hMc : C.IsSplitting hS Mc := ⟨hMcY, hQ, hM, hMonto, hP, hL, hnorm, hNY⟩
  have hxM := hMc.x_mem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxK : C.x ∈ Mc ⊓ stabilizer G (C.γ : Ω) :=
    Subgroup.mem_inf.mpr ⟨hxM, (C.x_smul hS).2.2⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers C.x) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, pow_two]; exact C.x_mul_self hS)
  obtain ⟨U, hxU, hU⟩ := exists_fusionIsSylowIn_ge hx2 (Subgroup.zpowers_le.mpr hxK)
  have hxU' : C.x ∈ U := hxU (Subgroup.mem_zpowers _)
  have hUK := hU.1
  have hUMc : U ≤ Mc := fun u hu => (Subgroup.mem_inf.mp (hUK hu)).1
  have hUv : ∀ u ∈ U, u ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    fun u hu => C.centralizer_Y_le hS (hMcY (hUMc hu))
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i with hγi
  set V : Subgroup G := U ⊓ ((rootCenter (seRadical (C.Dv.M C.i) γi)).comap (C.piM hS)).map
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subtype with hV
  have hmemV : ∀ u (hu : u ∈ U),
      u ∈ V ↔ C.piM hS ⟨u, hUv u hu⟩ ∈ rootCenter (seRadical (C.Dv.M C.i) γi) := by
    intro u hu
    constructor
    · rintro ⟨-, ⟨u', hu', hu'u⟩⟩
      rwa [show u' = ⟨u, hUv u hu⟩ from Subtype.ext hu'u] at hu'
    · exact fun h => Subgroup.mem_inf.mpr ⟨hu, ⟨⟨u, hUv u hu⟩, h, rfl⟩⟩
  have hV2 : ∀ u ∈ U, u ∈ V ↔ u * u = 1 := by
    intro u hu
    rw [hmemV u hu]
    constructor
    · intro h
      have h1 := (C.isNaturalSE_Dv C.i).mul_self_eq_one_of_mem_rootCenter h
      rw [← map_mul] at h1
      exact hMc.eq_one_of_piM_eq_one hU (mul_mem hu hu) h1
    · intro h
      have h1 := Subgroup.mem_inf.mp (hMc.piM_mem_stabilizer (hUK hu))
      refine (C.isNaturalSE_Dv C.i).mem_rootCenter_seRadical h1.1 h1.2 ?_
      rw [← map_mul]
      exact (congrArg (C.piM hS) (Subtype.ext h)).trans (map_one _)
  have hxV : C.x ∈ V := (hV2 _ hxU').mpr (C.x_mul_self hS)
  have hinj : ∀ u (hu : u ∈ U), C.piM hS ⟨u, hUv u hu⟩ = 1 → u = 1 :=
    fun u hu h1 => hMc.eq_one_of_piM_eq_one hU hu h1
  refine ⟨hxM, U, V, hUMc, inf_le_left, fun u hu => (Subgroup.mem_inf.mp (hUK hu)).2, hU, hxV,
    hV2, hinj, fun m hm => hMc.exists_mem_U_piM_eq hU hm,
    fun u hu => hMc.piM_mem_seRadical hU hu,
    fun m hm hmγ => hMc.exists_normalizer_piM_eq hU hm hmγ, ?_, ?_,
    fun c hc q hq hcq => hMc.exists_conj_x_eq hxM hc hq hcq⟩
  ·
    intro r hr hr1
    have hrU : r ∈ U := (Subgroup.mem_inf.mp hr).1
    have hrR := (hmemV r hrU).mp hr
    have hxR := (hmemV _ hxU').mp hxV
    have hr1' : C.piM hS ⟨r, hUv r hrU⟩ ≠ 1 := fun h => hr1 (hinj r hrU h)
    have hx1' : C.piM hS ⟨C.x, hUv _ hxU'⟩ ≠ 1 := fun h => by
      have h4 := (C.piM_x hS).2.1
      rw [show (⟨C.x, C.x_mem_centralizer hS⟩ :
          Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          ⟨C.x, hUv _ hxU'⟩ from rfl, h, orderOf_one] at h4
      omega
    have : Nontrivial (C.Dv.Ψc C.i) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by have := C.Dv.five_le_card C.i; omega)
    obtain ⟨c, hc⟩ := exists_ne γi
    obtain ⟨d, hdM, hdγ, -, hdx⟩ := (C.isNaturalSE_Dv C.i).exists_conj_eq (Ne.symm hc) hxR hx1'
      hrR hr1'
    obtain ⟨h, hhMc, hhγ, hhU, hhd⟩ := hMc.exists_normalizer_piM_eq hU hdM hdγ
    refine ⟨h, Subgroup.mem_inf.mpr ⟨hhMc, hhγ⟩, ?_⟩
    have h1 : h * C.x * h⁻¹ ∈ U := hhU _ hxU'
    have h2 : h * C.x * h⁻¹ * r⁻¹ ∈ U := mul_mem h1 (inv_mem hrU)
    have hhv := C.centralizer_Y_le hS (hMcY hhMc)
    have h3 : C.piM hS ⟨h * C.x * h⁻¹ * r⁻¹, hUv _ h2⟩ = 1 := by
      rw [show (⟨h * C.x * h⁻¹ * r⁻¹, hUv _ h2⟩ :
          Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          ⟨h, hhv⟩ * ⟨C.x, hUv _ hxU'⟩ * (⟨h, hhv⟩)⁻¹ * (⟨r, hUv r hrU⟩)⁻¹ from rfl,
        map_mul, map_mul, map_mul, map_inv, map_inv, hhd, hdx, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj _ h2 h3)
  ·
    intro r hr z hz hr1 hz1
    have hrU : r ∈ U := (Subgroup.mem_inf.mp hr).1
    have hrY := hMcY (hUMc hrU)
    have hzY := C.Z_le_centralizer_Y hS hz
    have hrzY : r * z ∈ Subgroup.centralizer (C.Y : Set G) := mul_mem hrY hzY
    have hrz2 : r * z * (r * z) = 1 := by
      have h1 : z * r = r * z := Subgroup.mem_centralizer_iff.mp hrY z (C.Z_le_Y hz)
      calc r * z * (r * z) = r * (z * r) * z := by group
        _ = r * r * (z * z) := by rw [h1]; group
        _ = 1 := by rw [(hV2 r hrU).mp hr, C.mul_self_eq_one_of_mem_Z hS hz, one_mul]
    have hzv := C.centralizer_Y_le hS hzY
    have hz1' : C.piM hS ⟨z, hzv⟩ = 1 := (C.piM_eq_one_iff hS _).mpr fun ω hω =>
      (mem_fixingSubgroup_iff G).mp (C.Z_le_fixingSubgroup hS hz) ω hω
    have hpiM : C.piM hS ⟨r * z, C.centralizer_Y_le hS hrzY⟩ = C.piM hS ⟨r, hUv r hrU⟩ := by
      rw [show (⟨r * z, C.centralizer_Y_le hS hrzY⟩ :
          Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          ⟨r, hUv r hrU⟩ * ⟨z, hzv⟩ from rfl, map_mul, hz1', mul_one]
    have hrM : C.piM hS ⟨r * z, C.centralizer_Y_le hS hrzY⟩ ∈ C.Dv.M C.i := by
      rw [hpiM]
      exact hM r (hUMc hrU)
    have hr1' : C.piM hS ⟨r * z, C.centralizer_Y_le hS hrzY⟩ ≠ 1 := by
      rw [hpiM]
      exact fun h => hr1 (hinj r hrU h)
    have hxz : C.x * 1 ∈ Mc := by rwa [mul_one]
    have hrzz : r * z * z⁻¹ ∈ Mc := by rw [mul_inv_cancel_right]; exact hUMc hrU
    obtain ⟨g, hg⟩ := hMc.exists_conj (one_mem _) hxz hrzY hrz2 hrM hr1' (inv_mem hz) hrzz
    rw [inv_inv, one_mul] at hg
    exact hg ▸ (conj_mem_longInv_iff g).mpr (C.mul_mem_longInvAt hS hz hz1).1

theorem exists_splitting_x_mem (hS : Sec4Setting G Ω) (hcov : SETwoCoverConj) :
    ∃ Mc : Subgroup G, ∃ hMcY : Mc ≤ Subgroup.centralizer (C.Y : Set G),
      Subgroup.centralizer (C.Y : Set G) ⊓
          oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc ∧
      (∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ ∈ C.Dv.M C.i) ∧
      (∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
        C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ = m) ∧
      (∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
        g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) ∧
      (∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
        C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc) ∧
      (∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc) ∧
      (∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) → ∀ c ∈ Mc, h * c * h⁻¹ ∈ Mc) ∧
    C.x ∈ Mc ∧
    ∃ U V : Subgroup G, ∃ hUMc : U ≤ Mc,
      V ≤ U ∧ U ≤ stabilizer G (C.γ : Ω) ∧
      fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω)) ∧ C.x ∈ V ∧
      (∀ u ∈ U, u ∈ V ↔ u * u = 1) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = 1 → u = 1) ∧
      (∀ m ∈ seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i), ∃ u, ∃ hu : u ∈ U,
        C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = m) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ ∈
        seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) ∧
      (∀ m ∈ C.Dv.M C.i, m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i →
        ∃ h, ∃ hh : h ∈ Mc, h ∈ stabilizer G (C.γ : Ω) ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
          C.piM hS ⟨h, C.centralizer_Y_le hS (hMcY hh)⟩ = m) ∧
      (∀ r ∈ V, r ≠ 1 → ∃ h ∈ Mc ⊓ stabilizer G (C.γ : Ω), h * C.x * h⁻¹ = r) ∧
      (∀ r ∈ V, ∀ z ∈ C.Z, r ≠ 1 → z ≠ 1 → r * z ∈ longInv G Ω) ∧
      (∀ c ∈ Mc, ∀ q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))),
        orderOf (c * q) = 2 → ∃ h : G, h * C.x * h⁻¹ = c * q) := by
  obtain ⟨Mc, hMcY, h1, h2, h3, h4, h5, h6, h7⟩ := C.exists_splitting hS hcov
  exact ⟨Mc, hMcY, h1, h2, h3, h4, h5, h6, h7,
    C.x_mem_of_splitting hS Mc hMcY h1 h2 h3 h4 h5 h6 h7⟩

end F6Main

end FinConfig

section CoverSplit

@[expose] def SETwoMultiplierBound : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (Δ : Type) [Finite Δ] (π : E →* Equiv.Perm Δ),
    IsNaturalSE π.range → π.ker ≤ Subgroup.center E → (∀ z ∈ π.ker, z * z = 1) →
      commutator E = ⊤ → Nat.card π.ker ≤ 4 ∧ (Nat.card π.ker = 4 → Nat.card π.range = 29120)

@[expose] def SzEightTwoCoverConj : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (Δ : Type) [Finite Δ] (π : E →* Equiv.Perm Δ),
    IsNaturalSE π.range → Nat.card π.range = 29120 → π.ker ≤ Subgroup.center E →
      (∀ z ∈ π.ker, z * z = 1) → Nat.card π.ker = 4 → commutator E = ⊤ →
        ∀ a : E, a * a = 1 → a ∉ π.ker → ∀ z ∈ π.ker, ∃ g : E, g * a * g⁻¹ = a * z

theorem seTwoCoverConj_of (h1 : SETwoMultiplierBound) (h2 : SzEightTwoCoverConj) :
    SETwoCoverConj := by
  intro E _ _ Δ _ π hM hZ hsq h4 hperf a ha haK z hz
  obtain ⟨hle, h29⟩ := h1 E Δ π hM hZ hsq hperf
  have h4' : Nat.card π.ker = 4 := le_antisymm hle h4
  exact h2 E Δ π hM (h29 h4') hZ hsq h4' hperf a ha haK z hz

end CoverSplit

end CFSG.Holt.H78
