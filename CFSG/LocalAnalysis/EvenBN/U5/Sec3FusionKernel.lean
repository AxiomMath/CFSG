module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3Fusion

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Facts

variable {f : ℕ} {K : Type} [Field K]

@[expose] def InvolutionsConjIntoV (h : UnitaryFieldData 2 f K) : Prop :=
  2 ≤ f → center (hypPSU h 2 1) = ⊥ → ∀ z : hypPSU h 2 1, z * z = 1 →
    ∃ w : hypPSU h 2 1, w⁻¹ * z * w ∈ (Vsub h).map (hypProj h 2 1)

@[expose] def OuterInvolutionFusion (h : UnitaryFieldData 2 f K) : Prop :=
  2 ≤ f → center (hypPSU h 2 1) = ⊥ → ∀ α : MulAut (hypPSU h 2 1), α * α = 1 → α ∉ Pi h →
    ∃ D : Subgroup (hypPSU h 2 1), (∀ z ∈ D, α z = z) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, c ≠ 1 ∧ c * c = 1 ∧ ∃ w : hypPSU h 2 1,
        MulAut.conj w * α * (MulAut.conj w)⁻¹ = α * MulAut.conj c

@[expose] def PerfectLeInn (h : UnitaryFieldData 2 f K) : Prop :=
  2 ≤ f → center (hypPSU h 2 1) = ⊥ →
    ∀ D : Subgroup (MulAut (hypPSU h 2 1)), ⁅D, D⁆ = D → D ≤ Pi h

@[expose] def TwoCentralizerV (h : UnitaryFieldData 2 f K) : Prop :=
  2 ≤ f → center (hypPSU h 2 1) = ⊥ → ∀ α : MulAut (hypPSU h 2 1), (∃ k : ℕ, α ^ 2 ^ k = 1) →
    (∀ w ∈ Vh h, α * w = w * α) → α ∈ Sh h

end Facts

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem L_commute_centralizer (d : Data G h) :
    ∀ x ∈ d.L, ∀ y ∈ centralizer (d.L : Set G), x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.1 hy x hx

theorem act_of_mem (d : Data G h) {a : G} (ha : a ∈ d.L) :
    d.act ⟨a, le_normalizer ha⟩ = MulAut.conj (d.e ⟨a, ha⟩) := by
  refine MulEquiv.ext fun p => d.e.symm.injective (Subtype.ext ?_)
  rw [coe_e_symm_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

theorem act_apply_eq_iff (d : Data G h) (n : normalizer (d.L : Set G)) (a : d.L) :
    d.act n (d.e a) = d.e a ↔ (n : G) * a = a * n := by
  constructor
  · intro h1
    have h2 := d.coe_e_symm_act_apply n (d.e a)
    rw [h1, MulEquiv.symm_apply_apply] at h2
    calc (n : G) * a = n * a * (n : G)⁻¹ * n := by group
      _ = a * n := by rw [← h2]
  · intro h1
    apply d.e.symm.injective
    apply Subtype.ext
    rw [coe_e_symm_act_apply, MulEquiv.symm_apply_apply, h1]
    group

variable [Finite G]

theorem Hyp.exists_conj_mem_A₁ (hd : d.Hyp) (hI : InvolutionsConjIntoV h) {l : G}
    (hl : l ∈ d.L) (hl2 : l * l = 1) : ∃ m ∈ d.L, m⁻¹ * l * m ∈ d.A₁ := by
  have hz : d.e ⟨l, hl⟩ * d.e ⟨l, hl⟩ = 1 := by
    rw [← map_mul]
    have : (⟨l, hl⟩ : d.L) * ⟨l, hl⟩ = 1 := Subtype.ext hl2
    rw [this, map_one]
  obtain ⟨w, v, hv, hvw⟩ := hI hd.two_le hd.center_hypPSU _ hz
  refine ⟨(d.e.symm w : G), (d.e.symm w).2, v, hv, ?_⟩
  rw [η_apply, hvw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem Hyp.kernel_comm (hd : d.Hyp) :
    ∀ x ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G),
      ∀ y ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G), x * y = y * x := by
  have := hd.kernel.1
  intro x hx y hy
  have := (IsCyclic.commGroup (α := (centralizer (d.L : Set G) ⊓
    centralizer ({d.t} : Set G) : Subgroup G))).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem Hyp.perfect_le_L (hd : d.Hyp) (hP : PerfectLeInn h) {D : Subgroup G}
    (hDC : D ≤ centralizer ({d.t} : Set G)) (hD : ⁅D, D⁆ = D) : D ≤ d.L := by
  set N := normalizer (d.L : Set G)
  have hDN : D ≤ N := hDC.trans hd.centralizer_le_normalizer
  have hE : ⁅D.subgroupOf N, D.subgroupOf N⁆ = D.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hDN, hD]
  have hact : ⁅d.actImage D, d.actImage D⁆ = d.actImage D := by
    rw [actImage, ← Subgroup.map_commutator, hE]
  have hPi := hP hd.two_le hd.center_hypPSU _ hact
  set S := centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)
  have hDLS : D ≤ d.L ⊔ S := by
    intro x hx
    have hxP : d.act ⟨x, hDN hx⟩ ∈ Pi h := hPi ((d.mem_actImage).2 ⟨x, hx, hDN hx, rfl⟩)
    have hxLC := (d.act_mem_Pi_iff (hDN hx)).1 hxP
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute d.L_commute_centralizer hxLC
    have hcT : c ∈ centralizer ({d.t} : Set G) := by
      have h1 : l⁻¹ * (l * c) ∈ centralizer ({d.t} : Set G) :=
        mul_mem (inv_mem (hd.L_le_centralizer hl)) (hDC hx)
      rwa [inv_mul_cancel_left] at h1
    exact mul_mem_sup hl ⟨hc, hcT⟩
  have hcomm : ⁅d.L ⊔ S, d.L ⊔ S⁆ ≤ d.L := by
    have hLS : ∀ x ∈ d.L, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
      d.L_commute_centralizer x hx y hy.1
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨l, hl, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hLS hx
    obtain ⟨l', hl', s', hs', rfl⟩ := exists_mul_of_mem_sup_of_commute hLS hy
    have h1 : Commute s l' := (hLS l' hl' s hs).symm
    have h2 : Commute s' l := (hLS l hl s' hs').symm
    have h3 : Commute s s' := hd.kernel_comm s hs s' hs'
    have e1 : s * l' * s⁻¹ = l' := by rw [h1.eq, mul_inv_cancel_right]
    have e2 : s * s' * s⁻¹ = s' := by rw [h3.eq, mul_inv_cancel_right]
    have e3 : s' * l⁻¹ * s'⁻¹ = l⁻¹ := by rw [h2.inv_right.eq, mul_inv_cancel_right]
    have key : ⁅l * s, l' * s'⁆ = ⁅l, l'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc l * s * (l' * s') * (l * s)⁻¹ * (l' * s')⁻¹
          = l * (s * l' * s⁻¹) * (s * s' * s⁻¹) * l⁻¹ * s'⁻¹ * l'⁻¹ := by group
        _ = l * l' * s' * l⁻¹ * s'⁻¹ * l'⁻¹ := by rw [e1, e2]
        _ = l * l' * (s' * l⁻¹ * s'⁻¹) * l'⁻¹ := by group
        _ = l * l' * l⁻¹ * l'⁻¹ := by rw [e3]
    rw [key]
    have hc := Subgroup.commutator_mem_commutator hl hl'
    exact Subgroup.commutator_le_self _ hc
  calc D = ⁅D, D⁆ := hD.symm
    _ ≤ ⁅d.L ⊔ S, d.L ⊔ S⁆ := Subgroup.commutator_mono hDLS hDLS
    _ ≤ d.L := hcomm

theorem Hyp.exists_conj_mem_B₁_of_inner (hd : d.Hyp) (hI : InvolutionsConjIntoV h) {x : G}
    (hxC : x ∈ centralizer ({d.t} : Set G)) (hxLC : x ∈ d.L ⊔ centralizer (d.L : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ d.t) :
    ∃ m ∈ d.L, m⁻¹ * x * m ∈ d.B₁ ∧ m⁻¹ * x * m ≠ d.t := by
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute d.L_commute_centralizer hxLC
  have hlc : l * c = c * l := d.L_commute_centralizer l hl c hc
  have hcT : c ∈ centralizer ({d.t} : Set G) := by
    have h1 : l⁻¹ * (l * c) ∈ centralizer ({d.t} : Set G) :=
      mul_mem (inv_mem (hd.L_le_centralizer hl)) hxC
    rwa [inv_mul_cancel_left] at h1
  have hll : l * l = 1 ∧ c * c = 1 := by
    have hsq : (l * l) * (c * c) = 1 := by
      calc (l * l) * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hlc]
        _ = (l * c) * (l * c) := by group
        _ = 1 := hx2
    have hmem : l * l ∈ d.L ⊓ centralizer (d.L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨d.L.mul_mem hl hl, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact (centralizer (d.L : Set G)).inv_mem ((centralizer (d.L : Set G)).mul_mem hc hc)
    rw [hd.inf_centralizer_eq_bot, mem_bot] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem, one_mul] at hsq
    exact hsq
  have hct : c ∈ zpowers d.t := by
    by_cases h1 : c = 1
    · rw [h1]; exact one_mem _
    · rw [hd.kernel.2.2.1 c ⟨hc, hcT⟩ (orderOf_eq_prime (by rw [sq]; exact hll.2) h1)]
      exact mem_zpowers _
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [one_mul] at hx1 hxt
    rcases (mem_zpowers_iff.1 hct) with ⟨k, hk⟩
    have hk' : d.t ^ k = d.t ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hd.t_two]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · rw [← hk, hk', h0, zpow_zero] at hx1
      exact hx1 rfl
    · rw [← hk, hk', h0, zpow_one] at hxt
      exact hxt rfl
  obtain ⟨m, hm, hmA⟩ := hd.exists_conj_mem_A₁ hI hl hll.1
  have hcm : m⁻¹ * c * m = c := by
    rw [mul_assoc, ← (d.L_commute_centralizer m hm c hc), ← mul_assoc, inv_mul_cancel, one_mul]
  have heq : m⁻¹ * (l * c) * m = (m⁻¹ * l * m) * c := by
    rw [show m⁻¹ * (l * c) * m = (m⁻¹ * l * m) * (m⁻¹ * c * m) by group, hcm]
  refine ⟨m, hm, ?_, ?_⟩
  · rw [heq]
    exact mul_mem (mem_sup_right hmA) (mem_sup_left hct)
  · rw [heq]
    intro hEq
    have hmem : m⁻¹ * l * m ∈ d.L ⊓ centralizer (d.L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨d.L.mul_mem (d.L.mul_mem (d.L.inv_mem hm) hl) hm, ?_⟩
      rw [eq_mul_inv_of_mul_eq hEq]
      exact (centralizer (d.L : Set G)).mul_mem hd.t_mem
        ((centralizer (d.L : Set G)).inv_mem hc)
    rw [hd.inf_centralizer_eq_bot, mem_bot] at hmem
    apply hl1
    calc l = m * (m⁻¹ * l * m) * m⁻¹ := by group
      _ = 1 := by rw [hmem]; group

theorem Hyp.exists_conj_mul_of_outer (hd : d.Hyp) (hO : OuterInvolutionFusion h)
    (hP : PerfectLeInn h) {g : G} (hcomm : (g * d.t * g⁻¹) * d.t = d.t * (g * d.t * g⁻¹))
    (hout : g * d.t * g⁻¹ ∉ d.L ⊔ centralizer (d.L : Set G)) :
    ∃ y ∈ d.L, y ≠ 1 ∧ ∃ g' : G, g'⁻¹ * d.t * g' = d.t * y := by
  set x := g * d.t * g⁻¹ with hxdef
  have hxC : x ∈ centralizer ({d.t} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hxN : x ∈ normalizer (d.L : Set G) := hd.centralizer_le_normalizer hxC
  have hx2 : x * x = 1 := by
    rw [hxdef]
    calc g * d.t * g⁻¹ * (g * d.t * g⁻¹) = g * (d.t * d.t) * g⁻¹ := by group
      _ = 1 := by rw [hd.t_mul_t]; group
  set α := d.act ⟨x, hxN⟩ with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨x, hxN⟩ : normalizer (d.L : Set G)) * ⟨x, hxN⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hαP : α ∉ Pi h := fun hP' => hout ((d.act_mem_Pi_iff hxN).1 hP')
  obtain ⟨D, hDfix, hDperf, c, hcD, hc1, hc2, w, hw⟩ :=
    hO hd.two_le hd.center_hypPSU α hα2 hαP
  set φ : hypPSU h 2 1 →* G := d.L.subtype.comp d.e.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := d.L.subtype_injective.comp d.e.symm.injective
  set DG : Subgroup G := D.map φ with hDG
  have hDGx : ∀ z ∈ DG, z * x = x * z := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := (d.act_apply_eq_iff ⟨x, hxN⟩ (d.e.symm z)).1 (by
      rw [MulEquiv.apply_symm_apply]
      exact hDfix z hz)
    exact h1.symm
  have hDGperf : ⁅DG, DG⁆ = DG := by rw [hDG, ← Subgroup.map_commutator, hDperf]
  set DG' : Subgroup G := DG.map (MulAut.conj g⁻¹).toMonoidHom with hDG'
  have hDG'C : DG' ≤ centralizer ({d.t} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hz' := hDGx z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxt : d.t = g⁻¹ * x * g := by rw [hxdef]; group
    rw [hxt]
    calc g⁻¹ * z * g * (g⁻¹ * x * g) = g⁻¹ * (z * x) * g := by group
      _ = g⁻¹ * (x * z) * g := by rw [hz']
      _ = g⁻¹ * x * g * (g⁻¹ * z * g) := by group
  have hDG'perf : ⁅DG', DG'⁆ = DG' := by rw [hDG', ← Subgroup.map_commutator, hDGperf]
  have hDG'L := hd.perfect_le_L hP hDG'C hDG'perf
  set y₀ : G := φ c with hy₀
  set m : G := φ w with hm
  have hy₀L : y₀ ∈ d.L := (d.e.symm c).2
  have hmL : m ∈ d.L := (d.e.symm w).2
  have hy₀1 : y₀ ≠ 1 := fun h1 => hc1 (hφinj (by rw [← hy₀, h1, map_one]))
  have hxy : x * y₀ = m * x * m⁻¹ := by
    have hmxN : m * x * m⁻¹ ∈ normalizer (d.L : Set G) :=
      mul_mem (mul_mem (le_normalizer hmL) hxN) (inv_mem (le_normalizer hmL))
    have hxyN : x * y₀ ∈ normalizer (d.L : Set G) := mul_mem hxN (le_normalizer hy₀L)
    have h1 : d.act ⟨x * y₀, hxyN⟩ = d.act ⟨m * x * m⁻¹, hmxN⟩ := by
      have e1 : (⟨x * y₀, hxyN⟩ : normalizer (d.L : Set G)) =
          ⟨x, hxN⟩ * ⟨y₀, le_normalizer hy₀L⟩ := rfl
      have e2 : (⟨m * x * m⁻¹, hmxN⟩ : normalizer (d.L : Set G)) =
          ⟨m, le_normalizer hmL⟩ * ⟨x, hxN⟩ * (⟨m, le_normalizer hmL⟩)⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_mul, map_inv, d.act_of_mem hy₀L, d.act_of_mem hmL]
      have hc' : d.e ⟨y₀, hy₀L⟩ = c := by
        have : (⟨y₀, hy₀L⟩ : d.L) = d.e.symm c := rfl
        rw [this, MulEquiv.apply_symm_apply]
      have hw' : d.e ⟨m, hmL⟩ = w := by
        have : (⟨m, hmL⟩ : d.L) = d.e.symm w := rfl
        rw [this, MulEquiv.apply_symm_apply]
      rw [hc', hw', ← hα, hw]
    have h2 : (x * y₀)⁻¹ * (m * x * m⁻¹) ∈ centralizer (d.L : Set G) := by
      have h3 : d.act (⟨x * y₀, hxyN⟩⁻¹ * ⟨m * x * m⁻¹, hmxN⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact (d.act_eq_one_iff _).1 h3
    have h4 : (x * y₀)⁻¹ * (m * x * m⁻¹) ∈ d.L := by
      have hxm : x⁻¹ * m * x ∈ d.L := by
        have := (mem_normalizer_iff.1 (inv_mem hxN) m).1 hmL
        simpa using this
      have : (x * y₀)⁻¹ * (m * x * m⁻¹) = y₀⁻¹ * (x⁻¹ * m * x) * m⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hy₀L) hxm) (inv_mem hmL)
    have h5 : (x * y₀)⁻¹ * (m * x * m⁻¹) ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨h4, h2⟩
    rw [hd.inf_centralizer_eq_bot, mem_bot] at h5
    exact (inv_mul_eq_one.1 h5)
  have hyL : g⁻¹ * y₀ * g ∈ d.L := hDG'L ⟨y₀, ⟨c, hcD, rfl⟩, by simp⟩
  refine ⟨g⁻¹ * y₀ * g, hyL, fun h1 => hy₀1 ?_, g⁻¹ * m⁻¹ * g, ?_⟩
  · calc y₀ = g * (g⁻¹ * y₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have hxt : d.t = g⁻¹ * x * g := by rw [hxdef]; group
    calc (g⁻¹ * m⁻¹ * g)⁻¹ * d.t * (g⁻¹ * m⁻¹ * g) = g⁻¹ * (m * x * m⁻¹) * g := by
          rw [hxt]; group
      _ = g⁻¹ * (x * y₀) * g := by rw [hxy]
      _ = d.t * (g⁻¹ * y₀ * g) := by rw [hxt]; group

theorem Hyp.exists_conj_mem_B₁ (hd : d.Hyp) (hI : InvolutionsConjIntoV h)
    (hO : OuterInvolutionFusion h) (hP : PerfectLeInn h) :
    ∃ g : G, g⁻¹ * d.t * g ∈ d.B₁ ∧ g⁻¹ * d.t * g ≠ d.t := by
  have := hd.setting.std.simple
  obtain ⟨g, hcomm, hne⟩ := exists_conj_ne_commute hd.setting.std.nonab hd.t_ne_one hd.t_mul_t
  set x := g * d.t * g⁻¹ with hxdef
  have hxt : x = g⁻¹⁻¹ * d.t * g⁻¹ := by rw [hxdef, inv_inv]
  have key : ∀ g₀ : G, g₀⁻¹ * d.t * g₀ ∈ centralizer ({d.t} : Set G) →
      g₀⁻¹ * d.t * g₀ ∈ d.L ⊔ centralizer (d.L : Set G) → g₀⁻¹ * d.t * g₀ ≠ d.t →
      ∃ g : G, g⁻¹ * d.t * g ∈ d.B₁ ∧ g⁻¹ * d.t * g ≠ d.t := by
    intro g₀ hC hLC hne₀
    have h2 : g₀⁻¹ * d.t * g₀ * (g₀⁻¹ * d.t * g₀) = 1 := by
      calc g₀⁻¹ * d.t * g₀ * (g₀⁻¹ * d.t * g₀) = g₀⁻¹ * (d.t * d.t) * g₀ := by group
        _ = 1 := by rw [hd.t_mul_t]; group
    have h1 : g₀⁻¹ * d.t * g₀ ≠ 1 := fun h1 => hd.t_ne_one (by
      calc d.t = g₀ * (g₀⁻¹ * d.t * g₀) * g₀⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    obtain ⟨m, -, hmB, hmne⟩ := hd.exists_conj_mem_B₁_of_inner hI hC hLC h2 h1 hne₀
    refine ⟨g₀ * m, ?_, ?_⟩
    · rw [show (g₀ * m)⁻¹ * d.t * (g₀ * m) = m⁻¹ * (g₀⁻¹ * d.t * g₀) * m by group]
      exact hmB
    · rw [show (g₀ * m)⁻¹ * d.t * (g₀ * m) = m⁻¹ * (g₀⁻¹ * d.t * g₀) * m by group]
      exact hmne
  by_cases hin : x ∈ d.L ⊔ centralizer (d.L : Set G)
  · refine key g⁻¹ ?_ ?_ ?_
    · rw [← hxt]
      exact mem_centralizer_singleton_iff.2 hcomm
    · rwa [← hxt]
    · rwa [← hxt]
  · obtain ⟨y, hyL, hy1, g', hg'⟩ := hd.exists_conj_mul_of_outer hO hP hcomm hin
    refine key g' ?_ ?_ ?_
    · rw [hg']
      refine mem_centralizer_singleton_iff.2 ?_
      have hyt : y * d.t = d.t * y := d.L_commute_centralizer y hyL d.t hd.t_mem
      rw [mul_assoc, hyt]
    · rw [hg']
      exact mul_mem (mem_sup_right hd.t_mem) (mem_sup_left hyL)
    · rw [hg']
      intro h1
      apply hy1
      calc y = d.t⁻¹ * (d.t * y) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]

omit [Finite G] in
theorem A₁_commute_A₃ (d : Data G h) : ∀ a ∈ d.A₁, ∀ b ∈ d.A₃, a * b = b * a := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, (central_Ssub_iff (Vsub_le_Ssub hv)).2 hv s hs]

omit [Finite G] in
theorem mem_A₁_of_commute (d : Data G h) {y : G} (hy : y ∈ d.A₃)
    (hc : ∀ b ∈ d.A₃, b * y = y * b) : y ∈ d.A₁ := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨g, (central_Ssub_iff hg).1 fun s hs => ?_, rfl⟩
  apply d.η_injOn (mul_mem (Ssub_le_Usub hs) (Ssub_le_Usub hg))
    (mul_mem (Ssub_le_Usub hg) (Ssub_le_Usub hs))
  rw [map_mul, map_mul]
  exact hc _ ⟨s, hs, rfl⟩

theorem Hyp.kernel_le_T (hd : d.Hyp) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) ≤ d.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)
  have hSN : d.T ≤ normalizer (S : Set G) := by
    intro x hx
    have hn := hd.kernel.2.2.2
    rw [mem_normalizer_iff]
    intro y
    have hxC := hd.T_le_centralizer hx
    constructor
    · intro hy
      have h1 := hn.conj_mem ⟨y, hy.2⟩ hy ⟨x, hxC⟩
      exact h1
    · intro hy
      have h1 := hn.conj_mem ⟨x * y * x⁻¹, hy.2⟩ hy ⟨x, hxC⟩⁻¹
      have : (x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ : G) = y := by group
      have h2 : ((⟨x, hxC⟩⁻¹ * ⟨x * y * x⁻¹, hy.2⟩ * (⟨x, hxC⟩⁻¹)⁻¹ :
          centralizer ({d.t} : Set G)) : G) = y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact this
      have h3 : y ∈ S := by
        rw [← h2]
        exact h1
      exact h3
  have h2 : IsPGroup 2 (d.T ⊔ S : Subgroup G) :=
    hd.isPGroup_T.to_sup_of_normal_right' hd.kernel.2.1 hSN
  have hle : d.T ⊔ S ≤ centralizer ({d.t} : Set G) := sup_le hd.T_le_centralizer inf_le_right
  rw [← hd.T_syl.eq_of_le le_sup_left hle h2]
  exact le_sup_right

theorem Hyp.A₃_le_R (hd : d.Hyp) : d.A₃ ≤ d.T ⊓ centralizer (d.B₁ : Set G) := by
  intro y hy
  refine Subgroup.mem_inf.2 ⟨hd.P_le (d.A₃_le_P hy), ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hle : d.B₁ ≤ centralizer ({y} : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2
        (d.L_commute_centralizer y (d.A₃_le_P.trans d.P_le_L hy) d.t hd.t_mem).symm
    · intro a ha
      exact mem_centralizer_singleton_iff.2 (d.A₁_commute_A₃ a ha y hy)
  exact mem_centralizer_singleton_iff.1 (hle hb)

theorem Hyp.kernel_le_R (hd : d.Hyp) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      d.T ⊓ centralizer (d.B₁ : Set G) := by
  intro c hc
  refine Subgroup.mem_inf.2 ⟨hd.kernel_le_T hc, ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hle : d.B₁ ≤ centralizer ({c} : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hc.2).symm
    · intro a ha
      exact mem_centralizer_singleton_iff.2
        (d.L_commute_centralizer a (d.A₁_le_P.trans d.P_le_L ha) c hc.1)
  exact mem_centralizer_singleton_iff.1 (hle hb)

theorem Hyp.B₁_le_R (hd : d.Hyp) : d.B₁ ≤ d.T ⊓ centralizer (d.B₁ : Set G) := by
  have := hd.isElementaryAbelian_B₁
  refine le_inf hd.B₁_le_T ?_
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val ((this.toIsMulCommutative.is_comm).comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem Hyp.weakly_closed_R (hd : d.Hyp) (c : G)
    (hc : ∀ r ∈ d.T ⊓ centralizer (d.B₁ : Set G), c⁻¹ * r * c ∈ d.T) :
    ∀ r ∈ d.T ⊓ centralizer (d.B₁ : Set G), c⁻¹ * r * c ∈ d.T ⊓ centralizer (d.B₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := d.B₁.map (MulAut.conj c⁻¹).toMonoidHom with hX
  have hXT : X ≤ d.T := by
    rintro _ ⟨b, hb, rfl⟩
    have := hc b (hd.B₁_le_R hb)
    simpa [MulAut.conj_apply] using this
  have := hd.isElementaryAbelian_B₁
  have hXe : CFSG.IsElementaryAbelian 2 X := CFSG.IsElementaryAbelian.map _
  have hXc : Nat.card X = 2 * (2 ^ f) ^ 4 := by
    rw [hX, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hd.card_B₁]
  have hXB := (hd.card_le_of_le_T hXT hXe).2 hXc
  intro r hr
  refine Subgroup.mem_inf.2 ⟨hc r hr, ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  rw [← hXB] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hrb : b' * r = r * b' := mem_centralizer_iff.1 hr.2 b' hb'
  calc c⁻¹ * b' * c * (c⁻¹ * r * c) = c⁻¹ * (b' * r) * c := by group
    _ = c⁻¹ * (r * b') * c := by rw [hrb]
    _ = c⁻¹ * r * c * (c⁻¹ * b' * c) := by group

theorem Hyp.R_le (hd : d.Hyp) (hC : TwoCentralizerV h) :
    d.T ⊓ centralizer (d.B₁ : Set G) ≤
      d.A₃ ⊔ (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)) := by
  intro r hr
  have hrN : r ∈ normalizer (d.L : Set G) := hd.T_le_normalizer hr.1
  have h2 : ∃ k : ℕ, d.act ⟨r, hrN⟩ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hd.isPGroup_T ⟨r, hr.1⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨r, hrN⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hcomm : ∀ w ∈ Vh h, d.act ⟨r, hrN⟩ * w = w * d.act ⟨r, hrN⟩ := by
    intro w hw
    rw [← d.actImage_A₁, mem_actImage] at hw
    obtain ⟨a, haA, haN, rfl⟩ := hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 hr.2 a (mem_sup_right haA)).symm
  have hS := hC hd.two_le hd.center_hypPSU _ h2 hcomm
  rw [← d.actImage_A₃, mem_actImage] at hS
  obtain ⟨y, hyA, hyN, hy⟩ := hS
  have hyr : y⁻¹ * r ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨y⁻¹ * r, mul_mem (inv_mem hyN) hrN⟩).1 ?_
    have : (⟨y⁻¹ * r, mul_mem (inv_mem hyN) hrN⟩ : normalizer (d.L : Set G)) =
        (⟨y, hyN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨r, hrN⟩ := rfl
    rw [this, map_mul, map_inv, hy, inv_mul_cancel]
  have hyrt : y⁻¹ * r ∈ centralizer ({d.t} : Set G) :=
    mul_mem (inv_mem (hd.L_le_centralizer (d.A₃_le_P.trans d.P_le_L hyA)))
      (hd.T_le_centralizer hr.1)
  rw [show r = y * (y⁻¹ * r) by group]
  exact mul_mem_sup hyA ⟨hyr, hyrt⟩

theorem Hyp.center_R_le (hd : d.Hyp) (hC : TwoCentralizerV h) {z : G}
    (hz : z ∈ d.T ⊓ centralizer (d.B₁ : Set G))
    (hzc : ∀ r ∈ d.T ⊓ centralizer (d.B₁ : Set G), r * z = z * r) :
    z ∈ d.A₁ ⊔ (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)) := by
  have hLS : ∀ x ∈ d.A₃, ∀ y ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G),
      x * y = y * x := fun x hx y hy =>
    d.L_commute_centralizer x (d.A₃_le_P.trans d.P_le_L hx) y hy.1
  obtain ⟨y, hy, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hLS (hd.R_le hC hz)
  refine mul_mem_sup (d.mem_A₁_of_commute hy fun b hb => ?_) hs
  have h1 := hzc b (hd.A₃_le_R hb)
  have h2 : b * s = s * b := hLS b hb s hs
  have h3 : b * y * s = y * b * s := by
    calc b * y * s = b * (y * s) := by group
      _ = y * s * b := h1
      _ = y * (s * b) := by group
      _ = y * (b * s) := by rw [h2]
      _ = y * b * s := by group
  exact mul_right_cancel h3

theorem Hyp.sec3_1_two (hd : d.Hyp) (hI : InvolutionsConjIntoV h)
    (hO : OuterInvolutionFusion h) (hP : PerfectLeInn h) (hC : TwoCentralizerV h) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) with hSdef
  set R := d.T ⊓ centralizer (d.B₁ : Set G) with hRdef
  have htS : zpowers d.t ≤ S := by
    rw [zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hd.t_mem, mem_centralizer_singleton_iff.2 rfl⟩
  by_contra hne
  obtain ⟨hcyc, h2S, huniq, -⟩ := hd.kernel
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2S
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    apply hne
    symm
    apply Subgroup.eq_of_le_of_card_ge htS
    rw [hn, hd.card_zpowers_t]
    interval_cases n <;> norm_num
  set k := 2 ^ (n - 1) with hk
  have hk2 : Nat.card S = 2 * k := by
    rw [hn, hk, ← pow_succ']
    congr 1
    omega
  have hkeven : Even k := by
    rw [hk]
    exact (Nat.even_pow' (by omega)).2 even_two
  have hkpos : 0 < k := by positivity
  obtain ⟨⟨s₀, hs₀⟩, hgen⟩ := hcyc.exists_generator
  have hord : orderOf s₀ = 2 * k := by
    rw [← hk2, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  have hs₀k : s₀ ^ k = d.t := by
    apply huniq _ (pow_mem hs₀ k)
    apply orderOf_eq_prime
    · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    · intro h1
      have := orderOf_le_of_pow_eq_one hkpos h1
      omega
  have hA₁S : ∀ x ∈ d.A₁, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    d.L_commute_centralizer x (d.A₁_le_P.trans d.P_le_L hx) y hy.1
  have hpow : ∀ z ∈ d.A₁ ⊔ S, z ^ k = 1 ∨ z ^ k = d.t := by
    intro z hz
    obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hA₁S hz
    rw [Commute.mul_pow (hA₁S a ha s hs) k]
    have hak : a ^ k = 1 := by
      obtain ⟨j, hj⟩ := hkeven
      rw [hj, ← two_mul, pow_mul, sq, d.A₁_comm_sq.2 a ha, one_pow]
    have hsk : (s ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, ← hk2]
      have := pow_card_eq_one' (G := S) (x := ⟨s, hs⟩)
      exact congrArg Subtype.val this
    rw [hak, one_mul]
    by_cases h1 : s ^ k = 1
    · exact Or.inl h1
    · exact Or.inr (huniq _ (pow_mem hs k) (orderOf_eq_prime hsk h1))
  obtain ⟨g, hgB, hgne⟩ := hd.exists_conj_mem_B₁ hI hO hP
  obtain ⟨n', hn'N, hn't⟩ := exists_normalizer_conj_eq_of_weakly_closed_in hd.T_syl
    (inf_le_left : R ≤ d.T) hd.weakly_closed_R
    (g := g) (fun r hr => (mem_centralizer_iff.1 hr.2 _ hgB).symm)
  have hs₀R : s₀ ∈ R := hd.kernel_le_R hs₀
  have hLS : ∀ x ∈ d.A₃, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    d.L_commute_centralizer x (d.A₃_le_P.trans d.P_le_L hx) y hy.1
  have hs₀Z : ∀ r ∈ R, r * s₀ = s₀ * r := by
    intro r hr
    obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hLS (hd.R_le hC hr)
    have h1 : a * s₀ = s₀ * a := hLS a ha s₀ hs₀
    have h2 : s * s₀ = s₀ * s := hd.kernel_comm s hs s₀ hs₀
    calc a * s * s₀ = a * (s * s₀) := by group
      _ = a * (s₀ * s) := by rw [h2]
      _ = (a * s₀) * s := by group
      _ = (s₀ * a) * s := by rw [h1]
      _ = s₀ * (a * s) := by group
  have hconjR : n'⁻¹ * s₀ * n' ∈ R := by
    have := (mem_normalizer_iff.1 (inv_mem hn'N) s₀).1 hs₀R
    rwa [inv_inv] at this
  have hconjZ : ∀ r ∈ R, r * (n'⁻¹ * s₀ * n') = (n'⁻¹ * s₀ * n') * r := by
    intro r hr
    have hr' : n' * r * n'⁻¹ ∈ R := (mem_normalizer_iff.1 hn'N r).1 hr
    calc r * (n'⁻¹ * s₀ * n') = n'⁻¹ * ((n' * r * n'⁻¹) * s₀) * n' := by group
      _ = n'⁻¹ * (s₀ * (n' * r * n'⁻¹)) * n' := by rw [hs₀Z _ hr']
      _ = (n'⁻¹ * s₀ * n') * r := by group
  have hmem := hd.center_R_le hC hconjR hconjZ
  have hconjk : (n'⁻¹ * s₀ * n') ^ k = n'⁻¹ * d.t * n' := by
    have := map_pow (MulAut.conj n'⁻¹) s₀ k
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [← this, hs₀k]
  rcases hpow _ hmem with h1 | h1
  · rw [hconjk] at h1
    apply hd.t_ne_one
    calc d.t = n' * (n'⁻¹ * d.t * n') * n'⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · rw [hconjk, hn't] at h1
    exact hgne h1

end Data

end CFSG.LocalAnalysis.EvenBN.U5
