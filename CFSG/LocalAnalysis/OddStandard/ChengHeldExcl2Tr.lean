module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Hom

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

open Classical in
@[expose] noncomputable def ext1 {H : Subgroup G} {B : Type*} [CommGroup B] (f : ↥H →* B)
    (x : G) : B :=
  if hx : x ∈ H then f ⟨x, hx⟩ else 1

section Ext1

omit [Finite G]

variable {H : Subgroup G} {B : Type*} [CommGroup B] (f : ↥H →* B)

theorem ext1_apply {x : G} (hx : x ∈ H) : ext1 f x = f ⟨x, hx⟩ := by
  simp [ext1, hx]

theorem ext1_mul {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ext1 f (x * y) = ext1 f x * ext1 f y := by
  rw [ext1_apply f (mul_mem hx hy), ext1_apply f hx, ext1_apply f hy]
  exact map_mul f ⟨x, hx⟩ ⟨y, hy⟩

theorem ext1_one : ext1 f 1 = 1 := by
  rw [ext1_apply f H.one_mem]
  exact map_one f

theorem ext1_inv {x : G} (hx : x ∈ H) : ext1 f x⁻¹ = (ext1 f x)⁻¹ := by
  rw [ext1_apply f (H.inv_mem hx), ext1_apply f hx]
  exact map_inv f ⟨x, hx⟩

theorem ext1_cj {a g : G} (ha : a ∈ H) (hg : g ∈ H) : ext1 f (cj a g) = ext1 f a := by
  unfold cj
  rw [ext1_mul f (mul_mem (H.inv_mem hg) ha) hg, ext1_mul f (H.inv_mem hg) ha, ext1_inv f hg]
  rw [mul_comm (ext1 f g)⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem ext1_pow {x : G} (hx : x ∈ H) (n : ℕ) : ext1 f (x ^ n) = (ext1 f x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact ext1_one f
  | succ n ih => rw [pow_succ, ext1_mul f (pow_mem hx n) hx, ih, pow_succ]

theorem ext1_cm {a b : G} (ha : a ∈ H) (hb : b ∈ H) : ext1 f (cm a b) = 1 := by
  have hcm : cm a b ∈ H := mul_mem (mul_mem (mul_mem (H.inv_mem ha) (H.inv_mem hb)) ha) hb
  have e : (⟨cm a b, hcm⟩ : ↥H) =
      (⟨a, ha⟩ : ↥H)⁻¹ * (⟨b, hb⟩ : ↥H)⁻¹ * ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext (by simp [cm])
  rw [ext1_apply f hcm, e]
  simp only [map_mul, map_inv]
  exact ChartShape.cm_eq_one_iff.2 (Commute.all _ _)

end Ext1

omit [Finite G] in
theorem zmod_two_tpu (a_t a_p a_u : Multiplicative (ZMod 2))
    (h1 : a_p = a_u * a_p * a_t ^ 3) (h2 : a_u = a_p * a_t) (h7 : a_t * a_p = 1) :
    a_t = 1 ∧ a_p = 1 ∧ a_u = 1 := by
  revert a_t a_p a_u
  decide

omit [Finite G] in
theorem zmod_two_ml (a_t a_m a_l : Multiplicative (ZMod 2))
    (h3 : a_m = a_l * a_m * a_t ^ 2) (h4 : a_l = a_m * a_t ^ 2) : a_m = 1 ∧ a_l = 1 := by
  revert a_t a_m a_l
  decide

omit [Finite G] in
theorem zmod_two_zx (a_z a_x : Multiplicative (ZMod 2))
    (h5 : a_z = a_x * a_z) (h6 : a_x = a_z) : a_z = 1 ∧ a_x = 1 := by
  revert a_z a_x
  decide

omit [Finite G] in
theorem zmod_two_mul_self (a : Multiplicative (ZMod 2)) : a * a = 1 := by
  revert a
  decide

omit [Finite G] in
theorem zmod_two_eq_ofAdd_one {a : Multiplicative (ZMod 2)} (ha : a ≠ 1) :
    a = Multiplicative.ofAdd 1 := by
  revert a
  decide

omit [Finite G] in
theorem zmod_two_ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem not_mem_S_of_mem_P (_hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) {x : G}
    (hx : x ∈ centralizer (K.c.V : Set G)) (hxW : x ∉ K.c.W) : x ∉ d.S := fun hxS =>
  hxW ⟨hxS, hx⟩

theorem exists_hom (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) {z : G}
    (hzP : z ∈ d.X ⊓ centralizer (K.c.V : Set G)) (hzW : z ∉ K.c.W) (hz2 : z * z = 1) :
    ∃ f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2),
      ext1 f z = Multiplicative.ofAdd 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := normalizer (K.c.V : Set G) with hH
  have hXH : d.X ≤ H := K.X_le_normalizer_V
  have hzX : z ∈ d.X := hzP.1
  have hzH : z ∈ H := hXH hzX
  have hSX : d.S ≤ d.X := d.S_le_X
  have hNorm : (d.S.subgroupOf d.X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSX]
    intro x hx
    exact mem_normalizer_fintype fun s hs => d.conj_mem_S hx hs
  have hQS : d.QS ≤ d.S := sup_le (fun u hu => (K.Q_le_W hQt hu).1) le_rfl
  have hexp : ∀ e : ↥d.X ⧸ d.S.subgroupOf d.X, e * e = 1 := by
    intro e
    induction e using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.2 (hQS (K.c.sq_mem_QS K.hα K.h K.hP K.hQ x.2))
  have hzS : z ∉ d.S := K.not_mem_S_of_mem_P hQt hzP.2 hzW
  have hzE : (QuotientGroup.mk ⟨z, hzX⟩ : ↥d.X ⧸ d.S.subgroupOf d.X) ≠ 1 := fun h =>
    hzS (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  obtain ⟨θ, hθ⟩ := exists_hom_zmod_two hexp hzE
  let θ₀ : ↥d.X →* Multiplicative (ZMod 2) := θ.comp (QuotientGroup.mk' _)
  have hθS : ∀ (s : G) (hs : s ∈ d.S), θ₀ ⟨s, hSX hs⟩ = 1 := by
    intro s hs
    show θ (QuotientGroup.mk ⟨s, hSX hs⟩) = 1
    rw [(QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hs), map_one]
  have hθz : θ₀ ⟨z, hzX⟩ = Multiplicative.ofAdd 1 := by
    exact zmod_two_eq_ofAdd_one hθ
  set X' : Subgroup ↥H := d.X.subgroupOf H with hX'
  let ϕ : ↥X' →* Multiplicative (ZMod 2) :=
    θ₀.comp (Subgroup.subgroupOfEquivOfLe hXH).toMonoidHom
  have hodd : ¬ 2 ∣ X'.index := by
    have hsyl := K.c.X_sylow_G_of_facts K.hα K.h K.hP K.hQ
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 (hsyl.of_le hXH le_top)).2.2
  have hA : ∀ a : Multiplicative (ZMod 2), a * a = 1 := zmod_two_mul_self
  have hz2' : (⟨z, hzH⟩ : ↥H) * ⟨z, hzH⟩ = 1 := Subtype.ext hz2
  have ha : ∀ x : ↥H, ∀ hx : x⁻¹ * (⟨z, hzH⟩ : ↥H) * x ∈ X',
      ϕ ⟨x⁻¹ * (⟨z, hzH⟩ : ↥H) * x, hx⟩ = Multiplicative.ofAdd 1 := by
    intro x hx
    have hwX : (x : G)⁻¹ * z * x ∈ d.X := by simpa using mem_subgroupOf.1 hx
    have hwP : (x : G)⁻¹ * z * x ∈ centralizer (K.c.V : Set G) := by
      simpa using K.P_normalized (inv_mem x.2) hzP.2
    have hwW : (x : G)⁻¹ * z * x ∉ K.c.W := fun hw => hzW (by
      have := (K.W_normalized x.2 _).1 hw
      simpa [mul_assoc] using this)
    have hwz : (x : G)⁻¹ * z * x * z⁻¹ ∈ K.c.W :=
      mul_inv_mem_of_relIndex_two (K.W_relIndex_two hQt) ⟨hwX, hwP⟩ hzP hwW hzW
    have e : (⟨(x : G)⁻¹ * z * x, hwX⟩ : ↥d.X) =
        ⟨(x : G)⁻¹ * z * x * z⁻¹, d.S_le_X hwz.1⟩ * ⟨z, hzX⟩ := Subtype.ext (by simp)
    show θ₀ ⟨(x : G)⁻¹ * z * x, hwX⟩ = Multiplicative.ofAdd 1
    rw [e, map_mul, hθS _ hwz.1, hθz, one_mul]
  obtain ⟨f, hf⟩ := exists_hom_apply_eq_of_conj_const_of_mul_self (X := X') hodd hA ϕ hz2' ha
  exact ⟨f, by rw [ext1_apply f hzH]; exact hf⟩

theorem g_mem_normalizer_V : K.g ∈ normalizer (K.c.V : Set G) := by
  have hGF := K.c.gFactsG K.hα K.h K.hP K.hQ K.g_norm K.g_act
  have hVeq := K.c.closure_famG_eq
  refine Sec2Aux.mem_normalizer_of_conj_le fun w hw => ?_
  have := hGF.V_stable K.hα w (by rw [hVeq]; exact hw)
  rwa [hVeq] at this

theorem ext1_S (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) :
    ∀ s ∈ d.S, ext1 f s = 1 := by
  have hSH : d.S ≤ normalizer (K.c.V : Set G) := K.c.S_le_normalizer_V K.hα K.h K.hP K.hQ
  have hgH := K.g_mem_normalizer_V
  have hact := K.g_act
  unfold GAct at hact
  simp only [↓reduceIte] at hact
  obtain ⟨ht, hp, hu, hm, hl, hz, hx⟩ := hact
  have mt : K.c.t ∈ d.S := K.c.t_mem.2
  have mp : K.c.pi ∈ d.S := K.c.mem.1
  have mu : K.c.tau ∈ d.S := K.c.mem.2.1
  have mm : K.c.mu ∈ d.S := K.c.mem.2.2.1
  have ml : K.c.lam ∈ d.S := K.c.mem.2.2.2.1
  have mz : K.c.ze ∈ d.S := K.c.mem.2.2.2.2.1
  have mx : K.c.xi ∈ d.S := K.c.mem.2.2.2.2.2
  have key : ∀ a ∈ d.S, ext1 f (cj a K.g) = ext1 f a := fun a ha => ext1_cj f (hSH ha) hgH
  have e1 := key _ mp
  rw [hp, ext1_mul f (hSH (mul_mem mu mp)) (hSH (pow_mem mt 3)), ext1_mul f (hSH mu) (hSH mp),
    ext1_pow f (hSH mt)] at e1
  have e2 := key _ mu
  rw [hu, ext1_mul f (hSH mp) (hSH mt)] at e2
  have e3 := key _ mm
  rw [hm, ext1_mul f (hSH (mul_mem ml mm)) (hSH (pow_mem mt 2)), ext1_mul f (hSH ml) (hSH mm),
    ext1_pow f (hSH mt)] at e3
  have e4 := key _ ml
  rw [hl, ext1_mul f (hSH mm) (hSH (pow_mem mt 2)), ext1_pow f (hSH mt)] at e4
  have e5 := key _ mz
  rw [hz, ext1_mul f (hSH mx) (hSH mz)] at e5
  have e6 := key _ mx
  rw [hx] at e6
  have e7 : ext1 f K.c.t * ext1 f K.c.pi = 1 := by
    have h1 := ext1_cm f (hSH mm) (hSH mz)
    rw [K.c.frame.mu_ze, ext1_mul f (hSH mt) (hSH mp)] at h1
    exact h1
  obtain ⟨h_t, h_p, h_u⟩ := zmod_two_tpu _ _ _ (by simpa using e1.symm) (by simpa using e2.symm) e7
  obtain ⟨h_m, h_l⟩ := zmod_two_ml _ _ _ (by simpa using e3.symm) (by simpa using e4.symm)
  obtain ⟨h_z, h_x⟩ := zmod_two_zx _ _ (by simpa using e5.symm) (by simpa using e6.symm)
  have hgen : ∀ a ∈ ({K.c.t, K.c.pi, K.c.tau, K.c.mu, K.c.lam, K.c.ze, K.c.xi} : Set G),
      ext1 f a = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  intro s hs
  rw [← K.c.gen] at hs
  have hmem : ∀ a ∈ closure ({K.c.t, K.c.pi, K.c.tau, K.c.mu, K.c.lam, K.c.ze, K.c.xi} : Set G),
      a ∈ normalizer (K.c.V : Set G) := fun a ha => hSH (K.c.gen ▸ ha)
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact ext1_one f
  | mul a b ha hb iha ihb => rw [ext1_mul f (hmem a ha) (hmem b hb), iha, ihb, one_mul]
  | inv a ha iha => rw [ext1_inv f (hmem a ha), iha, inv_one]

theorem ext1_P_iff (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t)
    (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {z : G}
    (hzP : z ∈ d.X ⊓ centralizer (K.c.V : Set G)) (hzW : z ∉ K.c.W)
    (hfz : ext1 f z = Multiplicative.ofAdd 1) {p : G}
    (hp : p ∈ d.X ⊓ centralizer (K.c.V : Set G)) : ext1 f p = 1 ↔ p ∈ K.c.W := by
  have hSH : d.S ≤ normalizer (K.c.V : Set G) := K.c.S_le_normalizer_V K.hα K.h K.hP K.hQ
  have hzH : z ∈ normalizer (K.c.V : Set G) := (centralizer_le_normalizer _) hzP.2
  constructor
  · intro h1
    by_contra hpW
    have hpz : p * z⁻¹ ∈ K.c.W :=
      mul_inv_mem_of_relIndex_two (K.W_relIndex_two hQt) hp hzP hpW hzW
    have e : ext1 f p = ext1 f (p * z⁻¹) * ext1 f z := by
      have : p = (p * z⁻¹) * z := by group
      conv_lhs => rw [this]
      exact ext1_mul f (hSH hpz.1) hzH
    rw [K.ext1_S f _ hpz.1, hfz, one_mul, h1] at e
    exact zmod_two_ofAdd_one_ne_one e.symm
  · intro hw
    exact K.ext1_S f p hw.1

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
