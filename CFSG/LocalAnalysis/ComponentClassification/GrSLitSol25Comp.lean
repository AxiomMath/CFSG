module

public import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.GrSLit.Sol25

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial

variable {H : Type*} [Group H]

theorem mem_of_mul_self_mem {w : H} (hw : Odd (orderOf w)) {N : Subgroup H} (h : w * w ∈ N) :
    w ∈ N := by
  obtain ⟨m, hm⟩ := hw
  have h1 : w = (w * w) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf w + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact pow_mem h _

theorem odd_orderOf_of_mem [Finite H] {Y : Subgroup H} (hY : Odd (Nat.card Y)) {y : H}
    (hy : y ∈ Y) : Odd (orderOf y) :=
  hY.of_dvd_nat (by rw [← Subgroup.orderOf_mk y hy]; exact orderOf_dvd_natCard _)

theorem mem_centralizer_conjSub_iff {g x : H} {K : Subgroup H} :
    x ∈ centralizer (conjSub g K : Set H) ↔ g⁻¹ * x * g ∈ centralizer (K : Set H) := by
  rw [← conjSub_centralizer]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_centralizer_of_mem_normalizer {n x : H} {K : Subgroup H}
    (hn : n ∈ normalizer (K : Set H)) (hx : x ∈ centralizer (K : Set H)) :
    n * x * n⁻¹ ∈ centralizer (K : Set H) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro k hk
  have hk' : n⁻¹ * k * n ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem hn) k).mp hk
    rwa [inv_inv] at this
  have h := hx _ hk'
  calc k * (n * x * n⁻¹) = n * ((n⁻¹ * k * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * k * n)) * n⁻¹ := by rw [h]
    _ = n * x * n⁻¹ * k := by group

theorem conjSub_pow_eq {g a : H} (hga : g * a = a * g) {K : Subgroup H}
    (h : conjSub g K = conjSub a K) (j : ℕ) : conjSub (g ^ j) K = conjSub (a ^ j) K := by
  induction j with
  | zero => simp only [pow_zero]
  | succ j ih =>
    have hc : g * a ^ j = a ^ j * g := (Commute.pow_right (show Commute g a from hga) j).eq
    rw [pow_succ', conjSub_mul, ih, ← conjSub_mul, hc, conjSub_mul, h, ← conjSub_mul, ← pow_succ]

theorem conjSub_eq_self_of_odd {y a : H} (hya : y * a = a * y) (ha : a * a = 1)
    (hy : Odd (orderOf y)) {K : Subgroup H} (h : conjSub y K = conjSub a K) :
    conjSub y K = K := by
  have h1 := conjSub_pow_eq hya h (orderOf y)
  obtain ⟨m, hm⟩ := hy
  have ha' : a ^ orderOf y = a := by
    rw [hm, pow_succ, pow_mul, pow_two, ha, one_pow, one_mul]
  rw [pow_orderOf_eq_one, ha'] at h1
  rw [h, ← h1, conjSub, show (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H from by ext; simp,
    Subgroup.map_id]

variable [Finite H]

theorem two_dvd_card_inf_centralizer {P F : Subgroup H} (hP : IsPGroup 2 P)
    (hPF : P ≤ normalizer (F : Set H)) (hF : 2 ∣ Nat.card F) :
    2 ∣ Nat.card ↥(F ⊓ centralizer (P : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P F := MulAction.compHom F (inclusion hPF)
  have h := hP.card_modEq_card_fixedPoints F
  have hfix : ∀ x : F, x ∈ MulAction.fixedPoints P F ↔ (x : H) ∈ centralizer (P : Set H) := by
    intro x
    rw [MulAction.mem_fixedPoints, mem_centralizer_iff]
    constructor
    · intro hx u hu
      have h1 := congrArg Subtype.val (hx ⟨u, hu⟩)
      change u * (x : H) * u⁻¹ = x at h1
      calc u * (x : H) = u * x * u⁻¹ * u := by group
        _ = x * u := by rw [h1]
    · intro hx u
      apply Subtype.ext
      change (u : H) * x * (u : H)⁻¹ = x
      rw [hx u u.2, mul_inv_cancel_right]
  have he : Nat.card (MulAction.fixedPoints P F) = Nat.card ↥(F ⊓ centralizer (P : Set H)) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, mem_inf.mpr ⟨x.1.2, (hfix x.1).mp x.2⟩⟩
        invFun := fun x => ⟨⟨x, (mem_inf.mp x.2).1⟩, (hfix _).mpr (mem_inf.mp x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [he] at h
  exact Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hF))

theorem exists_noncentral_mul_self_mem_center {K : Subgroup H} (hK : IsQuasisimple K) :
    ∃ k ∈ K, k ∉ (center K).map K.subtype ∧ k * k ∈ (center K).map K.subtype := by
  obtain ⟨-, hs, a, b, hab⟩ := hK
  have : IsSimpleGroup (K ⧸ center K) := hs
  have heven : 2 ∣ Nat.card (K ⧸ center K) := by
    by_contra hodd
    have hsol : Group.IsSolvable (K ⧸ center K) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 heven
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k, k.2, ?_, ?_⟩
  · rintro ⟨z, hz, hzk⟩
    have hk : k ∈ center K := by rwa [← Subtype.ext hzk]
    rw [(QuotientGroup.eq_one_iff k).mpr hk, orderOf_one] at hq
    exact absurd hq (by norm_num)
  · have h2 : ((k * k : K) : K ⧸ center K) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two, ← hq, pow_orderOf_eq_one]
    exact ⟨k * k, (QuotientGroup.eq_one_iff _).mp h2, rfl⟩

omit [Finite H] in
theorem mem_center_layer_of_forall {x : H} (hx : x ∈ layer H)
    (h : ∀ K : Subgroup H, IsComponent K → x ∈ centralizer (K : Set H)) :
    x ∈ (center (layer H)).map (layer H).subtype := by
  refine LocalAnalysis.ComponentInitial.mem_map_center_iff.mpr ⟨hx, fun e he => ?_⟩
  have hle : layer H ≤ centralizer ({x} : Set H) := by
    refine sSup_le fun K hK y hy => ?_
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (h K hK)) y hy)
  exact mem_centralizer_singleton_iff.mp (hle he)

omit [Finite H] in
theorem mem_center_of_mem_center_layer {K : Subgroup H} (hK : IsComponent K) {k : H}
    (hk : k ∈ K) (hkZ : k ∈ (center (layer H)).map (layer H).subtype) :
    k ∈ (center K).map K.subtype := by
  refine LocalAnalysis.ComponentInitial.mem_map_center_iff.mpr ⟨hk, fun e he => ?_⟩
  exact (LocalAnalysis.ComponentInitial.mem_map_center_iff.mp hkZ).2 e (component_le_layer hK he)

omit [Finite H] in
theorem mem_centralizer_of_mem_center_layer {K : Subgroup H} (hK : IsComponent K) {z : H}
    (hz : z ∈ (center (layer H)).map (layer H).subtype) : z ∈ centralizer (K : Set H) :=
  mem_centralizer_iff.mpr fun k hk =>
    (LocalAnalysis.ComponentInitial.mem_map_center_iff.mp hz).2 k (component_le_layer hK hk)

omit [Finite H] in
theorem center_layer_normal : ((center (layer H)).map (layer H).subtype).Normal := by
  have : (layer H).Characteristic := layer_characteristic
  have hEn : (layer H).Normal := inferInstance
  refine ⟨fun z hz g => ?_⟩
  rw [LocalAnalysis.ComponentInitial.mem_map_center_iff] at hz ⊢
  refine ⟨hEn.conj_mem z hz.1 g, fun e he => ?_⟩
  have he' : g⁻¹ * e * g ∈ layer H := by simpa using hEn.conj_mem e he g⁻¹
  have h := hz.2 _ he'
  calc e * (g * z * g⁻¹) = g * ((g⁻¹ * e * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * e * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * e := by group

omit [Finite H] in
theorem conjSub_one (K : Subgroup H) : conjSub (1 : H) K = K := by
  rw [conjSub, show (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H from by ext; simp,
    Subgroup.map_id]

omit [Finite H] in
theorem iSup_conjSub_le_layer {A K : Subgroup H} (hK : IsComponent K) :
    (⨆ (a : H) (_ : a ∈ A), conjSub a K) ≤ layer H :=
  iSup₂_le fun a _ => component_le_layer (isComponent_map_of_isComponent (MulAut.conj a) hK)

theorem iSup_conjSub_le_centralizer {A K L : Subgroup H} (hK : IsComponent K)
    (hL : IsComponent L) (hLA : ∀ a ∈ A, conjSub a K ≠ L) :
    (⨆ (a : H) (_ : a ∈ A), conjSub a K) ≤ centralizer (L : Set H) := by
  refine iSup₂_le fun a ha => ?_
  rcases distinct_components_commute (isComponent_map_of_isComponent (MulAut.conj a) hK) hL with
    h | h
  · exact absurd h (hLA a ha)
  · exact commutator_eq_bot_iff_le_centralizer.mp h

omit [Finite H] in
theorem le_normalizer_iSup_conjSub {A K : Subgroup H} :
    A ≤ normalizer ((⨆ (a : H) (_ : a ∈ A), conjSub a K : Subgroup H) : Set H) := by
  have key : ∀ b ∈ A, conjSub b (⨆ (a : H) (_ : a ∈ A), conjSub a K) ≤
      ⨆ (a : H) (_ : a ∈ A), conjSub a K := by
    intro b hb
    rw [conjSub, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [← conjSub, ← conjSub_mul]
    exact le_iSup₂_of_le (b * a) (mul_mem hb ha) le_rfl
  intro b hb
  exact mem_normalizer_of_conjSub_le (key b hb) (key b⁻¹ (inv_mem hb))

theorem normalizes_components_of_odd {A Y : Subgroup H} (hA2 : ∀ a ∈ A, a * a = 1)
    (hY : Odd (Nat.card Y)) (hYA : ∀ y ∈ Y, ∀ a ∈ A, y * a = a * y)
    (hNY : centralizer (A : Set H) ≤ normalizer (Y : Set H))
    (hYZ : ∀ y ∈ Y, ∀ z ∈ (center (layer H)).map (layer H).subtype, y * z = z * y)
    {K : Subgroup H} (hK : IsComponent K) : Y ≤ normalizer (K : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  by_contra hyK
  set W := (center (layer H)).map (layer H).subtype with hWdef
  have hWn : W.Normal := center_layer_normal
  set E : Subgroup H := ⨆ (a : H) (_ : a ∈ A), conjSub a K with hEdef
  have hEL : E ≤ layer H := iSup_conjSub_le_layer hK
  have hmove : ∀ g ∈ Y, ∀ a₀ ∈ A, ∀ a ∈ A, conjSub g (conjSub a₀ K) = conjSub a K →
      g ∈ normalizer (K : Set H) := by
    intro g hg a₀ ha₀ a ha h
    have hga₀ : g * a₀ = a₀ * g := hYA g hg a₀ ha₀
    have h1 : conjSub g K = conjSub (a₀⁻¹ * a) K := by
      have e1 : conjSub g (conjSub a₀ K) = conjSub a₀ (conjSub g K) := by
        rw [← conjSub_mul, ← conjSub_mul, hga₀]
      rw [conjSub_mul, ← h, e1, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h2 := conjSub_eq_self_of_odd (hYA g hg _ (mul_mem (inv_mem ha₀) ha))
      (hA2 _ (mul_mem (inv_mem ha₀) ha)) (odd_orderOf_of_mem hY hg) h1
    exact mem_normalizer_of_conjSub_eq h2
  obtain ⟨f, hfE, hfW, hf2, hfA⟩ : ∃ f ∈ E, f ∉ W ∧ f * f ∈ W ∧
      ∀ a ∈ A, f⁻¹ * (a * f * a⁻¹) ∈ W := by
    set π := QuotientGroup.mk' W with hπ
    have hA2' : IsPGroup 2 ↥(A.map π) := by
      refine IsPGroup.map (fun a => ⟨1, ?_⟩) π
      apply Subtype.ext
      simp only [pow_one, pow_two, Subgroup.coe_mul, OneMemClass.coe_one]
      exact hA2 a a.2
    have hAE : A.map π ≤ normalizer ((E.map π : Subgroup _) : Set (H ⧸ W)) := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.le_normalizer_map π (mem_map_of_mem π (le_normalizer_iSup_conjSub ha))
    obtain ⟨k, hkK, hkZ, hk2⟩ := exists_noncentral_mul_self_mem_center hK.1
    have hKE : K ≤ E := le_iSup₂_of_le (1 : H) (one_mem A) (le_of_eq (conjSub_one K).symm)
    have hkE : k ∈ E := hKE hkK
    have heven : 2 ∣ Nat.card ↥(E.map π) := by
      have hk1 : π k ≠ 1 := by
        rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        exact fun h => hkZ (mem_center_of_mem_center_layer hK hkK h)
      have hk2' : π k * π k = 1 := by
        rw [← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact center_component_le_center_layer hK hk2
      have hord : orderOf (⟨π k, mem_map_of_mem π hkE⟩ : ↥(E.map π)) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two, hk2']) hk1
      exact hord ▸ orderOf_dvd_natCard _
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2
      (two_dvd_card_inf_centralizer hA2' hAE heven)
    obtain ⟨hqE, hqC⟩ := mem_inf.mp q.2
    obtain ⟨f, hfE, hfq⟩ := hqE
    have hq' : orderOf (q : H ⧸ W) = 2 := by rw [Subgroup.orderOf_coe]; exact hq
    refine ⟨f, hfE, ?_, ?_, fun a ha => ?_⟩
    · intro hfW
      have : (q : H ⧸ W) = 1 := by
        rw [← hfq, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hfW
      rw [this, orderOf_one] at hq'
      exact absurd hq' (by norm_num)
    · have h1 : π (f * f) = 1 := by
        rw [map_mul, hfq, ← pow_two, ← hq', pow_orderOf_eq_one]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · have hc := (mem_centralizer_iff.mp hqC) (π a) (mem_map_of_mem π ha)
      rw [← hfq] at hc
      have h1 : π (f⁻¹ * (a * f * a⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc]
        group
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨K₀, hK₀, hfK₀⟩ : ∃ K₀ : Subgroup H, IsComponent K₀ ∧ f ∉ centralizer (K₀ : Set H) := by
    by_contra h
    push Not at h
    exact hfW (mem_center_layer_of_forall (hEL hfE) h)
  obtain ⟨a₀, ha₀, rfl⟩ : ∃ a₀ ∈ A, conjSub a₀ K = K₀ := by
    by_contra h
    push Not at h
    exact hfK₀ (iSup_conjSub_le_centralizer hK hK₀ h hfE)
  set K₀ := conjSub a₀ K with hK₀def
  have hfC : ∀ g : H, (∀ a ∈ A, conjSub a K ≠ conjSub g K₀) →
      f ∈ centralizer (conjSub g K₀ : Set H) := fun g hg =>
    iSup_conjSub_le_centralizer hK (isComponent_map_of_isComponent (MulAut.conj g) hK₀) hg hfE
  have h1 : f ∈ centralizer (conjSub y⁻¹ K₀ : Set H) := by
    refine hfC y⁻¹ fun a ha heq => hyK (hmove y hy a ha a₀ ha₀ ?_)
    rw [heq, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have h2 : f ∈ centralizer (conjSub (y⁻¹ * y⁻¹) K₀ : Set H) := by
    refine hfC (y⁻¹ * y⁻¹) fun a ha heq => hyK (mem_of_mul_self_mem (odd_orderOf_of_mem hY hy)
      (hmove (y * y) (mul_mem hy hy) a ha a₀ ha₀ ?_))
    rw [heq, ← conjSub_mul, show y * y * (y⁻¹ * y⁻¹) = 1 by group, conjSub_one]
  have hf'A : f * (y * f * y⁻¹)⁻¹ ∈ centralizer (A : Set H) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hc := hfA a ha
    have hafa : a * f * a⁻¹ = f * (f⁻¹ * (a * f * a⁻¹)) := by group
    have hyc : y * (f⁻¹ * (a * f * a⁻¹)) = (f⁻¹ * (a * f * a⁻¹)) * y := hYZ y hy _ hc
    have hya : y * a = a * y := hYA y hy a ha
    have e0 : a * (y * f * y⁻¹) * a⁻¹ = y * (a * f * a⁻¹) * y⁻¹ := by
      calc a * (y * f * y⁻¹) * a⁻¹ = (a * y) * f * (a * y)⁻¹ := by group
        _ = (y * a) * f * (y * a)⁻¹ := by rw [hya]
        _ = y * (a * f * a⁻¹) * y⁻¹ := by group
    have key : a * (f * (y * f * y⁻¹)⁻¹) * a⁻¹ = f * (y * f * y⁻¹)⁻¹ := by
      set c := f⁻¹ * (a * f * a⁻¹) with hcdef
      calc a * (f * (y * f * y⁻¹)⁻¹) * a⁻¹
          = (a * f * a⁻¹) * (a * (y * f * y⁻¹) * a⁻¹)⁻¹ := by group
        _ = (f * c) * (y * (f * c) * y⁻¹)⁻¹ := by rw [e0, hafa]
        _ = f * c * (y * c * y⁻¹)⁻¹ * (y * f * y⁻¹)⁻¹ := by group
        _ = f * c * c⁻¹ * (y * f * y⁻¹)⁻¹ := by rw [hyc, mul_inv_cancel_right]
        _ = f * (y * f * y⁻¹)⁻¹ := by group
    calc a * (f * (y * f * y⁻¹)⁻¹) = a * (f * (y * f * y⁻¹)⁻¹) * a⁻¹ * a := by group
      _ = f * (y * f * y⁻¹)⁻¹ * a := by rw [key]
  have hw : (f * (y * f * y⁻¹)⁻¹) * y * (f * (y * f * y⁻¹)⁻¹)⁻¹ * y⁻¹ ∈ Y :=
    mul_mem ((mem_normalizer_iff.mp (hNY hf'A) y).mp hy) (inv_mem hy)
  set w := (f * (y * f * y⁻¹)⁻¹) * y * (f * (y * f * y⁻¹)⁻¹)⁻¹ * y⁻¹ with hwdef
  set u := (y * f⁻¹ * y⁻¹) * ((y * y) * f * (y⁻¹ * y⁻¹)) * (y * f⁻¹ * y⁻¹) with hudef
  have hwu : w = f * u := by rw [hwdef, hudef]; group
  have hu : u ∈ centralizer (K₀ : Set H) := by
    have hA : y * f * y⁻¹ ∈ centralizer (K₀ : Set H) := by
      have h := mem_centralizer_conjSub_iff.mp h1
      rwa [inv_inv] at h
    have hB : (y * y) * f * (y⁻¹ * y⁻¹) ∈ centralizer (K₀ : Set H) := by
      have h := mem_centralizer_conjSub_iff.mp h2
      rwa [show (y⁻¹ * y⁻¹)⁻¹ = y * y by rw [mul_inv_rev, inv_inv]] at h
    have hA' : y * f⁻¹ * y⁻¹ ∈ centralizer (K₀ : Set H) := by
      have h := inv_mem hA
      rwa [show (y * f * y⁻¹)⁻¹ = y * f⁻¹ * y⁻¹ by group] at h
    rw [hudef]
    exact mul_mem (mul_mem hA' hB) hA'
  have hfN : f ∈ normalizer (K₀ : Set H) := layer_le_normalizer hK₀ (hEL hfE)
  have hwK : w ∉ centralizer (K₀ : Set H) := by
    intro h
    apply hfK₀
    have e : f = w * u⁻¹ := by rw [hwu]; group
    rw [e]
    exact mul_mem h (inv_mem hu)
  have hw2 : w * w ∈ centralizer (K₀ : Set H) := by
    have e : w * w = (f * f) * (f⁻¹ * u * f) * u := by rw [hwu]; group
    rw [e]
    refine mul_mem (mul_mem (mem_centralizer_of_mem_center_layer hK₀ hf2) ?_) hu
    have h := conj_mem_centralizer_of_mem_normalizer (inv_mem hfN) hu
    rwa [inv_inv] at h
  exact hwK (mem_of_mul_self_mem (odd_orderOf_of_mem hY hw) hw2)

end CFSG.ComponentClassification.GrSLit.Sol25
