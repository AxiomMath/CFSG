module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTau
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

theorem conj_tau_conj {M : Type*} [Group M] (τ : MulAut M) (g h : M) :
    (MulAut.conj h)⁻¹ * (MulAut.conj g * τ) * MulAut.conj h =
      MulAut.conj (h⁻¹ * g * τ h) * τ := by
  apply MulEquiv.ext
  intro x
  have e1 : ((MulAut.conj h)⁻¹ * (MulAut.conj g * τ) * MulAut.conj h) x =
      h⁻¹ * (g * τ (h * x * h⁻¹) * g⁻¹) * h := rfl
  have e2 : (MulAut.conj (h⁻¹ * g * τ h) * τ) x = (h⁻¹ * g * τ h) * τ x * (h⁻¹ * g * τ h)⁻¹ := rfl
  rw [e1, e2, map_mul, map_mul, map_inv]
  group

theorem sq_conj_tau {M : Type*} [Group M] (τ : MulAut M) (hτ : ∀ x, τ (τ x) = x) (g : M) :
    (MulAut.conj g * τ) * (MulAut.conj g * τ) = MulAut.conj (g * τ g) := by
  apply MulEquiv.ext
  intro x
  have e1 : ((MulAut.conj g * τ) * (MulAut.conj g * τ)) x = g * τ (g * τ x * g⁻¹) * g⁻¹ := rfl
  have e2 : (MulAut.conj (g * τ g)) x = (g * τ g) * x * (g * τ g)⁻¹ := rfl
  rw [e1, e2, map_mul, map_mul, map_inv, hτ]
  group

theorem aut_card_le {X : Type} [Group X] [Finite X] (h : StatedClassicalModel X .PSL 3 3 1) :
    Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 3 3 1 h).2.2.2.2
    (by norm_num)
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 2 := by
    have h1 := Nat.le_of_dvd (by norm_num) hb
    have e : 2 * 1 * Nat.gcd 3 (3 ^ 1 - 1) = 2 := by norm_num
    rw [e] at h1
    exact h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have h4 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ≤ Nat.card X :=
    Nat.card_le_card_of_surjective ((MulAut.conj : X →* MulAut X).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rw [h3]
  exact Nat.mul_le_mul h2 h4

theorem aut_card_S3 {X : Type} [Group X] (e : X ≃* S3) (hb : Nat.card (MulAut X) ≤ 2 * Nat.card X) :
    Nat.card (MulAut S3) ≤ 2 * Nat.card S3 := by
  rw [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]
  exact hb

section Model

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

@[expose] noncomputable def actN (e : ↥K ≃* S3) : ↥(Subgroup.normalizer (K : Set G)) →* MulAut S3 :=
  (MulAut.congr e).toMonoidHom.comp (conjAct K)

omit [Finite G] in
theorem actN_apply (e : ↥K ≃* S3) (n : ↥(Subgroup.normalizer (K : Set G))) (s : S3) :
    actN e n s = e (conjAct K n (e.symm s)) := rfl

omit [Finite G] in
theorem actN_G (e : ↥K ≃* S3) (n : ↥(Subgroup.normalizer (K : Set G))) (s : S3) :
    ((e.symm (actN e n s) : ↥K) : G) = (n : G) * ((e.symm s : ↥K) : G) * (n : G)⁻¹ := by
  rw [actN_apply, e.symm_apply_apply]
  rfl

theorem actN_eq_iff (e : ↥K ≃* S3) (n : ↥(Subgroup.normalizer (K : Set G))) (s t : S3) :
    actN e n s = t ↔ (n : G) * ((e.symm s : ↥K) : G) * (n : G)⁻¹ = ((e.symm t : ↥K) : G) := by
  rw [← actN_G e n s]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact e.symm.injective (Subtype.ext h)

theorem actN_k (e : ↥K ≃* S3) (n : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    ((e.symm (actN e n (e k)) : ↥K) : G) = (n : G) * (k : G) * (n : G)⁻¹ := by
  rw [actN_G, e.symm_apply_apply]

theorem actN_of_mem (e : ↥K ≃* S3) {k : G} (hk : k ∈ K) :
    actN e ⟨k, Subgroup.le_normalizer hk⟩ = MulAut.conj (e ⟨k, hk⟩) := by
  apply MulEquiv.ext
  intro s
  rw [actN_eq_iff]
  have : e.symm (MulAut.conj (e ⟨k, hk⟩) s) = ⟨k, hk⟩ * e.symm s * ⟨k, hk⟩⁻¹ := by
    simp [MulAut.conj_apply]
  rw [this]
  rfl

theorem actN_eq_one_iff (e : ↥K ≃* S3) (n : ↥(Subgroup.normalizer (K : Set G))) :
    actN e n = 1 ↔ ∀ k ∈ K, (n : G) * k = k * (n : G) := by
  constructor
  · intro h k hk
    have h1 := (actN_eq_iff e n (e ⟨k, hk⟩) (e ⟨k, hk⟩)).1 (by rw [h]; rfl)
    rw [e.symm_apply_apply] at h1
    change (n : G) * k * (n : G)⁻¹ = k at h1
    calc (n : G) * k = ((n : G) * k * (n : G)⁻¹) * n := by group
      _ = k * n := by rw [h1]
  · intro h
    apply MulEquiv.ext
    intro s
    rw [actN_eq_iff]
    have hc := h (e.symm s : G) (e.symm s).2
    show (n : G) * ((e.symm s : ↥K) : G) * (n : G)⁻¹ = ((e.symm s : ↥K) : G)
    calc (n : G) * ((e.symm s : ↥K) : G) * (n : G)⁻¹
        = ((e.symm s : ↥K) : G) * (n : G) * (n : G)⁻¹ := by rw [hc]
      _ = ((e.symm s : ↥K) : G) := by group

omit [Finite G] in
theorem inv_class_of
    (e : ↥K ≃* S3) : ∀ a ∈ K, ∀ b ∈ K, a ≠ 1 → b ≠ 1 → a ^ 2 = 1 → b ^ 2 = 1 →
    ∃ k ∈ K, k⁻¹ * a * k = b := by
  intro a ha b hb ha1 hb1 ha2 hb2
  have key : ∀ x (hx : x ∈ K), x ≠ 1 → x ^ 2 = 1 → ∃ g : S3, g * u0S * g⁻¹ = e ⟨x, hx⟩ := by
    intro x hx hx1 hx2
    apply hconjS
    · intro h
      apply hx1
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · rw [← map_pow]
      have : (⟨x, hx⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
  obtain ⟨g, hg⟩ := key a ha ha1 ha2
  obtain ⟨h, hh⟩ := key b hb hb1 hb2
  refine ⟨((e.symm (g * h⁻¹) : ↥K) : G), (e.symm (g * h⁻¹)).2, ?_⟩
  have h1 : (e.symm (g * h⁻¹))⁻¹ * ⟨a, ha⟩ * e.symm (g * h⁻¹) = ⟨b, hb⟩ := by
    apply e.injective
    simp only [map_mul, map_inv, e.apply_symm_apply]
    rw [← hg, ← hh]
    group
  exact congrArg Subtype.val h1

theorem z4_of
    (e : ↥K ≃* S3) (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) :
    ∀ u ∈ K, u ≠ 1 → u ^ 2 = 1 → ∀ y ∈ Subgroup.normalizer (K : Set G),
      (∀ v ∈ threeCoreCent K u, y * v = v * y) → ¬ Ch1.InducesInner y K →
        ∀ w ∈ K, (y * y)⁻¹ * w * (y * y) = u⁻¹ * w * u := by
  intro u hu hu1 hu2 y hy hcent hninner w hw
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hy
  let n : ↥(Subgroup.normalizer (K : Set G)) := ⟨y⁻¹, hyinv⟩
  have hnG : (n : G) = y⁻¹ := rfl
  have hnGi : (n : G)⁻¹ = y := by rw [hnG, inv_inv]
  let β : MulAut S3 := actN e n
  let u' : S3 := e ⟨u, hu⟩
  have huu : u * u = 1 := by rwa [sq] at hu2
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hu'2 : u' * u' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext huu
  have hfix : ∀ s : S3, s * u' = u' * s → s ^ 3 = 1 → β s = s := by
    intro s hs1 hs3
    have hvK : ((e.symm s : ↥K) : G) ∈ K := (e.symm s).2
    have hvu : ((e.symm s : ↥K) : G) * u = u * ((e.symm s : ↥K) : G) := by
      have h1 := congrArg (fun t => ((e.symm t : ↥K) : G)) hs1
      simpa [u'] using h1
    have hv3 : ((e.symm s : ↥K) : G) ^ 3 = 1 := by
      have h1 := congrArg (fun t => ((e.symm t : ↥K) : G)) hs3
      simpa using h1
    have hvmem : ((e.symm s : ↥K) : G) ∈ threeCoreCent K u :=
      Subgroup.subset_closure ⟨hvK, hvu, hv3⟩
    have hyv := hcent _ hvmem
    show actN e n s = s
    rw [actN_eq_iff]
    show y⁻¹ * ((e.symm s : ↥K) : G) * y⁻¹⁻¹ = ((e.symm s : ↥K) : G)
    calc y⁻¹ * ((e.symm s : ↥K) : G) * y⁻¹⁻¹ = y⁻¹ * (((e.symm s : ↥K) : G) * y) := by group
      _ = y⁻¹ * (y * ((e.symm s : ↥K) : G)) := by rw [← hyv]
      _ = ((e.symm s : ↥K) : G) := by group
  have hinner : ∀ g : S3, β ≠ MulAut.conj g := by
    intro g hg
    apply hninner
    refine ⟨(((e.symm g)⁻¹ : ↥K) : G), ((e.symm g)⁻¹).2, fun x hx => ?_⟩
    have h1 : β (e ⟨x, hx⟩) = g * e ⟨x, hx⟩ * g⁻¹ := by rw [hg]; rfl
    have h3 := actN_k e n ⟨x, hx⟩
    have h2 : ((e.symm (β (e ⟨x, hx⟩)) : ↥K) : G) =
        ((e.symm g : ↥K) : G) * x * ((e.symm g : ↥K) : G)⁻¹ := by
      rw [h1]
      simp
    have h4 : y⁻¹ * x * y = ((e.symm g : ↥K) : G) * x * ((e.symm g : ↥K) : G)⁻¹ := by
      rw [← h2]
      have h3' := h3
      rw [hnG, hnGi] at h3'
      exact h3'.symm
    rw [h4]
    simp
  have hz := z4S hb hu'1 hu'2 β hfix hinner (e ⟨w, hw⟩)
  have hzG := congrArg (fun t => ((e.symm t : ↥K) : G)) hz
  have hβ1 : ((e.symm (β (e ⟨w, hw⟩)) : ↥K) : G) = y⁻¹ * w * y := by
    have h5 := actN_k e n ⟨w, hw⟩
    rw [hnG, hnGi] at h5
    exact h5
  have hβ2 : ((e.symm (β (β (e ⟨w, hw⟩))) : ↥K) : G) = y⁻¹ * (y⁻¹ * w * y) * y := by
    have h5 := actN_k e n (e.symm (β (e ⟨w, hw⟩)))
    rw [e.apply_symm_apply, hβ1, hnG, hnGi] at h5
    exact h5
  have hrhs : ((e.symm (u' * e ⟨w, hw⟩ * u'⁻¹) : ↥K) : G) = u * w * u⁻¹ := by
    simp [u']
  rw [hβ2, hrhs] at hzG
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  calc (y * y)⁻¹ * w * (y * y) = y⁻¹ * (y⁻¹ * w * y) * y := by group
    _ = u * w * u⁻¹ := hzG
    _ = u⁻¹ * w * u := by rw [hui]

@[expose] noncomputable def actA (e : ↥K ≃* S3) {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    ↥A →* MulAut S3 :=
  (actN e).comp (Subgroup.inclusion hAN)

omit [Finite G] in
theorem actA_apply (e : ↥K ≃* S3) {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (a : ↥A) : actA e hAN a = actN e ⟨(a : G), hAN a.2⟩ := rfl

theorem actA_injective (e : ↥K ≃* S3) {A : Subgroup G} (hA : IsAutPair K A)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) : Function.Injective (actA e hAN) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : ∀ k ∈ K, (a : G) * k = k * (a : G) :=
    (actN_eq_one_iff e ⟨(a : G), hAN a.2⟩).1 ha
  have : (a : G) ∈ A ⊓ Subgroup.centralizer (K : Set G) :=
    ⟨a.2, Subgroup.mem_centralizer_iff.2 (fun k hk => (h1 k hk).symm)⟩
  rw [hA.2.2, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem actA_surjective (e : ↥K ≃* S3) (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3)
    {A : Subgroup G} (hA : IsAutPair K A) (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    Function.Surjective (actA e hAN) := by
  have hcard : Nat.card ↥A = 2 * Nat.card S3 := by
    rw [hA.2.1, Nat.card_congr e.toEquiv]
  have := (actA_injective e hA hAN).bijective_of_nat_card_le (by rw [hcard]; exact hb)
  exact this.2

theorem actA_of_mem (e : ↥K ≃* S3) {A : Subgroup G} (hA : IsAutPair K A)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    actA e hAN ⟨k, hA.1 hk⟩ = MulAut.conj (e ⟨k, hk⟩) := actN_of_mem e hk

theorem outer_decomp
    (e : ↥K ≃* S3) (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3)
    {A : Subgroup G} (hA : IsAutPair K A) (hAN : A ≤ Subgroup.normalizer (K : Set G)) {f : G}
    (hf : f ∈ A) (hfK : f ∉ K) (hf2 : f ^ 2 = 1) :
    ∃ g : S3, actA e hAN ⟨f, hf⟩ = MulAut.conj g * tauAut ∧ g * tauAut g = 1 := by
  obtain ⟨g, hg | hg⟩ := aut_cases hb (actA e hAN ⟨f, hf⟩)
  · exfalso
    apply hfK
    have hk : ((e.symm g : ↥K) : G) ∈ K := (e.symm g).2
    have h1 : actA e hAN ⟨f, hf⟩ = actA e hAN ⟨((e.symm g : ↥K) : G), hA.1 hk⟩ := by
      rw [hg, actA_of_mem e hA hAN hk]
      simp
    have h2 := actA_injective e hA hAN h1
    have h3 : f = ((e.symm g : ↥K) : G) := congrArg Subtype.val h2
    rw [h3]
    exact hk
  · refine ⟨g, hg, ?_⟩
    have h1 : actA e hAN ⟨f, hf⟩ * actA e hAN ⟨f, hf⟩ = 1 := by
      rw [← map_mul, ← map_one (actA e hAN)]
      congr 1
      exact Subtype.ext (by simpa [sq] using hf2)
    rw [hg, sq_conj_tau tauAut tau_tau] at h1
    have h2 : MulAut.conj (g * tauAut g) = MulAut.conj (1 : S3) := by rw [h1]; simp
    exact conj_injective_S3 h2

theorem outer_inv_of
    (e : ↥K ≃* S3) (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3)
    {A : Subgroup G} (hA : IsAutPair K A) :
    ∀ f ∈ A, ∀ f' ∈ A, f ∉ K → f' ∉ K → f ^ 2 = 1 → f' ^ 2 = 1 → ∃ a ∈ A, a⁻¹ * f * a = f' := by
  intro f hf f' hf' hfK hf'K hf2 hf'2
  have hidx : Idx2 K A := ⟨hA.1, hA.2.1⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hidx.le_normalizer
  obtain ⟨g, hα, hg⟩ := outer_decomp e hb hA hAN hf hfK hf2
  obtain ⟨g', hα', hg'⟩ := outer_decomp e hb hA hAN hf' hf'K hf'2
  obtain ⟨h, hh⟩ := outerS hg hg'
  have hk : ((e.symm h : ↥K) : G) ∈ K := (e.symm h).2
  refine ⟨((e.symm h : ↥K) : G), hA.1 hk, ?_⟩
  have h1 : (⟨((e.symm h : ↥K) : G), hA.1 hk⟩ : ↥A)⁻¹ * ⟨f, hf⟩ * ⟨((e.symm h : ↥K) : G), hA.1 hk⟩ =
      ⟨f', hf'⟩ := by
    apply actA_injective e hA hAN
    rw [map_mul, map_mul, map_inv, actA_of_mem e hA hAN hk, hα, hα']
    simp only [e.apply_symm_apply]
    rw [conj_tau_conj, hh]
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem noE8K
    (e : ↥K ≃* S3) {a b c : ↥K} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc1 : c ≠ 1)
    (hca : c ≠ a) (hcb : c ≠ b) (hcab : c ≠ a * b) (haa : a * a = 1) (hbb : b * b = 1)
    (hcc : c * c = 1) (hab' : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    False := by
  have inj1 : ∀ x : ↥K, x ≠ 1 → e x ≠ 1 := fun x hx h => hx (e.injective (h.trans (map_one e).symm))
  have sq1 : ∀ x : ↥K, x * x = 1 → e x * e x = 1 := fun x hx => by
    rw [← map_mul, hx, map_one]
  have com1 : ∀ x y : ↥K, x * y = y * x → e x * e y = e y * e x := fun x y hxy => by
    rw [← map_mul, ← map_mul, hxy]
  exact noE8S (inj1 a ha1) (inj1 b hb1) (fun h => hab (e.injective h)) (inj1 c hc1)
    (fun h => hca (e.injective h)) (fun h => hcb (e.injective h))
    (fun h => hcab (e.injective (by rw [map_mul]; exact h))) (sq1 a haa) (sq1 b hbb) (sq1 c hcc)
    (com1 a b hab') (com1 a c hac) (com1 b c hbc)

omit [Finite G] in
theorem conjugate_closure_pair (a b k : G) :
    CFSG.conjugate (Subgroup.closure ({a, b} : Set G)) k =
      Subgroup.closure ({k⁻¹ * a * k, k⁻¹ * b * k} : Set G) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_closure, Set.image_pair]
  simp

theorem e8Input_of
    (e : ↥K ≃* S3) (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3)
    {A : Subgroup G} (hA : IsAutPair K A) : E8Input K A := by
  have hidx : Idx2 K A := ⟨hA.1, hA.2.1⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hidx.le_normalizer
  have inj1 : ∀ x : ↥K, x ≠ 1 → e x ≠ 1 := fun x hx h => hx (e.injective (h.trans (map_one e).symm))
  have sq1 : ∀ x : ↥K, x * x = 1 → e x * e x = 1 := fun x hx => by
    rw [← map_mul, hx, map_one]
  have com1 : ∀ x y : ↥K, x * y = y * x → e x * e y = e y * e x := fun x y hxy => by
    rw [← map_mul, ← map_mul, hxy]
  have kdata : ∀ E : Subgroup G, E ≤ K → IsFourSubgroup E →
      ∃ a b : G, ∃ (ha : a ∈ K) (hb : b ∈ K), a ∈ E ∧ b ∈ E ∧ E = Subgroup.closure ({a, b} : Set G) ∧
        ∃ g : S3, g * u0S * g⁻¹ = e ⟨a, ha⟩ ∧ g * d2S * g⁻¹ = e ⟨b, hb⟩ := by
    intro E hEK hE
    obtain ⟨a, b, haE, hbE, ha1, hb1, hab, haa, hbb, hcomm, hEeq⟩ := exists_pair_of_four hE
    have haK : a ∈ K := hEK haE
    have hbK : b ∈ K := hEK hbE
    refine ⟨a, b, haK, hbK, haE, hbE, hEeq, kleinS ?_ ?_ ?_ ?_ ?_ ?_⟩
    · exact inj1 ⟨a, haK⟩ (fun h => ha1 (congrArg Subtype.val h))
    · exact inj1 ⟨b, hbK⟩ (fun h => hb1 (congrArg Subtype.val h))
    · exact fun h => hab (congrArg Subtype.val (e.injective h))
    · exact sq1 ⟨a, haK⟩ (Subtype.ext haa)
    · exact sq1 ⟨b, hbK⟩ (Subtype.ext hbb)
    · exact com1 ⟨a, haK⟩ ⟨b, hbK⟩ (Subtype.ext hcomm)
  refine ⟨hidx, ?_, ?_, ?_⟩
  ·
    intro F hFK hF
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, c, haF, hbF, hcF, ha1, hb1, hab, hc1, hca, hcb, hcab, haa, hbb, hcc, hab', hac,
      hbc⟩ := exists_triple hF hcon
    refine noE8K e (a := ⟨a, hFK haF⟩) (b := ⟨b, hFK hbF⟩) (c := ⟨c, hFK hcF⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun h => ha1 (congrArg Subtype.val h)
    · exact fun h => hb1 (congrArg Subtype.val h)
    · exact fun h => hab (congrArg Subtype.val h)
    · exact fun h => hc1 (congrArg Subtype.val h)
    · exact fun h => hca (congrArg Subtype.val h)
    · exact fun h => hcb (congrArg Subtype.val h)
    · exact fun h => hcab (congrArg Subtype.val h)
    · exact Subtype.ext haa
    · exact Subtype.ext hbb
    · exact Subtype.ext hcc
    · exact Subtype.ext hab'
    · exact Subtype.ext hac
    · exact Subtype.ext hbc
  ·
    intro E hEK hE
    obtain ⟨a, b, haK, hbK, haE, hbE, hEeq, g, hga, hgb⟩ := kdata E hEK hE
    refine ⟨?_, ?_⟩
    · intro x hx hcomm
      have hxa := hcomm a haE
      have hxb := hcomm b hbE
      have hxa' : e ⟨x, hx⟩ * e ⟨a, haK⟩ = e ⟨a, haK⟩ * e ⟨x, hx⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hxa)
      have hxb' : e ⟨x, hx⟩ * e ⟨b, hbK⟩ = e ⟨b, hbK⟩ * e ⟨x, hx⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hxb)
      rw [← hga] at hxa'
      rw [← hgb] at hxb'
      have h1 : (g⁻¹ * e ⟨x, hx⟩ * g) * u0S = u0S * (g⁻¹ * e ⟨x, hx⟩ * g) := by
        calc (g⁻¹ * e ⟨x, hx⟩ * g) * u0S
            = g⁻¹ * (e ⟨x, hx⟩ * (g * u0S * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * u0S * g⁻¹) * e ⟨x, hx⟩) * g := by rw [hxa']
          _ = u0S * (g⁻¹ * e ⟨x, hx⟩ * g) := by group
      have h2 : (g⁻¹ * e ⟨x, hx⟩ * g) * d2S = d2S * (g⁻¹ * e ⟨x, hx⟩ * g) := by
        calc (g⁻¹ * e ⟨x, hx⟩ * g) * d2S
            = g⁻¹ * (e ⟨x, hx⟩ * (g * d2S * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * d2S * g⁻¹) * e ⟨x, hx⟩) * g := by rw [hxb']
          _ = d2S * (g⁻¹ * e ⟨x, hx⟩ * g) := by group
      have hx'' : e ⟨x, hx⟩ = g * (g⁻¹ * e ⟨x, hx⟩ * g) * g⁻¹ := by group
      rcases centS h1 h2 with hc | hc | hc | hc
      · have : e ⟨x, hx⟩ = 1 := by rw [hx'', hc]; group
        have hx1 : x = 1 := congrArg Subtype.val (e.injective (this.trans (map_one e).symm))
        rw [hx1]
        exact E.one_mem
      · have : e ⟨x, hx⟩ = e ⟨a, haK⟩ := by rw [hx'', hc, hga]
        have hx1 : x = a := congrArg Subtype.val (e.injective this)
        rw [hx1]
        exact haE
      · have : e ⟨x, hx⟩ = e ⟨b, hbK⟩ := by rw [hx'', hc, hgb]
        have hx1 : x = b := congrArg Subtype.val (e.injective this)
        rw [hx1]
        exact hbE
      · have h5 : e ⟨x, hx⟩ = e ⟨a, haK⟩ * e ⟨b, hbK⟩ := by
          rw [hx'', hc, ← hga, ← hgb]
          group
        have hxab : (⟨x, hx⟩ : ↥K) = ⟨a, haK⟩ * ⟨b, hbK⟩ := by
          apply e.injective
          rw [map_mul]
          exact h5
        have hx1 : x = a * b := congrArg Subtype.val hxab
        rw [hx1]
        exact E.mul_mem haE hbE
    · obtain ⟨β, hββ, hβinner, hβa, hβb⟩ := kleinOuterS (a := e ⟨a, haK⟩) (b := e ⟨b, hbK⟩) ⟨g, hga, hgb⟩
      obtain ⟨f₀, hf₀⟩ := actA_surjective e hb hA hAN β
      have hfK : (f₀ : G) ∉ K := by
        intro hf
        apply hβinner (e ⟨(f₀ : G), hf⟩)
        rw [← hf₀, ← actA_of_mem e hA hAN hf]
      have hff : (f₀ : G) * f₀ = 1 := by
        have h1 : actA e hAN (f₀ * f₀) = actA e hAN 1 := by rw [map_mul, hf₀, hββ, map_one]
        have h2 := actA_injective e hA hAN h1
        exact congrArg Subtype.val h2
      have hfa : (f₀ : G) * a = a * f₀ := by
        have h1 : actA e hAN f₀ (e ⟨a, haK⟩) = e ⟨a, haK⟩ := by rw [hf₀]; exact hβa
        rw [actA_apply, actN_eq_iff, e.symm_apply_apply] at h1
        change (f₀ : G) * a * (f₀ : G)⁻¹ = a at h1
        calc (f₀ : G) * a = (f₀ * a * (f₀ : G)⁻¹) * f₀ := by group
          _ = a * f₀ := by rw [h1]
      have hfb : (f₀ : G) * b = b * f₀ := by
        have h1 : actA e hAN f₀ (e ⟨b, hbK⟩) = e ⟨b, hbK⟩ := by rw [hf₀]; exact hβb
        rw [actA_apply, actN_eq_iff, e.symm_apply_apply] at h1
        change (f₀ : G) * b * (f₀ : G)⁻¹ = b at h1
        calc (f₀ : G) * b = (f₀ * b * (f₀ : G)⁻¹) * f₀ := by group
          _ = b * f₀ := by rw [h1]
      refine ⟨f₀, f₀.2, hfK, hff, fun y hy => ?_⟩
      have hle : E ≤ Subgroup.centralizer ({(f₀ : G)} : Set G) := by
        rw [hEeq, Subgroup.closure_le]
        intro z hz
        rcases hz with rfl | hz
        · exact Subgroup.mem_centralizer_singleton_iff.2 hfa.symm
        · rw [Set.mem_singleton_iff.mp hz]
          exact Subgroup.mem_centralizer_singleton_iff.2 hfb.symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  ·
    intro E E' hEK hE hE'K hE'
    obtain ⟨a, b, haK, hbK, haE, hbE, hEeq, g, hga, hgb⟩ := kdata E hEK hE
    obtain ⟨a₂, b₂, ha₂K, hb₂K, ha₂E, hb₂E, hE'eq, g₂, hga₂, hgb₂⟩ := kdata E' hE'K hE'
    refine ⟨((e.symm (g * g₂⁻¹) : ↥K) : G), (e.symm (g * g₂⁻¹)).2, ?_⟩
    have hconj : ∀ (x y : G) (hx : x ∈ K) (hy : y ∈ K) (h1 : g * u0S * g⁻¹ = e ⟨x, hx⟩)
        (h2 : g₂ * u0S * g₂⁻¹ = e ⟨y, hy⟩), ((e.symm (g * g₂⁻¹) : ↥K) : G)⁻¹ * x *
          ((e.symm (g * g₂⁻¹) : ↥K) : G) = y := by
      intro x y hx hy h1 h2
      have h3 : (e.symm (g * g₂⁻¹))⁻¹ * ⟨x, hx⟩ * e.symm (g * g₂⁻¹) = ⟨y, hy⟩ := by
        apply e.injective
        simp only [map_mul, map_inv, e.apply_symm_apply]
        rw [← h1, ← h2]
        group
      exact congrArg Subtype.val h3
    have hconj' : ∀ (x y : G) (hx : x ∈ K) (hy : y ∈ K) (h1 : g * d2S * g⁻¹ = e ⟨x, hx⟩)
        (h2 : g₂ * d2S * g₂⁻¹ = e ⟨y, hy⟩), ((e.symm (g * g₂⁻¹) : ↥K) : G)⁻¹ * x *
          ((e.symm (g * g₂⁻¹) : ↥K) : G) = y := by
      intro x y hx hy h1 h2
      have h3 : (e.symm (g * g₂⁻¹))⁻¹ * ⟨x, hx⟩ * e.symm (g * g₂⁻¹) = ⟨y, hy⟩ := by
        apply e.injective
        simp only [map_mul, map_inv, e.apply_symm_apply]
        rw [← h1, ← h2]
        group
      exact congrArg Subtype.val h3
    rw [hEeq, hE'eq, conjugate_closure_pair, hconj a a₂ haK ha₂K hga hga₂,
      hconj' b b₂ hbK hb₂K hgb hgb₂]

end Model

theorem l33Facts_of_model
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : StatedClassicalModel ↥K .PSL 3 3 1) : L33Facts K := by
  obtain ⟨eK⟩ := psl33_equiv h
  let e : ↥K ≃* S3 := eK.trans psl33EquivS3
  have hbK := aut_card_le h
  have hb := aut_card_S3 e hbK
  exact ⟨hbK, inv_class_of e, z4_of e hb, fun A hA => outer_inv_of e hb hA,
    fun A hA F F' hFA hF'A hF hF8 hF' hF'8 =>
      (e8Input_of e hb hA).e8_conj hFA hF hF8 hF'A hF' hF'8,
    fun A hA E hEK hE => (e8Input_of e hb hA).e8_exists hEK hE⟩

end CFSG.QuasithinUnique.Unc25K1

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem l33AutFacts :
    L33AutFacts := by
  intro G _ _ K h
  exact Unc25K1.l33Facts_of_model h

end CFSG.QuasithinUnique
