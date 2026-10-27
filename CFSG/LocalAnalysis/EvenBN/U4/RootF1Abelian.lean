module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF1
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Factorization

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (exists_mem_inf_centralizer_mul_of_coprime
  mem_normalizer_inf mem_normalizer_sup)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem exists_conj_mul_inv_eq [Finite G] {X : Subgroup G} {i : G}
    (hi : i ∈ normalizer (X : Set G)) (hfpf : ∀ x ∈ X, i * x * i⁻¹ = x → x = 1) {z : G}
    (hz : z ∈ X) : ∃ z' ∈ X, i * z' * i⁻¹ * z'⁻¹ = z := by
  set ψ : X → X := fun z' =>
    ⟨i * z' * i⁻¹ * (z' : G)⁻¹, mul_mem ((mem_normalizer_iff.1 hi z').1 z'.2) (inv_mem z'.2)⟩
  have hinj : Function.Injective ψ := by
    intro z₁ z₂ e
    have e' : i * (z₁ : G) * i⁻¹ * (z₁ : G)⁻¹ = i * z₂ * i⁻¹ * (z₂ : G)⁻¹ := congrArg Subtype.val e
    have hw : (z₂ : G)⁻¹ * z₁ ∈ X := mul_mem (inv_mem z₂.2) z₁.2
    have h1 : i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (z₂ : G)⁻¹ * z₁ := by
      calc i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (i * z₂ * i⁻¹)⁻¹ * (i * z₁ * i⁻¹) := by group
        _ = (i * z₂ * i⁻¹)⁻¹ * (i * z₂ * i⁻¹ * (z₂ : G)⁻¹ * z₁) := by
            rw [show i * (z₁ : G) * i⁻¹ = i * z₁ * i⁻¹ * (z₁ : G)⁻¹ * z₁ by group, e']
        _ = (z₂ : G)⁻¹ * z₁ := by group
    have := hfpf _ hw h1
    exact Subtype.ext (by rw [← mul_left_cancel_iff (a := (z₂ : G)⁻¹), this, inv_mul_cancel])
  obtain ⟨z', hz'⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨z, hz⟩
  exact ⟨z', z'.2, congrArg Subtype.val hz'⟩

theorem mem_centralizer_sup_of_mem {J₁ J₂ : Subgroup G} {a : G}
    (h₁ : a ∈ centralizer (J₁ : Set G)) (h₂ : a ∈ centralizer (J₂ : Set G)) :
    a ∈ centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
  have key : J₁ ⊔ J₂ ≤ centralizer ({a} : Set G) := sup_le
    (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h₁ j hj))
    (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h₂ j hj))
  exact mem_centralizer_iff.2 fun j hj => mem_centralizer_singleton_iff.1 (key hj)

end Generic

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_norm_one_pow_four_ne_one : ∃ u : Kˣ, (u : K) * h.bar u = 1 ∧ (u : K) ^ 4 ≠ 1 := by
  have := h.finite
  set μ := (Units.map h.normHom).ker
  have hcard : Nat.card μ = 2 ^ f + 1 := h.card_ker_normUnits_and_surjective.1
  have hnt : Nontrivial μ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    have := Nat.one_le_two_pow (n := f)
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : μ)
  have hN : (u : K) * h.bar u = 1 := (UnitaryFieldData.mem_ker_normUnits h).1 hu
  refine ⟨u, hN, fun h4 => hu1 (Subtype.ext ?_)⟩
  have hcop : Nat.Coprime 4 (2 ^ f + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 ?_)
    exact (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
  have h4' : u ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h4, Units.val_one])
  have hq : u ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← h.bar_apply, mul_comm]
    exact hN
  have hd : orderOf u ∣ Nat.gcd 4 (2 ^ f + 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4') (orderOf_dvd_of_pow_eq_one hq)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem miyamotoXGL_mem_centralizer_I2pow_iff [CharP K 2] {b c d : K} :
    miyamotoXGL h 0 b c d ∈ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)) ↔ c = 0 := by
  have hpow : ∀ u : Kˣ, (u : K) * h.bar u = 1 → (u : K) ^ (2 ^ f - 1) = ((u : K) ^ 2)⁻¹ := by
    intro u hu
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    have hf1 := h.one_le
    have e : (u : K) ^ (2 ^ f - 1) * (u : K) = h.bar u := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h.bar_apply]
    apply eq_inv_of_mul_eq_one_left
    rw [sq, ← mul_assoc, e, mul_comm]
    exact hu
  constructor
  · intro hc
    obtain ⟨u, hu, hu4⟩ := exists_norm_one_pow_four_ne_one h
    have hmem : miyamotoI2Hom h u ∈ miyamotoI2pow h := (miyamotoI2Hom_mem_I2pow_iff h u).2 hu
    have e := (mem_centralizer_singleton_iff_conj).1 (centralizer_le
      (Set.singleton_subset_iff.2 hmem) hc)
    rw [miyamotoI2Hom_conj, miyamotoXGL_inj, hpow u hu, inv_inv] at e
    have hne : (u : K) ^ 2 * (u : K) ^ 2 ≠ 1 := by
      rw [← pow_add]
      exact hu4
    exact eq_zero_of_mul_eq_self hne e.2.2.1
  · rintro rfl
    refine mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨a, rfl⟩ := hg
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    refine (mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)).symm
    rw [miyamotoI2Hom_conj, miyamotoXGL_inj]
    have hN : ((a ^ (2 ^ f - 1) : Kˣ) : K) ^ 2 * h.bar (((a ^ (2 ^ f - 1) : Kˣ) : K) ^ 2) = 1 := by
      rw [map_pow, ← mul_pow, Units.val_pow_eq_pow_val, pow_sub_one_mul_bar h a.ne_zero, one_pow]
    refine ⟨by simp, rfl, by simp, by rw [hN, one_mul]⟩

theorem odd_card_miyamotoI : Odd (Nat.card (miyamotoI h)) := by
  have : Finite K := h.finite
  have hd : Nat.card (miyamotoI h) ∣ Nat.card (Kˣ × Kˣ) := by
    have h1 := Subgroup.card_map_dvd ((miyamotoIParam h).ker) (miyamotoIHom h)
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_prod, Nat.card_units, h.card] at hd
  refine Odd.of_dvd_nat ?_ hd
  have h1 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
  have h2 : Even (2 ^ (2 * f)) := (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩)
  exact (Nat.Even.sub_odd h1 h2 odd_one).mul (Nat.Even.sub_odd h1 h2 odd_one)

end ModelFacts

section ModelDecomp

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

omit [CharP K 2] in
theorem miyamotoA1_inf_centralizer_of_P {X R : Subgroup (GL (Fin 4) K)}
    (hPX : miyamotoP h ⊓ centralizer (X : Set (GL (Fin 4) K)) = R) (hR : R ≤ miyamotoA1 h) :
    miyamotoA1 h ⊓ centralizer (X : Set (GL (Fin 4) K)) = R := by
  refine le_antisymm (fun g hg => ?_) (le_inf hR fun g hg => ?_)
  · rw [← hPX]
    exact ⟨miyamotoA1_le_P h hg.1, hg.2⟩
  · rw [← hPX] at hg
    exact hg.2

theorem miyamotoA1_inf_centralizer_I1r2 (hf : 2 ≤ f) :
    miyamotoA1 h ⊓ centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K)) = miyamotoRootC h :=
  miyamotoA1_inf_centralizer_of_P h (miyamotoP_inf_centralizer_I1r2 h hf)
    ((miyamotoRootC_le_Z2 h).trans (miyamotoZ2_le_A1 h))

theorem miyamotoA1_inf_centralizer_I2 (hf : 2 ≤ f) :
    miyamotoA1 h ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) = miyamotoRootB h :=
  miyamotoA1_inf_centralizer_of_P h (miyamotoP_inf_centralizer_I2 h hf) (miyamotoRootB_le_A1 h)

theorem miyamotoA1_inf_centralizer_I2r1 (hf : 2 ≤ f) :
    miyamotoA1 h ⊓ centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) = miyamotoZ h :=
  miyamotoA1_inf_centralizer_of_P h (miyamotoP_inf_centralizer_I2r1 h hf)
    ((miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A1 h))

theorem miyamotoA1_decomp_one (hf : 2 ≤ f) {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h) :
    ∃ u ∈ miyamotoA1 h ⊓ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)),
      ∃ v ∈ miyamotoA1 h ⊓ centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K)), g = u * v := by
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hg
  refine ⟨miyamotoXGL h 0 b 0 d, ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩,
    (miyamotoXGL_mem_centralizer_I2pow_iff h).2 rfl⟩, miyamotoXGL h 0 0 c 0, ?_, ?_⟩
  · rw [miyamotoA1_inf_centralizer_I1r2 h hf]
    exact ⟨c, rfl⟩
  · rw [miyamotoXGL_mul_A1 h hb, add_zero, zero_add, add_zero]

theorem miyamotoA1_disj_one (hf : 2 ≤ f) {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h)
    (h₁ : g ∈ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)))
    (h₂ : g ∈ centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K))) : g = 1 := by
  have hC : g ∈ miyamotoRootC h := by
    rw [← miyamotoA1_inf_centralizer_I1r2 h hf]
    exact ⟨hg, h₂⟩
  obtain ⟨c, rfl⟩ := hC
  rw [(miyamotoXGL_mem_centralizer_I2pow_iff h).1 h₁, miyamotoXGL_zero]

theorem miyamotoA1_decomp_two (hf : 2 ≤ f) {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h)
    (hgJ : g ∈ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K))) :
    ∃ u ∈ miyamotoA1 h ⊓ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)) ⊓
        centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)),
      ∃ v ∈ miyamotoA1 h ⊓ centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)) ⊓
        centralizer (miyamotoI2 h : Set (GL (Fin 4) K)), g = u * v := by
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hg
  obtain rfl := (miyamotoXGL_mem_centralizer_I2pow_iff h).1 hgJ
  have hZ : miyamotoXGL h 0 0 0 d ∈ miyamotoA1 h ⊓
      centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) := by
    rw [miyamotoA1_inf_centralizer_I2r1 h hf]
    exact ⟨d, hd, rfl⟩
  have hB : miyamotoXGL h 0 b 0 0 ∈ miyamotoA1 h ⊓
      centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) := by
    rw [miyamotoA1_inf_centralizer_I2 h hf]
    exact ⟨b, hb, rfl⟩
  refine ⟨miyamotoXGL h 0 0 0 d, ⟨⟨hZ.1, (miyamotoXGL_mem_centralizer_I2pow_iff h).2 rfl⟩, hZ.2⟩,
    miyamotoXGL h 0 b 0 0, ⟨⟨hB.1, (miyamotoXGL_mem_centralizer_I2pow_iff h).2 rfl⟩, hB.2⟩, ?_⟩
  rw [miyamotoXGL_mul_A1 h (map_zero _), zero_add, add_zero, add_zero]

theorem miyamotoA1_disj_two (hf : 2 ≤ f) {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h)
    (h₁ : g ∈ centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)))
    (h₂ : g ∈ centralizer (miyamotoI2 h : Set (GL (Fin 4) K))) : g = 1 := by
  have hZ : g ∈ miyamotoZ h := by
    rw [← miyamotoA1_inf_centralizer_I2r1 h hf]
    exact ⟨hg, h₁⟩
  have hB : g ∈ miyamotoRootB h := by
    rw [← miyamotoA1_inf_centralizer_I2 h hf]
    exact ⟨hg, h₂⟩
  obtain ⟨d, -, rfl⟩ := hZ
  obtain ⟨b, -, e⟩ := hB
  rw [miyamotoXGL_inj] at e
  rw [e.2.2.2, miyamotoXGL_zero]

theorem exists_I1_conj_Z {d d' : K} (hd : h.bar d = d) (hd' : h.bar d' = d') (hd0 : d ≠ 0)
    (hd'0 : d' ≠ 0) : ∃ t : Kˣ, h.bar t = t ∧
      (miyamotoIHom h (t, t))⁻¹ * miyamotoXGL h 0 0 0 d * miyamotoIHom h (t, t) =
        miyamotoXGL h 0 0 0 d' := by
  have : Finite K := h.finite
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (d' / d)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim hd'0 hd0
  have hbr : h.bar r = r := by
    have e : h.bar r * h.bar r = r * r := by rw [← map_mul, ← hr, map_div₀, hd, hd']
    have : (h.bar r - r) * (h.bar r - r) = 0 := by
      linear_combination e + (r * r - h.bar r * r) * (CharTwo.two_eq_zero (R := K))
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  refine ⟨Units.mk0 r hr0, hbr, ?_⟩
  rw [miyamotoI1_conj h hbr, miyamotoXGL_inj]
  refine ⟨rfl, by simp, by simp, ?_⟩
  simp only [Units.val_mk0]
  rw [sq, ← hr]
  field_simp

theorem four_points {ω : K} (hω : ω + h.bar ω = 1) :
    miyamotoXGL h 0 1 0 (0 * h.bar 0) * miyamotoXGL h 0 1 ω (ω * h.bar ω) *
      miyamotoXGL h 0 1 1 (1 * h.bar 1) *
      miyamotoXGL h 0 1 (ω + 1) ((ω + 1) * h.bar (ω + 1)) = miyamotoXGL h 0 0 0 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [miyamotoXGL_mul_A1 h (map_one _), miyamotoXGL_mul_A1 h (by simp [map_add]),
    miyamotoXGL_mul_A1 h (by simp [map_add]), miyamotoXGL_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · linear_combination (2 : K) * h2
  · linear_combination (ω + 1) * h2
  · simp only [map_add, map_one, map_zero, mul_zero, zero_add, mul_one]
    linear_combination hω + (ω * h.bar ω + 1) * h2

theorem point_mem_A1 (p : K) : miyamotoXGL h 0 1 p (p * h.bar p) ∈ miyamotoA1 h ∧
    miyamotoXGL h 0 1 p (p * h.bar p) ≠ 1 ∧
    miyamotoQA1 h (miyamotoXGL h 0 1 p (p * h.bar p)) = 0 ∧
    miyamotoXGL h 0 1 p (p * h.bar p) ∉ miyamotoZ h := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, map_one _, by rw [map_mul, h.bar_bar, mul_comm]⟩,
    fun e => ?_, ?_, ?_⟩
  · rw [← miyamotoXGL_zero h, miyamotoXGL_inj] at e
    exact one_ne_zero e.2.1
  · rw [miyamotoQA1_miyamotoXGL]
    linear_combination (p * h.bar p) * h2
  · rintro ⟨d, -, e⟩
    rw [miyamotoXGL_inj] at e
    exact one_ne_zero e.2.1

end ModelDecomp

section PullDecomp

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem exists_mul_of_mem_miyamotoPull_of_forall {M X Y : Subgroup (GL (Fin 4) K)}
    (hX : X ≤ gramSU h (miyamotoJ4 K)) (hY : Y ≤ gramSU h (miyamotoJ4 K))
    (hdec : ∀ g ∈ M, ∃ x ∈ X, ∃ y ∈ Y, g = x * y) {a : G} (ha : a ∈ miyamotoPull h L η M) :
    ∃ x ∈ miyamotoPull h L η X, ∃ y ∈ miyamotoPull h L η Y, a = x * y := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  obtain ⟨x, hx, y, hy, e⟩ := hdec _ hg
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨x, hX hx⟩)).2 hx, _,
    (symm_mem_miyamotoPull_iff h L η (g := ⟨y, hY hy⟩)).2 hy, ?_⟩
  rw [← coe_mul, ← map_mul]
  have : g = ⟨x, hX hx⟩ * ⟨y, hY hy⟩ := Subtype.ext e
  rw [this]

theorem eq_one_of_mem_miyamotoPull_of_forall {M : Subgroup (GL (Fin 4) K)}
    (hM : ∀ g ∈ M, g = 1) {a : G} (ha : a ∈ miyamotoPull h L η M) : a = 1 := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have : g = 1 := Subtype.ext (hM _ hg)
  rw [this, map_one, coe_one]

end PullDecomp

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem IG_comm (_hS : Setting h L η t Q T) {x y : G} (hx : x ∈ miyamotoIG h L η)
    (hy : y ∈ miyamotoIG h L η) : x * y = y * x := by
  refine (commute_miyamotoPull_iff h L η (miyamotoI_le_gramSU h)).2 ?_ x hx y hy
  rintro _ ⟨p, -, rfl⟩ _ ⟨p', -, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem odd_card_of_le_IG (_hS : Setting h L η t Q T) {J : Subgroup G}
    (hJ : J ≤ miyamotoIG h L η) : Odd (Nat.card J) := by
  have h1 : Nat.card (miyamotoIG h L η) = Nat.card (miyamotoI h) :=
    card_miyamotoPull h L η (miyamotoI_le_gramSU h)
  exact Odd.of_dvd_nat (h1 ▸ odd_card_miyamotoI h) (Subgroup.card_dvd_of_le hJ)

theorem IG_le_normalizer_A1 (_hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoA1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have : x ∈ L ⊓ normalizer (miyamotoA1G h L η : Set G) := by
    rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h true false)]
    exact miyamotoPull_mono h L η (le_inf (miyamotoI_le_gramSU h)
      (miyamotoI_le_normalizer_unipotent h true false)) hx
  exact this.2

theorem IG_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoB1 h L η t : Set G) := fun _ hx =>
  mem_normalizer_sup (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1
    (hS.IG_le_C hx))) (hS.IG_le_normalizer_A1 hx)

theorem IG_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.IG_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1

theorem IG_le_normalizer_centralizer (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJ : J ≤ miyamotoIG h L η) :
    miyamotoIG h L η ≤ normalizer (centralizer (J : Set G) : Set G) := fun x hx =>
  mem_normalizer_fintype fun y hy => mem_centralizer_iff.2 fun k hk => by
    have hkx : Commute k x := hS.IG_comm (hJ hk) hx
    have hky : Commute k y := mem_centralizer_iff.1 hy k hk
    exact ((hkx.mul_right hky).mul_right hkx.inv_right).eq

theorem le_normalizer_of_le_IG (hS : Setting h L η t Q T) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ≤ miyamotoIG h L η) (h₂ : J₂ ≤ miyamotoIG h L η) :
    J₁ ≤ normalizer (J₂ : Set G) := fun x hx => mem_normalizer_fintype fun y hy => by
  rw [hS.IG_comm (h₁ hx) (h₂ hy), mul_inv_cancel_right]
  exact hy

theorem isPGroup_F1 (hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoF1G h L η t) :=
  hS.isPGroup_D1.to_le hS.F1_le_D1

theorem crossed_mem_centralizer (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJ : J ≤ miyamotoIG h L η) {e : G} (he : e ∈ centralizer (J : Set G)) :
    e⁻¹ * t * e * t ∈ centralizer (J : Set G) := mem_centralizer_iff.2 fun k hk => by
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.1 (hS.IG_le_C (hJ hk))
  have hke : k * e * k⁻¹ = e := by
    rw [mem_centralizer_iff.1 he k hk, mul_inv_cancel_right]
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := e) hkt
  rw [hke] at h1
  calc k * (e⁻¹ * t * e * t) = k * (e⁻¹ * t * e * t) * k⁻¹ * k := by group
    _ = e⁻¹ * t * e * t * k := by rw [← h1]

theorem exists_F1_centralizer_crossed_eq (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJ : J ≤ miyamotoIG h L η) {a : G} (ha : a ∈ miyamotoA1G h L η)
    (haJ : a ∈ centralizer (J : Set G)) :
    ∃ e ∈ miyamotoF1G h L η t, e ∈ centralizer (J : Set G) ∧ e⁻¹ * t * e * t = a := by
  obtain ⟨e, he, hea⟩ := hS.exists_F1_crossed_eq ha
  have hJF : J ≤ normalizer (miyamotoF1G h L η t : Set G) := hJ.trans hS.IG_le_normalizer_F1
  have hJA : J ≤ normalizer (miyamotoA1G h L η : Set G) := hJ.trans hS.IG_le_normalizer_A1
  have hFA : miyamotoF1G h L η t ≤ normalizer (miyamotoA1G h L η : Set G) := fun x hx =>
    hS.normalizer_B1_le_normalizer_A1 (hS.D1_le_normalizer_B1 (hS.F1_le_D1 hx))
  have hsolv : Group.IsSolvable (miyamotoF1G h L η t) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hS.isPGroup_F1.isNilpotent
    infer_instance
  have hcop := coprime_of_odd_of_isPGroup (hS.odd_card_of_le_IG hJ) hS.isPGroup_F1
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hS.A1_le_F1 hFA hJF
    hJA hsolv hcop he fun s hs => by
      have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (hS.IG_le_C (hJ hs))
      have hsF : s * e * s⁻¹ ∈ miyamotoF1G h L η t := (mem_normalizer_iff.1 (hJF hs) e).1 he
      refine (hS.crossed_eq_one_iff_F1 (mul_mem (inv_mem he) hsF)).1 ?_
      have h1 := hS.crossed_mul_D1 (inv_mem (hS.F1_le_D1 he)) (hS.F1_le_D1 hsF)
      have h2 := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := e) hst
      rw [h1, h2, hS.crossed_inv_D1 (hS.F1_le_D1 he), hea,
        show s * a * s⁻¹ = a by rw [mem_centralizer_iff.1 haJ s hs, mul_inv_cancel_right],
        inv_mul_cancel]
  refine ⟨c, hc.1, hc.2, ?_⟩
  have h1 := hS.crossed_mul_D1 (hS.F1_le_D1 hc.1) (hS.A1_le_D1 hn)
  rw [(hS.crossed_eq_one_iff_F1 (hS.A1_le_F1 hn)).2 hn, mul_one] at h1
  rw [← hea, h1]

theorem gomi_F1 (hS : Setting h L η t Q T) {J₀ J₁ J₂ : Subgroup G}
    (h₀ : J₀ ≤ miyamotoIG h L η) (h₁ : J₁ ≤ miyamotoIG h L η) (h₂ : J₂ ≤ miyamotoIG h L η)
    (hdec : ∀ a ∈ miyamotoA1G h L η, a ∈ centralizer (J₀ : Set G) →
      ∃ u ∈ miyamotoA1G h L η, u ∈ centralizer (J₀ : Set G) ∧ u ∈ centralizer (J₁ : Set G) ∧
        ∃ v ∈ miyamotoA1G h L η, v ∈ centralizer (J₀ : Set G) ∧ v ∈ centralizer (J₂ : Set G) ∧
          a = u * v)
    (hdisj : ∀ a ∈ miyamotoA1G h L η, a ∈ centralizer (J₁ : Set G) →
      a ∈ centralizer (J₂ : Set G) → a = 1) :
    (∀ x ∈ miyamotoF1G h L η t ⊓ centralizer (J₀ : Set G) ⊓ centralizer (J₁ : Set G),
      ∀ y ∈ miyamotoF1G h L η t ⊓ centralizer (J₀ : Set G) ⊓ centralizer (J₂ : Set G),
        x * y = y * x) ∧
    (∀ e ∈ miyamotoF1G h L η t, e ∈ centralizer (J₀ : Set G) →
      ∃ x ∈ miyamotoF1G h L η t ⊓ centralizer (J₀ : Set G) ⊓ centralizer (J₁ : Set G),
        ∃ y ∈ miyamotoF1G h L η t ⊓ centralizer (J₀ : Set G) ⊓ centralizer (J₂ : Set G),
          e = x * y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := miyamotoF1G h L η t ⊓ centralizer (J₀ : Set G) with hAdef
  have hJIG : J₁ ⊔ J₂ ≤ miyamotoIG h L η := sup_le h₁ h₂
  have hAc : ∀ x ∈ miyamotoA1G h L η, ∀ y ∈ miyamotoD1 h L η t, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hy) x hx)
  have hprod : ∀ e ∈ miyamotoF1G h L η t, e ∈ centralizer (J₀ : Set G) →
      ∃ x ∈ A ⊓ centralizer (J₁ : Set G), ∃ y ∈ A ⊓ centralizer (J₂ : Set G), e = x * y := by
    intro e he heJ
    have hδ := hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 he)
    obtain ⟨u, hu, hu0, hu1, v, hv, hv0, hv2, huv⟩ :=
      hdec _ hδ (hS.crossed_mem_centralizer h₀ heJ)
    obtain ⟨x₀, hx₀, hx₀J, hx₀u⟩ := hS.exists_F1_centralizer_crossed_eq (sup_le h₀ h₁) hu
      (mem_centralizer_sup_of_mem hu0 hu1)
    obtain ⟨y₀, hy₀, hy₀J, hy₀v⟩ := hS.exists_F1_centralizer_crossed_eq (sup_le h₀ h₂) hv
      (mem_centralizer_sup_of_mem hv0 hv2)
    have hx₀0 := centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left : J₀ ≤ J₀ ⊔ J₁)) hx₀J
    have hx₀1 := centralizer_le (SetLike.coe_subset_coe.2 (le_sup_right : J₁ ≤ J₀ ⊔ J₁)) hx₀J
    have hy₀0 := centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left : J₀ ≤ J₀ ⊔ J₂)) hy₀J
    have hy₀2 := centralizer_le (SetLike.coe_subset_coe.2 (le_sup_right : J₂ ≤ J₀ ⊔ J₂)) hy₀J
    have hxyD : x₀ * y₀ ∈ miyamotoD1 h L η t := hS.F1_le_D1 (mul_mem hx₀ hy₀)
    set w := (x₀ * y₀)⁻¹ * e with hw
    have hwF : w ∈ miyamotoF1G h L η t := mul_mem (inv_mem (mul_mem hx₀ hy₀)) he
    have hwA : w ∈ miyamotoA1G h L η := by
      refine (hS.crossed_eq_one_iff_F1 hwF).1 ?_
      rw [hw, hS.crossed_mul_D1 (inv_mem hxyD) (hS.F1_le_D1 he), hS.crossed_inv_D1 hxyD,
        hS.crossed_mul_D1 (hS.F1_le_D1 hx₀) (hS.F1_le_D1 hy₀), hx₀u, hy₀v, ← huv,
        inv_mul_cancel]
    have hwJ : w ∈ centralizer (J₀ : Set G) :=
      mul_mem (inv_mem (mul_mem hx₀0 hy₀0)) heJ
    obtain ⟨u', hu', hu'0, hu'1, v', hv', hv'0, hv'2, hw'⟩ := hdec w hwA hwJ
    refine ⟨x₀ * u', ⟨⟨mul_mem hx₀ (hS.A1_le_F1 hu'), mul_mem hx₀0 hu'0⟩, mul_mem hx₀1 hu'1⟩,
      y₀ * v', ⟨⟨mul_mem hy₀ (hS.A1_le_F1 hv'), mul_mem hy₀0 hv'0⟩, mul_mem hy₀2 hv'2⟩, ?_⟩
    have e1 : e = x₀ * y₀ * w := by rw [hw]; group
    rw [e1, hw', ← mul_assoc, mul_assoc x₀ y₀ u', ← hAc u' hu' y₀ (hS.F1_le_D1 hy₀)]
    group
  have hinf : (A ⊓ centralizer (J₁ : Set G)) ⊓ (A ⊓ centralizer (J₂ : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun e he => ?_
    obtain ⟨⟨⟨heF, heJ0⟩, heJ1⟩, ⟨-, heJ2⟩⟩ := he
    have hδ := hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 heF)
    have h1 := hdisj _ hδ (hS.crossed_mem_centralizer h₁ heJ1) (hS.crossed_mem_centralizer h₂ heJ2)
    have heA := (hS.crossed_eq_one_iff_F1 heF).1 h1
    exact (mem_bot).2 (hdisj e heA heJ1 heJ2)
  have hcomm := gomi_commute_conj (p := 2) (A := A) (J₁ := J₁) (J₂ := J₂)
    (hS.isPGroup_F1.to_le inf_le_left)
    (fun hd => Nat.not_even_iff_odd.2 (hS.odd_card_of_le_IG hJIG) (even_iff_two_dvd.2 hd))
    (fun j hj => mem_normalizer_inf (hS.IG_le_normalizer_F1 (hJIG hj))
      (hS.IG_le_normalizer_centralizer h₀ (hJIG hj)))
    (hS.le_normalizer_of_le_IG h₁ h₂) (hS.le_normalizer_of_le_IG h₂ h₁)
    (fun a ha => hprod a ha.1 ha.2) hinf
  exact ⟨hcomm, hprod⟩

omit [Finite G] in
theorem mem_centralizer_bot (x : G) : x ∈ centralizer ((⊥ : Subgroup G) : Set G) :=
  mem_centralizer_iff.2 fun g hg => by rw [mem_bot.1 hg, one_mul, mul_one]

theorem tori_le_IG (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoI2pow h) ≤ miyamotoIG h L η ∧
      miyamotoPull h L η (miyamotoI1r2 h) ≤ miyamotoIG h L η ∧
      miyamotoI2r1G h L η ≤ miyamotoIG h L η ∧ miyamotoI2G h L η ≤ miyamotoIG h L η :=
  ⟨miyamotoPull_mono h L η ((miyamotoI2pow_le_I2 h).trans (miyamotoI2_le_I h)),
    miyamotoPull_mono h L η (miyamotoI1r2_le_I h), miyamotoPull_mono h L η (miyamotoI2r1_le_I h),
    miyamotoPull_mono h L η (miyamotoI2_le_I h)⟩

theorem le_SU_facts (_hS : Setting h L η t Q T) :
    miyamotoI2pow h ≤ gramSU h (miyamotoJ4 K) ∧ miyamotoI1r2 h ≤ gramSU h (miyamotoJ4 K) ∧
      miyamotoI2r1 h ≤ gramSU h (miyamotoJ4 K) ∧ miyamotoI2 h ≤ gramSU h (miyamotoJ4 K) ∧
      miyamotoA1 h ≤ gramSU h (miyamotoJ4 K) :=
  ⟨(miyamotoI2pow_le_I2 h).trans (miyamotoI2_le_SU h),
    (miyamotoI1r2_le_I h).trans (miyamotoI_le_gramSU h),
    (miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h), miyamotoI2_le_SU h,
    miyamotoUnipotent_le_SU h true false⟩

theorem A1G_decomp_one (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η) :
    ∃ u ∈ miyamotoA1G h L η, u ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ∧
      ∃ v ∈ miyamotoA1G h L η, v ∈ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) ∧
        a = u * v := by
  have : CharP K 2 := h.charP
  obtain ⟨hpow, hr2, -, -, hA⟩ := hS.le_SU_facts
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_miyamotoPull_of_forall h L η
    (inf_le_left.trans hA) (inf_le_left.trans hA) (fun g hg => miyamotoA1_decomp_one h hS.two_le hg)
    ha
  rw [miyamotoPull_inf_centralizer h L η _ hpow] at hu
  rw [miyamotoPull_inf_centralizer h L η _ hr2] at hv
  exact ⟨u, hu.1, hu.2, v, hv.1, hv.2, rfl⟩

theorem A1G_disj_one (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η)
    (h₁ : a ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G))
    (h₂ : a ∈ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G)) : a = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨hpow, hr2, -, -, -⟩ := hS.le_SU_facts
  have hmem : a ∈ miyamotoPull h L η (miyamotoA1 h ⊓
      centralizer (miyamotoI2pow h : Set (GL (Fin 4) K)) ⊓
      centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K))) := by
    rw [miyamotoPull_inf_centralizer h L η _ hr2, miyamotoPull_inf_centralizer h L η _ hpow]
    exact ⟨⟨ha, h₁⟩, h₂⟩
  exact eq_one_of_mem_miyamotoPull_of_forall h L η
    (fun g hg => miyamotoA1_disj_one h hS.two_le (mem_inf.1 (mem_inf.1 hg).1).1
      (mem_inf.1 (mem_inf.1 hg).1).2 (mem_inf.1 hg).2) hmem

theorem A1G_decomp_two (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η)
    (haJ : a ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G)) :
    ∃ u ∈ miyamotoA1G h L η, u ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ∧
      u ∈ centralizer (miyamotoI2r1G h L η : Set G) ∧
      ∃ v ∈ miyamotoA1G h L η, v ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ∧
        v ∈ centralizer (miyamotoI2G h L η : Set G) ∧ a = u * v := by
  have : CharP K 2 := h.charP
  obtain ⟨hpow, -, hr1, hI2, hA⟩ := hS.le_SU_facts
  have ha' : a ∈ miyamotoPull h L η (miyamotoA1 h ⊓
      centralizer (miyamotoI2pow h : Set (GL (Fin 4) K))) := by
    rw [miyamotoPull_inf_centralizer h L η _ hpow]
    exact ⟨ha, haJ⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_miyamotoPull_of_forall h L η
    (inf_le_left.trans (inf_le_left.trans hA)) (inf_le_left.trans (inf_le_left.trans hA))
    (fun g hg => miyamotoA1_decomp_two h hS.two_le (mem_inf.1 hg).1 (mem_inf.1 hg).2) ha'
  rw [miyamotoPull_inf_centralizer h L η _ hr1, miyamotoPull_inf_centralizer h L η _ hpow] at hu
  rw [miyamotoPull_inf_centralizer h L η _ hI2, miyamotoPull_inf_centralizer h L η _ hpow] at hv
  exact ⟨u, hu.1.1, hu.1.2, hu.2, v, hv.1.1, hv.1.2, hv.2, rfl⟩

theorem A1G_disj_two (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η)
    (h₁ : a ∈ centralizer (miyamotoI2r1G h L η : Set G))
    (h₂ : a ∈ centralizer (miyamotoI2G h L η : Set G)) : a = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨-, -, hr1, hI2, -⟩ := hS.le_SU_facts
  have hmem : a ∈ miyamotoPull h L η (miyamotoA1 h ⊓
      centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) ⊓
      centralizer (miyamotoI2 h : Set (GL (Fin 4) K))) := by
    rw [miyamotoPull_inf_centralizer h L η _ hI2, miyamotoPull_inf_centralizer h L η _ hr1]
    exact ⟨⟨ha, h₁⟩, h₂⟩
  exact eq_one_of_mem_miyamotoPull_of_forall h L η
    (fun g hg => miyamotoA1_disj_two h hS.two_le (mem_inf.1 (mem_inf.1 hg).1).1
      (mem_inf.1 (mem_inf.1 hg).1).2 (mem_inf.1 hg).2) hmem

theorem A1G_inf_centralizer_S (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ⊓ centralizer (miyamotoI2r1G h L η : Set G) = miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨-, -, hr1, -, -⟩ := hS.le_SU_facts
  rw [← miyamotoPull_inf_centralizer h L η _ hr1, miyamotoA1_inf_centralizer_I2r1 h hS.two_le]

theorem ZP_le_centralizer_I2pow (hS : Setting h L η t Q T) :
    miyamotoZG h L η ≤ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) := by
  have : CharP K 2 := h.charP
  obtain ⟨hpow, -, -, -, hA⟩ := hS.le_SU_facts
  intro z hz
  have : z ∈ miyamotoPull h L η (miyamotoA1 h ⊓
      centralizer (miyamotoI2pow h : Set (GL (Fin 4) K))) := by
    refine miyamotoPull_mono h L η (fun g hg => ?_) hz
    obtain ⟨d, hd, rfl⟩ := hg
    exact ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩,
      (miyamotoXGL_mem_centralizer_I2pow_iff h).2 rfl⟩
  rw [miyamotoPull_inf_centralizer h L η _ hpow] at this
  exact this.2

theorem E_le_D1 (hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoD1 h L η t := by
  rw [hS.D1_eq]
  exact le_inf (hS.E_le_Y.trans (hS.Y_le_M.trans hS.M_le_normalizer_B1))
    (hS.E_le_centralizer_P.trans (centralizer_le (SetLike.coe_subset_coe.2
      (miyamotoPull_mono h L η (miyamotoA1_le_P h)))))

theorem IG_le_normalizer_E (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoEG h L η Q : Set G) :=
  hS.IG_le_H.trans hS.H_le_normalizer_E

theorem crossed_eq_one_iff_E (hS : Setting h L η t Q T) {e : G}
    (he : e ∈ miyamotoEG h L η Q) : e⁻¹ * t * e * t = 1 ↔ e ∈ miyamotoZG h L η :=
  hS.sec3_3.2.2.2.2.2.2.1 e he

theorem E_le_F1 (hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoF1G h L η t := by
  intro e he
  obtain ⟨i, hi, hfpf⟩ := hS.exists_I1_fpf_A1
  have hiI : i ∈ miyamotoIG h L η := miyamotoPull_mono h L η (miyamotoI1_le_I h) hi
  have hiZ : i ∈ normalizer (miyamotoZG h L η : Set G) := hS.H_le_normalizer_ZP (hS.IG_le_H hiI)
  have hδ : e⁻¹ * t * e * t ∈ miyamotoZG h L η := hS.sec3_3.2.2.2.2.2.1 e he
  obtain ⟨z', hz', hz'e⟩ := exists_conj_mul_inv_eq hiZ
    (fun x hx => hfpf x (hS.ZP_le_A1 hx)) hδ
  obtain ⟨e', he', he'z⟩ := hS.exists_E_crossed_eq hz'
  have hiE := hS.IG_le_normalizer_E hiI
  have hw : i * e' * i⁻¹ * e'⁻¹ ∈ miyamotoEG h L η Q :=
    mul_mem ((mem_normalizer_iff.1 hiE e').1 he') (inv_mem he')
  have he'D := hS.E_le_D1 he'
  have hieD : i * e' * i⁻¹ ∈ miyamotoD1 h L η t := hS.E_le_D1 ((mem_normalizer_iff.1 hiE e').1 he')
  have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.IG_le_C hiI)
  have hwδ : (i * e' * i⁻¹ * e'⁻¹)⁻¹ * t * (i * e' * i⁻¹ * e'⁻¹) * t = e⁻¹ * t * e * t := by
    rw [hS.crossed_mul_D1 hieD (inv_mem he'D),
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := e') hit, hS.crossed_inv_D1 he'D,
      he'z, hz'e]
  have hrest : e * (i * e' * i⁻¹ * e'⁻¹)⁻¹ ∈ miyamotoZG h L η := by
    refine (hS.crossed_eq_one_iff_E (mul_mem he (inv_mem hw))).1 ?_
    have hwD := hS.E_le_D1 hw
    rw [hS.crossed_mul_D1 (hS.E_le_D1 he) (inv_mem hwD), hS.crossed_inv_D1 hwD, hwδ,
      mul_inv_cancel]
  rw [show e = (e * (i * e' * i⁻¹ * e'⁻¹)⁻¹) * (i * e' * i⁻¹ * e'⁻¹) by group]
  exact mul_mem (hS.A1_le_F1 (hS.ZP_le_A1 hrest)) (hS.commutator_mem_F1 hi he'D)

theorem E_le_centralizer_S (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ centralizer (miyamotoI2r1G h L η : Set G) := fun e he => by
  have := hS.E_le_Y he
  rw [hS.Y_eq_Y0] at this
  exact this.2

theorem E_le_centralizer_I2pow (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  obtain ⟨hJI, -, -, -⟩ := hS.tori_le_IG
  set J := miyamotoPull h L η (miyamotoI2pow h)
  have hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G) := hJI.trans hS.IG_le_normalizer_E
  have hJZ : J ≤ normalizer (miyamotoZG h L η : Set G) :=
    hJI.trans (hS.IG_le_H.trans hS.H_le_normalizer_ZP)
  have hEZ : miyamotoEG h L η Q ≤ normalizer (miyamotoZG h L η : Set G) := fun e he => by
    have hc := centralizer_le (SetLike.coe_subset_coe.2
      (miyamotoPull_mono h L η (miyamotoZ_le_P h))) (hS.E_le_centralizer_P he)
    exact mem_normalizer_fintype fun z hz => by
      rw [← mem_centralizer_iff.1 hc z hz, mul_inv_cancel_right]
      exact hz
  have hE2 : IsPGroup 2 (miyamotoEG h L η Q) := hS.isPGroup_D1.to_le hS.E_le_D1
  have hsolv : Group.IsSolvable (miyamotoEG h L η Q) := by
    have := hE2.isNilpotent
    infer_instance
  intro e he
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hS.ZP_le_E hEZ hJE hJZ
    hsolv (coprime_of_odd_of_isPGroup (hS.odd_card_of_le_IG hJI) hE2) he fun j hj => by
      have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (hS.IG_le_C (hJI hj))
      have hjeE : j * e * j⁻¹ ∈ miyamotoEG h L η Q := (mem_normalizer_iff.1 (hJE hj) e).1 he
      refine (hS.crossed_eq_one_iff_E (mul_mem (inv_mem he) hjeE)).1 ?_
      have heD := hS.E_le_D1 he
      have hδ : e⁻¹ * t * e * t ∈ miyamotoZG h L η := hS.sec3_3.2.2.2.2.2.1 e he
      rw [hS.crossed_mul_D1 (inv_mem heD) (hS.E_le_D1 hjeE), hS.crossed_inv_D1 heD,
        CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := e) hjt,
        show j * (e⁻¹ * t * e * t) * j⁻¹ = e⁻¹ * t * e * t by
          rw [mem_centralizer_iff.1 (hS.ZP_le_centralizer_I2pow hδ) j hj, mul_inv_cancel_right],
        inv_mul_cancel]
  exact mul_mem hc.2 (hS.ZP_le_centralizer_I2pow hn)

theorem E_eq_F1_inf_centralizer_S (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q = miyamotoF1G h L η t ⊓ centralizer (miyamotoI2r1G h L η : Set G) := by
  refine le_antisymm (le_inf hS.E_le_F1 hS.E_le_centralizer_S) fun f hf => ?_
  obtain ⟨hfF, hfS⟩ := mem_inf.1 hf
  have hδ : f⁻¹ * t * f * t ∈ miyamotoZG h L η := by
    rw [← hS.A1G_inf_centralizer_S]
    exact ⟨hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hfF),
      hS.crossed_mem_centralizer hS.tori_le_IG.2.2.1 hfS⟩
  obtain ⟨e, he, hef⟩ := hS.exists_E_crossed_eq hδ
  have heF := hS.E_le_F1 he
  have hw : e⁻¹ * f ∈ miyamotoA1G h L η := by
    refine (hS.crossed_eq_one_iff_F1 (mul_mem (inv_mem heF) hfF)).1 ?_
    rw [hS.crossed_mul_D1 (inv_mem (hS.F1_le_D1 heF)) (hS.F1_le_D1 hfF),
      hS.crossed_inv_D1 (hS.F1_le_D1 heF), hef, inv_mul_cancel]
  have hwS : e⁻¹ * f ∈ centralizer (miyamotoI2r1G h L η : Set G) :=
    mul_mem (inv_mem (hS.E_le_centralizer_S he)) hfS
  have hwZ : e⁻¹ * f ∈ miyamotoZG h L η := by
    rw [← hS.A1G_inf_centralizer_S]
    exact ⟨hw, hwS⟩
  rw [show f = e * (e⁻¹ * f) by group]
  exact mul_mem he (hS.ZP_le_E hwZ)

theorem F1_torus_decomp (hS : Setting h L η t Q T) :
    (∀ x ∈ miyamotoF1G h L η t ⊓ centralizer ((⊥ : Subgroup G) : Set G) ⊓
        centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G),
      ∀ y ∈ miyamotoF1G h L η t ⊓ centralizer ((⊥ : Subgroup G) : Set G) ⊓
        centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G), x * y = y * x) ∧
    (∀ e ∈ miyamotoF1G h L η t, e ∈ centralizer ((⊥ : Subgroup G) : Set G) →
      ∃ x ∈ miyamotoF1G h L η t ⊓ centralizer ((⊥ : Subgroup G) : Set G) ⊓
          centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G),
        ∃ y ∈ miyamotoF1G h L η t ⊓ centralizer ((⊥ : Subgroup G) : Set G) ⊓
          centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G), e = x * y) ∧
    (∀ x ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ⊓
        centralizer (miyamotoI2r1G h L η : Set G),
      ∀ y ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ⊓
        centralizer (miyamotoI2G h L η : Set G), x * y = y * x) ∧
    (∀ e ∈ miyamotoF1G h L η t, e ∈ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) →
      ∃ x ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ⊓
          centralizer (miyamotoI2r1G h L η : Set G),
        ∃ y ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ⊓
          centralizer (miyamotoI2G h L η : Set G), e = x * y) := by
  obtain ⟨hpow, hr2, hr1, hI2⟩ := hS.tori_le_IG
  have g1 := hS.gomi_F1 bot_le hpow hr2
    (fun a ha _ => by
      obtain ⟨u, hu, hu1, v, hv, hv2, huv⟩ := hS.A1G_decomp_one ha
      exact ⟨u, hu, mem_centralizer_bot u, hu1, v, hv, mem_centralizer_bot v, hv2, huv⟩)
    (fun a ha h₁ h₂ => hS.A1G_disj_one ha h₁ h₂)
  have g2 := hS.gomi_F1 hpow hr1 hI2 (fun a ha haJ => hS.A1G_decomp_two ha haJ)
    (fun a ha h₁ h₂ => hS.A1G_disj_two ha h₁ h₂)
  exact ⟨g1.1, g1.2, g2.1, g2.2⟩

theorem conj_mem_E_of_mem_F1 (hS : Setting h L η t Q T) {f e : G}
    (hf : f ∈ miyamotoF1G h L η t) (he : e ∈ miyamotoEG h L η Q) :
    f * e * f⁻¹ ∈ miyamotoEG h L η Q := by
  obtain ⟨c1, d1, c2, d2⟩ := hS.F1_torus_decomp
  obtain ⟨x, hx, y, hy, rfl⟩ := d1 f hf (mem_centralizer_bot f)
  obtain ⟨x', hx', y', hy', rfl⟩ := d2 x (mem_inf.1 (mem_inf.1 hx).1).1 (mem_inf.1 hx).2
  have heF := hS.E_le_F1 he
  have heJ := hS.E_le_centralizer_I2pow he
  have he1 : e ∈ miyamotoF1G h L η t ⊓ centralizer ((⊥ : Subgroup G) : Set G) ⊓
      centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) :=
    ⟨⟨heF, mem_centralizer_bot e⟩, heJ⟩
  have he2 : e ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI2pow h) : Set G) ⊓
      centralizer (miyamotoI2r1G h L η : Set G) := ⟨⟨heF, heJ⟩, hS.E_le_centralizer_S he⟩
  have hx'E : x' ∈ miyamotoEG h L η Q := by
    rw [hS.E_eq_F1_inf_centralizer_S]
    exact ⟨(mem_inf.1 (mem_inf.1 hx').1).1, (mem_inf.1 hx').2⟩
  have hey : e * y = y * e := c1 e he1 y hy
  have hey' : e * y' = y' * e := c2 e he2 y' hy'
  have : x' * y' * y * e * (x' * y' * y)⁻¹ = x' * e * x'⁻¹ := by
    calc x' * y' * y * e * (x' * y' * y)⁻¹ = x' * y' * (y * e * y⁻¹) * y'⁻¹ * x'⁻¹ := by group
      _ = x' * (y' * e * y'⁻¹) * x'⁻¹ := by rw [← hey, mul_inv_cancel_right]; group
      _ = x' * e * x'⁻¹ := by rw [← hey', mul_inv_cancel_right]
  rw [this]
  exact mul_mem (mul_mem hx'E he) (inv_mem hx'E)

theorem E_inf_A1 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ miyamotoA1G h L η = miyamotoZG h L η := by
  refine le_antisymm (fun e he => (hS.crossed_eq_one_iff_E he.1).1 ?_)
    (le_inf hS.ZP_le_E hS.ZP_le_A1)
  exact (hS.crossed_eq_one_iff_F1 (hS.A1_le_F1 he.2)).2 he.2

theorem I1_le_normalizer_ZP (hS : Setting h L η t Q T) :
    miyamotoI1G h L η ≤ normalizer (miyamotoZG h L η : Set G) := fun _ hi =>
  hS.H_le_normalizer_ZP (hS.IG_le_H (miyamotoPull_mono h L η (miyamotoI1_le_I h) hi))

theorem exists_I1_conj_ZP (_hS : Setting h L η t Q T) {z w : G} (hz : z ∈ miyamotoZG h L η)
    (hw : w ∈ miyamotoZG h L η) (hz1 : z ≠ 1) (hw1 : w ≠ 1) :
    ∃ i ∈ miyamotoI1G h L η, i * z * i⁻¹ = w := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hw
  obtain ⟨d, hd, hgd⟩ := hg
  obtain ⟨d', hd', hkd⟩ := hk
  have hd0 : d ≠ 0 := fun e => hz1 (by
    rw [show g = 1 from Subtype.ext (by rw [hgd, e, miyamotoXGL_zero, coe_one]), map_one, coe_one])
  have hd'0 : d' ≠ 0 := fun e => hw1 (by
    rw [show k = 1 from Subtype.ext (by rw [hkd, e, miyamotoXGL_zero, coe_one]), map_one, coe_one])
  obtain ⟨s, hs, e⟩ := exists_I1_conj_Z h hd hd' hd0 hd'0
  have hDI : miyamotoIHom h (s, s) ∈ miyamotoI1 h := (mem_miyamotoI1 h).2 ⟨s, hs, rfl⟩
  have hDS : miyamotoIHom h (s, s) ∈ gramSU h (miyamotoJ4 K) := miyamotoI1_le_SU h hDI
  set D : gramSU h (miyamotoJ4 K) := ⟨_, hDS⟩
  refine ⟨((η.symm D⁻¹ : L) : G), (symm_mem_miyamotoPull_iff h L η).2 (inv_mem hDI), ?_⟩
  have e' : D⁻¹⁻¹⁻¹ * g * D⁻¹⁻¹ = k := Subtype.ext (by
    simp only [inv_inv, coe_mul, coe_inv]
    rw [hgd, hkd]
    exact e)
  rw [← e']
  simp only [map_mul, map_inv, coe_mul, coe_inv, inv_inv]

theorem mem_normalizer_ZP_of_conj (hS : Setting h L η t Q T) {x z : G}
    (hx : x ∈ miyamotoN1G h L η) (hz : z ∈ miyamotoZG h L η) (hz1 : z ≠ 1)
    (hxz : x * z * x⁻¹ ∈ miyamotoZG h L η) : x ∈ normalizer (miyamotoZG h L η : Set G) := by
  refine mem_normalizer_fintype fun w hw => ?_
  by_cases hw1 : w = 1
  · rw [hw1, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨i, hi, rfl⟩ := hS.exists_I1_conj_ZP hz hw hz1 hw1
  have hix : i * x = x * i := I1G_commute_N1G h L η hi hx
  have e : x * (i * z * i⁻¹) * x⁻¹ = i * (x * z * x⁻¹) * i⁻¹ := by
    have hix'' : i⁻¹ * x⁻¹ = x⁻¹ * i⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hix]
    calc x * (i * z * i⁻¹) * x⁻¹ = (x * i) * z * (i⁻¹ * x⁻¹) := by group
      _ = (i * x) * z * (x⁻¹ * i⁻¹) := by rw [hix, hix'']
      _ = i * (x * z * x⁻¹) * i⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 (hS.I1_le_normalizer_ZP hi) _).1 hxz

theorem N1_le_normalizer_A1 (hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ normalizer (miyamotoA1G h L η : Set G) := fun _ hn =>
  hS.normalizer_B1_le_normalizer_A1 (hS.N1G_le_normalizer_B1 hn).1

theorem A1_le_of_conj_ZP (hS : Setting h L η t Q T) {W : Subgroup G}
    (hW : ∀ x ∈ miyamotoN1G h L η, x ∉ normalizer (miyamotoZG h L η : Set G) →
      ∀ z ∈ miyamotoZG h L η, x * z * x⁻¹ ∈ W)
    (hI : ∀ i ∈ miyamotoI1G h L η, ∀ w ∈ W, i * w * i⁻¹ ∈ W) :
    miyamotoA1G h L η ≤ W := by
  have : CharP K 2 := h.charP
  have hA := miyamotoUnipotent_le_SU h true false
  have hz₁A : miyamotoXGL h 0 0 0 1 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_one _⟩
  set z₁ : G := ((η.symm ⟨_, hA hz₁A⟩ : L) : G) with hz₁
  have hz₁Z : z₁ ∈ miyamotoZG h L η := (symm_mem_miyamotoPull_iff h L η).2 ⟨1, map_one _, rfl⟩
  have hz₁1 : z₁ ≠ 1 := by
    intro e
    have : (⟨_, hA hz₁A⟩ : gramSU h (miyamotoJ4 K)) = 1 := by
      apply η.symm.injective
      rw [map_one]
      exact Subtype.ext e
    have e2 := congrArg Subtype.val this
    rw [OneMemClass.coe_one, ← miyamotoXGL_zero h, miyamotoXGL_inj] at e2
    exact one_ne_zero e2.2.2.2
  have hpt : ∀ p : K, ((η.symm ⟨_, hA (point_mem_A1 h p).1⟩ : L) : G) ∈ W := by
    intro p
    obtain ⟨hpA, hp1, hpQ, hpZ⟩ := point_mem_A1 h p
    obtain ⟨n, hn, hnz⟩ := exists_N1_conj_z1 h hpA hp1 hpQ
    have hnS : n ∈ gramSU h (miyamotoJ4 K) := miyamotoN1_le_gramSU h hn
    have hnG : ((η.symm ⟨n, hnS⟩ : L) : G) ∈ miyamotoN1G h L η :=
      (symm_mem_miyamotoPull_iff h L η).2 hn
    have e' : ((η.symm ⟨n, hnS⟩ : L) : G)⁻¹ * z₁ * ((η.symm ⟨n, hnS⟩ : L) : G)⁻¹⁻¹ =
        ((η.symm ⟨_, hA hpA⟩ : L) : G) := by
      rw [inv_inv, hz₁, ← coe_symm_conj_inv h L η]
      congr 2
      exact Subtype.ext hnz
    refine e' ▸ hW _ (inv_mem hnG) (fun hN => hpZ ?_) z₁ hz₁Z
    have := (mem_normalizer_iff.1 hN z₁).1 hz₁Z
    rw [e'] at this
    exact (symm_mem_miyamotoPull_iff h L η).1 this
  obtain ⟨ω, hω⟩ := exists_add_bar_eq_one h
  have hz₁W : z₁ ∈ W := by
    have hprod := mul_mem (mul_mem (mul_mem (hpt 0) (hpt ω)) (hpt 1)) (hpt (ω + 1))
    rw [← coe_mul, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul, ← map_mul] at hprod
    have e : (⟨_, hA (point_mem_A1 h 0).1⟩ : gramSU h (miyamotoJ4 K)) *
        ⟨_, hA (point_mem_A1 h ω).1⟩ * ⟨_, hA (point_mem_A1 h 1).1⟩ *
        ⟨_, hA (point_mem_A1 h (ω + 1)).1⟩ = ⟨_, hA hz₁A⟩ :=
      Subtype.ext (four_points h hω)
    rwa [e] at hprod
  have hZW : miyamotoZG h L η ≤ W := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨i, hi, rfl⟩ := hS.exists_I1_conj_ZP hz₁Z hw hz₁1 hw1
    exact hI i hi _ hz₁W
  set B := closure {y | ∃ x ∈ miyamotoN1G h L η, ∃ z ∈ miyamotoZG h L η, y = x * z * x⁻¹}
  have hBW : B ≤ W := by
    rw [closure_le]
    rintro _ ⟨x, hx, z, hz, rfl⟩
    by_cases hxN : x ∈ normalizer (miyamotoZG h L η : Set G)
    · exact hZW ((mem_normalizer_iff.1 hxN z).1 hz)
    · exact hW x hx hxN z hz
  have hBA : B ≤ miyamotoA1G h L η := by
    rw [closure_le]
    rintro _ ⟨x, hx, z, hz, rfl⟩
    exact (mem_normalizer_iff.1 (hS.N1_le_normalizer_A1 hx) z).1 (hS.ZP_le_A1 hz)
  have hBinv : ∀ n ∈ miyamotoN1G h L η, ∀ y ∈ B, n⁻¹ * y * n ∈ B := by
    intro n hn y hy
    refine closure_induction (fun y hy => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hy
    · obtain ⟨x, hx, z, hz, rfl⟩ := hy
      exact subset_closure ⟨n⁻¹ * x, mul_mem (inv_mem hn) hx, z, hz, by group⟩
    · rw [mul_one, inv_mul_cancel]
      exact one_mem _
    · rw [show n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) by group]
      exact mul_mem hx hy
    · rw [show n⁻¹ * x⁻¹ * n = (n⁻¹ * x * n)⁻¹ by group]
      exact inv_mem hx
  rcases miyamotoN1G_irreducible_A1G h L η hBA hBinv with h1 | h1
  · exfalso
    have : z₁ ∈ B := subset_closure ⟨1, one_mem _, z₁, hz₁Z, by group⟩
    rw [h1, mem_bot] at this
    exact hz₁1 this
  · rw [← h1]
    exact hBW

theorem E_comm_conj (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoN1G h L η)
    (hxN : x ∉ normalizer (miyamotoZG h L η : Set G)) {e e' : G} (he : e ∈ miyamotoEG h L η Q)
    (he' : e' ∈ miyamotoEG h L η Q) : e * (x * e' * x⁻¹) = (x * e' * x⁻¹) * e := by
  have hxF := hS.N1_le_normalizer_F1 hx
  have hxA := hS.N1_le_normalizer_A1 hx
  have heF := hS.E_le_F1 he
  have hy : x * e' * x⁻¹ ∈ miyamotoF1G h L η t := (mem_normalizer_iff.1 hxF e').1 (hS.E_le_F1 he')
  set y := x * e' * x⁻¹ with hydef
  set c := e * y * e⁻¹ * y⁻¹ with hc
  have hcA : c ∈ miyamotoA1G h L η :=
    hS.commutator_mem_A1_of_mem_D1 (hS.F1_le_D1 heF) (hS.F1_le_D1 hy)
  have hcE : c ∈ miyamotoEG h L η Q := by
    rw [hc, show e * y * e⁻¹ * y⁻¹ = e * (y * e⁻¹ * y⁻¹) by group]
    exact mul_mem he (hS.conj_mem_E_of_mem_F1 hy (inv_mem he))
  have hxcE : x⁻¹ * c * x ∈ miyamotoEG h L η Q := by
    have hx'e : x⁻¹ * e * x ∈ miyamotoF1G h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem hxF) e).1 heF
      rwa [inv_inv] at this
    have e1 : x⁻¹ * c * x =
        ((x⁻¹ * e * x) * e' * (x⁻¹ * e * x)⁻¹) * e'⁻¹ := by
      rw [hc, hydef]
      group
    rw [e1]
    exact mul_mem (hS.conj_mem_E_of_mem_F1 hx'e he') (inv_mem he')
  have hcZ : c ∈ miyamotoZG h L η := by
    rw [← hS.E_inf_A1]
    exact ⟨hcE, hcA⟩
  have hxcZ : x⁻¹ * c * x⁻¹⁻¹ ∈ miyamotoZG h L η := by
    rw [inv_inv, ← hS.E_inf_A1]
    refine ⟨hxcE, ?_⟩
    have := (mem_normalizer_iff.1 (inv_mem hxA) c).1 hcA
    rwa [inv_inv] at this
  by_cases hc1 : c = 1
  · rw [hc] at hc1
    calc e * y = e * y * e⁻¹ * y⁻¹ * (y * e) := by group
      _ = y * e := by rw [hc1, one_mul]
  · exact absurd (by
      have := hS.mem_normalizer_ZP_of_conj (inv_mem hx) hcZ hc1 hxcZ
      have := inv_mem this
      rwa [inv_inv] at this) hxN

noncomputable def crossedHomD1 (hS : Setting h L η t Q T) : miyamotoD1 h L η t →* G :=
  MonoidHom.mk' (fun d => (d : G)⁻¹ * t * d * t) fun a b => hS.crossed_mul_D1 a.2 b.2

theorem F1_le_of_conj_E (hS : Setting h L η t Q T) {W : Subgroup G}
    (hWF : W ≤ miyamotoF1G h L η t)
    (hW : ∀ x ∈ miyamotoN1G h L η, x ∉ normalizer (miyamotoZG h L η : Set G) →
      ∀ e ∈ miyamotoEG h L η Q, x * e * x⁻¹ ∈ W)
    (hI : ∀ i ∈ miyamotoI1G h L η, ∀ w ∈ W, i * w * i⁻¹ ∈ W) :
    miyamotoF1G h L η t ≤ W := by
  have hA : miyamotoA1G h L η ≤ W := hS.A1_le_of_conj_ZP
    (fun x hx hxN z hz => hW x hx hxN z (hS.ZP_le_E hz)) hI
  have hWD : W ≤ miyamotoD1 h L η t := hWF.trans hS.F1_le_D1
  set V := (W.subgroupOf (miyamotoD1 h L η t)).map hS.crossedHomD1 with hV
  have hmemV : ∀ w ∈ W, w⁻¹ * t * w * t ∈ V := fun w hw =>
    ⟨⟨w, hWD hw⟩, mem_subgroupOf.2 hw, rfl⟩
  have hVA : miyamotoA1G h L η ≤ V := by
    refine hS.A1_le_of_conj_ZP (fun x hx hxN z hz => ?_) (fun i hi v hv => ?_)
    · obtain ⟨e, he, rfl⟩ := hS.exists_E_crossed_eq hz
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1
        (hS.N1G_le_normalizer_B1 hx).2
      rw [← CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := e) hxt]
      exact hmemV _ (hW x hx hxN e he)
    · obtain ⟨⟨w, hwD⟩, hw, rfl⟩ := hv
      have hit : i * t = t * i := mem_centralizer_singleton_iff.1
        (hS.IG_le_C (miyamotoPull_mono h L η (miyamotoI1_le_I h) hi))
      change i * (w⁻¹ * t * w * t) * i⁻¹ ∈ V
      rw [← CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := w) hit]
      exact hmemV _ (hI i hi w (mem_subgroupOf.1 hw))
  intro f hf
  obtain ⟨⟨w, hwD⟩, hw, hwf⟩ := hVA (hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hf))
  have hw' : w ∈ W := mem_subgroupOf.1 hw
  have hwf' : w⁻¹ * t * w * t = f⁻¹ * t * f * t := hwf
  have hrest : w⁻¹ * f ∈ miyamotoA1G h L η := by
    refine (hS.crossed_eq_one_iff_F1 (mul_mem (inv_mem (hWF hw')) hf)).1 ?_
    rw [hS.crossed_mul_D1 (inv_mem hwD) (hS.F1_le_D1 hf), hS.crossed_inv_D1 hwD, hwf',
      inv_mul_cancel]
  rw [show f = w * (w⁻¹ * f) by group]
  exact mul_mem hw' (hA hrest)

theorem F1_eq_closure_conj_E (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t = closure {y | ∃ x ∈ miyamotoN1G h L η,
      x ∉ normalizer (miyamotoZG h L η : Set G) ∧ ∃ e ∈ miyamotoEG h L η Q, y = x * e * x⁻¹} := by
  set W := closure {y | ∃ x ∈ miyamotoN1G h L η,
    x ∉ normalizer (miyamotoZG h L η : Set G) ∧ ∃ e ∈ miyamotoEG h L η Q, y = x * e * x⁻¹}
  have hWF : W ≤ miyamotoF1G h L η t := by
    rw [closure_le]
    rintro _ ⟨x, hx, -, e, he, rfl⟩
    exact (mem_normalizer_iff.1 (hS.N1_le_normalizer_F1 hx) e).1 (hS.E_le_F1 he)
  refine le_antisymm (hS.F1_le_of_conj_E hWF
    (fun x hx hxN e he => subset_closure ⟨x, hx, hxN, e, he, rfl⟩) fun i hi w hw => ?_) hWF
  have hiI := miyamotoPull_mono h L η (miyamotoI1_le_I h) hi
  refine closure_induction (fun y hy => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hw
  · obtain ⟨x, hx, hxN, e, he, rfl⟩ := hy
    have hix : i * x = x * i := I1G_commute_N1G h L η hi hx
    refine subset_closure ⟨x, hx, hxN, i * e * i⁻¹,
      (mem_normalizer_iff.1 (hS.IG_le_normalizer_E hiI) e).1 he, ?_⟩
    have hix' : i⁻¹ * x⁻¹ = x⁻¹ * i⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hix]
    calc i * (x * e * x⁻¹) * i⁻¹ = (i * x) * e * (x⁻¹ * i⁻¹) := by group
      _ = (x * i) * e * (i⁻¹ * x⁻¹) := by rw [hix, hix']
      _ = x * (i * e * i⁻¹) * x⁻¹ := by group
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · rw [show i * (x * y) * i⁻¹ = (i * x * i⁻¹) * (i * y * i⁻¹) by group]
    exact mul_mem hx hy
  · rw [show i * x⁻¹ * i⁻¹ = (i * x * i⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem F1_le_centralizer_E (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ≤ centralizer (miyamotoEG h L η Q : Set G) := by
  rw [hS.F1_eq_closure_conj_E, closure_le]
  rintro _ ⟨x, hx, hxN, e', he', rfl⟩
  exact mem_centralizer_iff.2 fun e he => hS.E_comm_conj hx hxN he he'

theorem F1_comm (hS : Setting h L η t Q T) {f f' : G} (hf : f ∈ miyamotoF1G h L η t)
    (hf' : f' ∈ miyamotoF1G h L η t) : f * f' = f' * f := by
  have key : miyamotoF1G h L η t ≤ centralizer (miyamotoF1G h L η t : Set G) := by
    conv_lhs => rw [hS.F1_eq_closure_conj_E]
    rw [closure_le]
    rintro _ ⟨x, hx, -, e, he, rfl⟩
    refine mem_centralizer_iff.2 fun g hg => ?_
    have hxF := hS.N1_le_normalizer_F1 hx
    have hg' : x⁻¹ * g * x ∈ miyamotoF1G h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem hxF) g).1 hg
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 (hS.F1_le_centralizer_E hg') e he
    calc g * (x * e * x⁻¹) = x * ((x⁻¹ * g * x) * e) * x⁻¹ := by group
      _ = x * (e * (x⁻¹ * g * x)) * x⁻¹ := by rw [hc]
      _ = x * e * x⁻¹ * g := by group
  exact mem_centralizer_iff.1 (key hf') f hf

theorem F1_elementary_or_homocyclic (hS : Setting h L η t Q T) :
    (∀ f ∈ miyamotoF1G h L η t, f * f = 1) ∨
      (∀ f ∈ miyamotoF1G h L η t, f * f = 1 ↔ f ∈ miyamotoA1G h L η) := by
  have : CharP K 2 := h.charP
  set sqHom : miyamotoF1G h L η t →* G := MonoidHom.mk' (fun f => (f : G) * f) fun a b => by
    have := hS.F1_comm a.2 b.2
    simp only [coe_mul]
    calc (a : G) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← this]
      _ = a * a * (b * b) := by group with hsq
  have hrange : sqHom.range ≤ miyamotoA1G h L η := by
    rintro _ ⟨f, rfl⟩
    exact hS.mul_self_mem_A1_of_mem_D1 (hS.F1_le_D1 f.2)
  have hinv : ∀ n ∈ miyamotoN1G h L η, ∀ x ∈ sqHom.range, n⁻¹ * x * n ∈ sqHom.range := by
    rintro n hn _ ⟨f, rfl⟩
    have hnF := hS.N1_le_normalizer_F1 hn
    have hf' : n⁻¹ * f * n ∈ miyamotoF1G h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem hnF) f).1 f.2
      rwa [inv_inv] at this
    exact ⟨⟨_, hf'⟩, by simp only [hsq, MonoidHom.mk'_apply]; group⟩
  have hAe := isElementaryAbelian_miyamotoA1G h L η
  have hA2 : ∀ a ∈ miyamotoA1G h L η, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  rcases miyamotoN1G_irreducible_A1G h L η hrange hinv with h1 | h1
  · left
    intro f hf
    have : sqHom ⟨f, hf⟩ ∈ sqHom.range := ⟨_, rfl⟩
    rw [h1, mem_bot] at this
    exact this
  · right
    have hker : sqHom.ker = (miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t) := by
      have hle : (miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t) ≤ sqHom.ker := fun a ha =>
        hA2 _ (mem_subgroupOf.1 ha)
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      have h1' := Subgroup.card_mul_index sqHom.ker
      rw [Subgroup.index_ker, h1, card_miyamotoA1G, hS.card_F1] at h1'
      have h2 : Nat.card ((miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t)) = (2 ^ f) ^ 4 := by
        rw [← card_miyamotoA1G h L η]
        exact Nat.card_congr (subgroupOfEquivOfLe hS.A1_le_F1).toEquiv
      rw [h2]
      have hpos : 0 < (2 ^ f) ^ 4 := by positivity
      have : Nat.card sqHom.ker * (2 ^ f) ^ 4 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by
        rw [h1']
        ring
      exact (Nat.eq_of_mul_eq_mul_right hpos this).le
    intro f hf
    constructor
    · intro hff
      have : (⟨f, hf⟩ : miyamotoF1G h L η t) ∈ sqHom.ker := hff
      rw [hker] at this
      exact mem_subgroupOf.1 this
    · exact hA2 f

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
