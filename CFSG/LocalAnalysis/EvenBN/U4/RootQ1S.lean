module

public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1Core
public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1Semi

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (CosetData mem_normalizer_sup mem_normalizer_inf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo
  le_normalizer_oTwo)
open scoped commutatorElement

theorem mem_normalizer_lift {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {Y : Subgroup (Bar A)} {g : normalizer (A : Set G)}
    (hg : proj A g ∈ normalizer (Y : Set (Bar A))) : (g : G) ∈ normalizer (lift Y : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxN, hxY⟩ := mem_lift_iff.1 hx
  refine mem_lift_iff.2 ⟨mul_mem (mul_mem g.2 hxN) (inv_mem g.2), ?_⟩
  have := (mem_normalizer_iff.1 hg _).1 hxY
  rwa [← map_inv, ← map_mul, ← map_mul] at this

theorem exists_proj_eq_of_mem_bar {G : Type*} [Group G] {A X : Subgroup G} {x : Bar A}
    (hx : x ∈ bar A X) : ∃ y : normalizer (A : Set G), (y : G) ∈ X ∧ proj A y = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, mem_subgroupOf.1 hy, rfl⟩

@[expose] noncomputable def miyamotoS {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  oTwo (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem isPGroup_Q1 (hS : Setting h L η t Q T) :
    IsPGroup 2 (miyamotoF1G h L η t ⊔ Q : Subgroup G) :=
  hS.isPGroup_F1.to_sup_of_normal_left' hS.isPGroup_Q
    (hS.Q_le_T.trans hS.T_le_normalizer_F1)

theorem bar_Q1_comm (hS : Setting h L η t Q T) {a b : Bar (miyamotoF1G h L η t)}
    (ha : a ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q))
    (hb : b ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q)) : a * b = b * a := by
  obtain ⟨x, hx, rfl⟩ := exists_proj_eq_of_mem_bar ha
  obtain ⟨y, hy, rfl⟩ := exists_proj_eq_of_mem_bar hb
  rw [← map_mul, ← map_mul, proj_eq_proj_iff]
  have := (hS.Q1_mod_F1).2 _ (inv_mem hy) _ (inv_mem hx)
  rw [commutatorElement_def, inv_inv, inv_inv] at this
  simpa only [coe_mul, mul_inv_rev, mul_assoc] using this

theorem bar_Q1_mul_self (hS : Setting h L η t Q T) {a : Bar (miyamotoF1G h L η t)}
    (ha : a ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q)) : a * a = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_proj_eq_of_mem_bar ha
  rw [← map_mul, proj_eq_one_iff]
  exact (hS.Q1_mod_F1).1 _ hx

theorem tBar_mem_bar_Q1 (hS : Setting h L η t Q T) :
    hS.tBar ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) :=
  proj_mem_bar (mem_sup_right hS.t_mem_Q)

theorem bar_P1_le_bar_Q1 (hS : Setting h L η t Q T) :
    bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) ≤
      bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) :=
  bar_mono hS.P1_le_Q1

theorem cosetData_bar (hS : Setting h L η t Q T) :
    CosetData (bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)))
      (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) hS.tBar := by
  obtain ⟨key1, key2, -⟩ := hS.orbit_shape_bar
  have htQ := hS.tBar_mem_bar_Q1
  have hYQ := hS.bar_P1_le_bar_Q1
  have ht2 : hS.tBar * hS.tBar = 1 := hS.bar_Q1_mul_self htQ
  have htinv : hS.tBar⁻¹ = hS.tBar := inv_eq_of_mul_eq_one_right ht2
  have hYt : ∀ y ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η),
      hS.tBar * y = y * hS.tBar := fun y hy => hS.bar_Q1_comm htQ (hYQ hy)
  refine ⟨ht2, fun y hy => mem_centralizer_singleton_iff.2 (hYt y hy).symm,
    { is_comm := ⟨fun a b => Subtype.ext (hS.bar_Q1_comm (hYQ a.2) (hYQ b.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by rw [pow_two]; exact hS.bar_Q1_mul_self (hYQ a.2)) }, key2,
    fun g hg => ?_⟩
  have h1 := key1 g hg
  have e : g⁻¹ * hS.tBar * g * hS.tBar =
      hS.tBar * (hS.tBar * (g⁻¹ * hS.tBar * g)) * hS.tBar := by
    rw [← mul_assoc hS.tBar hS.tBar, ht2, one_mul]
  rw [e, hYt _ h1, mul_assoc, ht2, mul_one]
  exact h1

theorem IG_le_normalizer_Q (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (Q : Set G) := fun x hx => by
  rw [hS.Q_eq]
  exact mem_normalizer_sup (hS.IG_le_normalizer_PG hx)
    (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 (hS.IG_le_C hx)))

theorem T_le_normalizer_Q (hS : Setting h L η t Q T) : T ≤ normalizer (Q : Set G) :=
  fun _ hx => hS.normalizer_T_le_normalizer_Q (le_normalizer hx)

theorem T_le_normalizer_Q1 (hS : Setting h L η t Q T) :
    T ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup (hS.T_le_normalizer_F1 hx) (hS.T_le_normalizer_Q hx)

theorem proj_mem_centralizer_tBar_iff (hS : Setting h L η t Q T)
    (g : normalizer (miyamotoF1G h L η t : Set G)) :
    proj _ g ∈ centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) ↔
      ((g : G) * t)⁻¹ * (t * g) ∈ miyamotoF1G h L η t := by
  rw [mem_centralizer_singleton_iff, tBar, ← map_mul, ← map_mul, proj_eq_proj_iff]
  rfl

theorem le_bar_Q1_of_isPGroup (hS : Setting h L η t Q T) {R : Subgroup (Bar (miyamotoF1G h L η t))}
    (hRH : R ≤ bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
      centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))))
    (hRn : bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
      centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) ≤
        normalizer (R : Set (Bar (miyamotoF1G h L η t))))
    (hR2 : IsPGroup 2 R) : R ≤ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN := hS.normalizer_Q1_le_normalizer_F1
  have hFH : miyamotoF1G h L η t ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) :=
    le_sup_left.trans le_normalizer
  have htQ := hS.tBar_mem_bar_Q1
  have hBK : bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) ≤
      bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
        centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) :=
    le_inf (bar_mono le_normalizer) fun b hb =>
      mem_centralizer_singleton_iff.2 (hS.bar_Q1_comm hb htQ)
  set R' := R ⊔ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) with hR'
  have hR'2 : IsPGroup 2 R' :=
    hR2.to_sup_of_normal_left' (isPGroup_bar hS.isPGroup_Q1) (hBK.trans hRn)
  have hR'n : bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
        centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) ≤
      normalizer (R' : Set (Bar (miyamotoF1G h L η t))) := fun g hg =>
    mem_normalizer_sup (hRn hg) (bar_le_normalizer_bar le_sup_left le_rfl hg.1)
  set X := lift R' with hX
  have hX2 : IsPGroup 2 X := isPGroup_lift hS.isPGroup_F1 hR'2
  have hXn : ∀ g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G),
      (g * t)⁻¹ * (t * g) ∈ miyamotoF1G h L η t → g ∈ normalizer (X : Set G) := fun g hg hgt =>
    mem_normalizer_lift (g := ⟨g, hHN hg⟩)
      (hR'n ⟨proj_mem_bar hg, (hS.proj_mem_centralizer_tBar_iff _).2 hgt⟩)
  have hTX : T ≤ normalizer (X : Set G) := fun τ hτ => by
    refine hXn τ (hS.T_le_normalizer_Q1 hτ) ?_
    rw [mem_centralizer_singleton_iff.1 (hS.T_le hτ), inv_mul_cancel]
    exact one_mem _
  have hIX : miyamotoIG h L η ≤ normalizer (X : Set G) := fun i hi => by
    refine hXn i (hS.IG_le_normalizer_Q1 hi) ?_
    rw [mem_centralizer_singleton_iff.1 (hS.IG_le_C hi), inv_mul_cancel]
    exact one_mem _
  set X₀ := X ⊓ centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) with hX₀
  have hX₀Q : X₀ ≤ Q := by
    refine hS.le_Q_of_isPGroup (inf_le_left.trans inf_le_right) inf_le_right
      (hX2.to_le (inf_le_left.trans inf_le_left)) (fun τ hτ => ?_) (fun i hi => ?_)
    · exact mem_normalizer_inf (mem_normalizer_inf (hTX hτ) (le_normalizer (hS.T_le hτ)))
        (le_normalizer (hS.T_le_normalizer_Q hτ))
    · exact mem_normalizer_inf (mem_normalizer_inf (hIX hi) (le_normalizer (hS.IG_le_C hi)))
        (le_normalizer (hS.IG_le_normalizer_Q hi))
  intro r hr
  obtain ⟨⟨r₀, hr₀N⟩, rfl⟩ := proj_surjective r
  have hr₀H := (mem_bar_iff hFH _).1 (hRH hr).1
  have hr₀t := (hS.proj_mem_centralizer_tBar_iff _).1 (hRH hr).2
  have hr₀B := hS.mem_normalizer_B1_of_crossed_mem_F1 hr₀N hr₀t
  obtain ⟨c, hcQC, d, hd, rfl⟩ := hS.exists_mul_of_mem_normalizer_Q1_inf_B1 hr₀H hr₀B
  have hDQ : miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ Q := by
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_Q))
  have hdQ := hDQ hd
  have hdX : d ∈ X := mem_lift_of_proj_mem (x := ⟨d, hHN (le_normalizer hdQ)⟩)
    (mem_sup_right (proj_mem_bar hdQ))
  have hcdX : c * d ∈ X := mem_lift_of_proj_mem (x := ⟨c * d, hr₀N⟩) (mem_sup_left hr)
  have hcX : c ∈ X := by
    have := mul_mem hcdX (inv_mem hdX)
    rwa [mul_inv_cancel_right] at this
  have hcQ : c ∈ Q := hX₀Q ⟨⟨hcX, (mem_inf.1 hcQC).2⟩, (mem_inf.1 hcQC).1⟩
  exact (mem_bar_iff le_sup_left _).2 (mul_mem (mem_sup_right hcQ) hdQ)

theorem commutator_mem_bar_Q1 (hS : Setting h L η t Q T) {a k : Bar (miyamotoF1G h L η t)}
    (ha : a ∈ bar (miyamotoF1G h L η t) (miyamotoIG h L η))
    (hk : k ∈ bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
      centralizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
        Set (Bar (miyamotoF1G h L η t))) ⊓
      centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t)))) :
    a * k * a⁻¹ * k⁻¹ ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) := by
  have hFH : miyamotoF1G h L η t ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) :=
    le_sup_left.trans le_normalizer
  have hQF : miyamotoF1G h L η t ⊔ Q ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    sup_le le_normalizer (hS.Q_le_T.trans hS.T_le_normalizer_F1)
  obtain ⟨⟨hkH, hkY⟩, hkt⟩ := hk
  obtain ⟨k₀, -, rfl⟩ := exists_proj_eq_of_mem_bar hkH
  have hk₀H := (mem_bar_iff hFH _).1 hkH
  obtain ⟨a₀, ha₀I, rfl⟩ := exists_proj_eq_of_mem_bar ha
  have hc : ∀ x ∈ miyamotoF1G h L η t ⊔ Q, (k₀ : G) * x * (k₀ : G)⁻¹ * x⁻¹ ∈
      miyamotoF1G h L η t := by
    intro x hx
    have hxN := hQF hx
    have hcomm : proj _ k₀ * proj _ ⟨x, hxN⟩ = proj _ ⟨x, hxN⟩ * proj _ k₀ := by
      rcases hS.mem_P1_or_of_mem_Q1 hx with hxP | htxP
      · exact (mem_centralizer_iff.1 hkY _ (proj_mem_bar hxP)).symm
      · have htxN := hQF (hS.P1_le_Q1 htxP)
        have e : proj _ ⟨x, hxN⟩ = hS.tBar * proj _ ⟨t * x, htxN⟩ := by
          rw [tBar, ← map_mul]
          congr 1
          exact Subtype.ext (by
            change x = t * (t * x)
            rw [← mul_assoc, hS.t_mul_t, one_mul])
        rw [e, ← mul_assoc, mem_centralizer_singleton_iff.1 hkt, mul_assoc,
          (mem_centralizer_iff.1 hkY _ (proj_mem_bar htxP)).symm, ← mul_assoc]
    have h1 : proj _ (k₀ * ⟨x, hxN⟩ * k₀⁻¹ * ⟨x, hxN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_inv_cancel_right,
        mul_inv_cancel]
    exact proj_eq_one_iff.1 h1
  obtain ⟨q, hq, i₁, hi₁, e⟩ := exists_mul_of_mem_sup_of_le_normalizer'
    ((miyamotoPull_mono h L η (miyamotoI1_le_I h)).trans hS.IG_le_normalizer_Q1)
    (hS.mem_sup_I1_of_commutator_mem_F1 hk₀H hc)
  have hi₁I : i₁ ∈ miyamotoIG h L η := miyamotoPull_mono h L η (miyamotoI1_le_I h) hi₁
  have hcomm : (a₀ : G) * i₁ = i₁ * a₀ := hS.IG_comm ha₀I hi₁I
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    mem_bar_iff (le_sup_left : miyamotoF1G h L η t ≤ miyamotoF1G h L η t ⊔ Q)]
  change (a₀ : G) * k₀ * (a₀ : G)⁻¹ * (k₀ : G)⁻¹ ∈ miyamotoF1G h L η t ⊔ Q
  rw [e, show (a₀ : G) * (q * i₁) * (a₀ : G)⁻¹ * (q * i₁)⁻¹ =
      ((a₀ : G) * q * (a₀ : G)⁻¹) * ((a₀ : G) * i₁ * (a₀ : G)⁻¹ * i₁⁻¹) * q⁻¹ by group,
    hcomm, mul_inv_cancel_right, mul_inv_cancel, mul_one]
  exact mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_Q1 ha₀I) q).1 hq) (inv_mem hq)

theorem exists_bar_I_conj (hS : Setting h L η t Q T) {a a' : Bar (miyamotoF1G h L η t)}
    (ha : a ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) (ha1 : a ≠ 1)
    (ha' : a' ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η))
    (ha'1 : a' ≠ 1) :
    ∃ c ∈ bar (miyamotoF1G h L η t) (miyamotoIG h L η), c * a * c⁻¹ = a' := by
  have hFP : miyamotoF1G h L η t ≤ miyamotoF1G h L η t ⊔ miyamotoPG h L η := le_sup_left
  obtain ⟨x, rfl⟩ := proj_surjective a
  obtain ⟨x', rfl⟩ := proj_surjective a'
  have hx := (mem_bar_iff hFP x).1 ha
  have hx' := (mem_bar_iff hFP x').1 ha'
  have hxF : (x : G) ∉ miyamotoF1G h L η t := fun e => ha1 (proj_eq_one_iff.2 e)
  have hx'F : (x' : G) ∉ miyamotoF1G h L η t := fun e => ha'1 (proj_eq_one_iff.2 e)
  obtain ⟨i, hi, hix⟩ := hS.exists_IG_conj_mul_inv_mem_F1 hx hxF hx' hx'F
  have hiN := hS.IG_le_normalizer_F1 hi
  refine ⟨(proj _ ⟨i, hiN⟩)⁻¹, inv_mem (proj_mem_bar hi), ?_⟩
  have h1 : proj _ (⟨i, hiN⟩⁻¹ * x * ⟨i, hiN⟩ * x'⁻¹) = 1 :=
    proj_eq_one_iff.2 (by simpa only [coe_mul, coe_inv] using hix)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
  rw [inv_inv]
  exact h1

theorem exists_conj_eq_mul_bar (hS : Setting h L η t Q T) {y : Bar (miyamotoF1G h L η t)}
    (hy : y ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) :
    ∃ v ∈ bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
      centralizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
        Set (Bar (miyamotoF1G h L η t))),
      v⁻¹ * hS.tBar * v = hS.tBar * y := by
  have hc := hS.cosetData_bar
  have hHN := hS.normalizer_Q1_le_normalizer_F1
  have hP1N := hS.P1_le_normalizer_F1
  by_cases hy1 : y = 1
  · exact ⟨1, one_mem _, by simp [hy1]⟩
  obtain ⟨g, hg, hgP, hgt⟩ := hS.exists_mem_normalizer_Q1_crossed_not_mem_F1
  set gb := proj (miyamotoF1G h L η t) ⟨g, hHN hg⟩ with hgb
  have hgbH : gb ∈ bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) := proj_mem_bar hg
  have hgbY : gb ∈ centralizer (bar (miyamotoF1G h L η t)
      (miyamotoF1G h L η t ⊔ miyamotoPG h L η) : Set (Bar (miyamotoF1G h L η t))) := by
    refine mem_centralizer_iff.2 fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := exists_proj_eq_of_mem_bar hz
    have h1 : proj _ (⟨g, hHN hg⟩ * x * ⟨g, hHN hg⟩⁻¹ * x⁻¹) = 1 := proj_eq_one_iff.2 (hgP _ hx)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  set w := gb⁻¹ * hS.tBar * gb * hS.tBar with hw
  have hwY := hc.crossed_mem gb hgbH
  have hw1 : w ≠ 1 := by
    intro e
    apply hgt
    have h1 : hS.tBar * gb = gb * hS.tBar := by
      have h2 : gb⁻¹ * hS.tBar * gb = hS.tBar := by
        have := (hc.crossed_eq_iff (one_mem _)).1 e
        rwa [mul_one] at this
      calc hS.tBar * gb = gb * (gb⁻¹ * hS.tBar * gb) := by group
        _ = gb * hS.tBar := by rw [h2]
    rw [tBar, hgb, ← map_mul, ← map_mul, proj_eq_proj_iff] at h1
    convert inv_mem h1 using 1
    simp only [coe_mul]
    group
  obtain ⟨c, hcI, hcw⟩ := hS.exists_bar_I_conj hwY hw1 hy hy1
  have hcH : c ∈ bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :=
    bar_mono hS.IG_le_normalizer_Q1 hcI
  have hct : c * hS.tBar = hS.tBar * c := by
    obtain ⟨i, hi, rfl⟩ := exists_proj_eq_of_mem_bar hcI
    rw [tBar, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hS.IG_le_C hi))
  refine ⟨c * gb * c⁻¹, hc.conj_mem_inf_centralizer hcH ⟨hgbH, hgbY⟩, ?_⟩
  have hgt' : gb⁻¹ * hS.tBar * gb = hS.tBar * w := (hc.crossed_eq_iff hwY).1 rfl
  have hct' : c⁻¹ * hS.tBar = hS.tBar * c⁻¹ := by
    calc c⁻¹ * hS.tBar = c⁻¹ * (hS.tBar * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * hS.tBar) * c⁻¹ := by rw [hct]
      _ = hS.tBar * c⁻¹ := by group
  calc (c * gb * c⁻¹)⁻¹ * hS.tBar * (c * gb * c⁻¹) =
      c * (gb⁻¹ * (c⁻¹ * hS.tBar) * c * gb) * c⁻¹ := by group
    _ = c * (gb⁻¹ * hS.tBar * gb) * c⁻¹ := by rw [hct']; group
    _ = c * hS.tBar * (w * c⁻¹) := by rw [hgt']; group
    _ = hS.tBar * (c * w * c⁻¹) := by rw [hct]; group
    _ = hS.tBar * y := by rw [hcw]

theorem two_core_bar (hS : Setting h L η t Q T) :
    oTwo (bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))) ≤
      centralizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
        Set (Bar (miyamotoF1G h L η t))) ∧
    oTwo (bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))) ⊓
      centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) =
        bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) ∧
    (∀ y ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η),
      ∃ d ∈ oTwo (bar (miyamotoF1G h L η t)
        (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))),
        d⁻¹ * hS.tBar * d = hS.tBar * y) ∧
    ∀ g ∈ bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)),
      ∃ c ∈ bar (miyamotoF1G h L η t)
          (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
        centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))),
        ∃ d ∈ oTwo (bar (miyamotoF1G h L η t)
          (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))), g = c * d := by
  have hc := hS.cosetData_bar
  have htQ := hS.tBar_mem_bar_Q1
  have hYQ := hS.bar_P1_le_bar_Q1
  have hBn : bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ≤
        normalizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) :
          Set (Bar (miyamotoF1G h L η t))) :=
    bar_le_normalizer_bar le_sup_left le_rfl
  have hBK : bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) ≤
      bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
        centralizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
          Set (Bar (miyamotoF1G h L η t))) ⊓
        centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) :=
    le_inf (le_inf (bar_mono le_normalizer) fun b hb =>
      mem_centralizer_iff.2 fun y hy => hS.bar_Q1_comm (hYQ hy) hb)
      fun b hb => mem_centralizer_singleton_iff.2 (hS.bar_Q1_comm hb htQ)
  have hAH : bar (miyamotoF1G h L η t) (miyamotoIG h L η) ≤
      bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ⊓
        centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t))) := by
    rintro _ ⟨i, hi, rfl⟩
    have hiI := mem_subgroupOf.1 hi
    refine mem_inf.2 ⟨proj_mem_bar (hS.IG_le_normalizer_Q1 hiI),
      (hS.proj_mem_centralizer_tBar_iff _).2 ?_⟩
    rw [mem_centralizer_singleton_iff.1 (hS.IG_le_C hiI), inv_mul_cancel]
    exact one_mem _
  have hY : 2 < Nat.card (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) := by
    rw [hS.card_bar_P1]
    have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) hS.four_le
    calc 2 < 2 ^ f := hq
      _ ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQtr := hc.transitive_of_transitive hBn hAH
    (fun a ha k hk => hS.commutator_mem_bar_Q1 ha hk)
    (fun y hy y' hy' hy1 hy'1 => hS.exists_bar_I_conj hy hy1 hy' hy'1) hY
    (fun y hy => hS.exists_conj_eq_mul_bar hy)
  obtain ⟨h1, -, h3, h4, h5⟩ := hc.two_core (isPGroup_bar hS.isPGroup_Q1) hBK hBn
    (fun R hRH hRn hR2 => hS.le_bar_Q1_of_isPGroup hRH hRn hR2) hQtr
  exact ⟨h1, h3, h4, h5⟩

theorem miyamotoS_eq_lift (hS : Setting h L η t Q T) :
    miyamotoS h L η t Q = lift (oTwo (bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)))) := by
  have hHN := hS.normalizer_Q1_le_normalizer_F1
  have hFH : miyamotoF1G h L η t ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) :=
    le_sup_left.trans le_normalizer
  have hFS : miyamotoF1G h L η t ≤ miyamotoS h L η t Q := le_oTwo hFH hHN hS.isPGroup_F1
  refine le_antisymm (fun x hx => ?_) (le_oTwo ?_ (fun g hg => ?_)
    (isPGroup_lift hS.isPGroup_F1 (isPGroup_oTwo _)))
  · have hxN := hHN (oTwo_le _ hx)
    refine mem_lift_of_proj_mem (x := ⟨x, hxN⟩) ?_
    exact le_oTwo (bar_mono (oTwo_le _)) (bar_le_normalizer_bar hFS (le_normalizer_oTwo _))
      (isPGroup_bar (isPGroup_oTwo _)) (proj_mem_bar hx)
  · calc lift (oTwo (bar (miyamotoF1G h L η t)
          (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)))) ≤
        lift (bar (miyamotoF1G h L η t)
          (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))) := lift_mono (oTwo_le _)
      _ = normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := lift_bar hFH hHN
  · exact mem_normalizer_lift (g := ⟨g, hHN hg⟩) (le_normalizer_oTwo _ (proj_mem_bar hg))

theorem isPGroup_miyamotoS (_hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoS h L η t Q) :=
  isPGroup_oTwo _

theorem miyamotoS_le_normalizer_Q1 (_hS : Setting h L η t Q T) :
    miyamotoS h L η t Q ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) :=
  oTwo_le _

theorem normalizer_Q1_le_normalizer_miyamotoS (_hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer (miyamotoS h L η t Q : Set G) :=
  le_normalizer_oTwo _

theorem Q1_le_miyamotoS (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ Q ≤ miyamotoS h L η t Q := by
  obtain ⟨-, h3, -, -⟩ := hS.two_core_bar
  have hQN : miyamotoF1G h L η t ⊔ Q ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    sup_le le_normalizer (hS.Q_le_T.trans hS.T_le_normalizer_F1)
  intro x hx
  rw [hS.miyamotoS_eq_lift]
  refine mem_lift_of_proj_mem (x := ⟨x, hQN hx⟩) ?_
  have : proj _ ⟨x, hQN hx⟩ ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) :=
    proj_mem_bar hx
  rw [← h3] at this
  exact this.1

theorem commutator_miyamotoS_P1_mem_F1 (hS : Setting h L η t Q T) {s x : G}
    (hs : s ∈ miyamotoS h L η t Q) (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    s * x * s⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t := by
  obtain ⟨h1, -, -, -⟩ := hS.two_core_bar
  rw [hS.miyamotoS_eq_lift] at hs
  obtain ⟨hsN, hsO⟩ := mem_lift_iff.1 hs
  have hxN := hS.P1_le_normalizer_F1 hx
  have hcomm := mem_centralizer_iff.1 (h1 hsO) _ (proj_mem_bar (x := ⟨x, hxN⟩) hx)
  have h2 : proj _ (⟨s, hsN⟩ * ⟨x, hxN⟩ * ⟨s, hsN⟩⁻¹ * ⟨x, hxN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm, mul_inv_cancel_right, mul_inv_cancel]
  exact proj_eq_one_iff.1 h2

theorem mem_Q1_of_mem_miyamotoS (hS : Setting h L η t Q T) {s : G}
    (hs : s ∈ miyamotoS h L η t Q) (hst : (s * t)⁻¹ * (t * s) ∈ miyamotoF1G h L η t) :
    s ∈ miyamotoF1G h L η t ⊔ Q := by
  obtain ⟨-, h3, -, -⟩ := hS.two_core_bar
  rw [hS.miyamotoS_eq_lift] at hs
  obtain ⟨hsN, hsO⟩ := mem_lift_iff.1 hs
  have : proj _ ⟨s, hsN⟩ ∈ bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) := by
    rw [← h3]
    exact ⟨hsO, (hS.proj_mem_centralizer_tBar_iff _).2 hst⟩
  exact (mem_bar_iff le_sup_left _).1 this

theorem exists_mem_miyamotoS_conj (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    ∃ s ∈ miyamotoS h L η t Q, (s⁻¹ * t * s)⁻¹ * (t * x) ∈ miyamotoF1G h L η t := by
  obtain ⟨-, -, h4, -⟩ := hS.two_core_bar
  have hxN := hS.P1_le_normalizer_F1 hx
  obtain ⟨d, hd, hdt⟩ := h4 _ (proj_mem_bar (x := ⟨x, hxN⟩) hx)
  obtain ⟨s, rfl⟩ := proj_surjective d
  refine ⟨s, ?_, ?_⟩
  · rw [hS.miyamotoS_eq_lift]
    exact mem_lift_of_proj_mem hd
  · rw [tBar, ← map_inv, ← map_mul, ← map_mul, ← map_mul, proj_eq_proj_iff] at hdt
    simpa only [coe_mul, coe_inv] using hdt

theorem exists_mul_miyamotoS_of_mem_normalizer_Q1 (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    ∃ c ∈ normalizer (Q : Set G) ⊓ centralizer ({t} : Set G), ∃ s ∈ miyamotoS h L η t Q,
      g = c * s := by
  obtain ⟨-, -, -, h5⟩ := hS.two_core_bar
  have hHN := hS.normalizer_Q1_le_normalizer_F1
  have hFH : miyamotoF1G h L η t ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) :=
    le_sup_left.trans le_normalizer
  obtain ⟨cb, ⟨hcbH, hcbt⟩, d, hd, hgcd⟩ := h5 _ (proj_mem_bar (x := ⟨g, hHN hg⟩) hg)
  obtain ⟨c₀, rfl⟩ := proj_surjective cb
  obtain ⟨s₀, rfl⟩ := proj_surjective d
  have hc₀H := (mem_bar_iff hFH _).1 hcbH
  have hc₀t := (hS.proj_mem_centralizer_tBar_iff _).1 hcbt
  have hc₀B := hS.mem_normalizer_B1_of_crossed_mem_F1 c₀.2 hc₀t
  obtain ⟨c, hcQC, d₁, hd₁, hc₀⟩ := hS.exists_mul_of_mem_normalizer_Q1_inf_B1 hc₀H hc₀B
  have hs₀S : (s₀ : G) ∈ miyamotoS h L η t Q := by
    rw [hS.miyamotoS_eq_lift]
    exact mem_lift_of_proj_mem hd
  have hDQ : miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ Q := by
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_Q))
  have hd₁S := hS.Q1_le_miyamotoS (hDQ hd₁)
  rw [← map_mul, proj_eq_proj_iff] at hgcd
  have hf₀S := hS.Q1_le_miyamotoS (mem_sup_left hgcd)
  refine ⟨c, hcQC, d₁ * s₀ * ((g : G)⁻¹ * ((c₀ * s₀ : normalizer (miyamotoF1G h L η t : Set G)) :
    G))⁻¹, mul_mem (mul_mem hd₁S hs₀S) (inv_mem hf₀S), ?_⟩
  simp only [coe_mul]
  rw [hc₀]
  group

theorem card_miyamotoS (hS : Setting h L η t Q T) :
    Nat.card (miyamotoS h L η t Q) =
      (2 ^ f) ^ 2 * Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) := by
  obtain ⟨h1, h3, h4, -⟩ := hS.two_core_bar
  have hc := hS.cosetData_bar
  set Ob := oTwo (bar (miyamotoF1G h L η t)
    (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))) with hOb
  set Bb := bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ Q) with hBb
  have hBO : Bb ≤ Ob := by rw [← h3]; exact inf_le_left
  have : (Bb.subgroupOf Ob).Normal := hc.normal_subgroupOf (oTwo_le _) h1 h3
  obtain ⟨φ, -, -⟩ := hc.exists_mulEquiv_quotient (oTwo_le _) h1 h3 h4
  have hq : Nat.card (Ob ⧸ Bb.subgroupOf Ob) = (2 ^ f) ^ 2 := by
    rw [Nat.card_congr φ.toEquiv, hS.card_bar_P1]
  have hOcard : Nat.card Ob = (2 ^ f) ^ 2 * Nat.card Bb := by
    rw [← hq, ← Nat.card_congr (subgroupOfEquivOfLe hBO).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hFQ : miyamotoF1G h L η t ≤ miyamotoF1G h L η t ⊔ Q := le_sup_left
  have hQN : miyamotoF1G h L η t ⊔ Q ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    sup_le le_normalizer (hS.Q_le_T.trans hS.T_le_normalizer_F1)
  rw [hS.miyamotoS_eq_lift, card_lift, hOcard, mul_assoc, card_bar_mul hFQ hQN]

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
