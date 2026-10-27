module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsSteps

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped MatrixGroups

@[expose] def PSL2BorelInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (p n : ℕ) [Fact p.Prime],
    (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) →
    Nonempty (K ≃* PSL(2, GaloisField p n)) →
    ∀ Q : Subgroup X, IsSylowOf 2 Q K →
    ∀ E : Subgroup X, E ≤ K → E ≤ normalizer (Q : Set X) → Odd (Nat.card E) →
      ∃ H : Subgroup X, E ≤ H ∧ H ≤ K ∧ H ≤ normalizer (Q : Set X) ∧ Odd (Nat.card H) ∧
        (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧
        (∀ x ∈ Q, (∀ h ∈ H, h * x * h⁻¹ = x) → x = 1) ∧
        ∀ Y : Subgroup X, Y ≤ Q → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) → Y = ⊥ ∨ Y = Q

@[expose] def U3C1GmgIdentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
      IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t * w} : Set G)) →
      ∀ J : Subgroup G, (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J →
        J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
        (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) →
        (∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
          g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J) →
        (∃ (K : Subgroup G) (p n : ℕ) (_ : Fact p.Prime),
            (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
            Nonempty (K ≃* PSL(2, GaloisField p n)) ∧
            K ≤ centralizer ({t * w} : Set G) ∧
            IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G)) K ∧
            D ⊓ centralizer ({t * w} : Set G) ≤ K) ∨
        (∃ (K₁ E₁ : Subgroup G) (p n : ℕ) (_ : Fact p.Prime),
            (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
            Nonempty (K₁ ≃* PSL(2, GaloisField p n)) ∧
            K₁ ≤ centralizer ({t * w} : Set G) ∧
            (∀ a ∈ K₁, ∀ b ∈ K₁, a * (t * b * t⁻¹) = t * b * t⁻¹ * a) ∧
            IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁) K₁ ∧
            (∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
              ∃ x₁ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁,
                ∃ x₂ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁, x = x₁ * (t * x₂ * t⁻¹)) ∧
            E₁ ≤ K₁ ∧
            E₁ ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁ : Subgroup G) : Set G) ∧
            Odd (Nat.card E₁) ∧
            ∀ e ∈ D ⊓ centralizer ({t * w} : Set G),
              ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, e = e₁ * (t * e₂ * t⁻¹))

section General

variable {G : Type} [Group G]

theorem gmg_mem_normalizer {K : Subgroup G} {g : G} (h₁ : ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, g⁻¹ * x * g ∈ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e]
  exact h₂ _ hx

theorem gmg_sup_comm {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hAN : A ≤ normalizer (B : Set G) := fun a ha =>
    gmg_mem_normalizer (fun b hb => by rw [hAB a ha b hb, mul_inv_cancel_right]; exact hb)
      (fun b hb => by
        rw [show a⁻¹ * b * a = a⁻¹ * (b * a) by group, ← hAB a ha b hb, ← mul_assoc,
          inv_mul_cancel, one_mul]
        exact hb)
  intro x hx y hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hAN hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hAN hy
  have c1 : x₁ * y₂ = y₂ * x₁ := hAB x₁ hx₁ y₂ hy₂
  have c2 : x₂ * y₁ = y₁ * x₂ := (hAB y₁ hy₁ x₂ hx₂).symm
  have c3 : x₁ * y₁ = y₁ * x₁ := hA x₁ hx₁ y₁ hy₁
  have c4 : x₂ * y₂ = y₂ * x₂ := hB x₂ hx₂ y₂ hy₂
  calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
    _ = x₁ * (y₁ * x₂) * y₂ := by rw [c2]
    _ = (x₁ * y₁) * (x₂ * y₂) := by group
    _ = (y₁ * x₁) * (y₂ * x₂) := by rw [c3, c4]
    _ = y₁ * (x₁ * y₂) * x₂ := by group
    _ = y₁ * (y₂ * x₁) * x₂ := by rw [c1]
    _ = y₁ * y₂ * (x₁ * x₂) := by group

end General

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmg_t_mem_I : t ∈ centralizer ({t * w} : Set G) := by
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hW.step.start.le hW.w_mem)
  rw [mem_centralizer_singleton_iff]
  calc t * (t * w) = t * (w * t) := by rw [hwt]
    _ = t * w * t := (mul_assoc t w t).symm

theorem gmg_t_inv : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW.step.start.sq_eq_one)

theorem gmg_t_conj_U₁ {u : G} (hu : u ∈ U₁) : t * u * t⁻¹ ∈ U₁ := by
  have htU : t ∈ U := by
    rw [← hW.level.sup_eq]
    exact mem_sup_right (mem_zpowers t)
  exact (mem_normalizer_iff.mp (hW.level.U₁_normal htU) u).mp hu

theorem gmg_t_conj_F {x : G} (hx : x ∈ U₁ ⊓ centralizer ({t * w} : Set G)) :
    t * x * t⁻¹ ∈ U₁ ⊓ centralizer ({t * w} : Set G) :=
  mem_inf.mpr ⟨hW.gmg_t_conj_U₁ (mem_inf.mp hx).1,
    mul_mem (mul_mem hW.gmg_t_mem_I (mem_inf.mp hx).2) (inv_mem hW.gmg_t_mem_I)⟩

theorem gmg_D_le_normalizer_F :
    D ⊓ centralizer ({t * w} : Set G) ≤
      normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) := by
  intro e he
  obtain ⟨heD, heC⟩ := mem_inf.mp he
  have heN := hW.level.D_le heD
  refine gmg_mem_normalizer (fun x hx => ?_) (fun x hx => ?_)
  · exact mem_inf.mpr ⟨(mem_normalizer_iff.mp heN x).mp (mem_inf.mp hx).1,
      mul_mem (mul_mem heC (mem_inf.mp hx).2) (inv_mem heC)⟩
  · have heN' := inv_mem heN
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem heC) (mem_inf.mp hx).2) heC⟩
    have := (mem_normalizer_iff.mp heN' x).mp (mem_inf.mp hx).1
    rwa [inv_inv] at this

theorem gmg_odd_card_D_inf : Odd (Nat.card (D ⊓ centralizer ({t * w} : Set G) : Subgroup G)) :=
  Odd.of_dvd_nat hW.step.cartan.odd (Subgroup.card_dvd_of_le inf_le_left)

theorem gmg_layer_of_case_one (hB : PSL2BorelInput) {K : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hpn : p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5))
    (hK : Nonempty (K ≃* PSL(2, GaloisField p n)))
    (hKI : K ≤ centralizer ({t * w} : Set G))
    (hFK : IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G)) K)
    (hDK : D ⊓ centralizer ({t * w} : Set G) ≤ K) :
    ∃ H : Subgroup G, H ≤ centralizer ({t * w} : Set G) ∧
      H ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) ∧
      Odd (Nat.card H) ∧ D ⊓ centralizer ({t * w} : Set G) ≤ H ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
        (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x) ∧
      ∀ X : Subgroup G, X ≤ U₁ ⊓ centralizer ({t * w} : Set G) →
        (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
          X = ⊥ ∨ X = U₁ ⊓ centralizer ({t * w} : Set G) := by
  obtain ⟨H, hEH, hHK, hHN, hHodd, hHab, -, hHirr⟩ :=
    hB G K p n hpn hK _ hFK _ hDK hW.gmg_D_le_normalizer_F hW.gmg_odd_card_D_inf
  refine ⟨H, hHK.trans hKI, hHN, hHodd, hEH, ?_, fun X hXF hXH _ => hHirr X hXF hXH⟩
  intro h₁ hh₁ h₂ hh₂ x _
  have e : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = 1 := by
    rw [hHab h₁ hh₁ h₂ hh₂]
    group
  rw [e]
  group

theorem gmg_layer_of_case_two (hB : PSL2BorelInput) {K₁ E₁ : Subgroup G} {p n : ℕ}
    [Fact p.Prime] (hpn : p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5))
    (hK₁ : Nonempty (K₁ ≃* PSL(2, GaloisField p n)))
    (hK₁I : K₁ ≤ centralizer ({t * w} : Set G))
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₁, a * (t * b * t⁻¹) = t * b * t⁻¹ * a)
    (hT₁ : IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁) K₁)
    (hdec : ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
      ∃ x₁ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁,
        ∃ x₂ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁, x = x₁ * (t * x₂ * t⁻¹))
    (hE₁K : E₁ ≤ K₁)
    (hE₁N : E₁ ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁ : Subgroup G) : Set G))
    (hE₁odd : Odd (Nat.card E₁))
    (hDE : ∀ e ∈ D ⊓ centralizer ({t * w} : Set G),
      ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, e = e₁ * (t * e₂ * t⁻¹)) :
    ∃ H : Subgroup G, H ≤ centralizer ({t * w} : Set G) ∧
      H ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) ∧
      Odd (Nat.card H) ∧ D ⊓ centralizer ({t * w} : Set G) ≤ H ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
        (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x) ∧
      ∀ X : Subgroup G, X ≤ U₁ ⊓ centralizer ({t * w} : Set G) →
        (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
          X = ⊥ ∨ X = U₁ ⊓ centralizer ({t * w} : Set G) := by
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  set T₁ := F ⊓ K₁ with hT₁def
  obtain ⟨H₁, hEH₁, hH₁K, hH₁N, hH₁odd, hH₁ab, hH₁fix, hH₁irr⟩ :=
    hB G K₁ p n hpn hK₁ T₁ hT₁ E₁ hE₁K hE₁N hE₁odd
  have htinv := hW.gmg_t_inv
  have htI := hW.gmg_t_mem_I
  have htt : t * t = 1 := by rw [← sq]; exact hW.step.start.sq_eq_one
  set H₂ := H₁.map (MulAut.conj t).toMonoidHom with hH₂def
  have hmemH₂ : ∀ {y : G}, y ∈ H₂ ↔ ∃ h ∈ H₁, t * h * t⁻¹ = y := by
    intro y
    simp only [hH₂def, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hconjH₂ : ∀ h ∈ H₁, t * h * t⁻¹ ∈ H₂ := fun h hh => hmemH₂.mpr ⟨h, hh, rfl⟩
  have h12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := hmemH₂.mp hb
    exact hcomm a (hH₁K ha) c (hH₁K hc)
  have h22 : ∀ a ∈ H₂, ∀ b ∈ H₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := hmemH₂.mp ha
    obtain ⟨b', hb', rfl⟩ := hmemH₂.mp hb
    calc t * a' * t⁻¹ * (t * b' * t⁻¹) = t * (a' * b') * t⁻¹ := by group
      _ = t * (b' * a') * t⁻¹ := by rw [hH₁ab a' ha' b' hb']
      _ = t * b' * t⁻¹ * (t * a' * t⁻¹) := by group
  set H := H₁ ⊔ H₂ with hHdef
  have hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := gmg_sup_comm hH₁ab h22 h12
  have htF : ∀ x ∈ F, t * x * t⁻¹ ∈ F := fun x hx => hW.gmg_t_conj_F hx
  have htF' : ∀ x ∈ F, t⁻¹ * x * t ∈ F := fun x hx => by
    have := htF x hx
    rw [htinv] at this ⊢
    exact this
  have hH₁F : ∀ h ∈ H₁, ∀ x ∈ F, h * x * h⁻¹ ∈ F := by
    intro h hh x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec x hx
    have hc : h * (t * x₂ * t⁻¹) = t * x₂ * t⁻¹ * h := hcomm h (hH₁K hh) x₂ (mem_inf.mp hx₂).2
    have e2 : h * (t * x₂ * t⁻¹) * h⁻¹ = t * x₂ * t⁻¹ := by rw [hc, mul_inv_cancel_right]
    have e1 : h * (x₁ * (t * x₂ * t⁻¹)) * h⁻¹ =
        (h * x₁ * h⁻¹) * (h * (t * x₂ * t⁻¹) * h⁻¹) := by group
    rw [e1, e2]
    exact mul_mem (mem_inf.mp ((mem_normalizer_iff.mp (hH₁N hh) x₁).mp hx₁)).1
      (htF x₂ (mem_inf.mp hx₂).1)
  have hH₁N' : H₁ ≤ normalizer (F : Set G) := fun h hh =>
    gmg_mem_normalizer (hH₁F h hh) (fun x hx => by
      have := hH₁F h⁻¹ (inv_mem hh) x hx
      rwa [inv_inv] at this)
  have hH₂N' : H₂ ≤ normalizer (F : Set G) := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hmemH₂.mp hy
    refine gmg_mem_normalizer (fun x hx => ?_) (fun x hx => ?_)
    · rw [show t * h * t⁻¹ * x * (t * h * t⁻¹)⁻¹ = t * (h * (t⁻¹ * x * t) * h⁻¹) * t⁻¹ by group]
      exact htF _ (hH₁F h hh _ (htF' x hx))
    · rw [show (t * h * t⁻¹)⁻¹ * x * (t * h * t⁻¹) = t * (h⁻¹ * (t⁻¹ * x * t) * h⁻¹⁻¹) * t⁻¹ by
        group]
      exact htF _ (hH₁F h⁻¹ (inv_mem hh) _ (htF' x hx))
  refine ⟨H, sup_le (hH₁K.trans hK₁I) ?_, sup_le hH₁N' hH₂N', ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hmemH₂.mp hy
    exact mul_mem (mul_mem htI (hK₁I (hH₁K hh))) (inv_mem htI)
  ·
    have hH₂H₁ : H₂ ≤ normalizer (H₁ : Set G) := fun b hb =>
      gmg_mem_normalizer (fun a ha => by rw [← h12 a ha b hb, mul_inv_cancel_right]; exact ha)
        (fun a ha => by
          rw [show b⁻¹ * a * b = b⁻¹ * (a * b) by group, h12 a ha b hb, ← mul_assoc,
            inv_mul_cancel, one_mul]
          exact ha)
    have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hH₂H₁
    have hH₂card : Nat.card H₂ = Nat.card H₁ :=
      card_map_of_injective (MulAut.conj t).injective
    have hdvd : Nat.card H ∣ Nat.card H₁ * Nat.card H₂ := Dvd.intro _ hcard
    rw [hH₂card] at hdvd
    exact Odd.of_dvd_nat (hH₁odd.mul hH₁odd) hdvd
  ·
    intro e he
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hDE e he
    exact mul_mem (mem_sup_left (hEH₁ he₁)) (mem_sup_right (hconjH₂ e₂ (hEH₁ he₂)))
  ·
    intro h₁ hh₁ h₂ hh₂ x _
    have e : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = 1 := by
      rw [hHab h₁ hh₁ h₂ hh₂]
      group
    rw [e]
    group
  ·
    intro X hXF hXH hXt
    by_cases hX : X = ⊥
    · exact Or.inl hX
    right
    have key : ∀ y ∈ X, y ∈ T₁ → y ≠ 1 → X = F := by
      intro y hyX hyT hy1
      have hinv : ∀ h ∈ H₁, ∀ z ∈ X ⊓ T₁, h * z * h⁻¹ ∈ X ⊓ T₁ := fun h hh z hz =>
        mem_inf.mpr ⟨hXH h (mem_sup_left hh) z (mem_inf.mp hz).1,
          (mem_normalizer_iff.mp (hH₁N hh) z).mp (mem_inf.mp hz).2⟩
      rcases hH₁irr (X ⊓ T₁) inf_le_right hinv with h0 | hT
      · exact absurd (by rw [← mem_bot, ← h0]; exact mem_inf.mpr ⟨hyX, hyT⟩) hy1
      · have hT₁X : T₁ ≤ X := hT ▸ inf_le_left
        refine le_antisymm hXF fun z hz => ?_
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hdec z hz
        exact mul_mem (hT₁X hz₁) (hXt _ (hT₁X hz₂))
    obtain ⟨x, hxX, hx1⟩ := (Subgroup.bot_or_exists_ne_one X).resolve_left hX
    obtain ⟨x₁, hx₁, x₂, hx₂, hxe⟩ := hdec x (hXF hxX)
    by_cases h1 : x₁ = 1
    ·
      have e : t * x * t⁻¹ = x₂ := by
        rw [hxe, h1, one_mul, htinv]
        calc t * (t * x₂ * t) * t = (t * t) * x₂ * (t * t) := by group
          _ = x₂ := by rw [htt, one_mul, mul_one]
      refine key x₂ (e ▸ hXt x hxX) hx₂ fun h2 => hx1 ?_
      rw [hxe, h1, h2]
      group
    ·
      have hmove : ∃ h ∈ H₁, h * x₁ * h⁻¹ ≠ x₁ := by
        by_contra hno
        push Not at hno
        exact h1 (hH₁fix x₁ hx₁ hno)
      obtain ⟨h, hh, hhx⟩ := hmove
      have hc : h * (t * x₂ * t⁻¹) = t * x₂ * t⁻¹ * h :=
        hcomm h (hH₁K hh) x₂ (mem_inf.mp hx₂).2
      have e2 : h * (t * x₂ * t⁻¹) * h⁻¹ = t * x₂ * t⁻¹ := by rw [hc, mul_inv_cancel_right]
      have e : h * x * h⁻¹ * x⁻¹ = h * x₁ * h⁻¹ * x₁⁻¹ := by
        have e1 : h * (x₁ * (t * x₂ * t⁻¹)) * h⁻¹ * (x₁ * (t * x₂ * t⁻¹))⁻¹ =
            (h * x₁ * h⁻¹) * (h * (t * x₂ * t⁻¹) * h⁻¹) * (t * x₂ * t⁻¹)⁻¹ * x₁⁻¹ := by group
        rw [hxe, e1, e2]
        group
      refine key (h * x * h⁻¹ * x⁻¹)
        (mul_mem (hXH h (mem_sup_left hh) x hxX) (inv_mem hxX)) ?_ ?_
      · rw [e]
        exact mul_mem ((mem_normalizer_iff.mp (hH₁N hh) x₁).mp hx₁) (inv_mem hx₁)
      · rw [e]
        intro h0
        exact hhx (mul_inv_eq_one.mp h0)

end U3C1OuterSwapHigh

theorem u3C1GmsLayerInput_of_ident (hB : PSL2BorelInput) (hI : U3C1GmgIdentInput) :
    U3C1GmsLayerInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW h1 h2 h3 h4 h5 J hJ1 hJ2 hJ3 hJ4
  rcases hI G L f t T R₂ D d V U U₁ w s P hW h1 h2 h3 h4 h5 J hJ1 hJ2 hJ3 hJ4 with
    ⟨K, p, n, hp, hpn, hK, hKI, hFK, hDK⟩ |
      ⟨K₁, E₁, p, n, hp, hpn, hK₁, hK₁I, hcomm, hT₁, hdec, hE₁K, hE₁N, hE₁odd, hDE⟩
  · exact hW.gmg_layer_of_case_one hB hpn hK hKI hFK hDK
  · exact hW.gmg_layer_of_case_two hB hpn hK₁ hK₁I hcomm hT₁ hdec hE₁K hE₁N hE₁odd hDE

end CFSG.SeitzReduction.RankOne
