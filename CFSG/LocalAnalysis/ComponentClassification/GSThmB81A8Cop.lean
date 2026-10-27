module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Theta
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2019

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8

theorem exists_mem_centralizer_of_kernel {G : Type} [Group G] [Finite G] {J X P : Subgroup G}
    (hZ : center (J ⧸ pPrimeCore 2 J) = ⊥) (hXJ : X ≤ J) (hP : IsPGroup 2 P)
    (hPX : P ≤ normalizer (X : Set G)) (hPJ : P ≤ coreActionKernel J) {x : G} (hx : x ∈ X) :
    ∃ y ∈ X, (∀ π ∈ P, y * π = π * y) ∧ y⁻¹ * x ∈ (pPrimeCore 2 J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (J : Set G) with hN
  set φ := Eight.oddBarAction J with hφ
  have hXN : X ≤ N := hXJ.trans le_normalizer
  have hPN : P ≤ N := fun π hπ => (mem_coreActionKernel.mp (hPJ hπ)).1
  set Y : Subgroup ↥N := X.subgroupOf N with hY
  set E : Subgroup ↥N := P.subgroupOf N with hE
  have hE2 : IsPGroup 2 E := hP.comap_subtype
  have hEY : E ≤ normalizer (Y : Set ↥N) := by
    intro e he
    have h1 : (e : G) ∈ normalizer ((X ⊓ N : Subgroup G) : Set G) := by
      rw [inf_eq_left.mpr hXN]
      exact hPX he
    exact mem_normalizer_subgroupOf_of_inf e.2 h1
  have hO : Odd (Nat.card ((pPrimeCore 2 J).map J.subtype)) :=
    UnbalancedGS.odd_card_map_pPrimeCore_two J
  have hkerO : ∀ y : ↥N, (y : G) ∈ X → φ y = 1 → (y : G) ∈ (pPrimeCore 2 J).map J.subtype :=
    fun y hyX hy1 => inf_coreActionKernel_le_of_center_eq_bot hZ
      (mem_inf.mpr ⟨hXJ hyX, Eight.mem_ker_oddBarAction.mp hy1⟩)
  have hker : ¬ 2 ∣ Nat.card (φ.domRestrict Y).ker := by
    set f : ↥Y →* G := N.subtype.comp Y.subtype with hf
    have hfi : Function.Injective f := N.subtype_injective.comp Y.subtype_injective
    have hle : (φ.domRestrict Y).ker.map f ≤ (pPrimeCore 2 J).map J.subtype := by
      rintro _ ⟨k, hk, rfl⟩
      exact hkerO k k.2 hk
    have hd := card_dvd_of_le hle
    rw [card_map_of_injective hfi] at hd
    intro h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h2.trans hd))
  have key := OddQuot.map_inf_centralizer φ hE2 hEY hker
  have hxY : (⟨x, hXN hx⟩ : ↥N) ∈ Y := hx
  have hmem : φ ⟨x, hXN hx⟩ ∈ Y.map φ ⊓ centralizer ((E.map φ : Subgroup _) : Set _) := by
    refine mem_inf.mpr ⟨mem_map_of_mem φ hxY, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have he1 : φ e = 1 := by
      rw [← MonoidHom.mem_ker, Eight.mem_ker_oddBarAction]
      exact hPJ he
    rw [he1, one_mul, mul_one]
  rw [← key] at hmem
  obtain ⟨y, ⟨hyY, hyC⟩, hyx⟩ := mem_map.mp hmem
  have hyX : (y : G) ∈ X := hyY
  refine ⟨(y : G), hyX, fun π hπ => ?_, ?_⟩
  · have h1 := mem_centralizer_iff.mp hyC ⟨π, hPN hπ⟩ hπ
    exact (congrArg Subtype.val h1).symm
  · have h1 : φ (y⁻¹ * ⟨x, hXN hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    exact hkerO _ (mul_mem (inv_mem hyX) hx) h1

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}

theorem exists_theta (I : In81)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) {d : H₁.Data}
    (F : d.Facts) (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) :
    ∃ e₁ e₂ θ : H, e₁ ∈ h.D ∧ e₂ ∈ h.D ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧
      e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧ θ * (h.a * d.sigma) = h.a * d.sigma * θ ∧
      (∀ π ∈ h.P, θ * π = π * θ) ∧ Odd (orderOf θ) ∧
      θ * e₁ * θ⁻¹ = e₂ ∧ θ * e₂ * θ⁻¹ = e₁ * e₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hP, hA, hΦ⟩ := exists_model H₁ I.cf1 I.cf2 hA8
  obtain ⟨e₁, e₂, θ₀, he₁D, he₂D, he₁₁, he₂₂, he₁₂, he₁1, he₂1, hne, hθJB, hθτ, hθ₁, hθ₂⟩ :=
    exists_theta0 (M := M) I.cf1 I.cf2 hA8 F hP hA hΦ
  set E : Subgroup H := zpowers e₁ ⊔ zpowers e₂ with hE
  set X : Subgroup H :=
    h.J ⊓ centralizer ({h.a * d.sigma} : Set H) ⊓ normalizer (E : Set H) with hX
  obtain ⟨hE4, -⟩ := card_sup_zpowers_of_inv he₁₁ he₂₂ he₁1 he₂1 hne he₁₂
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hEJ : E ≤ h.J := sup_le (zpowers_le.mpr he₁D.2) (zpowers_le.mpr he₂D.2)
  have he₂E : e₂ ∈ E := mem_sup_right (mem_zpowers e₂)
  have he₁₂E : e₁ * e₂ ∈ E := mul_mem (mem_sup_left (mem_zpowers e₁)) he₂E
  obtain ⟨hθ₀J, hθ₀B⟩ := mem_inf.mp ((GSLit.fixedLayer_le_inf h.J h.B) hθJB)
  have hθ₀a : θ₀ * h.a = h.a * θ₀ := mem_centralizer_singleton_iff.mp (h.J_le hθ₀J)
  have hθ₀b : θ₀ * d.b = d.b * θ₀ :=
    (mem_centralizer_iff.mp hθ₀B d.b (d.B_eq ▸ mem_zpowers d.b)).symm
  have hθ₀X : θ₀ ∈ X := by
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hθ₀J, mem_centralizer_singleton_iff.mpr ?_⟩,
      mem_normalizer_sup he₁₁ he₂₂ he₁₂ (by rw [hθ₁]; exact he₂E) (by rw [hθ₂]; exact he₁₂E)⟩
    show θ₀ * (h.a * (d.tau * d.b)) = h.a * (d.tau * d.b) * θ₀
    rw [← mul_assoc, hθ₀a, mul_assoc, ← mul_assoc θ₀, hθτ, mul_assoc, hθ₀b]
    group
  have hPX : h.P ≤ normalizer (X : Set H) := by
    refine le_normalizer_of_conj fun π hπ w hw => ?_
    obtain ⟨⟨hwJ, hwC⟩, hwN⟩ := mem_inf.mp hw |>.imp mem_inf.mp id
    have hπC : π * (h.a * d.sigma) = h.a * d.sigma * π := by
      rw [← mul_assoc, h.toHyp52.comm_a (mem_inf.mp hπ).1, mul_assoc,
        ← Hyp59.L81Hyp.Data.sigma_comm_P I F h3 hπ, ← mul_assoc]
    have hπE : π ∈ normalizer (E : Set H) := mem_normalizer_sup he₁₁ he₂₂ he₁₂
      (by rw [← H₁.D_comm_P he₁D hπ, mul_inv_cancel_right]; exact mem_sup_left (mem_zpowers _))
      (by rw [← H₁.D_comm_P he₂D hπ, mul_inv_cancel_right]; exact he₂E)
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_normalizer_iff.mp
      (h.toHyp52.S_le_normalizer (mem_inf.mp hπ).1) w).mp hwJ, ?_⟩,
      mul_mem (mul_mem hπE hwN) (inv_mem hπE)⟩
    have hwC' := mem_centralizer_singleton_iff.mp hwC
    rw [mem_centralizer_singleton_iff]
    calc π * w * π⁻¹ * (h.a * d.sigma) = π * w * (π⁻¹ * (h.a * d.sigma)) := by group
      _ = π * w * ((h.a * d.sigma) * π⁻¹) := by
          rw [show π⁻¹ * (h.a * d.sigma) = (h.a * d.sigma) * π⁻¹ by
            rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hπC, inv_mul_cancel_left]]
      _ = π * (w * (h.a * d.sigma)) * π⁻¹ := by group
      _ = π * ((h.a * d.sigma) * w) * π⁻¹ := by rw [hwC']
      _ = (π * (h.a * d.sigma)) * w * π⁻¹ := by group
      _ = h.a * d.sigma * (π * w * π⁻¹) := by rw [hπC]; group
  obtain ⟨θ₁, hθ₁X, hθ₁P, hn⟩ := exists_mem_centralizer_of_kernel H₁.center_J
    (inf_le_left.trans inf_le_left) ((Six.isPGroup_S h.toHyp52).to_le inf_le_left) hPX
    inf_le_right hθ₀X
  set n := θ₁⁻¹ * θ₀ with hndef
  have hnX : n ∈ X := mul_mem (inv_mem hθ₁X) hθ₀X
  have hnE : ∀ x ∈ E, n * x * n⁻¹ = x := by
    intro x hx
    have hxJ := hEJ hx
    have h1 : n * x * n⁻¹ * x⁻¹ ∈ E :=
      mul_mem ((mem_normalizer_iff.mp hnX.2 x).mp hx) (inv_mem hx)
    have h2 : n * x * n⁻¹ * x⁻¹ ∈ (pPrimeCore 2 h.J).map h.J.subtype := by
      rw [show n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) by group]
      have hxO := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J
        (pPrimeCore 2 h.J) (le_normalizer hxJ)
      exact mul_mem hn ((mem_normalizer_iff.mp hxO _).mp (inv_mem hn))
    have h3' := eq_bot_of_le_two_group_of_le_odd hE2
      (UnbalancedGS.odd_card_map_pPrimeCore_two h.J) (inf_le_left :
        E ⊓ (pPrimeCore 2 h.J).map h.J.subtype ≤ E) inf_le_right
    have h4 : n * x * n⁻¹ * x⁻¹ = 1 := by
      have := mem_inf.mpr ⟨h1, h2⟩
      rw [h3', mem_bot] at this
      exact this
    exact mul_inv_eq_one.mp h4
  have hθ₁₀ : θ₁ = θ₀ * n⁻¹ := by rw [hndef]; group
  have hθ₁e : ∀ x ∈ E, θ₁ * x * θ₁⁻¹ = θ₀ * x * θ₀⁻¹ := by
    intro x hx
    have h1 : n⁻¹ * x * n = x := by
      calc n⁻¹ * x * n = n⁻¹ * (n * x * n⁻¹) * n := by rw [hnE x hx]
        _ = x := by group
    rw [hθ₁₀, show θ₀ * n⁻¹ * x * (θ₀ * n⁻¹)⁻¹ = θ₀ * (n⁻¹ * x * n) * θ₀⁻¹ by group, h1]
  have hθ₁₁ : θ₁ * e₁ * θ₁⁻¹ = e₂ := by rw [hθ₁e e₁ (mem_sup_left (mem_zpowers e₁)), hθ₁]
  have hθ₁₂ : θ₁ * e₂ * θ₁⁻¹ = e₁ * e₂ := by rw [hθ₁e e₂ he₂E, hθ₂]
  obtain ⟨m, hm⟩ := exists_odd_orderOf_pow θ₁
  obtain ⟨f, hf, hf1, hf2⟩ := exists_cycle_pow_two_pow hθ₁₁ hθ₁₂ he₁₁ he₂₂ he₁₂ m
  have hθ₁C : θ₁ * (h.a * d.sigma) = h.a * d.sigma * θ₁ :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hθ₁X).1).2
  have hfD : f ∈ h.D := by rcases hf with rfl | rfl <;> [exact he₂D; exact mul_mem he₁D he₂D]
  have hfprops : f * f = 1 ∧ e₁ * f = f * e₁ ∧ f ≠ 1 ∧ e₁ ≠ f := by
    rcases hf with rfl | rfl
    · exact ⟨he₂₂, he₁₂, he₂1, hne⟩
    · refine ⟨?_, ?_, fun h1 => hne ?_, fun h1 => he₂1 ?_⟩
      · rw [show e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ by group, ← he₁₂,
          show e₁ * (e₁ * e₂) * e₂ = (e₁ * e₁) * (e₂ * e₂) by group, he₁₁, he₂₂, one_mul]
      · rw [mul_assoc e₁ e₂ e₁, ← he₁₂]
      · exact (inv_eq_of_mul_eq_one_right he₁₁).symm.trans (inv_eq_of_mul_eq_one_right h1)
      · calc e₂ = e₁⁻¹ * (e₁ * e₂) := by group
          _ = e₁⁻¹ * e₁ := by rw [← h1]
          _ = 1 := by group
  refine ⟨e₁, f, θ₁ ^ 2 ^ m, he₁D, hfD, he₁₁, hfprops.1, hfprops.2.1, he₁1, hfprops.2.2.1,
    hfprops.2.2.2, (Commute.pow_left hθ₁C (2 ^ m)).eq,
    fun π hπ => (Commute.pow_left (hθ₁P π hπ) (2 ^ m)).eq, hm, hf1, hf2⟩

end CFSG.ComponentClassification.GSThmB.A8
