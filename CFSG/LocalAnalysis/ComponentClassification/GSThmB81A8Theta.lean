module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Model
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2019

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}
  {M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8}

theorem map_JB (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8)))
    (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup)
    (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    (h.JB.subgroupOf h.M3).map (rhoHat H₁ M) = QL8.originalSubgroup := by
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by rw [hP, hA]; exact cent_triv
  have hL : ⁅M.P ⊓ centralizer ({(M.Φ H₁.kloc.rhoA : P8)} : Set P8),
      M.P ⊓ centralizer ({(M.Φ H₁.kloc.rhoA : P8)} : Set P8)⁆ = QL8.originalSubgroup := by
    rw [hP, hΦ]; exact commutator_C0
  have hL0 := (l0_of_model M hPA hcent H₁.kloc.rhoA QL8.originalSubgroup hL card_QL8
    L_oddNormal).1
  have hmap : (Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA).map M.ι =
      QL8.originalSubgroup := by
    rw [Cat8.L0, map_commutator, map_innFix M hPA hcent, hL]
  have hker := H₁.kloc.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hle : (h.JB.subgroupOf h.M3).map H₁.kloc.rho ≤
      Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA := by
    rw [← H₁.kloc.commutator_JB_subgroupOf, map_commutator]
    exact commutator_mono H₁.kloc.map_JB_le_innFix H₁.kloc.map_JB_le_innFix
  have h1 := card_quotient_dvd_card_map H₁.kloc.rho hker (h.JB.subgroupOf h.M3)
  let e2 : h.JB ≃* h.JB.subgroupOf h.M3 := (subgroupOfEquivOfLe H₁.kloc.JB_le_M3).symm
  let e3 : h.JB ⧸ pPrimeCore 2 h.JB ≃* (h.JB.subgroupOf h.M3) ⧸
      pPrimeCore 2 (h.JB.subgroupOf h.M3) :=
    QuotientGroup.congr (pPrimeCore 2 h.JB) (pPrimeCore 2 (h.JB.subgroupOf h.M3)) e2
      (pPrimeCore_map_iso 2 e2)
  rw [← Nat.card_congr e3.toEquiv, h.card_JB_quotient, card_Jbar H₁ hA8] at h1
  have heq : (h.JB.subgroupOf h.M3).map H₁.kloc.rho =
      Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA :=
    eq_of_le_of_card_ge hle (by rw [hL0]; exact Nat.le_of_dvd Nat.card_pos h1)
  rw [show rhoHat H₁ M = M.ι.comp H₁.kloc.rho from rfl, ← Subgroup.map_map, heq, hmap]

theorem tau_mem_normalizer_JB {d : H₁.Data} :
    (⟨d.tau, d.tau_mem.2⟩ : ↥h.M3) ∈
      normalizer ((h.JB.subgroupOf h.M3 : Subgroup ↥h.M3) : Set ↥h.M3) := by
  refine mem_normalizer_subgroupOf_of_inf d.tau_mem.2 ?_
  rw [inf_eq_left.mpr H₁.kloc.JB_le_M3]
  exact GSLit.mem_normalizer_fixedLayer (h.toHyp52.S_le_normalizer d.tau_mem_S)
    (mem_inf.mp d.tau_mem_Q).2

theorem map_JB_inf_centralizer (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) {d : H₁.Data}
    (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup)
    (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    ((h.JB ⊓ centralizer ({d.tau} : Set H)).subgroupOf h.M3).map (rhoHat H₁ M) =
      QL8.originalSubgroup ⊓ centralizer ({psi M ⟨d.tau, le_normalizer d.tau_K⟩} : Set P8) := by
  set τM : ↥h.M3 := ⟨d.tau, d.tau_mem.2⟩ with hτM
  have hτ2 : τM * τM = 1 := Subtype.ext d.tau_sq
  have key := OddQuot.map_inf_centralizer (rhoHat H₁ M) (isPGroup_zpowers_of_mul_self hτ2)
    (zpowers_le.mpr (tau_mem_normalizer_JB (d := d)))
    (OddQuot.not_two_dvd_card_ker_domRestrict _ (not_two_dvd_card_ker_rhoHat hCF1 hCF2) _)
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq,
    map_JB hCF1 hCF2 hA8 hP hA hΦ] at key
  have hsub : (h.JB ⊓ centralizer ({d.tau} : Set H)).subgroupOf h.M3 =
      h.JB.subgroupOf h.M3 ⊓ centralizer ({τM} : Set ↥h.M3) := by
    ext m
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, hτM]
    exact ⟨fun h1 => ⟨h1.1, Subtype.ext h1.2⟩, fun h1 => ⟨h1.1, congrArg Subtype.val h1.2⟩⟩
  rw [hsub, key, rhoHat_eq_psi]

theorem mem_sup_of_mem_four {e₁ e₂ u : P8} (hu : u ∈ four e₁ e₂) :
    u ∈ zpowers e₁ ⊔ zpowers e₂ := by
  simp only [four, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mem_sup_left (mem_zpowers _)
  · exact mem_sup_right (mem_zpowers _)
  · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem mem_normalizer_sup {G : Type} [Group G] [Finite G] {e₁ e₂ c : G} (he₁ : e₁ * e₁ = 1)
    (he₂ : e₂ * e₂ = 1) (hc : e₁ * e₂ = e₂ * e₁) (h1 : c * e₁ * c⁻¹ ∈ zpowers e₁ ⊔ zpowers e₂)
    (h2 : c * e₂ * c⁻¹ ∈ zpowers e₁ ⊔ zpowers e₂) :
    c ∈ normalizer ((zpowers e₁ ⊔ zpowers e₂ : Subgroup G) : Set G) := by
  have hcomm : ∀ x ∈ zpowers e₁, ∀ y ∈ zpowers e₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hc i j).eq
  have h3 := Eight.mem_normalizer_of_conj_mem (C := zpowers e₁ ⊔ zpowers e₂) (s := c⁻¹)
    fun x hx => by
      rw [inv_inv]
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hcomm hx
      rw [show c * (x₁ * x₂) * c⁻¹ = (c * x₁ * c⁻¹) * (c * x₂ * c⁻¹) by group]
      refine mul_mem ?_ ?_
      · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self he₁ hx₁ with rfl | rfl
        · rw [mul_one, mul_inv_cancel]; exact one_mem _
        · exact h1
      · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self he₂ hx₂ with rfl | rfl
        · rw [mul_one, mul_inv_cancel]; exact one_mem _
        · exact h2
  simpa using inv_mem h3

theorem exists_theta0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) {d : H₁.Data}
    (F : d.Facts) (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup)
    (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    ∃ e₁ e₂ θ₀ : H, e₁ ∈ h.D ∧ e₂ ∈ h.D ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧
      e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧ θ₀ ∈ h.JB ∧ θ₀ * d.tau = d.tau * θ₀ ∧
      θ₀ * e₁ * θ₀⁻¹ = e₂ ∧ θ₀ * e₂ * θ₀⁻¹ = e₁ * e₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := not_two_dvd_card_ker_rhoHat (H₁ := H₁) (M := M) hCF1 hCF2
  set t := psi M ⟨d.tau, le_normalizer d.tau_K⟩ with ht
  obtain ⟨θh, eh₁, eh₂, hθL, he₁L, he₂L, hθt, he₁t, he₂t, hθ₁, hθ₂, he₁₁, he₂₂, he₁₂, he₁1,
    he₂1, hne, hcard, hnorm⟩ := exists_three_cycle (psi_tau_mem hCF1 hCF2 F hP hA hΦ)
  set C4 : Subgroup P8 := QL8.originalSubgroup ⊓ centralizer ({t} : Set P8) with hC4
  set Eh : Subgroup P8 := zpowers eh₁ ⊔ zpowers eh₂ with hEh
  have hEhC : Eh ≤ C4 := sup_le (zpowers_le.mpr ⟨he₁L, mem_centralizer_singleton_iff.mpr he₁t⟩)
    (zpowers_le.mpr ⟨he₂L, mem_centralizer_singleton_iff.mpr he₂t⟩)
  have hC4N : C4 ≤ normalizer (Eh : Set P8) := fun c hc =>
    mem_normalizer_sup he₁₁ he₂₂ he₁₂
      (mem_sup_of_mem_four (hnorm c hc.1 (mem_centralizer_singleton_iff.mp hc.2)).1)
      (mem_sup_of_mem_four (hnorm c hc.1 (mem_centralizer_singleton_iff.mp hc.2)).2)
  obtain ⟨hEh4, -⟩ := card_sup_zpowers_of_inv he₁₁ he₂₂ he₁1 he₂1 hne he₁₂
  have hEh2 : IsPGroup 2 Eh := IsPGroup.of_card (n := 2) (by rw [hEh4]; norm_num)
  set D' : Subgroup ↥h.M3 := h.D.subgroupOf h.M3 with hD'
  have hD2 : IsPGroup 2 D' :=
    ((Six.isPGroup_S h.toHyp52).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  have hcD : Nat.card (D'.map (rhoHat H₁ M)) = 8 := by
    rw [Eight.card_map_of_isPGroup hker hD2, hD', Six.card_subgroupOf_eq,
      inf_eq_left.mpr H₁.kloc.D_le_M3, card_D hCF1 hCF2 F hA hΦ]
  have hDC : D'.map (rhoHat H₁ M) ≤ C4 := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [← map_JB hCF1 hCF2 hA8 hP hA hΦ]
      exact mem_map_of_mem _ (h.D_le_JB hm)
    · rw [ht, rhoHat_eq_psi, ← map_mul, ← map_mul]
      exact congrArg (psi M) (Subtype.ext (d.D_comm_tau F hm).symm)
  have hEhD : Eh ≤ D'.map (rhoHat H₁ M) := by
    have hX : IsPGroup 2 ↥(D'.map (rhoHat H₁ M) ⊔ Eh) :=
      IsPGroup.to_sup_of_normal_right' (hD2.map _) hEh2 (hDC.trans hC4N)
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hdvd := card_dvd_of_le (sup_le hDC hEhC)
    rw [hcard, hn] at hdvd
    have h8 : 2 ^ n ∣ 2 ^ 3 :=
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right
        (by simpa using hdvd)
    have heq : D'.map (rhoHat H₁ M) = D'.map (rhoHat H₁ M) ⊔ Eh :=
      eq_of_le_of_card_ge le_sup_left (by rw [hn, hcD]; exact Nat.le_of_dvd (by norm_num) h8)
    rw [heq]
    exact le_sup_right
  obtain ⟨m₁, hm₁, hm₁e⟩ := mem_map.mp (hEhD (mem_sup_left (mem_zpowers eh₁)))
  obtain ⟨m₂, hm₂, hm₂e⟩ := mem_map.mp (hEhD (mem_sup_right (mem_zpowers eh₂)))
  have hinj := Eight.injOn_of_isPGroup hker hD2
  have hm₁₁ : m₁ * m₁ = 1 :=
    hinj (mul_mem hm₁ hm₁) (one_mem _) (by rw [map_mul, hm₁e, he₁₁, map_one])
  have hm₂₂ : m₂ * m₂ = 1 :=
    hinj (mul_mem hm₂ hm₂) (one_mem _) (by rw [map_mul, hm₂e, he₂₂, map_one])
  have hm₁₂ : m₁ * m₂ = m₂ * m₁ :=
    hinj (mul_mem hm₁ hm₂) (mul_mem hm₂ hm₁) (by rw [map_mul, map_mul, hm₁e, hm₂e, he₁₂])
  set G₁ : Subgroup ↥h.M3 := (h.JB ⊓ centralizer ({d.tau} : Set H)).subgroupOf h.M3 with hG₁
  have hDG : ∀ m ∈ D', m ∈ G₁ := fun m hm =>
    ⟨h.D_le_JB hm, mem_centralizer_singleton_iff.mpr (d.D_comm_tau F hm).symm⟩
  set φ₁ := (rhoHat H₁ M).domRestrict G₁ with hφ₁
  have hker₁ : ¬ 2 ∣ Nat.card φ₁.ker := OddQuot.not_two_dvd_card_ker_domRestrict _ hker G₁
  set f₁ : ↥G₁ := ⟨m₁, hDG m₁ hm₁⟩
  set f₂ : ↥G₁ := ⟨m₂, hDG m₂ hm₂⟩
  have hf₁ : f₁ * f₁ = 1 := Subtype.ext hm₁₁
  have hf₂ : f₂ * f₂ = 1 := Subtype.ext hm₂₂
  have hf₁1 : f₁ ≠ 1 := fun h1 => he₁1 (by rw [← hm₁e, show m₁ = 1 from congrArg Subtype.val h1,
    map_one])
  have hf₂1 : f₂ ≠ 1 := fun h1 => he₂1 (by rw [← hm₂e, show m₂ = 1 from congrArg Subtype.val h1,
    map_one])
  have hf₁₂ : f₁ ≠ f₂ := fun h1 => hne (by rw [← hm₁e, ← hm₂e,
    show m₁ = m₂ from congrArg Subtype.val h1])
  obtain ⟨hE₁4, -⟩ := card_sup_zpowers_of_inv hf₁ hf₂ hf₁1 hf₂1 hf₁₂ (Subtype.ext hm₁₂)
  have hE₁2 : IsPGroup 2 ↥(zpowers f₁ ⊔ zpowers f₂) :=
    IsPGroup.of_card (n := 2) (by rw [hE₁4]; norm_num)
  have hE₁map : (zpowers f₁ ⊔ zpowers f₂).map φ₁ = Eh := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hφ₁,
      MonoidHom.domRestrict_apply, MonoidHom.domRestrict_apply]
    exact congrArg₂ (fun x y => zpowers x ⊔ zpowers y) hm₁e hm₂e
  have hθran : θh ∈ φ₁.range := by
    rw [hφ₁, MonoidHom.domRestrict_range, hG₁, map_JB_inf_centralizer hCF1 hCF2 hA8 hP hA hΦ]
    exact ⟨hθL, mem_centralizer_singleton_iff.mpr hθt⟩
  have hθN : θh ∈ normalizer (((zpowers f₁ ⊔ zpowers f₂).map φ₁ : Subgroup P8) : Set P8) := by
    rw [hE₁map]
    exact hC4N ⟨hθL, mem_centralizer_singleton_iff.mpr hθt⟩
  obtain ⟨x, hxN, hxθ⟩ := mem_map.mp
    ((Eight.map_normalizer_eq hker₁ hE₁2).ge (mem_inf.mpr ⟨hθran, hθN⟩))
  have hED : zpowers f₁ ⊔ zpowers f₂ ≤ D'.comap G₁.subtype :=
    sup_le (zpowers_le.mpr hm₁) (zpowers_le.mpr hm₂)
  have hconj : ∀ f ∈ zpowers f₁ ⊔ zpowers f₂, ((x * f * x⁻¹ : ↥G₁) : ↥h.M3) ∈ D' :=
    fun f hf => hED ((mem_normalizer_iff.mp hxN f).mp hf)
  have hxD : ∀ f ∈ zpowers f₁ ⊔ zpowers f₂, ∀ m ∈ D',
      φ₁ (x * f * x⁻¹) = rhoHat H₁ M m → ((x * f * x⁻¹ : ↥G₁) : ↥h.M3) = m :=
    fun f hf m hm hfm => hinj (hconj f hf) hm hfm
  have hφx : φ₁ x = θh := hxθ
  have hx₁ := hxD f₁ (mem_sup_left (mem_zpowers _)) m₂ hm₂ (by
    rw [map_mul, map_mul, map_inv, hφx, hφ₁, MonoidHom.domRestrict_apply, hm₁e, hm₂e, hθ₁])
  have hx₂ := hxD f₂ (mem_sup_right (mem_zpowers _)) (m₁ * m₂) (mul_mem hm₁ hm₂) (by
    rw [map_mul, map_mul, map_inv, hφx, hφ₁, MonoidHom.domRestrict_apply, map_mul, hm₁e, hm₂e,
      hθ₂])
  refine ⟨(m₁ : H), (m₂ : H), (((x : ↥h.M3) : H)), hm₁, hm₂, congrArg Subtype.val hm₁₁,
    congrArg Subtype.val hm₂₂, congrArg Subtype.val hm₁₂, fun h1 => hf₁1 (Subtype.ext
      (Subtype.ext h1)), fun h1 => hf₂1 (Subtype.ext (Subtype.ext h1)), fun h1 => hf₁₂
      (Subtype.ext (Subtype.ext h1)), (mem_inf.mp x.2).1,
    mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2, ?_, ?_⟩
  · exact congrArg Subtype.val hx₁
  · exact congrArg Subtype.val hx₂

end CFSG.ComponentClassification.GSThmB.A8
