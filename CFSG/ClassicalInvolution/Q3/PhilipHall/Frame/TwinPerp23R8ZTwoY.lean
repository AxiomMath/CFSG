module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8UE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Conj

variable {Q : Type} [Group Q]

theorem conj_cent_of_perm {A B : Subgroup Q} {eb : Q}
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb) (ρ : Q) :
    (∀ x ∈ A, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) ∧
      (∀ x ∈ B, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) := by
  have key : ∀ x : Q, (ρ⁻¹ * x * ρ ∈ A ∨ ρ⁻¹ * x * ρ ∈ B) →
      ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹) := by
    intro x hx
    have h1 : eb * (ρ⁻¹ * x * ρ) = (ρ⁻¹ * x * ρ) * eb := by
      rcases hx with hx | hx
      · exact heA _ hx
      · exact heB _ hx
    calc ρ * eb * ρ⁻¹ * x = ρ * (eb * (ρ⁻¹ * x * ρ)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * x * ρ) * eb) * ρ⁻¹ := by rw [h1]
      _ = x * (ρ * eb * ρ⁻¹) := by group
  have hmem : ∀ (H : Subgroup Q) (x : Q), x ∈ H → ρ⁻¹ * x * ρ ∈ conjSub ρ⁻¹ H := by
    intro H x hx
    rw [mem_conjSub_iff]
    have e : ρ⁻¹⁻¹ * (ρ⁻¹ * x * ρ) * ρ⁻¹ = x := by group
    rw [e]
    exact hx
  constructor
  · intro x hx
    apply key
    rcases hperm ρ⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
    · left; rw [← h1]; exact hmem A x hx
    · right; rw [← h1]; exact hmem A x hx
  · intro x hx
    apply key
    rcases hperm ρ⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
    · right; rw [← h1]; exact hmem B x hx
    · left; rw [← h1]; exact hmem B x hx

end Conj

section Y


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_y (hT : Thm4RTwinBelow 3 n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hTwo : P23Two n) (hα : P23Alpha n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hAE : SecAE R e 6) :
    ∃ c' : Y, c' ∈ Subgroup.centralizer ({t} : Set Y) ∧
      (c' * e * c'⁻¹) * e = e * (c' * e * c'⁻¹) ∧ c' * e * c'⁻¹ ≠ e ∧
      ∀ l ∈ tightCore R ⊔ K', (c' * e * c'⁻¹) * l * (c' * e * c'⁻¹)⁻¹ * l⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW t hd.hzW)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZ' := R56.p23_zstar_cu hT hc hZ
  have hex : ∃ ℓ ∈ C, e * ℓ * e⁻¹ * ℓ⁻¹ ∉ oddCoreOf C := by
    by_contra hcon
    exact p23_e_not_zstar hT hTwo hα hc hZ' fun ℓ hℓ => by_contra fun h => hcon ⟨ℓ, hℓ, h⟩
  obtain ⟨ℓ, hℓC, hℓ⟩ := hex
  have hΦ := p23E8Phi_of_thm4 hT hcit hP Y R S t K' W u e g hc hno (Or.inl hZ) hAE
  set eC : ↥C := ⟨e, heC⟩ with heCdef
  set ℓC : ↥C := ⟨ℓ, hℓC⟩ with hℓCdef
  set xC : ↥C := ℓC * eC * ℓC⁻¹ with hxCdef
  have hmem_gen : ∀ x : ↥C, (∃ c ∈ C, (x : Y) = c * (1 * e) * c⁻¹) → F7I.piC C x ∈ p23ABar t 1 e :=
    fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
  have heb : F7I.piC C eC ∈ p23ABar t 1 e := hmem_gen eC ⟨1, C.one_mem, by simp [eC]⟩
  have hxb : F7I.piC C xC ∈ p23ABar t 1 e :=
    hmem_gen xC ⟨ℓ, hℓC, by simp [xC, eC, ℓC]⟩
  have hcomm := hΦ _ heb _ hxb
  have he2 : eC * eC = 1 := Subtype.ext hd.he2
  have hx2 : xC * xC = 1 := by
    rw [hxCdef]
    calc ℓC * eC * ℓC⁻¹ * (ℓC * eC * ℓC⁻¹) = ℓC * (eC * eC) * ℓC⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hex' : eC * xC * eC⁻¹ * xC⁻¹ ∈ classicalInvolutionOddCore ↥C := by
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥C)]
    show F7I.piC C _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc F7I.piC C eC * F7I.piC C xC * (F7I.piC C eC)⁻¹ * (F7I.piC C xC)⁻¹
        = (F7I.piC C xC * F7I.piC C eC) * (F7I.piC C eC)⁻¹ * (F7I.piC C xC)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  obtain ⟨dC, hd1, hd2⟩ := exists_commuting_conj (classicalInvolutionOddCore ↥C)
    (CFSG.ComponentClassification.OddCore.odd_card ↥C) he2 hx2 hex'
  set yC : ↥C := dC * xC * dC⁻¹ with hyCdef
  have hyY : (yC : Y) = ((dC : Y) * ℓ) * e * ((dC : Y) * ℓ)⁻¹ := by
    simp only [yC, xC, eC, ℓC, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcC' : (dC : Y) * ℓ ∈ C := C.mul_mem dC.2 hℓC
  refine ⟨(dC : Y) * ℓ, hcC', ?_, ?_, ?_⟩
  · rw [← hyY]
    exact congrArg Subtype.val hd1
  · rw [← hyY]
    intro hye
    apply hℓ
    have h1 : yC = eC := Subtype.ext hye
    rw [h1] at hd2
    have h2 : ((eC * xC⁻¹ : ↥C) : Y) ∈ oddCoreOf C := ⟨_, hd2, rfl⟩
    have h3 : ((eC * xC⁻¹ : ↥C) : Y) = e * ℓ * e⁻¹ * ℓ⁻¹ := by
      simp only [xC, eC, ℓC, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [h3] at h2
  · rw [← hyY]
    have hπy : F7I.piC C yC = F7I.piC C xC := by
      have h1 : F7I.piC C (yC * xC⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hd2
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    obtain ⟨-, -, -, -, -, -, -, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
    have hperm := p23_twin_perm hc hCdef
    obtain ⟨hcA, hcB⟩ := conj_cent_of_perm
      (A := ((tightCore R).subgroupOf C).map (F7I.piC C)) (B := (K'.subgroupOf C).map (F7I.piC C))
      hperm heA heB (F7I.piC C ℓC)
    have hxπ : F7I.piC C xC = F7I.piC C ℓC * F7I.piC C ⟨e, heC⟩ * (F7I.piC C ℓC)⁻¹ := by
      simp only [xC, map_mul, map_inv]
      rfl
    set Zy : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C) :=
      Subgroup.centralizer ({F7I.piC C yC} : Set _) with hZy
    have hK₀le : tightCore R ≤ C := le_centralizer_of_unique hz
    have hK'le : K' ≤ C := le_centralizer_of_unique hz'
    have hAle : ((tightCore R).subgroupOf C).map (F7I.piC C) ≤ Zy := by
      intro a ha
      rw [hZy, Subgroup.mem_centralizer_singleton_iff, hπy, hxπ]
      exact (hcA a ha).symm
    have hBle : (K'.subgroupOf C).map (F7I.piC C) ≤ Zy := by
      intro a ha
      rw [hZy, Subgroup.mem_centralizer_singleton_iff, hπy, hxπ]
      exact (hcB a ha).symm
    intro l hl
    have hlC : l ∈ C := sup_le hK₀le hK'le hl
    have hl' : (⟨l, hlC⟩ : ↥C) ∈ (tightCore R ⊔ K').subgroupOf C := hl
    rw [Subgroup.subgroupOf_sup hK₀le hK'le] at hl'
    have hZc : (⟨l, hlC⟩ : ↥C) ∈ Zy.comap (F7I.piC C) := by
      have hle : (tightCore R).subgroupOf C ⊔ K'.subgroupOf C ≤ Zy.comap (F7I.piC C) := by
        refine sup_le ?_ ?_
        · intro a ha
          exact hAle ⟨a, ha, rfl⟩
        · intro a ha
          exact hBle ⟨a, ha, rfl⟩
      exact hle hl'
    have hZc' := Subgroup.mem_centralizer_singleton_iff.mp hZc
    have h4 : F7I.piC C (yC * ⟨l, hlC⟩ * yC⁻¹ * ⟨l, hlC⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc F7I.piC C yC * F7I.piC C ⟨l, hlC⟩ * (F7I.piC C yC)⁻¹ * (F7I.piC C ⟨l, hlC⟩)⁻¹
          = (F7I.piC C ⟨l, hlC⟩ * F7I.piC C yC) * (F7I.piC C yC)⁻¹ * (F7I.piC C ⟨l, hlC⟩)⁻¹ := by
            rw [hZc']
        _ = 1 := by group
    have h5 := (F7I.piC_eq_one_iff _).mp h4
    simpa using h5

end Y

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
