module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOM
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

theorem oddCoreOf_normalized {Y : Type} [Group Y] [Finite Y] (C : Subgroup Y) :
    (∀ c ∈ C, ∀ o ∈ oddCoreOf C, c * o * c⁻¹ ∈ oddCoreOf C) ∧ oddCoreOf C ≤ C :=
  ⟨fun c hc o ho => (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf C hc) o).mp ho,
    by rintro _ ⟨c, -, rfl⟩; exact c.2⟩

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem Q_normalized (hc : P23Cfg n Y R S t K' W u e g) :
    tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) ∧
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ l ∈ tightCore R ⊔ K', c * l * c⁻¹ ∈ tightCore R ⊔ K' := by
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  refine ⟨sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz'), fun c hcC l hl => ?_⟩
  have hconj : conjSub c (tightCore R ⊔ K') = tightCore R ⊔ K' := by
    have hsup : conjSub c (tightCore R ⊔ K') = conjSub c (tightCore R) ⊔ conjSub c K' :=
      Subgroup.map_sup _ _ _
    rcases p23_conj_twins hc hcC with h | h
    · rw [hsup, h.1, h.2]
    · rw [hsup, h.1, h.2, sup_comm]
  rw [← hconj]
  exact conj_mem_conjSub hl

theorem y_inM (hc : P23Cfg n Y R S t K' W u e g) {y : Y} (hyu : y * u = u * y) (hyt : y * t = t * y)
    {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1) :
    InM (Subgroup.centralizer ({t} : Set Y)) (oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
      (tightCore R ⊔ K') y := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hd := hc.data
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C := le_centralizer_of_unique hz'
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have heC : e ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e_of_mem_W hd hd.hzW).symm
  obtain ⟨hU1, hU1', h8, h8', hnc, hnc', hcomm, -, -, b₁, b', hbb, hb₁K, hb'K', hb₁1, hb₁t, hb'1, hb't⟩ :=
    p23_twin_q8 hc hCdef htC heC
  have hfix : conjSub y (tightCore R) = tightCore R ∧ conjSub y K' = K' := by
    rcases p23_conj_twins hc hyC with h | h
    · exact h
    · exact (not_swap_of_odd hc.std.hne.symm h.1 h.2 hN hyN).elim
  have haN : (F7I.piC C ⟨y, hyC⟩) ^ N = 1 := by
    rw [← map_pow]
    have : (⟨y, hyC⟩ : ↥C) ^ N = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hyN)
    rw [this, map_one]
  have hat : F7I.piC C ⟨y, hyC⟩ * F7I.piC C ⟨t, htC⟩ = F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨y, hyC⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hyt)
  have hnorm : ∀ L : Subgroup Y, conjSub y L = L → ∀ x ∈ (L.subgroupOf C).map (F7I.piC C),
      F7I.piC C ⟨y, hyC⟩ * x * (F7I.piC C ⟨y, hyC⟩)⁻¹ ∈ (L.subgroupOf C).map (F7I.piC C) := by
    intro L hL x hx
    obtain ⟨k, hk, rfl⟩ := F7I.mem_map_piC.mp hx
    have hkC : y * (k : Y) * y⁻¹ ∈ C := C.mul_mem (C.mul_mem hyC k.2) (C.inv_mem hyC)
    refine F7I.mem_map_piC.mpr ⟨⟨y * (k : Y) * y⁻¹, hkC⟩, ?_, ?_⟩
    · have := conj_mem_conjSub (n := y) hk
      rwa [hL] at this
    · rw [show (⟨y * (k : Y) * y⁻¹, hkC⟩ : ↥C) = ⟨y, hyC⟩ * k * (⟨y, hyC⟩ : ↥C)⁻¹ from Subtype.ext rfl,
        map_mul, map_mul, map_inv]
  have hab : F7I.piC C ⟨y, hyC⟩ * (F7I.piC C b₁ * F7I.piC C b') =
      (F7I.piC C b₁ * F7I.piC C b') * F7I.piC C ⟨y, hyC⟩ := by
    have h1 : (⟨y, hyC⟩ : ↥C) * (b₁ * b') = (b₁ * b') * ⟨y, hyC⟩ := by
      apply Subtype.ext
      show y * ((b₁ : Y) * b') = ((b₁ : Y) * b') * y
      rw [hbb, hyu]
    simp only [← map_mul]
    rw [h1]
  obtain ⟨hA, hB⟩ := cent_of_cent_prod h8 h8' hnc hnc' hU1.ne_one hU1.sq hU1.unique hU1'.unique hcomm hN haN
    hat (hnorm _ hfix.1) (hnorm _ hfix.2) hb₁K hb'K' hb₁1 hb₁t hb'1 hb't hab
  set H : Subgroup Y :=
    ((Subgroup.centralizer ({F7I.piC C ⟨y, hyC⟩} : Set (↥C ⧸ classicalInvolutionOddCore ↥C))).comap
      (F7I.piC C)).map C.subtype with hHdef
  have hle : ∀ L : Subgroup Y, L ≤ C → (∀ x ∈ (L.subgroupOf C).map (F7I.piC C),
      F7I.piC C ⟨y, hyC⟩ * x = x * F7I.piC C ⟨y, hyC⟩) → L ≤ H := by
    intro L hLC hL k hk
    refine ⟨⟨k, hLC hk⟩, Subgroup.mem_comap.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr ?_), rfl⟩
    exact (hL _ (F7I.mem_map_piC.mpr ⟨⟨k, hLC hk⟩, hk, rfl⟩)).symm
  refine ⟨hyC, fun l hl => ?_⟩
  obtain ⟨l', hl', rfl⟩ := sup_le (hle _ hKC hA) (hle _ hK'C hB) hl
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hl')
  have h2 : F7I.piC C (⟨y, hyC⟩ * l' * (⟨y, hyC⟩ : ↥C)⁻¹ * l'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← h1]
    group
  exact (F7I.piC_eq_one_iff _).mp h2

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
