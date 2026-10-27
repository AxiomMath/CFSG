module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Norm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamGen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Piece

variable {Y : Type} [Group Y] [Finite Y]

theorem piece_le_gam {B L : Subgroup Y} {u b : Y} (huB : u ∈ B) (hbB : b ∈ B) (hu2 : u * u = 1)
    (hb2 : b * b = 1) (hu1 : u ≠ 1) (hb1 : b ≠ 1) (hub : u ≠ b) (hcomm : u * b = b * u)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set Y)) :
    L ⊓ Subgroup.centralizer ({b} : Set Y) ≤ p23Gam B L := by
  intro x hx
  set A := Subgroup.closure ({u, b} : Set Y) with hA
  have hAE : IsElemAbelian2 A 2 := T7A.isElemAbelian2_closure_pair hu2 hb2 hu1 hb1 hub hcomm
  have hAB : A ≤ B := by
    rw [hA, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [huB, hbB]
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hLC hx.1)
  have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hAx : ∀ h ∈ A, h * x = x * h := by
    intro h hh
    have hle : A ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [hA, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxb.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hxN : x ∈ Subgroup.normalizer (A : Set Y) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    constructor
    · intro hh
      have : x * h * x⁻¹ = h := by rw [← hAx h hh]; group
      rw [this]; exact hh
    · intro hh
      have hxa : x⁻¹ * (x * h * x⁻¹) * x = x * h * x⁻¹ := by
        have h1 := hAx _ hh
        calc x⁻¹ * (x * h * x⁻¹) * x = x⁻¹ * ((x * h * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [h1]
          _ = x * h * x⁻¹ := by group
      have hh2 : h = x⁻¹ * (x * h * x⁻¹) * x := by group
      rw [hh2, hxa]
      exact hh
  have hmem : A ∈ {A : Subgroup Y | A ≤ B ∧ (IsElemAbelian2 A 2 ∨ A = B)} := ⟨hAB, Or.inl hAE⟩
  exact (le_iSup₂_of_le A hmem le_rfl : L ⊓ Subgroup.normalizer (A : Set Y) ≤ p23Gam B L)
    ⟨hx.1, hxN⟩

end Piece

section Cert


variable {n : ℕ}

theorem p23E8YGam_proved : P23E8YGam n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6
  classical
  have hgen := p23E8LayerGen_proved hcit hP Y R S t K' W u e g hc hno hA5 hA6
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hue2 : (u * e) * (u * e) = 1 := ue_sq hc
  have hsup : ∀ x, x ∈ tightCore R ⊔ K' → u⁻¹ * x ∈ tightCore R ⊔ K' := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.hu) hx
  have hue1 : u * e ≠ 1 := by
    intro h
    apply e_not_mem_sup hc
    have : e = u⁻¹ * 1 := by rw [← h]; group
    rw [this]; exact hsup 1 (Subgroup.one_mem _)
  have hu_ne : u ≠ u * e := by
    intro h
    exact hd.he1 (by simpa using congrArg (u⁻¹ * ·) h.symm)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hne_ue⟩ := e_decomp hc
  have hut : u * t = t * u := comm_ut hc
  have hu_ue : u * (u * e) = u * e * u := hWab _ hd.huW _ (W.mul_mem hd.huW heW)
  have hue_t : u * e * t = t * (u * e) := hWab _ (W.mul_mem hd.huW heW) _ hd.hzW
  set L := rLayer (Om R) u with hL
  have hLC : L ≤ Subgroup.centralizer ({u} : Set Y) := rLayer_le_centralizer _ _
  have huB : u ∈ p23B t u e := Subgroup.subset_closure (by simp)
  have htB : t ∈ p23B t u e := Subgroup.subset_closure (by simp)
  have hueB : u * e ∈ p23B t u e := Subgroup.subset_closure (by simp)
  have hA₁ : L ⊓ Subgroup.centralizer ({u * e} : Set Y) ≤ p23Gam (p23B t u e) L :=
    piece_le_gam huB hueB hd.hu2 hue2 hd.hu1 hue1 hu_ne hu_ue hLC
  have hA₂ : L ⊓ Subgroup.centralizer ({t} : Set Y) ≤ p23Gam (p23B t u e) L :=
    piece_le_gam huB htB hd.hu2 hz.sq hd.hu1 hz.ne_one hd.huz hut hLC
  set A₀ : Subgroup Y := Subgroup.closure ({t, u * e} : Set Y) with hA₀
  have hA₀E : IsElemAbelian2 A₀ 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq hue2 hz.ne_one hue1 (fun h => hne_ue h.symm) hue_t.symm
  have hA₀B : A₀ ≤ p23B t u e := by
    rw [hA₀, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [htB, hueB]
  have hA₀C : A₀ ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [hA₀, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hut.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hu_ue.symm
  have hnL : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (L : Set Y) :=
    fun c hcc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_rLayer_eq hΩ hcc)
  set V : Subgroup Y := L ⊓ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) with hV
  have hVodd : ¬ 2 ∣ Nat.card V := by
    intro h2
    have h3 : Nat.card V ∣ Nat.card (oddCoreOf (Subgroup.centralizer ({u} : Set Y))) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact (Nat.not_even_iff_odd.mpr (oddCoreOf_odd_natCard _)) (even_iff_two_dvd.mpr (h2.trans h3))
  have hnV : A₀ ≤ Subgroup.normalizer (V : Set Y) := by
    intro a ha
    have haC := hA₀C ha
    have h1 : conjSub a L = L := mem_normalizer_iff_conjSub_eq.mp (hnL haC)
    have h2 : conjSub a (oddCoreOf (Subgroup.centralizer ({u} : Set Y))) =
        oddCoreOf (Subgroup.centralizer ({u} : Set Y)) :=
      mem_normalizer_iff_conjSub_eq.mp (Sec7.le_normalizer_oddCoreOf _ haC)
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    rw [hV, Sec13.L94T.conjSub_inf_eq, h1, h2]
  have hpower : ∀ member : A₀, member ^ 2 = 1 := fun member => by
    refine Subtype.ext ?_
    have := hA₀E.2 member.1 member.2
    simpa [pow_two] using this
  have hVgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two A₀ V hpower hA₀E.1 hVodd hnV
  have hA₃ : V ≤ p23Gam (p23B t u e) L := by
    rw [hVgen]
    refine iSup_le fun m => iSup_le fun hm => ?_
    have hmB : (m : Y) ∈ p23B t u e := hA₀B m.2
    have hm1 : (m : Y) ≠ 1 := fun h => hm (Subtype.ext h)
    have hum : u ≠ (m : Y) := by
      intro h
      have huA : u ∈ A₀ := h ▸ m.2
      have htA : t ∈ A₀ := Subgroup.subset_closure (by simp)
      have hueA : u * e ∈ A₀ := Subgroup.subset_closure (by simp)
      have hBA : p23B t u e ≤ A₀ := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl | rfl)
        exacts [hueA, huA, htA]
      have h1 := Subgroup.card_le_of_le hBA
      rw [B_natCard hc, hA₀E.1] at h1
      omega
    have hcomm : u * (m : Y) = (m : Y) * u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hA₀C m.2)).symm
    exact (inf_le_inf_right _ inf_le_left).trans
      (piece_le_gam huB hmB hd.hu2 (hA₀E.2 m.1 m.2) hd.hu1 hm1 hum hcomm hLC)
  exact hgen.trans (sup_le (sup_le hA₁ hA₂) hA₃)

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
