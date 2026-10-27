module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Norm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AZ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E8NormAZ8

variable {n : ℕ}

theorem p23E8ANorm_of_az8 (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n) (hΓ : P23E8YGam n)
    (hZ : P23E8AZ8 n) : P23E8ANorm n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hz' : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hu_ue : u * (u * e) = u * e * u := hWab _ hd.huW _ (W.mul_mem hd.huW heW)
  have hue2 : u * e * (u * e) = 1 := by
    have hue : u * e = e * u := hWab _ hd.huW _ heW
    calc u * e * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [hue]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
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
  have het : e * t = t * e := hWab _ heW _ hd.hzW
  have he_ne : e ≠ t := by
    intro h
    apply e_not_mem_sup hc
    rw [h]; exact Subgroup.mem_sup_left hz'.mem
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hA5)))
  have hmemB : ∀ x, (x = u * e ∨ x = u ∨ x = t) → x ∈ p23B t u e := by
    rintro x (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  have heB : e ∈ p23B t u e := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemB u (Or.inr (Or.inl rfl))))
      (hmemB (u * e) (Or.inl rfl))
    rwa [inv_mul_cancel_left] at h
  have hA1B : Subgroup.closure ({u, u * e} : Set Y) ≤ p23B t u e := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hmemB _ (Or.inr (Or.inl rfl))
    · exact hmemB _ (Or.inl rfl)
  have hA1E := T7A.isElemAbelian2_closure_pair hd.hu2 hue2 hd.hu1 hue1 hu_ne hu_ue
  have hA1 : alphaOf (Subgroup.closure ({u, u * e} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) := hbal _ hA1B hA1E
  have hA3 : alphaOf (Subgroup.closure ({e, t} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) := by
    refine hbal _ ?_ (T7A.isElemAbelian2_closure_pair hd.he2 hz'.sq hd.he1 hz'.ne_one he_ne het)
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact heB
    · exact hmemB _ (Or.inr (Or.inr rfl))
  have hY : rLayer (Om R) u ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) :=
    (hΓ hcit hP Y R S t K' W u e g hc hno hA5 hA6).trans
      (p23Gam_le_normalizer hbal hA1B hA1E _)
  have hut : t * u = u * t := hWab _ hd.hzW _ hd.huW
  have hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    have h := oddCoreOf_centralizer_le_normalizer_alphaOf (c := t) (z := u) hd.hu2 hz'.ne_one hut
    rwa [Set.pair_comm] at h
  refine ⟨fun x hx => ?_, fun c hc' => ?_⟩
  · obtain ⟨y, hyY, hyC, hcomm⟩ := p23_cu_frattini hT hc hx
    have hℓC : y⁻¹ * x ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyC) hx
    have hO := oddCoreOf_centralizer_le_normalizer_alphaOf (c := u) (z := u * e) hue2 hd.hu1 hu_ue
    rw [Set.pair_comm] at hO
    have hN := T7B.mem_normalizer_alphaOf_of_commutator (t := u * e) (z := u) (ℓ := y⁻¹ * x) hue2
      hu_ue hℓC hcomm hO
    rw [Set.pair_comm, hA1] at hN
    have ex : x = y * (y⁻¹ * x) := by group
    rw [ex]
    exact Subgroup.mul_mem _ (hY hyY) hN
  · obtain ⟨y, hyY, hyt, -, hcls⟩ := hZ hcit hP Y R S t K' W u e g hc hno hA5 hA6
    obtain ⟨i, -, o, ho, hce⟩ := hcls c hc'
    set C := Subgroup.centralizer ({t} : Set Y) with hCdef
    have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
    have hoC : o ∈ C := oddCoreOf_le_self C ho
    set d := (o * y ^ i)⁻¹ * c with hd'
    have hdC : d ∈ C := C.mul_mem (C.inv_mem (C.mul_mem hoC (C.pow_mem hyC i))) hc'
    have hde : d * e = e * d := by
      have h1 : c * e = (o * (y ^ i * e * (y ^ i)⁻¹) * o⁻¹) * c := by rw [← hce]; group
      calc d * e = (o * y ^ i)⁻¹ * (c * e) := by rw [hd']; group
        _ = (o * y ^ i)⁻¹ * ((o * (y ^ i * e * (y ^ i)⁻¹) * o⁻¹) * c) := by rw [h1]
        _ = e * d := by rw [hd']; group
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    have hdN : d ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
      have h := mem_normalizer_alphaOf_of_centralizes (c := e) (z := t) hde hdt
      rwa [hA3] at h
    have hceq : c = o * y ^ i * d := by rw [hd']; group
    rw [hceq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hOt ho) (Subgroup.pow_mem _ (hY hyY) i)) hdN

theorem p23E8A_of_az8 (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hΓ : P23E8YGam n) (hZ : P23E8AZ8 n) (hX : P23E8AAE7 n) (hS : P23E8ASigma n) : P23E8A n :=
  p23E8A_of_steps hE hα (p23E8ANorm_of_az8 hT hα hΓ hZ) hX hS

end E8NormAZ8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
