module

public import CFSG.LargeExtraspecial.AS35DFourFiveA
public import CFSG.LargeExtraspecial.AS35QThCoordA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] (S : Setting G)

@[expose] noncomputable def zp (ε : ZMod 2) : G := by
  classical
  exact if ε = 0 then 1 else S.z

theorem zp_zero : zp S 0 = 1 := by simp [zp]

theorem zp_one : zp S 1 = S.z := by simp [zp]

theorem zp_add (ε ε' : ZMod 2) : zp S (ε + ε') = zp S ε * zp S ε' := by
  rcases zmod2_cases ε with rfl | rfl <;> rcases zmod2_cases ε' with rfl | rfl
  · simp [zp_zero]
  · simp [zp_zero, zp_one]
  · simp [zp_zero, zp_one]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, zp_zero, zp_one, S.z_mul_z]

theorem zp_mem_QG (ε : ZMod 2) : zp S ε ∈ S.QG := by
  rcases zmod2_cases ε with rfl | rfl
  · rw [zp_zero]; exact S.QG.one_mem
  · rw [zp_one]; exact S.z_mem_QG

theorem zp_mem_M (ε : ZMod 2) : zp S ε ∈ S.M := S.QG_le_M (zp_mem_QG S ε)

theorem zp_comm (ε : ZMod 2) {g : G} (hg : g ∈ S.M) : zp S ε * g = g * zp S ε := by
  rcases zmod2_cases ε with rfl | rfl
  · rw [zp_zero, one_mul, mul_one]
  · rw [zp_one]; exact (S.z_comm hg).symm

theorem zp_mul_self (ε : ZMod 2) : zp S ε * zp S ε = 1 := by
  rw [← zp_add, zmod2_add_self, zp_zero]

theorem cl_zp (ε : ZMod 2) : S.cl (zp S ε) = 0 := by
  rcases zmod2_cases ε with rfl | rfl
  · rw [zp_zero, S.cl_one]
  · rw [zp_one, S.cl_z]

theorem zp_injective : Function.Injective (zp S) := by
  intro ε ε' h
  rcases zmod2_cases ε with rfl | rfl <;> rcases zmod2_cases ε' with rfl | rfl
  · rfl
  · rw [zp_zero, zp_one] at h; exact absurd h.symm S.z_ne_one
  · rw [zp_zero, zp_one] at h; exact absurd h S.z_ne_one
  · rfl

theorem mul_comm_zp [Finite G] {u v : G} (hu : u ∈ S.QG) (hv : v ∈ S.QG) :
    u * v = v * u * zp S (polar S.q (S.cl u) (S.cl v)) := by
  rcases zmod2_cases (polar S.q (S.cl u) (S.cl v)) with h | h
  · rw [h, zp_zero, mul_one]
    exact (S.polar_cl_eq_zero_iff hu hv).mp h
  · rw [h, zp_one]
    have hne := (S.polar_cl_eq_one_iff hu hv).mp h
    rcases S.commutator_eq_one_or_z hu hv with h1 | h1
    · exfalso
      apply hne
      calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
        _ = v * u := by rw [h1, one_mul]
    · calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
        _ = S.z * (v * u) := by rw [h1]
        _ = v * u * S.z := (S.z_comm (S.M.mul_mem (S.QG_le_M hv) (S.QG_le_M hu))).symm

@[expose] def normZ (Zh x : G) : G := x * (Zh * x * Zh⁻¹) * (Zh * Zh * x * (Zh * Zh)⁻¹)

variable {S}
variable {Zh : G} (hZhM : Zh ∈ S.M)
include hZhM

theorem conj_mem_QG' {x : G} (hx : x ∈ S.QG) : Zh * x * Zh⁻¹ ∈ S.QG := S.conj_mem_QG hZhM hx

theorem conj2_mem_QG {x : G} (hx : x ∈ S.QG) : Zh * Zh * x * (Zh * Zh)⁻¹ ∈ S.QG :=
  S.conj_mem_QG (S.M.mul_mem hZhM hZhM) hx

theorem normZ_mem_QG {x : G} (hx : x ∈ S.QG) : normZ Zh x ∈ S.QG :=
  S.QG.mul_mem (S.QG.mul_mem hx (conj_mem_QG' hZhM hx)) (conj2_mem_QG hZhM hx)

variable [Finite G]

theorem cl_conj_Zh {x : G} (hx : x ∈ S.QG) :
    S.cl (Zh * x * Zh⁻¹) = S.rhoL hZhM (S.cl x) := (S.rhoL_cl hZhM hx).symm

theorem cl_conj2_Zh {x : G} (hx : x ∈ S.QG) :
    S.cl (Zh * Zh * x * (Zh * Zh)⁻¹) = S.rhoL hZhM (S.rhoL hZhM (S.cl x)) := by
  rw [show Zh * Zh * x * (Zh * Zh)⁻¹ = Zh * (Zh * x * Zh⁻¹) * Zh⁻¹ by group,
    cl_conj_Zh hZhM (conj_mem_QG' hZhM hx), cl_conj_Zh hZhM hx]

variable {ζ : S.Qt →ₗ[ZMod 2] S.Qt} (hZh : ∀ v, S.rhoL hZhM v = ζ v)
  (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0)

include hZh hζ in
theorem cl_normZ {x : G} (hx : x ∈ S.QG) : S.cl (normZ Zh x) = 0 := by
  rw [normZ, S.cl_mul (S.QG.mul_mem hx (conj_mem_QG' hZhM hx)) (conj2_mem_QG hZhM hx),
    S.cl_mul hx (conj_mem_QG' hZhM hx), cl_conj_Zh hZhM hx, cl_conj2_Zh hZhM hx]
  simp only [hZh]
  have h0 := hζ (S.cl x)
  rw [← h0]
  abel

include hZh hζ in
theorem normZ_eq_one_or_z {x : G} (hx : x ∈ S.QG) : normZ Zh x = 1 ∨ normZ Zh x = S.z :=
  (S.cl_eq_zero_iff (normZ_mem_QG hZhM hx)).mp (cl_normZ hZhM hZh hζ hx)

omit [Finite G] in
theorem normZ_mul_zp {x : G} (hx : x ∈ S.QG) (ε : ZMod 2) :
    normZ Zh (x * zp S ε) = normZ Zh x * zp S ε := by
  have hc : ∀ g : G, g ∈ S.M → Zh * g * Zh⁻¹ ∈ S.M := fun g hg =>
    S.M.mul_mem (S.M.mul_mem hZhM hg) (S.M.inv_mem hZhM)
  have h1 : Zh * (x * zp S ε) * Zh⁻¹ = Zh * x * Zh⁻¹ * zp S ε := by
    calc Zh * (x * zp S ε) * Zh⁻¹ = Zh * x * Zh⁻¹ * (Zh * zp S ε * Zh⁻¹) := by group
      _ = Zh * x * Zh⁻¹ * (zp S ε * Zh * Zh⁻¹) := by rw [← zp_comm S ε hZhM]
      _ = Zh * x * Zh⁻¹ * zp S ε := by group
  have hZ2 : Zh * Zh ∈ S.M := S.M.mul_mem hZhM hZhM
  have h2 : Zh * Zh * (x * zp S ε) * (Zh * Zh)⁻¹ = Zh * Zh * x * (Zh * Zh)⁻¹ * zp S ε := by
    calc Zh * Zh * (x * zp S ε) * (Zh * Zh)⁻¹ =
        Zh * Zh * x * (Zh * Zh)⁻¹ * ((Zh * Zh) * zp S ε * (Zh * Zh)⁻¹) := by group
      _ = Zh * Zh * x * (Zh * Zh)⁻¹ * (zp S ε * (Zh * Zh) * (Zh * Zh)⁻¹) := by
        rw [← zp_comm S ε hZ2]
      _ = Zh * Zh * x * (Zh * Zh)⁻¹ * zp S ε := by group
  have hx' : Zh * x * Zh⁻¹ ∈ S.M := S.QG_le_M (conj_mem_QG' hZhM hx)
  have hx'' : Zh * Zh * x * (Zh * Zh)⁻¹ ∈ S.M := S.QG_le_M (conj2_mem_QG hZhM hx)
  rw [normZ, normZ, h1, h2]
  set x' := Zh * x * Zh⁻¹
  set x'' := Zh * Zh * x * (Zh * Zh)⁻¹
  have e1 : zp S ε * x' = x' * zp S ε := zp_comm S ε hx'
  have e2 : zp S ε * x'' = x'' * zp S ε := zp_comm S ε hx''
  calc x * zp S ε * (x' * zp S ε) * (x'' * zp S ε) =
      x * (zp S ε * x') * (zp S ε * x'') * zp S ε := by group
    _ = x * (x' * zp S ε) * (x'' * zp S ε) * zp S ε := by rw [e1, e2]
    _ = x * x' * (zp S ε * x'') * zp S ε * zp S ε := by group
    _ = x * x' * (x'' * zp S ε) * zp S ε * zp S ε := by rw [e2]
    _ = x * x' * x'' * zp S ε * (zp S ε * zp S ε) := by group
    _ = x * x' * x'' * zp S ε := by rw [zp_mul_self, mul_one]

include hZh in
theorem q_zeta (v : S.Qt) : S.q (ζ v) = S.q v := by
  rw [← hZh]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (S.rhoL_mem hZhM) v

include hZh hζ in
theorem normZ_mul {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    normZ Zh (x * y) = normZ Zh x * normZ Zh y *
      zp S (polar S.q (S.cl y) (S.cl x) + polar S.q (S.cl y) (ζ (S.cl x))) := by
  have hx' := conj_mem_QG' hZhM hx
  have hy' := conj_mem_QG' hZhM hy
  have hx'' := conj2_mem_QG hZhM hx
  have hy'' := conj2_mem_QG hZhM hy
  set x' := Zh * x * Zh⁻¹ with hx'd
  set x'' := Zh * Zh * x * (Zh * Zh)⁻¹ with hx''d
  set y' := Zh * y * Zh⁻¹ with hy'd
  set y'' := Zh * Zh * y * (Zh * Zh)⁻¹ with hy''d
  have c1 : Zh * (x * y) * Zh⁻¹ = x' * y' := by rw [hx'd, hy'd]; group
  have c2 : Zh * Zh * (x * y) * (Zh * Zh)⁻¹ = x'' * y'' := by rw [hx''d, hy''d]; group
  set z₁ := zp S (polar S.q (S.cl y) (S.cl x'))
  set z₂ := zp S (polar S.q (S.cl y') (S.cl x''))
  set z₃ := zp S (polar S.q (S.cl y) (S.cl x''))
  have e1 : y * x' = x' * y * z₁ := mul_comm_zp S hy hx'
  have e2 : y' * x'' = x'' * y' * z₂ := mul_comm_zp S hy' hx''
  have e3 : y * x'' = x'' * y * z₃ := mul_comm_zp S hy hx''
  have hM : ∀ {g : G}, g ∈ S.QG → g ∈ S.M := fun hg => S.QG_le_M hg
  have hc1 : ∀ {g : G}, g ∈ S.M → z₁ * g = g * z₁ := fun hg => zp_comm S _ hg
  have hc2 : ∀ {g : G}, g ∈ S.M → z₂ * g = g * z₂ := fun hg => zp_comm S _ hg
  have hc3 : ∀ {g : G}, g ∈ S.M → z₃ * g = g * z₃ := fun hg => zp_comm S _ hg
  have key : x * y * (x' * y') * (x'' * y'') = x * x' * x'' * (y * y' * y'') * (z₃ * z₂ * z₁) := by
    calc x * y * (x' * y') * (x'' * y'') = x * (y * x') * y' * x'' * y'' := by group
      _ = x * x' * y * (z₁ * (y' * x'')) * y'' := by rw [e1]; group
      _ = x * x' * y * (y' * x'' * z₁) * y'' := by
        rw [hc1 (S.M.mul_mem (hM hy') (hM hx''))]
      _ = x * x' * (y * x'') * y' * (z₂ * (z₁ * y'')) := by rw [e2]; group
      _ = x * x' * (y * x'') * y' * (y'' * (z₂ * z₁)) := by
        have hh : z₂ * (z₁ * y'') = y'' * (z₂ * z₁) := by
          calc z₂ * (z₁ * y'') = z₂ * (y'' * z₁) := by rw [hc1 (hM hy'')]
            _ = (z₂ * y'') * z₁ := by group
            _ = (y'' * z₂) * z₁ := by rw [hc2 (hM hy'')]
            _ = y'' * (z₂ * z₁) := by group
        rw [hh]
      _ = x * x' * x'' * (y * (z₃ * y')) * y'' * (z₂ * z₁) := by rw [e3]; group
      _ = x * x' * x'' * (y * y' * (z₃ * y'')) * (z₂ * z₁) := by
        rw [hc3 (hM hy')]; group
      _ = x * x' * x'' * (y * y' * y'') * (z₃ * z₂ * z₁) := by
        rw [hc3 (hM hy'')]; group
  rw [normZ, c1, c2, key, ← normZ, ← normZ]
  congr 1
  rw [← zp_add, ← zp_add]
  congr 1
  rw [hx'd, hx''d, hy'd, cl_conj_Zh hZhM hx, cl_conj2_Zh hZhM hx, cl_conj_Zh hZhM hy, hZh, hZh,
    hZh, polar_map_map S.q (q_zeta hZhM hZh), zeta_zeta hζ, polar_add_right]
  have hfin : ∀ a b : ZMod 2, b + a + b + b = a + b := by decide
  exact hfin _ _

end CFSG.LargeExtraspecial.AS35QTh
