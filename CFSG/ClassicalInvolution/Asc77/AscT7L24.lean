module

public import CFSG.ClassicalInvolution.Asc77.AscT7L12
public import CFSG.ClassicalInvolution.Asc77.AscT7L17
public import CFSG.ClassicalInvolution.Asc77.AscT7L23

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (modelUniv)

namespace T7L

section MatrixU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_conj_x0_u0_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) {a b : Su K p f 4} (ha : a ∈ R)
    (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ c : Su K p f 4, x = c * x0 K p f * c⁻¹ ∧ a * b = c * u0 K p f * c⁻¹ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hRg' : R = (R0 K p f).map (MulAut.conj g).toMonoidHom := hRg
  have hR'g' : R' = (R0' K p f).map (MulAut.conj g).toMonoidHom := hR'g
  have hxg' : x = g * x0 K p f * g⁻¹ := hxg
  have hx'neg := twin_neg_su h2 hxg' hR'g' hx'R' hx'2 hx'1
  have hzc : ∀ y : Su K p f 4, y * zneg K p f = zneg K p f * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  rw [hRg'] at ha
  rw [hR'g'] at hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at haa hbb ⊢
  have ha₀2 : a₀ * a₀ = x0 K p f := by
    have : g * (a₀ * a₀) * g⁻¹ = g * x0 K p f * g⁻¹ := by rw [← hxg', ← haa]; group
    exact mul_left_cancel (mul_right_cancel this)
  have hb₀2 : b₀ * b₀ = zneg K p f * x0 K p f := by
    have : g * (b₀ * b₀) * g⁻¹ = g * (zneg K p f * x0 K p f) * g⁻¹ := by
      calc g * (b₀ * b₀) * g⁻¹ = g * b₀ * g⁻¹ * (g * b₀ * g⁻¹) := by group
        _ = x' := hbb
        _ = zneg K p f * x := hx'neg
        _ = zneg K p f * (g * x0 K p f * g⁻¹) := by rw [hxg']
        _ = g * (zneg K p f * x0 K p f) * g⁻¹ := by
          calc zneg K p f * (g * x0 K p f * g⁻¹) = (zneg K p f * g) * x0 K p f * g⁻¹ := by group
            _ = (g * zneg K p f) * x0 K p f * g⁻¹ := by rw [← hzc g]
            _ = g * (zneg K p f * x0 K p f) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hcomm : b₀ * a₀ = a₀ * b₀ := (R0_comm_R0' ha₀ hb₀).symm
  have hw : a₀ * b₀ ∈ R0 K p f ⊔ R0' K p f :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₀) (Subgroup.mem_sup_right hb₀)
  have hzx : x0 K p f * zneg K p f = zneg K p f * x0 K p f := hzc _
  have hw2 : (a₀ * b₀) * (a₀ * b₀) = zneg K p f := by
    calc (a₀ * b₀) * (a₀ * b₀) = a₀ * (b₀ * a₀) * b₀ := by group
      _ = (a₀ * a₀) * (b₀ * b₀) := by rw [hcomm]; group
      _ = x0 K p f * (zneg K p f * x0 K p f) := by rw [ha₀2, hb₀2]
      _ = (x0 K p f * zneg K p f) * x0 K p f := by group
      _ = zneg K p f * (x0 K p f * x0 K p f) := by rw [hzx]; group
      _ = zneg K p f := by rw [x0_mul_self, mul_one]
  have hz1 := zneg_ne_one_u (K := K) (p := p) (f := f) h2
  have hzz := zneg_mul_self (K := K) (p := p) (f := f)
  rcases classify_w hK h2 hw (hw2 ▸ zneg_mem_center) with h | h | h | h | ⟨h, hh, hwh⟩
  · exfalso
    rw [h, mul_one] at hw2
    exact hz1 hw2.symm
  · exfalso
    rw [h, x0_mul_self] at hw2
    exact hz1 hw2.symm
  · exfalso
    have : (zneg K p f * x0 K p f) * (zneg K p f * x0 K p f) = 1 := by
      calc (zneg K p f * x0 K p f) * (zneg K p f * x0 K p f)
          = zneg K p f * (x0 K p f * zneg K p f) * x0 K p f := by group
        _ = zneg K p f * (zneg K p f * x0 K p f) * x0 K p f := by rw [hzx]
        _ = (zneg K p f * zneg K p f) * (x0 K p f * x0 K p f) := by group
        _ = 1 := by rw [hzz, x0_mul_self, mul_one]
    rw [h, this] at hw2
    exact hz1 hw2.symm
  · exfalso
    rw [h, hzz] at hw2
    exact hz1 hw2.symm
  · have hle : R0 K p f ⊔ R0' K p f ≤ Subgroup.centralizer ({x0 K p f} : Set (Su K p f 4)) :=
      sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (R0_comm_x0 hr))
        (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
          (R0_comm_R0' x0_mem_R0 hr).symm)
    have hxh : h * x0 K p f = x0 K p f * h :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    refine ⟨g * h, ?_, ?_⟩
    · calc x = g * x0 K p f * g⁻¹ := hxg'
        _ = g * (h * x0 K p f * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 K p f * (g * h)⁻¹ := by group
    · calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (h * u0 K p f * h⁻¹) * g⁻¹ := by rw [hwh]
        _ = g * h * u0 K p f * (g * h)⁻¹ := by group

end MatrixU

section Row

variable (p : ℕ) [Fact p.Prime]

theorem e4GenSU : E4GenSU p := by
  intro e hadm hp2 hq h1
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨ω, hω, hσω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 ∧
      unitaryInvolution (GaloisField p (2 * e)) p e ω = ω := by
    have : Fintype (GaloisField p (2 * e)) := Fintype.ofFinite _
    obtain ⟨ω, hω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 := by
      have hsq : IsSquare (-1 : GaloisField p (2 * e)) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
        have hm : p ^ e = 4 * (p ^ e / 4) + 1 := by omega
        rw [hm]
        ring_nf
        omega
      obtain ⟨ω, hω⟩ := hsq
      exact ⟨ω, hω.symm⟩
    refine ⟨ω, hω, ?_⟩
    rw [unitaryInvolution_apply]
    have hω4 : ω ^ 4 = 1 := by linear_combination (ω * ω - 1) * hω
    have hm : p ^ e = 4 * (p ^ e / 4) + 1 := by omega
    rw [hm, pow_add, pow_mul, hω4, one_pow, one_mul, pow_one]
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRφ := (hφ R).mp hR
  have hR'φ := (hφ R').mp hR'
  have hneφ : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hc : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    have hxinv : (φ x)⁻¹ = φ x := by rw [← map_inv, inv_eq_of_mul_eq_one_right hx2]
    rw [hxinv, ← map_mul, ← hcomm x hx x' hx']
    exact (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ _).mpr hxx'
  obtain ⟨c, hxc, habc⟩ := exists_conj_x0_u0_su hK hp2 hRφ hR'φ hneφ
    (x := φ x) (x' := φ x') ⟨x, hx, rfl⟩ (by rw [← map_mul, hx2, map_one])
    (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hx', rfl⟩
    (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc (a := φ a) (b := φ b)
    ⟨a, ha, rfl⟩ (by rw [← map_mul, haa]) ⟨b, hb, rfl⟩ (by rw [← map_mul, hbb])
  have hSu := top_le_sup_of_conj c hxc habc (top_le_x0_sup_u0_su hK hp2 hω hσω)
  exact e4_goal_of_top_le _ _ _ (top_le_sup_of_equiv φ.symm (x := φ x) (y := φ a * φ b)
    (by simp) (by simp [map_mul]) hSu)

end Row

end T7L

end CFSG.ClassicalInvolution.Asc77
