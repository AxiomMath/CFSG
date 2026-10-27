module

public import CFSG.ClassicalInvolution.Asc77.AscT7L10
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuModel

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

theorem zneg_ne_one_u (h2 : (2 : K) ≠ 0) : zneg K p f ≠ 1 := by
  intro h
  have h1 := congrArg suMat h
  rw [suMat_zneg, suMat_one] at h1
  have := congrFun (congrFun h1 0) 0
  simp at this
  apply h2
  linear_combination -this

theorem R0_comm_x0 {r : Su K p f 4} (hr : r ∈ R0 K p f) : r * x0 K p f = x0 K p f * r := by
  obtain ⟨A, rfl⟩ := hr
  have hx0 : x0 K p f = blockEmb K p f 4 2 0 (by norm_num) (negOneSU K p f) := rfl
  rw [hx0, ← map_mul, ← map_mul, negOneSU_comm]

theorem exists_longRootU_comm_ab (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {ω : K}
    (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) {a b : Su K p f 4} (ha : a ∈ R)
    (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ R'' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num),
      ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
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
  · have hzO := zOm_mem_center hω hσω
    set z' := zOm hω hσω with hz'
    set Y := yB h2 hω hσω with hY
    have hyx := yB_conj_x0 h2 hω hσω
    set s : Su K p f 4 := z'⁻¹ * x0 K p f with hs
    have hzi : Y * z'⁻¹ = z'⁻¹ * Y := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hzO) Y
    have hu0 : u0 K p f = Y * s * Y⁻¹ := by
      calc u0 K p f = z'⁻¹ * (z' * u0 K p f) := by group
        _ = z'⁻¹ * (Y * x0 K p f * Y⁻¹) := by rw [← hyx]
        _ = (z'⁻¹ * Y) * x0 K p f * Y⁻¹ := by group
        _ = (Y * z'⁻¹) * x0 K p f * Y⁻¹ := by rw [hzi]
        _ = Y * s * Y⁻¹ := by rw [hs]; group
    set c : Su K p f 4 := g * h * Y with hc'
    refine ⟨(R0 K p f).map (MulAut.conj c).toMonoidHom,
      (mem_longRootSetU_iff (show 2 ≤ 4 by norm_num)).mpr ⟨c, rfl⟩, ?_⟩
    have hab : g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = c * s * c⁻¹ := by
      calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (h * u0 K p f * h⁻¹) * g⁻¹ := by rw [hwh]
        _ = c * s * c⁻¹ := by rw [hu0, hc']; group
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hrs : r * s = s * r := by
      have h1 : r * x0 K p f = x0 K p f * r := R0_comm_x0 hr
      have h2' : r * z'⁻¹ = z'⁻¹ * r := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hzO) r
      calc r * s = (r * z'⁻¹) * x0 K p f := by rw [hs]; group
        _ = z'⁻¹ * (r * x0 K p f) := by rw [h2']; group
        _ = z'⁻¹ * (x0 K p f * r) := by rw [h1]
        _ = s * r := by rw [hs]; group
    rw [hab]
    calc c * s * c⁻¹ * (c * r * c⁻¹) = c * (s * r) * c⁻¹ := by group
      _ = c * (r * s) * c⁻¹ := by rw [hrs]
      _ = c * r * c⁻¹ * (c * s * c⁻¹) := by group

end MatrixU

section Row

variable (p : ℕ) [Fact p.Prime]

theorem twinCentralSU : TwinCentralSU p := by
  intro e hadm hp2 hq h3
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨ω, hω, hσω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 ∧
      unitaryInvolution (GaloisField p (2 * e)) p e ω = -ω := by
    have : Fintype (GaloisField p (2 * e)) := Fintype.ofFinite _
    obtain ⟨ω, hω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 := by
      have hsq : IsSquare (-1 : GaloisField p (2 * e)) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
        have hm : p ^ e = 4 * (p ^ e / 4) + 3 := by omega
        rw [hm]
        ring_nf
        omega
      obtain ⟨ω, hω⟩ := hsq
      exact ⟨ω, hω.symm⟩
    refine ⟨ω, hω, ?_⟩
    rw [unitaryInvolution_apply]
    have hω4 : ω ^ 4 = 1 := by linear_combination (ω * ω - 1) * hω
    have hm : p ^ e = 4 * (p ^ e / 4) + 3 := by omega
    rw [hm, pow_add, pow_mul, hω4, one_pow, one_mul]
    linear_combination ω * hω
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRφ := (hφ R).mp hR
  have hR'φ := (hφ R').mp hR'
  have hneφ : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hc : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    have hxinv : (φ x)⁻¹ = φ x := by rw [← map_inv, inv_eq_of_mul_eq_one_right hx2]
    rw [hxinv, ← map_mul, ← hcomm x hx x' hx']
    exact (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ _).mpr hxx'
  obtain ⟨R'', hR'', hcomm''⟩ := exists_longRootU_comm_ab hK hp2 hω hσω hRφ hR'φ hneφ
    (x := φ x) (x' := φ x') ⟨x, hx, rfl⟩ (by rw [← map_mul, hx2, map_one])
    (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hx', rfl⟩
    (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc (a := φ a) (b := φ b)
    ⟨a, ha, rfl⟩ (by rw [← map_mul, haa]) ⟨b, hb, rfl⟩ (by rw [← map_mul, hbb])
  refine ⟨R''.map φ.symm.toMonoidHom, (hφ _).mpr ?_, ?_⟩
  · have : (R''.map φ.symm.toMonoidHom).map φ.toMonoidHom = R'' := by
      rw [Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
        ext y
        simp
      rw [this, Subgroup.map_id]
    rw [this]
    exact hR''
  · rintro _ ⟨r, hr, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul]
    have := hcomm'' r hr
    simpa using this

end Row

end T7L

end CFSG.ClassicalInvolution.Asc77
