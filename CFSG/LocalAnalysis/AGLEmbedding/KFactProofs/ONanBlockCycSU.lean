module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits Matrix

section Plane

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem exists_plane_elements {p : Fin n} (hp : p ≠ Fin.rev p) :
    ∃ x y : SU σ n,
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single p (Fin.rev p) 1 ∧
      ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single (Fin.rev p) p 1 ∧
      (x * y) ^ 3 = 1 ∧ ¬ Commute x (x * y) := by
  have h11 : (1 : F) ∈ traceZero σ := by
    rw [mem_traceZero, map_one]
    exact CharTwo.add_self_eq_zero 1
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hp' := rev_ne_rev_rev hp
  set x : SU σ n := longRootHom σ hp (Multiplicative.ofAdd ⟨1, h11⟩) with hx
  set y : SU σ n := longRootHom σ hp' (Multiplicative.ofAdd ⟨1, h11⟩) with hy
  set a : Matrix (Fin n) (Fin n) F := Matrix.single p (Fin.rev p) 1 with ha
  set b : Matrix (Fin n) (Fin n) F := Matrix.single (Fin.rev p) p 1 with hb
  have hxmat : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + a := rfl
  have hymat : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + b := by
    change 1 + Matrix.single (Fin.rev p) (Fin.rev (Fin.rev p)) 1 = _
    rw [Fin.rev_rev]
  have hrp : Fin.rev p ≠ p := hp.symm
  have ha2 : a + a = 0 := by
    rw [ha, ← Matrix.single_add, h2, Matrix.single_zero]
  have hb2 : b + b = 0 := by
    rw [hb, ← Matrix.single_add, h2, Matrix.single_zero]
  have haa : a * a = 0 := by
    rw [ha]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hrp _
  have hbb : b * b = 0 := by
    rw [hb]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hp _
  have hab : a * b = Matrix.single p p 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have hba : b * a = Matrix.single (Fin.rev p) (Fin.rev p) 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have haba : a * b * a = a := by
    rw [hab, ha, Matrix.single_mul_single_same, mul_one]
  have hbab : b * a * b = b := by
    rw [hba, hb, Matrix.single_mul_single_same, mul_one]
  obtain ⟨hx2, hy2, hbraid, hxyx⟩ := braid_of_rels ha2 hb2 haa hbb haba hbab
  have hx2' : x * x = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hxmat]; exact hx2))
  have hy2' : y * y = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hymat]; exact hy2))
  have hbraid' : x * y * x = y * x * y :=
    Subtype.ext (Units.ext (by
      simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat]
      exact hbraid))
  refine ⟨x, y, hxmat, hymat, cube_eq_one_of_braid hx2' hy2' hbraid', fun hc => ?_⟩
  have h := hc.eq
  have h' := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat] at h'
  rw [hxyx, ← mul_assoc, hx2, one_mul] at h'
  have h'' := congrFun (congrFun h' p) p
  simp [ha, hb, hrp, h2] at h''

theorem commute_one_add_of_mul_eq_zero {R : Type*} [Ring R] {A B : R} (h1 : A * B = 0)
    (h2 : B * A = 0) : Commute (1 + A) (1 + B) := by
  show (1 + A) * (1 + B) = (1 + B) * (1 + A)
  have e1 : (1 + A) * (1 + B) = 1 + A + B + A * B := by noncomm_ring
  have e2 : (1 + B) * (1 + A) = 1 + B + A + B * A := by noncomm_ring
  rw [e1, e2, h1, h2]
  abel

omit [CharP F 2] in
theorem commute_of_planes {p q : Fin n} (hpq : p ≠ q) (hpq' : p ≠ Fin.rev q) {x y : SU σ n}
    (hxm : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single p (Fin.rev p) 1)
    (hym : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single (Fin.rev p) p 1)
    {x' y' : SU σ n}
    (hxm' : ((x' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + Matrix.single q (Fin.rev q) 1)
    (hym' : ((y' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + Matrix.single (Fin.rev q) q 1) :
    Commute x x' ∧ Commute x y' ∧ Commute y x' ∧ Commute y y' := by
  have hp1 : Fin.rev p ≠ q := fun h => hpq' (by rw [← h, Fin.rev_rev])
  have hq1 : Fin.rev q ≠ p := fun h => hpq' h.symm
  have hp2 : Fin.rev p ≠ Fin.rev q := fun h => hpq (Fin.rev_injective h)
  have hc : ∀ {u v : SU σ n} {A B : Matrix (Fin n) (Fin n) F},
      ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + A →
      ((v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + B → A * B = 0 → B * A = 0 →
        Commute u v := fun {u v A B} hu hv h1 h2 => by
    have := commute_one_add_of_mul_eq_zero h1 h2
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hu, hv]
    exact this.eq
  have hz : ∀ {i j k l : Fin n}, j ≠ k → ∀ a b : F,
      Matrix.single i j a * Matrix.single k l b = 0 := fun hjk a b =>
    Matrix.single_mul_single_of_ne _ _ _ _ hjk _
  have hxx : Commute x x' := hc hxm hxm' (hz hp1 1 1) (hz hq1 1 1)
  have hxy : Commute x y' := hc hxm hym' (hz hp2 1 1) (hz hpq.symm 1 1)
  have hyx : Commute y x' := hc hym hxm' (hz hpq 1 1) (hz hp2.symm 1 1)
  have hyy : Commute y y' := hc hym hym' (hz hq1.symm 1 1) (hz hp1.symm 1 1)
  exact ⟨hxx, hxy, hyx, hyy⟩

end Plane

section Model

open CFSG.AGLEmbedding.BlockCyc

theorem hasE9_of_model_psu {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (hn4 : 4 ≤ n) : HasE9 Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hbq := borelQuotient_su hcard (by omega) ζ hζ e
  have hp0 : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_rev]
    omega
  have hq0 : (⟨1, by omega⟩ : Fin n) ≠ Fin.rev ⟨1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_rev]
    omega
  have hpq : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hpq' : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_rev]
    omega
  obtain ⟨x, y, hx, hy, h3, hnc⟩ := exists_plane_elements (σ := unitaryInvolution F 2 f) hp0
  obtain ⟨x', y', hx', hy', h3', hnc'⟩ := exists_plane_elements (σ := unitaryInvolution F 2 f) hq0
  obtain ⟨hxx, hxy, hyx, hyy⟩ := commute_of_planes hpq hpq' hx hy hx' hy'
  exact hasE9_of_commuting_orders _ hbq.ker_central (a₁ := x * y) (a₂ := x' * y') (b₁ := x)
    (b₂ := x') h3 h3' (hxx.mul_left hyx |>.mul_right (hxy.mul_left hyy)).eq
    ((hxx.symm).mul_right hyx.symm) hnc' hnc

theorem hasE9_of_model_psu_of_parabolic {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hJtop : J ≠ ⊤) : HasE9 Y := by
  by_cases hn4 : 4 ≤ n
  · exact hasE9_of_model_psu h hn4
  · exfalso
    obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
    obtain ⟨i, j, hij⟩ :=
      (borelQuotient_su hcard (by omega) ζ hζ e).exists_two_nodes T J hNJ hJ hJtop
    have hi : i.val < n / 2 := i.isLt
    have hj : j.val < n / 2 := j.isLt
    exact hij (Fin.ext (by omega))

end Model

end CFSG.AGLEmbedding.BlockCyc
