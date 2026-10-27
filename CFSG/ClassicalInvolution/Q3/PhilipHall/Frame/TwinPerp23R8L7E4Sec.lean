module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AXVPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOAct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsORel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Cov
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYGrp
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOD8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Wr

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

theorem comm_vec_apply {w v : Wr 6} (hv : v.perm = 1) (i : Fin 6) :
    (w * v * w⁻¹ * v⁻¹).vec i = v.vec (w.perm.symm i) + v.vec i := by
  have key : (w * v * w⁻¹ * v⁻¹).vec i =
      w.vec i + v.vec (w.perm.symm i) + w.vec (w.perm ((w.perm * v.perm).symm i)) +
        v.vec (v.perm ((w.perm * v.perm * w.perm⁻¹).symm i)) := rfl
  rw [key, hv, mul_one, mul_inv_cancel]
  simp only [Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply]
  rw [add_right_comm (w.vec i), zmod_two_add_self, zero_add]

theorem perm_one_of_comm {β : Finset (Fin 6)} (hβ : β.card = 4) {w v : Wr 6}
    (hw : ∀ i ∈ β, w.perm i = i) (hvp : v.perm = 1) {d : Fin 6} (hdβ : d ∉ β)
    (hd : ∀ i j, i ≠ d → j ≠ d → v.vec i = v.vec j) (hne : mkQ 6 v ≠ 1)
    (hcomm : mkQ 6 (w * v * w⁻¹ * v⁻¹) = 1) : w.perm = 1 := by
  obtain ⟨p, q, hpq, hp, hq, hout⟩ := exists_compl_pair hβ
  rcases perm_dichotomy hpq hp hq hout w.perm hw with h | h
  · exact h
  · exfalso
    obtain ⟨b₀, hb₀⟩ : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
    obtain ⟨d', hd'd, hsw⟩ : ∃ d' : Fin 6, d' ≠ d ∧ w.perm.symm d = d' := by
      rcases hout d hdβ with rfl | rfl
      · exact ⟨q, hpq.symm, by rw [h, Equiv.symm_swap, Equiv.swap_apply_left]⟩
      · exact ⟨p, hpq, by rw [h, Equiv.symm_swap, Equiv.swap_apply_right]⟩
    have hsb : w.perm.symm b₀ = b₀ := by
      apply w.perm.injective
      rw [Equiv.apply_symm_apply, hw b₀ hb₀]
    have hvd : v.vec d ≠ v.vec d' := by
      intro hv
      apply hne
      refine mkQ_eq_one_of_const v hvp (v.vec d') fun i => ?_
      by_cases hi : i = d
      · rw [hi, hv]
      · exact hd i d' hi hd'd
    have hmem : w * v * w⁻¹ * v⁻¹ ∈ piSub 6 := (QuotientGroup.eq_one_iff _).mp hcomm
    have hconst : (w * v * w⁻¹ * v⁻¹).vec b₀ = (w * v * w⁻¹ * v⁻¹).vec d := by
      rcases hmem with h1 | h1 <;>
        exact (congrFun (congrArg Wr.vec h1) b₀).trans ((congrFun (congrArg Wr.vec h1) d).symm)
    rw [comm_vec_apply hvp, comm_vec_apply hvp, hsb, hsw, zmod_two_add_self] at hconst
    exact hvd ((by decide : ∀ a b : ZMod 2, 0 = a + b → b = a) _ _ hconst)

theorem comm_of_acts {Q : Type} [Group Q] {Φ : Set (Subgroup Q)} (D : AEData Q Φ) {σ τ : Q → Q}
    {w v : Wr 6} (hw : D.Acts σ w) (hv : D.Acts τ v) (hστ : ∀ q, σ (τ q) = τ (σ q)) :
    mkQ 6 (w * v * w⁻¹ * v⁻¹) = 1 := by
  have hc : ∀ x ∈ TwinThinPf8.Hn 6,
      mkQ 6 (w⁻¹ * v⁻¹ * w * v) * x * (mkQ 6 (w⁻¹ * v⁻¹ * w * v))⁻¹ = x := by
    intro x hx
    rw [← D.range_eq] at hx
    obtain ⟨q, rfl⟩ := hx
    have h1 := hw (τ q)
    have h2 := hv (σ q)
    rw [hv q] at h1
    rw [hw q, ← hστ q, h1] at h2
    calc mkQ 6 (w⁻¹ * v⁻¹ * w * v) * D.φ q * (mkQ 6 (w⁻¹ * v⁻¹ * w * v))⁻¹ =
        (mkQ 6 w)⁻¹ * (mkQ 6 v)⁻¹ * (mkQ 6 w * (mkQ 6 v * D.φ q * (mkQ 6 v)⁻¹) * (mkQ 6 w)⁻¹) *
          mkQ 6 v * mkQ 6 w := by
          simp only [map_mul, map_inv]
          group
      _ = (mkQ 6 w)⁻¹ * (mkQ 6 v)⁻¹ * (mkQ 6 v * (mkQ 6 w * D.φ q * (mkQ 6 w)⁻¹) * (mkQ 6 v)⁻¹) *
          mkQ 6 v * mkQ 6 w := by rw [h2]
      _ = D.φ q := by group
  have h3 := ClsO.mkQ_eq_one_of_centralizes _ hc
  simp only [map_mul, map_inv] at h3
  have h4 : mkQ 6 w * mkQ 6 v = mkQ 6 v * mkQ 6 w := by
    calc mkQ 6 w * mkQ 6 v =
        mkQ 6 v * mkQ 6 w * ((mkQ 6 w)⁻¹ * (mkQ 6 v)⁻¹ * mkQ 6 w * mkQ 6 v) := by group
      _ = mkQ 6 v * mkQ 6 w := by rw [h3, mul_one]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h4]
  group

end Wr

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

section Y

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
open CFSG.ClassicalInvolution.Q3.AE

theorem exists_y_rel_lay (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    ∃ y : Y, y ∈ rLayer (Om R) u ∧ y * u = u * y ∧ y * t = t * y ∧ (∃ a : ℕ, y ^ 3 ^ a = 1) ∧
      (∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹) ∧
      ∃ m : Y, (∃ N : ℕ, Odd N ∧ m ^ N = 1) ∧ m * u = u * m ∧
        (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = t * m ∨
          e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = u * t * m) := by
  classical
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hxx, hvH, hzv, hvH2, hψinj, hrange, hψx, hιr, hψv⟩ :=
    AY.frame_psi hc hA5
  obtain ⟨w, hwA, hw3, hwv, hwx, hwxc, hwprod⟩ := ClsO.exists_three_elt_prod hιr
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hNodd : Odd (Nat.card N) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) u)
  obtain ⟨q, hq⟩ := hrange (mkQ 5 w) (Subgroup.mem_map_of_mem _ hwA)
  have hq3 : q ^ 3 = 1 := hψinj (by rw [map_pow, hq, hw3, map_one])
  have hqv : q * (QuotientGroup.mk vH : ↥(coreHull (Om R) u) ⧸ N) =
      QuotientGroup.mk vH * q :=
    hψinj (by rw [map_mul, map_mul, hq, hψv]; exact hwv)
  have hqx : q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) ≠ QuotientGroup.mk x * q := by
    intro h
    apply hwx
    have := congrArg ψ h
    rwa [map_mul, map_mul, hq, hψx] at this
  have hqxc : (q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * q⁻¹) * QuotientGroup.mk x =
      QuotientGroup.mk x * (q * QuotientGroup.mk x * q⁻¹) := by
    apply hψinj
    simp only [map_mul, map_inv, hq]
    rw [hψx]
    exact hwxc
  have hxq : (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * QuotientGroup.mk x = 1 := by
    rw [← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one]
  have hprodq : (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * (q * QuotientGroup.mk x * q⁻¹) *
      (q ^ 2 * QuotientGroup.mk x * (q ^ 2)⁻¹) = QuotientGroup.mk vH := by
    apply hψinj
    simp only [map_mul, map_inv, map_pow, hq]
    rw [hψx, hψv]
    exact hwprod
  obtain ⟨y₁, hy₁q, hy₁v, a, hy₁a⟩ := AY.exists_pow_three_lift hNodd hvH2 hq3 hqv
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  obtain ⟨y, hy⟩ : ∃ y : Y, y = hcoeHom (Om R) u y₁ := ⟨_, rfl⟩
  have hyY : y ∈ rLayer (Om R) u := by
    rw [hy]
    exact TwinDisc.coreHull_map_le_rLayer hΩ
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2)
      ⟨(y₁ : ↥(Subgroup.centralizer ({u} : Set Y))), y₁.2, rfl⟩
  have hyu : y * u = u * y := by
    rw [hy]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u y₁)
  have hyv : y * v' = v' * y := by
    rw [← hvH, hy, ← map_mul, ← map_mul, hy₁v]
  have hyt : y * t = t * y := by
    rcases hzv with ht | ht
    · rw [ht]; exact hyv
    · rw [ht]
      calc y * (u * v') = (y * u) * v' := by group
        _ = (u * y) * v' := by rw [hyu]
        _ = u * (y * v') := by group
        _ = u * (v' * y) := by rw [hyv]
        _ = (u * v') * y := by group
  have hy3 : y ^ 3 ^ a = 1 := by rw [hy, ← map_pow, hy₁a, map_one]
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hue : u * e = e * u := hWab _ hd.huW _ heW
  have het : e * t = t * e := hWab _ heW _ hd.hzW
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr het
  have heO : ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
      e * g * e⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ heC) g).mp hg
  have hPH : (QuotientGroup.mk (x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹)) :
      ↥(coreHull (Om R) u) ⧸ N) = QuotientGroup.mk vH := by
    rw [← hprodq, ← hy₁q]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    rfl
  obtain ⟨nH, hnH⟩ : ∃ nH : ↥(coreHull (Om R) u),
      nH = vH⁻¹ * (x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹)) := ⟨_, rfl⟩
  have hnN : nH ∈ N := by
    rw [hnH]
    exact QuotientGroup.eq.mp hPH.symm
  obtain ⟨m, hm⟩ : ∃ m : Y, m = hcoeHom (Om R) u nH := ⟨_, rfl⟩
  have hmu : m * u = u * m := by
    rw [hm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u nH)
  have hmN : m ^ Nat.card N = 1 := by
    have h1 : nH ^ Nat.card N = 1 := by
      have := pow_card_eq_one' (G := ↥N) (x := ⟨nH, hnN⟩)
      exact congrArg Subtype.val this
    rw [hm, ← map_pow, h1, map_one]
  have hP : (u * e) * (y * (u * e) * y⁻¹) * (y ^ 2 * (u * e) * (y ^ 2)⁻¹) = v' * m := by
    have h1 : vH * nH = x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹) := by rw [hnH]; group
    have h2 := congrArg (hcoeHom (Om R) u) h1
    simp only [map_mul, map_inv, map_pow, hvx, hvH] at h2
    rw [hm, hy]
    exact h2.symm
  have hyu' : y * u * y⁻¹ = u := by rw [hyu]; group
  have hy2u : y ^ 2 * u * (y ^ 2)⁻¹ = u := by
    have h : y ^ 2 * u = u * y ^ 2 := (Commute.pow_left (show Commute y u from hyu) 2).eq
    rw [h]; group
  have hue1 : u * (y * e * y⁻¹) = (y * e * y⁻¹) * u := by
    calc u * (y * e * y⁻¹) = (y * u * y⁻¹) * (y * e * y⁻¹) := by rw [hyu']
      _ = y * (u * e) * y⁻¹ := by group
      _ = y * (e * u) * y⁻¹ := by rw [hue]
      _ = (y * e * y⁻¹) * (y * u * y⁻¹) := by group
      _ = (y * e * y⁻¹) * u := by rw [hyu']
  have hue2 : u * (y ^ 2 * e * (y ^ 2)⁻¹) = (y ^ 2 * e * (y ^ 2)⁻¹) * u := by
    calc u * (y ^ 2 * e * (y ^ 2)⁻¹) = (y ^ 2 * u * (y ^ 2)⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := by rw [hy2u]
      _ = y ^ 2 * (u * e) * (y ^ 2)⁻¹ := by group
      _ = y ^ 2 * (e * u) * (y ^ 2)⁻¹ := by rw [hue]
      _ = (y ^ 2 * e * (y ^ 2)⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) := by group
      _ = (y ^ 2 * e * (y ^ 2)⁻¹) * u := by rw [hy2u]
  have hP' : (u * e) * (y * (u * e) * y⁻¹) * (y ^ 2 * (u * e) * (y ^ 2)⁻¹) =
      u * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) := by
    have h1 : y * (u * e) * y⁻¹ = u * (y * e * y⁻¹) := by
      calc y * (u * e) * y⁻¹ = (y * u * y⁻¹) * (y * e * y⁻¹) := by group
        _ = u * (y * e * y⁻¹) := by rw [hyu']
    have h2 : y ^ 2 * (u * e) * (y ^ 2)⁻¹ = u * (y ^ 2 * e * (y ^ 2)⁻¹) := by
      calc y ^ 2 * (u * e) * (y ^ 2)⁻¹ = (y ^ 2 * u * (y ^ 2)⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := by group
        _ = u * (y ^ 2 * e * (y ^ 2)⁻¹) := by rw [hy2u]
    rw [h1, h2]
    exact ClsO.triple_comm_aux hd.hu2 hue hue1 hue2
  obtain ⟨X, hX⟩ : ∃ X : Y, X = e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := ⟨_, rfl⟩
  have hX1 : u * X = v' * m := by rw [hX, ← hP', hP]
  have hX2 : X = u * (v' * m) := by
    calc X = (u * u) * X := by rw [hd.hu2, one_mul]
      _ = u * (u * X) := mul_assoc _ _ _
      _ = u * (v' * m) := by rw [hX1]
  refine ⟨y, hyY, hyu, hyt, ⟨a, hy3⟩, ?_, m, ⟨Nat.card N, hNodd, hmN⟩, hmu, ?_⟩
  · intro o ho hyo
    have hpow := AY.commutator_pow_card hyu heO ho hyo
    rw [hy] at hpow
    have hpow' : (y₁ * x * y₁⁻¹ * x⁻¹) ^ Nat.card ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y))) =
        1 := by
      apply hcoeHom_injective (Om R) u
      rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hvx, map_one]
      exact hpow
    have hq' := congrArg (QuotientGroup.mk' N) hpow'
    simp only [map_pow, map_mul, map_inv, QuotientGroup.mk'_apply, hy₁q] at hq'
    exact AY.commutator_pow_ne_one hxq hqx hqxc (oddCoreOf_odd_natCard _) hq'
  · rcases hzv with ht | ht
    · right
      rw [← hX, hX2, ht]
      group
    · left
      rw [← hX, hX2, ht]
      group

end Y

section Vec

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected

theorem comm_qE_of_zdata (hB : P23E8ACaseB n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hA5 : SecAE R u 5) (hA6 : SecAE R e 6)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥)
    (hOE : oddCoreOf (rLayer (Om R) e) = ⊥)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) (hZ : P23ZData t u e Z)
    {a : Y} (ha : a ∈ Z) {x : Y} (hx : x ∈ rLayer (Om R) e) :
    x * a * x⁻¹ * a⁻¹ ∈ AXV.qE hc D := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hZK : ∀ z ∈ Z, ∀ k ∈ tightCore R ⊔ K', z * k = k * z := by
    intro z hz k hk
    have h := p23_zdata_comm_twins hc hZ hz hk
    rw [hOt, Subgroup.mem_bot] at h
    calc z * k = z * k * z⁻¹ * k⁻¹ * (k * z) := by group
      _ = k * z := by rw [h, one_mul]
  obtain ⟨y, hyY, -, hyt, ⟨a₃, hya⟩, hnm, m, ⟨N, hN, hmN⟩, hmu, hrel⟩ := exists_y_rel_lay hc hA5
  have hyC : y ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hyN : y ∈ Subgroup.normalizer (Z : Set Y) := by
    obtain ⟨o, ho, m', hm', hym⟩ := hZ.frattini y hyC
    rw [hOt, Subgroup.mem_bot] at ho
    rw [hym, ho, one_mul]
    exact hm'.2
  have hyCN : y ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y) := ⟨hyC, hyN⟩
  have hZy : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := fun z hz => (Subgroup.mem_normalizer_iff.mp hyN z).mp hz
  have hA : y * e * y⁻¹ ∈ Z := hZy e hZ.he
  have hA' : y⁻¹ * e * y⁻¹⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) e).mp hZ.he
  have hc₁Z : y⁻¹ * e * y ∈ Z := by
    have h := hA'
    rwa [inv_inv] at h
  have hA2 : y ^ 2 * e * (y ^ 2)⁻¹ ∈ Z := by
    have h := hZy _ hA
    rwa [show y * (y * e * y⁻¹) * y⁻¹ = y ^ 2 * e * (y ^ 2)⁻¹ by
      simp only [sq, mul_inv_rev, mul_assoc]] at h
  have hprod : e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = t := by
    have h := ClsO.E_prod_eq hc hZ hyt hN hmN hmu hrel (o := fun _ => 1) (nn := fun i => y ^ i)
      (E := fun i => y ^ i * e * (y ^ i)⁻¹) (fun _ => Subgroup.one_mem _)
      (fun i => Subgroup.pow_mem _ hyCN i) (fun i => (one_mul _).symm) (fun _ => rfl)
    simp only [pow_zero, pow_one, one_mul, mul_one, inv_one] at h
    exact h
  have hy3e : y ^ 3 * e = e * y ^ 3 := by
    have h1 : y * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) * y⁻¹ = t := by
      rw [hprod, hyt, mul_inv_cancel_right]
    have h2 : y * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) * y⁻¹ =
        (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) * (y ^ 3 * e * (y ^ 3)⁻¹) := by group
    have h3 := hprod.trans (h1.symm.trans h2)
    have hcomm : e * ((y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) =
        (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) * e := hZ.comm _ hZ.he _ (Z.mul_mem hA hA2)
    rw [mul_assoc e, hcomm] at h3
    have h4 : y ^ 3 * e * (y ^ 3)⁻¹ = e := (mul_left_cancel h3).symm
    calc y ^ 3 * e = y ^ 3 * e * (y ^ 3)⁻¹ * y ^ 3 := by group
      _ = e * y ^ 3 := by rw [h4]
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := AY.isPGroup_zpowers_of_pow_eq_one Nat.prime_three hya
  have hy3' : IsPGroup 3 (Subgroup.zpowers y⁻¹) := by rw [Subgroup.zpowers_inv]; exact hy3
  have hye : y * e * y⁻¹ ≠ e := fun h => hnm 1 (Subgroup.one_mem _) (by rw [h]; group)
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have hmt : y * t * y⁻¹ = t := by rw [hyt, mul_inv_cancel_right]
  have hye' : y⁻¹ * e * y⁻¹⁻¹ ≠ e := by
    rw [inv_inv]
    intro h
    apply hye
    calc y * e * y⁻¹ = y * (y⁻¹ * e * y) * y⁻¹ := by rw [h]
      _ = e := by group
  have hc₁e : y⁻¹ * e * y ≠ e := by
    have h := hye'
    rwa [inv_inv] at h
  have hc₁O : y⁻¹ * e * y ∈ p23Orb Z t e := ⟨y⁻¹, Subgroup.inv_mem _ hyCN, by rw [inv_inv]⟩
  obtain ⟨hy2a, -⟩ := AXV.y_sq_conj hy3e
  have hT1 : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y * e * y⁻¹} : Set Y) :=
    AXV.cent_te hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu hyY hyt hy3 hye
      (hZ.comm _ hA _ hZ.ht) (hZ.comm _ hA _ hZ.he) (hZK _ hA)
  have hT2 : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) := by
    have h := AXV.cent_te hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu
      (Subgroup.inv_mem _ hyY) hyt' hy3' hye'
      (hZ.comm _ hA' _ hZ.ht) (hZ.comm _ hA' _ hZ.he) (hZK _ hA')
    rwa [inv_inv] at h
  obtain ⟨M, hM, M', hM', hMu, hM'u, hMM', zM, hzM, hzM', hzMue⟩ :=
    AXV.u_other hc hA5 h2grp hOu
  have hgte : g⁻¹ * u * g⁻¹⁻¹ = t * e := by
    rw [← AXV.g_te hc]
    group
  have hJ₀te : conjSub g⁻¹ M ≤ Subgroup.centralizer ({t * e} : Set Y) := by
    have h := AXV.conj_le_cent hMu g⁻¹
    rwa [hgte] at h
  have hJ₀'te : conjSub g⁻¹ M' ≤ Subgroup.centralizer ({t * e} : Set Y) := by
    have h := AXV.conj_le_cent hM'u g⁻¹
    rwa [hgte] at h
  have hJ₀Ω : conjSub g⁻¹ M ∈ Om R := hΩ.conjInvariant g⁻¹ M hM
  have hJ₀'Ω : conjSub g⁻¹ M' ∈ Om R := hΩ.conjInvariant g⁻¹ M' hM'
  have hJ₀L := TwinPerpV3.A6b.le_rLayer_of_mem hJ₀Ω (h2grp _ hJ₀Ω) hJ₀te
  have hJ₀'L := TwinPerpV3.A6b.le_rLayer_of_mem hJ₀'Ω (h2grp _ hJ₀'Ω) hJ₀'te
  have hz₀ := hzM.conj g⁻¹
  have hz₀' := hzM'.conj g⁻¹
  have hz₀t : g⁻¹ * zM * g⁻¹⁻¹ ≠ t := by
    intro h
    apply hzMue
    calc zM = g * (g⁻¹ * zM * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [h]
      _ = u * e := hd.hgt
  have hJ₀ne : conjSub g⁻¹ M' ≠ conjSub g⁻¹ M := by
    intro h
    apply hMM'
    have h' := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at h'
    exact h'.symm
  have hc₁C : y⁻¹ * e * y ∈ Subgroup.centralizer ({e} : Set Y) := hZ.le_cent hZ.he hc₁Z
  obtain ⟨w₁, hw₁⟩ := AXV.exists_acts (hc := hc) (D := D) hc₁C
  have hw₁p : w₁.perm = 1 := by
    have hne : conjSub y (conjSub g⁻¹ M') ≠ conjSub y (conjSub g⁻¹ M) := by
      intro h
      apply hJ₀ne
      have h' := congrArg (conjSub y⁻¹) h
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h'
    have hzt' : y * (g⁻¹ * zM * g⁻¹⁻¹) * y⁻¹ ≠ t := by
      intro h
      apply hz₀t
      calc g⁻¹ * zM * g⁻¹⁻¹ = y⁻¹ * (y * (g⁻¹ * zM * g⁻¹⁻¹) * y⁻¹) * y := by group
        _ = y⁻¹ * t * y := by rw [h]
        _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [hmt]
        _ = t := by group
    have h1 : conjSub y (conjSub g⁻¹ M) ≤ Subgroup.centralizer ({e} : Set Y) := by
      have h := AXV.conj_le_cent (hJ₀L.trans hT2) y
      rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at h
    have h2 : conjSub y (conjSub g⁻¹ M') ≤ Subgroup.centralizer ({e} : Set Y) := by
      have h := AXV.conj_le_cent (hJ₀'L.trans hT2) y
      rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at h
    have h3 : conjSub y (conjSub g⁻¹ M) ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) := by
      have h := AXV.conj_le_cent (hJ₀L.trans hT1) y
      rwa [hy2a] at h
    have h4 : conjSub y (conjSub g⁻¹ M') ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) := by
      have h := AXV.conj_le_cent (hJ₀'L.trans hT1) y
      rwa [hy2a] at h
    exact AXV.perm_one (hc := hc) (D := D) h2grp hOe hc₁C (hZK _ hc₁Z) (hΩ.conjInvariant y _ hJ₀Ω)
      (hΩ.conjInvariant y _ hJ₀'Ω) h1 h2 hne (hz₀.conj y) (hz₀'.conj y) hzt'
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (h3 hk)).symm)
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (h4 hk)).symm) hw₁
  obtain ⟨β, hβ, b₀, hlA, hlA', hzt, htA, htA', -⟩ := ZTwo.twin_labels hc D
  have hw₁B : ∀ b : Bool, ∀ q ∈ memBar β hβ b, mkQ 6 w₁ * q * (mkQ 6 w₁)⁻¹ = q := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact AXV.acts_cent (hc := hc) hc₁C hw₁
        (fun k hk => hZK _ hc₁Z k (Subgroup.mem_sup_left hk)) hlA
    · have hb' := AXV.bool_eq_not_of_ne hb
      subst hb'
      exact AXV.acts_cent (hc := hc) hc₁C hw₁
        (fun k hk => hZK _ hc₁Z k (Subgroup.mem_sup_right hk)) hlA'
  obtain ⟨dd, hdd⟩ : ∃ d : Fin 6, ∀ i j, i ≠ d → j ≠ d → w₁.vec i = w₁.vec j := by
    rcases AXV.vec_type hβ hw₁p hw₁B with h | h
    · exact h
    · exact absurd h (AXV.not_zbar (hc := hc) (D := D) hOE hT2 hy3e hyt hye hzt hc₁C hw₁)
  have hne1 : mkQ 6 w₁ ≠ 1 := by
    intro h1
    have hfix : ∀ q, TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc)
        ⟨y⁻¹ * e * y, hc₁C⟩ q = q := by
      apply AXV.eq_of_perfect D.perfect
        (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨y⁻¹ * e * y, hc₁C⟩).toMonoidHom
      intro q
      apply D.ker_le
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show D.φ (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨y⁻¹ * e * y, hc₁C⟩ q) *
        (D.φ q)⁻¹ = 1
      rw [hw₁ q, h1]
      group
    have hact : ClsO.actHom hc hZ ⟨y⁻¹ * e * y, hc₁Z⟩ = 1 := MulEquiv.ext fun q => hfix q
    exact not_centModE_orbit hc hZ D hc₁O hc₁e (ClsO.centModE_of_act_eq_one hc hZ hact)
  have hddβ : dd ∉ β := by
    intro hdβ
    obtain ⟨-, k, hk⟩ := ClsO.form_of_centralizes hβ w₁ hw₁B
    obtain ⟨b, hbβ, hbd⟩ := Finset.exists_mem_ne (by rw [hβ]; norm_num) dd
    apply hne1
    refine ZTwo.mkQ_eq_one_of_const w₁ hw₁p k fun i => ?_
    by_cases hi : i = dd
    · rw [hi]
      exact hk dd hdβ
    · rw [hdd i b hi hbd]
      exact hk b hbβ
  have haC : a ∈ Subgroup.centralizer ({e} : Set Y) := hZ.le_cent hZ.he ha
  obtain ⟨w, hw, hwB⟩ := ClsO.exists_cent_w hc D hlA hlA' hzt htA htA' haC (hZ.comm _ ha _ hZ.ht)
    (fun l hl => p23_zdata_comm_twins hc hZ ha hl)
  have hcomm := comm_of_acts D.toAEData hw hw₁ (fun q => by
    rw [← ZTwo.secAut_mul hc, ← ZTwo.secAut_mul hc,
      show (⟨a, haC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) * ⟨y⁻¹ * e * y, hc₁C⟩ =
        ⟨y⁻¹ * e * y, hc₁C⟩ * ⟨a, haC⟩ from Subtype.ext (hZ.comm _ ha _ hc₁Z)])
  have hwp : w.perm = 1 :=
    perm_one_of_comm hβ (ClsO.form_of_centralizes hβ w hwB).1 hw₁p hddβ hdd hne1 hcomm
  exact AXV.comm_qE (hc := hc) (D := D) haC hw hwp hx

theorem comm_two_of_mem_Ea (hB : P23E8ACaseB n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hA5 : SecAE R u 5) (hA6 : SecAE R e 6)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥)
    (hOE : oddCoreOf (rLayer (Om R) e) = ⊥)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (hVe : V ≤ aSub R Z e) (heX : e ∈ rLayerSub (Om R) V) {f : Y} (hfZ : f ∈ Z)
    (hfX : f ∈ rLayerSub (Om R) V) :
    ∀ x ∈ Ea (p23SecFamV R V)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨e, heX⟩),
      ∃ k : ℕ, (x * QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩ *
        x⁻¹ * (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩)⁻¹) ^
          (2 ^ k) = 1 := by
  obtain ⟨-, hE₀E, -, -⟩ := LemL.p23_cover_V hc hZ hVZ (e_mem_orb Z t e) hVe
  intro xb hxb
  rw [LemL.Ea_eq_secImage hc hZ (e_mem_orb Z t e) heX] at hxb
  obtain ⟨x, hx, rfl⟩ := hxb
  have hxE : (x : Y) ∈ rLayer (Om R) e := hE₀E (Subgroup.mem_subgroupOf.mp hx)
  have hq := comm_qE_of_zdata hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu hOE hOe D hZ hfZ hxE
  obtain ⟨k, hk⟩ := AXV.qE_isPGroup (hc := hc) (D := D) hOE ⟨_, hq⟩
  refine ⟨k, ?_⟩
  have hk' : ((x : Y) * f * (x : Y)⁻¹ * f⁻¹) ^ (2 ^ k) = 1 :=
    (Subgroup.coe_pow _ _ _).symm.trans (congrArg Subtype.val hk)
  have h1 : (x * ⟨f, hfX⟩ * x⁻¹ * (⟨f, hfX⟩ : ↥(rLayerSub (Om R) V))⁻¹) ^ (2 ^ k) = 1 :=
    Subtype.ext ((Subgroup.coe_pow _ _ _).trans hk')
  have h2 := congrArg (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V))) h1
  simpa only [map_mul, map_inv, map_pow, map_one] using h2

theorem not_central_inv_mul (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {f : Y} (hf : f ∈ p23Orb Z t e)
    (hfe : f ≠ e) (hVe : V ≤ aSub R Z e) (hVf : V ≤ aSub R Z f) (heX : e ∈ rLayerSub (Om R) V)
    (hfX : f ∈ rLayerSub (Om R) V) :
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨e, heX⟩)⁻¹ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩ ∉
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) := by
  intro hz
  set X := rLayerSub (Om R) V with hX
  set eb := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨e, heX⟩ with heb
  set fb := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨f, hfX⟩ with hfb
  have key : ∀ c : SecQuot X, c * fb = fb * c ↔ c * eb = eb * c := by
    intro c
    have hzc : c * (eb⁻¹ * fb) = eb⁻¹ * fb * c := Subgroup.mem_center_iff.mp hz c
    have h1 : c * fb = c * eb * (eb⁻¹ * fb) := by group
    have h2 : fb * c = eb * c * (eb⁻¹ * fb) := by
      calc fb * c = eb * (eb⁻¹ * fb * c) := by group
        _ = eb * (c * (eb⁻¹ * fb)) := by rw [hzc]
        _ = eb * c * (eb⁻¹ * fb) := by group
    rw [h1, h2]
    exact mul_left_inj _
  have hcent : Subgroup.centralizer ({fb} : Set (SecQuot X)) =
      Subgroup.centralizer ({eb} : Set (SecQuot X)) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact key c
  have hEa : Ea (p23SecFamV R V) fb = Ea (p23SecFamV R V) eb := by
    apply le_antisymm
    · exact Ea_le fun L hL hLc => le_Ea hL (by rw [← hcent]; exact hLc)
    · exact Ea_le fun L hL hLc => le_Ea hL (by rw [hcent]; exact hLc)
  have heE := mem_Ea_self hc hZ hVZ (e_mem_orb Z t e) hVe heX
  have hfE := mem_Ea_self hc hZ hVZ hf hVf hfX
  have hzE : eb⁻¹ * fb ∈ Ea (p23SecFamV R V) fb :=
    (Ea (p23SecFamV R V) fb).mul_mem ((Ea (p23SecFamV R V) fb).inv_mem (by rw [hEa]; exact heE)) hfE
  have h1 := central_Ea hc hZ hVZ D hf hVf hfX (not_central_f hc hZ hVZ D hf hfe hVe hfX) _ hz hzE
  have h2 : (⟨e, heX⟩ : ↥X)⁻¹ * ⟨f, hfX⟩ ∈ classicalInvolutionOddCore ↥X := by
    have h3 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ((⟨e, heX⟩ : ↥X)⁻¹ * ⟨f, hfX⟩) = 1 := by
      rw [map_mul, map_inv]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp h3
  have hfZ : f ∈ Z := hZ.orb_le hf
  have hsq : ((⟨e, heX⟩ : ↥X)⁻¹ * ⟨f, hfX⟩) * ((⟨e, heX⟩ : ↥X)⁻¹ * ⟨f, hfX⟩) = 1 := by
    apply Subtype.ext
    show (e⁻¹ * f) * (e⁻¹ * f) = 1
    have he2 : e * e = 1 := hZ.sq e hZ.he
    have hf2 : f * f = 1 := hZ.sq f hfZ
    have hfe' : f * e = e * f := hZ.comm _ hfZ _ hZ.he
    rw [inv_eq_of_mul_eq_one_right he2]
    calc e * f * (e * f) = e * (f * e) * f := by group
      _ = e * (e * f) * f := by rw [hfe']
      _ = (e * e) * (f * f) := by group
      _ = 1 := by rw [he2, hf2, one_mul]
  have h4 := Asc77.eq_one_of_isPGroup_of_mem_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥X) h2
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq)
  apply hfe
  have h5 : e⁻¹ * f = 1 := congrArg Subtype.val h4
  calc f = e * (e⁻¹ * f) := by group
    _ = e := by rw [h5, mul_one]

end Vec

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
