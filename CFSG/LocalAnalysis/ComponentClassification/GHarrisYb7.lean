module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb6
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb5

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.card_ut_ab : (Finset.univ.filter fun u : UT3 F4c => u.a = 0 ∧ u.b = 0).card =
    4 := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

theorem pow_conj_mem {X : Type*} [Group X] {H : Subgroup X} {w : X}
    (h : ∀ e ∈ H, w * e * w⁻¹ ∈ H) (k : ℕ) : ∀ e ∈ H, w ^ k * e * (w ^ k)⁻¹ ∈ H := by
  induction k with
  | zero => intro e he; simpa using he
  | succ k ih =>
    intro e he
    rw [pow_succ, show w ^ k * w * e * (w ^ k * w)⁻¹ = w ^ k * (w * e * w⁻¹) * (w ^ k)⁻¹ by
      group]
    exact ih _ (h e he)

theorem pow_comm_of_comm {X : Type*} [Group X] {w c : X} (h : w * c = c * w) (k : ℕ) :
    w ^ k * c = c * w ^ k := ((Commute.pow_left (show Commute w c from h) k)).eq

namespace GHSylow

variable (D : GHSylow Y)

theorem exists_odd_lift (w : D.Xt) : ∃ (g : D.Y1) (a : ℕ), D.piX g = w ∧
    Odd (orderOf (g ^ (2 ^ a))) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers D.lY) w
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g, a, rfl, ?_⟩
  rw [orderOf_pow_of_dvd (pow_pos (by norm_num) a).ne' (by rw [hgm]; exact dvd_mul_right _ _),
    hgm, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
  exact hm


theorem centralizes_Et {w : D.Xt} (hodd : Odd (orderOf w))
    (hZ : ∀ c ∈ D.Et ⊓ D.Ft, w * c = c * w) (hN : ∀ e ∈ D.Et, w * e * w⁻¹ ∈ D.Et) :
    ∀ e ∈ D.Et, w * e = e * w := by
  obtain ⟨g, a, rfl, hp⟩ := D.exists_odd_lift w
  set p := g ^ (2 ^ a) with hpdef
  have hpX : D.piX p = D.piX g ^ (2 ^ a) := by rw [hpdef, map_pow]
  have hcent := D.centralizes_E_of_odd (p := (p : Y)) p.2 (by rwa [Subgroup.orderOf_coe])
    (fun v hvE hvF => by
      have hvY : v ∈ D.Y1 := D.E_le_Y1 hvE
      have hc : D.piX p * D.piX ⟨v, hvY⟩ = D.piX ⟨v, hvY⟩ * D.piX p := by
        rw [hpX]
        exact pow_comm_of_comm (hZ _ (mem_inf.mpr ⟨(D.piX_mem_Et_iff _).mpr hvE,
          (D.piX_mem_Ft_iff _).mpr hvF⟩)) _
      have h1 : D.piX (p * ⟨v, hvY⟩ * p⁻¹) = D.piX ⟨v, hvY⟩ := by
        rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        D.mem_zpowers_l_iff] at h1
      simpa using h1)
    (fun e he => by
      have heY : e ∈ D.Y1 := D.E_le_Y1 he
      have h1 : D.piX (p * ⟨e, heY⟩ * p⁻¹) ∈ D.Et := by
        rw [map_mul, map_mul, map_inv, hpX]
        exact pow_conj_mem hN _ _ ((D.piX_mem_Et_iff _).mpr he)
      exact (D.piX_mem_Et_iff _).mp h1)
  have hpE : ∀ e ∈ D.Et, D.piX p * e = e * D.piX p := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hcent _ (mem_subgroupOf.mp hy)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (p : Y) * y = (p : Y) * y * (p : Y)⁻¹ * p := by group
      _ = y * p := by rw [h]
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := D.piX g) (n := 2 ^ a)
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd))
  intro e he
  rw [← hk, ← hpX]
  exact pow_comm_of_comm (hpE e he) k

theorem centralizes_Ft {w : D.Xt} (hodd : Odd (orderOf w))
    (hZ : ∀ c ∈ D.Et ⊓ D.Ft, w * c = c * w) (hN : ∀ f ∈ D.Ft, w * f * w⁻¹ ∈ D.Ft) :
    ∀ f ∈ D.Ft, w * f = f * w := by
  obtain ⟨g, a, rfl, hp⟩ := D.exists_odd_lift w
  set p := g ^ (2 ^ a) with hpdef
  have hpX : D.piX p = D.piX g ^ (2 ^ a) := by rw [hpdef, map_pow]
  have hcent := D.centralizes_F_of_odd (p := (p : Y)) p.2 (by rwa [Subgroup.orderOf_coe])
    (fun v hvE hvF => by
      have hvY : v ∈ D.Y1 := D.E_le_Y1 hvE
      have hc : D.piX p * D.piX ⟨v, hvY⟩ = D.piX ⟨v, hvY⟩ * D.piX p := by
        rw [hpX]
        exact pow_comm_of_comm (hZ _ (mem_inf.mpr ⟨(D.piX_mem_Et_iff _).mpr hvE,
          (D.piX_mem_Ft_iff _).mpr hvF⟩)) _
      have h1 : D.piX (p * ⟨v, hvY⟩ * p⁻¹) = D.piX ⟨v, hvY⟩ := by
        rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        D.mem_zpowers_l_iff] at h1
      simpa using h1)
    (fun f hf => by
      have hfY : f ∈ D.Y1 := D.F_le_Y1 hf
      have h1 : D.piX (p * ⟨f, hfY⟩ * p⁻¹) ∈ D.Ft := by
        rw [map_mul, map_mul, map_inv, hpX]
        exact pow_conj_mem hN _ _ ((D.piX_mem_Ft_iff _).mpr hf)
      exact (D.piX_mem_Ft_iff _).mp h1)
  have hpF : ∀ f ∈ D.Ft, D.piX p * f = f * D.piX p := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hcent _ (mem_subgroupOf.mp hy)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (p : Y) * y = (p : Y) * y * (p : Y)⁻¹ * p := by group
      _ = y * p := by rw [h]
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := D.piX g) (n := 2 ^ a)
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd))
  intro f hf
  rw [← hk, ← hpX]
  exact pow_comm_of_comm (hpF f hf) k

theorem card_Et_inf_Ft
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    Nat.card ↥(D.Et ⊓ D.Ft) = 4 := by
  classical
  set T := ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)
  have hle : D.Et ⊓ D.Ft ≤ T := inf_le_left.trans (D.Et_le hO hz)
  have hp : ∀ w (hw : w ∈ T), w ∈ D.Et ⊓ D.Ft ↔
      (D.tUT hO hz ⟨w, hw⟩).a = 0 ∧ (D.tUT hO hz ⟨w, hw⟩).b = 0 := by
    intro w hw
    rw [mem_inf, D.mem_Et_iff_tUT hO hz hw, D.mem_Ft_iff_tUT hO hz hw, and_comm]
  rw [← SE.card_ut_ab, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨D.tUT hO hz ⟨w, hle w.2⟩, (hp w (hle w.2)).mp w.2⟩
      invFun := fun u => ⟨((D.tUT hO hz).symm u.1 : D.Xt), by
        rw [hp _ (Subtype.mem _)]; simpa using u.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp only [Subtype.coe_eta,
        MulEquiv.apply_symm_apply]) }

theorem exists_centralizes_ZT
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) {P : Subgroup D.Xt}
    (hP9 : 9 ∣ Nat.card P) (hPE : ∀ w ∈ P, ∀ e ∈ D.Et, w * e * w⁻¹ ∈ D.Et)
    (hPF : ∀ w ∈ P, ∀ f ∈ D.Ft, w * f * w⁻¹ ∈ D.Ft) :
    ∃ w ∈ P, w ≠ 1 ∧ ∀ c ∈ D.Et ⊓ D.Ft, w * c = c * w := by
  set Z := D.Et ⊓ D.Ft with hZ
  have hmem : ∀ w ∈ P, ∀ c ∈ Z, w * c * w⁻¹ ∈ Z := fun w hw c hc =>
    mem_inf.mpr ⟨hPE w hw c (mem_inf.mp hc).1, hPF w hw c (mem_inf.mp hc).2⟩
  have hmem' : ∀ w ∈ P, ∀ c ∈ Z, w⁻¹ * c * w ∈ Z := fun w hw c hc => by
    simpa using hmem w⁻¹ (inv_mem hw) c hc
  let ψ : P →* Equiv.Perm Z :=
    { toFun := fun w =>
        { toFun := fun c => ⟨w * c * w⁻¹, hmem w w.2 c c.2⟩
          invFun := fun c => ⟨w⁻¹ * c * w, hmem' w w.2 c c.2⟩
          left_inv := fun c => Subtype.ext (by simp [mul_assoc])
          right_inv := fun c => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun c => Subtype.ext (by simp)
      map_mul' := fun w₁ w₂ => Equiv.ext fun c => Subtype.ext (by simp [mul_assoc]) }
  by_contra hno
  push Not at hno
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    by_contra hw1
    obtain ⟨c, hc, hcw⟩ := hno w w.2 (fun h => hw1 (Subtype.ext h))
    apply hcw
    have h2 : (w : D.Xt) * c * (w : D.Xt)⁻¹ = c :=
      congrArg Subtype.val (congrArg (fun σ => (σ ⟨c, hc⟩ : Z)) hw)
    calc (w : D.Xt) * c = w * c * (w : D.Xt)⁻¹ * w := by group
      _ = c * w := by rw [h2]
  have hdvd : Nat.card P ∣ Nat.card (Equiv.Perm Z) := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at this
  rw [Nat.card_perm, hZ, D.card_Et_inf_Ft hO hz] at hdvd
  have := hP9.trans hdvd
  norm_num at this

end GHSylow

end CFSG.ComponentClassification.GHarris
