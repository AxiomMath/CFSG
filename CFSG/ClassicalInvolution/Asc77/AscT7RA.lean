module

public import CFSG.ClassicalInvolution.Asc77.AscT7FC
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section PureGroup

namespace T7R

variable {G : Type} [Group G]

theorem commute_of_comm_eq_one {n x : G} (h : n * x * n⁻¹ * x⁻¹ = 1) : n * x = x * n := by
  have h1 : n * x * n⁻¹ = x := by
    have := congrArg (fun y => y * x) h
    simpa [mul_assoc] using this
  calc n * x = (n * x * n⁻¹) * n := by group
    _ = x * n := by rw [h1]

theorem comm_mul_of_commute {n a b : G}
    (h : a * (n * b * n⁻¹ * b⁻¹) = (n * b * n⁻¹ * b⁻¹) * a) :
    n * (a * b) * n⁻¹ * (a * b)⁻¹ = (n * a * n⁻¹ * a⁻¹) * (n * b * n⁻¹ * b⁻¹) := by
  calc n * (a * b) * n⁻¹ * (a * b)⁻¹
      = (n * a * n⁻¹ * a⁻¹) * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = (n * a * n⁻¹ * a⁻¹) * ((n * b * n⁻¹ * b⁻¹) * a * a⁻¹) := by rw [h]
    _ = (n * a * n⁻¹ * a⁻¹) * (n * b * n⁻¹ * b⁻¹) := by group

theorem exists_fourGroup_of_pair {B : Subgroup G} {x y n : G} (hxB : x ∈ B) (hyB : y ∈ B)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hcomm : x * y = y * x) (hnx : n * x = x * n) (hny : n * y = y * n) :
    ∃ A : Subgroup G, A ≤ B ∧ IsElemAbelian2 A 2 ∧ ∀ w ∈ A, n * w = w * n := by
  refine ⟨Subgroup.closure {x, y}, ?_, T7A.isElemAbelian2_closure_pair hx2 hy2 hx1 hy1 hxy hcomm,
    ?_⟩
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hxB
    · exact hyB
  · intro w hw
    have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({n} : Set G) := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hnx.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hny.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm

theorem mul_ne_one_of_ne {x y : G} (hx : x * x = 1) (hxy : x ≠ y) : x * y ≠ 1 := by
  intro h
  apply hxy
  have h1 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1]
  exact (inv_eq_of_mul_eq_one_right hx).symm

theorem exists_fourGroup_fixed {a b c n ζ : G}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b)
    (hc : c ∉ Subgroup.closure ({a, b} : Set G))
    (hζa : ζ * a = a * ζ) (hζb : ζ * b = b * ζ) (hζ2 : ζ * ζ = 1)
    (hna : n * a * n⁻¹ * a⁻¹ = 1 ∨ n * a * n⁻¹ * a⁻¹ = ζ)
    (hnb : n * b * n⁻¹ * b⁻¹ = 1 ∨ n * b * n⁻¹ * b⁻¹ = ζ)
    (hnc : n * c * n⁻¹ * c⁻¹ = 1 ∨ n * c * n⁻¹ * c⁻¹ = ζ) :
    ∃ A : Subgroup G, A ≤ Subgroup.closure ({a, b, c} : Set G) ∧ IsElemAbelian2 A 2 ∧
      ∀ w ∈ A, n * w = w * n := by
  set B : Subgroup G := Subgroup.closure ({a, b, c} : Set G) with hB
  have haB : a ∈ B := Subgroup.subset_closure (by simp)
  have hbB : b ∈ B := Subgroup.subset_closure (by simp)
  have hcB : c ∈ B := Subgroup.subset_closure (by simp)
  have haS : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbS : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hgen : ∀ x ∈ ({a, b, c} : Set G), ∀ y ∈ ({a, b, c} : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact hab
    · exact hac
    · exact hab.symm
    · rfl
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · rfl
  have hgen2 : ∀ x ∈ ({a, b, c} : Set G), x * x = 1 := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ha2
    · exact hb2
    · exact hc2
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := T7A.commutes_closure hgen
  have hsq : ∀ x ∈ B, x * x = 1 := T7A.sq_closure hgen2 hgen
  have hc1 : c ≠ 1 := fun h => hc (h ▸ Subgroup.one_mem _)
  have hca : c ≠ a := fun h => hc (h ▸ haS)
  have hcb : c ≠ b := fun h => hc (h ▸ hbS)
  have hcab : c ≠ a * b := fun h => hc (h ▸ Subgroup.mul_mem _ haS hbS)
  have hbc_a : a ≠ b * c := by
    intro h
    apply hc
    have : c = b * a := by
      calc c = b * (b * c) := by rw [← mul_assoc, hb2, one_mul]
        _ = b * a := by rw [← h]
    rw [this]
    exact Subgroup.mul_mem _ hbS haS
  have hac_b : b ≠ a * c := by
    intro h
    apply hc
    have : c = a * b := by
      calc c = a * (a * c) := by rw [← mul_assoc, ha2, one_mul]
        _ = a * b := by rw [← h]
    rw [this]
    exact Subgroup.mul_mem _ haS hbS
  have hab1 : a * b ≠ 1 := mul_ne_one_of_ne ha2 hab'
  have hac1 : a * c ≠ 1 := mul_ne_one_of_ne ha2 hca.symm
  have hbc1 : b * c ≠ 1 := mul_ne_one_of_ne hb2 hcb.symm
  have habB : a * b ∈ B := B.mul_mem haB hbB
  have hacB : a * c ∈ B := B.mul_mem haB hcB
  have hbcB : b * c ∈ B := B.mul_mem hbB hcB
  have habac : a * b ≠ a * c := fun h => hcb.symm (mul_left_cancel h)
  have dab : ∀ d₁ d₂ : G, n * a * n⁻¹ * a⁻¹ = d₁ → n * b * n⁻¹ * b⁻¹ = d₂ →
      a * d₂ = d₂ * a → n * (a * b) * n⁻¹ * (a * b)⁻¹ = d₁ * d₂ := by
    intro d₁ d₂ h₁ h₂ hc'
    rw [← h₁, ← h₂]
    exact comm_mul_of_commute (by rw [h₂]; exact hc')
  have dac : ∀ d₁ d₂ : G, n * a * n⁻¹ * a⁻¹ = d₁ → n * c * n⁻¹ * c⁻¹ = d₂ →
      a * d₂ = d₂ * a → n * (a * c) * n⁻¹ * (a * c)⁻¹ = d₁ * d₂ := by
    intro d₁ d₂ h₁ h₂ hc'
    rw [← h₁, ← h₂]
    exact comm_mul_of_commute (by rw [h₂]; exact hc')
  have dbc : ∀ d₁ d₂ : G, n * b * n⁻¹ * b⁻¹ = d₁ → n * c * n⁻¹ * c⁻¹ = d₂ →
      b * d₂ = d₂ * b → n * (b * c) * n⁻¹ * (b * c)⁻¹ = d₁ * d₂ := by
    intro d₁ d₂ h₁ h₂ hc'
    rw [← h₁, ← h₂]
    exact comm_mul_of_commute (by rw [h₂]; exact hc')
  have hfin : ∀ x y : G, x ∈ B → y ∈ B → x ≠ 1 → y ≠ 1 → x ≠ y →
      n * x * n⁻¹ * x⁻¹ = 1 → n * y * n⁻¹ * y⁻¹ = 1 →
      ∃ A : Subgroup G, A ≤ B ∧ IsElemAbelian2 A 2 ∧ ∀ w ∈ A, n * w = w * n := by
    intro x y hx hy hx1 hy1 hxy hnx hny
    exact exists_fourGroup_of_pair hx hy (hsq x hx) (hsq y hy) hx1 hy1 hxy (hcomm x hx y hy)
      (commute_of_comm_eq_one hnx) (commute_of_comm_eq_one hny)
  rcases hna with ha | ha <;> rcases hnb with hb | hb <;> rcases hnc with hc' | hc'
  · exact hfin a b haB hbB ha1 hb1 hab' ha hb
  · exact hfin a b haB hbB ha1 hb1 hab' ha hb
  · exact hfin a c haB hcB ha1 hc1 hca.symm ha hc'
  · exact hfin a (b * c) haB hbcB ha1 hbc1 hbc_a ha
      (by rw [dbc ζ ζ hb hc' hζb.symm, hζ2])
  · exact hfin b c hbB hcB hb1 hc1 hcb.symm hb hc'
  · exact hfin b (a * c) hbB hacB hb1 hac1 hac_b hb
      (by rw [dac ζ ζ ha hc' hζa.symm, hζ2])
  · exact hfin c (a * b) hcB habB hc1 hab1 hcab hc'
      (by rw [dab ζ ζ ha hb hζa.symm, hζ2])
  · exact hfin (a * b) (a * c) habB hacB hab1 hac1 habac
      (by rw [dab ζ ζ ha hb hζa.symm, hζ2])
      (by rw [dac ζ ζ ha hc' hζa.symm, hζ2])

end T7R

end PureGroup

open T7R

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

@[expose] def GoodElt (Ω : Set (Subgroup G)) (W : Subgroup G) (a : G) : Prop :=
  a ∈ W ∧ ∀ ρ : Rep Ω W, ρ.r * a * ρ.r⁻¹ * a⁻¹ ∈ ρ.K ⊓ W

namespace Ctx

variable (c : Ctx p f Ω W)

include c

theorem good_of_mem_inf (σ : Rep Ω W) {v : G} (hv : v ∈ σ.K ⊓ W) : GoodElt Ω W v := by
  refine ⟨hv.2, fun ρ => ?_⟩
  by_cases hK : ρ.K = σ.K
  · have hvρ : v ∈ ρ.K ⊓ W := hK ▸ hv
    rw [c.conj_inv ρ hvρ]
    exact (ρ.K ⊓ W).mul_mem ((ρ.K ⊓ W).inv_mem hvρ) ((ρ.K ⊓ W).inv_mem hvρ)
  · exact c.comm_mem ρ σ hK hv

theorem good_mul {a b : G} (ha : GoodElt Ω W a) (hb : GoodElt Ω W b) :
    GoodElt Ω W (a * b) := by
  refine ⟨W.mul_mem ha.1 hb.1, fun ρ => ?_⟩
  have h := comm_mul_of_commute (n := ρ.r) (a := a) (b := b)
    (c.comm_W a ha.1 _ (hb.2 ρ).2)
  rw [h]
  exact (ρ.K ⊓ W).mul_mem (ha.2 ρ) (hb.2 ρ)

theorem comm_eq_one_or (ρ : Rep Ω W) {ζ : G} (hζ : IsUniqueInvolution ρ.K ζ) {a : G}
    (ha : GoodElt Ω W a) (ha2 : a * a = 1) :
    ρ.r * a * ρ.r⁻¹ * a⁻¹ = 1 ∨ ρ.r * a * ρ.r⁻¹ * a⁻¹ = ζ := by
  have hb : ρ.r * a * ρ.r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp ρ.r_mem_normalizer a).mp ha.1
  have hb2 : (ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹) = 1 := by
    calc (ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹) = ρ.r * (a * a) * ρ.r⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hd2 : (ρ.r * a * ρ.r⁻¹ * a⁻¹) * (ρ.r * a * ρ.r⁻¹ * a⁻¹) = 1 := by
    have hcomm := c.comm_W _ hb a ha.1
    rw [hinv]
    calc (ρ.r * a * ρ.r⁻¹ * a) * (ρ.r * a * ρ.r⁻¹ * a)
        = (ρ.r * a * ρ.r⁻¹) * (a * (ρ.r * a * ρ.r⁻¹)) * a := by group
      _ = (ρ.r * a * ρ.r⁻¹) * ((ρ.r * a * ρ.r⁻¹) * a) * a := by rw [← hcomm]
      _ = ((ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹)) * (a * a) := by group
      _ = 1 := by rw [hb2, ha2, one_mul]
  exact hζ.unique _ (ha.2 ρ).1 hd2

theorem exists_fourGroup_centralized (ρ : Rep Ω W) {a b d : G}
    (ha : GoodElt Ω W a) (hb : GoodElt Ω W b) (hd : GoodElt Ω W d)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hd2 : d * d = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hdab : d ∉ Subgroup.closure ({a, b} : Set G)) :
    ∃ A : Subgroup G, A ≤ Subgroup.closure ({a, b, d} : Set G) ∧ IsElemAbelian2 A 2 ∧
      ∀ w ∈ A, ρ.r * w = w * ρ.r := by
  obtain ⟨ζ, hζ⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq ρ.hK
  have hζW : ζ ∈ W := c.mem_W_of_isUniqueInvolution ρ hζ
  exact exists_fourGroup_fixed ha2 hb2 hd2 (c.comm_W a ha.1 b hb.1) (c.comm_W a ha.1 d hd.1)
    (c.comm_W b hb.1 d hd.1) ha1 hb1 hab hdab (c.comm_W ζ hζW a ha.1) (c.comm_W ζ hζW b hb.1)
    hζ.sq (c.comm_eq_one_or ρ hζ ha ha2) (c.comm_eq_one_or ρ hζ hb hb2)
    (c.comm_eq_one_or ρ hζ hd hd2)

theorem exists_mul_self_eq (ρ : Rep Ω W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    ∃ w ∈ ρ.R ⊓ W, w * w = z ∧ orderOf w = 4 := by
  obtain ⟨w, hwRW, hw4⟩ := exists_orderOf_four c.hp c.hq c.hΩ c.hW ρ.hR
  refine ⟨w, hwRW, ?_, hw4⟩
  have hw4' : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw4] at this
  have hw2 : w * w ≠ 1 := fun h => by
    have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hw4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hwwsq : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hw4'
  have hwwR : w * w ∈ ρ.R := ρ.R.mul_mem hwRW.1 hwRW.1
  have hwwK : w * w ∈ ρ.K := ρ.hRK.1 hwwR
  exact (hz.unique (w * w) hwwK hwwsq).resolve_left hw2

end Ctx

end Thompson

end CFSG.ClassicalInvolution.Asc77
