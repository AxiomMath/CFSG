module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRankEngine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareGeneric
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbeddingD2.HeisEngine

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.RealThreeRank
open scoped commutatorElement

section Lift

variable {X Y : Type*} [Group X] [Group Y]

theorem exists_lift_pow_eq_one {p : ℕ} (hp : Odd p) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {a g : Y} (ha : a ^ p = 1) (hg : g * a * g⁻¹ = a⁻¹) :
    ∃ x : X, ρ x = a ∧ x ^ p = 1 := by
  obtain ⟨k, rfl⟩ := hp
  obtain ⟨x₀, rfl⟩ := hρ a
  obtain ⟨w, rfl⟩ := hρ g
  have hzk : x₀ ^ (2 * k + 1) ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow]; exact ha
  have htk : x₀ * (w * x₀ * w⁻¹) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hg]
    exact mul_inv_cancel _
  have hzc := Subgroup.mem_center_iff.1 (hker hzk)
  have htc := Subgroup.mem_center_iff.1 (hker htk)
  have hconj : w * x₀ * w⁻¹ = x₀⁻¹ * (x₀ * (w * x₀ * w⁻¹)) := (inv_mul_cancel_left _ _).symm
  have hzz : x₀ ^ (2 * k + 1) * x₀ ^ (2 * k + 1) = (x₀ * (w * x₀ * w⁻¹)) ^ (2 * k + 1) := by
    have h1 : w * x₀ ^ (2 * k + 1) * w⁻¹ = x₀ ^ (2 * k + 1) := by
      rw [hzc w, mul_inv_cancel_right]
    have h2 : (w * x₀ * w⁻¹) ^ (2 * k + 1) =
        x₀⁻¹ ^ (2 * k + 1) * (x₀ * (w * x₀ * w⁻¹)) ^ (2 * k + 1) := by
      conv_lhs => rw [hconj]
      exact Commute.mul_pow (htc x₀⁻¹) _
    rw [conj_pow, h1, inv_pow] at h2
    exact eq_inv_mul_iff_mul_eq.1 h2
  have hvk : ((x₀ * (w * x₀ * w⁻¹)) ^ k)⁻¹ * x₀ ^ (2 * k + 1) ∈ ρ.ker :=
    mul_mem (inv_mem (pow_mem htk k)) hzk
  have hvp : (((x₀ * (w * x₀ * w⁻¹)) ^ k)⁻¹ * x₀ ^ (2 * k + 1)) ^ (2 * k + 1) =
      x₀ ^ (2 * k + 1) := by
    rw [Commute.mul_pow (hzc _), inv_pow, ← pow_mul, mul_comm k, pow_mul, ← hzz, ← pow_add,
      ← pow_mul, ← pow_mul, show (2 * k + 1) * (2 * k + 1) =
        (2 * k + 1 + (2 * k + 1)) * k + (2 * k + 1) by ring, pow_add, inv_mul_cancel_left]
  have hvc := Subgroup.mem_center_iff.1 (hker hvk)
  refine ⟨x₀ * (((x₀ * (w * x₀ * w⁻¹)) ^ k)⁻¹ * x₀ ^ (2 * k + 1))⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hvk, inv_one, mul_one]
  · rw [Commute.mul_pow (Subgroup.mem_center_iff.1 (hker (inv_mem hvk)) x₀), inv_pow, hvp,
      mul_inv_cancel]

omit [Group Y] in
theorem eq_one_of_conj_eq_inv_of_conj_eq {p : ℕ} (hp : Odd p) {g w : X} (hg : g ^ p = 1)
    (hw : w * g * w⁻¹ = g⁻¹) (hw' : w * g * w⁻¹ = g) : g = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : g ^ 2 = 1 := by
    have := hw'.symm.trans hw
    rw [sq]
    calc g * g = g * g⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel g
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hg
  exact hg

theorem exists_lift_mem {p : ℕ} (hp : Odd p) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X} (hkP : ρ.ker ≤ P) {g w : Y}
    (hgP : g ∈ P.map ρ) (hg : g ^ p = 1) (hw : w * g * w⁻¹ = g⁻¹) :
    ∃ x ∈ P, ρ x = g ∧ x ^ p = 1 := by
  obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp ρ hρ hker hg hw
  obtain ⟨y, hy, hyg⟩ := hgP
  refine ⟨x, ?_, hx, hxp⟩
  have hk : y⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyg, hx, inv_mul_cancel]
  simpa using mul_mem hy (hkP hk)

variable [Finite X]

theorem three_le_pRank_of_real_triple {p : ℕ} [Fact p.Prime] (hp : Odd p) (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X}
    (hkP : ρ.ker ≤ P) {A₁ A₂ A₃ : Subgroup Y} (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b)
    (h13 : ∀ a ∈ A₁, ∀ b ∈ A₃, Commute a b) (h23 : ∀ a ∈ A₂, ∀ b ∈ A₃, Commute a b)
    {g₁ g₂ g₃ w₁ w₂ w₃ : Y} (hg₁ : g₁ ∈ ⁅A₁, A₁⁆) (hg₂ : g₂ ∈ ⁅A₂, A₂⁆) (hg₃ : g₃ ∈ ⁅A₃, A₃⁆)
    (hP₁ : g₁ ∈ P.map ρ) (hP₂ : g₂ ∈ P.map ρ) (hP₃ : g₃ ∈ P.map ρ)
    (h3₁ : g₁ ^ p = 1) (h3₂ : g₂ ^ p = 1) (h3₃ : g₃ ^ p = 1)
    (h1₁ : g₁ ≠ 1) (h1₂ : g₂ ≠ 1) (h1₃ : g₃ ≠ 1)
    (hw₂ : w₂ ∈ A₂) (hw₃ : w₃ ∈ A₃) (hi₁ : w₁ * g₁ * w₁⁻¹ = g₁⁻¹) (hi₂ : w₂ * g₂ * w₂⁻¹ = g₂⁻¹)
    (hi₃ : w₃ * g₃ * w₃⁻¹ = g₃⁻¹) : 3 ≤ CFSG.Open.pRank p P := by
  have hA₁ : ⁅A₁, A₁⁆ ≤ A₁ := Subgroup.commutator_le_self A₁
  have hA₂ : ⁅A₂, A₂⁆ ≤ A₂ := Subgroup.commutator_le_self A₂
  have hA₃ : ⁅A₃, A₃⁆ ≤ A₃ := Subgroup.commutator_le_self A₃
  obtain ⟨x₁, hx₁P, hx₁, hx₁3⟩ := exists_lift_mem hp ρ hρ hker hkP hP₁ h3₁ hi₁
  obtain ⟨x₂, hx₂P, hx₂, hx₂3⟩ := exists_lift_mem hp ρ hρ hker hkP hP₂ h3₂ hi₂
  obtain ⟨x₃, hx₃P, hx₃, hx₃3⟩ := exists_lift_mem hp ρ hρ hker hkP hP₃ h3₃ hi₃
  have c12 : Commute x₁ x₂ := commute_lift_of_commutes ρ hρ hker h12 hg₁ hx₁ (hx₂ ▸ hA₂ hg₂)
  have c13 : Commute x₁ x₃ := commute_lift_of_commutes ρ hρ hker h13 hg₁ hx₁ (hx₃ ▸ hA₃ hg₃)
  have c23 : Commute x₂ x₃ := commute_lift_of_commutes ρ hρ hker h23 hg₂ hx₂ (hx₃ ▸ hA₃ hg₃)
  set y₁ : ↥P := ⟨x₁, hx₁P⟩
  set y₂ : ↥P := ⟨x₂, hx₂P⟩
  set y₃ : ↥P := ⟨x₃, hx₃P⟩
  have hρ₁ : ∀ n : ℕ, ρ ((y₁ : X) ^ n) = g₁ ^ n := fun n => by rw [map_pow, hx₁]
  have hρ₂ : ∀ n : ℕ, ρ ((y₂ : X) ^ n) = g₂ ^ n := fun n => by rw [map_pow, hx₂]
  refine (three_le_pRank_of_gens (G := ↥P) (p := p) (x := y₁) (y := y₂) (z := y₃)
    (Subtype.ext hx₁3) (Subtype.ext hx₂3) (Subtype.ext hx₃3)
    (Subtype.ext c12.eq) (Subtype.ext c13.eq) (Subtype.ext c23.eq) ?_ ?_ ?_).trans
    (pRank_top_subtype_le p (Fact.out : p.Prime).one_lt P)
  · intro h
    apply h1₁
    rw [← hx₁]
    exact congrArg (fun y : ↥P => ρ (y : X)) h |>.trans (map_one ρ)
  · intro n h
    apply h1₂
    have he : g₁ ^ n = g₂ := by
      rw [← hρ₁, ← hx₂]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h)
    refine eq_one_of_conj_eq_inv_of_conj_eq hp h3₂ hi₂ ?_
    rw [← he]
    exact conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n
  · intro n m h
    apply h1₃
    have he : g₁ ^ n * g₂ ^ m = g₃ := by
      rw [← hρ₁, ← hρ₂, ← map_mul, ← hx₃]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h)
    refine eq_one_of_conj_eq_inv_of_conj_eq hp h3₃ hi₃ ?_
    rw [← he]
    have e1 := conj_pow_eq_of_commute (h13 _ (hA₁ hg₁) _ hw₃).symm n
    have e2 := conj_pow_eq_of_commute (h23 _ (hA₂ hg₂) _ hw₃).symm m
    calc w₃ * (g₁ ^ n * g₂ ^ m) * w₃⁻¹ = (w₃ * g₁ ^ n * w₃⁻¹) * (w₃ * g₂ ^ m * w₃⁻¹) := by
          group
      _ = g₁ ^ n * g₂ ^ m := by rw [e1, e2]

theorem three_le_pRank_of_real_pair {p : ℕ} [Fact p.Prime] (hp : Odd p) (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X}
    (hkP : ρ.ker ≤ P) (h3 : p ∣ Nat.card ρ.ker) {A₁ A₂ : Subgroup Y}
    (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b) {g₁ g₂ w₂ : Y} (hg₁ : g₁ ∈ ⁅A₁, A₁⁆)
    (hg₂ : g₂ ∈ ⁅A₂, A₂⁆) (hP₁ : g₁ ∈ P.map ρ) (hP₂ : g₂ ∈ P.map ρ) (h3₁ : g₁ ^ p = 1)
    (h3₂ : g₂ ^ p = 1) (h1₁ : g₁ ≠ 1) (h1₂ : g₂ ≠ 1) {w₁ : Y} (hi₁ : w₁ * g₁ * w₁⁻¹ = g₁⁻¹)
    (hw₂ : w₂ ∈ A₂) (hi₂ : w₂ * g₂ * w₂⁻¹ = g₂⁻¹) : 3 ≤ CFSG.Open.pRank p P := by
  have hA₁ : ⁅A₁, A₁⁆ ≤ A₁ := Subgroup.commutator_le_self A₁
  have hA₂ : ⁅A₂, A₂⁆ ≤ A₂ := Subgroup.commutator_le_self A₂
  obtain ⟨x₁, hx₁P, hx₁, hx₁3⟩ := exists_lift_mem hp ρ hρ hker hkP hP₁ h3₁ hi₁
  obtain ⟨x₂, hx₂P, hx₂, hx₂3⟩ := exists_lift_mem hp ρ hρ hker hkP hP₂ h3₂ hi₂
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p h3
  have hzk : (z : X) ∈ ρ.ker := z.2
  have hzc : (z : X) ∈ Subgroup.center X := hker hzk
  have hz3 : (z : X) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : X) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact (Fact.out : p.Prime).one_lt.ne' hz.symm
  have c12 : Commute x₁ x₂ := commute_lift_of_commutes ρ hρ hker h12 hg₁ hx₁ (hx₂ ▸ hA₂ hg₂)
  have c1z : Commute x₁ z := (Subgroup.mem_center_iff.mp hzc x₁)
  have c2z : Commute x₂ z := (Subgroup.mem_center_iff.mp hzc x₂)
  set y₁ : ↥P := ⟨x₁, hx₁P⟩
  set y₂ : ↥P := ⟨x₂, hx₂P⟩
  set y₃ : ↥P := ⟨z, hkP hzk⟩
  have hρ₁ : ∀ n : ℕ, ρ ((y₁ : X) ^ n) = g₁ ^ n := fun n => by rw [map_pow, hx₁]
  have hρ₂ : ∀ n : ℕ, ρ ((y₂ : X) ^ n) = g₂ ^ n := fun n => by rw [map_pow, hx₂]
  have hind : ∀ n : ℕ, g₁ ^ n ≠ g₂ := fun n he => h1₂ (by
    refine eq_one_of_conj_eq_inv_of_conj_eq hp h3₂ hi₂ ?_
    rw [← he]
    exact conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n)
  refine (three_le_pRank_of_gens (G := ↥P) (p := p) (x := y₁) (y := y₂) (z := y₃)
    (Subtype.ext hx₁3) (Subtype.ext hx₂3) (Subtype.ext hz3)
    (Subtype.ext c12.eq) (Subtype.ext c1z) (Subtype.ext c2z) ?_ ?_ ?_).trans
    (pRank_top_subtype_le p (Fact.out : p.Prime).one_lt P)
  · intro h
    apply h1₁
    rw [← hx₁]
    exact congrArg (fun y : ↥P => ρ (y : X)) h |>.trans (map_one ρ)
  · intro n h
    exact hind n (by
      rw [← hρ₁, ← hx₂]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h))
  · intro n m h
    have hzv := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at hzv
    have he : g₁ ^ n * g₂ ^ m = 1 := by
      rw [← hρ₁, ← hρ₂, ← map_mul]
      change ρ ((y₁ : X) ^ n * (y₂ : X) ^ m) = 1
      rw [hzv]
      exact hzk
    have he' : g₁ ^ n * (g₂ ^ m)⁻¹ = 1 := by
      have e1 := conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n
      have e2 : w₂ * g₂ ^ m * w₂⁻¹ = (g₂ ^ m)⁻¹ := by
        rw [← inv_pow, ← hi₂, conj_pow]
      calc g₁ ^ n * (g₂ ^ m)⁻¹ = (w₂ * g₁ ^ n * w₂⁻¹) * (w₂ * g₂ ^ m * w₂⁻¹) := by rw [e1, e2]
        _ = w₂ * (g₁ ^ n * g₂ ^ m) * w₂⁻¹ := by group
        _ = 1 := by rw [he, mul_one, mul_inv_cancel]
    have hm2 : g₂ ^ m = (g₂ ^ m)⁻¹ :=
      (eq_inv_of_mul_eq_one_right he).trans (eq_inv_of_mul_eq_one_right he').symm
    have hgm : g₂ ^ m = 1 := by
      refine eq_one_of_conj_eq_inv_of_conj_eq (w := 1) hp ?_ (by rw [one_mul, inv_one, mul_one,
        ← hm2]) (by group)
      rw [← pow_mul, mul_comm, pow_mul, h3₂, one_pow]
    have hgn : g₁ ^ n = 1 := by rwa [hgm, mul_one] at he
    have ho₁ : orderOf g₁ = p := orderOf_eq_prime h3₁ h1₁
    have ho₂ : orderOf g₂ = p := orderOf_eq_prime h3₂ h1₂
    obtain ⟨a, rfl⟩ := ho₁ ▸ orderOf_dvd_of_pow_eq_one hgn
    obtain ⟨c, rfl⟩ := ho₂ ▸ orderOf_dvd_of_pow_eq_one hgm
    apply hz1
    rw [← hzv, pow_mul, pow_mul]
    change (x₁ ^ p) ^ a * (x₂ ^ p) ^ c = 1
    rw [hx₁3, hx₂3, one_pow, one_pow, one_mul]

end Lift

section Over

variable {K Y : Type*} [Group K] [Group Y]

@[expose] def RealOver (p : ℕ) (π : K →* Y) (Λ : Subgroup K) (J : Subgroup Y) : Prop :=
  ∃ g ∈ ⁅Λ, Λ⁆, π g ∈ J ∧ g ^ p = 1 ∧ g ∉ Subgroup.center K ∧ ∃ w ∈ Λ, w * g * w⁻¹ = g⁻¹

theorem mul_eq_commutatorElement_pow {x y : K} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) {k : ℕ}
    (h : (x * y) ^ (2 * k + 1) = 1) : x * y = ⁅x, y⁆ ^ (k + 1) := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx])
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy])
  have hc : ⁅x, y⁆ = (x * y) ^ 2 := by
    rw [commutatorElement_def, hx', hy', sq]
    group
  rw [hc, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h, one_mul]

theorem RealOver.of_involutions {p : ℕ} (hp : Odd p) {π : K →* Y} {Λ : Subgroup K}
    {J : Subgroup Y} {x y : K} (hx : x ∈ Λ) (hy : y ∈ Λ) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (h : (x * y) ^ p = 1) (hc : x * y ∉ Subgroup.center K) (hJ : π (x * y) ∈ J) :
    RealOver p π Λ J := by
  obtain ⟨k, rfl⟩ := hp
  refine ⟨x * y, ?_, hJ, h, hc, x, hx, ParabRealThree.conj_mul_eq_inv_of_sq hx2 hy2⟩
  rw [mul_eq_commutatorElement_pow hx2 hy2 h]
  exact pow_mem (Subgroup.commutator_mem_commutator hx hy) _

omit [Group Y] in
theorem not_mem_center_of_conj_eq_inv {p : ℕ} (hp : Odd p) {g w : K} (hg : g ^ p = 1)
    (hw : w * g * w⁻¹ = g⁻¹) (h1 : g ≠ 1) : g ∉ Subgroup.center K := fun hz =>
  h1 (eq_one_of_conj_eq_inv_of_conj_eq hp hg hw
    (by rw [Subgroup.mem_center_iff.1 hz w, mul_inv_cancel_right]))

theorem RealOver.of_involutions' {p : ℕ} (hp : Odd p) {π : K →* Y} {Λ : Subgroup K}
    {J : Subgroup Y} {x y : K} (hx : x ∈ Λ) (hy : y ∈ Λ) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (h : (x * y) ^ p = 1) (h1 : x * y ≠ 1) (hJ : π (x * y) ∈ J) : RealOver p π Λ J :=
  RealOver.of_involutions hp hx hy hx2 hy2 h
    (not_mem_center_of_conj_eq_inv hp h (ParabRealThree.conj_mul_eq_inv_of_sq hx2 hy2) h1) hJ

theorem RealOver.mono {p : ℕ} {π : K →* Y} {Λ Λ' : Subgroup K} {J : Subgroup Y}
    (h : RealOver p π Λ J) (hle : Λ ≤ Λ') : RealOver p π Λ' J := by
  obtain ⟨g, hg, hgJ, hg3, hgc, w, hw, hwg⟩ := h
  exact ⟨g, Subgroup.commutator_mono hle hle hg, hgJ, hg3, hgc, w, hle hw, hwg⟩

theorem RealOver.conj {p : ℕ} {π : K →* Y} {Λ : Subgroup K} {J : Subgroup Y}
    (h : RealOver p π Λ J) {k : K} (hk : π k ∈ J) :
    RealOver p π (Λ.map (MulAut.conj k).toMonoidHom) J := by
  obtain ⟨g, hg, hgJ, hg3, hgc, w, hw, hwg⟩ := h
  refine ⟨k * g * k⁻¹, ?_, ?_, ?_, fun hz => hgc ?_, k * w * k⁻¹, ⟨w, hw, rfl⟩, ?_⟩
  · rw [← Subgroup.map_commutator]
    exact ⟨g, hg, rfl⟩
  · rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hk hgJ) (inv_mem hk)
  · rw [conj_pow, hg3, mul_one, mul_inv_cancel]
  · rw [Subgroup.mem_center_iff] at hz ⊢
    intro a
    have := hz (k * a * k⁻¹)
    have e : k * g * k⁻¹ * (k * a * k⁻¹) = k * (g * a) * k⁻¹ := by group
    have e' : k * a * k⁻¹ * (k * g * k⁻¹) = k * (a * g) * k⁻¹ := by group
    rw [e, e'] at this
    exact mul_left_cancel (mul_right_cancel this)
  · calc k * w * k⁻¹ * (k * g * k⁻¹) * (k * w * k⁻¹)⁻¹ = k * (w * g * w⁻¹) * k⁻¹ := by group
      _ = (k * g * k⁻¹)⁻¹ := by rw [hwg]; group

variable {X : Type*} [Group X] [Finite X] {π : K →* Y} {J : Subgroup Y}

omit [Finite X] in
theorem RealOver.image {p : ℕ} (hπker : π.ker ≤ Subgroup.center K) {Λ : Subgroup K}
    (h : RealOver p π Λ J) (ρ : X →* Y) (hρ : Function.Surjective ρ) :
    ∃ g ∈ ⁅Λ.map π, Λ.map π⁆, g ∈ (J.comap ρ).map ρ ∧ g ^ p = 1 ∧ g ≠ 1 ∧
      ∃ w ∈ Λ.map π, w * g * w⁻¹ = g⁻¹ := by
  obtain ⟨g, hg, hgJ, hg3, hgc, w, hw, hwg⟩ := h
  refine ⟨π g, ?_, ?_, by rw [← map_pow, hg3, map_one], fun h1 => hgc (hπker h1), π w,
    ⟨w, hw, rfl⟩, by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hwg]⟩
  · rw [← Subgroup.map_commutator]
    exact ⟨g, hg, rfl⟩
  · rw [Subgroup.map_comap_eq_self_of_surjective hρ]
    exact hgJ

theorem three_le_pRank_of_triple {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hπker : π.ker ≤ Subgroup.center K) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {Λ₁ Λ₂ Λ₃ : Subgroup K} (c12 : Commutes Λ₁ Λ₂)
    (c13 : Commutes Λ₁ Λ₃) (c23 : Commutes Λ₂ Λ₃) (h₁ : RealOver p π Λ₁ J)
    (h₂ : RealOver p π Λ₂ J) (h₃ : RealOver p π Λ₃ J) :
    3 ≤ CFSG.Open.pRank p (J.comap ρ) := by
  obtain ⟨g₁, hg₁, hP₁, h3₁, h1₁, w₁, -, hi₁⟩ := h₁.image hπker ρ hρ
  obtain ⟨g₂, hg₂, hP₂, h3₂, h1₂, w₂, hw₂, hi₂⟩ := h₂.image hπker ρ hρ
  obtain ⟨g₃, hg₃, hP₃, h3₃, h1₃, w₃, hw₃, hi₃⟩ := h₃.image hπker ρ hρ
  have hkP : ρ.ker ≤ J.comap ρ := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact one_mem J
  exact three_le_pRank_of_real_triple hp ρ hρ hρker hkP
    (ParabRankEngine.commute_map_of_commutes c12) (ParabRankEngine.commute_map_of_commutes c13)
    (ParabRankEngine.commute_map_of_commutes c23) hg₁ hg₂ hg₃ hP₁ hP₂ hP₃ h3₁ h3₂ h3₃ h1₁ h1₂
    h1₃ hw₂ hw₃ hi₁ hi₂ hi₃

theorem three_le_pRank_of_pair {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hπker : π.ker ≤ Subgroup.center K) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) (h3 : p ∣ Nat.card ρ.ker) {Λ₁ Λ₂ : Subgroup K}
    (c12 : Commutes Λ₁ Λ₂) (h₁ : RealOver p π Λ₁ J) (h₂ : RealOver p π Λ₂ J) :
    3 ≤ CFSG.Open.pRank p (J.comap ρ) := by
  obtain ⟨g₁, hg₁, hP₁, h3₁, h1₁, w₁, -, hi₁⟩ := h₁.image hπker ρ hρ
  obtain ⟨g₂, hg₂, hP₂, h3₂, h1₂, w₂, hw₂, hi₂⟩ := h₂.image hπker ρ hρ
  have hkP : ρ.ker ≤ J.comap ρ := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact one_mem J
  exact three_le_pRank_of_real_pair hp ρ hρ hρker hkP h3
    (ParabRankEngine.commute_map_of_commutes c12) hg₁ hg₂ hP₁ hP₂ h3₁ h3₂ h1₁ h1₂ hi₁ hw₂ hi₂

end Over

section Coprime

variable {X Y : Type*} [Group X] [Group Y] {ρ : X →* Y}

omit [Group Y] in
theorem eq_one_of_mem_of_coprime {p : ℕ} {V : Subgroup X} (hV : Nat.Coprime p (Nat.card V))
    {x : X} (hx : x ∈ V) {e : ℕ} (he : x ^ p ^ e = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left e hV)
    (orderOf_dvd_of_pow_eq_one he) (Subgroup.orderOf_dvd_natCard V hx))

omit [Group Y] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup X} (h : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup h

theorem exists_isPGroup_map_eq [Finite X] {p : ℕ} [Fact p.Prime] (hρ : Function.Surjective ρ)
    {U₁ : Subgroup Y} (hU₁ : IsPGroup p U₁) :
    ∃ U : Subgroup X, U ≤ U₁.comap ρ ∧ IsPGroup p U ∧ U.map ρ = U₁ := by
  set C := U₁.comap ρ
  let ρ' : C →* U₁ := (ρ.comp C.subtype).codRestrict U₁ fun x => x.2
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite U₁ := Finite.of_surjective ρ' hρ'
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  have hPtop : ((P : Subgroup C).map ρ') = ⊤ := by
    rw [← Sylow.coe_mapSurjective hρ']
    obtain ⟨n, hn⟩ := hU₁.index ((P.mapSurjective hρ' : Sylow p U₁) : Subgroup U₁)
    have hnd := (P.mapSurjective hρ').not_dvd_index
    rcases n with _ | n
    · exact Subgroup.index_eq_one.1 (by simpa using hn)
    · exact absurd (hn ▸ dvd_pow_self p (Nat.succ_ne_zero n)) hnd
  refine ⟨(P : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have e : ((P : Subgroup C).map C.subtype).map ρ = ((P : Subgroup C).map ρ').map U₁.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e, hPtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem pRank_le_pRank_comap_of_coprime [Finite X] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (hρ : Function.Surjective ρ) (hker : Nat.Coprime p (Nat.card ρ.ker)) (J : Subgroup Y) :
    CFSG.Open.pRank p J ≤ CFSG.Open.pRank p (J.comap ρ) := by
  obtain ⟨E, hEJ, hE, hcard⟩ := exists_pRank hp.out.one_lt J
  obtain ⟨U, hUE, hU, hUm⟩ := exists_isPGroup_map_eq hρ (isPGroup_of_isElemAbelian hE)
  have hUJ : U ≤ J.comap ρ := hUE.trans (Subgroup.comap_mono hEJ)
  have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 => by
    obtain ⟨e, he⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_of_coprime hker (show x ∈ ρ.ker from h1)
      (by simpa using congrArg Subtype.val he)
  have hU1 : IsElemAbelian p (U.map ρ) := hUm ▸ hE
  have hUe : IsElemAbelian p U := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hc := hU1.1.is_comm.comm ⟨ρ a, a, a.2, rfl⟩ ⟨ρ b, b, b.2, rfl⟩
      have hc' : ρ ((a : X) * (b : X) * ((b : X) * (a : X))⁻¹) = 1 := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
      have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
      simpa using mul_inv_eq_one.1 this
    · exact hinj _ (pow_mem hx p) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)
  have hinj' : Function.Injective (ρ.comp U.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (Subtype.ext (hinj _ x.2 hx))
  have hcU : Nat.card U = p ^ CFSG.Open.pRank p J := by
    have e := Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at e
    rw [e, hUm, hcard]
  exact le_pRank hp.out.one_lt hUJ hUe hcU

end Coprime

section Torus

variable {K Y : Type*} [Group K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}

theorem three_le_pRank_of_torus {p : ℕ} [Fact p.Prime] (hext : SteinbergExtras D n H)
    (hπp : Nat.Coprime p (Nat.card π.ker)) {J : Subgroup Y} (hBJ : borel D H ≤ J.comap π)
    {a b c : Fin D.rank} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {x y z : K}
    (hxH : x ∈ H a) (hyH : y ∈ H b) (hzH : z ∈ H c) (hx3 : x ^ p = 1) (hy3 : y ^ p = 1)
    (hz3 : z ^ p = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) :
    3 ≤ CFSG.Open.pRank p J := by
  have hT : ∀ k, H k ≤ J.comap π := fun k => (le_iSup H k).trans (le_sup_left.trans hBJ)
  have cxy := hext.torus_commute a b x hxH y hyH
  have cxz := hext.torus_commute a c x hxH z hzH
  have cyz := hext.torus_commute b c y hyH z hzH
  have hk : ∀ w : K, w ^ p = 1 → π w = 1 → w = 1 := fun w hw h1 =>
    eq_one_of_mem_of_coprime hπp (show w ∈ π.ker from h1) (e := 1) (by simpa using hw)
  have hind := hext.torus_iSupIndep
  have hdisj : ∀ {k : Fin D.rank} {S : Set (Fin D.rank)}, k ∉ S →
      Disjoint (H k) (⨆ j ∈ S, H j) := fun {k S} hkS =>
    (hind k).mono_right (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le
      (fun h : j = k => hkS (h ▸ hj)) le_rfl))
  set x' : ↥J := ⟨π x, hT a hxH⟩
  set y' : ↥J := ⟨π y, hT b hyH⟩
  set z' : ↥J := ⟨π z, hT c hzH⟩
  refine (three_le_pRank_of_gens (G := ↥J) (p := p) (x := x') (y := y') (z := z')
    (Subtype.ext (by simp [x', ← map_pow, hx3])) (Subtype.ext (by simp [y', ← map_pow, hy3]))
    (Subtype.ext (by simp [z', ← map_pow, hz3])) (Subtype.ext (by simp [x', y', ← map_mul,
      cxy.eq])) (Subtype.ext (by simp [x', z', ← map_mul, cxz.eq]))
    (Subtype.ext (by simp [y', z', ← map_mul, cyz.eq])) ?_ ?_ ?_).trans
    (RealThreeRank.pRank_top_subtype_le p (Fact.out : p.Prime).one_lt J)
  · intro h1
    exact hx1 (hk x hx3 (congrArg Subtype.val h1))
  · intro e he
    have he' : π x ^ e = π y := by
      have := congrArg Subtype.val he
      simpa [x', y'] using this
    have hw : π (y * (x ^ e)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, he', mul_inv_cancel]
    have hw3 : (y * (x ^ e)⁻¹) ^ p = 1 := by
      rw [(cxy.symm.pow_right e).inv_right.mul_pow, hy3, inv_pow, ← pow_mul, mul_comm,
        pow_mul, hx3, one_pow, inv_one, one_mul]
    have hyx : y = x ^ e := mul_inv_eq_one.1 (hk _ hw3 hw)
    have hmem : y ∈ H b ⊓ ⨆ j ∈ ({a} : Set (Fin D.rank)), H j :=
      ⟨hyH, hyx ▸ (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a} : Set (Fin D.rank))) => H j) a
        rfl le_rfl) (pow_mem hxH e)⟩
    rw [(hdisj (by simpa using hab.symm)).eq_bot] at hmem
    exact hy1 hmem
  · intro e f he
    have he' : π x ^ e * π y ^ f = π z := by
      have := congrArg Subtype.val he
      simpa [x', y', z'] using this
    have hw : π (z * (x ^ e * y ^ f)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_pow, map_pow, he', mul_inv_cancel]
    have cz : Commute z (x ^ e * y ^ f) :=
      ((cxz.symm.pow_right e).mul_right (cyz.symm.pow_right f))
    have hxy3 : (x ^ e * y ^ f) ^ p = 1 := by
      rw [(cxy.pow_pow e f).mul_pow, ← pow_mul, ← pow_mul, mul_comm e, mul_comm f, pow_mul,
        pow_mul, hx3, hy3, one_pow, one_pow, one_mul]
    have hw3 : (z * (x ^ e * y ^ f)⁻¹) ^ p = 1 := by
      rw [cz.inv_right.mul_pow, hz3, inv_pow, hxy3, inv_one, one_mul]
    have hzxy : z = x ^ e * y ^ f := mul_inv_eq_one.1 (hk _ hw3 hw)
    have hmem : z ∈ H c ⊓ ⨆ j ∈ ({a, b} : Set (Fin D.rank)), H j := by
      refine ⟨hzH, hzxy ▸ mul_mem ?_ ?_⟩
      · exact (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a, b} : Set (Fin D.rank))) => H j) a
          (by simp) le_rfl) (pow_mem hxH e)
      · exact (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a, b} : Set (Fin D.rank))) => H j) b
          (by simp) le_rfl) (pow_mem hyH f)
    rw [(hdisj (by simp [hac.symm, hbc.symm])).eq_bot] at hmem
    exact hz1 hmem

end Torus

section Nonabelian

theorem not_isMulCommutative_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hB : ¬ IsMulCommutative B) : ¬ IsMulCommutative A := by
  intro hA
  refine hB ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  rw [← map_mul, ← map_mul, hA.is_comm.comm a b]

theorem exists_nonabelian_of_hasSubquotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} {U : Type*} [Group U] (hU : IsPGroup p U)
    (hUc : ¬ IsMulCommutative U) (h : LeviSection.HasSubquotient H U) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧ ¬ IsMulCommutative P := by
  obtain ⟨P, hPH, hP, f, hf⟩ := h.exists_isPGroup_surjective ⊤ (hU.to_subgroup ⊤)
  exact ⟨P, hPH, hP, not_isMulCommutative_of_surjective (Subgroup.topEquiv.toMonoidHom.comp f)
    ((MulEquiv.surjective _).comp hf) hUc⟩

theorem hasSubquotient_self {G : Type*} [Group G] (P : Subgroup G) :
    LeviSection.HasSubquotient P P :=
  ⟨P, le_rfl, MonoidHom.id P, Function.surjective_id⟩

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem hasSubquotient_torus_sup_leviM (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : borel D H ≤ J.comap π) {U : Type*} [Group U]
    (hU2 : ∀ R : Subgroup U, R.Normal → IsPGroup 2 R → R = ⊥)
    (hQ : LeviSection.HasSubquotient J U) :
    LeviSection.HasSubquotient ((⨆ k, H k) ⊔ leviM D (negIndices D (J.comap π))) U := by
  have hA : LeviSection.HasSubquotient (J.comap π) U := by
    refine LeviSection.HasSubquotient.of_map π ?_
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surj]
  have hle := leviRad_sup_leviM_le hBJ
  have hnorm : J.comap π ≤ Subgroup.normalizer
      (leviRad D (negIndices D (J.comap π)) : Set K) := by
    refine (eq_borel_sup_rankOne h.ct h.extras hBJ).le.trans (sup_le ?_ ?_)
    · exact borel_le_normalizer_leviRad h.ct h.extras
    · exact iSup₂_le fun _ hi => rankOne_le_normalizer_leviRad h.extras hi
  have hsup : J.comap π ≤ leviRad D (negIndices D (J.comap π)) ⊔
      ((⨆ k, H k) ⊔ leviM D (negIndices D (J.comap π))) := by
    refine (le_torus_sup_leviRad_sup_leviM h.ct h.extras hBJ).trans ?_
    rw [sup_left_comm]
  exact hA.of_sup_normal_pGroup (le_sup_left.trans hle)
    (sup_le (le_sup_left.trans hBJ) (le_sup_right.trans hle)) hnorm hsup
    (isPGroup_leviRad h.extras h.pGroup) hU2

theorem eq_bot_of_isPGroup_two {U : Type*} [Group U] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hU : IsPGroup p U) (R : Subgroup U) (hR : IsPGroup 2 R) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 p hp2.symm R R hR (hU.to_subgroup R))

theorem exists_nonabelian_le_torus_sup_leviM [Finite K] (h : BorelQuotient D n H π M)
    {J : Subgroup Y} (hBJ : borel D H ≤ J.comap π) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup Y} (hPJ : P ≤ J) (hP : IsPGroup p P) (hPc : ¬ IsMulCommutative P) :
    ∃ Q : Subgroup K, Q ≤ (⨆ k, H k) ⊔ leviM D (negIndices D (J.comap π)) ∧ IsPGroup p Q ∧
      ¬ IsMulCommutative Q :=
  exists_nonabelian_of_hasSubquotient hP hPc (hasSubquotient_torus_sup_leviM h hBJ
    (fun R _ hR => eq_bot_of_isPGroup_two hp2 hP R hR) ((hasSubquotient_self P).mono hPJ))

end Nonabelian

end CFSG.AGLEmbeddingD2.HeisEngine
