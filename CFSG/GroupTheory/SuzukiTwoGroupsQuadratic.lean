module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_10

public section

namespace CFSG.GroupTheory.SuzukiTwoGroup

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_sq_of_commute {x y : G} (h : Commute x ⁅y, x⁆) :
    (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
  have hyx : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]
    group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [hyx]
    _ = (x * ⁅y, x⁆) * (x * y * y) := by group
    _ = (⁅y, x⁆ * x) * (x * y * y) := by rw [h.eq]
    _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group

theorem commutatorElement_mul_right_of_commute {x y y' : G} (h : Commute (x * y * x⁻¹) ⁅x, y'⁆) :
    ⁅x, y * y'⁆ = ⁅x, y'⁆ * ⁅x, y⁆ := by
  calc ⁅x, y * y'⁆ = (x * y * x⁻¹) * ⁅x, y'⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅x, y'⁆ * (x * y * x⁻¹) * y⁻¹ := by rw [h.eq]
    _ = ⁅x, y'⁆ * ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_left_of_commute {x x' y : G} (h : Commute x ⁅x', y⁆) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * (y * x⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅x', y⁆ * x * (y * x⁻¹ * y⁻¹) := by rw [h.eq]
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem card_quotient_le_sq_of_sq_eq_one_imp_mem [Finite G] (E : Subgroup G)
    (hEc : E ≤ center G) (hEsq : ∀ e ∈ E, e ^ 2 = 1) (hsq : ∀ x : G, x ^ 2 ∈ E)
    (haniso : ∀ x : G, x ^ 2 = 1 → x ∈ E) [E.Normal] :
    Nat.card (G ⧸ E) ≤ Nat.card E ^ 2 := by
  classical
  have hV2 : ∀ v : G ⧸ E, v ^ 2 = 1 := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq x
  have hVc : ∀ a b : G ⧸ E, a * b = b * a := fun a b =>
    Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (hV2 g)) a b
  have hcommE : ∀ x y : G, ⁅x, y⁆ ∈ E := by
    intro x y
    have h1 : ((⁅x, y⁆ : G) : G ⧸ E) = 1 := by
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hVc (x : G ⧸ E) (y : G ⧸ E)]
      group
    rwa [QuotientGroup.eq_one_iff] at h1
  have hcommZ : ∀ x y : G, ⁅x, y⁆ ∈ center G := fun x y => hEc (hcommE x y)
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hEc b.2) a)
  have hEinv : ∀ e ∈ E, e⁻¹ = e := fun e he =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hEsq e he])
  let _ : CommGroup (G ⧸ E) := { (inferInstance : Group (G ⧸ E)) with mul_comm := hVc }
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hEcomm }
  let _ : Module (ZMod 2) (Additive (G ⧸ E)) := AddCommGroup.zmodModule fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hV2, ofMul_one]
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow]
    rw [show (Additive.toMul v) ^ 2 = 1 from Subtype.ext (hEsq _ (Additive.toMul v).2), ofMul_one]
  let sqE : G → E := fun x => ⟨x ^ 2, hsq x⟩
  have hsqE : ∀ a b : G, a⁻¹ * b ∈ E → sqE a = sqE b := by
    intro a b hab
    apply Subtype.ext
    change a ^ 2 = b ^ 2
    have hb : b = a * (a⁻¹ * b) := by group
    have hc : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.1 (hEc hab) a
    rw [hb, hc.mul_pow, hEsq _ hab, mul_one]
  let qV : G ⧸ E → E := fun v =>
    Quotient.liftOn' v sqE fun a b h => hsqE a b (QuotientGroup.leftRel_apply.1 h)
  have hqV : ∀ x : G, qV (x : G ⧸ E) = sqE x := fun x => rfl
  have hcomm_eq : ∀ a c b d : G, a⁻¹ * b ∈ E → c⁻¹ * d ∈ E → ⁅a, c⁆ = ⁅b, d⁆ := by
    intro a c b d hab hcd
    have hb : b = a * (a⁻¹ * b) := by group
    have hd : d = c * (c⁻¹ * d) := by group
    have h1 : ∀ e ∈ E, ∀ g : G, ⁅e, g⁆ = 1 := fun e he g =>
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (hEc he) g).symm
    have h2 : ∀ e ∈ E, ∀ g : G, ⁅g, e⁆ = 1 := fun e he g =>
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (hEc he) g)
    rw [hb, hd, commutatorElement_mul_left_of_commute (Subgroup.mem_center_iff.1 (hcommZ _ _) _),
      h1 _ hab, one_mul,
      commutatorElement_mul_right_of_commute (Subgroup.mem_center_iff.1 (hcommZ _ _) _),
      h2 _ hcd, one_mul]
  let bV : G ⧸ E → G ⧸ E → E := fun u v =>
    Quotient.liftOn₂' u v (fun x y => (⟨⁅x, y⁆, hcommE x y⟩ : E)) fun a c b d hab hcd =>
      Subtype.ext (hcomm_eq a c b d (QuotientGroup.leftRel_apply.1 hab)
        (QuotientGroup.leftRel_apply.1 hcd))
  have hbV : ∀ x y : G, bV (x : G ⧸ E) (y : G ⧸ E) = ⟨⁅x, y⁆, hcommE x y⟩ := fun x y => rfl
  have hsurj : ∀ m : Additive (G ⧸ E), ∃ x : G, m = Additive.ofMul (x : G ⧸ E) := by
    intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
    exact ⟨x, by rw [hx, ofMul_toMul]⟩
  have hbV_left : ∀ x x' y : G,
      bV ((x * x' : G) : G ⧸ E) (y : G ⧸ E) = bV (x : G ⧸ E) y * bV (x' : G ⧸ E) y := by
    intro x x' y
    rw [hbV, hbV, hbV]
    apply Subtype.ext
    change ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆
    rw [commutatorElement_mul_left_of_commute (Subgroup.mem_center_iff.1 (hcommZ _ _) _)]
    exact (Subgroup.mem_center_iff.1 (hcommZ x y) _)
  have hbV_right : ∀ x y y' : G,
      bV (x : G ⧸ E) ((y * y' : G) : G ⧸ E) = bV (x : G ⧸ E) y * bV (x : G ⧸ E) y' := by
    intro x y y'
    rw [hbV, hbV, hbV]
    apply Subtype.ext
    change ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
    rw [commutatorElement_mul_right_of_commute (Subgroup.mem_center_iff.1 (hcommZ _ _) _)]
    exact (Subgroup.mem_center_iff.1 (hcommZ x y) _)
  let f : Additive (G ⧸ E) → Additive (G ⧸ E) → Additive E := fun u v =>
    Additive.ofMul (bV (Additive.toMul u) (Additive.toMul v))
  have hf1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n := by
    intro m₁ m₂ n
    obtain ⟨x₁, rfl⟩ := hsurj m₁
    obtain ⟨x₂, rfl⟩ := hsurj m₂
    obtain ⟨y, rfl⟩ := hsurj n
    change Additive.ofMul (bV ((x₁ * x₂ : G) : G ⧸ E) (y : G ⧸ E)) = _
    rw [hbV_left]
    rfl
  have hf3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂ := by
    intro m n₁ n₂
    obtain ⟨x, rfl⟩ := hsurj m
    obtain ⟨y₁, rfl⟩ := hsurj n₁
    obtain ⟨y₂, rfl⟩ := hsurj n₂
    change Additive.ofMul (bV (x : G ⧸ E) ((y₁ * y₂ : G) : G ⧸ E)) = _
    rw [hbV_right]
    rfl
  have hf0l : ∀ n, f 0 n = 0 := fun n => by
    have h := hf1 0 0 n
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hf0r : ∀ m, f m 0 = 0 := fun m => by
    have h := hf3 m 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hsl : ∀ (c : ZMod 2) m n, f (c • m) n = c • f m n := by
    intro c m n
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    generalize c.val = k
    induction k with
    | zero => rw [zero_nsmul, zero_nsmul, hf0l]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hf1, ih]
  have hsr : ∀ (c : ZMod 2) m n, f m (c • n) = c • f m n := by
    intro c m n
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    generalize c.val = k
    induction k with
    | zero => rw [zero_nsmul, zero_nsmul, hf0r]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hf3, ih]
  let B : Additive (G ⧸ E) →ₗ[ZMod 2] Additive (G ⧸ E) →ₗ[ZMod 2] Additive E :=
    LinearMap.mk₂ (ZMod 2) f hf1 hsl hf3 hsr
  let q : Additive (G ⧸ E) → Additive E := fun u => Additive.ofMul (qV (Additive.toMul u))
  have hq0 : q 0 = 0 := by
    change Additive.ofMul (qV ((1 : G) : G ⧸ E)) = 0
    rw [hqV]
    change Additive.ofMul (⟨(1 : G) ^ 2, hsq 1⟩ : E) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (one_pow 2)
  have hqadd : ∀ x y, q (x + y) = q x + q y + B x y := by
    intro u v
    obtain ⟨x, rfl⟩ := hsurj u
    obtain ⟨y, rfl⟩ := hsurj v
    change Additive.ofMul (qV ((x * y : G) : G ⧸ E)) =
      Additive.ofMul (qV (x : G ⧸ E) * qV (y : G ⧸ E) * bV (x : G ⧸ E) (y : G ⧸ E))
    congr 1
    rw [hqV, hqV, hqV, hbV]
    apply Subtype.ext
    change (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x, y⁆
    rw [mul_sq_of_commute (Subgroup.mem_center_iff.1 (hcommZ y x) x), ← commutatorElement_inv,
      hEinv _ (hcommE x y), mul_assoc]
    exact (Subgroup.mem_center_iff.1 (hcommZ x y) _).symm
  have hBself : ∀ x, B x x = 0 := by
    intro u
    obtain ⟨x, rfl⟩ := hsurj u
    change Additive.ofMul (bV (x : G ⧸ E) (x : G ⧸ E)) = Additive.ofMul 1
    rw [hbV]
    congr 1
    exact Subtype.ext (commutatorElement_self x)
  have hnz : ∀ x : Additive (G ⧸ E), q x = 0 → x = 0 := by
    intro u hu
    obtain ⟨x, rfl⟩ := hsurj u
    change Additive.ofMul (qV (x : G ⧸ E)) = Additive.ofMul 1 at hu
    rw [hqV] at hu
    have hx : x ^ 2 = 1 := congrArg Subtype.val (Additive.ofMul.injective hu)
    change Additive.ofMul (x : G ⧸ E) = Additive.ofMul 1
    rw [(QuotientGroup.eq_one_iff x).2 (haniso x hx)]
  let _ : Fintype (Additive (G ⧸ E)) := Fintype.ofFinite _
  let _ : Fintype (Additive E) := Fintype.ofFinite _
  have hcV : Nat.card (G ⧸ E) = 2 ^ Module.finrank (ZMod 2) (Additive (G ⧸ E)) := by
    rw [Nat.card_congr (Additive.ofMul : G ⧸ E ≃ Additive (G ⧸ E)), Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hcE : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    rw [Nat.card_congr (Additive.ofMul : E ≃ Additive E), Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  by_contra hlt
  push Not at hlt
  rw [hcV, hcE, ← pow_mul] at hlt
  have hdim : 2 * Module.finrank (ZMod 2) (Additive E) <
      Module.finrank (ZMod 2) (Additive (G ⧸ E)) := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
    omega
  obtain ⟨x, hx, hqx⟩ := BenderSuzuki.External.Higman.lemma10_exists_nonzero_quadratic_zero
    (Additive (G ⧸ E)) (Additive E) q B hq0 hqadd hBself hdim
  exact hx (hnz x hqx)

end CFSG.GroupTheory.SuzukiTwoGroup
