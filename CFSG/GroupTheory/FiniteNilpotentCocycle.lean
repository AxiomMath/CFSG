module

public import CFSG.GroupTheory.FixedPointQuotientCard
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

universe u v

section GeneralPower

variable {G : Type u} [Group G]

theorem mem_center_of_pow_mem_center {n : ℕ}
    (hpow : Function.Bijective (fun g : G => g ^ n)) {w : G}
    (hw : w ^ n ∈ Subgroup.center G) : w ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hw ⊢
  intro g
  have hgz : g * w ^ n * g⁻¹ = w ^ n := by
    rw [hw g, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : g * w * g⁻¹ = w := by
    apply hpow.1
    change (g * w * g⁻¹) ^ n = w ^ n
    rw [conj_pow, hgz]
  calc
    g * w = (g * w * g⁻¹) * g := by group
    _ = w * g := by rw [hconj]

theorem bijective_pow_quotient_center {n : ℕ}
    (hpow : Function.Bijective (fun g : G => g ^ n)) :
    Function.Bijective (fun q : G ⧸ Subgroup.center G => q ^ n) := by
  classical
  let Z : Subgroup G := Subgroup.center G
  constructor
  · intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H x =>
      induction q₂ using QuotientGroup.induction_on with
      | H y =>
        have hmk : ((x ^ n : G) : G ⧸ Z) = ((y ^ n : G) : G ⧸ Z) := by
          simpa [QuotientGroup.mk_pow] using h
        have hz : (x ^ n)⁻¹ * y ^ n ∈ Z := (QuotientGroup.eq).mp hmk
        obtain ⟨c, hc⟩ := hpow.2 ((x ^ n)⁻¹ * y ^ n)
        have hc' : c ^ n = (x ^ n)⁻¹ * y ^ n := hc
        have hcZ : c ∈ Z :=
          mem_center_of_pow_mem_center hpow (by rw [hc']; exact hz)
        have hcx : c * x = y := by
          apply hpow.1
          have hc_comm_x : Commute c x := (Subgroup.mem_center_iff.mp hcZ x).symm
          calc
            (c * x) ^ n = c ^ n * x ^ n := Commute.mul_pow hc_comm_x n
            _ = ((x ^ n)⁻¹ * y ^ n) * x ^ n := by rw [hc']
            _ = x ^ n * ((x ^ n)⁻¹ * y ^ n) :=
              (Subgroup.mem_center_iff.mp hz (x ^ n)).symm
            _ = y ^ n := by group
        change (x : G ⧸ Z) = (y : G ⧸ Z)
        rw [← hcx]
        simp [hcZ]
  · intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨x, hx⟩ := hpow.2 y
      have hx' : x ^ n = y := hx
      refine ⟨(x : G ⧸ Z), ?_⟩
      change ((x : G ⧸ Z) ^ n) = ((y : G) : G ⧸ Z)
      rw [← QuotientGroup.mk_pow, hx']

end GeneralPower

section Abelian

variable {F : Type v} [Group F] [Finite F]
variable {A : Type u} [Group A]

theorem exists_inv_mul_of_mul_comm
    (hcomm : ∀ x y : A, x * y = y * x)
    (α : F →* MulAut A)
    (hpow : Function.Bijective (fun a : A => a ^ Nat.card F))
    (c : F → A)
    (hcoc : ∀ a b, c (a * b) = c a * α a (c b)) :
    ∃ u : A, ∀ a, c a = u⁻¹ * α a u := by
  classical
  let commA : CommGroup A := CommGroup.mk hcomm
  let fintypeF : Fintype F := Fintype.ofFinite F
  let C : A := ∏ a : F, c a
  have hC_perm (b : F) : C = ∏ a : F, c (b * a) := by
    dsimp only [C]
    exact (Equiv.prod_comp (Equiv.mulLeft b) c).symm
  have hCb (b : F) : C = c b ^ Nat.card F * α b C := by
    calc
      C = ∏ a : F, c (b * a) := hC_perm b
      _ = ∏ a : F, c b * α b (c a) := by
            apply Finset.prod_congr rfl
            intro a _
            rw [hcoc]
      _ = (∏ a : F, c b) * (∏ a : F, α b (c a)) := by
            rw [Finset.prod_mul_distrib]
      _ = (c b) ^ Nat.card F * α b C := by
            rw [Nat.card_eq_fintype_card, Finset.prod_const]
            congr 1
            exact (map_prod (α b) (fun a => c a) Finset.univ).symm
  have hαC (b : F) : α b C = C * (c b ^ Nat.card F)⁻¹ := by
    have h := hCb b
    calc
      α b C = (c b ^ Nat.card F)⁻¹ * C := by
        conv_rhs => rw [h]
        group
      _ = C * (c b ^ Nat.card F)⁻¹ := by rw [mul_comm]
  obtain ⟨v, hv⟩ := hpow.2 (C⁻¹)
  have hv' : v ^ Nat.card F = C⁻¹ := hv
  have hvα (b : F) : α b v = v * c b := by
    apply hpow.1
    calc
      (α b v) ^ Nat.card F = α b (v ^ Nat.card F) := by rw [map_pow]
      _ = α b (C⁻¹) := by rw [hv']
      _ = (α b C)⁻¹ := by rw [map_inv]
      _ = (C * (c b ^ Nat.card F)⁻¹)⁻¹ := by rw [hαC b]
      _ = c b ^ Nat.card F * C⁻¹ := by group
      _ = c b ^ Nat.card F * v ^ Nat.card F := by rw [hv']
      _ = (v * c b) ^ Nat.card F := by
            rw [mul_pow, mul_comm]
  refine ⟨v, fun b => ?_⟩
  calc
    c b = v⁻¹ * (v * c b) := by group
    _ = v⁻¹ * α b v := by rw [hvα b]

end Abelian


section Nilpotent

theorem exists_inv_mul_of_nilpotencyClass_le (n : ℕ) :
    ∀ (G : Type u) [Group G] [Group.IsNilpotent G],
      Group.nilpotencyClass G ≤ n →
      ∀ (F : Type v) [Group F] [Finite F],
        ∀ (α : F →* MulAut G),
          Function.Bijective (fun g : G => g ^ Nat.card F) →
          ∀ (c : F → G),
            (∀ a b, c (a * b) = c a * α a (c b)) →
            ∃ u : G, ∀ a, c a = u⁻¹ * α a u := by
  induction n with
  | zero =>
      intro G _ _ hclass F _ _ α hpow c hcoc
      have hzero : Group.nilpotencyClass G = 0 := Nat.le_zero.mp hclass
      let subsingletonG : Subsingleton G :=
        (Group.nilpotencyClass_zero_iff_subsingleton).mp hzero
      exact ⟨1, fun a => Subsingleton.elim (c a) (1⁻¹ * α a 1)⟩
  | succ n ih =>
      intro G _ _ hclass F _ _ α hpow c hcoc
      let Z : Subgroup G := Subgroup.center G
      let Q := G ⧸ Z
      have hnilQ : Group.IsNilpotent Q := Group.nilpotent_quotient_of_nilpotent Z
      have hclQ : Group.nilpotencyClass Q = Group.nilpotencyClass G - 1 := by
        dsimp [Q, Z]
        exact Group.nilpotencyClass_quotient_center
      have hclassQ : Group.nilpotencyClass Q ≤ n := by
        rw [hclQ]
        exact (Nat.sub_le_iff_le_add).mpr hclass
      let αQ : F →* MulAut Q :=
        { toFun := fun a => CFSG.quotientAut (α a)
          map_one' := by
            ext q
            induction q using QuotientGroup.induction_on with
            | H x =>
                rw [show α 1 = (1 : MulAut G) from map_one α]
                change CFSG.quotientAut (1 : MulAut G) (QuotientGroup.mk' Z x) =
                  (1 : MulAut Q) (QuotientGroup.mk' Z x)
                rw [CFSG.quotientAut_mk]
                rfl
          map_mul' := by
            intro a b
            ext q
            induction q using QuotientGroup.induction_on with
            | H x =>
                change CFSG.quotientAut (α (a * b)) (QuotientGroup.mk' Z x) =
                  CFSG.quotientAut (α a)
                    (CFSG.quotientAut (α b) (QuotientGroup.mk' Z x))
                rw [map_mul, CFSG.quotientAut_mk, CFSG.quotientAut_mk,
                  CFSG.quotientAut_mk]
                rfl }
      let cQ : F → Q := fun a => QuotientGroup.mk' Z (c a)
      have hcocQ : ∀ a b, cQ (a * b) = cQ a * αQ a (cQ b) := by
        intro a b
        dsimp only [cQ]
        change QuotientGroup.mk' Z (c (a * b)) =
          QuotientGroup.mk' Z (c a) *
            CFSG.quotientAut (α a) (QuotientGroup.mk' Z (c b))
        rw [hcoc, CFSG.quotientAut_mk, ← map_mul]
      have hpowQ : Function.Bijective (fun q : Q => q ^ Nat.card F) := by
        dsimp [Q, Z]
        exact bijective_pow_quotient_center hpow
      obtain ⟨uQ, huQ⟩ := ih Q hclassQ F αQ hpowQ cQ hcocQ
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective Z uQ
      rw [← hu] at huQ
      let w : F → G := fun a => u⁻¹ * α a u
      have huQ' : ∀ a, QuotientGroup.mk' Z (c a) = QuotientGroup.mk' Z (w a) := by
        intro a
        have h := huQ a
        dsimp only [cQ] at h
        have hR : (QuotientGroup.mk' Z u)⁻¹ *
            CFSG.quotientAut (α a) (QuotientGroup.mk' Z u) =
            QuotientGroup.mk' Z (w a) := by
          rw [CFSG.quotientAut_mk, ← map_inv, ← map_mul]
        change QuotientGroup.mk' Z (c a) =
          (QuotientGroup.mk' Z u)⁻¹ *
            CFSG.quotientAut (α a) (QuotientGroup.mk' Z u) at h
        rw [hR] at h
        exact h
      have hwcoc : ∀ a b, w (a * b) = w a * α a (w b) := by
        intro a b
        dsimp only [w]
        simp only [map_mul, map_inv, MulAut.mul_apply]
        group
      let dG : F → G := fun a => (w a)⁻¹ * c a
      have hdZ : ∀ a, dG a ∈ Z := by
        intro a
        change (w a)⁻¹ * c a ∈ Z
        exact (QuotientGroup.eq).mp (huQ' a).symm
      let d : F → Z := fun a => ⟨dG a, hdZ a⟩
      let αZ : F →* MulAut Z :=
        { toFun := fun a => CFSG.centerAut (α a)
          map_one' := by
            ext z
            simp [CFSG.centerAut_coe]
          map_mul' := by
            intro a b
            ext z
            simp [CFSG.centerAut_coe, MulAut.mul_apply] }
      have hαZ_coe : ∀ (a : F) (z : Z), ((αZ a z : Z) : G) = α a (z : G) := by
        intro a z
        exact CFSG.centerAut_coe (α a) z
      have hdcocG : ∀ a b, dG (a * b) = dG a * α a (dG b) := by
        intro a b
        have hd_comm : ∀ g : G, dG a * g = g * dG a :=
          fun g => (Subgroup.mem_center_iff.mp (hdZ a) g).symm
        calc
          dG (a * b) = (w (a * b))⁻¹ * c (a * b) := rfl
          _ = (w a * α a (w b))⁻¹ * (c a * α a (c b)) := by rw [hwcoc, hcoc]
          _ = (α a (w b))⁻¹ * (w a)⁻¹ * (c a * α a (c b)) := by group
          _ = (α a (w b))⁻¹ * ((w a)⁻¹ * c a) * α a (c b) := by group
          _ = (α a (w b))⁻¹ * dG a * α a (c b) := rfl
          _ = dG a * ((α a (w b))⁻¹ * α a (c b)) := by
                rw [show (α a (w b))⁻¹ * dG a = dG a * (α a (w b))⁻¹ from
                  (hd_comm (α a (w b))⁻¹).symm]
                group
          _ = dG a * α a ((w b)⁻¹ * c b) := by rw [← map_inv, ← map_mul]
          _ = dG a * α a (dG b) := rfl
      have hdcocZ : ∀ a b, d (a * b) = d a * αZ a (d b) := by
        intro a b
        apply Subtype.ext
        dsimp only [d]
        change dG (a * b) = dG a * ((αZ a (d b) : Z) : G)
        rw [hαZ_coe a (d b)]
        exact hdcocG a b
      have hpowZ : Function.Bijective (fun z : Z => z ^ Nat.card F) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          exact hpow.1 (congrArg Subtype.val hxy)
        · intro z
          obtain ⟨g, hg⟩ := hpow.2 (z : G)
          have hg' : g ^ Nat.card F = (z : G) := hg
          have hgZ : g ∈ Z :=
            mem_center_of_pow_mem_center hpow (by rw [hg']; exact z.2)
          exact ⟨⟨g, hgZ⟩, Subtype.ext hg'⟩
      have hcommZ : ∀ x y : Z, x * y = y * x := by
        intro x y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp y.2 (x : G)
      obtain ⟨vZ, hvZ⟩ :=
        exists_inv_mul_of_mul_comm (F := F) (A := Z) hcommZ αZ hpowZ d hdcocZ
      have hdG_v : ∀ a, dG a = (vZ : G)⁻¹ * α a (vZ : G) := by
        intro a
        have h := congrArg Subtype.val (hvZ a)
        simpa [d, hαZ_coe] using h
      refine ⟨u * (vZ : G), ?_⟩
      intro a
      have hv_comm : ∀ g : G, (vZ : G)⁻¹ * g = g * (vZ : G)⁻¹ := by
        intro g
        exact (Subgroup.mem_center_iff.mp (Z.inv_mem vZ.2) g).symm
      calc
        c a = w a * dG a := by
          dsimp only [w, dG]
          group
        _ = (u⁻¹ * α a u) * ((vZ : G)⁻¹ * α a (vZ : G)) := by
          rw [hdG_v a]
        _ = (u * (vZ : G))⁻¹ * α a (u * (vZ : G)) := by
          rw [mul_inv_rev, map_mul]
          rw [hv_comm u⁻¹]
          conv_rhs =>
            rw [mul_assoc,
              ← mul_assoc (vZ : G)⁻¹ (α a u) (α a (vZ : G))]
          rw [hv_comm (α a u)]
          group

theorem exists_inv_mul_of_finite_actor
    {F : Type v} [Group F] [Finite F]
    {G : Type u} [Group G] [Group.IsNilpotent G]
    (α : F →* MulAut G)
    (hpow : Function.Bijective (fun g : G => g ^ Nat.card F))
    (c : F → G)
    (hcoc : ∀ a b, c (a * b) = c a * α a (c b)) :
    ∃ u : G, ∀ a, c a = u⁻¹ * α a u :=
  exists_inv_mul_of_nilpotencyClass_le (Group.nilpotencyClass G) G
    (le_refl (Group.nilpotencyClass G)) F α hpow c hcoc

end Nilpotent

theorem cocycle_of_twist
    {A G : Type*} [Group A] [Group G]
    (α : A →* MulAut G) (c : A → G)
    (hcoc : ∀ a b, c (a * b) = c a * α a (c b)) (u : G) :
    ∀ a b, u * c (a * b) * (α (a * b) u)⁻¹ =
      (u * c a * (α a u)⁻¹) * α a (u * c b * (α b u)⁻¹) := by
  intro a b
  simp only [hcoc, map_mul, MulAut.mul_apply, map_inv]
  group

theorem exists_conj_of_mul_inv_mem_of_finite_actor
    {F : Type v} [Group F] [Finite F] {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hpow : Function.Bijective (fun x : N => x ^ Nat.card F))
    (φ ψ : F →* G) (hcong : ∀ a, φ a * (ψ a)⁻¹ ∈ N) :
    ∃ u : N, ∀ a, (u : G) * φ a * (u : G)⁻¹ = ψ a := by
  let α : F →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp ψ
  let c : F → N := fun a => ⟨φ a * (ψ a)⁻¹, hcong a⟩
  have hc : ∀ a b, c (a * b) = c a * α a (c b) := by
    intro a b
    apply Subtype.ext
    change φ (a*b) * (ψ (a*b))⁻¹ =
      (φ a * (ψ a)⁻¹) * (ψ a * (φ b * (ψ b)⁻¹) * (ψ a)⁻¹)
    rw [map_mul, map_mul]
    group
  obtain ⟨u, hu⟩ := exists_inv_mul_of_finite_actor α hpow c hc
  refine ⟨u, fun a => ?_⟩
  have h := congrArg Subtype.val (hu a)
  change φ a * (ψ a)⁻¹ = (u : G)⁻¹ * (ψ a * (u : G) * (ψ a)⁻¹) at h
  calc
    (u : G) * φ a * (u : G)⁻¹ =
      (u : G) * (φ a * (ψ a)⁻¹) * ψ a * (u : G)⁻¹ := by group
    _ = ψ a := by rw [h]; group

end CFSG.GroupTheory
