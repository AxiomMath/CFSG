module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionAlternating
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OrthogonalEightCover

open Matrix MatrixExtension
open scoped commutatorElement

variable {P : Type*} [Group P]

@[expose] def kerSq (π : P →* Multiplicative (binaryAltMatrices 4)) : Subgroup P where
  carrier := {c | c ∈ Subgroup.center P ∧ π c = 1 ∧ c ^ 2 = 1}
  mul_mem' {a b} ha hb := ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [map_mul, ha.2.1, hb.2.1, mul_one],
    by rw [(show Commute a b from (Subgroup.mem_center_iff.mp ha.1 b).symm).mul_pow, ha.2.2,
      hb.2.2, mul_one]⟩
  one_mem' := ⟨Subgroup.one_mem _, map_one π, one_pow 2⟩
  inv_mem' {a} ha := ⟨Subgroup.inv_mem _ ha.1, by rw [map_inv, ha.2.1, inv_one],
    by rw [inv_pow, ha.2.2, inv_one]⟩

instance kerSq_normal (π : P →* Multiplicative (binaryAltMatrices 4)) : (kerSq π).Normal :=
  Subgroup.normal_of_le_center fun _ h => h.1

theorem commutatorElement_sq_left' {a b : P} (hab : a * ⁅a, b⁆ = ⁅a, b⁆ * a) :
    ⁅a ^ 2, b⁆ = ⁅a, b⁆ ^ 2 := by
  simp only [commutatorElement_def, sq] at hab ⊢
  calc a * a * b * (a * a)⁻¹ * b⁻¹ = a * (a * b * a⁻¹ * b⁻¹) * (b * a⁻¹ * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * a * (b * a⁻¹ * b⁻¹) := by rw [hab]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group

theorem binary_alternating_four_extension_complement (act : GL (Fin 4) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binaryAltMatrices 4)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * ((π x).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ)
    (hC : π.ker ≤ Subgroup.center P) (hC4 : ∀ c ∈ π.ker, c ^ 4 = 1)
    (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c) :
    ∃ P₀ : Subgroup P, (∀ g, ∀ x ∈ P₀, act g x ∈ P₀) ∧ (∀ x ∈ P₀, π x = 1 → x ^ 2 = 1) ∧
      ∀ v, ∃ x ∈ P₀, π x = v := by
  classical
  set C₀ := kerSq π with hC₀
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  have hH : ∀ a b : Multiplicative (binaryAltMatrices 4), a * b = b * a := fun a b =>
    Multiplicative.toAdd.injective (Subtype.ext (by
      simp only [toAdd_mul, AddSubgroup.coe_add]
      exact add_comm _ _))
  have hsq : ∀ x : P, π (x ^ 2) = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [map_pow, toAdd_pow, AddSubgroup.coe_nsmul, two_nsmul]
    exact binary_add_self _
  have hcommC₀ : ∀ x y : P, ⁅x, y⁆ ∈ C₀ := by
    intro x y
    have hk : π ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hH _ _
    have hc := hC hk
    refine ⟨hc, hk, ?_⟩
    rw [← commutatorElement_sq_left' (Subgroup.mem_center_iff.mp hc x),
      commutatorElement_eq_one_of_mem_center_left (hC (hsq x))]
  have hC₀inv : ∀ g, ∀ c ∈ C₀, act g c ∈ C₀ := fun g c hc => by
    rw [hCfix g c hc.2.1]
    exact hc
  set actB : GL (Fin 4) (ZMod 2) →* MulAut (P ⧸ C₀) :=
    BinarySymplecticSix.quotientAct act C₀ hC₀inv with hactB
  have hactBmk : ∀ g (x : P), actB g (x : P ⧸ C₀) = (act g x : P ⧸ C₀) := fun g x =>
    BinarySymplecticSix.quotientAct_mk act C₀ hC₀inv g x
  set πB : P ⧸ C₀ →* Multiplicative (binaryAltMatrices 4) :=
    QuotientGroup.lift C₀ π fun c hc => hc.2.1 with hπBdef
  have hπB : ∀ x : P, πB (x : P ⧸ C₀) = π x := fun x => QuotientGroup.lift_mk _ _ _
  have hπBsurj : Function.Surjective πB := by
    intro v
    obtain ⟨x, hx⟩ := hπ v
    exact ⟨x, by rw [hπB, hx]⟩
  have hπBact : ∀ g x, ((πB (actB g x)).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * ((πB x).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H x => rw [hactBmk, hπB, hπB, hπact]
  have hcommB : ∀ a b : P ⧸ C₀, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact hcommC₀ _ _
  have hker : ∀ c : P ⧸ C₀, c ∈ πB.ker → ∃ y : P, π y = 1 ∧ (y : P ⧸ C₀) = c := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hπB] at hc
      exact ⟨y, hc, rfl⟩
  have hC2B : ∀ c ∈ πB.ker, c ^ 2 = 1 := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := hker c hc
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨Subgroup.pow_mem _ (hC hy) 2, by rw [map_pow, hy, one_pow], ?_⟩
    rw [← pow_mul]
    exact hC4 y hy
  have hCfixB : ∀ g, ∀ c ∈ πB.ker, actB g c = c := by
    intro g c hc
    obtain ⟨y, hy, rfl⟩ := hker c hc
    rw [hactBmk, hCfix g y hy]
  have hsqB := binaryAlt_sq_eq_one (by norm_num) actB πB hπBsurj hπBact hC2B hCfixB hcommB
  let _ : CommGroup (P ⧸ C₀) := { (inferInstance : Group (P ⧸ C₀)) with mul_comm := hcommB }
  let _ : Module (ZMod 2) (Additive (P ⧸ C₀)) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hsqB, ofMul_one]
  let actA : GL (Fin 4) (ZMod 2) →* AddMonoid.End (Additive (P ⧸ C₀)) :=
    { toFun := fun g => MonoidHom.toAdditive (actB g).toMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        rw [map_mul]
        rfl }
  have hactA : ∀ g x, actA g x = Additive.ofMul (actB g x.toMul) := fun _ _ => rfl
  let πA : Additive (P ⧸ C₀) →+ Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    { toFun := fun x => ((πB x.toMul).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hπA : ∀ x, πA x = ((πB x.toMul).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun _ => rfl
  have hkerA : ∀ x : Additive (P ⧸ C₀), πA x = 0 → x.toMul ∈ πB.ker := fun x h => by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hπactA : ∀ g x, πA (actA g x) = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * πA x *
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ := fun g x => by
    rw [hactA, hπA, hπA, toMul_ofMul, hπBact]
  have hCA : ∀ g, ∀ c ∈ πA.ker, actA g c = c := fun g c hc => by
    rw [hactA, hCfixB g _ (hkerA c hc), ofMul_toMul]
  have hF1 : ∀ {a b : Fin 4} (hab : a ≠ b) {i j : Fin 4}, i ≠ b → j ≠ b →
      ∀ {x : Additive (P ⧸ C₀)}, πA x = binaryOff i j → actA (binaryTransvection hab) x = x := by
    intro a b hab i j hi hj x hx
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x.toMul
    rw [← ofMul_toMul x, ← hy] at hx ⊢
    rw [hπA, toMul_ofMul, hπB] at hx
    set t := binaryTransvection hab with ht
    have hfix : π (act t y) = π y := hinj (by
      rw [hπact, hx, ht, binaryTransvection_congr_binaryOff_of_ne hab hi hj])
    have hc : π (act t y * y⁻¹) = 1 := by rw [map_mul, map_inv, hfix, mul_inv_cancel]
    have htt : act t (act t y) = y := by
      rw [← MulAut.mul_apply, ← map_mul, ht, binaryTransvection_mul_self, map_one,
        MulAut.one_apply]
    have hc2 : (act t y * y⁻¹) ^ 2 = 1 := by
      set c := act t y * y⁻¹ with hcdef
      have e : act t y = c * y := by rw [hcdef, inv_mul_cancel_right]
      have h2 : c * c * y = y := by
        have h3 := htt
        rw [e, map_mul, hCfix t c hc, e, ← mul_assoc] at h3
        exact h3
      rw [sq]
      exact mul_eq_right.mp h2
    have hcC₀ : act t y * y⁻¹ ∈ C₀ := ⟨hC hc, hc, hc2⟩
    rw [hactA, toMul_ofMul, hactBmk]
    congr 1
    rw [QuotientGroup.eq]
    have : (act t y)⁻¹ * y = y⁻¹ * (act t y * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [this]
    exact (kerSq_normal π).conj_mem _ (inv_mem hcC₀) y⁻¹
  have hliftA : ∀ i j : Fin 4, ∃ x, πA x = binaryOff i j := fun i j => by
    obtain ⟨x, hx⟩ := hπBsurj (Multiplicative.ofAdd ⟨binaryOff i j,
      binaryOff_mem_binaryAltMatrices i j⟩)
    exact ⟨Additive.ofMul x, by rw [hπA, toMul_ofMul, hx]; rfl⟩
  obtain ⟨o, ho, hos, hod, hact⟩ := exists_off_equivariant_lifts le_rfl hπactA hCA
    (fun hab _ _ hi hj _ hx => hF1 hab hi hj hx) hliftA
  obtain ⟨hSinj, hSsurj⟩ := altSection_closure_spec o hod hos πA ho
  set S := AddSubgroup.closure (Set.range fun p : Fin 4 × Fin 4 => o p.1 p.2) with hS
  have hSinv : ∀ g, ∀ x ∈ S, actA g x ∈ S := by
    refine fun g => act_mem_of_closure_eq_top actA closure_binaryTransvection ?_ ?_ g
    · rintro _ ⟨a, b, h, rfl⟩
      exact ⟨a, b, h, (binaryTransvection_inv h).symm⟩
    · rintro _ ⟨a, b, h, rfl⟩ x hx
      have hmem : ∀ k l, o k l ∈ S := fun k l => AddSubgroup.subset_closure ⟨(k, l), rfl⟩
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hy
        change actA (binaryTransvection h) (o i j) ∈ S
        rw [hact]
        refine add_mem (add_mem (hmem i j) ?_) ?_
        · split_ifs
          · exact hmem a j
          · exact zero_mem _
        · split_ifs
          · exact hmem i a
          · exact zero_mem _
      | zero => rw [map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
  let P₀ : Subgroup P :=
    { carrier := {x | Additive.ofMul (x : P ⧸ C₀) ∈ S}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul ((a * b : P) : P ⧸ C₀) ∈ S
        rw [QuotientGroup.mk_mul, ofMul_mul]
        exact S.add_mem ha hb
      one_mem' := by
        change Additive.ofMul ((1 : P) : P ⧸ C₀) ∈ S
        rw [QuotientGroup.mk_one, ofMul_one]
        exact S.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul ((a⁻¹ : P) : P ⧸ C₀) ∈ S
        rw [QuotientGroup.mk_inv, ofMul_inv]
        exact S.neg_mem ha }
  have hP₀ : ∀ x, x ∈ P₀ ↔ Additive.ofMul (x : P ⧸ C₀) ∈ S := fun _ => Iff.rfl
  refine ⟨P₀, fun g x hx => ?_, fun x hx h1 => ?_, fun v => ?_⟩
  · rw [hP₀] at hx ⊢
    have := hSinv g _ hx
    rwa [hactA, toMul_ofMul, hactBmk] at this
  · have h0 := hSinj _ hx (by rw [hπA, toMul_ofMul, hπB, h1]; rfl)
    rw [← ofMul_one, Additive.ofMul.injective.eq_iff, QuotientGroup.eq_one_iff] at h0
    exact h0.2.2
  · obtain ⟨s, hs, hsv⟩ := hSsurj _ v.toAdd.2
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective s.toMul
    refine ⟨x, by rw [hP₀, hx, ofMul_toMul]; exact hs, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [← hsv, hπA, ← hx, hπB]

end OrthogonalEightCover

end CFSG.LocalAnalysis.ComponentInitial
