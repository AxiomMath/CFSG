module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3BabyForm
public import CFSG.Monster.B.Pinned.Primes.ThreeTwelve

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

open CFSG.Blueprint CFSG.Monster.B.Pinned Subgroup Module
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G] {n : ℕ} {q : Fin n → G} {z : G}
  {M : Matrix (Fin n) (Fin n) (ZMod 3)}

private theorem lg_inv' (hD : CommData 3 q z M) {y : G} (hy : y ∈ zpowers z) :
    lg 3 z y⁻¹ = -lg 3 z y := by
  have h := lg_mul (p := 3) hD.orderOf_z hy (inv_mem hy)
  rw [mul_inv_cancel, lg_one hD.orderOf_z] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem bcomm_mul_right' (hD : CommData 3 q z M) {u v w : G}
    (hu : u ∈ closure (Set.range q)) (hv : v ∈ closure (Set.range q))
    (hw : w ∈ closure (Set.range q)) : bcomm u (v * w) = bcomm u v * bcomm u w := by
  have h1 : bcomm (v * w) u = bcomm v u * bcomm w u := hD.bcomm_mul hv hw hu
  have hcomm : Commute (bcomm u v) (bcomm u w) := by
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (hD.bcomm_mem hu hv)
    obtain ⟨b, hb⟩ := mem_zpowers_iff.1 (hD.bcomm_mem hu hw)
    rw [← ha, ← hb]
    exact (Commute.refl z).zpow_zpow a b
  calc bcomm u (v * w) = (bcomm (v * w) u)⁻¹ := bcomm_swap _ _
    _ = (bcomm v u * bcomm w u)⁻¹ := by rw [h1]
    _ = (bcomm w u)⁻¹ * (bcomm v u)⁻¹ := mul_inv_rev _ _
    _ = bcomm u w * bcomm u v := by rw [← bcomm_swap, ← bcomm_swap]
    _ = bcomm u v * bcomm u w := hcomm.eq.symm

private theorem bcomm_inv_right' (hD : CommData 3 q z M) {u v : G}
    (hu : u ∈ closure (Set.range q)) (hv : v ∈ closure (Set.range q)) :
    bcomm u v⁻¹ = (bcomm u v)⁻¹ := by
  have h := bcomm_mul_right' hD hu (inv_mem hv) hv
  rw [inv_mul_cancel, show bcomm u 1 = 1 by simp [bcomm]] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem lg_bcomm' (hD : CommData 3 q z M) {u v : G} (hu : u ∈ closure (Set.range q))
    (hv : v ∈ closure (Set.range q)) :
    lg 3 z (bcomm u v) = coord 3 q z M u ⬝ᵥ (M *ᵥ coord 3 q z M v) := by
  have hpsi : psi 3 q z u = coord 3 q z M u ᵥ* M := by
    rw [coord, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hD.isUnit_det, Matrix.vecMul_one]
  induction hv using closure_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    have h1 : lg 3 z (bcomm u (q j)) = psi 3 q z u j := rfl
    rw [h1, hpsi, hD.coord_q j, Matrix.mulVec_single_one]
    rfl
  | one =>
    rw [show bcomm u 1 = 1 by simp [bcomm], lg_one hD.orderOf_z, hD.coord_one,
      Matrix.mulVec_zero, dotProduct_zero]
  | mul v w hv hw ihv ihw =>
    rw [bcomm_mul_right' hD hu hv hw, lg_mul hD.orderOf_z (hD.bcomm_mem hu hv)
      (hD.bcomm_mem hu hw), ihv, ihw, hD.coord_mul hv hw, Matrix.mulVec_add, dotProduct_add]
  | inv v hv ihv =>
    rw [bcomm_inv_right' hD hu hv, lg_inv' hD (hD.bcomm_mem hu hv), ihv, hD.coord_inv hv,
      Matrix.mulVec_neg, dotProduct_neg]

private theorem card_le_of_coord_mem [Finite G] (hD : CommData 3 q z M) {C : Subgroup G}
    (hCQ : C ≤ closure (Set.range q)) {W : Submodule (ZMod 3) (Fin n → ZMod 3)}
    (hW : ∀ c ∈ C, coord 3 q z M c ∈ W) : Nat.card C ≤ 3 * 3 ^ finrank (ZMod 3) W := by
  set f := hD.coordHom.comp (inclusion hCQ)
  have hker : Nat.card f.ker ≤ 3 := by
    have hz : ∀ b : f.ker, ((b : C) : G) ∈ zpowers z := fun b => by
      have hb : inclusion hCQ (b : C) ∈ hD.coordHom.ker := by
        rw [MonoidHom.mem_ker]
        exact MonoidHom.mem_ker.1 b.2
      rw [hD.ker_coordHom] at hb
      exact mem_subgroupOf.1 hb
    calc Nat.card f.ker ≤ Nat.card (zpowers z) :=
          Nat.card_le_card_of_injective (fun b => ⟨_, hz b⟩) fun b b' e => by
            have e' := congrArg Subtype.val e
            exact Subtype.ext (Subtype.ext e')
      _ = 3 := by rw [Nat.card_zpowers, hD.orderOf_z]
  have hrange : Nat.card f.range ≤ Nat.card W := by
    have hr : ∀ r : f.range, Multiplicative.toAdd (r : Multiplicative (Fin n → ZMod 3)) ∈ W := by
      rintro ⟨_, b, rfl⟩
      exact hW b b.2
    exact Nat.card_le_card_of_injective (fun r => ⟨_, hr r⟩) fun r r' e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext (Multiplicative.toAdd.injective e')
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := W), Nat.card_zmod] at hrange
  rw [← Subgroup.card_ker_mul_card_range f]
  exact Nat.mul_le_mul hker hrange

end Generic

section Local


private theorem le_Q_of_le_ker (h13 : (Nat.card NativeSporadic.B).factorization 3 = 13)
    {C : Subgroup LThree} (hC : C ≤ rhoThree.ker) (h3 : IsPGroup 3 C) :
    C ≤ QThree.subgroupOf LThree := by
  haveI := finite_B
  haveI := normal_QThree_LThree
  have hQ : Nat.card (QThree.subgroupOf LThree) = 3 ^ 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe QThree_le_LThree).toEquiv, card_QThree]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (h3.to_sup_of_normal_right (IsPGroup.of_card hQ))
  by_contra hCQ
  have hlt : QThree.subgroupOf LThree < C ⊔ QThree.subgroupOf LThree :=
    lt_of_le_of_ne le_sup_right fun e => hCQ (le_sup_left.trans e.symm.le)
  have h10 : 10 ≤ k := by
    have h := card_lt_of_lt hlt
    rw [hk, hQ] at h
    have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 3)).1 h
    omega
  have hker : 3 ^ 10 ∣ Nat.card rhoThree.ker :=
    (pow_dvd_pow 3 h10).trans (by rw [← hk]; exact card_dvd_of_le (sup_le hC QThree_le_ker))
  have hK : 3 ^ 4 ∣ Nat.card rhoThree.range := by
    rw [range_rhoThree, show 3 ^ 4 = 81 by norm_num, ← card_sylS]
    exact card_dvd_of_le sylS_le_KThree
  have hL : Nat.card rhoThree.ker * Nat.card rhoThree.range ∣ Nat.card NativeSporadic.B := by
    rw [Subgroup.card_ker_mul_card_range]
    exact card_subgroup_dvd_card LThree
  have hdvd : 3 ^ 14 ∣ Nat.card NativeSporadic.B := by
    rw [show 3 ^ 14 = 3 ^ 10 * 3 ^ 4 by norm_num]
    exact (Nat.mul_dvd_mul hker hK).trans hL
  have := (Nat.prime_three.pow_dvd_iff_le_factorization
    (Nat.card_pos (α := NativeSporadic.B)).ne').1 hdvd
  omega

private theorem span_coord_le_orthogonal {C : Subgroup NativeSporadic.B} (hCQ : C ≤ QThree)
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) :
    Submodule.span (ZMod 3) (coord 3 qThree zThree MThree '' (C : Set NativeSporadic.B)) ≤
      (Matrix.toBilin' MThree).orthogonal
        (Submodule.span (ZMod 3) (coord 3 qThree zThree MThree '' (C : Set NativeSporadic.B))) := by
  have hD := commData_three
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun n hn => ?_
  induction hn using Submodule.span_induction with
  | mem n hn =>
    obtain ⟨a, ha, rfl⟩ := hn
    rw [Matrix.toBilin'_apply', ← lg_bcomm' hD (hCQ ha) (hCQ hb),
      (bcomm_eq_one_iff (G := NativeSporadic.B)).2 (hC a ha b hb), lg_one hD.orderOf_z]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add n m _ _ hn hm => rw [map_add, LinearMap.add_apply, hn, hm, add_zero]
  | smul c n _ hn => rw [map_smul, LinearMap.smul_apply, hn, smul_zero]

private theorem coord_vecMul_rho {f : LThree} {c : NativeSporadic.B} (hc : c ∈ QThree)
    (hcf : c * (f : NativeSporadic.B) = f * c) :
    coord 3 qThree zThree MThree c ᵥ*
      ((rhoThree f : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      coord 3 qThree zThree MThree c := by
  rw [← coord_conj_three f hc, mul_assoc, hcf, inv_mul_cancel_left]

theorem card_le_of_le_comap_sylS (h13 : (Nat.card NativeSporadic.B).factorization 3 = 13)
    {F : Subgroup LThree} (hFP : F ≤ sylS.comap rhoThree) (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF3 : IsPGroup 3 F) : Nat.card F ≤ 3 ^ 6 := by
  haveI := finite_B
  have hD := commData_three
  set ψ := rhoThree.comp F.subtype
  have hKQ := le_Q_of_le_ker h13 (C := ψ.ker.map F.subtype) (by rintro _ ⟨f, hf, rfl⟩; exact hf)
    ((hF3.to_subgroup ψ.ker).map F.subtype)
  obtain ⟨C, hCQ, hCF, hC, hCk⟩ : ∃ C : Subgroup NativeSporadic.B, C ≤ QThree ∧
      (∀ c ∈ C, ∀ f ∈ F, c * (f : NativeSporadic.B) = f * c) ∧
      (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∧ Nat.card C = Nat.card ψ.ker := by
    have hCF : ∀ c ∈ (ψ.ker.map F.subtype).map LThree.subtype, ∀ f ∈ F,
        c * (f : NativeSporadic.B) = f * c := by
      rintro _ ⟨_, ⟨g, -, rfl⟩, rfl⟩ f hf
      rw [Subgroup.coe_subtype, Subgroup.coe_subtype, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        hF _ g.2 f hf]
    refine ⟨(ψ.ker.map F.subtype).map LThree.subtype, ?_, hCF, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact mem_subgroupOf.1 (hKQ hf)
    · rintro a ha _ ⟨_, ⟨g, -, rfl⟩, rfl⟩
      exact hCF a ha _ g.2
    · rw [card_map_of_injective LThree.subtype_injective,
        card_map_of_injective F.subtype_injective]
  have hDS : ψ.range ≤ sylS := by
    rintro _ ⟨f, rfl⟩
    exact hFP f.2
  have hDc : ∀ d ∈ ψ.range, ∀ d' ∈ ψ.range, d * d' = d' * d := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hF _ a.2 _ b.2)
    rw [← map_mul, ← map_mul, hab]
  have hfix : ∀ d ∈ ψ.range, ∀ u ∈ Submodule.span (ZMod 3)
      (coord 3 qThree zThree MThree '' (C : Set NativeSporadic.B)),
      u ᵥ* (d : Matrix (Fin 8) (Fin 8) (ZMod 3)) = u := by
    rintro _ ⟨f, rfl⟩ u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨c, hc, rfl⟩ := hu
      exact coord_vecMul_rho (hCQ hc) (hCF c hc _ f.2)
    | zero => rw [Matrix.zero_vecMul]
    | add u v _ _ hu hv => rw [Matrix.add_vecMul, hu, hv]
    | smul r u _ hu => rw [Matrix.smul_vecMul, hu]
  have h5 := card_mul_le_of_le_sylS hDS hDc (span_coord_le_orthogonal hCQ hC) hfix
  have hW := card_le_of_coord_mem hD hCQ (W := Submodule.span (ZMod 3)
    (coord 3 qThree zThree MThree '' (C : Set NativeSporadic.B)))
    fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range ψ, ← hCk]
  calc Nat.card C * Nat.card ψ.range ≤ 3 * 3 ^ finrank (ZMod 3) (Submodule.span (ZMod 3)
        (coord 3 qThree zThree MThree '' (C : Set NativeSporadic.B))) * Nat.card ψ.range :=
        Nat.mul_le_mul_right _ hW
    _ ≤ 3 * 3 ^ 5 := by rw [mul_assoc]; exact Nat.mul_le_mul_left 3 h5
    _ = 3 ^ 6 := by norm_num

end Local

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

end
