module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Shape
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup GH74.Filter.Lie
open scoped commutatorElement MatrixGroups

namespace Q5Cube

@[expose] def z4Frattini : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

theorem z4Frattini_surjective : Function.Surjective z4Frattini := by decide

theorem z4Frattini_eq_one_of_sq :
    ∀ z : Multiplicative (ZMod 4), z ^ 2 = 1 → z4Frattini z = 1 := by decide

theorem sq_two : ∀ b : Multiplicative (ZMod 2), b ^ 2 = 1 := by decide

theorem z4_pow_four : ∀ m : Multiplicative (ZMod 4), m ^ 4 = 1 := by decide

theorem z4_cases : ∀ m : Multiplicative (ZMod 4), m = 1 ∨ m = Multiplicative.ofAdd 1 ∨
    m = Multiplicative.ofAdd 1 ^ 2 ∨ m = Multiplicative.ofAdd 1 ^ 3 := by decide

theorem zmodHom_injective {A : Type*} [Group A] {c : A} (hc : c ^ 4 = 1) (h4 : orderOf c = 4) :
    Function.Injective (LocalAnalysis.ComponentInitial.zmodHom 4 c hc) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have hone := LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one 4 c hc
  rcases z4_cases m with rfl | rfl | rfl | rfl
  · rfl
  · rw [hone] at hm
    rw [hm, orderOf_one] at h4
    omega
  · rw [map_pow, hone] at hm
    exact absurd hm (pow_ne_one_of_lt_orderOf (by norm_num) (by omega))
  · rw [map_pow, hone] at hm
    exact absurd hm (pow_ne_one_of_lt_orderOf (by norm_num) (by omega))

theorem not_gen4_of_q8_q8_z4 {P : Type*} [Group P] (ψ₁ ψ₂ : QuaternionGroup 2 →* P)
    (χ : Multiplicative (ZMod 4) →* P) (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂)
    (hχ : Function.Injective χ) (h12 : ∀ x y, Commute (ψ₁ x) (ψ₂ y))
    (h1χ : ∀ x z, Commute (ψ₁ x) (χ z)) (h2χ : ∀ y z, Commute (ψ₂ y) (χ z)) :
    ¬ GH74.Gen4 P := by
  let α₂ : QuaternionGroup 2 × Multiplicative (ZMod 4) →* P := ψ₂.noncommCoprod χ h2χ
  let α : QuaternionGroup 2 × (QuaternionGroup 2 × Multiplicative (ZMod 4)) →* P :=
    ψ₁.noncommCoprod α₂ (fun x yz => (h12 x yz.1).mul_right (h1χ x yz.2))
  have hα : ∀ x y z, α (x, (y, z)) = ψ₁ x * (ψ₂ y * χ z) := fun _ _ _ => rfl
  let β := q8Frattini.prodMap (q8Frattini.prodMap z4Frattini)
  refine GH74.Filter.not_gen4_of_surjection α β ?_ ?_ ?_ ?_ ?_
  · exact Prod.map_surjective.2 ⟨q8Frattini_surjective,
      Prod.map_surjective.2 ⟨q8Frattini_surjective, z4Frattini_surjective⟩⟩
  · exact fun a b => Prod.ext (q8Frattini_comm _ _) (Prod.ext (q8Frattini_comm _ _)
      (mul_comm _ _))
  · exact fun a => Prod.ext (q8Frattini_sq _) (Prod.ext (q8Frattini_sq _) (sq_two _))
  · rw [Nat.card_prod, Nat.card_prod, q8Frattini_card]
    simp [Nat.card_eq_fintype_card]
  · rintro ⟨x, y, z⟩ hxyz
    rw [MonoidHom.mem_ker, hα] at hxyz
    have ex : ψ₁ x = (ψ₂ y * χ z)⁻¹ := eq_inv_of_mul_eq_one_left hxyz
    have ey : ψ₂ y = (ψ₁ x)⁻¹ * (χ z)⁻¹ :=
      calc ψ₂ y = (ψ₁ x)⁻¹ * (ψ₁ x * (ψ₂ y * χ z)) * (χ z)⁻¹ := by group
        _ = (ψ₁ x)⁻¹ * (χ z)⁻¹ := by rw [hxyz, mul_one]
    have hx : ∀ w, x * w = w * x := fun w => h₁ (by
      rw [map_mul, map_mul, ex]
      exact (((h12 w y).mul_right (h1χ w z)).inv_right).symm.eq)
    have hy : ∀ w, y * w = w * y := fun w => h₂ (by
      rw [map_mul, map_mul, ey]
      exact (((h12 x w).symm.inv_right).mul_right ((h2χ w z).inv_right)).symm.eq)
    have hx2 : ψ₁ x ^ 2 = 1 := by
      rcases q8_central x hx with rfl | rfl
      · simp
      · rw [← map_pow, show (a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one]
    have hy2 : ψ₂ y ^ 2 = 1 := by
      rcases q8_central y hy with rfl | rfl
      · simp
      · rw [← map_pow, show (a 2 : QuaternionGroup 2) ^ 2 = 1 by decide, map_one]
    have ez : χ z = (ψ₁ x * ψ₂ y)⁻¹ :=
      calc χ z = (ψ₁ x * ψ₂ y)⁻¹ * (ψ₁ x * (ψ₂ y * χ z)) := by group
        _ = (ψ₁ x * ψ₂ y)⁻¹ := by rw [hxyz, mul_one]
    have hz2 : χ (z ^ 2) = 1 := by
      rw [map_pow, ez, inv_pow, (h12 x y).mul_pow, hx2, hy2, one_mul, inv_one]
    have hz : z ^ 2 = 1 := hχ (hz2.trans (map_one χ).symm)
    show (q8Frattini x, (q8Frattini y, z4Frattini z)) = 1
    rw [q8Frattini_center x hx, q8Frattini_center y hy, z4Frattini_eq_one_of_sq z hz]
    rfl

end Q5Cube

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.not_fourGenerated_of_cyclic4 (hD : TightDatum R S t) {N : Subgroup G}
    [N.Normal] {s : G} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) {H₁ H₂ : Subgroup G}
    (h₁N : H₁ ≤ N) (h₂N : H₂ ≤ N) (h₁ : H₁ ≤ Subgroup.centralizer ({t} : Set G))
    (h₂ : H₂ ≤ Subgroup.centralizer ({t} : Set G)) [Group.IsPerfect H₁] [Group.IsPerfect H₂]
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (φ₁ φ₂ : QuaternionGroup 2 →* G)
    (hi₁ : Function.Injective φ₁) (hi₂ : Function.Injective φ₂) (hr₁ : ∀ x, φ₁ x ∈ H₁)
    (hr₂ : ∀ x, φ₂ x ∈ H₂) : ¬ TwoSubgroupsFourGenerated N := by
  intro hF
  set C : Subgroup G := N ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  set O : Subgroup C := (oddCoreImg R).subgroupOf C with hOdef
  have hCt : ∀ g ∈ C, g ∈ Subgroup.centralizer ({t} : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp hg).2
  have : O.Normal := ⟨fun n hn g => by
    rw [hOdef, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using datum_conj_mem_oddCoreImg hD (hCt _ g.2) hn⟩
  have hC₁ : ∀ x, φ₁ x ∈ C := fun x => Subgroup.mem_inf.mpr ⟨h₁N (hr₁ x), h₁ (hr₁ x)⟩
  have hC₂ : ∀ x, φ₂ x ∈ C := fun x => Subgroup.mem_inf.mpr ⟨h₂N (hr₂ x), h₂ (hr₂ x)⟩
  have hsC : s ∈ C := Subgroup.mem_inf.mpr ⟨hsN, hD.cent hsR⟩
  have hs4' : (⟨s, hsC⟩ : C) ^ 4 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hs4, pow_orderOf_eq_one, Subgroup.coe_one]
  have hs4'' : orderOf (⟨s, hsC⟩ : C) = 4 := by rw [Subgroup.orderOf_mk, hs4]
  let χ₀ := LocalAnalysis.ComponentInitial.zmodHom 4 (⟨s, hsC⟩ : C) hs4'
  have hχ₀ : Function.Injective χ₀ := Q5Cube.zmodHom_injective hs4' hs4''
  have hχR : ∀ m, ((χ₀ m : C) : G) ∈ R := by
    intro m
    rcases Q5Cube.z4_cases m with rfl | rfl | rfl | rfl <;>
      simp only [map_one, map_pow, χ₀, LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one,
        Subgroup.coe_pow, Subgroup.coe_one] <;>
      first | exact R.one_mem | exact hsR | exact R.pow_mem hsR _
  have hO1 : ∀ c : C, c ∈ O → orderOf c ∣ 8 → c = 1 := fun c hc h8 => Subtype.ext
    (eq_one_of_mem_oddCoreImg (Subgroup.mem_subgroupOf.mp hc) (by rwa [Subgroup.orderOf_coe]))
  have hinj : ∀ {K : Type} [Group K] (f : K →* C), Function.Injective f →
      (∀ k : K, orderOf k ∣ 8) → Function.Injective ((QuotientGroup.mk' O).comp f) := by
    intro K _ f hf h8
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hf ((hO1 _ hk ((orderOf_map_dvd f k).trans (h8 k))).trans (map_one f).symm)
  have hcomm_mk : ∀ a b : C, ⁅(a : G), (b : G)⁆ ∈ oddCoreImg R →
      Commute (QuotientGroup.mk' O a) (QuotientGroup.mk' O b) := by
    intro a b hab
    show QuotientGroup.mk' O _ * QuotientGroup.mk' O _ =
      QuotientGroup.mk' O _ * QuotientGroup.mk' O _
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 := datum_conj_mem_oddCoreImg hD (hCt _ (a * b)⁻¹.2) ((oddCoreImg R).inv_mem hab)
    have e : (((a * b)⁻¹ : C) : G) * ⁅(a : G), (b : G)⁆⁻¹ * (((a * b)⁻¹ : C) : G)⁻¹ =
        (((a * b)⁻¹ * (b * a) : C) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rwa [e] at h1
  let ψ₁ := (QuotientGroup.mk' O).comp (φ₁.codRestrict C hC₁)
  let ψ₂ := (QuotientGroup.mk' O).comp (φ₂.codRestrict C hC₂)
  let χ := (QuotientGroup.mk' O).comp χ₀
  have hgen : GH74.Gen4 (C ⧸ O) := GH74.Gen4.quotient O (GH74.Gen4.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe inf_le_left) (GH74.Gen4.subgroup (C.subgroupOf N) hF))
  refine Q5Cube.not_gen4_of_q8_q8_z4 ψ₁ ψ₂ χ ?_ ?_ ?_ ?_ ?_ ?_ hgen
  · exact hinj _ (fun _ _ h => hi₁ (congrArg Subtype.val h)) orderOf_q8_dvd
  · exact hinj _ (fun _ _ h => hi₂ (congrArg Subtype.val h)) orderOf_q8_dvd
  · exact hinj _ hχ₀ fun m => (orderOf_dvd_of_pow_eq_one (Q5Cube.z4_pow_four m)).trans
      (by norm_num)
  · intro x y
    show Commute (QuotientGroup.mk' O _) (QuotientGroup.mk' O _)
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (hr₁ x) _ (hr₂ y))
  · exact fun x m => hcomm_mk _ _ (datum_commutator_mem hD h₁ _ (hr₁ x) _ (hχR m))
  · exact fun y m => hcomm_mk _ _ (datum_commutator_mem hD h₂ _ (hr₂ y) _ (hχR m))

theorem TightDatum.not_fourGenerated_of_sl2Pair_cyclic4 (hD : TightDatum R S t)
    {N : Subgroup G} [N.Normal] {s : G} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (htN : t ∈ N) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂)) (h4₁ : 4 ≤ Nat.card F₁)
    (h4₂ : 4 ≤ Nat.card F₂) {H₁ H₂ : Subgroup N}
    (h₁ : H₁ ≤ Subgroup.centralizer ({⟨t, htN⟩} : Set N))
    (h₂ : H₂ ≤ Subgroup.centralizer ({⟨t, htN⟩} : Set N))
    (hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (e₁ : H₁ ≃* SL(2, F₁)) (e₂ : H₂ ≃* SL(2, F₂)) :
    ¬ TwoSubgroupsFourGenerated N := by
  let e₁' : ↥(H₁.map N.subtype) ≃* SL(2, F₁) :=
    (Subgroup.equivMapOfInjective H₁ N.subtype N.subtype_injective).symm.trans e₁
  let e₂' : ↥(H₂.map N.subtype) ≃* SL(2, F₂) :=
    (Subgroup.equivMapOfInjective H₂ N.subtype N.subtype_injective).symm.trans e₂
  have : Group.IsPerfect (H₁.map N.subtype) := isPerfect_of_equiv_sl2 h4₁ e₁'
  have : Group.IsPerfect (H₂.map N.subtype) := isPerfect_of_equiv_sl2 h4₂ e₂'
  obtain ⟨φ₁, hi₁, hr₁, -⟩ := exists_q8_of_mulEquiv_sl2 hF₁ _ e₁'
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hF₂ _ e₂'
  have hcen : ∀ {H : Subgroup N}, H ≤ Subgroup.centralizer ({⟨t, htN⟩} : Set N) →
      H.map N.subtype ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro H hH _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hH hx)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  refine TightDatum.not_fourGenerated_of_cyclic4 hD hsR hsN hs4 (Subgroup.map_subtype_le _)
    (Subgroup.map_subtype_le _) (hcen h₁) (hcen h₂) ?_ φ₁ φ₂ hi₁ hi₂ hr₁ hr₂
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (hc a ha b hb)

theorem TightDatum.not_fourGenerated_of_twoSL2Shape_cyclic4 (hD : TightDatum R S t)
    {N : Subgroup G} [N.Normal] {s : G} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (htN : t ∈ N) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (hsh : TwoSL2Shape N ⟨t, htN⟩ F) : ¬ TwoSubgroupsFourGenerated N := by
  obtain ⟨H₁, H₂, h₁, h₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ := hsh
  exact TightDatum.not_fourGenerated_of_sl2Pair_cyclic4 hD hsR hsN hs4 htN hF hF h4 h4 h₁ h₂ hc
    e₁ e₂

end CFSG.ClassicalInvolution.Q3.TA3
