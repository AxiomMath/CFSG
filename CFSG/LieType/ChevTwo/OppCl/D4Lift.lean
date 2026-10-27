module

public import CFSG.LieType.ChevTwo.OppCl.D4Normal
public import CFSG.LieType.ChevTwo.OppositeFixedExcE78

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Cert

variable
    {K : Type} [Field K] [Finite K]

theorem d4P_pow_three : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K

theorem fieldAut_d4P (σ : RingAut K) : fieldAutHom Tag.D4 K σ (d4P K) = d4P K :=
  units_map_entrywiseHom_diagramMap (σ : K →+* K)

theorem map_conj_d4P_pow (n : ℕ) {H : Subgroup (ModGL Tag.D4 K)}
    (hH : H = adjointGroup Tag.D4 K ∨ H = posUnipotent Tag.D4 K ∨
      H = negUnipotent Tag.D4 K) :
    H.map (MulAut.conj (d4P K ^ n)).toMonoidHom = H :=
  map_conj_pow_of_map_conj (diagramMap TwistTag.D4 K) (map_conj_diagramMap TwistTag.D4 K hH) n

theorem map_conj_d4P {H : Subgroup (ModGL Tag.D4 K)}
    (hH : H = adjointGroup Tag.D4 K ∨ H = posUnipotent Tag.D4 K ∨
      H = negUnipotent Tag.D4 K) :
    H.map (MulAut.conj (d4P K)).toMonoidHom = H := by
  simpa using map_conj_d4P_pow (K := K) 1 hH

theorem d4P_mem_normalizer_adjointGroup :
    d4P K ∈ Subgroup.normalizer (adjointGroup Tag.D4 K : Set (ModGL Tag.D4 K)) :=
  mem_normalizer_of_map_eq (map_conj_d4P (Or.inl rfl))

theorem map_conj_eq_of_mem_normalizer' {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 h y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
    have := (Subgroup.mem_normalizer_iff.1 h (g⁻¹ * x * g)).2
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact this hx

variable (K) in
@[expose] noncomputable def d4Chat : Subgroup (ModGL Tag.D4 K) :=
  adjointGroup Tag.D4 K ⊔ Subgroup.zpowers (d4P K)

theorem fieldAut_mem_d4Chat (σ : RingAut K) {h : ModGL Tag.D4 K} (hh : h ∈ d4Chat K) :
    fieldAutHom Tag.D4 K σ h ∈ d4Chat K := by
  have hle : d4Chat K ≤ (d4Chat K).comap (fieldAutHom Tag.D4 K σ).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_sup_left (fieldAut_mem_adjointGroup σ hx)
    · rw [Subgroup.mem_comap]
      change fieldAutHom Tag.D4 K σ (d4P K) ∈ d4Chat K
      rw [fieldAut_d4P]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact hle hh

variable (K) in
@[expose] noncomputable def d4LiftSub : Subgroup (GamL Tag.D4 K) :=
  gamSub (d4Chat K) fun _ _ hh => fieldAut_mem_d4Chat _ hh

theorem d4Chat_le_normalizer :
    d4Chat K ≤ Subgroup.normalizer (adjointGroup Tag.D4 K : Set (ModGL Tag.D4 K)) :=
  sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 d4P_mem_normalizer_adjointGroup)

theorem mem_sup_zpowers_d4P_iff {H : Subgroup (ModGL Tag.D4 K)}
    (hH : d4P K ∈ Subgroup.normalizer (H : Set (ModGL Tag.D4 K))) {x : ModGL Tag.D4 K} :
    x ∈ H ⊔ Subgroup.zpowers (d4P K) ↔ ∃ h ∈ H, ∃ i : ℕ, x = h * d4P K ^ i := by
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  have hLE : Subgroup.zpowers (d4P K) ≤ Subgroup.normalizer (H : Set (ModGL Tag.D4 K)) :=
    Subgroup.zpowers_le.2 hH
  have hco := Subgroup.coe_mul_of_right_le_normalizer_left H (Subgroup.zpowers (d4P K)) hLE
  constructor
  · intro hx
    have hx' : x ∈ (H : Set (ModGL Tag.D4 K)) * (Subgroup.zpowers (d4P K) : Set (ModGL Tag.D4 K)) := by
      rw [← hco]; exact hx
    obtain ⟨h, hh, y, hy, rfl⟩ := hx'
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
    exact ⟨h, hh, i, by rw [hi]⟩
  · rintro ⟨h, hh, i, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i))

theorem map_conjAct_adjointGroup {s : GamL Tag.D4 K} (hs : s ∈ d4LiftSub K) :
    (adjointGroup Tag.D4 K).map (conjAct Tag.D4 K s).toMonoidHom = adjointGroup Tag.D4 K := by
  have e : conjAct Tag.D4 K s = MulAut.conj s.left * fieldAutHom Tag.D4 K s.right := rfl
  rw [e, map_toMonoidHom_mul_mulAut]
  have h1 : (adjointGroup Tag.D4 K).map (fieldAutHom Tag.D4 K s.right).toMonoidHom =
      adjointGroup Tag.D4 K := map_exactEntrywiseAut s.right (Or.inl rfl)
  rw [h1]
  exact map_conj_eq_of_mem_normalizer' (d4Chat_le_normalizer hs)

@[expose] noncomputable def d4LiftHom : d4LiftSub K →* MulAut (adjointGroup Tag.D4 K) where
  toFun s := mulAutRestrict (adjointGroup Tag.D4 K) (conjAct Tag.D4 K s.1)
    (map_conjAct_adjointGroup s.2)
  map_one' := MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_mulAutRestrict, MulAut.one_apply]
    show conjAct Tag.D4 K (1 : GamL Tag.D4 K) (h : ModGL Tag.D4 K) = h
    rw [map_one]; rfl)
  map_mul' s t := MulEquiv.ext fun h => Subtype.ext (by
    rw [MulAut.mul_apply, coe_mulAutRestrict, coe_mulAutRestrict, coe_mulAutRestrict]
    show conjAct Tag.D4 K (s.1 * t.1) (h : ModGL Tag.D4 K) =
      conjAct Tag.D4 K s.1 (conjAct Tag.D4 K t.1 h)
    rw [map_mul]; rfl)

theorem coe_d4LiftHom (s : d4LiftSub K) (h : adjointGroup Tag.D4 K) :
    ((d4LiftHom s h : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = conjAct Tag.D4 K s.1 h := rfl

@[expose] noncomputable def d4MkLift (g : adjointGroup Tag.D4 K) (σ : K ≃+* K) (i : ℕ) :
    GamL Tag.D4 K :=
  ⟨(g : ModGL Tag.D4 K) * d4P K ^ i, σ⟩

theorem d4MkLift_mem (g : adjointGroup Tag.D4 K) (σ : K ≃+* K) (i : ℕ) :
    d4MkLift g σ i ∈ d4LiftSub K :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left g.2)
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i))

theorem coe_d4LiftHom_d4MkLift (g : adjointGroup Tag.D4 K) (σ : K ≃+* K) (i : ℕ)
    (h : adjointGroup Tag.D4 K) :
    ((d4LiftHom ⟨d4MkLift g σ i, d4MkLift_mem g σ i⟩ h : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      (g : ModGL Tag.D4 K) * d4P K ^ i *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K) *
          ((g : ModGL Tag.D4 K) * d4P K ^ i)⁻¹ := by
  rw [coe_d4LiftHom, conjAct_apply]
  rfl

theorem d4Rho_pow_eq_one_iff (i : ℕ) : d4Rho ^ i = 1 ↔ i % 3 = 0 := by
  have h3 : d4Rho ^ 3 = 1 := d4Rho_pow_three'
  have e : d4Rho ^ i = d4Rho ^ (i % 3) := by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, h3, one_pow, mul_one]
  rw [e]
  have key : ∀ r : ℕ, r < 3 → (d4Rho ^ r = 1 ↔ r = 0) := by
    intro r hr
    interval_cases r <;> simp <;> decide
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem d4P_pow_eq_one_of_mod {i : ℕ} (h : i % 3 = 0) : d4P K ^ i = 1 := by
  rw [← Nat.mod_add_div i 3, h, zero_add, pow_mul, d4P_pow_three, one_pow]

theorem d4LiftHom_mkLift_eq (g : adjointGroup Tag.D4 K) (σ : K ≃+* K) (i : ℕ) :
    d4LiftHom ⟨d4MkLift g σ i, d4MkLift_mem g σ i⟩ =
      MulAut.conj g * (exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K i) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have hP : Units.map (entrywiseHom σ.toRingHom) (d4P K) = d4P K :=
    units_map_entrywiseHom_diagramMap σ.toRingHom
  rw [coe_d4LiftHom_d4MkLift, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, coe_exactNormalAut_zero, rootDiagUnit_one, coe_d4Graph,
    Subgroup.coe_inv]
  simp only [one_mul, inv_one, mul_one, map_mul, map_inv, map_pow, hP]
  group

theorem eq_one_of_conj_normal_form_eq_one {g : adjointGroup Tag.D4 K} {σ : K ≃+* K} {i : ℕ}
    (h : MulAut.conj g * (exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K i) = 1) :
    g = 1 ∧ σ = 1 ∧ d4P K ^ i = 1 := by
  have hA : exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K i = MulAut.conj g⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_right h
  have hAmem : MulAut.conj g⁻¹ ∈ unipotentPairAut Tag.D4 K :=
    hA ▸ mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem i)
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hAmem
  have hperm : d4Rho ^ i = 1 := by
    refine perm_map_simple_unique (α := exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K i)
      (π := d4Rho ^ i) (π' := 1) (fun j => ?_) (fun j => ?_)
    · rw [map_toMonoidHom_mul_mulAut, map_simplePosSubgroup_d4Graph,
        map_simplePosSubgroup_exactNormalAut]
      rfl
    · rw [hA, hb, map_simplePosSubgroup_exactNormalAut]
      rfl
  have hi : d4P K ^ i = 1 := d4P_pow_eq_one_of_mod ((d4Rho_pow_eq_one_iff i).1 hperm)
  have hγ : d4Graph K i = 1 := MulEquiv.ext fun x => Subtype.ext (by
    rw [coe_d4Graph, hi]; simp)
  have hE : exactNormalAut Tag.D4 K 1 σ 0 = exactNormalAut Tag.D4 K b 1 0 := by
    rw [hγ, mul_one] at hA
    exact hA.trans hb
  obtain ⟨-, hσ⟩ := exactNormalAut_zero_injective (σ' := 1) hE
  have hE1 : exactNormalAut Tag.D4 K 1 σ 0 = 1 := by rw [hσ]; exact exactNormalAut_one_one_zero
  have h1 : MulAut.conj g⁻¹ = 1 := by rw [← hA, hE1, hγ, mul_one]
  have hg1 : g⁻¹ = 1 := mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
    (h1.trans (map_one _).symm)
  exact ⟨inv_eq_one.1 hg1, hσ, hi⟩

theorem d4LiftHom_injective : Function.Injective (d4LiftHom (K := K)) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => ?_
  obtain ⟨g, hg, i, hgi⟩ := (mem_sup_zpowers_d4P_iff d4P_mem_normalizer_adjointGroup).1
    (show s.1.left ∈ adjointGroup Tag.D4 K ⊔ Subgroup.zpowers (d4P K) from s.2)
  have hs' : s = ⟨d4MkLift ⟨g, hg⟩ s.1.right i, d4MkLift_mem _ _ _⟩ :=
    Subtype.ext (SemidirectProduct.ext hgi rfl)
  rw [hs', d4LiftHom_mkLift_eq] at hs
  obtain ⟨hg1, hσ1, hi1⟩ := eq_one_of_conj_normal_form_eq_one hs
  rw [hs']
  refine Subtype.ext (SemidirectProduct.ext ?_ ?_)
  · show (⟨g, hg⟩ : adjointGroup Tag.D4 K).1 * d4P K ^ i = 1
    rw [hi1, mul_one]
    exact congrArg Subtype.val hg1
  · exact hσ1

theorem exists_lift_of_odd (hK : ringChar K = 2) {m : ℕ} (hm : Odd m)
    {α : MulAut (adjointGroup Tag.D4 K)} (hα : α ^ m = 1) :
    ∃ s : d4LiftSub K, d4LiftHom s = α := by
  obtain ⟨g, σ, ε, -, h⟩ := exists_odd_normal_form hK hm hα
  exact ⟨⟨d4MkLift g σ ε, d4MkLift_mem g σ ε⟩, MulEquiv.ext fun x => Subtype.ext (by
    rw [coe_d4LiftHom_d4MkLift, h x])⟩

theorem exists_lift_group (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut (adjointGroup Tag.D4 K))} (hR : IsPGroup p R) :
    ∃ T : Subgroup (GamL Tag.D4 K), T ≤ d4LiftSub K ∧ Odd (Nat.card T) ∧
      (∀ α ∈ R, ∃ s ∈ T, ∀ h : adjointGroup Tag.D4 K,
        (α h : ModGL Tag.D4 K) = conjAct Tag.D4 K s h) ∧
      (∀ s ∈ T, ∃ α ∈ R, ∀ h : adjointGroup Tag.D4 K,
        (α h : ModGL Tag.D4 K) = conjAct Tag.D4 K s h) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hrange : R ≤ (d4LiftHom (K := K)).range := by
    intro α hα
    obtain ⟨k, hk⟩ := hR ⟨α, hα⟩
    have hk' : α ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨s, hs⟩ := exists_lift_of_odd hK (hodd.pow : Odd (p ^ k)) hk'
    exact ⟨s, hs⟩
  set T0 : Subgroup (d4LiftSub K) := R.comap d4LiftHom with hT0
  refine ⟨T0.map (d4LiftSub K).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact s.2
  · have h1 : Nat.card (T0.map (d4LiftSub K).subtype) = Nat.card T0 :=
      Subgroup.card_map_of_injective (d4LiftSub K).subtype_injective
    have h2 : Nat.card T0 = Nat.card R := by
      have h3 : Nat.card (T0.map (d4LiftHom (K := K))) = Nat.card T0 :=
        Subgroup.card_map_of_injective d4LiftHom_injective
      rw [← h3, hT0, Subgroup.map_comap_eq, inf_of_le_right hrange] 
    rw [h1, h2]
    haveI : Finite R := inferInstance
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact hodd.pow
  · intro α hα
    obtain ⟨s, hs⟩ := hrange hα
    refine ⟨s.1, ⟨s, ?_, rfl⟩, fun h => ?_⟩
    · show d4LiftHom s ∈ R
      rw [hs]; exact hα
    · rw [← hs]; rfl
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨d4LiftHom s, hs, fun h => rfl⟩

end Cert

end CFSG.LieType.ChevTwo.Semi
