module

public import CFSG.LocalAnalysis.EvenBN.GMS.ComponentAction
public import CFSG.LocalAnalysis.EvenBN.GMS.NormalForms
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGoldschmidt
public import CFSG.LocalAnalysis.EvenBN.GMS.GoldschmidtLayer

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.ABGLocalTools
open scoped MatrixGroups

theorem isElementaryAbelian_of_mul_self {G : Type*} [Group G] {E : Subgroup G}
    (hE : ∀ x ∈ E, x * x = 1) : IsElementaryAbelian 2 E where
  is_comm := ⟨fun a b => by
    apply Subtype.ext
    have ha : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hE _ a.2)
    have hb : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hE _ b.2)
    have hab : ((a : G) * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hE _ (mul_mem a.2 b.2))
    rw [mul_inv_rev, ha, hb] at hab
    simp only [coe_mul]
    exact hab.symm⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by rw [pow_two]; exact hE _ g.2)

namespace LocalSetting

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

theorem not_isSolvable_A (h : LocalSetting A t U V D n) : ¬ Group.IsSolvable A := by
  have := h.isSimpleGroup
  have hnab : ∃ a b : A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ : center A = ⊤ := eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun b => hcon b a
    rw [h.center_eq_bot] at hZ
    apply h.U_ne_bot
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, h.U_le hu⟩ : A) ∈ (⊥ : Subgroup A) := by rw [hZ]; exact mem_top _
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp h1))
  have : Group.IsPerfect A := ⟨Helpers.commutator_eq_top A hnab⟩
  have : Nontrivial A := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨⟨a * b, b * a, hab⟩⟩
  exact Group.IsPerfect.not_isSolvable A

theorem alternative_two (h : LocalSetting A t U V D n)
    (S : Sylow 2 H) (hVS : V ≤ S)
    (hE : sSup {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ normalClosure (V : Set H)} =
      normalClosure (V : Set H))
    (htype : ∀ K : Subgroup H, IsComponentOf K ⊤ → K ≤ normalClosure (V : Set H) →
      goldschmidtSimpleType (K ⧸ center K))
    (hmemV : ∀ x ∈ (S : Subgroup H), x ∈ normalClosure (V : Set H) → x * x = 1 → x ∈ V)
    {K : Subgroup H} (hK : IsComponentOf K ⊤) (hLK : CFSG.layer H = K) :
    ∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
      ∃ ψ : CFSG.layer H ≃* SL(2, k₂),
        (∀ x y : CFSG.layer H, (y : H) = t⁻¹ * x * t →
          ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
            (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
        ∀ g : SL(2, k₂), g ∈ (A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom ↔
          ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
            (g : Matrix (Fin 2) (Fin 2) k₂) i j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := h.layer_eq_normalClosure hE
  have hAL := h.A_le_layer hE
  have hVL : V ≤ CFSG.layer H := hLV ▸ (le_normalClosure : V ≤ normalClosure (V : Set H))
  have hLC : centralizer (CFSG.layer H : Set H) = ⊥ := hLV ▸ h.centralizer_normalClosure_eq_bot
  have htinv : t⁻¹ = t := h.t_inv
  have htt : t * t = 1 := h.t_mul_t
  have hX : goldschmidtSimpleType (CFSG.layer H) := by
    have hT := htype K hK (hLK ▸ hLV.le)
    have hZ := h.center_eq_bot_of_isComponentOf hE hK
    let e1 : (K ⧸ center K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let e2 : K ≃* CFSG.layer H := MulEquiv.subgroupCongr hLK.symm
    exact CFSG.Goldschmidt.Red2.goldschmidtSimpleType_of_mulEquiv (e1.trans e2).symm hT
  have h16 : 16 ∣ Nat.card (CFSG.layer H) := by
    have h1 : Nat.card V ∣ Nat.card (CFSG.layer H) := card_dvd_of_le hVL
    rw [h.card_V] at h1
    refine dvd_trans ?_ h1
    calc 16 = (2 ^ 2) ^ 2 := by norm_num
      _ ∣ (2 ^ n) ^ 2 := pow_dvd_pow_of_dvd (pow_dvd_pow 2 h.two_le) 2
  let α : MulAut (CFSG.layer H) := MulAut.conjNormal t
  have hα : ∀ x : CFSG.layer H, (α x : H) = t⁻¹ * x * t := by
    intro x
    change ((MulAut.conjNormal t) x : H) = _
    rw [MulAut.conjNormal_apply, htinv]
  have hαα : α * α = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc t⁻¹ * (t⁻¹ * (x : H) * t) * t = (t⁻¹ * t⁻¹) * x * (t * t) := by group
      _ = x := by rw [htinv, htt, one_mul, mul_one]
  have htL : t ∉ CFSG.layer H := by
    intro htL
    have hot : orderOf (⟨t, htL⟩ : CFSG.layer H) = 2 := by rw [orderOf_mk, h.orderOf_t]
    refine CFSG.SeitzReduction.RankOne.false_of_goldschmidtSimpleType hX h16
      (U := zpowers ⟨t, htL⟩) (Y := A.subgroupOf (CFSG.layer H)) ?_ ?_ ?_ ?_
    · rw [Ne, zpowers_eq_bot]
      intro h1
      exact h.t_ne_one (congrArg Subtype.val h1)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hot, pow_one])
    · rw [CFSG.SeitzReduction.RankOne.normalizer_zpowers_eq_centralizer_of_involution hot]
      intro a ha
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (h.le_centralizer (mem_subgroupOf.mp ha)))
    · intro hsol
      exact h.not_isSolvable_A (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hAL).symm.toMonoidHom) (subgroupOfEquivOfLe hAL).symm.injective)
  have hαout : α ∉ (MulAut.conj : CFSG.layer H →* MulAut (CFSG.layer H)).range := by
    rintro ⟨g, hg⟩
    have hgt : (g : H)⁻¹ * t ∈ centralizer (CFSG.layer H : Set H) := by
      refine mem_centralizer_iff.mpr fun y hy => ?_
      have h1 := congrArg (fun φ : MulAut (CFSG.layer H) => ((φ ⟨y, hy⟩ : CFSG.layer H) : H)) hg
      simp only [MulAut.conj_apply, coe_mul, coe_inv] at h1
      rw [hα] at h1
      rw [htinv] at h1
      calc y * ((g : H)⁻¹ * t) = (g : H)⁻¹ * (g * y * (g : H)⁻¹) * t := by group
        _ = (g : H)⁻¹ * (t * y * t) * t := by rw [h1]
        _ = (g : H)⁻¹ * t * y * (t * t) := by group
        _ = (g : H)⁻¹ * t * y := by rw [htt, mul_one]
    rw [hLC, mem_bot] at hgt
    have : t = g := (inv_mul_eq_one.mp hgt).symm
    exact htL (this ▸ g.2)
  have hfix : ∀ E : Subgroup (CFSG.layer H), (∀ x ∈ E, α x = x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E < (2 ^ n) ^ 2 := by
    intro E hEα hE2
    have hE' : E.map (CFSG.layer H).subtype ≤ centralizer ({t} : Set H) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : t⁻¹ * (x : H) * t = x := by rw [← hα, hEα x hx]
      rw [mem_centralizer_singleton_iff]
      change (x : H) * t = t * x
      calc (x : H) * t = t * (t⁻¹ * x * t) := by group
        _ = t * x := by rw [h1]
    have hE2' : ∀ y ∈ E.map (CFSG.layer H).subtype, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hE2 x hx)
    have h1 := h.card_lt_of_le_centralizer hE' (isElementaryAbelian_of_mul_self hE2')
    rwa [card_map_of_injective (CFSG.layer H).subtype_injective] at h1
  have hW : ∃ W : Subgroup (CFSG.layer H), (∀ x ∈ W, x * x = 1) ∧
      (2 ^ n) ^ 2 ≤ Nat.card W := by
    refine ⟨V.subgroupOf (CFSG.layer H), fun x hx => Subtype.ext
      (h.V_mul_self _ (mem_subgroupOf.mp hx)), ?_⟩
    rw [← h.card_V]
    exact (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).ge
  obtain ⟨f, hf3, ⟨e⟩⟩ := exists_psl2_of_goldschmidtSimpleType_of_outer hX h16 α hαα hαout hfix hW
  have hSyl : IsSylowOf 2 ((S : Subgroup H) ⊓ CFSG.layer H) (CFSG.layer H) := by
    have h0 : IsSylowOf 2 (S : Subgroup H) ⊤ :=
      isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
    exact h0.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr inferInstance])
  obtain ⟨Q, hQ⟩ := hSyl
  obtain ⟨hQcard, hQ2⟩ := sylow_facts_of_psl2 (by omega) e Q
  have hVeq : V = (S : Subgroup H) ⊓ CFSG.layer H := by
    refine le_antisymm (le_inf hVS hVL) ?_
    rw [← hQ]
    rintro _ ⟨x, hx, rfl⟩
    have hxS : (x : H) ∈ (S : Subgroup H) ⊓ CFSG.layer H := by
      rw [← hQ]
      exact mem_map_of_mem _ hx
    exact hmemV x (mem_inf.mp hxS).1 (hLV ▸ x.2) (congrArg Subtype.val (hQ2 x hx))
  have hcardV : Nat.card V = 2 ^ f := by
    rw [hVeq, ← hQ, card_map_of_injective (CFSG.layer H).subtype_injective, hQcard]
  have hf : f = 2 * n := by
    rw [h.card_V, ← pow_mul] at hcardV
    have := Nat.pow_right_injective le_rfl hcardV
    omega
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let ψ₀ : CFSG.layer H ≃* SL(2, GaloisField 2 f) := e.trans CFSG.CGT.Timmesfeld75.pslMulEquivSL
  obtain ⟨e', hfe', ψ, hψ⟩ := exists_frobenius_normal_form (by omega) hF ψ₀ α hαα hαout
  have hen : e' = n := by omega
  subst hen
  let Fα : Subgroup (CFSG.layer H) := (centralizer ({t} : Set H)).subgroupOf (CFSG.layer H)
  have hFα : ∀ x : CFSG.layer H, x ∈ Fα ↔ α x = x := by
    intro x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      rw [hα]
      calc t⁻¹ * (x : H) * t = t⁻¹ * (t * x) := by rw [mul_assoc, hx]
        _ = x := by group
    · intro hx
      have h1 : t⁻¹ * (x : H) * t = x := by rw [← hα, hx]
      calc (x : H) * t = t * (t⁻¹ * x * t) := by group
        _ = t * x := by rw [h1]
  have hX' : ∀ g ∈ Fα.map ψ.toMonoidHom, ∀ i j,
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) i j ^ 2 ^ e' =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) i j := by
    rintro _ ⟨x, hx, rfl⟩ i j
    have h1 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) => m i j) (hψ x)
    simp only [Matrix.map_apply] at h1
    rw [(hFα x).mp hx] at h1
    exact h1.symm
  obtain ⟨k, hkF, hkFin, hk, ⟨αA⟩⟩ := h.app.2.2.1.2.2
  have hcardX : Nat.card (Fα.map ψ.toMonoidHom) ≤ Nat.card SL(2, k) :=
    card_le_of_frobenius_fixed (k := k) (by omega) (by rw [hF, hf]) (by
      rw [Nat.card_eq_fintype_card, hk]) _ hX'
  have hP : (A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom = Fα.map ψ.toMonoidHom := by
    apply eq_of_le_of_card_ge
    · exact map_mono fun x hx => mem_subgroupOf.mpr (h.le_centralizer (mem_subgroupOf.mp hx))
    · calc Nat.card (Fα.map ψ.toMonoidHom) ≤ Nat.card SL(2, k) := hcardX
        _ = Nat.card A := (Nat.card_congr αA.toEquiv).symm
        _ = Nat.card (A.subgroupOf (CFSG.layer H)) :=
          (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).symm
        _ = Nat.card ((A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom) :=
          (card_map_of_injective ψ.injective).symm
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, ?_, ψ, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hF, hf]
    ring
  · intro x y hyx
    have hy : y = α x := Subtype.ext (by rw [hα]; exact hyx)
    rw [hy]
    exact hψ x
  · intro g
    rw [hP]
    constructor
    · exact hX' g
    · intro hg
      refine ⟨ψ.symm g, (hFα _).mpr (ψ.injective ?_), ψ.apply_symm_apply g⟩
      apply Subtype.ext
      rw [hψ, ψ.apply_symm_apply]
      ext i j
      exact hg i j

section Main


theorem layer_selection_of_stronglyClosed (h : LocalSetting A t U V D n) (S : Sylow 2 H)
    (hVS : V ≤ S)
    (hclosed : ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ (S : Subgroup H) → g⁻¹ * v * g ∈ V) :
    centralizer (CFSG.layer H : Set H) = ⊥ ∧ A ≤ CFSG.layer H ∧
      CFSG.layer H = normalClosure (A : Set H) ∧ V ≤ CFSG.layer H ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
          ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
            ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
          ∃ ψ : CFSG.layer H ≃* SL(2, k₂),
            (∀ x y : CFSG.layer H, (y : H) = t⁻¹ * x * t →
              ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
            ∀ g : SL(2, k₂), g ∈ (A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  obtain ⟨hE, hmemV, htype⟩ := h.goldschmidt_normalClosure S hVS hclosed
  have hLV := h.layer_eq_normalClosure hE
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (CFSG.layer H ≃* SL(2, k) × SL(2, k)) → (CFSG.layer H ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (isEmpty_mulEquiv_sl2_prod (k := k) (by have := h.two_le; omega) hk₂').false
      (ψ₂.symm.trans ψ₁)
  refine ⟨hLV ▸ h.centralizer_normalClosure_eq_bot, h.A_le_layer hE,
    hLV.trans (h.normalClosure_A_eq hE htype).symm,
    hLV ▸ (le_normalClosure : V ≤ normalClosure (V : Set H)), ?_⟩
  rcases h.layer_dichotomy hE htype with ⟨K, hK, hLK⟩ | h1
  · have h2 := h.alternative_two S hVS hE htype hmemV hK hLK
    refine Or.inr ⟨h2, ?_⟩
    rintro ⟨k, _, _, -, ψ₁, -⟩
    obtain ⟨k₂, _, _, hk₂, ψ₂, -⟩ := h2
    exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ₁ ψ₂
  · refine Or.inl ⟨h1, ?_⟩
    rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
    obtain ⟨k, _, _, -, ψ₁, -⟩ := h1
    exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ₁ ψ₂

end Main

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
