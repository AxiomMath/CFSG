module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenAbs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLThreeArith

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

namespace OLThreeAdic

open CFSG.Open (StatedScalars StatedProj pCoreOf)

section Card

variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U] [Module.Finite F U]

noncomputable def linearEquivEquivGL :
    (U ≃ₗ[F] U) ≃ GL (Fin (Module.finrank F U)) F :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm.trans
    (Matrix.GeneralLinearGroup.toLin' (Module.finBasis F U)).symm).toEquiv

theorem natCard_linearEquiv [Finite F] :
    Nat.card (U ≃ₗ[F] U) =
      ∏ i : Fin (Module.finrank F U), (Nat.card F ^ Module.finrank F U - Nat.card F ^ (i : ℕ)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (linearEquivEquivGL (F := F) (U := U)), Matrix.card_GL_field,
    Nat.card_eq_fintype_card (α := F)]

theorem natCard_linearEquiv_ne_zero [Finite F] : Nat.card (U ≃ₗ[F] U) ≠ 0 := by
  classical
  rw [Nat.card_congr (linearEquivEquivGL (F := F) (U := U))]
  exact Nat.card_pos.ne'

end Card

section Restriction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

noncomputable def resSub (Q : Subgroup (V ≃ₗ[F] V)) (W : Submodule F V)
    (h : ∀ g ∈ Q, W.map (g : V →ₗ[F] V) = W) : Q →* (W ≃ₗ[F] W) where
  toFun g := LinearEquiv.ofSubmodules (g : V ≃ₗ[F] V) W W (h g g.2)
  map_one' := by ext; rfl
  map_mul' g g' := by ext; rfl

noncomputable def resQuot (Q : Subgroup (V ≃ₗ[F] V)) (W : Submodule F V)
    (h : ∀ g ∈ Q, W.map (g : V →ₗ[F] V) = W) : Q →* ((V ⧸ W) ≃ₗ[F] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (g : V ≃ₗ[F] V) (h g g.2)
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rfl
  map_mul' g g' := by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rfl

theorem add_self_eq_zero_of_charTwo [CharP F 2] (x : V) : x + x = 0 := by
  rw [← two_smul F x, (CharTwo.two_eq_zero : (2 : F) = 0), zero_smul]

theorem resHom_injective [CharP F 2] {Q : Subgroup (V ≃ₗ[F] V)} (hQ : IsPGroup 3 Q)
    (W : Submodule F V) (h : ∀ g ∈ Q, W.map (g : V →ₗ[F] V) = W) :
    Function.Injective ((resSub Q W h).prod (resQuot Q W h)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg1 : resSub Q W h g = 1 := (Prod.mk.inj hg).1
  have hg2 : resQuot Q W h g = 1 := (Prod.mk.inj hg).2
  have hW : ∀ w ∈ W, (g : V ≃ₗ[F] V) w = w := fun w hw => by
    have := congrArg (fun φ : W ≃ₗ[F] W => (φ ⟨w, hw⟩ : V)) hg1
    simpa [resSub] using this
  have hQW : ∀ v : V, (g : V ≃ₗ[F] V) v - v ∈ W := fun v => by
    have := congrArg (fun φ : (V ⧸ W) ≃ₗ[F] (V ⧸ W) => φ (Submodule.Quotient.mk v)) hg2
    have h' : Submodule.Quotient.mk ((g : V ≃ₗ[F] V) v) = (Submodule.Quotient.mk v : V ⧸ W) := by
      simpa [resQuot] using this
    exact (Submodule.Quotient.eq W).mp h'
  have hsq : (g : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have h1 := hW _ (hQW v)
    rw [map_sub] at h1
    have h2 := add_self_eq_zero_of_charTwo (F := F) (V := V) ((g : V ≃ₗ[F] V) v)
    have h3 := add_self_eq_zero_of_charTwo (F := F) (V := V) v
    show (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) v) = v
    have h4 : (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) v) =
        (g : V ≃ₗ[F] V) v + ((g : V ≃ₗ[F] V) v - v) := by
      rw [← h1]
      abel
    rw [h4]
    have h5 : (g : V ≃ₗ[F] V) v + ((g : V ≃ₗ[F] V) v - v) =
        ((g : V ≃ₗ[F] V) v + (g : V ≃ₗ[F] V) v) - v := by abel
    rw [h5, h2, zero_sub, neg_eq_iff_add_eq_zero]
    exact h3
  have hgg : g * g = 1 := Subtype.ext hsq
  obtain ⟨k, hk⟩ := hQ g
  have hd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  have hd3 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf g = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd2 hd3
  exact orderOf_eq_one_iff.mp h1

end Restriction

section Bound

variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [Module.Finite F V]

theorem padicValNat_card_le_of_invariant {p : ℕ} (hq : Nat.card F = 2 ^ p)
    (hp : p % 6 = 1 ∨ p % 6 = 5) (hV : Module.finrank F V = 6) (Q : Subgroup (V ≃ₗ[F] V))
    (hQ : IsPGroup 3 Q) (W : Submodule F V) (hW : ∀ g ∈ Q, ∀ v ∈ W, g v ∈ W) (hW0 : W ≠ ⊥)
    (hW1 : W ≠ ⊤) : padicValNat 3 (Nat.card Q) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmap : ∀ g ∈ Q, W.map (g : V →ₗ[F] V) = W := fun g hg => by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hW g hg v hv
    · intro w hw
      refine ⟨(g⁻¹ : V ≃ₗ[F] V) w, hW g⁻¹ (Q.inv_mem hg) w hw, ?_⟩
      exact (g : V ≃ₗ[F] V).apply_symm_apply w
  have hinj := resHom_injective hQ W hmap
  have hdvd : Nat.card Q ∣
      Nat.card (W ≃ₗ[F] W) * Nat.card ((V ⧸ W) ≃ₗ[F] (V ⧸ W)) := by
    rw [← Nat.card_prod]
    exact Subgroup.card_dvd_of_injective _ hinj
  have ha1 : 1 ≤ Module.finrank F W := by
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    exact Module.finrank_pos
  have ha5 : Module.finrank F W ≤ 5 := by
    have := Submodule.finrank_lt hW1
    omega
  have hb : Module.finrank F (V ⧸ W) + Module.finrank F W = 6 := by
    rw [Submodule.finrank_quotient_add_finrank, hV]
  have hA0 := natCard_linearEquiv_ne_zero (F := F) (U := W)
  have hB0 := natCard_linearEquiv_ne_zero (F := F) (U := V ⧸ W)
  have hA : padicValNat 3 (Nat.card (W ≃ₗ[F] W)) = Module.finrank F W / 2 := by
    rw [natCard_linearEquiv, hq]
    exact padicValNat_three_prod_gl hp ha5
  have hB : padicValNat 3 (Nat.card ((V ⧸ W) ≃ₗ[F] (V ⧸ W))) = Module.finrank F (V ⧸ W) / 2 := by
    rw [natCard_linearEquiv, hq]
    exact padicValNat_three_prod_gl hp (by omega)
  have hle := padicValNat_le_of_dvd' Nat.prime_three (mul_ne_zero hA0 hB0) hdvd
  rw [padicValNat.mul hA0 hB0, hA, hB] at hle
  omega

end Bound

def fixedSpace {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (R : Subgroup (V ≃ₗ[F] V)) : Submodule F V where
  carrier := {w | ∀ x ∈ R, x w = w}
  add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
  zero_mem' := fun x _ => map_zero x
  smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx]

theorem exists_two_subgroup_normalized {G : Type*} [Group G] [Finite G] (Z : Subgroup G)
    [Z.Normal] (hZc : Z ≤ Subgroup.center G) (R : Subgroup (G ⧸ Z)) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) :
    ∃ R' : Subgroup G, IsPGroup 2 R' ∧ R' ≠ ⊥ ∧
      (Subgroup.normalizer (R : Set (G ⧸ Z))).comap (QuotientGroup.mk' Z) ≤
        Subgroup.normalizer (R' : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rt : Subgroup G := R.comap (QuotientGroup.mk' Z) with hRt
  refine ⟨pCoreOf 2 Rt, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Rt,
    exists_two_subgroup_preimage Z hZc R hR2 hR1, fun g hg => ?_⟩
  have hgN : g ∈ Subgroup.normalizer (Rt : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.mp (Subgroup.mem_comap.mp hg) (x : G ⧸ Z)
    have e : ((g * x * g⁻¹ : G) : G ⧸ Z) = (g : G ⧸ Z) * (x : G ⧸ Z) * (g : G ⧸ Z)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    show (x : G ⧸ Z) ∈ R ↔ ((g * x * g⁻¹ : G) : G ⧸ Z) ∈ R
    rw [e]
    exact h
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Rt hgN

theorem padicValNat_three_card_normalizer_le {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] [CharP F 2] (hι : Fintype.card ι = 6) {p : ℕ}
    (hq : Nat.card F = 2 ^ p) (hp : p % 6 = 1 ∨ p % 6 = 5) (H : Subgroup (GL ι F))
    (R : Subgroup (StatedProj H)) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    padicValNat 3 (Nat.card (Subgroup.normalizer (R : Set (StatedProj H)))) ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hZc, -⟩ := scalars_subgroupOf_facts ι F H
  obtain ⟨R', hR'2, hR'1, hRN⟩ := exists_two_subgroup_normalized
    ((StatedScalars ι F).subgroupOf H) hZc R hR2 hR1
  set N : Subgroup (StatedProj H) := Subgroup.normalizer (R : Set (StatedProj H)) with hN
  set Ñ : Subgroup H := N.comap (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) with hÑ
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 Ñ))
  let ρ : ↥H →* ((ι → F) ≃ₗ[F] (ι → F)) := (natAction ι F).comp H.subtype
  have hρ : Function.Injective ρ := (natAction_injective ι F).comp H.subtype_injective
  let θ : ↥Ñ →* ((ι → F) ≃ₗ[F] (ι → F)) := ρ.comp Ñ.subtype
  have hθ : Function.Injective θ := hρ.comp Ñ.subtype_injective
  let Q : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := (P : Subgroup Ñ).map θ
  have hQ : IsPGroup 3 Q := P.isPGroup'.map θ
  let W : Submodule F (ι → F) := fixedSpace (R'.map ρ)
  have hWmem : ∀ w : ι → F, w ∈ W ↔ ∀ y ∈ R', ρ y w = w := fun w => by
    constructor
    · intro hw y hy
      exact hw (ρ y) ⟨y, hy, rfl⟩
    · rintro hw _ ⟨y, hy, rfl⟩
      exact hw y hy
  have hWQ : ∀ g ∈ Q, ∀ v ∈ W, g v ∈ W := by
    intro g hg v hv
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.mp hg
    rw [hWmem] at hv ⊢
    intro y hy
    have hconj : (n : ↥H)⁻¹ * y * n ∈ R' := by
      have := (Subgroup.mem_normalizer_iff.mp (hRN n.2) ((n : ↥H)⁻¹ * y * n)).mpr
      refine this ?_
      have e : (n : ↥H) * ((n : ↥H)⁻¹ * y * n) * (n : ↥H)⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 := hv _ hconj
    have key : ρ y * ρ n = ρ n * ρ ((n : ↥H)⁻¹ * y * n) := by
      rw [map_mul, map_mul, map_inv]
      group
    have h2 := congrArg (fun φ : (ι → F) ≃ₗ[F] (ι → F) => φ v) key
    simp only [LinearEquiv.mul_apply] at h2
    show ρ y (ρ n v) = ρ n v
    rw [h2, h1]
  have hW0 : W ≠ ⊥ := by
    haveI : Nontrivial (ι → F) := inferInstance
    obtain ⟨v, hv0, hv⟩ := exists_ne_zero_fixed (R'.map ρ) (hR'2.map ρ)
    intro hbot
    have : v ∈ W := fun x hx => hv x hx
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  have hW1 : W ≠ ⊤ := by
    intro htop
    apply hR'1
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply hρ
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    exact (hWmem v).mp hv x hx
  have hV : Module.finrank F (ι → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  have hbound := padicValNat_card_le_of_invariant hq hp hV Q hQ W hWQ hW0 hW1
  have hQcard : Nat.card Q = Nat.card (P : Subgroup Ñ) := Subgroup.card_map_of_injective hθ
  have hPcard : Nat.card (P : Subgroup Ñ) = 3 ^ (Nat.card Ñ).factorization 3 :=
    Sylow.card_eq_multiplicity P
  rw [hQcard, hPcard, padicValNat.prime_pow] at hbound
  have hÑ3 : padicValNat 3 (Nat.card Ñ) ≤ 3 := by
    rwa [← Nat.factorization_def _ Nat.prime_three]
  have hdvd : Nat.card N ∣ Nat.card Ñ := by
    have := Subgroup.card_map_dvd (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H))
      (H := Ñ)
    rwa [hÑ, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _) N] at this
  exact (padicValNat_le_of_dvd' Nat.prime_three Nat.card_pos.ne' hdvd).trans hÑ3

theorem padicValNat_three_card_normalizer_le_of_equiv {K : Type} [Group K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2]
    (hι : Fintype.card ι = 6) {p : ℕ} (hq : Nat.card F = 2 ^ p) (hp : p % 6 = 1 ∨ p % 6 = 5)
    {H : Subgroup (GL ι F)} (e : K ≃* StatedProj H) (R : Subgroup K) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) : padicValNat 3 (Nat.card (Subgroup.normalizer (R : Set K))) ≤ 3 := by
  have h := padicValNat_three_card_normalizer_le hι hq hp H (R.map e.toMonoidHom)
    (hR2.map e.toMonoidHom)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h))
  exact (padicValNat_le_of_dvd' Nat.prime_three Nat.card_pos.ne'
    (card_normalizer_dvd_of_mulEquiv e R)).trans h

end OLThreeAdic

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
