module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Input
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActPSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Image
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ThreeModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConcB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.Yardstones.Md0ec50421ce4 (PSimple)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


section Conj

variable {G : Type*} [Group G]

private theorem map_conj_eq_of_normal {I : Subgroup G} (hI : I.Normal) (a : G) :
    I.map (MulAut.conj a).toMonoidHom = I := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hI.conj_mem y hy a
  · intro hx
    refine ⟨a⁻¹ * x * a⁻¹⁻¹, hI.conj_mem x hx a⁻¹, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_eq_self_of_mapsTo [Finite G] {J : Subgroup G} {α : MulAut G}
    (h : ∀ j ∈ J, α j ∈ J) : J.map α.toMonoidHom = J :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨j, hj, rfl⟩; exact h j hj)
    (by rw [Subgroup.card_map_of_injective α.injective])

end Conj

theorem twE6JCompInput_holds : TwE6JCompInput := by
  intro K _ _ ℓ f _ _ hK hf hℓ2 h3 c hc hct
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ, hσζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 6
  exact (TwE6Conc.modelAGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 (by norm_num) hc hct
    (by norm_num : 0 < 4) (TwE6Outer.leviSU_comp_diagThreeHom_injective c hc h3)).2.2.2.2.1

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

section Levi

variable (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) {ζ : K} (hζ : ζ ≠ 0)
  (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
  (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

include hK hf hζ hσζ hP in
private theorem map_leviJ_fieldActor {δ : K ≃+* K} (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j) :
    ((TwE6Conc.leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))).map
        (fieldActor (unitaryInvolution K ℓ f) δ).toMonoidHom =
      (TwE6Conc.leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  refine map_eq_self_of_mapsTo fun x hx => ?_
  obtain ⟨y, rfl⟩ := TwE6Conc.exists_leviSU_eq hK hf hζ hσζ P hP hx
  rw [TwE6Outer.entrywise_leviSU hK hf hζ hσζ P hP hδζ hPδ]
  exact TwE6Conc.leviSU_mem_leviJ hK hf hζ hσζ P hP _

include hK hf hζ hσζ hP in
private theorem pow_eq_one_of_fix_leviJ {ε : K ≃+* K} (hε : orderOf ε = 3) (hεζ : ε ζ = ζ)
    (hεP : ∀ i j, ε ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    {v : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hv : ∀ s : Su K ℓ f 6, ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag →
      v (TwE6Conc.leviSU hK hf hζ hσζ P hP s) = TwE6Conc.leviSU hK hf hζ hσζ P hP s)
    {n : ℕ} (hfix : ∀ j ∈ (TwE6Conc.leviJ K ℓ f).subgroupOf
      (twistedE6RootGroup K (unitaryInvolution K ℓ f)),
      (v * fieldActor (unitaryInvolution K ℓ f) ε ^ n :
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) j = j) :
    ε ^ n = 1 := by
  have hQ2 : 2 ≤ ℓ ^ f := (Fact.out : ℓ.Prime).two_le.trans (Nat.le_self_pow (by omega) ℓ)
  refine TwE6Outer.eq_one_of_forall_fixed hK hQ2 Nat.prime_three ?_ fun u hu => ?_
  · rw [← pow_mul, mul_comm, pow_mul, ← hε, pow_orderOf_eq_one, one_pow]
  set u' := Units.map (ε ^ n).toRingHom.toMonoidHom u with hu'def
  have hu' : u' ^ (ℓ ^ f + 1) = 1 := TwE6Outer.map_pow_eq_one hu
  have h1 := hfix (TwE6Conc.leviSU hK hf hζ hσζ P hP (TwE6Outer.yLam hK u hu))
    (TwE6Conc.leviSU_mem_leviJ hK hf hζ hσζ P hP _)
  rw [MulAut.mul_apply, TwE6Outer.fieldActor_pow,
    TwE6Outer.entrywise_leviSU hK hf hζ hσζ P hP (TwE6Outer.ringEquiv_pow_apply_eq hεζ n)
      (fun i j => TwE6Outer.ringEquiv_pow_apply_eq (hεP i j) n),
    TwE6Outer.suidMap_yLam hK u hu hu',
    hv (TwE6Outer.yLam hK u' hu') (by rw [TwE6Outer.coe_yLam]; exact Matrix.isDiag_diagonal _)]
    at h1
  have h4 : TwE6Conc.leviSU hK hf hζ hσζ P hP
      (TwE6Outer.yLam hK u' hu' * (TwE6Outer.yLam hK u hu)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := TwE6Conc.exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h4
  rw [TwE6Outer.coe_yLam_mul_inv] at hμ
  have e44 := congrFun (congrFun hμ 4) 4
  have e00 := congrFun (congrFun hμ 0) 0
  simp [TwE6Outer.yTuple] at e44 e00
  rw [← e44] at e00
  have h5 : (u' : K) = u := by
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    field_simp at e00
    exact e00
  rw [hu'def, Units.coe_map] at h5
  exact h5

end Levi

private theorem concA_of_actData_conj (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) {X : Type} [Group X] [Finite X]
    (e : PSimple 3 S ≃* X) {Γ : Ω →* MulAut X}
    (hΓe : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
      e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)) (ψ : MulAut X)
    (hW : ModelGen.ActData 3 B (fun x => ((MulAut.conj ψ).toMonoidHom.comp Γ) x)) :
    S267ConcA 3 S B := by
  refine ModelGen.concA_of_actData_pSimple Nat.prime_three (by norm_num) hS hperf hcore hB hBC
    (e.trans ψ) _ (fun x g => ?_) hW
  show ψ (e (chevQuotHom 3 S ⟨(x : Ω) * g * (x : Ω)⁻¹, hS.conj_mem _ g.2 _⟩)) =
    (ψ * Γ x * ψ⁻¹) (ψ (e (chevQuotHom 3 S g)))
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hΓe]

private theorem exists_conj_eq_of_commute_twInndiag (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (h3 : ¬ 3 ∣ ℓ ^ f) {ε₀ : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    {X Y : Subgroup (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))}
    (hIn : (twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f)).Normal)
    (hXI : X ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f))
    (hYI : Y ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f))
    (hX : IsElemAbelian 3 X) (hY : IsElemAbelian 3 Y) (hXc : Nat.card X = 3 ^ 6)
    (hYc : Nat.card Y = 3 ^ 6) (hXε : ∀ x ∈ X, x * ε₀ = ε₀ * x)
    (hYε : ∀ y ∈ Y, y * ε₀ = ε₀ * y) :
    ∃ h : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)), h * ε₀ = ε₀ * h ∧
      Y.map (MulAut.conj h).toMonoidHom = X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  haveI : Finite (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
    Finite.of_injective (fun φ : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) =>
      (φ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →
        ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))) fun a b h => MulEquiv.ext (congrFun h)
  set H : Subgroup (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
    Subgroup.centralizer {ε₀} with hH
  have hXH : X ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hXε x hx)
  have hYH : Y ≤ H := fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hYε y hy)
  have hX'c : Nat.card (X.subgroupOf H) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hY'c : Nat.card (Y.subgroupOf H) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv, hYc]
  obtain ⟨P, hXP⟩ := (IsPGroup.of_card hX'c).exists_le_sylow
  obtain ⟨P', hYP'⟩ := (IsPGroup.of_card hY'c).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H P' P
  set Q := (P : Subgroup ↥H).map H.subtype with hQ
  have hQp : IsPGroup 3 Q := P.isPGroup'.map H.subtype
  have hXQ : X ≤ Q := fun x hx => ⟨⟨x, hXH hx⟩, hXP hx, rfl⟩
  have hYQ : Y.map (MulAut.conj (g : MulAut _)).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conj g ⟨y, hYH hy⟩, ?_, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hYP' hy)
  have hYI' : Y.map (MulAut.conj (g : MulAut _)).toMonoidHom ≤
      twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hIn.conj_mem y (hYI hy) g
  have hYe' : IsElemAbelian 3 (Y.map (MulAut.conj (g : MulAut _)).toMonoidHom) :=
    CFSG.StandardType.TableB.isElemAbelian_map hY _
  have hYc' : Nat.card (Y.map (MulAut.conj (g : MulAut _)).toMonoidHom) = 3 ^ 6 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hYc]
  refine ⟨g, (Subgroup.mem_centralizer_singleton_iff.1 g.2), ?_⟩
  exact (eq_of_le_of_isPGroup_twInndiag Fact.out hf hK _ (unitaryInvolution_apply K ℓ f) h3 hQp hXI
    hYI' hXQ hYQ hX hYe' hXc hYc').symm

theorem concA_of_twE6_vtw_outer (hVtw : TwE6VtwInput) (hJc : TwE6JCompInput)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    (hB4 : 3 ^ 4 ≤ Nat.card B)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hΓe : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
      e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩))
    (hΓker : Γ.ker = centModSubgroup 3 S) {b : Ω} (hb : b ∈ B)
    (hbI : Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f))
    (h6 : 3 ^ 6 ≤ Nat.card ↥(B.map Γ ⊓ (twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f)))) :
    S267ConcA 3 S B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓ : ℓ.Prime := Fact.out
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, -, hZ0, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK
      (unitaryInvolution K ℓ f) (unitaryInvolution_apply K ℓ f)
  have hIΘ : ∀ α, α ∈ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f) ↔ Θ α = 1 := fun α => by
    rw [← hker, MonoidHom.mem_ker]
  have hβ3 : Γ b ^ 3 = 1 := by rw [← map_pow, hB.2 b hb, map_one]
  have hε1 : Θ (Γ b) ≠ 1 := fun h => hbI ((hIΘ _).2 h)
  have hε : orderOf (Θ (Γ b)) = 3 := orderOf_eq_prime (by rw [← map_pow, hβ3, map_one]) hε1
  obtain ⟨d, rfl⟩ := TwE6Outer.exists_eq_mul_of_orderOf hK Nat.prime_three (by norm_num) hε
  have hK' : Nat.card K = ℓ ^ (2 * (3 * d)) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, ψ₁, -, hψ₁⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order hℓ hf K hK'
      (unitaryInvolution K ℓ (3 * d)) (unitaryInvolution_apply K ℓ (3 * d)) Θ hΘ Nat.prime_three
      (by norm_num) (Γ b) hβ3 hε1
  set ε := Θ (Γ b) with hεdef
  set ε₀ := fieldActor (unitaryInvolution K ℓ (3 * d)) ε with hε₀def
  have hΘε₀ : Θ ε₀ = ε := hΘ ε₀ 1 1 ε (by rw [map_one, map_one, one_mul, one_mul])
  have hQ1 : 1 ≤ ℓ ^ (3 * d) := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨ζ, hζ, hσζ, hεζ⟩ :=
    TwE6Outer.exists_unitaryInvolution_eq_neg_fixed Nat.prime_three (by norm_num) hK hε
  obtain ⟨P, hP, hεP⟩ := TwE6Outer.exists_wittMatrix_fixed Nat.prime_three (by norm_num) hK hε 6
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact TwE6Outer.three_dvd_sq_sub_one_of_dvd_add_one hQ1 h3
  obtain ⟨c, hc, hεc⟩ := exists_orderOf_eq_fixSubfield Nat.prime_three hε h3K
  have hcs := TwE6Outer.add_inv_eq_neg_one_of_orderOf_three hc
  have hct : unitaryInvolution K ℓ (3 * d) ((c : K) + ((c⁻¹ : Kˣ) : K)) =
      (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [hcs, map_neg, map_one]
  obtain ⟨V, hVI, hVe, hVc, hr₀V, -, hVJ, hVk, ⟨v₁, hv₁V, hv₁r, hv₁L⟩, hVδ, hVdiag⟩ :=
    hVtw hK hf hℓ2 h3 hζ hσζ P hP hc hct
  have hVε : ∀ v ∈ V, v * ε₀ = ε₀ * v := fun v hv => (hVδ ε hεζ hεc hεP v hv).symm
  have hIn : (twistedE6Inn K (unitaryInvolution K ℓ (3 * d)) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ (3 * d))).Normal := by
    rw [← hker]
    infer_instance
  have h3' : ¬ 3 ∣ ℓ ^ (3 * d) := fun h => by
    have := (Nat.dvd_add_right h).1 h3
    norm_num at this
  set Γ₁ := (MulAut.conj ψ₁).toMonoidHom.comp Γ with hΓ₁def
  have hΓ₁b : Γ₁ b = ε₀ := hψ₁
  set W := B.map Γ₁ ⊓ (twistedE6Inn K (unitaryInvolution K ℓ (3 * d)) ⊔
    twistedE6Diag K (unitaryInvolution K ℓ (3 * d))) with hWdef
  have hWeq : (B.map Γ ⊓ (twistedE6Inn K (unitaryInvolution K ℓ (3 * d)) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ (3 * d)))).map (MulAut.conj ψ₁).toMonoidHom = W := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj ψ₁).injective, map_conj_eq_of_normal hIn,
      Subgroup.map_map]
  have hWe : IsElemAbelian 3 W :=
    CFSG.Open.IsElemAbelian.mono (CFSG.StandardType.TableB.isElemAbelian_map hB Γ₁) inf_le_left
  have hWc : Nat.card W = 3 ^ 6 := by
    refine le_antisymm (card_le_of_le_twInndiag hℓ hf hK _ (unitaryInvolution_apply K ℓ (3 * d)) h3'
      hWe inf_le_right) ?_
    rw [← hWeq, Subgroup.card_map_of_injective (MulAut.conj ψ₁).injective]
    exact h6
  have hWε : ∀ w ∈ W, w * ε₀ = ε₀ * w := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    have hxb : x * b = b * x := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨b, hb⟩)
    rw [← hΓ₁b, ← map_mul, ← map_mul, hxb]
  obtain ⟨h, hhε, hhW⟩ := exists_conj_eq_of_commute_twInndiag hK hf h3' hIn hVI inf_le_right hVe hWe
    hVc hWc hVε hWε
  set ψ := h * ψ₁ with hψdef
  set Γ' := (MulAut.conj ψ).toMonoidHom.comp Γ with hΓ'def
  have hΓ'eq : Γ' = (MulAut.conj h).toMonoidHom.comp Γ₁ := MonoidHom.ext fun x => by
    show (h * ψ₁) * Γ x * (h * ψ₁)⁻¹ = h * (ψ₁ * Γ x * ψ₁⁻¹) * h⁻¹
    group
  have hΓ'b : Γ' b = ε₀ := by
    rw [hΓ'eq, MonoidHom.comp_apply, hΓ₁b]
    show h * ε₀ * h⁻¹ = ε₀
    rw [hhε, mul_inv_cancel_right]
  have hVeq : B.map Γ' ⊓ (twistedE6Inn K (unitaryInvolution K ℓ (3 * d)) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ (3 * d))) = V := by
    rw [hΓ'eq, ← Subgroup.map_map, ← map_conj_eq_of_normal hIn h,
      ← Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective]
    exact hhW
  have hVB : V ≤ B.map Γ' := by
    rw [← hVeq]
    exact inf_le_left
  have hε₀B : ε₀ ∈ B.map Γ' := ⟨b, hb, hΓ'b⟩
  have hdecomp : ∀ x ∈ B, ∃ v ∈ V, ∃ n : ℕ, Γ' x = v * ε₀ ^ n := by
    intro x hx
    have hx3 : Θ (Γ' x) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hB.2 x hx, map_one, map_one]
    have hεfin : IsOfFinOrder ε :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, by rw [← hε, pow_orderOf_eq_one]⟩
    have hmem : Θ (Γ' x) ∈ Subgroup.zpowers ε := by
      haveI : IsCyclic (RingAut K) :=
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
      haveI : Finite ↥(Subgroup.zpowers (Θ (Γ' x))) :=
        (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx3⟩).finite_zpowers
      have hle : Subgroup.zpowers (Θ (Γ' x)) ≤ Subgroup.zpowers ε := by
        rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hε]
        exact orderOf_dvd_of_pow_eq_one hx3
      exact hle (Subgroup.mem_zpowers _)
    obtain ⟨n, -, hn⟩ := Finset.mem_image.1 (hεfin.mem_zpowers_iff_mem_range_orderOf.1 hmem)
    have hn' : ε ^ n = Θ (Γ' x) := hn
    refine ⟨Γ' x * (ε₀ ^ n)⁻¹, ?_, n, by group⟩
    rw [← hVeq]
    refine Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ ⟨x, hx, rfl⟩ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hε₀B n)), ?_⟩
    rw [hIΘ, map_mul, map_inv, map_pow, hΘε₀, ← hn', mul_inv_cancel]
  have hpJ : 3 ∣ Nat.card ↥((TwE6Conc.leviJ K ℓ (3 * d)).subgroupOf
      (twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d)))) := by
    have hinj := TwE6Outer.leviSU_comp_diagThreeHom_injective (hK := hK) (hf := hf) (hζ := hζ)
      (hσζ := hσζ) (P := P) (hP := hP) c hc h3
    set y := TwE6Outer.diagThreeHom c hc h3 TwE6Outer.diagGen4 with hy
    have hy1 : TwE6Conc.leviSU hK hf hζ hσζ P hP y ≠ 1 := fun h1 =>
      TwE6Outer.diagGen4_ne_one (hinj (h1.trans (map_one _).symm))
    have hmem : TwE6Conc.leviSU hK hf hζ hσζ P hP y ∈ (TwE6Conc.leviJ K ℓ (3 * d)).subgroupOf
        (twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d))) :=
      Subgroup.mem_subgroupOf.2 (TwE6Conc.leviSU_mem_leviJ hK hf hζ hσζ P hP y)
    have ho : orderOf (⟨TwE6Conc.leviSU hK hf hζ hσζ P hP y, hmem⟩ :
        ↥((TwE6Conc.leviJ K ℓ (3 * d)).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d))))) = 3 := by
      rw [Subgroup.orderOf_mk]
      refine orderOf_eq_prime ?_ hy1
      rw [hy, ← map_pow, ← map_pow, TwE6Conc.pow_eq_one_of_fin, map_one, map_one]
    have h1 := orderOf_dvd_natCard (⟨TwE6Conc.leviSU hK hf hζ hσζ P hP y, hmem⟩ :
        ↥((TwE6Conc.leviJ K ℓ (3 * d)).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d)))))
    rwa [ho] at h1
  set J := (TwE6Conc.leviJ K ℓ (3 * d)).subgroupOf
    (twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d))) with hJdef
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (TwE6Conc.twE6LeviSA_le_twistedE6RootGroup hK hf)).symm
      (TwE6Conc.isQuasisimple_twE6LeviSA hζ hσζ hK).1
  have hJcomp := hJc hK hf hℓ2 h3 hc hct
  have hr₀1 : TwE6Conc.twE6R0 c hct ≠ 1 := fun h1 => by
    have h2 := TwE6Conc.orderOf_twE6R0 Nat.prime_three (by norm_num) hc hct
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hd₁1 : MulAut.conj (TwE6Conc.twE6R0 c hct) ≠ 1 := fun h1 => by
    apply hr₀1
    have hcen : TwE6Conc.twE6R0 c hct ∈
        Subgroup.center ↥(twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d))) :=
      Subgroup.mem_center_iff.2 fun g => by
        have h2 := congrArg (fun φ : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d))) =>
          φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * TwE6Conc.twE6R0 c hct
            = TwE6Conc.twE6R0 c hct * g * (TwE6Conc.twE6R0 c hct)⁻¹ * TwE6Conc.twE6R0 c hct := by
              rw [h2]
          _ = TwE6Conc.twE6R0 c hct * g := by group
    rw [hZ0] at hcen
    exact Subgroup.mem_bot.1 hcen
  have hBker : Nat.card ↥(B ⊓ Γ'.ker) = 3 := by
    rw [hΓ'def, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj ψ).injective, hΓker]
    exact hBC
  have hJB : ∀ x ∈ B, J.map (Γ' x).toMonoidHom = J := by
    intro x hx
    obtain ⟨v, hv, n, hvn⟩ := hdecomp x hx
    rw [hvn]
    have hmap : J.map (v * ε₀ ^ n).toMonoidHom = (J.map (ε₀ ^ n).toMonoidHom).map v.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hmap, hε₀def, TwE6Outer.fieldActor_pow, map_leviJ_fieldActor hK hf hζ hσζ P hP
      (TwE6Outer.ringEquiv_pow_apply_eq hεζ n) (fun i j => TwE6Outer.ringEquiv_pow_apply_eq (hεP i j) n)]
    exact hVJ v hv
  have hJk : ∀ x ∈ B, (∀ j ∈ J, j * (Γ' x j)⁻¹ ∈ GLAPPrimeCoreOf 3 J) →
      Γ' x ∈ Subgroup.zpowers (MulAut.conj (TwE6Conc.twE6R0 c hct)) := by
    intro x hx hcore'
    obtain ⟨v, hv, n, hvn⟩ := hdecomp x hx
    have hfix : ∀ j ∈ J, (Γ' x).toMonoidHom j = j :=
      CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf Nat.prime_three hJq
        hpJ (Γ' x).toMonoidHom fun j hj => by
          have h1 := (GLAPPrimeCoreOf 3 J).inv_mem (hcore' j hj)
          rwa [mul_inv_rev, inv_inv] at h1
    have hεn : ε ^ n = 1 := pow_eq_one_of_fix_leviJ hK hf hζ hσζ P hP hε hεζ hεP (hVdiag v hv)
      fun j hj => by
        show (v * ε₀ ^ n) j = j
        rw [← hvn]
        exact hfix j hj
    have hε₀n : ε₀ ^ n = 1 := by
      rw [hε₀def, TwE6Outer.fieldActor_pow, hεn, ← fieldActorHom_apply, map_one]
    rw [hvn, hε₀n, mul_one] at hcore' ⊢
    exact hVk v hv hcore'
  have hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (TwE6Conc.twE6R0 c hct))) J := by
    rw [fixSubgroup_conj_eq_centralizer_zpowers]
    exact hJcomp
  have htJ : J ≤ Subgroup.centralizer ({TwE6Conc.twE6T K ℓ (3 * d)} :
      Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ (3 * d)))) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (TwE6Conc.twE6T_commute hj).symm
  have htd : MulAut.conj (TwE6Conc.twE6R0 c hct) (TwE6Conc.twE6T K ℓ (3 * d)) =
      TwE6Conc.twE6T K ℓ (3 * d) := by
    rw [MulAut.conj_apply, TwE6Conc.twE6R0_mul_twE6T, mul_inv_cancel_right]
  have hW := actData_of_distinguished Nat.prime_three hB Γ' hBker hB4 (hVB hr₀V) hd₁1 (hVB hv₁V)
    hv₁r hJ hJB hJk hv₁L (TwE6Conc.twE6T_ne_one hℓ2) (TwE6Conc.twE6T_sq K ℓ (3 * d)) htJ htd
  exact concA_of_actData_conj hS hperf hcore hB hBC e hΓe ψ hW

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
