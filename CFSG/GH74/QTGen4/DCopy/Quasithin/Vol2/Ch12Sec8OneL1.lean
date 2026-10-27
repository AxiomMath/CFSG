module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_lOne_rep_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ∃ (Q : Type) (_ : Group Q) (ρX : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G)) →* Q),
      Function.Surjective (ρX.comp (Subgroup.inclusion
        (show lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) from oTwoUpper_le _))) ∧
      (ρX.comp (Subgroup.inclusion
        (show lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) from oTwoUpper_le _))).ker =
        CFSG.pCore 2 ↥(lOne L V₁) ∧
      (∀ x : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G)),
        (∀ v ∈ V, (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ V₁) → ρX x = 1) ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  have hn4 : 4 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  let _ := zmodModuleOf hsq
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  set X := L ⊓ Subgroup.normalizer (V₁ : Set G) with hXdef
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLV
  set W₁ := subOf (V := V) V₁ with hW₁
  have : Finite (Additive ↥V ⧸ W₁) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W₁)

  have hdimV : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ↥V) = 2 ^ n := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hdimW : Module.finrank (ZMod 2) W₁ = 1 := finrank_subOf hV₁.1 hV₁.2.1
  have hdimQ : Module.finrank (ZMod 2) (Additive ↥V ⧸ W₁) = n - 1 := by
    have := Submodule.finrank_quotient_add_finrank W₁
    omega
  obtain ⟨eQ⟩ := nonempty_linearEquiv_mulEquiv_sl hdimQ
  obtain ⟨hsimp, a₀, b₀, hab₀⟩ := isSimpleGroup_sl_zmod_two (m := n - 1) (by omega)
  have : IsSimpleGroup ((Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁)) := eQ.isSimpleGroup
  have : Finite ((Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁)) :=
    Finite.of_equiv _ eQ.symm.toEquiv
  have hnabQ : ∃ a b : (Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁), a * b ≠ b * a :=
    ⟨eQ.symm a₀, eQ.symm b₀, fun h' => hab₀ (by simpa using congrArg eQ h')⟩

  let σ : ↥X →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    linHom.comp ((conjAct V).comp (Subgroup.inclusion hXV))
  have hσ : ∀ (x : ↥X) (v : Additive ↥V), ((Additive.toMul (σ x v) : ↥V) : G) =
      (x : G) * ((Additive.toMul v : ↥V) : G) * (x : G)⁻¹ := fun x v => rfl
  have hσle : ∀ x : ↥X, W₁.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) ≤ W₁ := by
    rintro x _ ⟨w, hw, rfl⟩
    have hw' : ((w.toMul : ↥V) : G) ∈ V₁ := mem_subOf.1 hw
    show (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w ∈ subOf (V := V) V₁
    rw [mem_subOf, show ((σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) = σ x w from rfl, hσ]
    exact (Subgroup.mem_normalizer_iff.1 x.2.2 _).1 hw'
  have hσW : ∀ x : ↥X, W₁.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) = W₁ := by
    intro x
    refine le_antisymm (hσle x) fun w hw => ?_
    refine ⟨σ x⁻¹ w, hσle x⁻¹ ⟨w, hw, rfl⟩, ?_⟩
    show σ x (σ x⁻¹ w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

  let ρX : ↥X →* ((Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁)) :=
    { toFun := fun x => Submodule.Quotient.equiv W₁ W₁ (σ x) (hσW x)
      map_one' := by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
        simp [map_one]
      map_mul' := fun x y => by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
        simp [map_mul] }
  have hρX : ∀ (x : ↥X) (v : Additive ↥V),
      ρX x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (σ x v) := fun x v => rfl

  have hρXsurj : Function.Surjective ρX := by
    intro τ
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl W₁
    let e := Submodule.quotientEquivOfIsCompl W₁ C hC
    let τC : C ≃ₗ[ZMod 2] C := (e.symm.trans τ).trans e
    let β : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V :=
      ((Submodule.prodEquivOfIsCompl W₁ C hC).symm.trans
        ((LinearEquiv.refl (ZMod 2) W₁).prodCongr τC)).trans
        (Submodule.prodEquivOfIsCompl W₁ C hC)
    have hβW : ∀ w (hw : w ∈ W₁), β w = w := fun w hw => by
      have h1 : (Submodule.prodEquivOfIsCompl W₁ C hC).symm w = (⟨w, hw⟩, 0) :=
        Submodule.prodEquivOfIsCompl_symm_apply_left W₁ C hC ⟨w, hw⟩
      simp only [β, LinearEquiv.trans_apply, h1]
      simp [Submodule.coe_prodEquivOfIsCompl']
    have hβC : ∀ c : C, β c = (τC c : Additive ↥V) := fun c => by
      have h1 := Submodule.prodEquivOfIsCompl_symm_apply_right W₁ C hC c
      simp only [β, LinearEquiv.trans_apply, h1]
      simp [Submodule.coe_prodEquivOfIsCompl']
    have hβQ : ∀ v, (Submodule.Quotient.mk (β v) : Additive ↥V ⧸ W₁) =
        τ (Submodule.Quotient.mk v) := by
      intro v
      obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ C hC).surjective v
      have e1 : (Submodule.prodEquivOfIsCompl W₁ C hC) (a, b) = (a : Additive ↥V) + b :=
        Submodule.coe_prodEquivOfIsCompl' W₁ C hC (a, b)
      rw [e1, map_add, hβW _ a.2, hβC, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
        (Submodule.Quotient.mk_eq_zero W₁).2 a.2, zero_add, zero_add]
      show (Submodule.Quotient.mk (e (τ (e.symm b)) : Additive ↥V) : Additive ↥V ⧸ W₁) =
        τ (Submodule.Quotient.mk b)
      rw [Submodule.mk_quotientEquivOfIsCompl_apply, Submodule.quotientEquivOfIsCompl_symm_apply]
    have hαL : mulAutOfLin β ∈ autOn L V := by
      rw [autOn_eq_top_of_hyp1281One h]
      exact Subgroup.mem_top _
    obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
    have hconj : ∀ v : ↥V, l * (v : G) * l⁻¹ =
        ((Additive.toMul (β (Additive.ofMul v)) : ↥V) : G) := fun v => by
      rw [← mulAutOfLin_apply, ← hlα]
      rfl
    have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hconj ⟨x, hV₁.1 hx⟩
      rw [hβW _ ((mem_subOf (x := Additive.ofMul (⟨x, hV₁.1 hx⟩ : ↥V))).2 hx)] at h1
      change l * x * l⁻¹ = x at h1
      calc x * l = (l * x * l⁻¹) * l := by rw [h1]
        _ = l * x := by group
    refine ⟨⟨l, Subgroup.mem_subgroupOf.1 hlL, hlV₁⟩, ?_⟩
    apply LinearEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
    rw [hρX, ← hβQ]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    exact hconj (Additive.toMul v)

  have hkerX : ∀ x : ↥X, ρX x = 1 → (x : G) ^ 2 ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    intro x hx
    refine ⟨L.pow_mem x.2.1 2, ?_⟩
    show (x : G) ^ 2 ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := LinearEquiv.congr_fun hx (Submodule.Quotient.mk (Additive.ofMul (⟨v, hv⟩ : ↥V)))
    rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁, mem_subOf] at h1
    have hd : (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ V₁ := by
      have e1 : ((Additive.toMul (σ x (Additive.ofMul ⟨v, hv⟩) - Additive.ofMul ⟨v, hv⟩) :
          ↥V) : G) = (x : G) * v * (x : G)⁻¹ * v⁻¹ := by
        rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
        rfl
      rw [← e1]
      exact h1
    set d := (x : G) * v * (x : G)⁻¹ * v⁻¹ with hddef
    have hxd : (x : G) * d = d * x :=
      Subgroup.mem_centralizer_iff.1 (le_centralizer_normalizer_of_card_eq_two hV₁2 hd) x x.2.2
    have hdV : d ∈ V := hV₁.1 hd
    have e2 : (x : G) * v * (x : G)⁻¹ = d * v := by rw [hddef]; group
    have e3 : (x : G) * d * (x : G)⁻¹ = d := by rw [hxd]; group
    have e4 : (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹ = v := by
      calc (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹
          = ((x : G) * d * (x : G)⁻¹) * ((x : G) * v * (x : G)⁻¹) := by
            rw [hddef, pow_two]; group
        _ = d * (d * v) := by rw [e3, e2]
        _ = v := by rw [← mul_assoc, ← pow_two, hsq d hdV, one_mul]
    calc v * (x : G) ^ 2 = ((x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹) * (x : G) ^ 2 := by rw [e4]
      _ = (x : G) ^ 2 * v := inv_mul_cancel_right _ _

  set L₁ := lOne L V₁ with hL₁
  have hL₁X : L₁ ≤ X := oTwoUpper_le X
  have hXL₁ : X ≤ Subgroup.normalizer (L₁ : Set G) := le_normalizer_oTwoUpper X
  let ρ : ↥L₁ →* ((Additive ↥V ⧸ W₁) ≃ₗ[ZMod 2] (Additive ↥V ⧸ W₁)) :=
    ρX.comp (Subgroup.inclusion hL₁X)

  have hρsurj : Function.Surjective ρ := by
    have hnorm : ρ.range.Normal := by
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 ha
      obtain ⟨x, rfl⟩ := hρXsurj g
      have hy : (x : G) * (y : G) * (x : G)⁻¹ ∈ L₁ :=
        (Subgroup.mem_normalizer_iff.1 (hXL₁ x.2) _).1 y.2
      refine MonoidHom.mem_range.2 ⟨⟨_, hy⟩, ?_⟩
      show ρX (Subgroup.inclusion hL₁X ⟨_, hy⟩) =
        ρX x * ρX (Subgroup.inclusion hL₁X y) * (ρX x)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.range with hb | ht
    · exfalso
      apply not_isPGroup_of_isSimpleGroup hnabQ (p := 2)
      intro τ
      obtain ⟨x, rfl⟩ := hρXsurj τ
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X x.2
      refine ⟨k, ?_⟩
      have h1 : ρ ⟨_, hk⟩ ∈ ρ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      rw [← map_pow, ← h1]
      show ρX _ = ρX _
      congr 1
    · exact MonoidHom.range_eq_top.1 ht

  have hker : ρ.ker = CFSG.pCore 2 ↥L₁ := by
    apply le_antisymm
    · have hp : IsPGroup 2 ρ.ker := by
        intro y
        have hy1 : ρ (y : ↥L₁) = 1 := MonoidHom.mem_ker.1 y.2
        have h2 := hkerX _ hy1
        rw [inf_centralizer_eq_pCoreOf_F4 h1222 h] at h2
        obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, h2⟩
        refine ⟨k + 1, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        have h3 := congrArg Subtype.val hk
        simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_inclusion] at h3 ⊢
        rw [pow_succ', pow_mul]
        exact h3
      exact LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ρ) hp
    · have hm : ((CFSG.pCore 2 ↥L₁).map ρ).Normal :=
        Subgroup.Normal.map CFSG.pCore_normal ρ hρsurj
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L₁).map ρ) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L₁)).map ρ
      exact (Subgroup.map_eq_bot_iff _).1 (eq_bot_of_normal_of_isPGroup hnabQ _ hp)
  refine ⟨_, inferInstance, ρX, hρsurj, hker, fun x hx => ?_, ⟨eQ⟩⟩

  apply LinearEquiv.ext
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁ q
  rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁, mem_subOf]
  have e1 : ((Additive.toMul (σ x v - v) : ↥V) : G) =
      (x : G) * ((Additive.toMul v : ↥V) : G) * (x : G)⁻¹ * ((Additive.toMul v : ↥V) : G)⁻¹ := by
    rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
  rw [e1]
  exact hx _ (Additive.toMul v).2

theorem lOne_quotient_mulEquiv_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
      Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := by
  obtain ⟨Q, _, ρX, hsurj, hker, -, ⟨eQ⟩⟩ := exists_lOne_rep_F4 h1222 h hn hV₁
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).trans eQ⟩

theorem lOne_mem_cComp_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    lOne L V₁ ∈ cComp (lOne L V₁ ⊔ T) := by
  obtain ⟨e⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
  have hn4 : 4 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  refine mem_cComp_of_quasisimple_quotient (oTwoUpper_eq_top_of_isPGroup _)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl_zmod_two (by omega)).1)
    (A3.subnormal_of_normal le_sup_left ?_)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer (le_normalizer_lOne h.hyp.normalizes hV₁.2.2)

theorem lOne_lemma_1_2_4_data_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V₁ : Set G)) ∧
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ ∧
      lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) ∧ lOne L V₁ ∈ lFamily T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  refine ⟨isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow hV₁.2.2, fun hb => ?_,
    (oTwoUpper_le _).trans inf_le_right, ?_⟩
  · have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hV₁.2.1)
    rw [hb, le_bot_iff] at h1
    have h2 := Subgroup.card_eq_one.2 h1
    omega
  · rw [lFamily, Set.mem_ofPred_eq]
    exact lOne_mem_cComp_F4 h1222 h hn hV₁

theorem normalizer_le_of_lOne_le_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n) (hn : n ≠ 3)
    {V₁ K₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨hS, hH, -, hB⟩ := lOne_lemma_1_2_4_data_F4 h1222 h hn hV₁
  have hKn := lemma_1_2_4_normal h.hyp.qtke h.hyp.simple h.hyp.nonabelian h37 h38 hH hS hB hLK
    hK (le_normalizer_lOne h.hyp.normalizes hV₁.2.2)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (A3.subnormal_le hK.2.2.1)).1 hKn

theorem exists_cComp_normalizer_ge_lOne_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ∃ K₁ : Subgroup G, lOne L V₁ ≤ K₁ ∧
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) ∧
      Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨hS, hH, hBH, hB⟩ := lOne_lemma_1_2_4_data_F4 h1222 h hn hV₁
  obtain ⟨K, ⟨hK, hLK⟩, -⟩ := lemma_1_2_4_existsUnique h.hyp.qtke h.hyp.simple
    h.hyp.nonabelian h37 h39 hH hS hBH hB
  exact ⟨K, hLK, hK, normalizer_le_of_lOne_le_F4 h1222 h37 h38 h hn hV₁ hLK hK⟩

end CFSG.Quasithin.H13
