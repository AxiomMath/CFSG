module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSelection
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Seven

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis CFSG.LocalAnalysis.EvenBN.GMS
open scoped MatrixGroups

section Components

variable {H : Type*} [Group H]

theorem inf_eq_bot_or_le_of_isSubnormal {L : Subgroup H} [IsSimpleGroup L] {M N : Subgroup H}
    (hMN : IsSubnormal M N) (hN : N = ⊤) : M ⊓ L = ⊥ ∨ L ≤ M := by
  induction hMN with
  | refl => exact Or.inr (hN ▸ le_top)
  | step hHM hn hMK ih =>
    rename_i H' M' K'
    rcases ih hN with h1 | h1
    · left
      exact eq_bot_iff.2 fun x hx => h1 ▸ ⟨hHM hx.1, hx.2⟩
    ·
      have hnL : ((H' ⊓ L).subgroupOf L).Normal := by
        refine ⟨fun x hx l => ?_⟩
        rw [mem_subgroupOf] at hx ⊢
        obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.1 hx
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have := hn.conj_mem ⟨(x : H), hHM hxH⟩ (mem_subgroupOf.2 hxH) ⟨(l : H), h1 l.2⟩
          rw [mem_subgroupOf] at this
          simpa using this
        · simpa using mul_mem (mul_mem l.2 hxL) (inv_mem l.2)
      rcases hnL.eq_bot_or_eq_top with h2 | h2
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        have : (⟨x, hx.2⟩ : L) ∈ (H' ⊓ L).subgroupOf L := mem_subgroupOf.2 hx
        rw [h2, mem_bot] at this
        exact mem_bot.2 (congrArg Subtype.val this)
      · right
        intro l hl
        have : (⟨l, hl⟩ : L) ∈ (H' ⊓ L).subgroupOf L := by rw [h2]; exact mem_top _
        exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 this)).1

theorem eq_of_isComponentOf_of_le {L K : Subgroup H} [IsSimpleGroup L] (hK : IsComponentOf K ⊤)
    (hKL : K ≤ L) : K = L := by
  rcases inf_eq_bot_or_le_of_isSubnormal (L := L) hK.2.1 rfl with h1 | h1
  · exfalso
    rw [inf_eq_left.2 hKL] at h1
    have : Nontrivial (K ⧸ center K) := hK.2.2.2.toNontrivial
    obtain ⟨a, b, hab⟩ := this
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h1 a a.2)
    have hb : b = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h1 b b.2)
    rw [ha, hb]
  · exact le_antisymm hKL h1

end Components

section Products

theorem not_isSimpleGroup_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Nontrivial G₁]
    [Nontrivial G₂] : ¬ IsSimpleGroup (G₁ × G₂) := by
  intro hs
  obtain ⟨g₁, hg₁⟩ := exists_ne (1 : G₁)
  obtain ⟨g₂, hg₂⟩ := exists_ne (1 : G₂)
  rcases (MonoidHom.normal_ker (MonoidHom.snd G₁ G₂)).eq_bot_or_eq_top with h1 | h1
  · have : ((g₁, 1) : G₁ × G₂) ∈ (MonoidHom.snd G₁ G₂).ker := MonoidHom.mem_ker.2 rfl
    rw [h1, mem_bot] at this
    exact hg₁ (congrArg Prod.fst this)
  · have : ((1, g₂) : G₁ × G₂) ∈ (MonoidHom.snd G₁ G₂).ker := by rw [h1]; exact mem_top _
    exact hg₂ (MonoidHom.mem_ker.1 this)

end Products

namespace LocalSetting

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H}

theorem layer_selection_four
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hK : CFSG.SectionRank.IsKGroupCat H)
    (h : LocalSetting A t U V D 4) (hVA : V ≤ normalClosure (A : Set H)) :
    centralizer (CFSG.layer H : Set H) = ⊥ ∧ A ≤ CFSG.layer H ∧
      CFSG.layer H = normalClosure (A : Set H) ∧ V ≤ CFSG.layer H ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 4 ∧
          ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
            ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ 4) ^ 2 ∧
          ∃ ψ : CFSG.layer H ≃* SL(2, k₂),
            (∀ x y : CFSG.layer H, (y : H) = t⁻¹ * x * t →
              ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ 4)) ∧
            ∀ g : SL(2, k₂), g ∈ (A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ 4 =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨-, -, k, hkF, hkFt, hk, ⟨φ⟩⟩, ⟨-, -, -, hAn⟩, -⟩ := h.app
  have hSLD : GMSK.StdLinearData H A 4 :=
    ⟨by norm_num, h.isStandard, h.not_normal, k, hkF, hkFt, hk, ⟨φ⟩⟩
  obtain ⟨S₀, hS₀⟩ := h.exists_sylow_centralizer
  have hS₀card : Nat.card (S₀ : Subgroup (centralizer (A : Set H))) = 2 := by
    rw [hS₀, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 h.t_mem_centralizer)).toEquiv,
      Nat.card_zpowers, h.orderOf_t]
  have hsyl2 : ∀ S : Sylow 2 (centralizer (A : Set H)), Nat.card S = 2 := fun S => by
    rw [Nat.card_congr (Sylow.equiv S S₀).toEquiv]
    exact hS₀card
  have hLO := hL H hK h.oddCore_eq_bot 4 A hSLD hsyl2
  have hrel : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set H)) := by
    rw [Subgroup.relIndex, ← hS₀]
    exact S₀.not_dvd_index
  obtain ⟨-, -, hAE, hDE, hCD, halt, -⟩ := GMSK.oneOrTwoLayer_of_stdLinearData h.oddCore_eq_bot
    hSLD h.orderOf_t h.t_mem_centralizer hrel
  have hVL : V ≤ CFSG.layer H := hDE ▸ hVA
  have hNV : normalClosure (V : Set H) = CFSG.layer H := by
    refine le_antisymm (normalClosure_le_normal hVL) ?_
    rw [← hDE]
    exact normalClosure_le_normal h.A_le_normalClosure
  refine ⟨hDE ▸ hCD, hAE, hDE.symm, hVL, ?_⟩
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ 4) ^ 2 →
      (CFSG.layer H ≃* SL(2, k) × SL(2, k)) → (CFSG.layer H ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * 4) := by
      rw [Nat.card_eq_fintype_card, hk₂]
      norm_num
    exact (isEmpty_mulEquiv_sl2_prod (k := k) (by norm_num) hk₂').false (ψ₂.symm.trans ψ₁)
  have := h.isSimpleGroup
  have hAna : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩
  have : Nontrivial A := by
    obtain ⟨x, y, hxy⟩ := hAna
    exact ⟨⟨x * y, y * x, hxy⟩⟩
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have := @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 H _ V h.isElementaryAbelian_V x hx
    rwa [sq] at this
  have hVcard : Nat.card V = 2 ^ 8 := by
    rw [h.card_V]
    norm_num
  rcases halt.or with ⟨hDs, hDna, -, hnt⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hψA, hψt⟩
  ·
    rw [hDE] at hDs hDna hnt
    have hfirst : ¬ ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 4 ∧
        ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
          (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
          ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
            ψ x = (y₁, y₂) → ψ y = (y₂, y₁) := by
      rintro ⟨k', _, _, -, ψ, α, -⟩
      have : Nontrivial (SL(2, k')) := α.symm.toEquiv.nontrivial
      exact not_isSimpleGroup_prod (ψ.symm.isSimpleGroup)
    refine Or.inr ⟨?_, hfirst⟩
    rcases hLO with ⟨⟨e⟩⟩ | ⟨hL2 | hU3 | hL3⟩ | ⟨h42, -⟩ | ⟨h43, -⟩
    ·
      exact absurd e.symm.isSimpleGroup not_isSimpleGroup_prod
    ·
      rcases hL2 with ⟨-, -, K', hK'F, hK'fin, hK'card, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      swap
      · exact absurd h0 (by norm_num)
      swap
      · exact absurd h0 (by norm_num)
      swap
      · exact absurd h0 (by norm_num)
      have hK'8 : Nat.card K' = 2 ^ 8 := by rw [hK'card]
      have : CharP K' 2 := ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := 8) (by norm_num) hK'8
      set eSL : CFSG.layer H ≃* SL(2, K') := eK.trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K').symm.trans
          CFSG.Walter.psl2MulEquivSL2OfCharTwo) with heSL
      have hcard2 : ∀ P : Subgroup H, IsPGroup 2 P → P ≤ CFSG.layer H → Nat.card P ≤ 2 ^ 8 := by
        intro P hP hPL
        classical
        let := Fintype.ofFinite K'
        have hdvd : Nat.card P ∣ 2 ^ 8 * 65535 := by
          have h1 := card_dvd_of_le hPL
          rw [Nat.card_congr eSL.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
            Fin.val_one, pow_zero, pow_one, ← Nat.card_eq_fintype_card, hK'8] at h1
          norm_num at h1
          exact h1
        obtain ⟨m, hm⟩ := hP.exists_card_eq
        rw [hm] at hdvd ⊢
        have h2 : 2 ^ m ∣ 2 ^ 8 :=
          (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 65535)).dvd_of_dvd_mul_right hdvd
        exact Nat.le_of_dvd (by positivity) h2
      obtain ⟨S, hVS⟩ :=
        (@CFSG.IsElementaryAbelian.isPGroup 2 V _ h.isElementaryAbelian_V).exists_le_sylow
      have hSV : (S : Subgroup H) ⊓ CFSG.layer H = V := by
        refine (eq_of_le_of_card_ge (le_inf hVS hVL) ?_).symm
        rw [hVcard]
        exact hcard2 _ (S.isPGroup'.to_inf_left) inf_le_right
      have hmemV : ∀ x ∈ (S : Subgroup H), x ∈ normalClosure (V : Set H) → x * x = 1 →
          x ∈ V := fun x hxS hxV _ => by
        rw [← hSV]
        exact Subgroup.mem_inf.2 ⟨hxS, hNV ▸ hxV⟩
      have hZ : center (CFSG.layer H) = ⊥ := by
        rcases (center (CFSG.layer H)).normal_of_characteristic.eq_bot_or_eq_top with h1 | h1
        · exact h1
        · exfalso
          obtain ⟨x, y, hxy⟩ := hDna
          apply hxy
          have hy : y ∈ center (CFSG.layer H) := by rw [h1]; exact mem_top y
          exact (mem_center_iff.1 hy x)
      have hKc : IsComponentOf (CFSG.layer H) ⊤ := by
        refine ⟨le_top, IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤), ?_⟩
        · exact (inferInstance : (CFSG.layer H).Normal).subgroupOf ⊤
        · refine ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top _ hDna, ?_⟩
          have := hDs
          exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
            (QuotientGroup.quotientBot (G := CFSG.layer H))).isSimpleGroup
      have htype : ∀ K : Subgroup H, IsComponentOf K ⊤ → K ≤ normalClosure (V : Set H) →
          CFSG.Open.goldschmidtSimpleType (K ⧸ center K) := by
        intro K hK hKV
        obtain rfl := eq_of_isComponentOf_of_le (L := CFSG.layer H) hK (hNV ▸ hKV)
        refine Or.inl ⟨8, by norm_num, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientBot (G := CFSG.layer H))).trans (eSL.trans
            ((CFSG.ClassicalModels.specialLinearFieldEquiv
              (CFSG.ClassicalModels.finiteFieldEquivGaloisField K' 2 8 (by norm_num) hK'8)
              (Fin 2)).trans CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm))⟩⟩
      have hE' : sSup {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ normalClosure (V : Set H)} =
          normalClosure (V : Set H) := by
        have hset : {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ normalClosure (V : Set H)} =
            {K : Subgroup H | IsComponentOf K ⊤} := by
          ext K
          exact ⟨fun hK => hK.1, fun hK => ⟨hK, hNV ▸ le_layer_of_isComponentOf hK⟩⟩
        rw [hset, ← layer_eq_sSup, hNV]
      exact h.alternative_two S hVS hE' htype hmemV hKc rfl
    ·
      exfalso
      have hb := CFSG.LocalAnalysis.EvenBN.TwoF4.card_le_of_lieModel_PSU3 hU3
        (E := V.subgroupOf (CFSG.layer H)) fun x hx => Subtype.ext (hV2 _ (mem_subgroupOf.1 hx))
      rw [Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv, hVcard] at hb
      norm_num at hb
    ·
      exfalso
      have hA17 : 17 ∣ Nat.card A := by
        classical
        rw [Nat.card_congr φ.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
          Fin.val_one, pow_zero, pow_one, hk]
        norm_num
      exact false_of_lieModel_PSL3_four h.t_mul_t hL3 hnt hAE h.le_centralizer hAna hAn hA17 hVL
        hV2 hVcard h.t_mem_normalizer_V
    · exact absurd h42 (by norm_num)
    · exact absurd h43 (by norm_num)
  ·
    set ψ' : CFSG.layer H ≃* SL(2, k) × SL(2, k) :=
      (MulEquiv.subgroupCongr hDE.symm).trans (ψ.trans (MulEquiv.prodCongr φ φ)) with hψ'
    refine Or.inl ⟨⟨k, hkF, hkFt, hk, ψ', φ, fun a x hxa => ?_, fun x y y₁ y₂ hxy hx => ?_⟩,
      fun ⟨k₂, _, _, hk₂, ψ₂, _⟩ => hexcl k hkF hkFt k₂ _ _ hk₂ ψ' ψ₂⟩
    · have hx' : (MulEquiv.subgroupCongr hDE.symm x : normalClosure (A : Set H)) =
          ⟨a, subset_normalClosure a.2⟩ := Subtype.ext hxa
      rw [hψ', MulEquiv.trans_apply, MulEquiv.trans_apply, hx', hψA a a.2]
      rfl
    · have hxD : (x : H) ∈ normalClosure (A : Set H) := by rw [hDE]; exact x.2
      have hyD : t⁻¹ * (x : H) * t ∈ normalClosure (A : Set H) := by
        rw [← hxy, hDE]
        exact y.2
      have hy' : (MulEquiv.subgroupCongr hDE.symm y : normalClosure (A : Set H)) =
          ⟨t⁻¹ * x * t, hyD⟩ := Subtype.ext hxy
      have hx' : (MulEquiv.subgroupCongr hDE.symm x : normalClosure (A : Set H)) =
          ⟨x, hxD⟩ := rfl
      rw [hψ', MulEquiv.trans_apply, MulEquiv.trans_apply, hx'] at hx
      rw [hψ', MulEquiv.trans_apply, MulEquiv.trans_apply, hy', hψt (x : H) hxD hyD]
      generalize ψ ⟨(x : H), hxD⟩ = p at hx ⊢
      obtain ⟨p₁, p₂⟩ := p
      change (φ p₁, φ p₂) = (y₁, y₂) at hx
      change (φ p₂, φ p₁) = (y₂, y₁)
      rw [Prod.mk.injEq] at hx
      rw [hx.1, hx.2]

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.U5
