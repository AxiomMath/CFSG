module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23H

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem stmt5_2_8_Q_of_F4
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4)
    (hsp : Stmt5_2_8_special_F4) : Stmt5_2_8_Q_F4 := by
  intro G _ _ T M L V H B D L₂ n K' hyp hM23 hlt hmax hexc
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set W := pCoreOf 2 K' with hWdef
  have hKK' : K ≤ K' := hlt.le
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K'
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')

  have hLin := isLin2Type_oTwoUpper_of_F4 h526 h1284 hSz hU4 hsp hyp hM23 hlt hmax
  have hcardK := card_eq_of_isLin2Type hLin
  have hG2 : Nat.card ↥(D ⊔ (sec52S M H ⊓ L) ⊔ K) = 960 :=
    card_right_eq_960_of_isAmalgamOfGroup hM23.1
  have hKdvd : Nat.card K ∣ 960 := hG2 ▸ Subgroup.card_dvd_of_le le_sup_right
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  obtain ⟨hn2, ha4⟩ := lin2_arith h.two_le (by rw [← ha, ← hcardK]; exact hKdvd)
  have hUQ : blockU K ≤ Q := by
    show ⁅pCoreOf 2 K, K⁆ ≤ pCoreOf 2 K
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hKN : K ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    have h1 : k * q⁻¹ * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp (Q.inv_mem hq)
    rw [commutatorElement_def]
    have h2 := Q.mul_mem hq h1
    simpa [mul_assoc] using h2
  have hU16 : 16 ≤ Nat.card ↥(blockU K) := by
    obtain ⟨F, _, _, hF, -, -, -, β, hβ, -, -⟩ := hLin
    have h1 := Nat.card_le_card_of_surjective β hβ
    rw [Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)), Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, hF, hn2] at h1
    simpa using h1
  have hcardQ : Nat.card Q = 16 := by
    have h1 := (hU16.trans (Subgroup.card_le_of_le hUQ))
    have h2 : 2 ^ a ≤ 16 := by
      calc 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) ha4
        _ = 16 := by norm_num
    rw [ha] at h1 ⊢
    omega

  have hTN : T ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_isLocal_of_excA7 (CFSG.QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
      h37 h38 hmax.1 hexc

  obtain ⟨hsh, ⟨α, hα, hαker⟩, hidx⟩ := hexc
  set π : ↥K' →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp α with hπ
  have hker : π.ker = W.subgroupOf K' := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _), hαker,
      CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore, hWdef, pCoreOf, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  have hrange : π.range = alternatingGroup (Fin 7) := by
    rw [hπ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨-, -, hQW⟩ := pCoreOf_le_of_card_eq hker hrange hW2 hKK' hK'N h.two_le hcardK

  obtain ⟨-, -, -, -, -, -, hKT, hab⟩ := h526 G T M L V H B D L₂ n hyp
  have hKS : pCoreOf 2 (K ⊔ sec52S M H) = Q := by
    rcases hab with ⟨-, -, -, h1⟩ | ⟨m, -, h2n, -⟩
    · exact h1
    · omega
  have hXN : K' ⊔ T ≤ Subgroup.normalizer (K' : Set G) := sup_le Subgroup.le_normalizer hTN
  have hXW : K' ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')
  have hTs : IsSylowTwoOf T (K' ⊔ T) := isSylowTwoOf_of_isSylowTwo hyp.sylow le_sup_right
  have hWX : W ≤ K' ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_left
  have hWT : W ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal ⟨hTs.1, hTs.2.1, hTs.2.2⟩ hWX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW) hW2
  have hKTN : K ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (hKK'.trans hK'N) (le_sup_right.trans hXW)
  have hWKT : W ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hWT.trans le_sup_right) hKTN hW2
  rw [hKT, hKS] at hWKT
  have hWQ : W = Q := le_antisymm hWKT hQW

  have hZ := CFSG.QuasithinUnique.L246.C123.blockZ_eq_bot_of_isExcA7Block
    ⟨hsh, ⟨α, hα, hαker⟩, hidx⟩
  have hcardU' : Nat.card ↥(blockU K') = 16 := by
    rw [hZ, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
    rw [hidx]
    norm_num
  have hcardW : Nat.card W = 16 := by rw [hWQ, hcardQ]
  have hUW : blockU K' = W :=
    Subgroup.eq_of_le_of_card_ge (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh)
      (by rw [hcardW, hcardU'])
  have hWab : IsElemAbelian 2 W := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have ha' : (a : G) ∈ blockU K' := by rw [hUW]; exact a.2
      have hb' : (b : G) ∈ blockU K' := by rw [hUW]; exact b.2
      exact CFSG.QuasithinUnique.C1.blockU_comm hsh a ha' b
        (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh hb')
    · have hx' : x ∈ blockU K' := by rw [hUW]; exact hx
      exact CFSG.QuasithinUnique.C1.blockU_sq hsh x hx'
  refine ⟨hWab, hcardW, ?_⟩

  set N := Subgroup.normalizer (W : Set G) with hNdef
  have hW1 : W ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardW
    norm_num at hcardW
  have hWN : W ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW2
  have hTNW : T ≤ N := le_sup_right.trans hXW
  have hInH : InH T N := ⟨hTNW, fun hb => hW1 (eq_bot_iff.mpr (hb ▸ hWN))⟩
  have hchar := charTwo_of_inH' h.qtke hyp.sylow hInH
  have hO2N : pCoreOf 2 N = W := by
    refine le_antisymm ?_ hWN
    have hTsN : IsSylowTwoOf T N := isSylowTwoOf_of_isSylowTwo hyp.sylow hTNW
    have hPN : pCoreOf 2 N ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
    have hPT : pCoreOf 2 N ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal
      ⟨hTsN.1, hTsN.2.1, hTsN.2.2⟩ hPN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr
        (Subgroup.le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    have hKTN' : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
      hKTN.trans (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N))
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right) hKTN'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [hKT, hKS, ← hWQ] at h1
    exact h1
  unfold CharTwo at hchar
  rw [hO2N] at hchar

  have hcommW : ∀ a b : ↥W, a * b = b * a := fun a b => hWab.1.1.comm a b
  let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hcommW }
  have hW2' : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hWab.2 w w.2)
  set X := K' ⊔ T with hXdef
  let φ : ↥X →* MulAut ↥W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hXW)
  have hφ : ∀ (g : ↥X) (w : ↥W), ((φ g w : ↥W) : G) = g * w * (g : G)⁻¹ := fun g w => rfl
  have hkerφ : ∀ g : ↥X, φ g = 1 → (g : G) ∈ W := by
    intro g hg
    have hc : (g : G) ∈ N ⊓ Subgroup.centralizer (W : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hXW g.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := congrArg (fun f : MulAut ↥W => ((f ⟨w, hw⟩ : ↥W) : G)) hg
      simp only [hφ, MulAut.one_apply] at h1
      calc w * (g : G) = (g : G) * w * (g : G)⁻¹ * g := by rw [h1]
        _ = g * w := by group
    exact hchar hc

  set Λ := (K'.subgroupOf X).map φ with hΛdef
  have hcardK' : Nat.card K' = 2520 * 16 := by
    have h1 := card_eq_card_modO2_mul K'
    have h2 : Nat.card (↥K' ⧸ CFSG.pCore 2 ↥K') = 2520 := by
      rw [← card_alternatingGroup_seven]
      exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv
    have hW16 : Nat.card ↥(pCoreOf 2 K') = 16 := hcardW
    rw [h1, h2, hW16]
  have hcardΛ : Nat.card Λ = 2520 := by
    let ψ := φ.domRestrict (K'.subgroupOf X)
    have h1 : Nat.card ψ.range = ψ.ker.index := (Subgroup.index_ker ψ).symm
    rw [MonoidHom.domRestrict_range] at h1
    have h2 := Subgroup.card_mul_index ψ.ker
    have hmem : ∀ k : ↥(K'.subgroupOf X), k ∈ ψ.ker ↔ ((k : X) : G) ∈ W := by
      intro k
      rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      constructor
      · exact hkerφ _
      · intro hk
        refine MulEquiv.ext fun w => Subtype.ext ?_
        rw [hφ, MulAut.one_apply]
        have h3 : ((k : X) : G) * w = w * ((k : X) : G) := congrArg Subtype.val (hcommW ⟨_, hk⟩ w)
        rw [h3, mul_inv_cancel_right]
    have h3 : Nat.card ψ.ker = 16 := by
      rw [← hcardW]
      refine Nat.card_congr
        { toFun := fun k => ⟨(((k : ↥(K'.subgroupOf X)) : X) : G), (hmem k).mp k.2⟩
          invFun := fun w => ⟨⟨⟨w, (CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_left w.2⟩,
            Subgroup.mem_subgroupOf.mpr ((CFSG.LieType.BorelTits.pCoreOf_le 2 K') w.2)⟩,
            (hmem _).mpr w.2⟩
          left_inv := fun k => rfl
          right_inv := fun w => rfl }
    have h4 : Nat.card ↥(K'.subgroupOf X) = 2520 * 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hcardK']
    rw [hΛdef, h1]
    have h5 : ψ.ker.index * Nat.card ψ.ker = 2520 * 16 := by rw [mul_comm, h2, h4]
    rw [h3] at h5
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h5
  have hNΛ := CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_2520 hW2'
    (by rw [hcardW]) hcardΛ

  intro t ht
  have htX : t ∈ X := Subgroup.mem_sup_right ht
  have hφt : φ ⟨t, htX⟩ ∈ Λ := by
    rw [← hNΛ, Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨t, htX⟩ * k * ⟨t, htX⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hTN ht) _).mp (Subgroup.mem_subgroupOf.mp hk)
    · rintro ⟨k, hk, hkf⟩
      refine ⟨⟨t, htX⟩⁻¹ * k * ⟨t, htX⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTN ht)) _).mp
          (Subgroup.mem_subgroupOf.mp hk)
        simpa using h1
      · rw [map_mul, map_mul, hkf, map_inv]
        group
  obtain ⟨k, hk, hkt⟩ := hφt
  have hk' : ((k : X) : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  have hd : φ (k⁻¹ * ⟨t, htX⟩) = 1 := by rw [map_mul, map_inv, hkt, inv_mul_cancel]
  have hdW := hkerφ _ hd
  have hdK' : ((k⁻¹ * ⟨t, htX⟩ : ↥X) : G) ∈ K' := (CFSG.LieType.BorelTits.pCoreOf_le 2 K') hdW
  have e : t = (k : G) * ((k⁻¹ * ⟨t, htX⟩ : ↥X) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact K'.mul_mem hk' hdK'

end CFSG.Quasithin.H13
