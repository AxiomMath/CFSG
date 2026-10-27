module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.JonesParshall

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem one_lt_rParam_orth_ch6_F4 (h432 : Stmt4_3_2_F4) (hH11 : Ch6InH11) (hE610 : Ch6InE610Four)
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    (hVΩ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ V) : 1 < rParam V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hTI := h.isTISetIn_of_orth_ch6 horth (by norm_num)
  have hE := stmt6_1_3_one_F4 h432 h hTI
  have hNV : Subgroup.normalizer (V : Set G) ≤ M := hE.normalizer_le
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.L_le_normalizer
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := h.T_le_normalizer

  by_contra hr
  obtain ⟨U, hUV, hCU, hU1⟩ : ∃ U : Subgroup G, U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧ mQuot V U = 1 := by
    have hlt : rParam V < 2 := lt_of_le_of_lt (not_lt.mp hr) (by norm_num)
    unfold rParam at hlt
    obtain ⟨U, hU⟩ := iInf_lt_iff.mp hlt
    obtain ⟨⟨hUV, hCU⟩, hU2⟩ := iInf_lt_iff.mp hU
    have hm : mQuot V U < 2 := by exact_mod_cast hU2
    have hm0 : mQuot V U ≠ 0 := by
      intro h0
      have := (E3.mQuot_eq_zero_iff hV2 hUV).mp h0
      rw [this] at hCU
      exact hCU (Subgroup.centralizer_le_normalizer _)
    exact ⟨U, hUV, hCU, by omega⟩
  have hrel : U.relIndex V = 2 := by rw [E3.relIndex_eq_two_pow hV2, hU1, pow_one]
  have hidx : (U.subgroupOf V).index = 2 := hrel
  have hclose : ∀ x ∈ V, ∀ y ∈ V, x ∉ U → y ∉ U → x * y ∈ U := by
    intro x hx y hy hxU hyU
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
      (iff_of_false (fun h' => hxU (Subgroup.mem_subgroupOf.mp h'))
        (fun h' => hyU (Subgroup.mem_subgroupOf.mp h')))
    exact Subgroup.mem_subgroupOf.mp h1

  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left
      h.toHyp5_0_1.sup_le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint, hP, hline, -⟩ :=
    (show IsOrthCh5 L V (2 * 2) from horth).exists_lineCoord hSL
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * 2) := by rw [← Nat.card_eq_fintype_card]; exact hF
  let e : ↥V → ↥(hermA 2 F) := fun w => ⟨Multiplicative.toAdd (Y w), hYherm w⟩
  have he_mul : ∀ w w', e (w * w') = e w + e w' := fun w w' =>
    Subtype.ext (by simp only [e, map_mul, toAdd_mul]; rfl)
  have he_inj : Function.Injective e := fun w w' hww' =>
    hYinj (Multiplicative.toAdd.injective (congrArg Subtype.val hww'))
  have he_surj : Function.Surjective e := fun X => by
    obtain ⟨w, hw⟩ := hYsurj X X.2
    exact ⟨w, Subtype.ext hw⟩
  have he_act : ∀ (x : ↥(autOn L V)) (w : ↥V),
      ((e ((x : MulAut ↥V) w) : ↥(hermA 2 F)) : Matrix (Fin 2) (Fin 2) F) =
        twistActCh6 2 (ψ x) (e w) := fun x w => hYint x w

  let U' : AddSubgroup ↥(hermA 2 F) :=
    { carrier := {X | ∃ w : ↥V, (w : G) ∈ U ∧ e w = X}
      add_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', U.mul_mem hw hw', he_mul w w'⟩
      zero_mem' := ⟨1, U.one_mem, by
        have h1 := he_mul 1 1
        rw [mul_one] at h1
        have h2 : e 1 + e 1 = e 1 + 0 := by rw [← h1, add_zero]
        exact add_left_cancel h2⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨w, hw, ?_⟩
        rw [neg_eq_of_add_eq_zero_right (hermA_add_self (e w))] }
  have hmemU' : ∀ w : ↥V, e w ∈ U' ↔ (w : G) ∈ U := fun w =>
    ⟨fun ⟨w', hw', hww'⟩ => he_inj hww' ▸ hw', fun hw => ⟨w, hw, rfl⟩⟩
  have hU'close : ∀ X Y, X ∉ U' → Y ∉ U' → X + Y ∈ U' := by
    intro X Y hX hY
    obtain ⟨w, rfl⟩ := he_surj X
    obtain ⟨w', rfl⟩ := he_surj Y
    rw [hmemU'] at hX hY
    rw [← he_mul, hmemU']
    exact hclose _ w.2 _ w'.2 hX hY
  obtain ⟨τ, c, hnd⟩ := exists_herm_pairing_ch6 hF' (by norm_num)
  obtain ⟨v₀, hv₀⟩ := exists_herm_hyperplane_ch6 hnd U' hU'close
  have hmemU : ∀ w : ↥V, (w : G) ∈ U ↔
      τ (c * detPolarCh6 (v₀ : Matrix (Fin 2) (Fin 2) F) (e w)) = 0 := fun w => by
    rw [← hmemU', hv₀]

  obtain ⟨g, hg11⟩ := exists_twist_11_eq_zero_ch6 hF v₀.2
  have hσ : ∀ x : F, sig 2 (sig 2 x) = x := sig_sig hF'
  set v₁ := twistActCh6 2 g (v₀ : Matrix (Fin 2) (Fin 2) F) with hv₁
  have hv₁H : v₁ ∈ hermA 2 F := twist_mem 2 hσ v₀.2 _
  obtain ⟨t₀, ht₀0, ht₀v, ht₀Y⟩ := exists_unip_fix_ch6 hF' hv₁H hg11

  obtain ⟨ℓN, hℓL, hℓ⟩ := mem_autOn_iff.mp (ψ.symm g).2
  have hℓV : (ℓN : G) ∈ Subgroup.normalizer (V : Set G) := ℓN.2
  have hℓM : (ℓN : G) ∈ M := h.L_le hℓL
  set U'' := U.map (MulAut.conj (ℓN : G)).toMonoidHom with hU''
  have hU''V : U'' ≤ V := by
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hℓV u).mp (hUV hu)
  have hmemU'' : ∀ w : ↥V, (w : G) ∈ U'' ↔
      τ (c * detPolarCh6 v₁ (e w)) = 0 := by
    intro w
    have hw' : (ℓN : G)⁻¹ * w * (ℓN : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hℓV) w).mp w.2
      simpa using this
    have key : (w : G) ∈ U'' ↔ (ℓN : G)⁻¹ * w * (ℓN : G) ∈ U := by
      constructor
      · rintro ⟨u, hu, hue⟩
        have : u = (ℓN : G)⁻¹ * w * (ℓN : G) := by
          rw [← hue]
          simp [MulAut.conj_apply, mul_assoc]
        rw [← this]
        exact hu
      · intro hu
        exact ⟨_, hu, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [key]
    have hx : (((ψ.symm g)⁻¹ : ↥(autOn L V)) : MulAut ↥V) = conjAct V ℓN⁻¹ := by
      rw [Subgroup.coe_inv, ← hℓ, map_inv]
    have hxw : (((((ψ.symm g)⁻¹ : ↥(autOn L V)) : MulAut ↥V) w : ↥V) : G) =
        (ℓN : G)⁻¹ * w * (ℓN : G) := by
      rw [hx, conjAct_apply_coe]
      simp
    have he' : e ⟨(ℓN : G)⁻¹ * w * (ℓN : G), hw'⟩ =
        e ((((ψ.symm g)⁻¹ : ↥(autOn L V)) : MulAut ↥V) w) := by
      congr 1
      exact Subtype.ext hxw.symm
    rw [hmemU ⟨_, hw'⟩, he']
    have hact := he_act (ψ.symm g)⁻¹ w
    rw [map_inv, MulEquiv.apply_symm_apply] at hact
    rw [hact]
    have h1 := detPolarCh6_twist (a := 2) g (v₀ : Matrix (Fin 2) (Fin 2) F)
      (twistActCh6 2 g⁻¹ (e w))
    have h2 : twistActCh6 2 g (twistActCh6 2 g⁻¹ (e w)) = (e w : Matrix (Fin 2) (Fin 2) F) :=
      twist_twist_inv 2 g _
    rw [h2] at h1
    rw [← h1]

  have hu : (CFSG.Quasithin.Vol2.Ch10.SecA.unipSL t₀ : SL2 F) = uMat t₀ := Subtype.ext rfl
  have hsP : ((ψ.symm (CFSG.Quasithin.Vol2.Ch10.SecA.unipSL t₀) : ↥(autOn L V)) : MulAut ↥V) ∈
      autOn (T ⊓ L) V := (hP _).mpr ⟨t₀, MulEquiv.apply_symm_apply _ _⟩
  obtain ⟨sN, hsS, hs⟩ := mem_autOn_iff.mp hsP
  have hsV : (sN : G) ∈ Subgroup.normalizer (V : Set G) := sN.2
  have hes : ∀ w : ↥V, ∀ hw : (sN : G) * w * (sN : G)⁻¹ ∈ V,
      (e ⟨(sN : G) * w * (sN : G)⁻¹, hw⟩ : Matrix (Fin 2) (Fin 2) F) =
        twistActCh6 2 (uMat t₀) (e w) := by
    intro w hw
    have hact := he_act (ψ.symm (CFSG.Quasithin.Vol2.Ch10.SecA.unipSL t₀)) w
    have hw' : (⟨(sN : G) * w * (sN : G)⁻¹, hw⟩ : ↥V) =
        ((ψ.symm (CFSG.Quasithin.Vol2.Ch10.SecA.unipSL t₀) : ↥(autOn L V)) : MulAut ↥V) w := by
      apply Subtype.ext
      rw [← hs, conjAct_apply_coe]
    rw [hw', hact, MulEquiv.apply_symm_apply, hu]
  have hpair_s : ∀ w : ↥V, ∀ hw : (sN : G) * w * (sN : G)⁻¹ ∈ V,
      detPolarCh6 v₁ (e ⟨(sN : G) * w * (sN : G)⁻¹, hw⟩) = detPolarCh6 v₁ (e w) := by
    intro w hw
    rw [hes w hw]
    conv_lhs => rw [← ht₀v]
    exact detPolarCh6_twist _ _ _
  have hsN : (sN : G) ∈ T ⊓ Subgroup.normalizer (U'' : Set G) := by
    refine ⟨hsS.1, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
    constructor
    · intro hx
      have hxV := hU''V hx
      have hw : (sN : G) * x * (sN : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsV x).mp hxV
      have h1 := (hmemU'' ⟨x, hxV⟩).mp hx
      refine (hmemU'' ⟨_, hw⟩).mpr ?_
      rw [hpair_s ⟨x, hxV⟩ hw]
      exact h1
    · intro hx
      have hw := hU''V hx
      have hxV : x ∈ V := (Subgroup.mem_normalizer_iff.mp hsV x).mpr hw
      have h1 := (hmemU'' ⟨_, hw⟩).mp hx
      rw [hpair_s ⟨x, hxV⟩ hw] at h1
      exact (hmemU'' ⟨x, hxV⟩).mpr h1

  have hQ : ch6Q T V = pCoreOf 2 (L ⊔ T) := h.centralizer_eq
  have hQN : pCoreOf 2 (L ⊔ T) ≤ T ⊓ Subgroup.normalizer (U'' : Set G) := by
    rw [← hQ]
    rintro q ⟨hqT, hqC⟩
    refine ⟨hqT, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
    have hfix : ∀ y ∈ V, q * y * q⁻¹ = y := fun y hy => by
      rw [(Subgroup.mem_centralizer_iff.mp hqC y hy).symm, mul_inv_cancel_right]
    constructor
    · intro hx
      rw [hfix x (hU''V hx)]
      exact hx
    · intro hx
      have hxV : x ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV hqT) x).mpr (hU''V hx)
      rw [hfix x hxV] at hx
      exact hx

  have hΩ : omegaOneCenterOf (T ⊓ Subgroup.normalizer (U'' : Set G)) ≤ U'' := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨⟨hzN, hzC⟩, hz2⟩
    have hzC' : z ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        Subgroup.mem_centralizer_iff.mp hzC q (hQN hq)
    have hzQ : z ∈ pCoreOf 2 (L ⊔ T) :=
      h.toHyp5_0_1.charTwo_sup ⟨(le_sup_right : T ≤ L ⊔ T) hzN.1, hzC'⟩
    have hzZ : z ∈ centerOf (pCoreOf 2 (L ⊔ T)) := ⟨hzQ, hzC'⟩
    have hzV : z ∈ V := hVΩ (Subgroup.subset_closure ⟨hzZ, hz2⟩)
    have hzs : (sN : G) * z * (sN : G)⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp hzC _ hsN, mul_inv_cancel_right]
    have hw : (sN : G) * z * (sN : G)⁻¹ ∈ V := by rw [hzs]; exact hzV
    have hfixz : twistActCh6 2 (uMat t₀) (e ⟨z, hzV⟩) =
        (e ⟨z, hzV⟩ : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hes ⟨z, hzV⟩ hw]
      congr 2
      exact Subtype.ext hzs
    have h0 := ht₀Y _ (e ⟨z, hzV⟩).2 hfixz
    refine (hmemU'' ⟨z, hzV⟩).mpr ?_
    rw [h0, mul_zero, map_zero]

  have hCVT : ∀ v : ↥V, (v : G) ∈ Subgroup.centralizer (T : Set G) → (v : G) ∈ U'' := by
    intro v hv
    have hvS : (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le inf_le_left hv
    obtain ⟨h01, h10, h11⟩ := hline v hvS
    refine (hmemU'' v).mpr ?_
    have h0 : detPolarCh6 v₁ (e v) = 0 := by
      have e01 : (e v : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := h01
      have e10 : (e v : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h10
      have e11 : (e v : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := h11
      simp only [detPolarCh6, e01, e10, e11, hg11]
      ring
    rw [h0, mul_zero, map_zero]
  have hTp : IsPGroup 2 (autOn T V) :=
    (h.sylow.1.comap_of_injective (Subgroup.normalizer (V : Set G)).subtype
      Subtype.coe_injective).map _
  have htop : (⊤ : Subgroup ↥V) ≠ ⊥ := by
    intro h0
    apply h.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥V) ∈ (⊥ : Subgroup ↥V) := h0 ▸ Subgroup.mem_top _
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  obtain ⟨v, -, hv1, hvfix⟩ := exists_fixed_of_two hTp (M := (⊤ : Subgroup ↥V))
    (fun v _ => sq_eq_one_of_coord hYinj v) htop (fun _ _ _ _ => trivial)
  have hvT : (v : G) ∈ Subgroup.centralizer (T : Set G) :=
    (mem_centralizer_iff_autOn hTV v).mpr hvfix
  have hvU'' : (v : G) ∈ U'' := hCVT v hvT
  have hv1' : (v : G) ≠ 1 := fun h' => hv1 (Subtype.ext h')
  have hZU : V ⊓ Subgroup.centralizer (T : Set G) ⊓ U'' ≠ ⊥ := by
    intro h0
    have hmem : (v : G) ∈ V ⊓ Subgroup.centralizer (T : Set G) ⊓ U'' := ⟨⟨v.2, hvT⟩, hvU''⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hv1' hmem
  have hU''ne : U'' ≠ ⊥ := fun h0 => hv1' (by
    have := hvU''
    rwa [h0, Subgroup.mem_bot] at this)
  have hU0 : U ≠ ⊥ := fun h0 => hU''ne (by rw [hU'', h0, Subgroup.map_bot])
  have hCUM : ¬ Subgroup.centralizer (U : Set G) ≤ M :=
    (inf_eq_inf_normalizer_of_isTISetIn hTI hNV hU0 hUV
      (Subgroup.centralizer_le_normalizer _)).2.mpr hCU
  have hCU''M : ¬ Subgroup.centralizer (U'' : Set G) ≤ M := by
    intro hle
    apply hCUM
    intro c hc
    have hc' : (ℓN : G) * c * (ℓN : G)⁻¹ ∈ Subgroup.centralizer (U'' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      have hcu := Subgroup.mem_centralizer_iff.mp hc u hu
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      calc (ℓN : G) * u * (ℓN : G)⁻¹ * ((ℓN : G) * c * (ℓN : G)⁻¹) =
          (ℓN : G) * (u * c) * (ℓN : G)⁻¹ := by group
        _ = (ℓN : G) * (c * u) * (ℓN : G)⁻¹ := by rw [hcu]
        _ = (ℓN : G) * c * (ℓN : G)⁻¹ * ((ℓN : G) * u * (ℓN : G)⁻¹) := by group
    have hm := hle hc'
    have e1 : c = (ℓN : G)⁻¹ * ((ℓN : G) * c * (ℓN : G)⁻¹) * (ℓN : G) := by group
    rw [e1]
    exact M.mul_mem (M.mul_mem (M.inv_mem hℓM) hm) hℓM
  have hmQ'' : mQuot V U'' = 1 := by
    have hVmap : V.map (MulAut.conj (ℓN : G)).toMonoidHom = V :=
      map_conj_eq_of_mem_normalizer_ch6 hℓV
    have h1 : U''.relIndex V = U.relIndex V := by
      have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (ℓN : G)).toMonoidHom) U V
        (MulAut.conj (ℓN : G)).injective
      rw [hVmap] at this
      exact this
    unfold mQuot
    rw [h1, hrel]
    simp
  have hres : twoPrimeResidual (M ⊓ Subgroup.centralizer (U'' : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := by
    have hle : twoPrimeResidual (M ⊓ Subgroup.centralizer (U'' : Set G)) ≤
        M ⊓ Subgroup.centralizer (U'' : Set G) :=
      iInf₂_le _ ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; norm_num⟩
    exact hle.trans (le_inf inf_le_left
      (h.inf_centralizer_le_of_hyperplane_ch6 hH11 horth hTI hNV hU''V hmQ''))
  have hΓ : U'' ∈ E6.gammaE64 V M := ⟨hU''V, hU''ne, hCU''M, hres⟩
  exact hE610 G T M V U'' hE hΓ hmQ'' (Or.inl hZU) hΩ

end Hyp611

end CFSG.Quasithin.H13
