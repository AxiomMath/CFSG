module

public import CFSG.GH74.GLS.LU.Local.FiveStdRed2
public import CFSG.GH74.GLS.LU.Local.FiveStdOf
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMap

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.FiveStd.Mat CFSG.GH74.L5U5
  CFSG.GH74.GLS.Stage2.Final

theorem orderOf_eq_of_isConj' {G : Type} [Group G] {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

omit [Finite G] in
theorem exists_pair (hb : baseCheck = true) {S₀ : Sylow 2 G}
    (hset : ((S₀ : Subgroup G) : Set G) = S st.ι S0) {t'' u'' : G}
    (hsyl : LUSyl G st.z S₀ st.K₁ st.K₂ t'' u'') :
    ∃ tE uE : E, st.ι tE = t'' ∧ st.ι uE = u'' ∧ tE ∈ S0 ∧ uE ∈ S0 ∧ pairCond tE uE = true := by
  obtain ⟨-, hV1, hV2, hV0, -⟩ := baseCheck_spec hb
  have ht : t'' ∈ ((S₀ : Subgroup G) : Set G) := hsyl.t_mem
  have hu : u'' ∈ ((S₀ : Subgroup G) : Set G) := hsyl.u_mem
  rw [hset] at ht hu
  obtain ⟨tE, htE, rfl⟩ := mem_S.1 ht
  obtain ⟨uE, huE, rfl⟩ := mem_S.1 hu
  have hvt : validE tE = true := hV0 _ htE
  have hvu : validE uE = true := hV0 _ huE
  refine ⟨tE, uE, rfl, rfl, htE, huE, ?_⟩
  have hK1mem : ∀ x ∈ K1l, st.ι x ∈ st.K₁ := fun x hx => by
    have : st.ι x ∈ S st.ι K1l := mem_S.2 ⟨x, hx, rfl⟩
    rw [← st.hK₁] at this
    exact this
  have hsw : swapsK tE = true := by
    unfold swapsK
    rw [List.all_eq_true]
    intro x hx
    have hxv : validE x = true := hV1 x hx
    refine (st.model.inL_iff hV2 (st.model.valid_conjE hvt hxv)).2 ?_
    rw [st.model.map_conjE hvt hxv]
    have h2 : (MulAut.conj (st.ι tE)).toMonoidHom (st.ι x) ∈ st.K₂ := by
      rw [← hsyl.t_swap]
      exact Subgroup.mem_map_of_mem _ (hK1mem x hx)
    have h3 : st.ι tE * st.ι x * (st.ι tE)⁻¹ ∈ S st.ι K2l := by
      rw [← st.hK₂]
      exact h2
    exact h3
  have hnk : normK1 uE = true := by
    unfold normK1
    rw [List.all_eq_true]
    intro x hx
    have hxv : validE x = true := hV1 x hx
    refine (st.model.inL_iff hV1 (st.model.valid_conjE hvu hxv)).2 ?_
    rw [st.model.map_conjE hvu hxv]
    have h2 := ((Subgroup.mem_normalizer_iff.1 hsyl.u_norm) (st.ι x)).1 (hK1mem x hx)
    rw [← st.hK₁] at *
    exact h2
  have hot : ordE tE = 2 :=
    st.model.ordE_of_orderOf hvt ((orderOf_eq_of_isConj' hsyl.t_conj).symm.trans hsyl.z_inv)
      (by norm_num) (by norm_num)
  have hou : ordE uE = 2 := st.model.ordE_of_orderOf hvu hsyl.u_ord (by norm_num) (by norm_num)
  have hne : uE ≠ zE := fun h => hsyl.u_ne (by rw [h])
  have hcm : commE tE uE = true := (st.model.commE_iff hvt hvu).2 hsyl.ut.symm
  unfold pairCond
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨⟨List.contains_iff_mem.2 (List.mem_filter.2 ⟨htE, hsw⟩),
    List.contains_iff_mem.2 (List.mem_filter.2 ⟨huE, hnk⟩)⟩, hot⟩, hou⟩, hne⟩, hcm⟩

end FiveStdSetting

theorem charP_five_of_card (F : Type) [Field F] [Finite F] (hF5 : Nat.card F = 5) : CharP F 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF5)

theorem cjL_inv_eq {G : Type} [Group G] {g : G} {K : Subgroup G} (h : cjL g K = K) : cjL g⁻¹ K = K := by
  have := cjL_cjL g⁻¹ g K
  rw [h, inv_mul_cancel, cjL_one] at this
  exact this

theorem fiveModelLeaf_of_check (hc : fiveStdCheck = true) : FiveModelLeaf := by
  intro Gs _ _ hL z' S' K₁' K₂' t' u' hcomps hsyl
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
  have hF5 : Nat.card F = 5 := by simpa using hF
  have : CharP F 5 := charP_five_of_card F hF5
  have e' : Gs ≃* PG (ModelData.lin F) := e
  obtain ⟨hb, hs, hd, hcov, hreps⟩ := fiveStdCheck_spec hc
  obtain ⟨S₀, Ψ, hset, hcen, hsup, hΨz, hΨS, hK1, hK2⟩ :=
    exists_psi_comps hF5 hc hL e' S' z' K₁' K₂' hcomps hsyl.z_inv ((centerIs_iff _ _).1 hsyl.z_cen)
  let st := fiveStdSetting (F := F) hF5
  have hz : st.z = yP (ModelData.lin F) := ιF_zE
  have hsyl0 := CFSG.GH74.GLS.Stage2.Final.ModelLUT.luSyl_map Ψ hΨS.symm hsyl
  rw [hΨz, hK1, hK2] at hsyl0
  have hsyl' : LUSyl (PG (ModelData.lin F)) st.z S₀ st.K₁ st.K₂ (Ψ t') (Ψ u') := by
    rw [hz]
    exact hsyl0
  obtain ⟨tE, uE, htE, huE, htS0, huS0, hpair⟩ := st.exists_pair hb hset hsyl'
  have hpmem : (tE, uE) ∈ Pairs := by
    unfold Pairs
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
    exact ⟨tE, htS0, uE, ⟨huS0, hpair⟩, rfl⟩
  obtain ⟨-, -, hcover⟩ := coverCheck_spec hcov
  obtain ⟨r, hr, g, hg, hgr⟩ := hcover _ hpmem
  have hgC := (List.mem_filter.1 hg).1
  have hgs : g.s = false := by simpa using (List.mem_filter.1 hg).2
  have hgv : validE g = true := (mem_Cs_iff g).1 hgC
  obtain ⟨hb1, hb2⟩ := st.hblock g hgC hgs
  have hgt : conjE g r.1 = tE := (Prod.mk.inj hgr).1
  have hgu : conjE g r.2 = uE := (Prod.mk.inj hgr).2
  have hrv1 : validE r.1 = true := by
    obtain ⟨-, -, -, hV0, -⟩ := baseCheck_spec hb
    obtain ⟨-, hpc, -⟩ := coverCheck_spec hcov
    have := hpc r hr
    unfold pairCond at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩ := this
    exact hV0 _ (List.mem_filter.1 (List.contains_iff_mem.1 h1)).1
  have hrv2 : validE r.2 = true := by
    obtain ⟨-, -, -, hV0, -⟩ := baseCheck_spec hb
    obtain ⟨-, hpc, -⟩ := coverCheck_spec hcov
    have := hpc r hr
    unfold pairCond at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩ := this
    exact hV0 _ (List.mem_filter.1 (List.contains_iff_mem.1 h2)).1
  let Φ₂ : Gs ≃* PG (ModelData.lin F) := Ψ.trans (MulAut.conj (st.ι g)⁻¹)
  have hycomm : yP (ModelData.lin F) * st.ι g = st.ι g * yP (ModelData.lin F) :=
    ιF_comm_yP hgv
  have hΦz : Φ₂ z' = st.z := by
    show (st.ι g)⁻¹ * Ψ z' * (st.ι g)⁻¹⁻¹ = st.z
    rw [hΨz, hz, inv_inv, mul_assoc, hycomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hΦK1 : K₁'.map Φ₂.toMonoidHom = st.K₁ := by
    rw [map_trans_conj, hK1]
    exact cjL_inv_eq hb1
  have hΦK2 : K₂'.map Φ₂.toMonoidHom = st.K₂ := by
    rw [map_trans_conj, hK2]
    exact cjL_inv_eq hb2
  have hΦt : Φ₂ t' = st.ι r.1 := by
    show (st.ι g)⁻¹ * Ψ t' * (st.ι g)⁻¹⁻¹ = st.ι r.1
    rw [← htE, ← hgt, st.model.map_conjE hgv hrv1, inv_inv]
    group
  have hΦu : Φ₂ u' = st.ι r.2 := by
    show (st.ι g)⁻¹ * Ψ u' * (st.ι g)⁻¹⁻¹ = st.ι r.2
    rw [← huE, ← hgu, st.model.map_conjE hgv hrv2, inv_inv]
    group
  let st₂ := st.ofEquiv Φ₂.symm
  have hr' : (r.1, r.2) ∈ reps := by
    rw [Prod.mk.eta]
    exact hr
  have hfacts := st₂.facts_of_rep hc hr' S'
  have e1 : st₂.z = z' := by
    show Φ₂.symm (st.ι zE) = z'
    rw [MulEquiv.symm_apply_eq]
    exact hΦz.symm
  have e2 : st₂.K₁ = K₁' := by
    show st.K₁.map Φ₂.symm.toMonoidHom = K₁'
    rw [← hΦK1]
    exact CFSG.GH74.GLS.Stage2.Final.ModelLUT.map_symm_map Φ₂ K₁'
  have e3 : st₂.K₂ = K₂' := by
    show st.K₂.map Φ₂.symm.toMonoidHom = K₂'
    rw [← hΦK2]
    exact CFSG.GH74.GLS.Stage2.Final.ModelLUT.map_symm_map Φ₂ K₂'
  have e4 : st₂.ι r.1 = t' := by
    show Φ₂.symm (st.ι r.1) = t'
    rw [MulEquiv.symm_apply_eq]
    exact hΦt.symm
  have e5 : st₂.ι r.2 = u' := by
    show Φ₂.symm (st.ι r.2) = u'
    rw [MulEquiv.symm_apply_eq]
    exact hΦu.symm
  have key : ∀ (z : Gs) (K₁ K₂ : Subgroup Gs) (t u : Gs), z = z' → K₁ = K₁' → K₂ = K₂' → t = t' →
      u = u' → FiveModelFacts z S' K₁ K₂ t u → FiveModelFacts z' S' K₁' K₂' t' u' := by
    rintro _ _ _ _ _ rfl rfl rfl rfl rfl h
    exact h
  exact key _ _ _ _ _ e1 e2 e3 e4 e5 hfacts

theorem fiveModelBaseLeaf_of_check (hc : fiveStdCheck = true) : FiveModelBaseLeaf := by
  intro Gs _ _ hL z' S' hz'c hz'ord
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
  have hF5 : Nat.card F = 5 := by simpa using hF
  have : CharP F 5 := charP_five_of_card F hF5
  have e' : Gs ≃* PG (ModelData.lin F) := e
  obtain ⟨hb, hs, hd, hcov, hreps⟩ := fiveStdCheck_spec hc
  obtain ⟨S₀, Ψ, hset, hcen, hsup, hΨz, hΨS⟩ :=
    exists_psi hF5 hb e' S' z' hz'ord ((centerIs_iff _ _).1 hz'c)
  let st := fiveStdSetting (F := F) hF5
  have h2 : (2 : F) ≠ 0 := two_ne_zero_F
  have h5 : 5 ≤ Nat.card F := by rw [hF5]
  refine ⟨?_, ?_, ?_⟩
  · apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
    rw [ModelLT.layerTimesSylow_map Ψ z' S', hΨz, hΨS, ModelLT.centralizer_map_equiv Ψ z', hΨz]
    unfold layerTimesSylow
    rw [layer_map_eq (ModelData.lin F) h2 (ModelH2.h2_quasisimple_lin F h5)]
    exact hsup
  · have h1 := Nat.card_congr (ModelLT.centralizerEquiv Ψ z').toEquiv
    rw [hΨz] at h1
    rw [h1]
    have hz : st.z = yP (ModelData.lin F) := ιF_zE
    have h3 := st.card_Cz hb
    rw [hz] at h3
    exact h3
  · have h1 := oddCore_card_one hL S' z' hz'ord hz'c
    have h3 : pPrimeCore 2 ↥(centralizer ({z'} : Set Gs)) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    show (pPrimeCore 2 ↥(Cz z')).map (Cz z').subtype = ⊥
    rw [h3, Subgroup.map_bot]

end CFSG.GH74.GLS.LU.Local.Five
