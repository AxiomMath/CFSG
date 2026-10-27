module

public import CFSG.GH74.GLS.Stage2.Final.ModelPGLLin
public import CFSG.GH74.GLS.Stage2.Final.ModelIVKFam

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

theorem Ez_map_equiv {K G : Type} [Group K] [Group G] (Φ : K ≃* G) (z : K) :
    (IVK.Ez z).map Φ.toMonoidHom = IVK.Ez (Φ z) := by
  have h1 : ∀ x : K, IVK.Ez x = CFSG.GH74.GLS.layerTimesSylow x ⊥ := fun x => by
    unfold CFSG.GH74.GLS.layerTimesSylow IVK.Ez
    rw [sup_bot_eq]
  have h2 : ∀ x : G, IVK.Ez x = CFSG.GH74.GLS.layerTimesSylow x ⊥ := fun x => by
    unfold CFSG.GH74.GLS.layerTimesSylow IVK.Ez
    rw [sup_bot_eq]
  rw [h1, h2, ModelLT.layerTimesSylow_map Φ z ⊥, Subgroup.map_bot]

theorem map_conj_comm {K G : Type} [Group K] [Group G] (Φ : K ≃* G) (t : K) (E : Subgroup K) :
    (E.map (MulAut.conj t).toMonoidHom).map Φ.toMonoidHom =
      (E.map Φ.toMonoidHom).map (MulAut.conj (Φ t)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem Dat410.map_equiv {K G : Type} [Group K] [Group G] (Φ : K ≃* G) {q : ℕ} {z : K}
    {S : Subgroup K} {t w : K} {E₁ E₂ : Subgroup K} (h : Dat410 q z S t w E₁ E₂) :
    Dat410 q (Φ z) (S.map Φ.toMonoidHom) (Φ t) (Φ w) (E₁.map Φ.toMonoidHom)
      (E₂.map Φ.toMonoidHom) := by
  have hinj : Function.Injective Φ.toMonoidHom := Φ.injective
  have hconj : ∀ {a b : K}, IsConj a b → IsConj (Φ a) (Φ b) := fun {a b} hab =>
    MonoidHom.map_isConj Φ.toMonoidHom hab
  have hEz := Ez_map_equiv Φ z
  refine
    { t_mem := Subgroup.mem_map_of_mem Φ.toMonoidHom h.t_mem
      w_mem := Subgroup.mem_map_of_mem Φ.toMonoidHom h.w_mem
      t_ord := by rw [MulEquiv.orderOf_eq]; exact h.t_ord
      w_ord := ?_
      comm := by rw [← map_mul, ← map_mul, h.comm]
      prod := ?_
      inter := ?_
      t_conj := hconj h.t_conj
      Ez_eq := ?_
      E₂_eq := ?_
      sl2 := ?_
      inter_E := ?_
      comm_E := ?_
      norm_E := ?_
      classes := ?_
      tz_ne := ?_
      E_fus := ?_
      pgl := ?_
      w_fus := ?_ }
  · rcases h.w_ord with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [MulEquiv.orderOf_eq]; exact h1
  · have := congrArg (Subgroup.map Φ.toMonoidHom) h.prod
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hEz] at this
    exact this
  · have := congrArg (Subgroup.map Φ.toMonoidHom) h.inter
    rw [Subgroup.map_inf _ _ _ hinj, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      hEz, Subgroup.map_bot] at this
    exact this
  · rw [← hEz, h.Ez_eq, Subgroup.map_sup]
  · rw [h.E₂_eq, map_conj_comm]
  · obtain ⟨F₀, iF, fF, hP, ⟨e⟩⟩ := h.sl2
    exact ⟨F₀, iF, fF, hP, ⟨(MulEquiv.subgroupMap Φ E₁).symm.trans e⟩⟩
  · have := congrArg (Subgroup.map Φ.toMonoidHom) h.inter_E
    rw [Subgroup.map_inf _ _ _ hinj, MonoidHom.map_zpowers] at this
    exact this
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show Φ a * Φ b = Φ b * Φ a
    rw [← map_mul, ← map_mul, h.comm_E a ha b hb]
  · have h1 := Subgroup.map_equiv_normalizer_eq (E₁ : Subgroup K) Φ
    have := congrArg (Subgroup.map Φ.toMonoidHom) h.norm_E
    rw [Subgroup.map_inf _ _ _ hinj, Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj,
      MonoidHom.map_zpowers, h1, hEz] at this
    exact this
  · intro x hx
    obtain ⟨y, rfl⟩ := Φ.surjective x
    have hy : orderOf y = 2 := by rw [← MulEquiv.orderOf_eq Φ]; exact hx
    rcases h.classes y hy with h1 | h1
    · exact Or.inl (hconj h1)
    · refine Or.inr ?_
      have := hconj h1
      rwa [map_mul] at this
  · intro hc
    apply h.tz_ne
    have := isConj_of_equiv Φ (a := z) (b := t * z) (by rw [map_mul]; exact hc)
    exact this
  · intro x hx hx2 hxz
    rw [← hEz] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy2 : orderOf y = 2 := by rw [← MulEquiv.orderOf_eq Φ]; exact hx2
    have hyz : y ≠ z := fun h' => hxz (by subst h'; rfl)
    have := hconj (h.E_fus y hy hy2 hyz)
    rwa [map_mul] at this
  · intro hw Ei hEi
    have hw' : w ≠ 1 := fun h' => hw (by rw [h', map_one])
    have hEi' : ∃ Ei' ∈ ({E₁, E₂} : Set (Subgroup K)), Ei = Ei'.map Φ.toMonoidHom := by
      rcases hEi with rfl | rfl
      · exact ⟨E₁, Or.inl rfl, rfl⟩
      · exact ⟨E₂, Or.inr rfl, rfl⟩
    obtain ⟨Ei', hEi'm, rfl⟩ := hEi'
    exact pgl_quot_transport Φ rfl rfl rfl (h.pgl hw' Ei' hEi'm)
  · intro hw
    have hw' : w ≠ 1 := fun h' => hw (by rw [h', map_one])
    obtain ⟨h1, h2⟩ := h.w_fus hw'
    refine ⟨?_, ?_⟩
    · have := hconj h1
      rwa [map_mul] at this
    · intro x hx hx2
      obtain ⟨hxS, hxE⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.1 hxS
      have hyE : y ∈ IVK.Ez z := by
        rw [← hEz] at hxE
        obtain ⟨y', hy', hy'x⟩ := Subgroup.mem_map.1 hxE
        have : y' = y := Φ.injective hy'x
        rw [← this]
        exact hy'
      have hy2 : orderOf (y * w) = 2 := by
        rw [← MulEquiv.orderOf_eq Φ, map_mul]
        exact hx2
      have := hconj (h2 y (Subgroup.mem_inf.2 ⟨hyS, hyE⟩) hy2)
      rwa [map_mul] at this

theorem isCentralInvolution_map {K G : Type} [Group K] [Group G] [Finite K] [Finite G] (Φ : K ≃* G)
    {y : K} (hy : CFSG.GH74.IsCentralInvolution y) : CFSG.GH74.IsCentralInvolution (Φ y) := by
  obtain ⟨h2, S, hyS, hyc⟩ := hy
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact h2, sylowMap Φ S, ?_, ?_⟩
  · rw [coe_sylowMap]
    exact Subgroup.mem_map_of_mem _ hyS
  · rw [coe_sylowMap]
    rintro _ ⟨s, hs, rfl⟩
    show Φ s * Φ y = Φ y * Φ s
    rw [← map_mul, ← map_mul, hyc s hs]

theorem exists_Phi_sylow {K G : Type} [Group K] [Group G] [Finite K] [Finite G] (e : K ≃* G)
    {S₀ : Sylow 2 G} {y : G} (hy : orderOf y = 2) (hc : CenterIs (S₀ : Subgroup G) y)
    (P : Sylow 2 K) {z : K} (hz : orderOf z = 2) (hzP : z ∈ (P : Subgroup K))
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) :
    ∃ Φ : K ≃* G, (P : Subgroup K).map Φ.toMonoidHom = (S₀ : Subgroup G) ∧ Φ z = y := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₀ P
  refine ⟨Φ, hΦ, ?_⟩
  have hzS : Φ z ∈ (S₀ : Subgroup G) := by
    rw [← hΦ]
    exact Subgroup.mem_map_of_mem _ hzP
  have hzc' : ∀ s ∈ (S₀ : Subgroup G), s * Φ z = Φ z * s := by
    intro s hs
    rw [← hΦ] at hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
    show Φ x * Φ z = Φ z * Φ x
    rw [← map_mul, ← map_mul, hzc x hx]
  have hmem := (hc _).1 ⟨hzS, hzc'⟩
  exact eq_of_mem_zpowers_of_orderOf_two hy (by rw [MulEquiv.orderOf_eq]; exact hz) hmem

theorem ivk410_of_model {K G : Type} [Group K] [Finite K] [Group G] [Finite G] (e : K ≃* G)
    {q : ℕ} {S₀ : Sylow 2 G} {y : G} (hy : orderOf y = 2) (hc : CenterIs (S₀ : Subgroup G) y)
    {t w : G} {E₁ E₂ : Subgroup G} (hD : Dat410 q y (S₀ : Subgroup G) t w E₁ E₂)
    (hiff : w = 1 ↔ IVK.IsPSp4 K q) (hcen : ∀ x : G, CFSG.GH74.IsCentralInvolution x → IsConj y x)
    (P : Sylow 2 K) {z : K} (hz : orderOf z = 2) (hzP : z ∈ (P : Subgroup K))
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) :
    ∃ (t' w' : K) (E₁' E₂' : Subgroup K), Dat410 q z (P : Subgroup K) t' w' E₁' E₂' ∧
      (w' = 1 ↔ IVK.IsPSp4 K q) ∧ ∀ y' : K, CFSG.GH74.IsCentralInvolution y' → IsConj z y' := by
  obtain ⟨Φ, hΦS, hΦz⟩ := exists_Phi_sylow e hy hc P hz hzP hzc
  have hzr : Φ.symm y = z := by rw [← hΦz]; simp
  have hPr : (S₀ : Subgroup G).map Φ.symm.toMonoidHom = (P : Subgroup K) := by
    rw [← hΦS, Subgroup.map_map]
    have : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id K := by ext x; simp
    rw [this, Subgroup.map_id]
  have hD' := Dat410.map_equiv Φ.symm hD
  rw [hzr, hPr] at hD'
  refine ⟨Φ.symm t, Φ.symm w, E₁.map Φ.symm.toMonoidHom, E₂.map Φ.symm.toMonoidHom, hD',
    (MulEquiv.map_eq_one_iff Φ.symm).trans hiff, fun y' hy' => ?_⟩
  have h1 := hcen _ (isCentralInvolution_map Φ hy')
  rw [← hΦz] at h1
  exact isConj_of_equiv Φ h1

theorem dP_dRefl_ne_one {F : Type} [Field F] {M : ModelData F} (h2 : (2 : F) ≠ 0)
    (hd : dRefl F ∈ M.U2) :
    dP M (dRefl F) hd ≠ 1 := by
  intro h
  have h' : mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ =
      mkP M ⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ := by
    rw [show (⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ : ↥M.K4) = 1 from
      Subtype.ext diagGL_one, map_one]
    exact h
  obtain ⟨c, h1, -⟩ := (mkP_diag_eq_iff _ _).1 h'
  apply dRefl_not_scalar h2 c⁻¹
  rw [← sc2_inv]
  have h1' : sc2 c * dRefl F = 1 := h1.symm
  exact eq_inv_of_mul_eq_one_right h1'

@[expose] def UniPglStmt : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2), p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 1 →
    PglStmt (ModelData.uni hF) (p ^ f) (dP _ (dRefl F) dRefl_mem_uni)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem ivk_4_10_of_uniPgl (hU : UniPglStmt) : IVK.IVK_4_10 := by
  intro K _ _ q hq h5 hK P z hzP hz2 hzc
  rcases cases_IsSp4L4U4 hq h5 hK with ⟨F, iF, fF, hqF, hG, hZ, ⟨e⟩⟩ |
      ⟨F, iF, fF, hqF, h4, hG, hZ, ⟨e⟩⟩ |
      ⟨F, iF, fF, p, f, hfp, hcp, hF, hqpf, h4, hG, hZ, ⟨e⟩⟩
  ·
    subst hqF
    have h2 := hG.two_ne_zero
    obtain ⟨S₀, hc, hD⟩ := sp410 h2 h5
    have hpsp : IVK.IsPSp4 K (Nat.card F) := ⟨F, iF, fF, rfl, ⟨e.trans (ModelSp.spEquiv F).symm⟩⟩
    obtain ⟨t', w', E₁', E₂', hD', hw, hcen⟩ := ivk410_of_model e (orderOf_yP _ h2)
      hc hD ⟨fun _ => hpsp, fun _ => rfl⟩
      (fun x hx => central_inv_conj (orderOf_yP _ h2) hc hx) P hz2 hzP hzc
    exact ⟨t', w', E₁', E₂', hD'.t_mem, hD'.w_mem, hD'.t_ord, hD'.w_ord, hD'.comm, hD'.prod,
      hD'.inter, hD'.t_conj, hD'.Ez_eq, hD'.E₂_eq, hD'.sl2, hD'.inter_E, hD'.comm_E, hD'.norm_E, hw,
      hD'.classes, hD'.tz_ne, hD'.E_fus, hD'.pgl, hD'.w_fus, hcen⟩
  ·
    subst hqF
    have h2 := hG.two_ne_zero
    obtain ⟨S₀, hc, hD⟩ := lin410 h2 h5 h4 (pglStmt_lin h2 h5 h4)
    have hL : IVK.IsLnEps 4 K 1 (Nat.card F) := Or.inl ⟨rfl, F, iF, fF, rfl, ⟨e⟩⟩
    have hnp : ¬ IVK.IsPSp4 K (Nat.card F) := fun hp => (ivk_PSp4_ne_LU K _ hp).1 hL
    obtain ⟨t', w', E₁', E₂', hD', hw, hcen⟩ := ivk410_of_model e (orderOf_yP _ h2)
      hc hD
      ⟨fun h => absurd h (dP_dRefl_ne_one h2 _), fun h => absurd h hnp⟩
      (fun x hx => central_inv_conj (orderOf_yP _ h2) hc hx) P hz2 hzP hzc
    exact ⟨t', w', E₁', E₂', hD'.t_mem, hD'.w_mem, hD'.t_ord, hD'.w_ord, hD'.comm, hD'.prod,
      hD'.inter, hD'.t_conj, hD'.Ez_eq, hD'.E₂_eq, hD'.sl2, hD'.inter_E, hD'.comm_E, hD'.norm_E, hw,
      hD'.classes, hD'.tz_ne, hD'.E_fus, hD'.pgl, hD'.w_fus, hcen⟩
  ·
    subst hqpf
    have h2 := hG.two_ne_zero
    have hp2 : p ≠ 2 := by
      intro hp
      apply h2
      have h0 : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
      rw [hp] at h0
      exact_mod_cast h0
    obtain ⟨S₀, hc, hD⟩ := uni410 hF hp2 h5 h4 (hU F p f hF hp2 h5 h4)
    have hL : IVK.IsLnEps 4 K (-1) (p ^ f) := Or.inr ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩
    have hnp : ¬ IVK.IsPSp4 K (p ^ f) := fun hp => (ivk_PSp4_ne_LU K _ hp).2 hL
    obtain ⟨t', w', E₁', E₂', hD', hw, hcen⟩ := ivk410_of_model e (orderOf_yP _ h2)
      hc hD
      ⟨fun h => absurd h (dP_dRefl_ne_one h2 _), fun h => absurd h hnp⟩
      (fun x hx => central_inv_conj (orderOf_yP _ h2) hc hx) P hz2 hzP hzc
    exact ⟨t', w', E₁', E₂', hD'.t_mem, hD'.w_mem, hD'.t_ord, hD'.w_ord, hD'.comm, hD'.prod,
      hD'.inter, hD'.t_conj, hD'.Ez_eq, hD'.E₂_eq, hD'.sl2, hD'.inter_E, hD'.comm_E, hD'.norm_E, hw,
      hD'.classes, hD'.tz_ne, hD'.E_fus, hD'.pgl, hD'.w_fus, hcen⟩

end CFSG.GH74.GLS.Stage2.Final
