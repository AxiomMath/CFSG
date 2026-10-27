module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Cent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem isEA_of_isFourSubgroup {X : Type} [Group X] {U : Subgroup X} (hU : IVK.IsFourSubgroup U) :
    Dihedral.IsEA U := by
  obtain ⟨hEA, -⟩ := hU
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
    rwa [pow_two] at this
  · have := (IsMulCommutative.is_comm (M := ↥U)).comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this

theorem isFourSubgroup_of_isEA {X : Type} [Group X] {U : Subgroup X} (hU : Dihedral.IsEA U)
    (hc : Nat.card U = 4) : IVK.IsFourSubgroup U := by
  refine ⟨?_, hc⟩
  have hcomm : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext ((hU a a.2).2 b b.2)⟩⟩
  exact { toIsMulCommutative := hcomm
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => by
            have := (hU g g.2).1
            exact Subtype.ext (by simpa [pow_two] using this)) }

variable [Finite G]

@[expose] noncomputable def timgP (h : SitFacts x Kb e N T) (V : Subgroup G) : Subgroup (MulAut ↥Kb) :=
  ((V.subgroupOf (Pg x Kb T)).map (PgEquiv h).toMonoidHom).map N.P.subtype

theorem mem_timgP (h : SitFacts x Kb e N T) {V : Subgroup G} (hV : V ≤ Pg x Kb T)
    {a : MulAut ↥Kb} : a ∈ timgP h V ↔ ∃ g ∈ V, phig x Kb g = a := by
  constructor
  · rintro ⟨y, ⟨g', hg', rfl⟩, rfl⟩
    exact ⟨g'.1, hg', (PgEquiv_apply h g').symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨PgEquiv h ⟨g, hV hg⟩, ⟨⟨g, hV hg⟩, hg, rfl⟩, PgEquiv_apply h _⟩

theorem timgP_le (h : SitFacts x Kb e N T) (V : Subgroup G) : timgP h V ≤ N.P := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem card_timgP (h : SitFacts x Kb e N T) {V : Subgroup G} (hV : V ≤ Pg x Kb T) :
    Nat.card (timgP h V) = Nat.card V := by
  unfold timgP
  rw [Subgroup.card_map_of_injective N.P.subtype_injective,
    Subgroup.card_map_of_injective (f := (PgEquiv h).toMonoidHom) (PgEquiv h).injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv

theorem isEA_timgP (h : SitFacts x Kb e N T) {V : Subgroup G} (hV : V ≤ Pg x Kb T)
    (hEA : IsElemAb2 V) : Dihedral.IsEA (timgP h V) := by
  have hC : ∀ g ∈ V, g ∈ Cx x := fun g hg => ((mem_Kg x Kb).1 (hV hg).2).1
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (mem_timgP h hV).1 ha
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← phig_mul x Kb (hC g hg) (hC g hg), (hEA g hg).1, phig_one]
  · obtain ⟨g', hg', rfl⟩ := (mem_timgP h hV).1 hb
    rw [← phig_mul x Kb (hC g hg) (hC g' hg'), ← phig_mul x Kb (hC g' hg') (hC g hg),
      (hEA g hg).2 g' hg']

@[expose] noncomputable def comapP (h : SitFacts x Kb e N T) (U : Subgroup (MulAut ↥Kb)) : Subgroup G :=
  ((U.subgroupOf N.P).map (PgEquiv h).symm.toMonoidHom).map (Pg x Kb T).subtype

theorem mem_comapP (h : SitFacts x Kb e N T) {U : Subgroup (MulAut ↥Kb)} (_hU : U ≤ N.P) {g : G} :
    g ∈ comapP h U ↔ g ∈ Pg x Kb T ∧ phig x Kb g ∈ U := by
  constructor
  · rintro ⟨g', ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨((PgEquiv h).symm y).2, ?_⟩
    have := PgEquiv_apply h ((PgEquiv h).symm y)
    rw [MulEquiv.apply_symm_apply] at this
    show phig x Kb ((PgEquiv h).symm y : G) ∈ U
    rw [← this]
    exact hy
  · rintro ⟨hg, hgU⟩
    refine ⟨(PgEquiv h).symm ⟨phig x Kb g, (h.hPN _).2 ⟨g, hg, rfl⟩⟩, ⟨_, hgU, rfl⟩, ?_⟩
    have : (PgEquiv h) ⟨g, hg⟩ = ⟨phig x Kb g, (h.hPN _).2 ⟨g, hg, rfl⟩⟩ :=
      Subtype.ext (PgEquiv_apply h _)
    show (((PgEquiv h).symm ⟨phig x Kb g, _⟩ : ↥(Pg x Kb T)) : G) = g
    rw [← this]
    simp

theorem comapP_le (h : SitFacts x Kb e N T) (U : Subgroup (MulAut ↥Kb)) :
    comapP h U ≤ Pg x Kb T := by
  rintro _ ⟨g', -, rfl⟩
  exact g'.2

theorem timgP_comapP (h : SitFacts x Kb e N T) {U : Subgroup (MulAut ↥Kb)} (hU : U ≤ N.P) :
    timgP h (comapP h U) = U := by
  ext a
  rw [mem_timgP h (comapP_le h U)]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((mem_comapP h hU).1 hg).2
  · intro ha
    obtain ⟨g, hg, hga⟩ := (h.hPN a).1 (hU ha)
    exact ⟨g, (mem_comapP h hU).2 ⟨hg, hga ▸ ha⟩, hga⟩

theorem card_comapP (h : SitFacts x Kb e N T) {U : Subgroup (MulAut ↥Kb)} (hU : U ≤ N.P) :
    Nat.card (comapP h U) = Nat.card U := by
  rw [← card_timgP h (comapP_le h U), timgP_comapP h hU]

omit [Finite G] in
theorem isElemAb2_comapP (h : SitFacts x Kb e N T) [Finite G] {U : Subgroup (MulAut ↥Kb)}
    (hU : U ≤ N.P) (hEA : Dihedral.IsEA U) : IsElemAb2 (comapP h U) := by
  have hP := comapP_le h U
  have hC : ∀ g ∈ comapP h U, g ∈ Cx x := fun g hg => ((mem_Kg x Kb).1 (hP hg).2).1
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · apply h.phig_inj_P ((comapP h U).mul_mem ha ha |> hP) (Pg x Kb T).one_mem
    rw [phig_mul x Kb (hC a ha) (hC a ha), phig_one]
    have := (hEA _ ((mem_comapP h hU).1 ha).2).1
    exact this
  · apply h.phig_inj_P ((comapP h U).mul_mem ha hb |> hP) ((comapP h U).mul_mem hb ha |> hP)
    rw [phig_mul x Kb (hC a ha) (hC b hb), phig_mul x Kb (hC b hb) (hC a ha)]
    exact (hEA _ ((mem_comapP h hU).1 ha).2).2 _ ((mem_comapP h hU).1 hb).2

omit [Kb.Normal] [Finite G] in
theorem NP_le_NPt : N.P ≤ N.Pt := fun _ ha => ⟨ha.1, IVK.innAut_le_innDiagSub e ha.2⟩

omit [Kb.Normal] in
theorem NPt_index_two (hF : IVK.L2Field F) : (N.P.subgroupOf N.Pt).index = 2 := by
  have hcomap : N.P.subgroupOf N.Pt = (IVK.innAut ↥Kb).comap N.Pt.subtype := by
    ext g
    constructor
    · intro hg; exact (Subgroup.mem_subgroupOf.1 hg).2
    · intro hg; exact Subgroup.mem_subgroupOf.2 ⟨g.2.1, hg⟩
  have h2 : (IVK.innAut ↥Kb).relIndex (IVK.innDiagSub e) = 2 := IVK.innAut_relIndex_two e hF
  have hle2 : (N.P.subgroupOf N.Pt).index ≤ 2 := by
    rw [hcomap, Subgroup.index_comap, Subgroup.range_subtype]
    calc (IVK.innAut ↥Kb).relIndex N.Pt ≤ (IVK.innAut ↥Kb).relIndex (IVK.innDiagSub e) :=
          Subgroup.relIndex_le_of_le_right (fun a ha => ha.2) (by rw [h2]; norm_num)
      _ = 2 := h2
  have hne1 : (N.P.subgroupOf N.Pt).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have ht : N.t ∈ N.Pt := ⟨N.t_mem, N.t_mem_diag⟩
    have : (⟨N.t, ht⟩ : ↥N.Pt) ∈ N.P.subgroupOf N.Pt := by rw [h1]; exact Subgroup.mem_top _
    exact N.t_not_mem_inn (Subgroup.mem_subgroupOf.1 this).2
  have hne0 : (N.P.subgroupOf N.Pt).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem ip_P_trans (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d) :
    IP_P_trans (Pg x Kb T) (Qg x Kb T) (Rdg x Kb e T) := by
  intro u hu huPQ hu2 a ha b hb hau hbu
  obtain ⟨huT, huC, huD⟩ := hu
  have haC : a ∈ Cx x := ((mem_Kg x Kb).1 ha.2).1
  have hbC : b ∈ Cx x := ((mem_Kg x Kb).1 hb.2).1
  have hle : N.P ≤ N.Pt := NP_le_NPt
  obtain ⟨m₀, hm₀, ⟨e₀⟩⟩ := NP_dihedral (e := e) (N := N) h.hF h12c
  obtain ⟨-, -, -, n₁, hn₁⟩ := h12d F h.hF ↥Kb e N
  obtain ⟨m₁, hm₁, -, ⟨e₁⟩⟩ := isDihedralTwoGroup_equiv hn₁
  have hidx := NPt_index_two (e := e) (N := N) h.hF
  have hnc : ¬ IsCyclic ↥(N.P.subgroupOf N.Pt) := by
    intro hc
    have h1 : IsCyclic ↥N.P := (Subgroup.subgroupOfEquivOfLe hle).isCyclic.1 hc
    have h2 : IsCyclic (DihedralGroup (2 ^ m₀)) := e₀.isCyclic.1 h1
    exact DihedralGroup.not_isCyclic (by
      have : 2 ≤ 2 ^ m₀ := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m₀ := Nat.pow_le_pow_right (by norm_num) hm₀
      omega) h2
  have h4 : 4 ∣ 2 ^ m₁ := by
    have hc1 := Subgroup.card_mul_index (N.P.subgroupOf N.Pt)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr e₀.toEquiv, Nat.card_congr e₁.toEquiv, DihedralGroup.nat_card,
      DihedralGroup.nat_card] at hc1
    have hm1 : 2 ^ m₁ = 2 * 2 ^ m₀ := by omega
    have : 2 ∣ 2 ^ m₀ := dvd_pow_self 2 (by omega)
    rw [hm1]
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc]; ring⟩
  have hinnP : ∀ g ∈ Pg x Kb T, phig x Kb g ∈ IVK.innAut ↥Kb := fun g hg => SitFacts.phig_mem_inn hg.2
  have hDiag : ∀ g ∈ Pg x Kb T, phig x Kb (g * u) ∈ N.Pt := by
    intro g hg
    have hgC : g ∈ Cx x := ((mem_Kg x Kb).1 hg.2).1
    refine ⟨h.hTN _ (T.mul_mem hg.1 huT), ?_⟩
    rw [phig_mul x Kb hgC huC]
    exact mul_mem (IVK.innAut_le_innDiagSub e (hinnP g hg)) huD
  have hnotP : ∀ g ∈ Pg x Kb T, phig x Kb (g * u) ∉ N.P := by
    intro g hg hP'
    have hgC : g ∈ Cx x := ((mem_Kg x Kb).1 hg.2).1
    apply huPQ
    apply h.mem_PQ_of_inn ⟨huT, huC, huD⟩
    have := (NP_mem_iff.1 hP').2
    rw [phig_mul x Kb hgC huC] at this
    have h5 := mul_mem (inv_mem (hinnP g hg)) this
    simpa using h5
  have hsq : ∀ g ∈ Pg x Kb T, g * u * (g * u) = 1 → phig x Kb (g * u) * phig x Kb (g * u) = 1 := by
    intro g hg hgu
    have hgC : g ∈ Cx x := ((mem_Kg x Kb).1 hg.2).1
    rw [← phig_mul x Kb (mul_mem hgC huC) (mul_mem hgC huC), hgu, phig_one]
  let σ : ↥N.Pt := ⟨phig x Kb (a * u), hDiag a ha⟩
  let τ' : ↥N.Pt := ⟨phig x Kb (b * u), hDiag b hb⟩
  obtain ⟨p₀, hp₀, hconj⟩ := Dihedral.exists_conj_of_index_two_of_equiv e₁ h4 hidx hnc
    (σ := σ) (τ := τ') (Subtype.ext (hsq a ha hau)) (Subtype.ext (hsq b hb hbu))
    (fun hm => hnotP a ha (Subgroup.mem_subgroupOf.1 hm))
    (fun hm => hnotP b hb (Subgroup.mem_subgroupOf.1 hm))
  obtain ⟨p, hp, hpp⟩ := (h.hPN _).1 (Subgroup.mem_subgroupOf.1 hp₀)
  have hpC : p ∈ Cx x := ((mem_Kg x Kb).1 hp.2).1
  refine ⟨p, hp, ?_⟩
  have hconj' : phig x Kb p * phig x Kb (a * u) * (phig x Kb p)⁻¹ = phig x Kb (b * u) := by
    have := congrArg Subtype.val hconj
    simpa [σ, τ', hpp] using this
  have hmemP : (p * (a * u) * p⁻¹) * (b * u)⁻¹ ∈ Pg x Kb T := by
    have hnorm := (Pg_normal x Kb h.T_le_C).2 u huT p⁻¹ ((Pg x Kb T).inv_mem hp)
    have : p * (a * u) * p⁻¹ * (b * u)⁻¹ = p * a * (u * p⁻¹ * u⁻¹) * b⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem ((Pg x Kb T).mul_mem hp ha) hnorm) ((Pg x Kb T).inv_mem hb)
  have hone : phig x Kb ((p * (a * u) * p⁻¹) * (b * u)⁻¹) = phig x Kb 1 := by
    have hauC : a * u ∈ Cx x := mul_mem haC huC
    have hbuC : b * u ∈ Cx x := mul_mem hbC huC
    rw [phig_mul x Kb (mul_mem (mul_mem hpC hauC) (inv_mem hpC)) (inv_mem hbuC),
      phig_mul x Kb (mul_mem hpC hauC) (inv_mem hpC), phig_mul x Kb hpC hauC,
      phig_inv x Kb hpC, phig_inv x Kb hbuC, hconj', mul_inv_cancel, phig_one]
  have := h.phig_inj_P hmemP (Pg x Kb T).one_mem hone
  exact mul_inv_eq_one.1 this

theorem ip_cent_four (h : SitFacts x Kb e N T) (h13fa : IVK.IVK_1_3f_a)
    (h13fb : IVK.IVK_1_3f_b) : IP_cent_four T (Pg x Kb T) (Qg x Kb T) (Rdg x Kb e T) := by
  intro V hVP hV
  obtain ⟨U, hUP, hU4, hUC, hUF⟩ := h13fb F h.hF ↥Kb e N
  have hV4 : IVK.IsFourSubgroup (timgP h V) :=
    isFourSubgroup_of_isEA (isEA_timgP h hVP hV.1) (by rw [card_timgP h hVP]; exact hV.2)
  obtain ⟨g, hgPt, hgU⟩ := h13fa F h.hF ↥Kb e N U (timgP h V) hUP (timgP_le h V) hU4 hV4
  have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
  have hFD : IVK.innDiagSub e ⊓ IVK.fieldAutSub e = ⊥ := IVK.innDiagSub_inf_fieldAutSub e
  have hUFc : ∀ u ∈ U, ∀ f ∈ IVK.fieldAutSub e, u * f = f * u := by
    intro u hu f hf
    have : f ∈ Subgroup.centralizer (U : Set (MulAut ↥Kb)) := by
      rw [hUC]; exact mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 this) u hu
  have hUV : ∀ u ∈ U, g * u * g⁻¹ ∈ timgP h V := by
    intro u hu
    have : g * u * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := ⟨u, hu, by simp [MulAut.conj_apply]⟩
    rw [hgU] at this
    exact this
  have hVU : ∀ a ∈ timgP h V, g⁻¹ * a * g ∈ U := by
    intro a ha
    rw [← hgU] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    simpa [MulAut.conj_apply, mul_assoc] using hu
  let W : Subgroup G :=
    { carrier := {t | t ∈ T ∧ t ∈ Cx x ∧ g⁻¹ * phig x Kb t * g ∈ IVK.fieldAutSub e}
      one_mem' := ⟨T.one_mem, one_mem _, by rw [phig_one]; simp⟩
      mul_mem' := by
        rintro a b ⟨ha, haC, haF⟩ ⟨hb, hbC, hbF⟩
        refine ⟨T.mul_mem ha hb, mul_mem haC hbC, ?_⟩
        rw [phig_mul x Kb haC hbC]
        have : g⁻¹ * (phig x Kb a * phig x Kb b) * g =
            (g⁻¹ * phig x Kb a * g) * (g⁻¹ * phig x Kb b * g) := by group
        rw [this]; exact mul_mem haF hbF
      inv_mem' := by
        rintro a ⟨ha, haC, haF⟩
        refine ⟨T.inv_mem ha, inv_mem haC, ?_⟩
        rw [phig_inv x Kb haC]
        have : g⁻¹ * (phig x Kb a)⁻¹ * g = (g⁻¹ * phig x Kb a * g)⁻¹ := by group
        rw [this]; exact inv_mem haF }
  have hmemW : ∀ t, t ∈ W ↔ t ∈ T ∧ t ∈ Cx x ∧ g⁻¹ * phig x Kb t * g ∈ IVK.fieldAutSub e :=
    fun t => Iff.rfl
  have hVC : ∀ v ∈ V, v ∈ Cx x := fun v hv => ((mem_Kg x Kb).1 (hVP hv).2).1
  refine ⟨W, fun t ht => ht.1, ?_, ?_, ?_⟩
  ·
    ext t
    constructor
    · rintro ⟨⟨htT, htC, htF⟩, -, -, htD⟩
      refine ⟨htT, htC, ?_⟩
      have h1 : g⁻¹ * phig x Kb t * g ∈ IVK.innDiagSub e := by
        have := hD.conj_mem _ htD g⁻¹
        simpa using this
      have h2 : g⁻¹ * phig x Kb t * g ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e := ⟨h1, htF⟩
      rw [hFD] at h2
      have h3 : g⁻¹ * phig x Kb t * g = 1 := h2
      calc phig x Kb t = g * (g⁻¹ * phig x Kb t * g) * g⁻¹ := by group
        _ = 1 := by rw [h3]; group
    · rintro ⟨htT, htC, ht1⟩
      refine ⟨⟨htT, htC, by rw [ht1]; simp⟩, ?_⟩
      exact SitFacts.Qg_le_Rd ⟨htT, htC, ht1⟩
  ·
    intro v hv w hw
    obtain ⟨hwT, hwC, hwF⟩ := hw
    have hvC := hVC v hv
    have hvT : v ∈ T := (hVP hv).1
    refine ⟨T.mul_mem (T.mul_mem hvT hwT) (T.inv_mem hvT), mul_mem (mul_mem hvC hwC) (inv_mem hvC), ?_⟩
    rw [phig_mul x Kb (mul_mem hvC hwC) (inv_mem hvC), phig_mul x Kb hvC hwC, phig_inv x Kb hvC]
    have hu : g⁻¹ * phig x Kb v * g ∈ U := hVU _ ((mem_timgP h hVP).2 ⟨v, hv, rfl⟩)
    have := hUFc _ hu _ hwF
    have e1 : g⁻¹ * (phig x Kb v * phig x Kb w * (phig x Kb v)⁻¹) * g =
        (g⁻¹ * phig x Kb v * g) * (g⁻¹ * phig x Kb w * g) * (g⁻¹ * phig x Kb v * g)⁻¹ := by group
    rw [e1, this, mul_inv_cancel_right]
    exact hwF
  ·
    intro d hdT hcent
    have hdC := h.T_le_C hdT
    have hcentA : ∀ u ∈ U, (g * u * g⁻¹) * phig x Kb d = phig x Kb d * (g * u * g⁻¹) := by
      intro u hu
      obtain ⟨v, hv, hvu⟩ := (mem_timgP h hVP).1 (hUV u hu)
      rw [← hvu, ← phig_mul x Kb (hVC v hv) hdC, ← phig_mul x Kb hdC (hVC v hv), (hcent v hv).symm]
    have hdU : g⁻¹ * phig x Kb d * g ∈ Subgroup.centralizer (U : Set (MulAut ↥Kb)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hcentA u hu
      calc u * (g⁻¹ * phig x Kb d * g) = g⁻¹ * ((g * u * g⁻¹) * phig x Kb d) * g := by group
        _ = g⁻¹ * (phig x Kb d * (g * u * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * phig x Kb d * g) * u := by group
    rw [hUC] at hdU
    obtain ⟨u, hu, f, hf, huf⟩ := (mem_sup_iff_of_comm hUFc).1 hdU
    obtain ⟨v, hv, hvu⟩ := (mem_timgP h hVP).1 (hUV u hu)
    have hvC := hVC v hv
    refine ⟨v, hv, v⁻¹ * d, ⟨T.mul_mem (T.inv_mem (hVP hv).1) hdT, mul_mem (inv_mem hvC) hdC, ?_⟩,
      by group⟩
    rw [phig_mul x Kb (inv_mem hvC) hdC, phig_inv x Kb hvC, hvu]
    have : g⁻¹ * ((g * u * g⁻¹)⁻¹ * phig x Kb d) * g = u⁻¹ * (g⁻¹ * phig x Kb d * g) := by group
    rw [this, huf]
    simpa using hf

end CFSG.GH74.GLS.Stage1.Thm6.Glue
