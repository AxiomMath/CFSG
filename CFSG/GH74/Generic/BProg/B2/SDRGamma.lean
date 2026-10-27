module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.GLS.C3.Layer1.U1aRank
public import CFSG.GH74.GLS.C3.Layer1.U1aSetup
public import CFSG.LocalAnalysis.ComponentClassification.GSLitIsoTarget
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.GH74.Generic.BProg.B2.SDR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_bot_of_one_le_pRank' {Q : Subgroup G} (h : 1 ≤ pRank 2 ↥Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : pRank 2 ↥(⊥ : Subgroup G) ≤ 0 := by
    refine csSup_le' ?_
    rintro k ⟨E, -, hcard⟩
    have hd : Nat.card ↥E ∣ Nat.card ↥(⊥ : Subgroup G) := Subgroup.card_subgroup_dvd_card E
    rw [Subgroup.card_bot, hcard] at hd
    have h1 : 2 ^ k ≤ 1 := Nat.le_of_dvd one_pos hd
    by_contra hk
    have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  omega

theorem exists_inv_normalizer_le {R : Subgroup G} (hR : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥)
    (hr : pRank 2 ↥R ≤ 1) :
    ∃ z ∈ R, orderOf z = 2 ∧ normalizer (R : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨z, hzR, hz2, hzc⟩ := CFSG.ComponentClassification.GSLit.exists_involution_mem_center
    hR le_rfl Subgroup.le_normalizer hR1
  have huniq : ∀ u ∈ R, orderOf u = 2 → u = z := by
    intro u huR hu2
    by_contra hne
    have := C3.Layer1.U1a.two_le_pRank_of_commute (D := R) huR hzR hu2 hz2 (hzc u huR) hne
    omega
  refine ⟨z, hzR, hz2, fun n hn => ?_⟩
  rw [Subgroup.mem_normalizer_iff] at hn
  have hmem : n * z * n⁻¹ ∈ R := (hn z).1 hzR
  have hord : orderOf (n * z * n⁻¹) = 2 := by
    rw [← hz2]; exact C3.Layer1.U1a.orderOf_conj_eq' n
  have heq := huniq _ hmem hord
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [heq]

theorem inU0C_of_four {M E : Subgroup G} (hEM : E ≤ M) (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (hcard : Nat.card ↥E = 4) (hJ : ∀ e ∈ E, orderOf e = 2 → centralizer ({e} : Set G) ≤ M) :
    InU0C M E := by
  have hr : pRank 2 ↥E = 2 := by
    have := hE
    exact pRank_eq_of_card_eq_pow one_lt_two (by simpa using hcard)
  refine ⟨⟨hEM, hE, hr.ge⟩, Or.inl hr, ?_⟩
  rw [hr]
  unfold gammaKC
  refine iSup₂_le fun U hUE => iSup_le fun hrU => ?_
  obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (ne_bot_of_one_le_pRank' hrU)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : orderOf u = 2 := by
    have hd : orderOf (⟨u, hUE huU⟩ : ↥E) ∣ 2 :=
      (Monoid.order_dvd_exponent _).trans hE.exponent_dvd_p
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.1 h1) (fun h => hu1' (congrArg Subtype.val h))
    · rwa [Subgroup.orderOf_mk] at h2
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huU)).trans (hJ u (hUE huU) hu2)

theorem gammaK_le_of_thm2C {M Q : Subgroup G} (h2 : Stage2Concl2C M) (hQM : Q ≤ M) (hQp : IsPGroup 2 ↥Q)
    (hJ : ∀ y ∈ Q, orderOf y = 2 → centralizer ({y} : Set G) ≤ M) : gammaK 2 Q 1 ≤ M := by
  unfold gammaK
  refine iSup₂_le fun R hRQ => iSup_le fun hrR => ?_
  have hRp : IsPGroup 2 ↥R := hQp.to_le hRQ
  have hR1 : R ≠ ⊥ := ne_bot_of_one_le_pRank' hrR
  by_cases hr : pRank 2 ↥R ≤ 1
  · obtain ⟨z, hzR, hz2, hN⟩ := exists_inv_normalizer_le hRp hR1 hr
    exact hN.trans (hJ z (hRQ hzR) hz2)
  · obtain ⟨a, ha, b, hb, ha2, hb2, hab, hcomm⟩ :=
      C3.Layer1.U1a.exists_commuting_involutions (D := R) (by omega)
    obtain ⟨V, hVle, hVel, hV4⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
        (H := G) ha2 hb2 hcomm hab
    have hVR : V ≤ R := hVle.trans ((Subgroup.closure_le _).2 (by
      rintro y (rfl | rfl)
      · exact ha
      · exact hb))
    have hU0 : InU0C M V := inU0C_of_four (hVR.trans (hRQ.trans hQM)) hVel hV4
      (fun e he he2 => hJ e (hRQ (hVR he)) he2)
    intro n hn
    refine h2 V hU0 n ?_
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    have hvR : v ∈ R := hVR hv
    have hn' : n⁻¹ ∈ normalizer (R : Set G) := (normalizer (R : Set G)).inv_mem hn
    rw [Subgroup.mem_normalizer_iff] at hn'
    have := (hn' v).1 hvR
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hRQ.trans hQM (by simpa using this)

theorem false_of_conj_inter {M Q : Subgroup G} (h2 : Stage2Concl2C M) (hQM : Q ≤ M)
    (hJ : ∀ y ∈ Q, orderOf y = 2 → centralizer ({y} : Set G) ≤ M) {g : G} (hg : g ∉ M)
    (h : 2 ≤ pRank 2 ↥(CFSG.conjugate Q g ⊓ M)) : False := by
  obtain ⟨a, ha, b, hb, ha2, hb2, hab, hcomm⟩ := C3.Layer1.U1a.exists_commuting_involutions h
  have hmemQ : ∀ y ∈ CFSG.conjugate Q g, g * y * g⁻¹ ∈ Q := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply, mul_assoc] using hq
  set a₀ := g * a * g⁻¹ with ha₀
  set b₀ := g * b * g⁻¹ with hb₀
  have ha₀2 : orderOf a₀ = 2 := by rw [ha₀, C3.Layer1.U1a.orderOf_conj_eq']; exact ha2
  have hb₀2 : orderOf b₀ = 2 := by rw [hb₀, C3.Layer1.U1a.orderOf_conj_eq']; exact hb2
  have hcomm₀ : a₀ * b₀ = b₀ * a₀ := by
    calc a₀ * b₀ = g * (a * b) * g⁻¹ := by rw [ha₀, hb₀]; group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm]
      _ = b₀ * a₀ := by rw [ha₀, hb₀]; group
  have hab₀ : a₀ ≠ b₀ := fun h => hab (by
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [ha₀, hb₀, mul_assoc] using this)
  obtain ⟨V, hVle, hVel, hV4⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      (H := G) ha₀2 hb₀2 hcomm₀ hab₀
  have hclQ : Subgroup.closure ({a₀, b₀} : Set G) ≤ Q := (Subgroup.closure_le _).2 (by
    rintro y (rfl | rfl)
    · exact hmemQ a ha.1
    · exact hmemQ b hb.1)
  have hVQ : V ≤ Q := hVle.trans hclQ
  have hU0 : InU0C M V := inU0C_of_four (hVQ.trans hQM) hVel hV4
    (fun e he he2 => hJ e (hVQ he) he2)
  refine hg (h2 V hU0 g ?_)
  have hcl : (Subgroup.closure ({a₀, b₀} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨t, ht, rfl⟩
    rcases ht with rfl | rfl
    · simpa [ha₀, MulAut.conj_apply, mul_assoc] using ha.2
    · simpa [hb₀, MulAut.conj_apply, mul_assoc] using hb.2
  exact (Subgroup.map_mono hVle).trans hcl

end CFSG.GH74.Generic.BProg.B2.SDR
