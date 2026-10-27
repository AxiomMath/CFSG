module

public import CFSG.GH74.GLS.Stage1.Main.BrG2KAbs
public import CFSG.GH74.GLS.Stage1.Main.BrModel
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

namespace CFSG.GH74.GLS.Stage1.Main

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem pgroup_le_oPrimeResidual {T : Subgroup Y} (hT : IsPGroup 2 ↥T) : T ≤ oPrimeResidual 2 Y := by
  intro x hx
  apply Subgroup.subset_closure
  obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem g2_sylow_inf {K₁ K₂ T : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    {n : ℕ}
    (hv₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1)
    (hv₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1)
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2)
    (hT2 : IsPGroup 2 ↥T) (hTcard : Nat.card ↥T = 2 ^ (2 * n + 2))
    (hidx : ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y)).index = 2) :
    Nat.card ↥(T ⊓ (K₁ ⊔ K₂)) = 2 ^ (2 * n + 1) ∧ (K₁ ⊔ K₂).relIndex T = 2 := by
  have hTΓ : T ≤ oPrimeResidual 2 Y := pgroup_le_oPrimeResidual hT2
  have hcardK : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := card_sup_mul_two hc hinf
  have hK1 : Nat.card ↥K₁ = Nat.card ↥(StatedSL 2 F₁) := Nat.card_congr e₁.toEquiv
  have hK2 : Nat.card ↥K₂ = Nat.card ↥(StatedSL 2 F₂) := Nat.card_congr e₂.toEquiv
  have hpos₁ : 0 < Nat.card ↥K₁ := Nat.card_pos
  have hpos₂ : 0 < Nat.card ↥K₂ := Nat.card_pos
  have hposK : 0 < Nat.card ↥(K₁ ⊔ K₂) := Nat.card_pos
  have hv : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 = 2 * n + 1 := by
    have h1 : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 2 =
        (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 := by rw [hcardK]
    rw [Nat.factorization_mul hposK.ne' (by norm_num), Nat.factorization_mul hpos₁.ne' hpos₂.ne'] at h1
    simp only [Finsupp.coe_add, Pi.add_apply] at h1
    rw [hK1, hK2, hv₁, hv₂] at h1
    have h2 : (Nat.factorization 2) 2 = 1 := Nat.prime_two.factorization_self
    omega
  have hrel : (K₁ ⊔ K₂).relIndex T ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right hTΓ (H := K₁ ⊔ K₂) (by
      show ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y)).index ≠ 0
      rw [hidx]; norm_num)
    have h2 : (K₁ ⊔ K₂).relIndex (oPrimeResidual 2 Y) = 2 := hidx
    omega
  have hcardT : Nat.card ↥(T ⊓ (K₁ ⊔ K₂)) * (K₁ ⊔ K₂).relIndex T = Nat.card ↥T := by
    have h1 := Subgroup.card_mul_index (((K₁ ⊔ K₂) ⊓ T).subgroupOf T)
    have h2 : Nat.card ↥(((K₁ ⊔ K₂) ⊓ T).subgroupOf T) = Nat.card ↥(T ⊓ (K₁ ⊔ K₂)) := by
      rw [inf_comm]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h3 : (((K₁ ⊔ K₂) ⊓ T).subgroupOf T).index = (K₁ ⊔ K₂).relIndex T :=
      Subgroup.inf_relIndex_right _ _
    rw [h2, h3] at h1
    exact h1
  have hTK2 : IsPGroup 2 ↥(T ⊓ (K₁ ⊔ K₂)) := hT2.to_inf_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hTK2
  have hdvd : Nat.card ↥(T ⊓ (K₁ ⊔ K₂)) ∣ Nat.card ↥(K₁ ⊔ K₂) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hjle : j ≤ 2 * n + 1 := by
    rw [hj] at hdvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hposK.ne').1 hdvd
    omega
  have hr0 : (K₁ ⊔ K₂).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr : (K₁ ⊔ K₂).relIndex T = 2 := by
    rw [hj, hTcard] at hcardT
    by_contra hne
    have hr1 : (K₁ ⊔ K₂).relIndex T = 1 := by omega
    rw [hr1, mul_one] at hcardT
    have := Nat.pow_right_injective (le_refl 2) hcardT
    omega
  refine ⟨?_, hr⟩
  rw [hr, hj, hTcard] at hcardT
  rw [hj]
  have h2 : 2 ^ j * 2 = 2 ^ (2 * n + 1) * 2 := by
    rw [hcardT]; ring
  have := Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  rw [this]

theorem g2_oPrimePResidual_eq {K₁ K₂ T : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] {n : ℕ} (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    (hv₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1)
    (hv₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1)
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2)
    (hT2 : IsPGroup 2 ↥T) (hTcard : Nat.card ↥T = 2 ^ (2 * n + 2))
    (hKΓ : K₁ ⊔ K₂ ≤ oPrimeResidual 2 Y)
    (hidx : ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y)).index = 2) :
    oPrimePResidual 2 Y = K₁ ⊔ K₂ := by
  have hTΓ : T ≤ oPrimeResidual 2 Y := pgroup_le_oPrimeResidual hT2
  have hK₁Γ : K₁ ≤ oPrimeResidual 2 Y := le_sup_left.trans hKΓ
  have hK₂Γ : K₂ ≤ oPrimeResidual 2 Y := le_sup_right.trans hKΓ
  obtain ⟨-, hrel⟩ := g2_sylow_inf hv₁ hv₂ e₁ e₂ hc hinf hT2 hTcard hidx
  have hN : ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y)).Normal := Subgroup.normal_of_index_eq_two hidx
  have hperf : (K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y) ≤ oResidual 2 ↥(oPrimeResidual 2 Y) := by
    rw [Subgroup.subgroupOf_sup hK₁Γ hK₂Γ]
    exact sup_le
      (hasSL2_le_oResidual hodd₁ ((Subgroup.subgroupOfEquivOfLe hK₁Γ).trans e₁))
      (hasSL2_le_oResidual hodd₂ ((Subgroup.subgroupOfEquivOfLe hK₂Γ).trans e₂))
  have hT' : IsPGroup 2 ↥(T.subgroupOf (oPrimeResidual 2 Y)) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTΓ).symm
  have hTnot : ¬ T ≤ K₁ ⊔ K₂ := by
    intro hle
    have : (K₁ ⊔ K₂).relIndex T = 1 := Subgroup.relIndex_eq_one.2 hle
    omega
  have hTnot' : ¬ T.subgroupOf (oPrimeResidual 2 Y) ≤ (K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y) := by
    intro hle
    apply hTnot
    intro x hx
    exact hle (show (⟨x, hTΓ hx⟩ : ↥(oPrimeResidual 2 Y)) ∈ T.subgroupOf (oPrimeResidual 2 Y) from hx)
  have hY : (K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y) ⊔ T.subgroupOf (oPrimeResidual 2 Y) = ⊤ := by
    set N := (K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y) with hNdef
    set T' := T.subgroupOf (oPrimeResidual 2 Y) with hT'def
    have hdvd : (N ⊔ T').index ∣ N.index := Subgroup.index_dvd_of_le le_sup_left
    rw [hidx] at hdvd
    have hne : (N ⊔ T').index ≠ 2 := by
      intro h2
      have h3 := Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T')
      rw [h2, hidx] at h3
      have h4 : N.relIndex (N ⊔ T') = 1 := by omega
      exact hTnot' ((le_sup_right : T' ≤ N ⊔ T').trans (Subgroup.relIndex_eq_one.1 h4))
    have h1 : (N ⊔ T').index = 1 := by
      have := (Nat.dvd_prime Nat.prime_two).1 hdvd
      tauto
    exact Subgroup.index_eq_one.1 h1
  have hres := oResidual_sup_eq hN hperf hT' hY
  unfold oPrimePResidual
  rw [hres]
  exact Subgroup.map_subgroupOf_eq_of_le hKΓ

end Abstract


section Ctx

@[expose] def G2SylowShapeFact : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 0 < f → LieModel Gs .G2 0 p f →
    ∀ S' : Sylow 2 Gs, ∃ (A : Subgroup Gs) (a t y : Gs) (n : ℕ), 2 ≤ n ∧
      ShapeConds (S' : Subgroup Gs) A a t y n ∧ ((p ^ f) ^ 2 - 1).factorization 2 = n + 1

structure G2Ctx {G : Type} [Group G] [Finite G] (z : G) (S : Subgroup G) where
  n : ℕ
  two_le : 2 ≤ n
  Gs : Type
  [grp : Group Gs]
  S' : Subgroup Gs
  A : Subgroup Gs
  a : Gs
  t : Gs
  y : Gs
  shape : ShapeConds S' A a t y n
  eS : ↥S ≃* ↥S'
  F₁ : Type
  F₂ : Type
  [fld₁ : Field F₁]
  [fld₂ : Field F₂]
  [fin₁ : Finite F₁]
  [fin₂ : Finite F₂]
  K₁ : Subgroup (CentralizerBar z)
  K₂ : Subgroup (CentralizerBar z)
  e₁ : ↥K₁ ≃* StatedSL 2 F₁
  e₂ : ↥K₂ ≃* StatedSL 2 F₂
  odd₁ : Odd (Nat.card F₁)
  odd₂ : Odd (Nat.card F₂)
  five : 5 ≤ Nat.card F₁
  card_le : Nat.card F₂ ≤ Nat.card F₁
  v₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1
  v₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  inf_card : Nat.card ↥(K₁ ⊓ K₂) = 2
  le_Γ : K₁ ⊔ K₂ ≤ oPrimeResidual 2 (CentralizerBar z)
  idx : ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 (CentralizerBar z))).index = 2

attribute [instance] G2Ctx.grp G2Ctx.fld₁ G2Ctx.fld₂ G2Ctx.fin₁ G2Ctx.fin₂

theorem G2Ctx.exists (hshape : G2SylowShapeFact) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} (hT : G2Term G z S) : Nonempty (G2Ctx z S) := by
  obtain ⟨p, f, hp, hp2, ⟨Gs, iGs, fGs, hL, S', ⟨eS⟩⟩, -, hsl⟩ := hT
  obtain ⟨F, F₁, F₂, iF, iF₁, iF₂, fF, fF₁, fF₂, hFq, hodd₁, hodd₂, hle, h5, hfac₁, hfac₂, K, hKΓ,
    hidx, K₁, K₂, hK12, hcomm, hinf, ⟨e₁⟩, ⟨e₂⟩⟩ := hsl
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hFq, h0, pow_zero] at h1
      exact lt_irrefl _ h1
    · exact h0
  obtain ⟨A, a, t, y, n, hn, hSC, hnq⟩ := hshape Gs p f hp hp2 hf hL S'
  have hpf_odd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hpf1 : 1 < p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rwa [hFq] at h1
  have hFac : (Nat.card ↥(StatedSL 2 F)).factorization 2 = n + 1 := by
    rw [card_statedSL_two' F, hFq]
    have hne1 : p ^ f ≠ 0 := by omega
    have hne2 : (p ^ f) ^ 2 - 1 ≠ 0 := by
      have : 1 < (p ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) hpf1
      omega
    rw [Nat.factorization_mul hne1 hne2, Finsupp.coe_add, Pi.add_apply, hnq]
    have : (p ^ f).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.mpr hpf_odd) (even_iff_two_dvd.mpr hd))
    omega
  refine ⟨⟨n, hn, Gs, S', A, a, t, y, hSC, eS, F₁, F₂, K₁, K₂, e₁, e₂, hodd₁, hodd₂, h5, hle,
    hfac₁.trans hFac, hfac₂.trans hFac, hcomm, hinf, ?_, ?_⟩⟩
  · rw [hK12]; exact hKΓ
  · rw [hK12]; exact hidx

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

theorem G2Ctx.card_S : Nat.card ↥S = 2 ^ (2 * C.n + 2) := by
  rw [Nat.card_congr C.eS.toEquiv]
  exact C.shape.card_eq

theorem cen2_S_inf_oddCore (hcen : Cen2 G z S) : S ⊓ OddCore z = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  exact Subgroup.mem_bot.2 (eq_one_of_mem_pgroup_oddCore hcen.sylow.isPGroup hs.1 hs.2)


theorem G2Ctx.sylow_bar (hcen : Cen2 G z S) :
    IsPGroup 2 ↥(barOf z S) ∧ Nat.card ↥(barOf z S) = 2 ^ (2 * C.n + 2) := by
  refine ⟨(isSylowOf_barOf hcen.sylow).isPGroup, ?_⟩
  rw [← C.card_S]
  exact (Nat.card_congr (barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen)).toEquiv).symm

theorem G2Ctx.sylow_inf (hcen : Cen2 G z S) :
    Nat.card ↥(barOf z S ⊓ (C.K₁ ⊔ C.K₂)) = 2 ^ (2 * C.n + 1) ∧
      (C.K₁ ⊔ C.K₂).relIndex (barOf z S) = 2 := by
  obtain ⟨h2, hcard⟩ := C.sylow_bar hcen
  exact g2_sylow_inf C.v₁ C.v₂ C.e₁ C.e₂ C.comm C.inf_card h2 hcard C.idx

theorem G2Ctx.oPrime_eq (hcen : Cen2 G z S) : oPrimePResidual 2 (CentralizerBar z) = C.K₁ ⊔ C.K₂ := by
  obtain ⟨h2, hcard⟩ := C.sylow_bar hcen
  exact g2_oPrimePResidual_eq C.odd₁ C.odd₂ C.v₁ C.v₂ C.e₁ C.e₂ C.comm C.inf_card h2 hcard C.le_Γ C.idx

theorem G2Ctx.perfect_le_K₁_of_three (h3 : Nat.card C.F₂ = 3) {J : Subgroup (CentralizerBar z)}
    (hJ : Group.IsPerfect ↥J) (hJN : J ≤ C.K₁ ⊔ C.K₂) : J ≤ C.K₁ := by
  classical
  set N : Subgroup (CentralizerBar z) := C.K₁ ⊔ C.K₂ with hNdef
  set K : Subgroup ↥N := C.K₁.subgroupOf N with hKdef
  have hKn : K.Normal := by
    constructor
    intro n hn g
    obtain ⟨g, hg⟩ := g
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' C.comm hg
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hbn : b * (n : CentralizerBar z) = (n : CentralizerBar z) * b := (C.comm n hn b hb).symm
    have e : a * b * (n : CentralizerBar z) * (a * b)⁻¹ = a * n * a⁻¹ := by
      calc a * b * (n : CentralizerBar z) * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n * a⁻¹ := by rw [hbn]; group
    show a * b * (n : CentralizerBar z) * (a * b)⁻¹ ∈ C.K₁
    rw [e]
    exact C.K₁.mul_mem (C.K₁.mul_mem ha hn) (C.K₁.inv_mem ha)
  have hK₂N : C.K₂ ≤ N := le_sup_right
  let f : ↥C.K₂ →* (↥N ⧸ K) := (QuotientGroup.mk' K).comp (Subgroup.inclusion hK₂N)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' C.comm hg
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (⟨b, hK₂N hb⟩ : ↥N) : ↥N ⧸ K) = QuotientGroup.mk ⟨a * b, hg⟩
    rw [QuotientGroup.eq]
    show (⟨b, hK₂N hb⟩ : ↥N)⁻¹ * ⟨a * b, hg⟩ ∈ K
    rw [Subgroup.mem_subgroupOf]
    have e : ((⟨b, hK₂N hb⟩ : ↥N)⁻¹ * ⟨a * b, hg⟩ : ↥N) = (b⁻¹ * (a * b) : CentralizerBar z) := rfl
    rw [e]
    have hba : b⁻¹ * (a * b) = a := by
      have h1 : a * b = b * a := C.comm a ha b hb
      rw [h1]; group
    rw [hba]
    exact ha
  have hK₂s : Group.IsSolvable ↥C.K₂ := by
    obtain ⟨eM⟩ := nonempty_equiv_m3 h3 C.e₂
    have := isSolvable_m3
    exact Group.isSolvable_of_isSolvable_injective (f := eM.toMonoidHom) eM.injective
  have hQs : Group.IsSolvable (↥N ⧸ K) := Group.isSolvable_of_surjective hf
  set J' : Subgroup ↥N := J.subgroupOf N with hJ'
  have hJ'p : Group.IsPerfect ↥J' := by
    have e : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJN
    exact Group.IsPerfect.ofSurjective (G := ↥J) (G' := ↥J') (f := e.symm.toMonoidHom) e.symm.surjective
  have himg : J'.map (QuotientGroup.mk' K) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(J'.map (QuotientGroup.mk' K)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hJ'p
    have : Group.IsPerfect ↥(J'.map (QuotientGroup.mk' K)) := Group.IsPerfect.map (QuotientGroup.mk' K)
    have hs : Group.IsSolvable ↥(J'.map (QuotientGroup.mk' K)) := inferInstance
    exact Group.IsPerfect.not_isSolvable ↥(J'.map (QuotientGroup.mk' K)) hs
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg
  intro x hx
  have hx' : (⟨x, hJN hx⟩ : ↥N) ∈ J' := hx
  exact himg hx'

theorem G2Ctx.le_innerE (hcen : Cen2 G z S) : C.K₁ ⊔ C.K₂ ≤ InnerE z := by
  have hN : (C.K₁ ⊔ C.K₂).Normal := by
    rw [← C.oPrime_eq hcen]
    exact Stage1.Thm6.Prod.oPrimePResidual_normal Nat.prime_two _
  have hq₁ : IsQuasisimple ↥C.K₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (C.e₁.trans (specialLinearGroupEquivStatedSL 2 C.F₁).symm).symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by have := C.five; omega))
  have hc₁ : IsComponent C.K₁ := ⟨hq₁, isSubnormal_of_comm_normal C.comm hN⟩
  have hK₁E : C.K₁ ≤ layer (CentralizerBar z) := CFSG.LocalCores.component_le_layer hc₁
  refine sup_le (hK₁E.trans le_sup_left) ?_
  by_cases h3 : Nat.card C.F₂ = 3
  · have hE : layer (CentralizerBar z) ≤ C.K₁ := by
      refine sSup_le fun J hJ => ?_
      have hJN : J ≤ C.K₁ ⊔ C.K₂ := by
        rw [← C.oPrime_eq hcen]
        exact perfect_le_oPrimePResidual' hJ.1.1
      exact C.perfect_le_K₁_of_three h3 hJ.1.1 hJN
    refine le_sup_of_le_right ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact C.comm x (hE hx) b hb
  · have h5 : 5 ≤ Nat.card C.F₂ := by
      have h2 : 2 ≤ Nat.card C.F₂ := Finite.one_lt_card
      obtain ⟨r, hr⟩ := C.odd₂
      omega
    have hq₂ : IsQuasisimple ↥C.K₂ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (C.e₂.trans (specialLinearGroupEquivStatedSL 2 C.F₂).symm).symm
        (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by omega))
    have hcomm' : ∀ b ∈ C.K₂, ∀ a ∈ C.K₁, b * a = a * b := fun b hb a ha => (C.comm a ha b hb).symm
    have hN' : (C.K₂ ⊔ C.K₁).Normal := by rw [sup_comm]; exact hN
    have hc₂ : IsComponent C.K₂ := ⟨hq₂, isSubnormal_of_comm_normal hcomm' hN'⟩
    exact (CFSG.LocalCores.component_le_layer hc₂).trans le_sup_left

theorem G2Ctx.LBar_eq (hcen : Cen2 G z S) : LBar z = C.K₁ ⊔ C.K₂ := by
  rw [Stage1.Thm6.Prod.LBar_eq z, C.oPrime_eq hcen]
  exact inf_eq_left.2 (C.le_innerE hcen)

include C in
theorem G2Ctx.perfInner (hcen : Cen2 G z S) : PerfInner z := by
  intro Q hQ
  have h := perfect_le_oPrimePResidual' hQ
  rw [C.oPrime_eq hcen] at h
  exact h.trans (C.le_innerE hcen)

theorem G2Ctx.mem_LC_iff (hcen : Cen2 G z S) {s : G} (hs : s ∈ S) (hsC : s ∈ Cen z) :
    s ∈ LC z ↔ toBar z ⟨s, hsC⟩ ∈ C.K₁ ⊔ C.K₂ := by
  obtain ⟨k, hk⟩ := hcen.sylow.isPGroup ⟨s, hs⟩
  have hk' : (⟨s, hsC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) ⟨s, hsC⟩ hk', C.LBar_eq hcen]

end Ctx


section Rel

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.relIndex_RC (hcen : Cen2 G z S) : (RC S z).relIndex S = 2 := by
  have hSC : S ≤ Cen z := hcen.sylow.le
  have hSN : S ⊓ OddCore z = ⊥ := cen2_S_inf_oddCore hcen
  set β : ↥S ≃* ↥(barOf z S) := barEquiv z S hSC hSN with hβdef
  obtain ⟨-, hrel⟩ := C.sylow_inf hcen
  have hcomap : (RC S z).subgroupOf S =
      ((C.K₁ ⊔ C.K₂).subgroupOf (barOf z S)).comap β.toMonoidHom := by
    ext s
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, RC, Subgroup.mem_inf]
    rw [C.mem_LC_iff hcen s.2 (hSC s.2)]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨s.2, h⟩
  show ((RC S z).subgroupOf S).index = 2
  rw [hcomap, Subgroup.index_comap_of_surjective _ β.surjective]
  exact hrel

end Rel

end CFSG.GH74.GLS.Stage1.Main
