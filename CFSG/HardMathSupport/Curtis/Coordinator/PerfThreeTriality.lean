module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityDefs
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityCent
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCent
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.EvenSmallLie.OmegaEight CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

@[expose] def conjOnNormalizer {Y : Type} [Group Y] (L : Subgroup Y) (u : Y)
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) : ↥L ≃* ↥L where
  toFun x := ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu x).1 x.2⟩
  invFun x := ⟨u⁻¹ * x * u, by
    have h2 := (Subgroup.mem_normalizer_iff.1 hu (u⁻¹ * x * u)).2
    have e : u * (u⁻¹ * (x : Y) * u) * u⁻¹ = x := by group
    rw [e] at h2
    exact h2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOnNormalizer_apply {Y : Type} [Group Y] (L : Subgroup Y) (u : Y)
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) (x : ↥L) :
    ((conjOnNormalizer L u hu x : ↥L) : Y) = u * x * u⁻¹ :=
  rfl

theorem exists_mulEquiv_omegaT (hZ : OddCenterRest) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {u : Y} (h : FixPerfThreeHyp L J u)
    (hD : IsLieOf IdxD8 (↥L ⧸ Subgroup.center ↥L)) : Nonempty (↥L ≃* omegaT) := by
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hD
  cases x
  case D r q =>
    obtain ⟨hr, hp, hq⟩ := hd
    subst hr
    obtain ⟨φ⟩ := CFSG.AGLEmbedding.O8pCent.nonempty_mulEquiv_omegaT_catalog ⟨.D 4 q, hv⟩ q hq rfl
    have hIdx : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L) := ⟨⟨.D 4 q, hv⟩, hp, ⟨e⟩⟩
    have hrest : IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L) := Or.inr (Or.inl hIdx)
    rcases hZ Y L h.parab.comp h.parab.odd hrest with hc | ⟨-, ⟨e6⟩⟩
    · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hc
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans
        (e.trans φ)⟩
    · exfalso
      have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 174182400 := by
        rw [Nat.card_congr (e.trans φ).toEquiv, card_omegaT]
      have h2 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
        rw [Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
  all_goals exact hd.elim

theorem exists_outer_of_conj {Y : Type} [Group Y] {L : Subgroup Y}
    {u : Y} (hnorm : u ∈ Subgroup.normalizer (L : Set Y)) (hu3 : u ^ 3 = 1)
    (hu : u ∉ L ⊔ Subgroup.centralizer (L : Set Y)) (ψ : ↥L ≃* omegaT) :
    ∃ a : Equiv.Perm (Fin 360), a ∈ autT ∧ a ^ 3 = 1 ∧ a ∉ omegaT ∧
      ∀ g : omegaT, ((ψ (conjOnNormalizer L u hnorm (ψ.symm g)) : omegaT) :
        Equiv.Perm (Fin 360)) = a * g * a⁻¹ := by
  set c := conjOnNormalizer L u hnorm with hc
  let α : MulAut omegaT := ψ.symm.trans (c.trans ψ)
  have hα : ∀ g, α g = ψ (c (ψ.symm g)) := fun g => rfl
  set a₀ : autT := autEquiv.symm α with ha₀
  have hαa : autEquiv a₀ = α := autEquiv.apply_symm_apply α
  have hform : ∀ g : omegaT, ((ψ (c (ψ.symm g)) : omegaT) : Equiv.Perm (Fin 360)) =
      (a₀ : Equiv.Perm (Fin 360)) * g * (a₀ : Equiv.Perm (Fin 360))⁻¹ := by
    intro g
    rw [← hα, ← hαa]
    exact autEquiv_apply a₀ g
  have huuu : u * u * u = 1 := by simpa [pow_succ, mul_assoc] using hu3
  have hc3 : ∀ x : ↥L, c (c (c x)) = x := by
    intro x
    apply Subtype.ext
    simp only [hc, conjOnNormalizer_apply]
    calc u * (u * (u * (x : Y) * u⁻¹) * u⁻¹) * u⁻¹ = (u * u * u) * x * (u * u * u)⁻¹ := by group
      _ = x := by rw [huuu]; group
  have hα3 : α ^ 3 = 1 := by
    refine MulEquiv.ext fun g => ?_
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, hα, MulEquiv.symm_apply_apply,
      MulAut.one_apply]
    rw [hc3]
    exact ψ.apply_symm_apply g
  refine ⟨a₀, a₀.2, ?_, ?_, hform⟩
  · have h1 : a₀ ^ 3 = 1 := autEquiv.injective (by rw [map_pow, hαa, hα3, map_one])
    have := congrArg (fun z : autT => (z : Equiv.Perm (Fin 360))) h1
    simpa using this
  · intro hω
    apply hu
    set ã : omegaT := ⟨a₀, hω⟩ with hã
    set l : ↥L := ψ.symm ã with hl
    have hcx : ∀ x : ↥L, c x = l * x * l⁻¹ := by
      intro x
      apply ψ.injective
      apply Subtype.ext
      have := hform (ψ x)
      rw [ψ.symm_apply_apply] at this
      rw [this]
      simp [hl, hã]
    have hcent : (l : Y)⁻¹ * u ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg Subtype.val (hcx ⟨x, hx⟩)
      simp only [hc, conjOnNormalizer_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc x * ((l : Y)⁻¹ * u) = (l : Y)⁻¹ * ((l : Y) * x * (l : Y)⁻¹) * u := by group
        _ = (l : Y)⁻¹ * (u * x * u⁻¹) * u := by rw [← h1]
        _ = (l : Y)⁻¹ * u * x := by group
    have : u = (l : Y) * ((l : Y)⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem_sup l.2 hcent

theorem symm_mem_normalizer_of_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (S : Subgroup G)
    {n : H} (hn : n ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup H) : Set H)) :
    e.symm n ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro g
  have h1 := hn (e g)
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
  simpa using h1

theorem mem_normalizer_of_subgroupOf {Y : Type} [Group Y] {L T : Subgroup Y} (hTL : T ≤ L)
    {x : ↥L} (hx : x ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (x : Y) ∈ Subgroup.normalizer (T : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro t
  constructor
  · intro ht
    exact (hx ⟨t, hTL ht⟩).1 ht
  · intro ht
    have htL : t ∈ L := by
      have h1 : (x : Y)⁻¹ * ((x : Y) * t * (x : Y)⁻¹) * (x : Y) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem x.2) (hTL ht)) x.2
      simpa [mul_assoc] using h1
    exact (hx ⟨t, htL⟩).2 ht

theorem abelian_of_flag (hFlag : TrialityFlagInput) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {u : Y} (hJL : J ≤ L) (hJne : J ≠ L)
    (hT : ∃ T : Subgroup Y, IsSylowTwoOf T L ∧ L ⊓ Subgroup.normalizer (T : Set Y) ≤ J)
    (hnorm : u ∈ Subgroup.normalizer (L : Set Y)) (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J)
    (ψ : ↥L ≃* omegaT) (E : Subgroup (Equiv.Perm (Fin 360))) (hEω : E ≤ omegaT)
    (hE3 : IsPGroup 3 E)
    (hfixE : ∀ e : omegaT, (e : Equiv.Perm (Fin 360)) ∈ E →
      conjOnNormalizer L u hnorm (ψ.symm e) = ψ.symm e) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, ⟨hTL, hT2, hTidx⟩, hTN⟩ := hT
  set TL : Subgroup ↥L := T.subgroupOf L with hTLdef
  have hTLp : IsPGroup 2 TL := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  set Tω : Subgroup omegaT := TL.map ψ.toMonoidHom with hTω
  have hTωp : IsPGroup 2 Tω := hTLp.map ψ.toMonoidHom
  have hTωidx : ¬ 2 ∣ Tω.index := by
    have h1 := Subgroup.index_map_equiv TL ψ
    rw [← h1] at hTidx
    exact hTidx
  set Jω : Subgroup omegaT := (J.subgroupOf L).map ψ.toMonoidHom with hJω
  have hN : Subgroup.normalizer (((hTωp.toSylow hTωidx : Sylow 2 omegaT) : Subgroup omegaT) :
      Set omegaT) ≤ Jω := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((TL.map ψ.toMonoidHom : Subgroup omegaT) : Set omegaT) := hn
    have hxN := mem_normalizer_of_subgroupOf hTL (symm_mem_normalizer_of_map ψ TL hn')
    have hxJ : ((ψ.symm n : ↥L) : Y) ∈ J :=
      hTN ⟨(ψ.symm n).2, hxN⟩
    refine ⟨ψ.symm n, hxJ, ?_⟩
    simp
  have hJne' : Jω ≠ ⊤ := by
    intro htop
    apply hJne
    refine le_antisymm hJL fun y hy => ?_
    have hmem : ψ ⟨y, hy⟩ ∈ Jω := htop ▸ Subgroup.mem_top _
    obtain ⟨z, hz, hzy⟩ := hmem
    have : z = ⟨y, hy⟩ := ψ.injective hzy
    rw [this] at hz
    exact hz
  set E' : Subgroup omegaT := E.subgroupOf omegaT with hE'
  have hE'p : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEω).symm
  have hE'J : E' ≤ Jω := by
    intro z hz
    have hfz := hfixE z hz
    have hxJ : ((ψ.symm z : ↥L) : Y) ∈ J := hfix _ (ψ.symm z).2 (by
      have := congrArg Subtype.val hfz
      simpa [conjOnNormalizer_apply] using this)
    exact ⟨ψ.symm z, hxJ, by simp⟩
  intro x hx y hy
  have := hFlag omegaT (CFSG.EvenSmallLie.OmegaEight.statedClassicalModel_omegaT) Jω
    (hTωp.toSylow hTωidx) hN hJne' E' hE'J hE'p ⟨x, hEω hx⟩ hx ⟨y, hEω hy⟩ hy
  exact congrArg Subtype.val this

theorem fixPerfThreeTrialityD
    (hZ : OddCenterRest) (hFlag : TrialityFlagInput) : FixPerfThreeTrialityD := by
  intro Y _ _ L J u h hu hD
  obtain ⟨ψ⟩ := exists_mulEquiv_omegaT hZ h hD
  obtain ⟨a, haA, ha3, haω, hform⟩ := exists_outer_of_conj h.norm h.pow hu ψ
  obtain ⟨E, hEω, hEc, hE3, x, hx, y, hy, hxy⟩ := exists_nonabelian_three_cent_of_outer haA ha3 haω
  apply hxy
  refine abelian_of_flag hFlag h.parab.parab.1 h.parab.ne_top h.parab.parab.2 h.norm h.fix ψ E hEω
    hE3 ?_ x hx y hy
  intro e he
  apply ψ.injective
  apply Subtype.ext
  rw [MulEquiv.apply_symm_apply, hform e, hEc e he]
  group

end CFSG.HardMathSupport.Curtis.Coordinator
