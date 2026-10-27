module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpETwo
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNMain

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

private theorem sq_mem_of_card_le_two_mul {G : Type*} [Group G] {E K : Subgroup G} [Finite E]
    (h : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ K)) {e : G} (he : e ∈ E) : e ^ 2 ∈ K := by
  set K' : Subgroup E := (E ⊓ K).subgroupOf E
  have hcard : Nat.card K' = Nat.card ↥(E ⊓ K) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : E ⊓ K ≤ E)).toEquiv
  have hmul := K'.card_mul_index
  have hpos : 0 < Nat.card K' := Nat.card_pos
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have hi : K'.index = 1 ∨ K'.index = 2 := by
    rcases Nat.lt_or_ge K'.index 3 with h3 | h3
    · have h0 : K'.index ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hmul
        omega
      omega
    · exfalso
      have : Nat.card K' * 3 ≤ Nat.card K' * K'.index := Nat.mul_le_mul_left _ h3
      omega
  have hmem : (⟨e, he⟩ : E) ^ 2 ∈ K' := by
    rcases hi with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact mem_top _
    · exact Subgroup.sq_mem_of_index_two h2 _
  exact (mem_inf.mp (mem_subgroupOf.mp hmem)).2

private theorem card_fusionZStar_quot_le {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) :
    Nat.card (B ⧸ Open.fusionZStar B) ≤ Nat.card (A ⧸ Open.fusionZStar A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : (pPrimeCore 2 A).map f ≤ pPrimeCore 2 B :=
    Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective 2 f hf
  have hle : Open.fusionZStar A ≤ (Open.fusionZStar B).comap f := by
    intro a ha
    rw [mem_comap, GSThmB.OddQuot.mem_fusionZStar_iff]
    intro b
    obtain ⟨m, rfl⟩ := hf b
    rw [← map_commutatorElement]
    exact hO (mem_map_of_mem f (GSThmB.OddQuot.mem_fusionZStar_iff.mp ha m))
  exact Nat.card_le_card_of_surjective _
    (QuotientGroup.map_surjective_of_surjective _ _ f (QuotientGroup.mk_surjective.comp hf) hle)

private noncomputable def centerQuotAut (L : Type*) [Group L] :
    MulAut L →* MulAut (L ⧸ center L) where
  toFun α := QuotientGroup.congr (center L) (center L) α (Subgroup.map_center_eq α)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    simp only [QuotientGroup.congr_mk']
    rfl
  map_mul' α β := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    simp only [QuotientGroup.congr_mk', MulAut.mul_apply]

private theorem centerQuotAut_mk {L : Type*} [Group L] (α : MulAut L) (l : L) :
    centerQuotAut L α (QuotientGroup.mk' (center L) l) = QuotientGroup.mk' (center L) (α l) := by
  simp only [centerQuotAut, MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.congr_mk']

private theorem isPComponent_map_center {L : Type} [Group L] [Finite L]
    {Q : Subgroup (MulAut L)} {Tb : Subgroup L} (hTbF : Tb ≤ EvenPump.autFixed Q)
    (hTb : IsPComponent 2 (Tb.subgroupOf (EvenPump.autFixed Q))) :
    Tb.map (QuotientGroup.mk' (center L)) ≤ EvenPump.autFixed (Q.map (centerQuotAut L)) ∧
      IsPComponent 2 ((Tb.map (QuotientGroup.mk' (center L))).subgroupOf
        (EvenPump.autFixed (Q.map (centerQuotAut L)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* L ⧸ center L := QuotientGroup.mk' (center L)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = center L := QuotientGroup.ker_mk' _
  have hΨ : ∀ (α : MulAut L) (l : L), centerQuotAut L α (π l) = π (α l) :=
    fun α l => centerQuotAut_mk α l
  set F := EvenPump.autFixed (Q.map (centerQuotAut L)) with hFdef
  have hπF : (EvenPump.autFixed Q).map π ≤ F := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hFdef, EvenPump.mem_autFixed]
    rintro _ ⟨α, hα, rfl⟩
    rw [hΨ, hl α hα]
  have hnorm : (((EvenPump.autFixed Q).map π).subgroupOf F).Normal := by
    constructor
    rintro ⟨y₀, hy₀F⟩ hy ⟨g₀, hg₀F⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨l, rfl⟩ := hπs g₀
    refine ⟨l * c * l⁻¹, ?_, by simp only [map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]⟩
    refine EvenPump.mem_autFixed.mpr fun α hα => ?_
    have h1 : π (α l) = π l := by
      have h2 := (EvenPump.mem_autFixed.mp hg₀F) (centerQuotAut L α) ⟨α, hα, rfl⟩
      rwa [hΨ] at h2
    have hz : l⁻¹ * α l ∈ center L := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [map_mul, map_mul, map_inv, (EvenPump.mem_autFixed.mp hc) α hα]
    have hzc := (mem_center_iff.mp hz) c
    calc α l * c * (α l)⁻¹ = l * ((l⁻¹ * α l) * c) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * α l)) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by rw [hzc]
      _ = l * c * l⁻¹ := by group
  have hT1 : IsPComponent 2 ((Tb.map π).subgroupOf ((EvenPump.autFixed Q).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 (π.subgroupMap (EvenPump.autFixed Q))
      (π.subgroupMap_surjective _) ?_ (Tb.subgroupOf (EvenPump.autFixed Q)) hTb
    · rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap π hTbF] at h
    · intro x hx
      have h1 : (x : L) ∈ center L := by
        rw [← hπk, MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact mem_center_iff.mpr fun y => Subtype.ext ((mem_center_iff.mp h1) y)
  have hTF' : Tb.map π ≤ (EvenPump.autFixed Q).map π := map_mono hTbF
  exact ⟨hTF'.trans hπF, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTF' hπF
    hnorm.isSubnormal).mpr hT1⟩

private theorem exists_reduced_pump_hom {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) {E : Subgroup H} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set H)) {T : Subgroup H} (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H)))) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L), IsQuasisimple L ∧
      pPrimeCore 2 L = ⊥ ∧ Nonempty (L ≃* ↥M ⧸ pPrimeCore 2 ↥M) ∧
      ∃ ψ : ↥E →* MulAut L, ∃ Tb : Subgroup L, Tb ≤ EvenPump.autFixed ψ.range ∧
        IsPComponent 2 (Tb.subgroupOf (EvenPump.autFixed ψ.range)) ∧
        Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* ↥Tb ⧸ pPrimeCore 2 ↥Tb) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set H) with hNdef
  have hMN : M ≤ N := le_normalizer
  set M₁ : Subgroup N := M.subgroupOf N with hM₁def
  have hM₁n : M₁.Normal := normal_in_normalizer
  set O₁ : Subgroup N := (pPrimeCore 2 ↥M₁).map M₁.subtype with hO₁def
  have hO₁n : O₁.Normal := ConjAct.normal_of_characteristic_of_normal
  set φ : N →* N ⧸ O₁ := QuotientGroup.mk' O₁ with hφdef
  have hφ : ¬ 2 ∣ Nat.card φ.ker := by
    rw [hφdef, QuotientGroup.ker_mk', hO₁def,
      Subgroup.card_map_of_injective M₁.subtype_injective]
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  let eM : ↥M₁ ≃* ↥M := subgroupOfEquivOfLe hMN
  set Mb : Subgroup (N ⧸ O₁) := M₁.map φ with hMbdef
  have hMbn : Mb.Normal := hM₁n.map φ (QuotientGroup.mk'_surjective O₁)
  let f₁ : ↥M₁ →* ↥Mb := φ.subgroupMap M₁
  have hf₁s : Function.Surjective f₁ := φ.subgroupMap_surjective M₁
  have hf₁k : f₁.ker = pPrimeCore 2 ↥M₁ := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : φ (m : N) = 1 := congrArg Subtype.val h
      have h2 : (m : N) ∈ O₁ := (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨m', hm', hmm'⟩ := h2
      rw [← M₁.subtype_injective hmm']
      exact hm'
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem M₁.subtype h)
  let eL : ↥Mb ≃* ↥M ⧸ pPrimeCore 2 ↥M :=
    ((QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hf₁k)).trans (Sol78.coreQuotCongr eM)
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have hMbq : IsQuasisimple ↥Mb := LocalCores.isQuasisimple_of_mulEquiv eL.symm hMq
  have hMbO : pPrimeCore 2 ↥Mb = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 eL
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.injective).mp h1
  set E₁ : Subgroup N := E.subgroupOf N with hE₁def
  have hE₁ : IsPGroup 2 E₁ := hE.of_equiv (subgroupOfEquivOfLe hEN).symm
  set Eb : Subgroup (N ⧸ O₁) := E₁.map φ with hEbdef
  let ι : ↥E →* N := inclusion hEN
  let ψ : ↥E →* MulAut ↥Mb := (MulAut.conjNormal (H := Mb)).comp (φ.comp ι)
  have hψ : ∀ e : ↥E, ∀ y : ↥Mb, ((ψ e y : ↥Mb) : N ⧸ O₁) = φ (ι e) * y * (φ (ι e))⁻¹ :=
    fun e y => MulAut.conjNormal_apply _ _
  have hfix : EvenPump.autFixed ψ.range =
      (Mb ⊓ centralizer (Eb : Set (N ⧸ O₁))).subgroupOf Mb := by
    ext y
    rw [EvenPump.mem_autFixed, mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨y.2, ?_⟩
      rintro _ ⟨e₁, he₁, rfl⟩
      have h1 := congrArg Subtype.val (h (ψ ⟨(e₁ : H), he₁⟩) ⟨_, rfl⟩)
      rw [hψ] at h1
      have h2 : ι ⟨(e₁ : H), he₁⟩ = e₁ := Subtype.ext rfl
      rw [h2] at h1
      calc φ e₁ * (y : N ⧸ O₁) = φ e₁ * y * (φ e₁)⁻¹ * φ e₁ := by group
        _ = y * φ e₁ := by rw [h1]
    · rintro ⟨-, hc⟩ _ ⟨e, rfl⟩
      apply Subtype.ext
      rw [hψ, hc (φ (ι e)) ⟨ι e, e.2, rfl⟩, mul_inv_cancel_right]
  refine ⟨↥Mb, inferInstance, inferInstance, hMbq, hMbO, ⟨eL⟩, ψ, ?_⟩
  set T₁ : Subgroup N := T.subgroupOf N with hT₁def
  have hT₁Y : T₁ ≤ (M ⊓ centralizer (E : Set H)).subgroupOf N := fun t ht =>
    mem_subgroupOf.mpr ⟨hTM ht, hTE ht⟩
  have hT₁ : IsPComponent 2 (T₁.subgroupOf ((M ⊓ centralizer (E : Set H)).subgroupOf N)) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hMN) 2
      Nat.prime_two).mpr
      (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTM hTE) inf_le_right hT)
  have hmap := GSThmB.OddQuot.isPComponent_map φ hφ hT₁Y hT₁
  have hcop : ((M ⊓ centralizer (E : Set H)).subgroupOf N).map φ =
      Mb ⊓ centralizer (Eb : Set (N ⧸ O₁)) := by
    rw [EvenPump.inf_centralizer_subgroupOf hEN M]
    exact GSThmB.OddQuot.map_inf_centralizer φ hE₁
      (by rw [normalizer_eq_top_iff.mpr hM₁n]; exact le_top)
      (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict φ hφ M₁)
  rw [hcop] at hmap
  have hT₁Mb : T₁.map φ ≤ Mb := map_mono fun t ht => hTM ht
  refine ⟨(T₁.map φ).subgroupOf Mb, ?_, ?_, ?_⟩
  · rw [hfix]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact (map_mono hT₁Y).trans hcop.le hy
  · rw [hfix]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hmap
  · let eT₁ : ↥T₁ ≃* ↥T := subgroupOfEquivOfLe (hTM.trans hMN)
    obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (φ.subgroupMap T₁)
      (φ.subgroupMap_surjective T₁) (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap φ hφ T₁)
    let eTb : ↥((T₁.map φ).subgroupOf Mb) ≃* ↥(T₁.map φ) := subgroupOfEquivOfLe hT₁Mb
    exact ⟨(Sol78.coreQuotCongr eT₁).symm.trans (e₂.trans (Sol78.coreQuotCongr eTb).symm)⟩

private theorem subgroupOf_data {X : Type} [Group X] [Finite X] {H M E T : Subgroup X}
    (hEH : E ≤ H) (hEN : E ≤ normalizer (M : Set X)) (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X)))) :
    E.subgroupOf H ≤ normalizer ((M.subgroupOf H : Subgroup H) : Set H) ∧
      T.subgroupOf H ≤ M.subgroupOf H ∧
      T.subgroupOf H ≤ centralizer ((E.subgroupOf H : Subgroup H) : Set H) ∧
      IsPComponent 2 ((T.subgroupOf H).subgroupOf
        (centralizer ((E.subgroupOf H : Subgroup H) : Set H))) := by
  have hCH : (H ⊓ centralizer (E : Set X)).subgroupOf H =
      centralizer ((E.subgroupOf H : Subgroup H) : Set H) := by
    rw [EvenPump.inf_centralizer_subgroupOf hEH H, subgroupOf_self, top_inf_eq]
  refine ⟨fun e he => ?_, fun t ht => hTM ht, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    exact mem_normalizer_iff.mp (hEN he) h
  · rw [← hCH]
    exact fun t ht => mem_subgroupOf.mpr ⟨t.2, hTE ht⟩
  · rw [← hCH]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hT

theorem pumpStep (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    {H : Type} [Group H] [Finite H] (hK : SectionRank.IsKGroupCat H)
    {M : Subgroup H} (hM : IsPComponent 2 M) {E : Subgroup H} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set H))
    (hEk : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ coreActionKernel M))
    {T : Subgroup H} (hTM : T ≤ M) (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H))))
    (hTt : (∃ m : ℕ, Even m ∧ 10 ≤ m ∧
        Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin m))) ∨
      Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* Blueprint.NativeSporadic.Carrier .HN)) :
    (∃ n : ℕ, Even n ∧ 10 ≤ n ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n))) ∨
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, _, hLK, hLq, hLO, ⟨eL⟩, Q, hQ2, hQc, Tb, hTbF, hTb, ⟨eTb⟩⟩ :=
    EvenPump.exists_reduced_pump hK hM hE hEN (fun e he => sq_mem_of_card_le_two_mul hEk he) hEk
      hTM hTE hT
  have hQ : IsPGroup 2 Q := EvenPump.isPGroup_of_mul_self hQ2
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  let eLM : L ⧸ center L ≃* ↥M ⧸ Open.fusionZStar ↥M :=
    (Sol78.centerQuotCongr eL).trans (Sol78.coreQuotientCenterEquiv ↥M)
  rcases (show Nat.card Q = 1 ∨ Nat.card Q = 2 by
      have := Nat.card_pos (α := Q)
      omega) with hQ1 | hQ2'
  ·
    have hQb : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQ1
    have hFtop : EvenPump.autFixed Q = ⊤ := by
      rw [eq_top_iff]
      intro l _ q hq
      rw [hQb, mem_bot] at hq
      rw [hq]
      rfl
    have hTbp : IsPComponent 2 Tb :=
      (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 Tb (EvenPump.autFixed Q) hTbF
        (by rw [hFtop]; exact Subgroup.Normal.isSubnormal inferInstance)).mp hTb
    have hTbtop : Tb = ⊤ := by
      rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hLq
        ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 Tb).mp hTbp).1 with
        h | h
      · exact h
      · exfalso
        have hp : ⁅Tb, Tb⁆ = Tb :=
          Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hTbp)
        have hc : ⁅Tb, Tb⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr fun t ht =>
          mem_centralizer_iff.mpr fun u _ => (mem_center_iff.mp (h ht) u)
        exact (Subgroup.nontrivial_iff_ne_bot Tb).mp
          (CatalogueBAlternating.pComponent_nontrivial hTbp) (hp.symm.trans hc)
    let eLT : ↥Tb ≃* L := (MulEquiv.subgroupCongr hTbtop).trans Subgroup.topEquiv
    have hTO : pPrimeCore 2 ↥Tb = ⊥ := by
      have h1 := pPrimeCore_map_iso 2 eLT
      rw [hLO] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ eLT.injective).mp h1
    let eTM : ↥T ⧸ pPrimeCore 2 ↥T ≃* ↥M ⧸ pPrimeCore 2 ↥M :=
      eTb.trans (((QuotientGroup.quotientMulEquivOfEq hTO).trans QuotientGroup.quotientBot).trans
        (eLT.trans eL))
    let eZ : ↥T ⧸ Open.fusionZStar ↥T ≃* ↥M ⧸ Open.fusionZStar ↥M :=
      Sol78.fusionZStarQuotOfCore eTM
    rcases hTt with ⟨m, hm, hm10, ⟨eT⟩⟩ | ⟨⟨eT⟩⟩
    · exact Or.inl ⟨m, hm, hm10, ⟨eZ.symm.trans ((QuotientGroup.quotientMulEquivOfEq
        (EvenPump.fusionZStar_eq_of_alt (by omega) eT)).trans eT)⟩⟩
    · exact Or.inr ⟨eZ.symm.trans eT⟩
  ·
    have := EvenPump.finite_pumpY Q
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ↥Q, q₀ ≠ 1 := by
      by_contra h
      push Not at h
      have h1 : Nat.card Q = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
      omega
    have hq₀2 : (q₀ : MulAut L) * q₀ = 1 := hQ2 _ q₀.2
    have hq₀ne : (q₀ : MulAut L) ≠ 1 := fun h => hq₀ (Subtype.ext h)
    have hzp : zpowers q₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hQ2']
      exact orderOf_eq_prime (by rw [sq]; exact Subtype.ext hq₀2) hq₀
    set x : EvenPump.PumpY Q := SemidirectProduct.inr q₀
    have hx : orderOf x = 2 := EvenPump.orderOf_inr Q hq₀2 hq₀ne
    have hrange : (SemidirectProduct.inr : ↥Q →* EvenPump.PumpY Q).range = zpowers x := by
      rw [MonoidHom.range_eq_map, ← hzp, MonoidHom.map_zpowers]
    have hC : centralizer (((SemidirectProduct.inr : ↥Q →* EvenPump.PumpY Q).range :
        Subgroup (EvenPump.PumpY Q)) : Set (EvenPump.PumpY Q)) =
        centralizer ({x} : Set (EvenPump.PumpY Q)) := by
      rw [hrange, centralizer_zpowers_eq]
    obtain ⟨hT'C, hT'pc⟩ := EvenPump.isPComponent_centralizer_range Q hTbF hTb
    rw [hC] at hT'C hT'pc
    set T' := Tb.map (SemidirectProduct.inl : L →* EvenPump.PumpY Q)
    let eT'T : ↥Tb ≃* ↥T' := Tb.equivMapOfInjective _ SemidirectProduct.inl_injective
    let eTT' : ↥T ⧸ pPrimeCore 2 ↥T ≃* ↥T' ⧸ pPrimeCore 2 ↥T' :=
      eTb.trans (Sol78.coreQuotCongr eT'T)
    have hxN : x ∈ normalizer ((EvenPump.pumpL Q : Subgroup (EvenPump.PumpY Q)) :
        Set (EvenPump.PumpY Q)) := by
      have := EvenPump.pumpL_normal Q
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top x
    have hT'M : T' ≤ EvenPump.pumpL Q := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
    obtain ⟨eP⟩ := EvenPump.nonempty_pumpL_fusionZStar_equiv Q hLO
    have hYK := EvenPump.isKGroupCat_pumpY Q hLK hQ
    have hLc := EvenPump.isPComponent_pumpL Q hLq hLO
    rcases hTt with ⟨m, hm, hm10, ⟨eT⟩⟩ | ⟨⟨eT⟩⟩
    ·
      let eT'q : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin m) := eTT'.symm.trans eT
      have hT'Z : Open.fusionZStar ↥T' = pPrimeCore 2 ↥T' :=
        EvenPump.fusionZStar_eq_of_alt (by omega) eT'q
      have hex : (Open.fusionZStar ↥T').map T'.subtype ≤ (pPrimeCore 2 ↥T').map T'.subtype ⊔
          (Open.fusionZStar ↥(EvenPump.pumpL Q)).map (EvenPump.pumpL Q).subtype := by
        rw [hT'Z]
        exact le_sup_left
      let eZ : ↥T' ⧸ Open.fusionZStar ↥T' ≃* alternatingGroup (Fin m) :=
        (QuotientGroup.quotientMulEquivOfEq hT'Z).trans eT'q
      rcases hcore (EvenPump.PumpY Q) hYK (EvenPump.pumpL Q) hLc x hx hxN T' hT'M hT'C hT'pc hex
          m hm hm10 ⟨eZ⟩ with ⟨m', hm', hmm', ⟨eY⟩⟩ | ⟨-, ⟨eY⟩⟩
      · exact Or.inl ⟨m', hm', by omega, ⟨eLM.symm.trans (eP.symm.trans eY)⟩⟩
      · exact Or.inr ⟨eLM.symm.trans (eP.symm.trans eY)⟩
    ·
      obtain ⟨eY⟩ := hHN (EvenPump.PumpY Q) hYK (EvenPump.pumpL Q) hLc x hx hxN T' hT'M hT'C
        hT'pc ⟨(Sol78.fusionZStarQuotOfCore eTT').symm.trans eT⟩
      exact Or.inr ⟨eLM.symm.trans (eP.symm.trans eY)⟩

theorem pumpStep' (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    {X : Type} [Group X] [Finite X] {H M E T : Subgroup X} (hK : SectionRank.IsKGroupCat ↥H)
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) (hEH : E ≤ H) (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set X))
    (hEk : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ coreActionKernel M))
    (hTM : T ≤ M) (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X))))
    (hTt : (∃ m : ℕ, Even m ∧ 10 ≤ m ∧
        Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin m))) ∨
      Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* Blueprint.NativeSporadic.Carrier .HN)) :
    (∃ n : ℕ, Even n ∧ 10 ≤ n ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n))) ∨
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  obtain ⟨hEN', hTM', hTE', hT'⟩ := subgroupOf_data hEH hEN hTM hTE hT
  have hEk' : Nat.card ↥(E.subgroupOf H) ≤
      2 * Nat.card ↥(E.subgroupOf H ⊓ coreActionKernel (M.subgroupOf H)) := by
    have h1 : Nat.card ↥(E.subgroupOf H) = Nat.card E :=
      Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv
    have h2 : Nat.card ↥(E ⊓ coreActionKernel M) ≤
        Nat.card ↥(E.subgroupOf H ⊓ coreActionKernel (M.subgroupOf H)) := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hEH :
        E ⊓ coreActionKernel M ≤ H)).toEquiv]
      refine Subgroup.card_le_of_le fun g hg => ?_
      rw [mem_subgroupOf, mem_inf] at hg
      exact mem_inf.mpr ⟨hg.1, (FooteLit.mem_coreActionKernel_subgroupOf_iff hMH g).mpr hg.2⟩
    omega
  let eM : ↥(M.subgroupOf H) ≃* ↥M := subgroupOfEquivOfLe hMH
  let eT : ↥(T.subgroupOf H) ≃* ↥T := subgroupOfEquivOfLe (hTM.trans hMH)
  have hTt' : (∃ m : ℕ, Even m ∧ 10 ≤ m ∧ Nonempty (↥(T.subgroupOf H) ⧸
      pPrimeCore 2 ↥(T.subgroupOf H) ≃* alternatingGroup (Fin m))) ∨
      Nonempty (↥(T.subgroupOf H) ⧸ Open.fusionZStar ↥(T.subgroupOf H) ≃*
        Blueprint.NativeSporadic.Carrier .HN) := by
    rcases hTt with ⟨m, hm, hm10, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨m, hm, hm10, ⟨(Sol78.coreQuotCongr eT).trans e⟩⟩
    · exact Or.inr ⟨(Sol78.fusionZStarQuotCongr eT).trans e⟩
  rcases pumpStep hcore hHN hK hM (hE.of_equiv (subgroupOfEquivOfLe hEH).symm) hEN' hEk' hTM'
      hTE' hT' hTt' with ⟨n, hn, hn10, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨n, hn, hn10, ⟨(Sol78.fusionZStarQuotCongr eM).symm.trans e⟩⟩
  · exact Or.inr ⟨(Sol78.fusionZStarQuotCongr eM).symm.trans e⟩

theorem center_eq_bot_of_autFixed_alt' {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    {n : ℕ} (hn : 8 ≤ n) (eA : L ⧸ center L ≃* alternatingGroup (Fin n))
    {Q : Subgroup (MulAut L)} (hQ : IsPGroup 2 Q) {T : Subgroup L}
    (hTF : T ≤ EvenPump.autFixed Q) (hT : IsPComponent 2 (T.subgroupOf (EvenPump.autFixed Q)))
    {s : ℕ} (hs : 6 ≤ s) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin s)) :
    center L = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := hq.1
  set π : L →* alternatingGroup (Fin n) := eA.toMonoidHom.comp (QuotientGroup.mk' (center L))
    with hπdef
  have hπs : Function.Surjective π := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eA.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : Nat.card (center L) ∣ 2 := by
    have h := RankTwoAlt.card_ker_dvd_two hq.1.commutator_eq_top hn hπs hπk.le
    rwa [hπk] at h
  have hTZ : ∀ z ∈ T, z ∈ center L → z = 1 := by
    intro z hzT hzZ
    have hzc : (⟨z, hzT⟩ : T) ∈ center T :=
      mem_center_iff.mpr fun t => Subtype.ext ((mem_center_iff.mp hzZ) t)
    have h1 : eT (QuotientGroup.mk' _ ⟨z, hzT⟩) ∈ center (alternatingGroup (Fin s)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := eT.surjective a
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, (mem_center_iff.mp hzc) t]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot,
      map_eq_one_iff _ eT.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have ho1 := orderOf_dvd_natCard (⟨⟨z, hzT⟩, h1⟩ : pPrimeCore 2 T)
    have ho2 := orderOf_dvd_natCard (⟨z, hzZ⟩ : center L)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at ho1
    rw [Subgroup.orderOf_mk] at ho2
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 T)) := pPrimeCore_coprime_card
    have h4 : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (ho2.trans hZ2) with h | h
      · exact h
      · exfalso
        rw [h] at ho1
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) ho1
    exact orderOf_eq_one_iff.mp h4
  have hπT : ∀ t₁ ∈ T, ∀ t₂ ∈ T, π t₁ = π t₂ → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ h
    have h3 : t₁⁻¹ * t₂ ∈ center L := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h4 := hTZ _ (mul_mem (inv_mem h₁) h₂) h3
    rw [inv_mul_eq_one] at h4
    exact h4
  set Ψ := EvenPump.altAutHom eA with hΨdef
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega)
    (by omega)
  set cN : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective MulAut.conjNormal hbij with hcNdef
  set Φ : ↥Q →* Equiv.Perm (Fin n) := cN.symm.toMonoidHom.comp (Ψ.comp Q.subtype) with hΦdef
  set Q' : Subgroup (Equiv.Perm (Fin n)) := Φ.range with hQ'def
  have hQ' : IsPGroup 2 Q' := hQ.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hΦ : ∀ (q : ↥Q) (a : alternatingGroup (Fin n)),
      (Φ q : Equiv.Perm (Fin n)) * a * (Φ q)⁻¹ = (Ψ q a : Equiv.Perm (Fin n)) := by
    intro q a
    have h1 : MulAut.conjNormal (Φ q) = Ψ q := cN.apply_symm_apply (Ψ q)
    rw [← h1, MulAut.conjNormal_apply]
  set F : Subgroup (alternatingGroup (Fin n)) := EvenPump.autFixed (Q.map Ψ) with hFdef
  have hFmem : ∀ a : alternatingGroup (Fin n),
      a ∈ F ↔ ∀ τ ∈ Q', τ * (a : Equiv.Perm (Fin n)) = a * τ := by
    intro a
    rw [EvenPump.mem_autFixed]
    constructor
    · rintro h _ ⟨q, rfl⟩
      have h2 := hΦ q a
      rw [h (Ψ q) ⟨q, q.2, rfl⟩] at h2
      calc (Φ q : Equiv.Perm (Fin n)) * a = Φ q * a * (Φ q)⁻¹ * Φ q := by group
        _ = a * Φ q := by rw [h2]
    · rintro h _ ⟨α, hα, rfl⟩
      apply Subtype.ext
      have h2 := hΦ ⟨α, hα⟩ a
      rw [h (Φ ⟨α, hα⟩) ⟨⟨α, hα⟩, rfl⟩, mul_inv_cancel_right] at h2
      exact h2.symm
  have hπF : (EvenPump.autFixed Q).map π ≤ F := by
    rintro _ ⟨l, hl, rfl⟩
    rw [EvenPump.mem_autFixed]
    rintro _ ⟨α, hα, rfl⟩
    show Ψ α (eA (QuotientGroup.mk' _ l)) = eA (QuotientGroup.mk' _ l)
    rw [hΨdef, EvenPump.altAutHom_mk, hl α hα]
  have hnorm : (((EvenPump.autFixed Q).map π).subgroupOf F).Normal := by
    constructor
    rintro ⟨y₀, hy₀F⟩ hy ⟨g₀, hg₀F⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨l, rfl⟩ := hπs g₀
    refine ⟨l * c * l⁻¹, ?_, by simp only [map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]⟩
    refine EvenPump.mem_autFixed.mpr fun α hα => ?_
    have h1 : π (α l) = π l := by
      have h2 := (EvenPump.mem_autFixed.mp hg₀F) (Ψ α) ⟨α, hα, rfl⟩
      rw [show π l = eA (QuotientGroup.mk' _ l) from rfl, hΨdef, EvenPump.altAutHom_mk] at h2
      exact h2
    have hz : l⁻¹ * α l ∈ center L := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [map_mul, map_mul, map_inv, (EvenPump.mem_autFixed.mp hc) α hα]
    have hzc := (mem_center_iff.mp hz) c
    calc α l * c * (α l)⁻¹ = l * ((l⁻¹ * α l) * c) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * α l)) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by rw [hzc]
      _ = l * c * l⁻¹ := by group
  have hT1 : IsPComponent 2 ((T.map π).subgroupOf ((EvenPump.autFixed Q).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 (π.subgroupMap (EvenPump.autFixed Q))
      (π.subgroupMap_surjective _) ?_ (T.subgroupOf (EvenPump.autFixed Q)) hT
    · rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap π hTF] at h
    · intro x hx
      have h1 : (x : L) ∈ center L := by
        rw [← hπk, MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact mem_center_iff.mpr fun y => Subtype.ext ((mem_center_iff.mp h1) y)
  have hTF' : T.map π ≤ (EvenPump.autFixed Q).map π := map_mono hTF
  have hT2 : IsPComponent 2 ((T.map π).subgroupOf F) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTF' hπF
      hnorm.isSubnormal).mpr hT1
  set ι := (alternatingGroup (Fin n)).subtype with hιdef
  set Nq := normalizer (Q' : Set (Equiv.Perm (Fin n))) with hNqdef
  set Fp := F.map ι with hFpdef
  have hFpN : Fp ≤ Nq := by
    rintro _ ⟨a, ha, rfl⟩
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    exact (hFmem a).mp ha
  have hFpn : (Fp.subgroupOf Nq).Normal := by
    constructor
    rintro ⟨x, hxN⟩ hx ⟨g, hg⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    have hga : g * (a : Equiv.Perm (Fin n)) * g⁻¹ ∈ alternatingGroup (Fin n) :=
      (alternatingGroup.normal (α := Fin n)).conj_mem _ a.2 g
    refine ⟨⟨_, hga⟩, (hFmem _).mpr fun τ hτ => ?_, rfl⟩
    have h1 : g⁻¹ * τ * g ∈ Q' := by
      have h2 := (mem_normalizer_iff.mp (inv_mem hg) τ).mp hτ
      rwa [inv_inv] at h2
    have h3 := (hFmem a).mp ha _ h1
    calc τ * (g * (a : Equiv.Perm (Fin n)) * g⁻¹) = g * ((g⁻¹ * τ * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * τ * g)) * g⁻¹ := by rw [h3]
      _ = g * (a : Equiv.Perm (Fin n)) * g⁻¹ * τ := by group
  set Tp := (T.map π).map ι with hTpdef
  have hTpFp : Tp ≤ Fp := map_mono (hTF'.trans hπF)
  have hι : ¬ 2 ∣ Nat.card ι.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (subtype_injective _), Subgroup.card_bot]
    norm_num
  have hT3 : IsPComponent 2 (Tp.subgroupOf Fp) :=
    GSThmB.OddQuot.isPComponent_map ι hι (hTF'.trans hπF) hT2
  have hT4 : IsPComponent 2 (Tp.subgroupOf Nq) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTpFp hFpN
      hFpn.isSubnormal).mpr hT3
  obtain ⟨hdeg, hLeq, -⟩ :=
    CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q' hQ' (Tp.subgroupOf Nq) hT4
  set Ω := MulAction.fixedPoints Q' (Fin n) with hΩdef
  obtain ⟨j⟩ : Nonempty (Fin 4 ↪ Ω) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    omega
  set ιn : Fin 4 ↪ Fin n := j.trans (Function.Embedding.subtype _) with hιndef
  have hne : ∀ a b : Fin 4, a ≠ b → j a ≠ j b := fun a b h => j.injective.ne h
  have key : ∀ (a b c d : Fin 4), a ≠ b → c ≠ d → ∃ t ∈ T,
      (π t : Equiv.Perm (Fin n)) =
        Equiv.Perm.viaEmbeddingHom ιn (Equiv.swap a b * Equiv.swap c d) := by
    intro a b c d hab hcd
    have hδ : Equiv.swap (j a) (j b) * Equiv.swap (j c) (j d) ∈ alternatingGroup Ω :=
      Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (hne a b hab) (hne c d hcd)
    have hd : CatalogueBAlternating.fixedPointsNormalizerHom Q'
        (Equiv.swap (j a) (j b) * Equiv.swap (j c) (j d)) ∈ Tp.subgroupOf Nq := by
      rw [hLeq]
      exact mem_map_of_mem _ hδ
    obtain ⟨u, ⟨t, ht, rfl⟩, hu⟩ := hd
    refine ⟨t, ht, ?_⟩
    rw [show (π t : Equiv.Perm (Fin n)) = ι (π t) from rfl, hu, Subgroup.coe_subtype,
      CatalogueBAlternating.fixedPointsNormalizerHom_coe, map_mul, map_mul,
      Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq,
      RankTwoAlt.viaEmbeddingHom_swap, RankTwoAlt.viaEmbeddingHom_swap]
    rfl
  obtain ⟨t₁, ht₁, hx⟩ := key 0 1 2 3 (by decide) (by decide)
  obtain ⟨t₂, ht₂, hy⟩ := key 0 2 1 3 (by decide) (by decide)
  have hcomm : t₁ * t₂ = t₂ * t₁ := by
    apply hπT _ (mul_mem ht₁ ht₂) _ (mul_mem ht₂ ht₁)
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, ← map_mul, ← map_mul,
      show (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) *
          (Equiv.swap 0 2 * Equiv.swap 1 3) =
        (Equiv.swap 0 2 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) by decide]
  rcases (Nat.dvd_prime Nat.prime_two).mp hZ2 with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd hcomm (RankTwoAlt.mul_ne_mul_of_card_ker_eq_two hn hπs hπk.le
      (by rw [hπk]; exact h2) ιn hx hy)

theorem exists_reduced_pump_pGroup {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) {E : Subgroup H} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set H)) {T : Subgroup H} (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H)))) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L), IsQuasisimple L ∧
      pPrimeCore 2 L = ⊥ ∧ Nonempty (L ≃* ↥M ⧸ pPrimeCore 2 ↥M) ∧
      ∃ Q : Subgroup (MulAut L), IsPGroup 2 Q ∧
        ∃ Tb : Subgroup L, Tb ≤ EvenPump.autFixed Q ∧
          IsPComponent 2 (Tb.subgroupOf (EvenPump.autFixed Q)) ∧
          Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* ↥Tb ⧸ pPrimeCore 2 ↥Tb) := by
  obtain ⟨L, _, _, hLq, hLO, eL, ψ, Tb, hTbF, hTb, eTb⟩ :=
    exists_reduced_pump_hom hM hE hEN hTM hTE hT
  exact ⟨L, inferInstance, inferInstance, hLq, hLO, eL, ψ.range,
    hE.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective, Tb, hTbF, hTb, eTb⟩

theorem nonempty_pPrimeCore_equiv_alt_of_fixed {H : Type} [Group H] [Finite H]
    {M : Subgroup H} (hM : IsPComponent 2 M) {E : Subgroup H} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set H)) {T : Subgroup H} (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H))))
    {s : ℕ} (hs : 6 ≤ s) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin s))
    {n : ℕ} (hn : 8 ≤ n) (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n)) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) := by
  obtain ⟨L, _, _, hLq, -, ⟨eL⟩, Q, hQ, Tb, hTbF, hTb, ⟨eTb⟩⟩ :=
    exists_reduced_pump_pGroup hM hE hEN hTM hTE hT
  let eLZ : L ⧸ center L ≃* alternatingGroup (Fin n) :=
    (Sol78.centerQuotCongr eL).trans ((Sol78.coreQuotientCenterEquiv ↥M).trans eM)
  have hZ := center_eq_bot_of_autFixed_alt' hLq hn eLZ hQ hTbF hTb hs (eTb.symm.trans eT)
  exact ⟨eL.symm.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans eLZ)⟩

theorem nonempty_pPrimeCore_equiv_alt_of_fixed' {X : Type} [Group X] [Finite X]
    {H M E T : Subgroup X} (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) (hEH : E ≤ H)
    (hE : IsPGroup 2 E) (hEN : E ≤ normalizer (M : Set X)) (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X))))
    {s : ℕ} (hs : 6 ≤ s) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin s))
    {n : ℕ} (hn : 8 ≤ n) (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n)) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) := by
  obtain ⟨hEN', hTM', hTE', hT'⟩ := subgroupOf_data hEH hEN hTM hTE hT
  let eM' : ↥(M.subgroupOf H) ≃* ↥M := subgroupOfEquivOfLe hMH
  let eT' : ↥(T.subgroupOf H) ≃* ↥T := subgroupOfEquivOfLe (hTM.trans hMH)
  obtain ⟨e⟩ := nonempty_pPrimeCore_equiv_alt_of_fixed hM
    (hE.of_equiv (subgroupOfEquivOfLe hEH).symm) hEN' hTM' hTE' hT' hs
    ((Sol78.coreQuotCongr eT').trans eT) hn ((Sol78.fusionZStarQuotCongr eM').trans eM)
  exact ⟨(Sol78.coreQuotCongr eM').symm.trans e⟩

theorem exists_autFixed_pComponent_image {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) {E : Subgroup H} (hEN : E ≤ normalizer (M : Set H))
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : Nat.card E ≤ 2) {T : Subgroup H} (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H)))) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), Nonempty (S ≃* ↥M ⧸ Open.fusionZStar ↥M) ∧
      ∃ Q : Subgroup (MulAut S), (∀ q ∈ Q, q * q = 1) ∧ Nat.card Q ≤ 2 ∧
        ∃ Tb : Subgroup S, Tb ≤ EvenPump.autFixed Q ∧
          IsPComponent 2 (Tb.subgroupOf (EvenPump.autFixed Q)) ∧
          Nat.card (↥Tb ⧸ Open.fusionZStar ↥Tb) ≤ Nat.card (↥T ⧸ Open.fusionZStar ↥T) := by
  obtain ⟨L, _, _, -, -, ⟨eL⟩, ψ, Tb, hTbF, hTb, ⟨eTb⟩⟩ :=
    exists_reduced_pump_hom hM (EvenPump.isPGroup_of_mul_self hE2) hEN hTM hTE hT
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  obtain ⟨hTF', hTp'⟩ := isPComponent_map_center hTbF hTb
  refine ⟨L ⧸ center L, inferInstance, inferInstance,
    ⟨(Sol78.centerQuotCongr eL).trans (Sol78.coreQuotientCenterEquiv ↥M)⟩,
    ψ.range.map (centerQuotAut L), ?_, ?_, _, hTF', hTp', ?_⟩
  · rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, show e * e = 1 from Subtype.ext (hE2 _ e.2), map_one, map_one]
  · calc Nat.card ↥(ψ.range.map (centerQuotAut L)) ≤ Nat.card ψ.range :=
          Nat.card_le_card_of_surjective _ ((centerQuotAut L).subgroupMap_surjective ψ.range)
      _ ≤ Nat.card E := Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective
      _ ≤ 2 := hEc
  · calc Nat.card (↥(Tb.map (QuotientGroup.mk' (center L))) ⧸
          Open.fusionZStar ↥(Tb.map (QuotientGroup.mk' (center L))))
        ≤ Nat.card (↥Tb ⧸ Open.fusionZStar ↥Tb) := card_fusionZStar_quot_le _
          ((QuotientGroup.mk' (center L)).subgroupMap_surjective Tb)
      _ = Nat.card (↥T ⧸ Open.fusionZStar ↥T) :=
          Nat.card_congr (Sol78.fusionZStarQuotOfCore eTb).symm.toEquiv

theorem exists_autFixed_pComponent_image' {X : Type} [Group X] [Finite X] {H M E T : Subgroup X}
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) (hEH : E ≤ H)
    (hEN : E ≤ normalizer (M : Set X)) (hE2 : ∀ e ∈ E, e * e = 1) (hEc : Nat.card E ≤ 2)
    (hTM : T ≤ M) (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X)))) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), Nonempty (S ≃* ↥M ⧸ Open.fusionZStar ↥M) ∧
      ∃ Q : Subgroup (MulAut S), (∀ q ∈ Q, q * q = 1) ∧ Nat.card Q ≤ 2 ∧
        ∃ Tb : Subgroup S, Tb ≤ EvenPump.autFixed Q ∧
          IsPComponent 2 (Tb.subgroupOf (EvenPump.autFixed Q)) ∧
          Nat.card (↥Tb ⧸ Open.fusionZStar ↥Tb) ≤ Nat.card (↥T ⧸ Open.fusionZStar ↥T) := by
  obtain ⟨hEN', hTM', hTE', hT'⟩ := subgroupOf_data hEH hEN hTM hTE hT
  let eM : ↥(M.subgroupOf H) ≃* ↥M := subgroupOfEquivOfLe hMH
  let eT : ↥(T.subgroupOf H) ≃* ↥T := subgroupOfEquivOfLe (hTM.trans hMH)
  have hEc' : Nat.card ↥(E.subgroupOf H) ≤ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv]
    exact hEc
  obtain ⟨S, _, _, ⟨eS⟩, Q, hQ2, hQc, Tb, hTbF, hTb, hcard⟩ :=
    exists_autFixed_pComponent_image hM hEN' (fun e he => Subtype.ext (hE2 _ he)) hEc' hTM'
      hTE' hT'
  refine ⟨S, inferInstance, inferInstance, ⟨eS.trans (Sol78.fusionZStarQuotCongr eM)⟩, Q, hQ2,
    hQc, Tb, hTbF, hTb, ?_⟩
  rwa [Nat.card_congr (Sol78.fusionZStarQuotCongr eT).toEquiv] at hcard

end CFSG.ComponentClassification.GSThmB.A10T
