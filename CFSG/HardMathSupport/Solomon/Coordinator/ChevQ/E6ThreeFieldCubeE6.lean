module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeFieldCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeOvergroup
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.Sporadic.Suz.Simple

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e6Inndiag
  exists_conj_entrywise_of_not_mem_e6Inndiag)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc (exists_primePower_fixSubfield
  catEquiv_adjointGroup_of_card not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_E6)

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Transport

variable {S : Type*} [Group S]

theorem exists_overgroupData_of_conj {D E : Subgroup (MulAut S)} [D.Normal] {x y ψ : MulAut S}
    (hψ : ψ * x * ψ⁻¹ = y) {J : Subgroup S} (hJy : J ≤ fixedSubgroup y)
    (hgen : J ≤ Subgroup.closure
      {k | k ∈ J ∧ ∃ b ∈ (E ⊓ D).map (MulAut.conj ψ).toMonoidHom, b ≠ 1 ∧ b k = k})
    (hfaith : ∀ a ∈ D, (∀ k ∈ J, a k = k) → a = 1)
    (hmax : ∀ H : Subgroup S, J ≤ H → H ≤ fixedSubgroup y ∨ H = ⊤) :
    ∃ J' : Subgroup S, J' ≤ fixedSubgroup x ∧
      J' ≤ Subgroup.closure {k | k ∈ J' ∧ ∃ b ∈ E ⊓ D, b ≠ 1 ∧ b k = k} ∧
      (∀ a ∈ E ⊓ D, (∀ k ∈ J', a k = k) → a = 1) ∧
      ∀ H : Subgroup S, J' ≤ H → H ≤ fixedSubgroup x ∨ H = ⊤ := by
  have hyψ : ∀ k, y (ψ k) = ψ (x k) := fun k => by
    rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hinvJ : ∀ k ∈ J, ψ⁻¹ k ∈ J.comap ψ.toMonoidHom := fun k hk => by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]
    exact hk
  refine ⟨J.comap ψ.toMonoidHom, fun k hk => ?_, fun k hk => ?_, fun a ha hfix => ?_,
    fun H hJH => ?_⟩
  · refine mem_fixedSubgroup.2 (ψ.injective ?_)
    rw [← hyψ]
    exact mem_fixedSubgroup.1 (hJy (Subgroup.mem_comap.1 hk))
  · have h2 := Subgroup.mem_map_of_mem (ψ⁻¹ : MulAut S).toMonoidHom
      (hgen (Subgroup.mem_comap.1 hk))
    rw [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulAut.inv_apply_self] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨l, ⟨hlJ, _, ⟨b, hb, rfl⟩, hb1, hbl⟩, rfl⟩
    refine ⟨hinvJ l hlJ, b, hb, fun h => hb1 (by rw [h, map_one]), ?_⟩
    have h3 : ψ (b (ψ⁻¹ l)) = l := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply] at hbl
      exact hbl
    exact (MulAut.inv_apply_self S ψ _).symm.trans (congrArg (fun z => ψ⁻¹ z) h3)
  · have h1 : ψ * a * ψ⁻¹ ∈ D := (inferInstance : D.Normal).conj_mem a ha.2 ψ
    refine conj_eq_one_iff.1 (hfaith _ h1 fun k hk => ?_)
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ (hinvJ k hk), MulAut.apply_inv_self]
  · have hJ : J ≤ H.map ψ.toMonoidHom := fun k hk =>
      ⟨ψ⁻¹ k, hJH (hinvJ k hk), MulAut.apply_inv_self S ψ k⟩
    rcases hmax _ hJ with hle | htop
    · refine Or.inl fun h hh => mem_fixedSubgroup.2 (ψ.injective ?_)
      rw [← hyψ]
      exact mem_fixedSubgroup.1 (hle ⟨h, hh, rfl⟩)
    · refine Or.inr (eq_top_iff.2 fun k _ => ?_)
      have hk : ψ k ∈ H.map ψ.toMonoidHom := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨h, hh, hhk⟩ := hk
      rwa [ψ.injective hhk] at hh

end Transport

section KFact

theorem le_closure_fixed_of_kfact (hS : AGLEmbeddingD2.KFactSeitzRankTwo) {S : Type*} [Group S]
    {J : Subgroup S} {d : TauCeti.ValidLieTypeIndex} (e : ↥J ≃* Cat d) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ AGLEmbeddingD2.IsD2SeitzException p d.1) {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) (hAJ : ∀ a ∈ A, ∀ k ∈ J, a k ∈ J)
    (hfaith : ∀ a ∈ A, (∀ k ∈ J, a k = k) → a = 1) :
    J ≤ Subgroup.closure {k | k ∈ J ∧ ∃ b ∈ A, b ≠ 1 ∧ b k = k} := by
  let r : ↥A → MulAut ↥J := fun a =>
    { toFun := fun k => ⟨(a : MulAut S) k, hAJ a a.2 k k.2⟩
      invFun := fun k => ⟨(a : MulAut S)⁻¹ k, hAJ _ (A.inv_mem a.2) k k.2⟩
      left_inv := fun k => Subtype.ext (MulAut.inv_apply_self S _ _)
      right_inv := fun k => Subtype.ext (MulAut.apply_inv_self S _ _)
      map_mul' := fun k l => Subtype.ext (map_mul (a : MulAut S) (k : S) (l : S)) }
  let ρ : ↥A →* MulAut (Cat d) :=
    (MulAut.congr e).toMonoidHom.comp
      { toFun := r
        map_one' := MulEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  have hρ : ∀ (a : ↥A) (k : ↥J), ρ a (e k) = e (r a k) := fun a k => by
    show e (r a (e.symm (e k))) = e (r a k)
    rw [MulEquiv.symm_apply_apply]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (hfaith a a.2 fun k hk => ?_)
    have h1 : e (r a ⟨k, hk⟩) = e ⟨k, hk⟩ := by rw [← hρ, ha, MulAut.one_apply]
    exact congrArg Subtype.val (e.injective h1)
  have hB : IsElemAbelian p ρ.range := by
    have h := (hA.subgroupOf A).map ρ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have hBc : Nat.card ρ.range = p ^ 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hAc]
  have htop := hS d p hp hp2 hpd hex ρ.range hB hBc
  intro s hs
  have h2 := Subgroup.mem_map_of_mem (J.subtype.comp e.symm.toMonoidHom)
    (htop.ge (Subgroup.mem_top (e ⟨s, hs⟩)))
  rw [MonoidHom.map_closure] at h2
  have h3 : (J.subtype.comp e.symm.toMonoidHom) (e ⟨s, hs⟩) = s := by
    show ((e.symm (e ⟨s, hs⟩) : ↥J) : S) = s
    rw [MulEquiv.symm_apply_apply]
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨k, ⟨_, ⟨a, rfl⟩, hx1, hxk⟩, rfl⟩
  refine ⟨(e.symm k).2, a, a.2, fun h => hx1 ?_, ?_⟩
  · rw [show a = 1 from Subtype.ext h, map_one]
  · have h4 : r a (e.symm k) = e.symm k := by
      apply e.injective
      rw [← hρ, MulEquiv.apply_symm_apply]
      exact hxk
    exact congrArg Subtype.val h4

end KFact



section Normalizes

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem commutator_subfieldGroup_eq (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (σ : K ≃+* K) :
    ⁅subfieldGroup τ σ, subfieldGroup τ σ⁆ =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  have hΓ : (subfieldGroup τ σ).map (adjointGroup τ K).subtype = entrywiseFixedGroup τ σ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_entrywiseFixedGroup.2 ⟨x.2, (coe_entrywiseAdjointAut τ σ x).symm.trans
        (congrArg Subtype.val (mem_fixedSubgroup.1 hx))⟩
    · intro hg
      obtain ⟨hgC, hgσ⟩ := mem_entrywiseFixedGroup.1 hg
      exact Subgroup.mem_map.2 ⟨⟨g, hgC⟩, mem_fixedSubgroup.2
        (Subtype.ext ((coe_entrywiseAdjointAut τ σ _).trans hgσ)), rfl⟩
  apply Subgroup.map_injective (adjointGroup τ K).subtype_injective
  rw [Subgroup.map_commutator, hΓ, commutator_entrywiseFixedGroup_eq hτ σ,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (fixedFieldImage_le.trans inf_le_left)]

theorem map_fixedFieldImage_subgroupOf_le
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K)
    {b : MulAut ↥(adjointGroup τ K)} (hb : Commute b (entrywiseAdjointAut τ σ)) :
    ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map b.toMonoidHom ≤
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  have hΓb : (subfieldGroup τ σ).map b.toMonoidHom ≤ subfieldGroup τ σ := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_fixedSubgroup.2 ?_
    have h := congrArg (fun φ : MulAut ↥(adjointGroup τ K) => φ g) hb.eq
    simp only [MulAut.mul_apply] at h
    rw [MulEquiv.coe_toMonoidHom, ← h, mem_fixedSubgroup.1 hg]
  rw [← commutator_subfieldGroup_eq hτ σ, Subgroup.map_commutator]
  exact Subgroup.commutator_mono hΓb hΓb

end Normalizes

section E6

theorem e6Inndiag_eq_ker (K : Type) [Field K] [Finite K] :
    ∃ Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)),
      e6Inndiag K = Θ.ker := by
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  exact ⟨Θ, Subgroup.ext fun α => (mem_ker_iff_mem_e6Inndiag Θ hker α).symm⟩

theorem e6Inndiag_normal (K : Type) [Field K] [Finite K] : (e6Inndiag K).Normal := by
  obtain ⟨Θ, hΘ⟩ := e6Inndiag_eq_ker K
  rw [hΘ]
  infer_instance

theorem card_inf_e6Inndiag {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hED : ¬ E ≤ e6Inndiag K) :
    Nat.card ↥(E ⊓ e6Inndiag K) = 3 ^ 2 := by
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  obtain ⟨Θ, hΘ⟩ := e6Inndiag_eq_ker K
  have hdvd : Nat.card ↥(E ⊓ e6Inndiag K) ∣ 3 ^ 3 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 by omega) with hk1 | rfl | rfl
  · exfalso
    obtain ⟨F, hFE, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
      Nat.prime_three hE inf_le_left bot_le (inf_bot_eq _)
    have hcF : Nat.card ↥(E ⊓ e6Inndiag K) * Nat.card F = 3 ^ 3 := by
      rw [← hEc]
      exact CFSG.SignalizerFunctorTheorem.card_mul_card_complement hE inf_le_left hFE hdisj hsup
    have hFD : F ⊓ e6Inndiag K = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ (E ⊓ e6Inndiag K) ⊓ F := ⟨⟨hFE hy.1, hy.2⟩, hy.1⟩
      rwa [hdisj] at this
    have hF2 : 3 ^ 2 ∣ Nat.card F := by
      have hFdvd : Nat.card F ∣ 3 ^ 3 := ⟨Nat.card ↥(E ⊓ e6Inndiag K), by rw [← hcF, mul_comm]⟩
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hFdvd
      rw [hk', hj', ← pow_add] at hcF
      have hkj := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hcF
      rw [hj']
      exact pow_dvd_pow 3 (by omega)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 3 hF2
    obtain ⟨F₁, hF₁F, hF₁c⟩ : ∃ F₁ ≤ F, Nat.card F₁ = 3 ^ 2 :=
      ⟨F₀.map F.subtype, Subgroup.map_subtype_le F₀,
        by rw [Subgroup.card_map_of_injective F.subtype_injective, hF₀]⟩
    have := (hE.mono (hF₁F.trans hFE)).isElementaryAbelian
    obtain ⟨ι, hιF, hι1, hιker⟩ := exists_ne_one_mem_ker_of_plane Tag.E6 (Or.inl rfl)
      Nat.prime_three (by norm_num) Θ F₁ hF₁c
    have hι : ι ∈ F ⊓ e6Inndiag K := ⟨hF₁F hιF, by rw [hΘ]; exact hιker⟩
    rw [hFD, Subgroup.mem_bot] at hι
    exact hι1 hι
  · exact hk'
  · exfalso
    apply hED
    have heq : E ⊓ e6Inndiag K = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hEc])
    rw [← heq]
    exact inf_le_right

theorem fixedFieldImage_le_closure_of_plane (hS : AGLEmbeddingD2.KFactSeitzRankTwo) {K : Type}
    [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hk2 : 2 < Nat.card (fixSubfield σ)) {A : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))}
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) (hAD : A ≤ e6Inndiag K)
    (hAσ : ∀ b ∈ A, Commute b (entrywiseAdjointAut Tag.E6 σ)) :
    (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) ≤ Subgroup.closure
      {k | k ∈ (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) ∧
        ∃ b ∈ A, b ≠ 1 ∧ b k = k} := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  let q : TauCeti.PrimePower := ⟨ringChar K, n, hℓ, n.pos⟩
  obtain ⟨q₀, hq₀p, hq₀card, -⟩ := exists_primePower_fixSubfield (q := q)
    (hK.trans (TauCeti.PrimePower.card_def q).symm) σ Nat.prime_three hσ
  have hv : (TauCeti.LieTypeIndex.E6 q₀).Valid := TauCeti.LieTypeIndex.valid_E6 q₀
  obtain ⟨e₂⟩ := catEquiv_adjointGroup_of_card CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q₀
    hv (fixSubfield σ) hq₀card.symm
  have hJC : fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K :=
    fixedFieldImage_le.trans inf_le_left
  refine le_closure_fixed_of_kfact hS
    (((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv (τ := Tag.E6) σ).symm).trans
      e₂.symm) Nat.prime_three (by norm_num) ?_
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q₀)) hA hAc
    (fun a ha k hk => map_fixedFieldImage_subgroupOf_le (Or.inr (Or.inr (Or.inl rfl))) σ
      (hAσ a ha) (Subgroup.mem_map_of_mem _ hk))
    (fun a ha hfix => eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σ) hk2 (hAD ha)
      fun x hx => hfix x (Subgroup.mem_subgroupOf.2 hx))
  show 3 ≠ (TauCeti.LieTypeIndex.E6 q₀).characteristic
  rw [TauCeti.LieTypeIndex.characteristic_E6, hq₀p]
  exact fun h => hK3 h.symm

theorem e6FieldCubes_of_kfact (hS : AGLEmbeddingD2.KFactSeitzRankTwo) :
    E6ThreeDefs.E6FieldCubes := by
  intro K _ _ hK3 hK8 E hE hEc hED
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hDn := e6Inndiag_normal K
  have hAc := card_inf_e6Inndiag hE hEc hED
  have hA : E ⊓ e6Inndiag K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAc
    norm_num at hAc
  refine seitzHyperGamma_eq_top_of_overgroups Nat.prime_three hE hEc hED hA ?_
  intro x hxE hxD
  obtain ⟨σ, hσ, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) (hE.2 x hxE) hxD
  have hk2 : Nat.card (fixSubfield σ) ≠ 2 := by
    intro h
    have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hσ, h] at hcard
    exact hK8 hcard
  have hk2' : 2 < Nat.card (fixSubfield σ) := by
    have : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
    omega
  have hgen := fixedFieldImage_le_closure_of_plane hS hK3 σ hσ hk2'
    ((hE.mono (inf_le_left : E ⊓ e6Inndiag K ≤ E)).map (MulAut.conj ψ).toMonoidHom)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hAc])
    (by
      rintro _ ⟨b, hb, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hDn.conj_mem b hb.2 ψ)
    (by
      rintro _ ⟨b, hb, rfl⟩
      have hbx : Commute b x := congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hb.1⟩ ⟨x, hxE⟩)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hψ]
      exact hbx.conj ψ)
  exact exists_overgroupData_of_conj hψ (fixedFieldImage_subgroupOf_le_subfieldGroup Tag.E6 σ)
    hgen (fun a ha hfix => eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σ) hk2' ha
      fun y hy => hfix y (Subgroup.mem_subgroupOf.2 hy))
    (le_subfieldGroup_or_eq_top_of_fixedFieldImage_le (Or.inl rfl) σ Nat.prime_three
      (by norm_num) hσ hk2)

end E6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
