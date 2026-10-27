module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.IsoPlaneBasic
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6HighIsoPlane
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwistedE6Corner
public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6TwoDiag

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution CFSG.RankThree.PartOne.TCX.Tri
  CFSG.HardMathSupport.Lang.Coordinator CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

set_option linter.unusedSectionVars true

section Index


theorem card_twistedE6Diag_map_le_gcd {q : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) :
    Nat.card ((twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ))) ≤
      Nat.gcd 3 (q + 1) := by
  classical
  have hσ2 : ∀ c, σ.toRingHom c = c ^ q := fun c => hσ c
  set S : Subgroup (Fin TwistTag.E6.tag.rank → Kˣ) :=
    compatSubgroup (t := TwistTag.E6) σ.toRingHom with hS
  have hker : Nat.card ↥(S ⊓ (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) =
      Nat.gcd 3 (q + 1) := by
    rw [hS]
    exact card_compat_inf_ker_E6_of_card (σ := σ.toRingHom) hK hσ2
  have hZS : ∀ c ∈ S, zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c ∈ S := fun c hc =>
    zpowMatrix_cartan_mem_compatSubgroup hc
  let ζ0 : (∀ a : Fin TwistTag.E6.foldedTag.rank, (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      (Fin TwistTag.E6.tag.rank → Kˣ) :=
    MonoidHom.mk' (compatDiag TwistTag.E6 σ.toRingHom) fun u v => compatDiag_mul u v
  have hζ0 : ∀ u, ζ0 u ∈ S := fun u =>
    (mem_compatSubgroup σ.toRingHom).2 fun i => compatDiag_perm u i
  let ζS : (∀ a : Fin TwistTag.E6.foldedTag.rank,
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →* S :=
    ζ0.codRestrict S hζ0
  let ZS : S →* S :=
    ((zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).comp S.subtype).codRestrict S
      fun c => hZS c.1 c.2
  let R : Subgroup S := ZS.range
  let Ω : (∀ a : Fin TwistTag.E6.foldedTag.rank, (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      S ⧸ R :=
    (QuotientGroup.mk' R).comp ζS
  let π : MulAut (twistedE6RootGroup K σ) →* MulAut (twistedE6RootGroup K σ) ⧸
      twistedE6Inn K σ := QuotientGroup.mk' (twistedE6Inn K σ)
  let Λ := compatDiagAutHom TwistTag.E6 K σ.toRingHom
  have hΩ : Ω.ker ≤ (π.comp Λ).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 : ζS u ∈ R := (QuotientGroup.eq_one_iff (ζS u)).1 hu
    obtain ⟨s, hs⟩ := h1
    have hc : compatDiag TwistTag.E6 σ.toRingHom u =
        zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan s.1 := by
      have := congrArg Subtype.val hs
      exact this.symm
    have hmem :=
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.compatDiagAutHom_mem_inner_of_zpowMatrix
        σ s.1 s.2 u hc
    exact (QuotientGroup.eq_one_iff _).2 hmem
  have hidx : (π.comp Λ).ker.index ≤ Ω.ker.index := Subgroup.index_antitone hΩ
  have h2 : Ω.ker.index = Nat.card Ω.range := Subgroup.index_ker Ω
  have h3 : Nat.card Ω.range ≤ Nat.card (S ⧸ R) := Subgroup.card_le_card_group Ω.range
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h5 : R.index = Nat.card ↥ZS.ker := by
    have e1 := Subgroup.card_mul_index ZS.ker
    have e2 := Subgroup.card_mul_index R
    have e3 : ZS.ker.index = Nat.card R := Subgroup.index_ker ZS
    rw [e3] at e1
    apply Nat.eq_of_mul_eq_mul_left hRpos
    calc Nat.card R * R.index = Nat.card S := e2
      _ = Nat.card ↥ZS.ker * Nat.card R := e1.symm
      _ = Nat.card R * Nat.card ↥ZS.ker := mul_comm _ _
  have h6 : Nat.card ↥ZS.ker = Nat.gcd 3 (q + 1) := by
    have hmap : ZS.ker.map S.subtype = S ⊓ (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        have h1 : ZS s = 1 := hs
        have h2 : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan
            (s : Fin TwistTag.E6.tag.rank → Kˣ) = 1 := congrArg Subtype.val h1
        exact ⟨s.2, MonoidHom.mem_ker.2 h2⟩
      · rintro ⟨hxS, hx⟩
        have hx' : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan x = 1 := MonoidHom.mem_ker.1 hx
        exact ⟨⟨x, hxS⟩, MonoidHom.mem_ker.2 (Subtype.ext hx'), rfl⟩
    rw [← Subgroup.card_map_of_injective S.subtype_injective, hmap, hker]
  have hmapR : (twistedE6Diag K σ).map π = (π.comp Λ).range :=
    (MonoidHom.range_comp π Λ).symm
  rw [hmapR, ← Subgroup.index_ker (π.comp Λ)]
  calc (π.comp Λ).ker.index ≤ Ω.ker.index := hidx
    _ = Nat.card Ω.range := h2
    _ ≤ Nat.card (S ⧸ R) := h3
    _ = R.index := rfl
    _ = Nat.card ↥ZS.ker := h5
    _ = Nat.gcd 3 (q + 1) := h6


theorem card_le_gcd_mul_card_inf_twistedE6Inn {q : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    {D : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hDd : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Nat.card D ≤ Nat.gcd 3 (q + 1) * Nat.card ↥(D ⊓ twistedE6Inn K σ) := by
  classical
  set N := twistedE6Inn K σ with hN
  have : N.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (twistedE6RootGroup K σ)
  set π := QuotientGroup.mk' N with hπ
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (twistedE6RootGroup K σ)) := inferInstance
  have himg : D.map π ≤ (twistedE6Diag K σ).map π := by
    rintro _ ⟨d, hd, rfl⟩
    have hdd : d ∈ ((N ⊔ twistedE6Diag K σ : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, hr, rfl⟩ := hdd
    refine ⟨r, hr, ?_⟩
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    change π r = π (i * r)
    rw [map_mul, hpi, one_mul]
  have hle : Nat.card (D.map π) ≤ Nat.gcd 3 (q + 1) :=
    (Subgroup.card_le_of_le himg).trans (card_twistedE6Diag_map_le_gcd K hK σ hσ)
  set φ : ↥D →* _ := π.comp D.subtype with hφ
  have hkerφ : φ.ker = N.subgroupOf D := by
    rw [hφ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rfl
  have hcardker : Nat.card φ.ker = Nat.card ↥(D ⊓ N) := by
    rw [hkerφ, ← Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Nat.card φ.range = Nat.card (D.map π) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hmul : Nat.card φ.ker * Nat.card φ.range = Nat.card D := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcardker, hrange] at hmul
  rw [← hmul, mul_comm]
  exact Nat.mul_le_mul_right _ hle

end Index

section Iso

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule


theorem twIsoLift_of_abelian_preimage {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ))
    (hab : ∀ x y : ↥(e6Data_valid.minGroup K),
      (e6Isogeny K x : ModGL Tag.E6 K) ∈ E₀.map (twistedE6RootGroup K σ).subtype →
      (e6Isogeny K y : ModGL Tag.E6 K) ∈ E₀.map (twistedE6RootGroup K σ).subtype →
      x * y = y * x) :
    TwIsoLift K σ E₀ := by
  classical
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  set S : Subgroup ↥(e6Data_valid.minGroup K) :=
    (E₀.map (twistedE6RootGroup K σ).subtype).comap
      ((adjointGroup Tag.E6 K).subtype.comp (e6Isogeny K)) with hS
  refine ⟨K, inferInstance, inferInstance, ι, S, fun x hx y hy => hab x y hx hy, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxad : (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2)
  obtain ⟨s, hs⟩ := e6Isogeny_surjective K ⟨_, hxad⟩
  have hs' : ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (x : ModGL TwistTag.E6.tag K) := by rw [hs]
  refine ⟨s, ?_, ?_⟩
  · show ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      E₀.map (twistedE6RootGroup K σ).subtype
    rw [hs']
    exact ⟨x, hx, rfl⟩
  · show baseChangeGL ι ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = _
    rw [hs']
    rfl

theorem conj_injective_twistedE6RootGroup {K : Type} [Field K] (σ : K ≃+* K) :
    Function.Injective (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)) :=
  conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)

theorem exists_isotropic_inner_plane_twE6 {q : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) (hq : 3 ∣ q + 1)
    {Ē : Subgroup (MulAut (twistedE6RootGroup K σ))} (hĒ : IsElemAbelian 3 Ē)
    (hcard : 3 ^ 4 ≤ Nat.card Ē) (hdiag : Ē ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ E₀ : Subgroup (twistedE6RootGroup K σ),
      E₀.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) ≤ Ē ∧
      (∀ x ∈ E₀, x ^ 3 = 1) ∧ Nat.card E₀ = 3 ^ 2 ∧ TwIsoLift K σ E₀ := by
  classical
  have hinj := conj_injective_twistedE6RootGroup σ
  have hgcd : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left hq
  have hrange : twistedE6Inn K σ =
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range := rfl
  have hI : 3 ^ 3 ≤ Nat.card ↥(Ē ⊓ twistedE6Inn K σ) := by
    have h := card_le_gcd_mul_card_inf_twistedE6Inn K hK σ hσ hdiag
    rw [hgcd] at h
    have h4 : (3 : ℕ) ^ 4 = 3 * 3 ^ 3 := by norm_num
    rw [h4] at hcard
    exact Nat.le_of_mul_le_mul_left (hcard.trans h) (by norm_num)
  have hĒI : IsElemAbelian 3 (Ē ⊓ twistedE6Inn K σ) := hĒ.mono inf_le_left
  obtain ⟨D, hDle, hD27⟩ := exists_le_card_eq_pow_of_isElemAbelian Nat.prime_three hĒI hI
  have hDel : IsElemAbelian 3 D := hĒI.mono hDle
  have hG : (twistedE6RootGroup K σ).map (baseChangeGL (RingHom.id K)) ≤ adjointGroup Tag.E6 K := by
    rw [map_baseChangeGL_id]
    intro x hx
    exact twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hx)
  obtain ⟨E, hED, hE9, habE⟩ := exists_isotropic_plane_of_lift
    (G := twistedE6RootGroup K σ) (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)) hinj (RingHom.id K) hG
    (fun d hd => (hrange ▸ (hDle hd).2)) hDel hD27
  obtain ⟨E₉, hE₉E, hE₉card⟩ :=
    exists_le_card_eq_pow_of_isElemAbelian Nat.prime_three (hDel.mono hED) hE9
  have hE₉D : E₉ ≤ D := hE₉E.trans hED
  have hE₉in : E₉ ≤ (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)).range := fun x hx => (hDle (hE₉D hx)).2
  set E₀ : Subgroup (twistedE6RootGroup K σ) := E₉.comap
    (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) with hE₀
  have hmap : E₀.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)) = E₉ := Subgroup.map_comap_eq_self hE₉in
  have hE₉el : IsElemAbelian 3 E₉ := (hDel.mono hED).mono hE₉E
  refine ⟨E₀, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact hE₉D.trans (hDle.trans inf_le_left)
  · intro x hx
    have h1 : (MulAut.conj x) ∈ E₉ := hx
    apply hinj
    rw [map_pow, map_one]
    exact hE₉el.2 _ h1
  · rw [← Subgroup.card_map_of_injective hinj (K := E₀), hmap, hE₉card]
  · refine twIsoLift_of_abelian_preimage σ E₀ fun x y hx hy => ?_
    have key : ∀ z : ↥(e6Data_valid.minGroup K),
        (e6Isogeny K z : ModGL Tag.E6 K) ∈ E₀.map (twistedE6RootGroup K σ).subtype →
        (e6Isogeny K z : ModGL Tag.E6 K) ∈ ((E.comap (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
          MulAut ↥(twistedE6RootGroup K σ))).map (twistedE6RootGroup K σ).subtype).map
            (baseChangeGL (RingHom.id K)) := by
      intro z hz
      obtain ⟨g, hg, hgz⟩ := hz
      refine ⟨g, ⟨g, Subgroup.comap_mono hE₉E hg, rfl⟩, ?_⟩
      rw [baseChangeGL_id]
      exact hgz
    exact habE x y (key x hx) (key y hy)

end Iso

section Cat


theorem planeGen_twE6_of_isotropic_plane {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq : q.card % 3 = 2) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (q.p ^ q.exponent) ^ 2)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) (hKchar : CharP K q.p)
    (e : Cat ⟨.twistedE6 q, hv⟩ ≃* ↥(twistedE6RootGroup K σ))
    (E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hiso : TwIsoLift K σ (E₀.map e.toMonoidHom)) :
    PlaneGen (E₀.map (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →*
      MulAut (Cat ⟨.twistedE6 q, hv⟩))) := by
  classical
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →*
      MulAut (Cat ⟨.twistedE6 q, hv⟩)) :=
    conj_injective_of_mulEquiv e (conj_injective_twistedE6RootGroup σ)
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := three_ne_p_of_card_mod_three_eq_two hq
  have hqc : (q.p ^ q.exponent) % 3 = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hTw : IsTwistedE6Index (TauCeti.LieTypeIndex.twistedE6 q) := ⟨q, rfl⟩
  have hcomm : IsMulCommutative E₀ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hE₀el : IsElemAbelian 3 E₀ := ⟨hcomm, hexp⟩
  set E : Subgroup (MulAut (Cat ⟨.twistedE6 q, hv⟩)) :=
    E₀.map (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →* MulAut (Cat ⟨.twistedE6 q, hv⟩)) with hE
  have hEel : IsElemAbelian 3 E := hE₀el.map _
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hinj]
    exact hcard
  have hin : InnerPlane ⟨.twistedE6 q, hv⟩ 3 E := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  by_cases hN : NormalizesRSubgroup ⟨.twistedE6 q, hv⟩ E
  · have hpd : 3 ≠ (⟨.twistedE6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := fun h =>
      hq3 (h.trans (TauCeti.LieTypeIndex.characteristic_twistedE6 q))
    have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
        (⟨.twistedE6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
      rintro (⟨-, ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd' | hd'⟩ |
        hd'⟩ | ⟨h5, -⟩)
      all_goals first | nomatch hd' | omega
    exact seitzExcParabolic ⟨.twistedE6 q, hv⟩ 3 Nat.prime_three (by norm_num) hpd hex E hEel
      hEcard ⟨hin, hTw.not_classical, hN⟩
  · have hnN : ¬ NormalizesRIn (ringChar K) (E₀.map e.toMonoidHom) := by
      rintro ⟨R, hR1, hRp, hRn⟩
      refine hN (exists_normalized_of_native e ⟨R, hR1, ?_, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩)
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6, ← hring]
      exact hRp
    have hexp' : ∀ x ∈ E₀.map e.toMonoidHom, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
    have hcard' : Nat.card (E₀.map e.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective e.injective, hcard]
    exact planeGen_map_conj_of_planeCl e hinj
      (planeCl_twE6_of_isoLift σ hK hσ hqc _ hexp' hcard' hnN hiso)

theorem exists_planeGen_of_large_twE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq : q.card % 3 = 2)
    {Ē : Subgroup (MulAut (Cat ⟨.twistedE6 q, hv⟩))} (hĒ : IsElemAbelian 3 Ē)
    (hcard : 3 ^ 4 ≤ Nat.card Ē) :
    ∃ E : Subgroup (MulAut (Cat ⟨.twistedE6 q, hv⟩)), E ≤ Ē ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧ PlaneGen E := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fintype K := Fintype.ofFinite K
  have hKchar : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hq3 : 3 ≠ q.p := three_ne_p_of_card_mod_three_eq_two hq
  have hqc : (q.p ^ q.exponent) % 3 = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →*
      MulAut (Cat ⟨.twistedE6 q, hv⟩)) :=
    conj_injective_of_mulEquiv e (conj_injective_twistedE6RootGroup σ)
  set Ēn : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) := Ē.map (MulAut.congr e).toMonoidHom
    with hĒn
  have hĒnel : IsElemAbelian 3 Ēn := hĒ.map _
  have hcardn : Nat.card Ēn = Nat.card Ē :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  by_cases hdiag : Ēn ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  ·
    obtain ⟨E₀P, hle, hexpP, hcardP, hiso⟩ := exists_isotropic_inner_plane_twE6
      (q := q.p ^ q.exponent) K hK σ hσ (by omega) hĒnel (by rw [hcardn]; exact hcard) hdiag
    set E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩) := E₀P.comap e.toMonoidHom with hE₀
    have hmap : E₀.map e.toMonoidHom = E₀P :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective E₀P
    have hexp : ∀ x ∈ E₀, x ^ 3 = 1 := by
      intro x hx
      apply e.injective
      rw [map_pow, map_one]
      exact hexpP _ hx
    have hcard₀ : Nat.card E₀ = 3 ^ 2 := by
      rw [← hcardP, ← hmap, Subgroup.card_map_of_injective e.injective]
    have hcomm : IsMulCommutative E₀ := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard₀
    have hE₀el : IsElemAbelian 3 E₀ := ⟨hcomm, hexp⟩
    refine ⟨E₀.map (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →* MulAut (Cat ⟨.twistedE6 q, hv⟩)), ?_,
      hE₀el.map _, ?_,
      planeGen_twE6_of_isotropic_plane hv hq σ hK hσ hKchar e E₀ hexp hcard₀
        (by rw [hmap]; exact hiso)⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle ⟨e x, hx, rfl⟩
      have h1 : (MulAut.congr e).toMonoidHom (MulAut.conj x) = MulAut.conj (e x) :=
        mulAut_congr_conj e x
      have h2 : y = MulAut.conj x := (MulAut.congr e).injective (hyx.trans h1.symm)
      rwa [h2] at hy
    · rw [Subgroup.card_map_of_injective hinj, hcard₀]
  ·
    obtain ⟨En, hEnle, hEncard, hEnnot⟩ := exists_plane_not_le_of_isElemAbelian Nat.prime_three
      hĒnel (by
        rw [hcardn]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard) hdiag
    have hEnel : IsElemAbelian 3 En := hĒnel.mono hEnle
    haveI : CFSG.IsElementaryAbelian 3 En := hEnel.isElementaryAbelian
    have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    have hgen : Subgroup.closure (fixUnion En) = ⊤ :=
      ExcWideThree.twistedE6_fieldPlanes_three ExcWideThree.twistedE6KernelLemma_holds q.prime_p
        (fun h => hq3 h.symm) q.exponent_pos hK2 σ hσ En hEncard hEnnot
    exact exists_plane_of_map_congr e hEnle hEnel hEncard
      ((planeGen_iff_closure_fixUnion En).mpr hgen)

end Cat

end CFSG.LieType.SeitzGeneration.ExcHighThree
