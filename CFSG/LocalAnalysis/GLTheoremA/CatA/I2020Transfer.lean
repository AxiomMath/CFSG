module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XAct
public import CFSG.Holt.Induced
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.I155X
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {X Y : Type} [Group X] [Group Y]

theorem i2020FixCentAt_map [Finite X] [Finite Y] (e : X ≃* Y) {β : MulAut X}
    {J : Subgroup X} (h : I2020FixCentAt β J) :
    I2020FixCentAt (MulAut.congr e β) (J.map e.toMonoidHom) := by
  classical
  intro T' hT' S' hS' hfix' hnorm' hcomm'
  set T : Subgroup X := T'.map e.symm.toMonoidHom with hTdef
  set S : Subgroup (MulAut X) := S'.map (MulAut.congr e).symm.toMonoidHom with hSdef
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp
  have hT : fusionIsSylowIn 2 T J := by
    have h1 := CFSG.Holt.fusionIsSylowIn_map (p := 2) e.symm.toMonoidHom hT'
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
    exact h1
  have hS2 : IsPGroup 2 S := hS'.map _
  have hfix : ∀ s ∈ S, ∀ t ∈ T, s t = t := by
    intro s hs t ht
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    have h1 : ((MulAut.congr e).symm s') (e.symm t') = e.symm (s' t') := by
      rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply]
    show ((MulAut.congr e).symm s') (e.symm t') = e.symm t'
    rw [h1, hfix' s' hs' t' ht']
  have hnorm : ∀ s ∈ S, β * s * β⁻¹ ∈ S := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    have hβ : (MulAut.congr e).symm (MulAut.congr e β) = β := MulEquiv.symm_apply_apply _ _
    refine Subgroup.mem_map.2 ⟨(MulAut.congr e β) * s' * (MulAut.congr e β)⁻¹,
      hnorm' s' hs', ?_⟩
    simp only [map_mul, map_inv]
    change (MulAut.congr e).symm (MulAut.congr e β) *
        (MulAut.congr e).symm s' * ((MulAut.congr e).symm (MulAut.congr e β))⁻¹ =
      β * (MulAut.congr e).symm s' * β⁻¹
    rw [hβ]
  have hcomm : ⁅S, Subgroup.zpowers β⁆ = S := by
    have hβ : (MulAut.congr e).symm (MulAut.congr e β) = β := MulEquiv.symm_apply_apply _ _
    have hz : (Subgroup.zpowers (MulAut.congr e β)).map
        (MulAut.congr e).symm.toMonoidHom = Subgroup.zpowers β := by
      rw [MonoidHom.map_zpowers,
        show (MulAut.congr e).symm.toMonoidHom ((MulAut.congr e) β) = β from hβ]
    have hS : S = S'.map (MulAut.congr e).symm.toMonoidHom := rfl
    calc ⁅S, Subgroup.zpowers β⁆
        = ⁅S'.map (MulAut.congr e).symm.toMonoidHom,
            (Subgroup.zpowers (MulAut.congr e β)).map (MulAut.congr e).symm.toMonoidHom⁆ := by
          rw [hS, ← hz]
      _ = (⁅S', Subgroup.zpowers (MulAut.congr e β)⁆).map
            (MulAut.congr e).symm.toMonoidHom := (Subgroup.map_commutator _ _ _).symm
      _ = S'.map (MulAut.congr e).symm.toMonoidHom := by rw [hcomm']
      _ = S := rfl
  have hmain := h T hT S hS2 hfix hnorm hcomm
  intro s' hs' j' hj'
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hj'
  have hsj := hmain ((MulAut.congr e).symm s') (Subgroup.mem_map.2 ⟨s', hs', rfl⟩) j hj
  have hcongr := congrArg e hsj
  simpa [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply] using hcongr

theorem i2020FixCentAt_congr [Finite X] [Finite Y] (e : X ≃* Y) (β : MulAut X)
    (J : Subgroup X) :
    I2020FixCentAt β J ↔ I2020FixCentAt (MulAut.congr e β) (J.map e.toMonoidHom) := by
  refine ⟨i2020FixCentAt_map e, fun h => ?_⟩
  have h' := i2020FixCentAt_map e.symm h
  have hcompX : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y :=
    MonoidHom.ext fun x => by simp
  have hβ : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext x
    simp [MulAut.congr_apply, MulAut.congr_symm_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  rw [Subgroup.map_map, hcompX, Subgroup.map_id, hβ] at h'
  exact h'

private theorem ker_central_of_mulEquiv (e : X ≃* Y) (U : Subgroup X) :
    ∀ y ∈ U ⊓ e.toMonoidHom.ker, ∀ x ∈ U, x * y = y * x := by
  intro y hy x _
  have hy1 : y = 1 := e.injective (by
    rw [map_one]
    exact (Subgroup.mem_inf.1 hy).2)
  rw [hy1, mul_one, one_mul]

theorem i2020FixCent_congr [Finite X] [Finite Y] {p : ℕ} (hp : p.Prime) (e : X ≃* Y)
    (P : Subgroup X → Prop) (P' : Subgroup Y → Prop)
    (hP : ∀ J : Subgroup X, P' (J.map e.toMonoidHom) ↔ P J) (β : MulAut X) :
    I2020FixCent p P β ↔ I2020FixCent p P' (MulAut.congr e β) := by
  classical
  have hfixeq : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map e.toMonoidHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e β
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp
  have hcomp' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y :=
    MonoidHom.ext fun x => by simp
  constructor
  · intro h J' hJ' hP'J'
    have hJ : GLAPComponent p (fixSubgroup β) (J'.map e.symm.toMonoidHom) := by
      have h1 := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.symm.toMonoidHom
        (ker_central_of_mulEquiv e.symm (fixSubgroup (MulAut.congr e β)))).1 J' hJ'
      have hmapfix : (fixSubgroup (MulAut.congr e β)).map e.symm.toMonoidHom =
          fixSubgroup β := by
        rw [hfixeq, Subgroup.map_map, hcomp, Subgroup.map_id]
      rwa [hmapfix] at h1
    have hPJ : P (J'.map e.symm.toMonoidHom) := by
      refine (hP _).1 ?_
      rwa [Subgroup.map_map, hcomp', Subgroup.map_id]
    have hmap := i2020FixCentAt_map e (h _ hJ hPJ)
    rwa [Subgroup.map_map, hcomp', Subgroup.map_id] at hmap
  · intro h J hJ hPJ
    have hJ' : GLAPComponent p (fixSubgroup (MulAut.congr e β)) (J.map e.toMonoidHom) := by
      have h1 := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom
        (ker_central_of_mulEquiv e (fixSubgroup β))).1 J hJ
      rwa [← hfixeq] at h1
    have hPJ' : P' (J.map e.toMonoidHom) := (hP J).2 hPJ
    exact (i2020FixCentAt_congr e β J).2 (h _ hJ' hPJ')

theorem pSimpleIsLie_of_pQuotEquiv {p : ℕ} {J : Subgroup X} {J' : Subgroup Y}
    (hPS : PSimple p J ≃* PSimple p J') {d : TauCeti.LieTypeIndex} :
    pSimpleIsLie p J d ↔ pSimpleIsLie p J' d := by
  constructor
  · rintro ⟨i, hi, ⟨f⟩⟩
    exact ⟨i, hi, ⟨hPS.symm.trans f⟩⟩
  · rintro ⟨i, hi, ⟨f⟩⟩
    exact ⟨i, hi, ⟨hPS.trans f⟩⟩

theorem center_pQuot_ne_bot_of_pQuotEquiv {p : ℕ} {J : Subgroup X} {J' : Subgroup Y}
    (hQ : PQuot p J ≃* PQuot p J') :
    Subgroup.center (PQuot p J) ≠ ⊥ ↔ Subgroup.center (PQuot p J') ≠ ⊥ := by
  have hmap : Subgroup.center (PQuot p J') =
      (Subgroup.center (PQuot p J)).map hQ.toMonoidHom :=
    (Subgroup.map_center_eq hQ).symm
  rw [hmap]
  exact ((Subgroup.map_eq_bot_iff_of_injective _ hQ.injective).ne).symm

theorem jType_of_pQuotEquiv {p q : ℕ} {J : Subgroup X} {J' : Subgroup Y}
    (hQ : PQuot p J ≃* PQuot p J') : JType p q J ↔ JType p q J' := by
  have hPS : PSimple p J ≃* PSimple p J' :=
    QuotientGroup.congr _ _ hQ (Subgroup.map_center_eq hQ)
  have hlie : ∀ d : TauCeti.LieTypeIndex, pSimpleIsLie p J d ↔ pSimpleIsLie p J' d :=
    fun d => pSimpleIsLie_of_pQuotEquiv hPS
  have hcenter := center_pQuot_ne_bot_of_pQuotEquiv hQ
  unfold JType IsSL3Type IsOmegaType
  constructor
  · rintro (⟨Q, hQp, hd, hc⟩ | ⟨Q, hQp, hd⟩)
    · rcases hd with hd | hd
      · exact Or.inl ⟨Q, hQp, Or.inl ((hlie _).1 hd), fun h3 => hcenter.1 (hc h3)⟩
      · exact Or.inl ⟨Q, hQp, Or.inr ((hlie _).1 hd), fun h3 => hcenter.1 (hc h3)⟩
    · refine Or.inr ⟨Q, hQp, ?_⟩
      rcases hd with hd | hd | hd
      · exact Or.inl ((hlie _).1 hd)
      · exact Or.inr (Or.inl ((hlie _).1 hd))
      · exact Or.inr (Or.inr ((hlie _).1 hd))
  · rintro (⟨Q, hQp, hd, hc⟩ | ⟨Q, hQp, hd⟩)
    · rcases hd with hd | hd
      · exact Or.inl ⟨Q, hQp, Or.inl ((hlie _).2 hd), fun h3 => hcenter.2 (hc h3)⟩
      · exact Or.inl ⟨Q, hQp, Or.inr ((hlie _).2 hd), fun h3 => hcenter.2 (hc h3)⟩
    · refine Or.inr ⟨Q, hQp, ?_⟩
      rcases hd with hd | hd | hd
      · exact Or.inl ((hlie _).2 hd)
      · exact Or.inr (Or.inl ((hlie _).2 hd))
      · exact Or.inr (Or.inr ((hlie _).2 hd))

theorem jType_map_mulEquiv [Finite X] [Finite Y] {p q : ℕ} (hp : p.Prime) (e : X ≃* Y)
    {J : Subgroup X} : JType p q J ↔ JType p q (J.map e.toMonoidHom) := by
  have hker : ¬ p ∣ Nat.card e.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective, Subgroup.card_bot]
    exact hp.not_dvd_one
  obtain ⟨hQ⟩ := nonempty_pQuot_equiv_map hp (ψ := e.toMonoidHom) hker J
  exact jType_of_pQuotEquiv hQ

section ChevTransfer

variable {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)

theorem ker_chevQuotHom_eq_glaPPrimeCore {K : Subgroup G}
    (hZ : Subgroup.center (PQuot p K) = ⊥) :
    (chevQuotHom p K).ker = GLAPPrimeCore p ↥K := by
  rw [chevQuotHom, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ, MonoidHom.comap_bot,
    ker_pQuotHom]

theorem not_dvd_card_ker_chevQuotHom (hp : p.Prime) {K : Subgroup G}
    (hZ : Subgroup.center (PQuot p K) = ⊥) :
    ¬ p ∣ Nat.card (chevQuotHom p K).ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [ker_chevQuotHom_eq_glaPPrimeCore hZ]
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card

theorem nonempty_pQuot_equiv_chevTransfer (hp : p.Prime) {K J : Subgroup G}
    (hZ : Subgroup.center (PQuot p K) = ⊥) (hJK : J ≤ K) :
    Nonempty (PQuot p J ≃* PQuot p (chevTransfer p K J)) := by
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_subgroupOf p hJK
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_map hp (ψ := chevQuotHom p K)
    (not_dvd_card_ker_chevQuotHom hp hZ) (J.subgroupOf K)
  exact ⟨e₁.symm.trans e₂⟩

theorem jType_chevTransfer (hp : p.Prime) {q : ℕ} {K J : Subgroup G}
    (hZ : Subgroup.center (PQuot p K) = ⊥) (hJK : J ≤ K) (h : JType p q J) :
    JType p q (chevTransfer p K J) := by
  obtain ⟨e⟩ := nonempty_pQuot_equiv_chevTransfer (G := G) hp hZ hJK
  exact (jType_of_pQuotEquiv e).1 h

end ChevTransfer

section GStep

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem chevQuotHom_eq_one_iff_centMod (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) {g : G} (hg : g ∈ K) :
    chevQuotHom p K ⟨g, hg⟩ = 1 ↔ CentMod p K g := by
  have hN := Subgroup.le_normalizer hg
  have hconj : chevQuotHom p K ⟨g, hg⟩ = 1 ↔
      MulAut.conj (chevQuotHom p K ⟨g, hg⟩) = 1 := by
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact conj_injective hp hK (by rw [h, map_one])
  rw [hconj, ← act_of_mem_K hg, act_of_mem hN, chevAut_eq_one_iff hp hK hN]

theorem chevQuotHom_normalizerMonoidHom {K : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    chevQuotHom p K (K.normalizerMonoidHom ⟨s, hs⟩ k) = act p K s (chevQuotHom p K k) := by
  rw [act_of_mem hs, chevAut_chevQuotHom]

theorem act_fixes_chevQuotHom_of_commutator (hp : p.Prime) {X K T S : Subgroup G}
    (hK : GLAPComponent p X K) (hTK : T ≤ K)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hTS : ⁅T, S⁆ ≤ centModSubgroup p K) {s t : G} (hs : s ∈ S) (ht : t ∈ T) :
    act p K s (chevQuotHom p K ⟨t, hTK ht⟩) = chevQuotHom p K ⟨t, hTK ht⟩ := by
  have hcommK : ⁅t, s⁆ ∈ K := by
    have h1 : s * t⁻¹ * s⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hSK hs) t⁻¹).1 (K.inv_mem (hTK ht))
    have h2 : t * (s * t⁻¹ * s⁻¹) ∈ K := K.mul_mem (hTK ht) h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hc : ⁅t, s⁆ ∈ centModSubgroup p K :=
    hTS (Subgroup.commutator_mem_commutator ht hs)
  have h1 : chevQuotHom p K ⟨⁅t, s⁆, hcommK⟩ = 1 :=
    (chevQuotHom_eq_one_iff_centMod hp hK hcommK).2 (centMod_iff.2 hc)
  have hnorm_eq : K.normalizerMonoidHom ⟨s, hSK hs⟩ ⟨t, hTK ht⟩ =
      ⟨s * t * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSK hs) t).1 (hTK ht)⟩ :=
    Subtype.ext rfl
  have hsplit : (⟨⁅t, s⁆, hcommK⟩ : ↥K) =
      ⟨t, hTK ht⟩ * (K.normalizerMonoidHom ⟨s, hSK hs⟩ ⟨t, hTK ht⟩)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hnorm_eq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hA : chevQuotHom p K (K.normalizerMonoidHom ⟨s, hSK hs⟩ ⟨t, hTK ht⟩) =
      act p K s (chevQuotHom p K ⟨t, hTK ht⟩) :=
    chevQuotHom_normalizerMonoidHom (p := p) (hSK hs) ⟨t, hTK ht⟩
  have h2 : chevQuotHom p K ⟨t, hTK ht⟩ *
      (act p K s (chevQuotHom p K ⟨t, hTK ht⟩))⁻¹ = 1 := by
    rw [← hA, ← map_inv, ← map_mul, ← hsplit]
    exact h1
  exact (mul_inv_eq_one.1 h2).symm

theorem fusionIsSylowIn_chevTransfer {K J T : Subgroup G}
    (hT : fusionIsSylowIn 2 T J) (hJK : J ≤ K) :
    fusionIsSylowIn 2 (chevTransfer p K T) (chevTransfer p K J) := by
  obtain ⟨S, hSmap⟩ := CFSG.Holt.exists_sylow_map_eq_of_fusionIsSylowIn hT
  have hTJ : T ≤ J := hT.1
  have hS : (S : Subgroup ↥J) = T.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [hSmap, Subgroup.map_subgroupOf_eq_of_le hTJ]
  let ψ : ↥J →* ↥K :=
    (J.subgroupOf K).subtype.comp (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom
  let φ : ↥J →* PSimple p K := (chevQuotHom p K).comp ψ
  have htop : fusionIsSylowIn 2 (S : Subgroup ↥J) ⊤ :=
    CFSG.Holt.exists_sylow_eq_iff_fusionIsSylowIn_top.1 ⟨S, rfl⟩
  have hmapT : (T.subgroupOf J).map φ = chevTransfer p K T := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hJK j.2⟩, hj, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨(k : G), hTJ (Subgroup.mem_subgroupOf.1 hk)⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hk), ?_⟩
      show chevQuotHom p K (ψ ⟨(k : G), _⟩) = chevQuotHom p K k
      exact congrArg (chevQuotHom p K) (Subtype.ext rfl)
  have hmapJ : (⊤ : Subgroup ↥J).map φ = chevTransfer p K J := by
    ext x
    constructor
    · rintro ⟨j, -, rfl⟩
      exact ⟨⟨j, hJK j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, trivial, ?_⟩
      show chevQuotHom p K (ψ ⟨(k : G), _⟩) = chevQuotHom p K k
      exact congrArg (chevQuotHom p K) (Subtype.ext rfl)
  have hres := CFSG.Holt.fusionIsSylowIn_map (p := 2) φ htop
  rw [hS, hmapT, hmapJ] at hres
  exact hres

theorem mem_map_subgroupOf_chevAut {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {t : MulAut (PSimple p K)} :
    t ∈ (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K) ↔
      ∃ s ∈ S, act p K s = t := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s : G), Subgroup.mem_subgroupOf.1 hs, act_of_mem s.2⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hSK hs⟩, Subgroup.mem_subgroupOf.2 hs, (act_of_mem (hSK hs)).symm⟩

theorem map_subgroupOf_chevAut_eq_zpowers_act (hp : p.Prime) {X K D : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyD : y ∈ D)
    (hDN : D ≤ Subgroup.normalizer (K : Set G))
    (hDC : D ≤ Subgroup.zpowers y ⊔ centModSubgroup p K) :
    (D.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K) =
      Subgroup.zpowers (act p K y) := by
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hDN hyD
  have hyC : y ∈ Subgroup.normalizer (centModSubgroup p K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact S3.conj_mem_centModSubgroup hyN hc
    · intro hc
      have h1 := S3.conj_mem_centModSubgroup (Subgroup.inv_mem _ hyN) hc
      simpa [mul_assoc] using h1
  have hzC : Subgroup.zpowers y ≤ Subgroup.normalizer (centModSubgroup p K : Set G) :=
    Subgroup.zpowers_le.2 hyC
  have hCl : centModSubgroup p K ≤ Subgroup.normalizer (K : Set G) := fun c hc =>
    (mem_centModSubgroup.1 hc).1
  have hpow : ∀ k : ℤ, act p K (y ^ k) = (act p K y) ^ k := by
    intro k
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ k =
        ⟨y ^ k, Subgroup.zpow_mem _ hyN k⟩ := Subtype.ext (by simp)
    calc act p K (y ^ k) = chevAut p K ⟨y ^ k, Subgroup.zpow_mem _ hyN k⟩ :=
          act_of_mem (Subgroup.zpow_mem _ hyN k)
      _ = chevAut p K ((⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ k) := by rw [h1]
      _ = (chevAut p K ⟨y, hyN⟩) ^ k := map_zpow _ _ _
      _ = (act p K y) ^ k := by rw [act_of_mem hyN]
  apply le_antisymm
  · intro t ht
    obtain ⟨d, hd, rfl⟩ := (mem_map_subgroupOf_chevAut hDN).1 ht
    have hmem : d ∈ ((Subgroup.zpowers y ⊔ centModSubgroup p K : Subgroup G) : Set G) := hDC hd
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzC] at hmem
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := hCl hc
    have hc1 : act p K c = 1 :=
      (act_eq_one_iff hp hK hcN).2 (centMod_iff.2 hc)
    have hkey : act p K (y ^ k * c) = (act p K y) ^ k := by
      rw [act_mul (Subgroup.zpow_mem _ hyN k) hcN, hpow k, hc1, mul_one]
    rw [hkey]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  · intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    refine (mem_map_subgroupOf_chevAut hDN).2 ⟨y ^ k, Subgroup.zpow_mem _ hyD k, ?_⟩
    exact hpow k

private theorem actImage_normalized {p : ℕ} {K S D : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyD : y ∈ D)
    (hSD : D ≤ Subgroup.normalizer (S : Set G))
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {s : MulAut (PSimple p K)}
    (hs : s ∈ (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K)) :
    act p K y * s * (act p K y)⁻¹ ∈
      (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_map_subgroupOf_chevAut hSK).1 hs
  have hs₀N : s₀ ∈ N := hSK hs₀
  have hyN' : y ∈ N := hyN
  have hyinvN : y⁻¹ ∈ N := Subgroup.inv_mem _ hyN'
  have hysN : y * s₀ ∈ N := Subgroup.mul_mem _ hyN' hs₀N
  have hone : act p K (1 : G) = 1 := by
    rw [act_of_mem (N.one_mem)]
    exact map_one _
  have hyinv : act p K y⁻¹ = (act p K y)⁻¹ := by
    have h1 : act p K y * act p K y⁻¹ = 1 := by
      rw [← act_mul hyN' hyinvN, mul_inv_cancel, hone]
    exact eq_inv_of_mul_eq_one_right h1
  have hconjS : y * s₀ * y⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 (hSD hyD) s₀).1 hs₀
  refine (mem_map_subgroupOf_chevAut hSK).2 ⟨y * s₀ * y⁻¹, hconjS, ?_⟩
  calc act p K (y * s₀ * y⁻¹)
      = act p K (y * s₀) * act p K y⁻¹ := act_mul hysN hyinvN
    _ = (act p K y * act p K s₀) * (act p K y)⁻¹ := by rw [act_mul hyN' hs₀N, hyinv]

private theorem actImage_commutator (hp : p.Prime) {X K S D : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyD : y ∈ D)
    (hD : D ≤ Subgroup.normalizer (K : Set G))
    (hDC : D ≤ Subgroup.zpowers y ⊔ centModSubgroup p K)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hDS : ⁅S, D⁆ = S) :
    ⁅(S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K),
        Subgroup.zpowers (act p K y)⁆ =
      (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  have hDbar : (D.subgroupOf N).map (chevAut p K) = Subgroup.zpowers (act p K y) :=
    map_subgroupOf_chevAut_eq_zpowers_act hp hK hyD hD hDC
  have hcomm0 : ⁅S.subgroupOf N, D.subgroupOf N⁆ = S.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [CFSG.commutator_subgroupOf_map_eq N D S hD hSK, hDS,
      Subgroup.map_subgroupOf_eq_of_le hSK]
  calc ⁅(S.subgroupOf N).map (chevAut p K), Subgroup.zpowers (act p K y)⁆
      = ⁅(S.subgroupOf N).map (chevAut p K), (D.subgroupOf N).map (chevAut p K)⁆ := by
        rw [hDbar]
    _ = (⁅S.subgroupOf N, D.subgroupOf N⁆).map (chevAut p K) :=
        (Subgroup.map_commutator _ _ _).symm
    _ = (S.subgroupOf N).map (chevAut p K) := by rw [hcomm0]

theorem commutator_le_centMod_of_i2020FixCentAt (hp : p.Prime)
    {X K J T S D : Subgroup G} {y : G}
    (hK : GLAPComponent p X K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hT : fusionIsSylowIn 2 T J)
    (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hTS : ⁅T, S⁆ ≤ centModSubgroup p K)
    (hyD : y ∈ D)
    (hD : D ≤ Subgroup.normalizer (K : Set G))
    (hDC : D ≤ Subgroup.zpowers y ⊔ centModSubgroup p K)
    (hSD : D ≤ Subgroup.normalizer (S : Set G))
    (hDS : ⁅S, D⁆ = S)
    (hfix : I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J)) :
    ⁅J, S⁆ ≤ centModSubgroup p K := by
  classical
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  set C : Subgroup G := centModSubgroup p K with hC
  set β : MulAut (PSimple p K) := act p K y with hβdef
  have hβ : β = chevAut p K ⟨y, hyN⟩ := act_of_mem hyN
  have hfixβ : I2020FixCentAt β (chevTransfer p K J) := by rwa [hβ]
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hTK : T ≤ K := hT.1.trans hJK
  set Sbar : Subgroup (MulAut (PSimple p K)) := (S.subgroupOf N).map (chevAut p K) with hSbar
  set Tbar : Subgroup (PSimple p K) := chevTransfer p K T with hTbar
  have hSbar2 : IsPGroup 2 Sbar := by
    have h1 : IsPGroup 2 (S.subgroupOf N) :=
      hS.comap_of_injective N.subtype N.subtype_injective
    exact h1.map (chevAut p K)
  have hTbarSylow : fusionIsSylowIn 2 Tbar (chevTransfer p K J) :=
    fusionIsSylowIn_chevTransfer hT hJK
  have hfixT : ∀ s ∈ Sbar, ∀ t ∈ Tbar, s t = t := by
    intro s hs t ht
    obtain ⟨s₀, hs₀, rfl⟩ := (mem_map_subgroupOf_chevAut hSK).1 hs
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
    have htT : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 ht₀
    have h1 := act_fixes_chevQuotHom_of_commutator hp hK hTK hSK hTS hs₀ htT
    simpa using h1
  have hnorm : ∀ s ∈ Sbar, β * s * β⁻¹ ∈ Sbar := fun s hs =>
    actImage_normalized hyN hyD hSD hSK hs
  have hcomm : ⁅Sbar, Subgroup.zpowers β⁆ = Sbar :=
    actImage_commutator hp hK hyD hD hDC hSK hDS
  have hmain := hfixβ Tbar hTbarSylow Sbar hSbar2 hfixT hnorm hcomm
  rw [Subgroup.commutator_comm]
  refine Subgroup.commutator_le.2 fun s hs j hj => ?_
  have hsN : s ∈ N := hSK hs
  have hjK : j ∈ K := hJK hj
  have hsbar : act p K s ∈ Sbar := (mem_map_subgroupOf_chevAut hSK).2 ⟨s, hs, rfl⟩
  have hq : chevQuotHom p K ⟨j, hjK⟩ ∈ chevTransfer p K J :=
    ⟨⟨j, hjK⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  have hfixj : act p K s (chevQuotHom p K ⟨j, hjK⟩) = chevQuotHom p K ⟨j, hjK⟩ :=
    hmain _ hsbar _ hq
  have hsjs : s * j * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hsN j).1 hjK
  have hcommK : ⁅s, j⁆ ∈ K := by
    have h2 : (s * j * s⁻¹) * j⁻¹ ∈ K := K.mul_mem hsjs (K.inv_mem hjK)
    simpa [commutatorElement_def, mul_assoc] using h2
  have h1 : chevQuotHom p K ⟨⁅s, j⁆, hcommK⟩ = 1 := by
    have hsplit : (⟨⁅s, j⁆, hcommK⟩ : ↥K) =
        K.normalizerMonoidHom ⟨s, hsN⟩ ⟨j, hjK⟩ * ⟨j, hjK⟩⁻¹ := by
      apply Subtype.ext
      have hnorm_eq : (K.normalizerMonoidHom ⟨s, hsN⟩ ⟨j, hjK⟩ : ↥K) =
          ⟨s * j * s⁻¹, hsjs⟩ := Subtype.ext rfl
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hnorm_eq]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rw [hsplit, map_mul, map_inv, chevQuotHom_normalizerMonoidHom hsN ⟨j, hjK⟩, hfixj,
      mul_inv_cancel]
  exact centMod_iff.1 ((chevQuotHom_eq_one_iff_centMod hp hK hcommK).1 h1)

end GStep

theorem i2020FixCentAt_of_fixCent_map [Finite X] [Finite Y] {p : ℕ} (hp : p.Prime)
    (e : X ≃* Y) {β : MulAut X} {J : Subgroup X}
    (hJ : GLAPComponent p (fixSubgroup β) J)
    (h : I2020FixCent p (fun _ => True) (MulAut.congr e β)) : I2020FixCentAt β J := by
  have hfixeq : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map e.toMonoidHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e β
  have hcomp : GLAPComponent p (fixSubgroup (MulAut.congr e β)) (J.map e.toMonoidHom) := by
    have h1 := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom
      (ker_central_of_mulEquiv e (fixSubgroup β))).1 J hJ
    rwa [← hfixeq] at h1
  exact (i2020FixCentAt_congr e β J).2 (h _ hcomp trivial)

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
