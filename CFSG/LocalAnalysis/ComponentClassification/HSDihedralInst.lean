module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelPairB
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreMain
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralAssembly
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStanding
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralLocal
public import CFSG.Monster.B.TwoA.Base.ElemAut

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open CFSG.ComponentClassification.HarrisLit GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.HSFLit (HaradaInput)

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

@[expose] def rhoS (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : ↥S →* MulAut (Bar L) :=
  (rho h).comp (Subgroup.inclusion hS.le)

@[expose] def rhoSL (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : ↥(S ⊓ L) →* MulAut (Bar L) :=
  (rho h).comp (Subgroup.inclusion (inf_le_left.trans hS.le))

abbrev DbarS (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : Subgroup (MulAut (Bar L)) :=
  ((S ⊓ L).subgroupOf S).map (rhoS h hS)

theorem rhoSL_injective (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : Function.Injective (rhoSL h hS) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  exact Subtype.ext (eq_one_of_rho_eq_one h hS d.2 hd)

theorem range_rhoSL (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : (rhoSL h hS).range = DbarS h hS := by
  ext φ
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨⟨d, (mem_inf.mp d.2).1⟩, d.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

@[expose] def equivDbar (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : ↥(S ⊓ L) ≃* ↥(DbarS h hS) :=
  (MonoidHom.ofInjective (rhoSL_injective h hS)).trans (MulEquiv.subgroupCongr (range_rhoSL h hS))

theorem map_rho_L (h : Config t L p f) :
    (L.subgroupOf (centralizer ({t} : Set X))).map (rho h) = innAut (Bar L) := by
  ext φ
  constructor
  · rintro ⟨⟨x, hx⟩, hxL, rfl⟩
    exact ⟨QuotientGroup.mk ⟨x, hxL⟩, (rho_of_mem h ⟨x, hxL⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨l, h.le_centralizer l.2⟩, l.2, rho_of_mem h l⟩

theorem isSylowOf_DbarS (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    IsSylowOf 2 (DbarS h hS) (innAut (Bar L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set X)
  have hD : IsSylowOf 2 ((S ⊓ L).subgroupOf C) (L.subgroupOf C) := by
    rw [← isSylowOf_map_subtype_iff C, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left (inf_le_right.trans h.le_centralizer), inf_of_le_left h.le_centralizer]
    exact isSylowOf_inf_L h hS
  have hmap : DbarS h hS = ((S ⊓ L).subgroupOf C).map (rho h) := by
    ext φ
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hS.le s.2⟩, hs, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, (mem_inf.mp hc).1⟩, hc, rfl⟩
  rw [hmap, ← map_rho_L h]
  exact isSylowOf_map (rho h) hD

theorem exists_sylow_map (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {K : Type} [Field K] [Finite K]
    (e : Bar L ≃* PSL2 K) :
    ∃ T : Sylow 2 (PSL2 K), (DbarS h hS).map (autEquiv e).toMonoidHom =
      (T : Subgroup (PSL2 K)).map (incl K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (DbarS h hS).map (autEquiv e).toMonoidHom
  have hP : IsSylowOf 2 P (pGammaL2PSLRange K) := by
    rw [← map_autEquiv_innAut e]
    exact isSylowOf_map _ (isSylowOf_DbarS h hS)
  have hT₀ : (P.comap (incl K)).map (incl K) = P :=
    map_comap_eq_self (by rw [range_incl]; exact hP.le)
  have hcard : Nat.card (P.comap (incl K)) = 2 ^ (Nat.card (PSL2 K)).factorization 2 := by
    rw [← card_map_of_injective (incl_injective K), hT₀, hP.card_eq, ← range_incl,
      ← Nat.card_congr (MonoidHom.ofInjective (incl_injective K)).toEquiv]
  exact ⟨Sylow.ofCard _ hcard, by rw [Sylow.coe_ofCard, hT₀]⟩

theorem dihedral_D (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥(S ⊓ L) ≃* DihedralGroup n) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  obtain ⟨T, hT⟩ := exists_sylow_map h hS e
  obtain ⟨m, hm, ⟨eT⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K (h.isOddPrimePower hK) T
  refine ⟨2 ^ m, ?_, ⟨(equivDbar h hS).trans <|
    ((DbarS h hS).equivMapOfInjective _ (autEquiv e).injective).trans <|
      (MulEquiv.subgroupCongr hT).trans <|
        ((T : Subgroup (PSL2 K)).equivMapOfInjective _ (incl_injective K)).symm.trans eT⟩⟩
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem map_ker_rhoS (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    (rhoS h hS).ker.map S.subtype = S ⊓ coreActionKernel L := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mem_inf.mpr ⟨s.2, (mem_ker_rho h _).mp hs⟩
  · intro hx
    exact ⟨⟨x, (mem_inf.mp hx).1⟩, (mem_ker_rho h _).mpr (mem_inf.mp hx).2, rfl⟩

@[expose] def datum (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : LocalDatum X (MulAut (Bar L)) where
  t := t
  S := S
  D := S ⊓ L
  ψ := rhoS h hS
  orderOf_t := h.orderOf_eq
  sylow := hS
  D_le := inf_le_left
  conj_mem_D := fun _ hs _ hd => conj_mem_D h hS hs hd
  eq_one_of_mem_D := fun _ hd h1 => eq_one_of_rho_eq_one h hS hd h1
  t_mem_ker := fun _ => rho_t h
  t_not_mem_D := fun ht => h.not_mem (mem_inf.mp ht).2
  isCyclic_ker :=
    (((rhoS h hS).ker.equivMapOfInjective S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_ker_rhoS h hS))).isCyclic.mpr (isCyclic_inf_kernel h hS)
  dihedral := dihedral_D h hS

theorem autFacts_datum
    (h : Config t L p f) {S : Subgroup X} (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    AutFacts (datum h hS) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
  obtain ⟨T, hT⟩ := exists_sylow_map h hS e
  refine (datum h hS).autFacts_of_autPair (AutPair.of_map (autEquiv e) ?_)
  change AutPair ((rhoS h hS).range.map (autEquiv e).toMonoidHom)
    ((DbarS h hS).map (autEquiv e).toMonoidHom)
  have hP : IsPGroup 2 ((rhoS h hS).range.map (autEquiv e).toMonoidHom) :=
    (IsPGroup.of_surjective hS.isPGroup _ (rhoS h hS).rangeRestrict_surjective).map _
  have hTP : (T : Subgroup (PSL2 K)).map (incl K) ≤
      (rhoS h hS).range.map (autEquiv e).toMonoidHom := by
    rw [← hT]
    refine map_mono fun x hx => ?_
    obtain ⟨s, -, rfl⟩ := hx
    exact ⟨s, rfl⟩
  rw [hT]
  exact Model.autPair_model h.prime h.ne_two hK (h.isOddPrimePower hK) T hP hTP

theorem model_involution
    (h : Config t L p f) {S : Subgroup X} (hS : IsSylowOf 2 S (centralizer ({t} : Set X)))
    {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K)) (e : Bar L ≃* PSL2 K)
    {α : MulAut (Bar L)} (hα2 : α * α = 1) (hαD : ∀ d ∈ DbarS h hS, α * d = d * α)
    (hαn : α ∉ DbarS h hS) :
    orderOf (autEquiv e α) = 2 ∧ (autEquiv e α).right ≠ 1 := by
  obtain ⟨T, hT⟩ := exists_sylow_map h hS e
  have hgD : ∀ d ∈ (T : Subgroup (PSL2 K)).map (incl K),
      autEquiv e α * d = d * autEquiv e α := by
    rw [← hT]
    rintro _ ⟨d, hd, rfl⟩
    change autEquiv e α * autEquiv e d = autEquiv e d * autEquiv e α
    rw [← map_mul, ← map_mul, hαD d hd]
  have hgr : (autEquiv e α).right ≠ 1 := fun hr => hαn (by
    have := Model.mem_of_centralizes hodd T hr hgD
    rw [← hT] at this
    exact (AutPair.memΦ (autEquiv e)).mp this)
  refine ⟨orderOf_eq_prime (by rw [pow_two, ← map_mul, hα2, map_one]) fun h1 => hgr ?_, hgr⟩
  rw [h1]
  rfl

theorem coreAt_of_config
    (hH : HaradaInput) (hX : ¬ SectionalRankLeFour X) (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : CoreAt t L S := by
  set Δ := datum h hS
  obtain ⟨hQ, w, hwS, hw2, hwD, hwn⟩ := Δ.coreOut hH (autFacts_datum h hS) hX
  set α := Δ.ψe w
  have hαα : α * α = 1 := by
    rw [← pow_two, ← Δ.ψe_pow hwS 2, hw2, Δ.ψe_one]
  have hw1 : w ≠ 1 := fun h1 => hwn (by
    change Δ.ψe w ∈ DbarS h hS
    rw [h1, Δ.ψe_one]
    exact one_mem _)
  refine ⟨?_, ⟨w, hwS, orderOf_eq_prime hw2 hw1, ?_⟩, fun p' f' hp' hp2' hm => ?_⟩
  · rw [← map_ker_rhoS h hS]
    exact hQ
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_psl2
    have hodd := h.isOddPrimePower hK
    obtain ⟨hord, hr⟩ := model_involution h hS hodd e hαα hwD hwn
    obtain ⟨b, σ, hσ, hgb⟩ := isFieldInvModel_of_involution hodd hord hr
    obtain ⟨e₁, he₁⟩ := field_of_conj_inr e α b σ hgb
    have hwN : w ∈ normalizer (L : Set X) := le_normalizer h (hS.le hwS)
    refine ⟨(barAction L ⟨w, hwN⟩)⁻¹, (isInducedAut_iff L w hwN _).mpr rfl, ?_⟩
    have hb : barAction L ⟨w, hwN⟩ = α := by
      rw [show α = Δ.ψe w from rfl, Δ.ψe_of_mem hwS]
      rfl
    rw [hb, inv_eq_of_mul_eq_one_right hαα]
    exact ⟨K, inferInstance, inferInstance, e₁, σ, hσ, he₁⟩
  · obtain ⟨-, hf', -, -, K, _, _, hK, ⟨e⟩⟩ := lieModel_psl2_data hm
    obtain ⟨hord, hr⟩ := model_involution h hS (isOddPrimePower_of hp' hp2' hf' hK) e hαα hwD hwn
    have h2 : (autEquiv e α).right ^ 2 = 1 := by
      rw [← right_pow, orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hord)]
      rfl
    exact Model.even_of_orderOf_two hp' hK (orderOf_eq_prime h2 hr)

end CFSG.ComponentClassification.HSDihedral
