module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step7b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Q81

theorem isOfType_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {F : (Y : Type) → [Group Y] → Prop} (e : A ≃* B) (h : IsOfType F A) : IsOfType F B := by
  obtain ⟨h2, Y, _, hY, ⟨eY⟩⟩ := h
  have hk1 : ¬ 2 ∣ Nat.card e.symm.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective, card_bot]
    norm_num
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.symm.toMonoidHom
    e.symm.surjective hk1
  exact ⟨isTwoQuasisimple_of_mulEquiv e h2, Y, inferInstance, hY, ⟨eZ.trans eY⟩⟩

theorem orderOf_mk_of_two {m b : X} (hbm : b ∈ centralizer ({m} : Set X)) (hb : orderOf b = 2) :
    orderOf (QuotientGroup.mk ⟨b, hbm⟩ : MBar m) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : (⟨b, hbm⟩ : ↥(centralizer ({m} : Set X))) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, ← hb, pow_orderOf_eq_one]; rfl)
  refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]) ?_
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [Subgroup.orderOf_mk, hb] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem exists_lift_isTwoComponentIn {β y : X} (hyβ : y ∈ centralizer ({β} : Set X))
    (hy : orderOf y = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)})
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)}))) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {β} ⊓ centralizer {y}) ∧
      ∃ g : ↥J →* ↥Y, Function.Surjective g ∧ ¬ 2 ∣ Nat.card g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let y' : ↥M := ⟨y, hyβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({y'} : Set ↥M)
  have hy'2 : y' * y' = 1 := Subtype.ext (by
    change y * y = 1
    rw [← sq, ← hy, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} :=
    map_centralizer_eq hodd hy'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    rw [← hCmap] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨-, hlift, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  obtain ⟨hĴ, hĴmap⟩ := hlift _ hY
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {y} := by
    rw [map_subtype_centralizer hyβ, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {y}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  generalize hĴdef : closure {x : ↥C | x ∈ (Y.subgroupOf (centralizer
    {(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)})).comap φ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} = Ĵ
    at hĴ hĴmap
  have hJle : (Ĵ.map C.subtype).map M.subtype ≤ centralizer {β} ⊓ centralizer {y} := by
    rw [← hCX]
    exact map_mono (map_subtype_le Ĵ)
  have hJeq : ((Ĵ.map C.subtype).map M.subtype).subgroupOf (centralizer {β} ⊓ centralizer {y}) =
      Ĵ.map eC.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, hux⟩
      exact ⟨u, hu, Subtype.ext hux⟩
    · rintro ⟨u, hu, hux⟩
      have h1 : ((eC u : ↥(centralizer ({β} : Set X) ⊓ centralizer {y})) : X) = x :=
        congrArg Subtype.val hux
      exact ⟨(u : ↥M), ⟨u, hu, rfl⟩, h1⟩
  refine ⟨(Ĵ.map C.subtype).map M.subtype, (isTwoComponentIn_iff hJle).mpr
    (by rw [hJeq]; exact isPComponent_map_mulEquiv eC hĴ), ?_⟩
  let eJ : ↥Ĵ ≃* ↥((Ĵ.map C.subtype).map M.subtype) :=
    ((Ĵ.equivMapOfInjective C.subtype C.subtype_injective).trans
      ((Ĵ.map C.subtype).equivMapOfInjective M.subtype M.subtype_injective))
  have hφĴ : ∀ x : ↥Ĵ, ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} :
      Set (MBar β)))) : MBar β) ∈ Y := by
    intro x
    have : φ x ∈ Ĵ.map φ := mem_map_of_mem φ x.2
    rw [hĴmap] at this
    exact this
  let g₀ : ↥Ĵ →* ↥Y := ((centralizer ({(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} :
    Set (MBar β))).subtype.comp (φ.comp Ĵ.subtype)).codRestrict Y hφĴ
  have hg₀ : Function.Surjective g₀ := by
    rintro ⟨u, hu⟩
    have hu' : (⟨u, hYle hu⟩ : ↥(centralizer ({(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} :
        Set (MBar β)))) ∈ Ĵ.map φ := by
      rw [hĴmap]; exact hu
    obtain ⟨x, hx, hxu⟩ := hu'
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    show ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨y, hyβ⟩ : MBar β)} : Set (MBar β)))) :
      MBar β) = u
    rw [hxu]
  have hg₀k : ¬ 2 ∣ Nat.card g₀.ker := by
    have hle : g₀.ker.map Ĵ.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : g₀ x = 1 := hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h2 := congrArg Subtype.val hx'
      exact h2
    have hc : Nat.card g₀.ker ∣ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective Ĵ.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => hφk (h2.trans hc)
  refine ⟨g₀.comp eJ.symm.toMonoidHom, hg₀.comp eJ.symm.surjective, ?_⟩
  have hk : Nat.card (g₀.comp eJ.symm.toMonoidHom).ker = Nat.card g₀.ker := by
    rw [← MonoidHom.comap_ker]
    exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ eJ.symm.injective).trans
      (MulEquiv.subgroupCongr (by
        rw [Subgroup.map_comap_eq_self_of_surjective eJ.symm.surjective]))).toEquiv
  rw [hk]
  exact hg₀k

end Q81

namespace Setting46e

variable {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}

theorem false_of_conj_z
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hCI : GSLit.ClassicalInvolutionInput) (h219 : Harris82Lemma219Input)
    (hP2 : Harris81Lemma33Simple) (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hT2 : Harris82Theorem2SLTwo)
    (hs : Setting46e t L p f S w z V i j) {R : Subgroup X} (hR : IsSylowOf 2 R ⊤)
    (hRz : R ≤ centralizer ({z} : Set X)) (hZR : R ⊓ centralizer (R : Set X) = zpowers z)
    (hTR : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ R) {β x c : X} (hβ : orderOf β = 2)
    (hx : orderOf x = 2) (hxβ : x ∈ centralizer ({β} : Set X)) (hc : c * x * c⁻¹ = z)
    {J : Subgroup (MBar β)} (hJle : J ≤ centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ : MBar β)})
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ : MBar β)})))
    (hJt : IsOfType (HarrisF 3) ↥J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J₁, hJ₁, g, hg, hgk⟩ := Q81.exists_lift_isTwoComponentIn hxβ hx hJle hJ
  obtain ⟨eZ₁⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective g hg hgk
  have hJ₁t : IsOfType (HarrisF 3) ↥J₁ := by
    obtain ⟨-, Y₀, _, hY₀, ⟨eY⟩⟩ := hJt
    exact ⟨hJ₁.2.2, Y₀, inferInstance, hY₀, ⟨eZ₁.trans eY⟩⟩
  have hβx : β ∈ centralizer ({x} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxβ).symm
  have hJ₁' : IsTwoComponentIn J₁ (centralizer {x} ⊓ centralizer {β}) := by
    rw [inf_comm]
    exact hJ₁
  obtain ⟨hle, hpc, ⟨eO⟩⟩ := L415.isPComponent_barOf hβx hβ hJ₁'
  obtain ⟨eZ₂⟩ := GrSLit.nonempty_fusionZStar_equiv_of_quotient_equiv eO
  have hbar : IsTwoComponentIn (barOf (centralizer {x}) J₁)
      (centralizer {(QuotientGroup.mk ⟨β, hβx⟩ : MBar x)}) := (isTwoComponentIn_iff hle).mpr hpc
  have hbart : IsOfType (HarrisF 3) ↥(barOf (centralizer {x}) J₁) := by
    obtain ⟨-, Y₀, _, hY₀, ⟨eY⟩⟩ := hJ₁t
    exact ⟨hbar.2.2, Y₀, inferInstance, hY₀, ⟨eZ₂.symm.trans eY⟩⟩
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  have hCx : centralizer ({x} : Set X) ≠ ⊤ := by
    intro htop
    have hxZ : x ∈ center X := mem_center_iff.mpr fun g =>
      (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({x} : Set X)))
    rw [(LocalCores.isQuasisimple_of_isSimpleGroup hnonab).2, mem_bot] at hxZ
    exact hx1 hxZ
  have hKG : SectionRank.IsKGroupCat (MBar x) :=
    (GSThmB.isKGroupCat_of_ne_top' hK hCx).quotient _
  obtain ⟨A, hA, hAt⟩ := Q81.exists_component_isOfType (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    hKG (Q81.orderOf_mk_of_two hβx hβ) hbar hbart
  let e := Q81.mbarConj c hc
  have hA' : IsComponent (A.map e.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e hA
  have hA't : IsOfType (HarrisF 3) ↥(A.map e.toMonoidHom) :=
    Q81.isOfType_of_mulEquiv (A.equivMapOfInjective e.toMonoidHom e.injective) hAt
  exact hs.not_isOfType_component hnonab hK hcat hCI h219 hP2 hGO hGC hT2 hR hRz hZR hTR hA'
    hA't

end Setting46e

end CFSG.ComponentClassification.HarrisLit
