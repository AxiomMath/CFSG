module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarOf
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthHyp

public section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup

theorem isL4U4Mod4_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : IsL4U4Mod4 X p f) : IsL4U4Mod4 Y p f := by
  rcases h with ⟨h, hq⟩ | ⟨h, hq⟩
  · exact Or.inl ⟨LieType.CurtisTits.lieModel_of_mulEquiv e h, hq⟩
  · exact Or.inr ⟨LieType.CurtisTits.lieModel_of_mulEquiv e h, hq⟩

structure BarData6 {P : Type} [Group P] (E : Subgroup (MulAut P)) (L : Subgroup P) (t : P)
    (J J₀ : Subgroup P) (p f : ℕ) : Prop where
  hE : IsPGroup 2 E
  hLE : L ≤ QPUCl.fixedBy E
  hLc : IsPComponent 2 (L.subgroupOf (QPUCl.fixedBy E))
  hLtop : L ≠ ⊤
  hLm : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f
  htL : t ∈ L
  ht2 : t * t = 1
  ht1 : t ≠ 1
  hJt : J ≤ centralizer {t}
  hJc : IsPComponent 2 (J.subgroupOf (centralizer {t}))
  hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f)
  hJ₀L : J₀ ≤ L
  hJ₀J : J₀ ≤ J
  hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J

@[expose] def BarConfig6 (P : Type) [Group P] (p f : ℕ) : Prop :=
  ∃ (E : Subgroup (MulAut P)) (L : Subgroup P) (t : P) (J J₀ : Subgroup P),
    BarData6 E L t J J₀ p f

theorem center_eq_bot_of_isL4U4Mod4 {X : Type} [Group X] [Group.IsPerfect X] {p f : ℕ}
    (h : IsL4U4Mod4 X p f) : center X = ⊥ := by
  have := QPUJ6.isSimpleGroup h
  exact QPUCl.center_eq_bot_of_simple_perfect'

variable {M : Type} [Group M] [Finite M]

theorem barConfig6_of_data {p f : ℕ} (hM : IsQuasisimple M) (hZ : IsPGroup 2 (center M))
    (hc : ∃ (E : Subgroup (MulAut M)) (L : Subgroup M) (t : M) (J J₀ : Subgroup M),
      IsPGroup 2 E ∧ L ≤ QPUJ.autFixed E ∧ IsPComponent 2 (L.subgroupOf (QPUJ.autFixed E)) ∧
      L ≠ ⊤ ∧ IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f ∧
      t ∈ L ∧ t * t = 1 ∧ t ∉ center M ∧
      J ≤ centralizer ({t} : Set M) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M))) ∧
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f) ∧
      J₀ ≤ L ∧ J₀ ≤ J ∧ J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    BarConfig6 (M ⧸ center M) p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, L, t, J, J₀, hE, hLE, hLc, hLtop, hLm, htL, ht2, htZ, hJt, hJc, hJm, hJ₀L, hJ₀J,
    hJ₀⟩ := hc
  have hLE' : L ≤ QPUCl.fixedBy E := hLE
  have hLc' : IsPComponent 2 (L.subgroupOf (QPUCl.fixedBy E)) := hLc
  have : Group.IsPerfect M := hM.1
  have hLperf := QPUCl.isPerfect_of_isPComponent hLE' hLc'
  have hJperf := QPUCl.isPerfect_of_isPComponent hJt hJc
  have hLZ := QPUCl.inf_center_eq_bot hZ (center_eq_bot_of_isL4U4Mod4 hLm)
  have hJZ := QPUCl.inf_center_eq_bot hZ (QPUCl.center_eq_bot_of_lieModel (Or.inl rfl) hJm)
  set eL := QPUCl.equivMapMk hLZ with heL
  set eJ := QPUCl.equivMapMk hJZ with heJ
  obtain ⟨hLb, hLbc⟩ := QPUCl.isPComponent_map_fixedBy E hLE' hLc'
  obtain ⟨hJb, hJbc⟩ := QPUCl.isPComponent_map_centralizer t hJt hJc
  refine ⟨E.map (QPUCl.quotAut M), L.map (QuotientGroup.mk' (center M)),
    QuotientGroup.mk' (center M) t, J.map (QuotientGroup.mk' (center M)),
    J₀.map (QuotientGroup.mk' (center M)), ⟨hE.map _, hLb, hLbc, QPUCl.map_mk_ne_top hLtop,
    isL4U4Mod4_of_mulEquiv (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) hLm,
    ⟨t, htL, rfl⟩, by rw [← map_mul, ht2, map_one], ?_, hJb, hJbc,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm,
    map_mono hJ₀L, map_mono hJ₀J, ?_⟩⟩
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact htZ
  · have hmapO : ((pPrimeCore 2 ↥J).map J.subtype).map (QuotientGroup.mk' (center M)) =
        (pPrimeCore 2 ↥(J.map (QuotientGroup.mk' (center M)))).map
          (J.map (QuotientGroup.mk' (center M))).subtype := by
      rw [← pPrimeCore_map_iso 2 eJ, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← hmapO, ← Subgroup.map_sup, hJ₀]

theorem barConfig6_of_config {p f : ℕ} (hc : QPUJ6Config M p f) :
    BarConfig6 (M ⧸ center M) p f :=
  barConfig6_of_data hc.1 hc.2.1 hc.2.2.2.2.2.2

variable {P P' : Type} [Group P] [Group P'] {E : Subgroup (MulAut P)} {L : Subgroup P} {t : P}
  {J J₀ : Subgroup P} {p f : ℕ}

theorem BarData6.map (h : BarData6 E L t J J₀ p f) (φ : P ≃* P') :
    BarData6 (E.map (MulAut.congr φ).toMonoidHom) (L.map φ.toMonoidHom) (φ t)
      (J.map φ.toMonoidHom) (J₀.map φ.toMonoidHom) p f := by
  have hfix := QPUCl.fixedBy_map_congr φ E
  have hcent := QPUCl.centralizer_map_equiv φ t
  refine ⟨h.hE.map _, ?_, ?_, ?_,
    isL4U4Mod4_of_mulEquiv (QuotientGroup.congr _ _ (L.equivMapOfInjective φ.toMonoidHom
      φ.injective) (pPrimeCore_map_iso 2 _)) h.hLm, ⟨t, h.htL, rfl⟩,
    by rw [← map_mul, h.ht2, map_one], fun h1 => h.ht1 (φ.injective (by rw [h1, map_one])), ?_,
    ?_, QPUCl.lieModel_map_equiv φ h.hJm, map_mono h.hJ₀L, map_mono h.hJ₀J, ?_⟩
  · rw [hfix]
    exact map_mono h.hLE
  · rw [hfix]
    exact QPUCl.isPComponent_map_subgroupOf φ h.hLE h.hLc
  · intro htop
    apply h.hLtop
    have := congrArg (Subgroup.map φ.symm.toMonoidHom) htop
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id P from by
      ext; simp, Subgroup.map_id, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 φ.symm.surjective] at this
  · rw [hcent]
    exact map_mono h.hJt
  · rw [hcent]
    exact QPUCl.isPComponent_map_subgroupOf φ h.hJt h.hJc
  · have hO : ((pPrimeCore 2 ↥J).map J.subtype).map φ.toMonoidHom =
        (pPrimeCore 2 ↥(J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype := by
      rw [← pPrimeCore_map_iso 2 (J.equivMapOfInjective φ.toMonoidHom φ.injective),
        Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← hO, ← Subgroup.map_sup, h.hJ₀]

theorem BarData6.noE8 [Finite P] (h : BarData6 E L t J J₀ p f) (hp2 : p ≠ 2) :
    ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ X10Orth.E8Triple u v w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu v hv w hw hT
  obtain ⟨hp, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h.hJm
  have hT3 : X10Orth.E8Triple (⟨u, hu⟩ : J) ⟨v, hv⟩ ⟨w, hw⟩ :=
    X10Orth.E8Triple.comap (φ := J.subtype) J.subtype_injective hT
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  refine X10Orth.false_of_statedProjSL h2 (hT3.map (e.toMonoidHom.comp
    (QuotientGroup.mk' (pPrimeCore 2 ↥J))) fun g hg h1 => ?_)
  have h1' : QuotientGroup.mk' (pPrimeCore 2 ↥J) g = 1 :=
    e.injective (by rw [map_one]; exact h1)
  have hgO : g ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff g).mp h1'
  have hd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg)
  have hdO : orderOf g ∣ Nat.card (pPrimeCore 2 ↥J) := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : pPrimeCore 2 ↥J)
    rwa [Subgroup.orderOf_mk] at this
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥J)
  have h1g : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hdO
  exact orderOf_eq_one_iff.mp h1g

theorem BarData6.simple_L (h : BarData6 E L t J J₀ p f) :
    IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) :=
  QPUJ6.isSimpleGroup h.hLm

theorem BarData6.primeResidual_L [Finite P] (h : BarData6 E L t J J₀ p f) :
    CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L (QPUCl.fixedBy E) h.hLE).1 h.hLc).2.1

theorem BarData6.exists_ne_one [Finite P] [hP : IsSimpleGroup P] (h : BarData6 E L t J J₀ p f) :
    ∃ e ∈ E, e ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have htop : QPUCl.fixedBy E = ⊤ := by
    rw [eq_top_iff]
    intro x _ e he
    rw [hne e he]
    rfl
  have hsub := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L (QPUCl.fixedBy E) h.hLE).1
    h.hLc).1
  have htopsub : (QPUCl.fixedBy E).IsSubnormal := by
    rw [htop]
    exact Subgroup.IsSubnormal.top
  have hL := Subgroup.IsSubnormal.trans h.hLE hsub htopsub
  rcases hL.eq_bot_or_top_of_isSimpleGroup hP with h1 | h1
  · exact Burgoyne.C.ne_bot_of_isPComponent h.hLE h.hLc h1
  · exact h.hLtop h1

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
