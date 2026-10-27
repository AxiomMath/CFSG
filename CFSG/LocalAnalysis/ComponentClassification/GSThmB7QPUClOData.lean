module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthHyp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup

structure BarData {P : Type} [Group P] (E : Subgroup (MulAut P)) (L : Subgroup P) (t : P)
    (J J₀ : Subgroup P) (p f : ℕ) : Prop where
  hE : IsPGroup 2 E
  hLE : L ≤ fixedBy E
  hLc : IsPComponent 2 (L.subgroupOf (fixedBy E))
  hLtop : L ≠ ⊤
  hLm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f
  htL : t ∈ L
  ht2 : t * t = 1
  ht1 : t ≠ 1
  hJt : J ≤ centralizer {t}
  hJc : IsPComponent 2 (J.subgroupOf (centralizer {t}))
  hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f
  hJ₀L : J₀ ≤ L
  hJ₀J : J₀ ≤ J
  hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J

theorem BarConfig.exists_barData {P : Type} [Group P] {p f : ℕ} (h : BarConfig P p f p f) :
    ∃ (E : Subgroup (MulAut P)) (L : Subgroup P) (t : P) (J J₀ : Subgroup P),
      BarData E L t J J₀ p f := by
  obtain ⟨E, L, t, J, J₀, hE, hLE, hLc, hLtop, hLm, htL, ht2, ht1, hJt, hJc, hJm, hJ₀L, hJ₀J,
    hJ₀⟩ := h
  exact ⟨E, L, t, J, J₀, ⟨hE, hLE, hLc, hLtop, hLm, htL, ht2, ht1, hJt, hJc, hJm, hJ₀L, hJ₀J, hJ₀⟩⟩

variable {P P' : Type} [Group P] [Group P'] {E : Subgroup (MulAut P)} {L : Subgroup P} {t : P}
  {J J₀ : Subgroup P} {p f : ℕ}

theorem BarData.map (h : BarData E L t J J₀ p f) (φ : P ≃* P') :
    BarData (E.map (MulAut.congr φ).toMonoidHom) (L.map φ.toMonoidHom) (φ t)
      (J.map φ.toMonoidHom) (J₀.map φ.toMonoidHom) p f := by
  have hfix := fixedBy_map_congr φ E
  have hcent := centralizer_map_equiv φ t
  refine ⟨h.hE.map _, ?_, ?_, ?_, lieModel_map_equiv φ h.hLm, ⟨t, h.htL, rfl⟩,
    by rw [← map_mul, h.ht2, map_one], fun h1 => h.ht1 (φ.injective (by rw [h1, map_one])), ?_,
    ?_, lieModel_map_equiv φ h.hJm, map_mono h.hJ₀L, map_mono h.hJ₀J, ?_⟩
  · rw [hfix]
    exact map_mono h.hLE
  · rw [hfix]
    exact isPComponent_map_subgroupOf φ h.hLE h.hLc
  · intro htop
    apply h.hLtop
    have := congrArg (Subgroup.map φ.symm.toMonoidHom) htop
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id P from by
      ext; simp, Subgroup.map_id, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 φ.symm.surjective] at this
  · rw [hcent]
    exact map_mono h.hJt
  · rw [hcent]
    exact isPComponent_map_subgroupOf φ h.hJt h.hJc
  · have hO : ((pPrimeCore 2 ↥J).map J.subtype).map φ.toMonoidHom =
        (pPrimeCore 2 ↥(J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype := by
      rw [← pPrimeCore_map_iso 2 (J.equivMapOfInjective φ.toMonoidHom φ.injective),
        Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← hO, ← Subgroup.map_sup, h.hJ₀]

theorem BarData.noE8 [Finite P] (h : BarData E L t J J₀ p f) (hp2 : p ≠ 2) :
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

theorem BarData.simple_L (h : BarData E L t J J₀ p f) :
    IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) := by
  have hcl : Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f := by
    rcases h.hLm with ⟨-, h⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · exact h
    all_goals exact absurd htag (by decide)
  exact ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 p f hcl

theorem BarData.primeResidual_L [Finite P] (h : BarData E L t J J₀ p f) :
    CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L (fixedBy E) h.hLE).1 h.hLc).2.1

theorem BarData.exists_ne_one [Finite P] [hP : IsSimpleGroup P] (h : BarData E L t J J₀ p f) :
    ∃ e ∈ E, e ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have htop : fixedBy E = ⊤ := by
    rw [eq_top_iff]
    intro x _ e he
    rw [hne e he]
    rfl
  have hsub := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L (fixedBy E) h.hLE).1 h.hLc).1
  have htopsub : (fixedBy E).IsSubnormal := by
    rw [htop]
    exact Subgroup.IsSubnormal.top
  have hL := Subgroup.IsSubnormal.trans h.hLE hsub htopsub
  rcases hL.eq_bot_or_top_of_isSimpleGroup hP with h1 | h1
  · exact Burgoyne.C.ne_bot_of_isPComponent h.hLE h.hLc h1
  · exact h.hLtop h1

end CFSG.ComponentClassification.GSThmB.QPUCl
