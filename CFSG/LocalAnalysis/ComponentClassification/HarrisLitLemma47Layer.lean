module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47C1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dii

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Lemma47

theorem commutator_self_eq_of_isPerfect {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) : ⁅H, H⁆ = H := by
  have h := congrArg (Subgroup.map H.subtype) hH.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem eq_bot_of_le_centralizer_self {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) (hc : H ≤ centralizer (H : Set G)) : H = ⊥ := by
  rw [← commutator_self_eq_of_isPerfect hH]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

theorem ne_bot_of_isQuasisimple {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsQuasisimple ↥H) : H ≠ ⊥ := by
  intro hb
  have := LocalCores.isQuasisimple_nontrivial hH
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥H
  apply hxy
  have hx : (x : G) ∈ (⊥ : Subgroup G) := hb ▸ x.2
  have hy : (y : G) ∈ (⊥ : Subgroup G) := hb ▸ y.2
  rw [mem_bot] at hx hy
  exact Subtype.ext (hx.trans hy.symm)

theorem lieModel_quotient_center_psl_two {Y : Type} [Group Y] {p n : ℕ}
    (hm : Blueprint.LieModel Y .PSL 2 p n) : Blueprint.LieModel (Y ⧸ center Y) .PSL 2 p n := by
  have := isSimpleGroup_of_lieModel_psl2 hm
  have hZ := (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hm)).2
  exact GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)) hm

theorem not_four_of_mulEquiv_psl_two {Q Y : Type} [Group Q] [Group Y] {p n k : ℕ} (hp2 : p ≠ 2)
    (e : Q ≃* Y) (hm : Blueprint.LieModel Y .PSL 2 p n)
    (h4 : Blueprint.LieModel (Q ⧸ center Q) .PSL 4 p k ∨
      Blueprint.LieModel (Q ⧸ center Q) .PSU 4 p k) : False := by
  have hmQ := lieModel_quotient_center_psl_two (GSThmB.OddQuot.lieModel_of_equiv e.symm hm)
  exact not_lieModel_psl_two_of_four hp2 hmQ h4

theorem isComponent_of_sup {G : Type} [Group G] {K K' : Subgroup G} {p n : ℕ}
    (hm : Blueprint.LieModel ↥K .PSL 2 p n) (hKK' : K' ≤ centralizer (K : Set G))
    (hsub : (K ⊔ K').IsSubnormal) : IsComponent K := by
  have := isSimpleGroup_of_lieModel_psl2 hm
  refine ⟨(LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hm)).1,
    IsSubnormal.step K (K ⊔ K') le_sup_left hsub ?_⟩
  rw [normal_subgroupOf_iff le_sup_left]
  intro a b ha hb
  have hN : K ⊔ K' ≤ normalizer (K : Set G) :=
    sup_le le_normalizer (hKK'.trans (Subgroup.centralizer_le_normalizer (K : Set G)))
  exact (mem_normalizer_iff.mp (hN hb) a).mp ha

end Lemma47

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem lieModel_KBar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) (he : IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    Blueprint.LieModel ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) .PSL 2 p (f / 2) := by
  obtain ⟨eK⟩ := nonempty_KBar_quotient_equiv L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  have e : ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≃*
      ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⧸
        pPrimeCore 2 ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq he.symm)
  exact GSThmB.OddQuot.lieModel_of_equiv (e.trans eK).symm (hσ.lieModel_bar_K hFC hKC i j)

theorem Lemma47.layer_of_isPComponent_four {β : X} {tb : MBar β} (hp2 : p ≠ 2)
    (hd : IsLemma46d p f L β tb) {J : Subgroup ↥(centralizer ({β} : Set X))}
    (hJ : IsPComponent 2 J) {k : ℕ}
    (htype : IsOfType (fun (Y : Type) [Group Y] =>
      Blueprint.LieModel Y .PSL 4 p k ∨ Blueprint.LieModel Y .PSU 4 p k) ↥J) :
    IsQuasisimple ↥(layer (MBar β)) ∧
      (Blueprint.LieModel (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) .PSL 4 p k ∨
        Blueprint.LieModel (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) .PSU 4 p k) ∧
      J.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) =
        layer (MBar β) := by
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨K₀, hK₀, -, hJK₀, -⟩ := hJ
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))
  have hJK : J.map π ≤ K₀ := hJK₀.le
  let g : ↥J →* ↥K₀ := (π.comp J.subtype).codRestrict K₀ (fun x => hJK ⟨x, x.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hJK₀] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgker : ¬ 2 ∣ Nat.card g.ker := by
    have hle : g.ker.map J.subtype ≤ pPrimeCore 2 ↥(centralizer ({β} : Set X)) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥(centralizer ({β} : Set X))) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card g.ker ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({β} : Set X))) := by
      rw [← Subgroup.card_map_of_injective J.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hc)
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective g hg hgker
  have hO₀ : pPrimeCore 2 ↥K₀ = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hK₀.2
  have eK : ↥J ⧸ Open.fusionZStar ↥J ≃* ↥K₀ ⧸ center ↥K₀ :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hO₀))
  obtain ⟨-, Y, _, hY, ⟨eY⟩⟩ := htype
  have hm₀ : Blueprint.LieModel (↥K₀ ⧸ center ↥K₀) .PSL 4 p k ∨
      Blueprint.LieModel (↥K₀ ⧸ center ↥K₀) .PSU 4 p k := by
    rcases hY with hY | hY
    · exact .inl (GSThmB.OddQuot.lieModel_of_equiv (eK.symm.trans eY).symm hY)
    · exact .inr (GSThmB.OddQuot.lieModel_of_equiv (eK.symm.trans eY).symm hY)
  have hK₀E : K₀ ≤ layer (MBar β) := le_sSup hK₀
  have hEn : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hK₀eq : K₀ = layer (MBar β) := by
    rcases hd with ⟨hEq, -⟩ | ⟨K₁, K₂, h12, -, hc12, -, ⟨e₁⟩, ⟨e₂⟩, hmK, -, -⟩
    · have hEc : IsComponent (layer (MBar β)) := ⟨hEq, hEn.isSubnormal⟩
      rcases LocalCores.distinct_components_commute hK₀ hEc with h1 | h1
      · exact h1
      · exfalso
        have hc : K₀ ≤ centralizer (K₀ : Set (MBar β)) :=
          (commutator_eq_bot_iff_le_centralizer.mp h1).trans (centralizer_le hK₀E)
        exact Lemma47.ne_bot_of_isQuasisimple hK₀.1
          (Lemma47.eq_bot_of_le_centralizer_self hK₀.1.1 hc)
    · exfalso
      have hc21 : K₂ ≤ centralizer (K₁ : Set (MBar β)) := le_centralizer_iff.mp hc12
      have hK₁c : IsComponent K₁ :=
        Lemma47.isComponent_of_sup (GSThmB.OddQuot.lieModel_of_equiv e₁.symm hmK) hc21
          (h12 ▸ hEn.isSubnormal)
      have hK₂c : IsComponent K₂ :=
        Lemma47.isComponent_of_sup (GSThmB.OddQuot.lieModel_of_equiv e₂.symm hmK) hc12
          (by rw [sup_comm] at h12; exact h12 ▸ hEn.isSubnormal)
      rcases LocalCores.distinct_components_commute hK₀ hK₁c with h1 | h1
      · subst h1
        exact Lemma47.not_four_of_mulEquiv_psl_two hp2 e₁ hmK hm₀
      rcases LocalCores.distinct_components_commute hK₀ hK₂c with h2 | h2
      · subst h2
        exact Lemma47.not_four_of_mulEquiv_psl_two hp2 e₂ hmK hm₀
      have hle : layer (MBar β) ≤ centralizer (K₀ : Set (MBar β)) := by
        rw [← h12]
        exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1))
          (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h2))
      exact Lemma47.ne_bot_of_isQuasisimple hK₀.1
        (Lemma47.eq_bot_of_le_centralizer_self hK₀.1.1 (hK₀E.trans hle))
  subst hK₀eq
  exact ⟨hK₀.1, hm₀, hJK₀⟩

theorem tBar_not_mem_centralizer_layer [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) {k : ℕ}
    (he : IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hE : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hm : Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 p k ∨
      Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 p k) :
    hσ.tBar i j ∉ centralizer
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : Set (MBar (w ^ (orderOf w / 2) *
        t ^ i * z ^ j))) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  intro htc
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hEn : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hEc : IsComponent (layer (MBar β)) := ⟨hE, hEn.isSubnormal⟩
  have hEt : layer (MBar β) ≤ layer (MBar β) ⊓ centralizer {hσ.tBar i j} := by
    refine le_inf le_rfl fun x hx => mem_centralizer_singleton_iff.mpr ?_
    exact ((mem_centralizer_iff.mp htc) x hx)
  have h1 := le_layerIn_of_isComponent hO hEc hEt
  rw [hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j] at h1
  have heq : layer (MBar β) = KBar L β :=
    le_antisymm h1 (hσ.KBar_le_layer hnonab hK hSch hFC hKC i j)
  exact Lemma47.not_four_of_mulEquiv_psl_two h.config.ne_two (MulEquiv.subgroupCongr heq)
    (hσ.lieModel_KBar hFC hKC i j he) hm

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
