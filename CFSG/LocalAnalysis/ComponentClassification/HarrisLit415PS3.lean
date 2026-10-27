module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415P47
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PK
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem isTwoComponentIn_map_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') {J A : Subgroup G} (h : IsTwoComponentIn J A) :
    IsTwoComponentIn (J.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  have hle : J.map e.toMonoidHom ≤ A.map e.toMonoidHom := map_mono h.1
  rw [isTwoComponentIn_iff hle]
  have h1 := isPComponent_map_mulEquiv (A.equivMapOfInjective e.toMonoidHom e.injective)
    ((isTwoComponentIn_iff h.1).mp h)
  convert h1 using 1
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, h.1 hx⟩, hx, rfl⟩
  · rintro ⟨⟨x, hxA⟩, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩

theorem layerIn_inf_eq_of_unique {G : Type*} [Group G] [Finite G] {E : Subgroup G} [E.Normal]
    {b : G} {J : Subgroup G} (hJE : J ≤ E) (hJb : J ≤ centralizer {b})
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer {b})))
    (huniq : ∀ J' : Subgroup ↥(centralizer ({b} : Set G)), IsPComponent 2 J' →
      J' = J.subgroupOf (centralizer {b})) :
    IsTwoComponentIn J (E ⊓ centralizer {b}) ∧
      (∀ J' : Subgroup G, IsTwoComponentIn J' (E ⊓ centralizer {b}) → J' = J) ∧
      GSThmB.layerIn (E ⊓ centralizer {b}) = J := by
  have hJ : IsTwoComponentIn J (E ⊓ centralizer {b}) := by
    rw [isTwoComponentIn_iff (le_inf hJE hJb)]
    exact UnbalancedCorr.isPComponent_subgroupOf_of_le (le_inf hJE hJb) inf_le_right hJc
  have hu : ∀ J' : Subgroup G, IsTwoComponentIn J' (E ⊓ centralizer {b}) → J' = J := by
    intro J' hJ'
    have h1 := (isTwoComponentIn_iff hJ'.1).mp hJ'
    have h2 := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hJ'.1 inf_le_right
      (by rw [inf_subgroupOf_right]; exact Subgroup.Normal.isSubnormal inferInstance) h1
    have h3 := (Subgroup.subgroupOf_inj).mp (huniq _ h2)
    rwa [inf_of_le_left (hJ'.1.trans inf_le_right), inf_of_le_left hJb] at h3
  exact ⟨hJ, hu, layerIn_eq_of_unique hJ hu⟩

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem orderOf_alpha : orderOf α = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [sq, hD.alpha_mul_alpha]) fun h1 => ?_
  obtain ⟨g, hgα, -, -⟩ := hD.fd.α_conj
  apply Standing.t_ne_one hD.hs.standing
  rw [h1] at hgα
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [hgα]; group

theorem exists_J₀ (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    ∃ J₀ : Subgroup X, IsTwoComponentIn J₀ (centralizer {z₁} ⊓ centralizer {α}) ∧
      (∀ J, IsTwoComponentIn J (centralizer {z₁} ⊓ centralizer {α}) → J = J₀) ∧
      Blueprint.LieModel (↥J₀ ⧸ pPrimeCore 2 ↥J₀) .PSL 2 p (f / 2) := by
  obtain ⟨g, i', j', hgα, hgz, -, -⟩ := hD.exists_conj_x hnβ
  set x := w ^ (orderOf w / 2) * t ^ i' * z ^ j' with hx
  set K' := centralizerResidual L x with hK'
  have hσ := hD.hs.setup
  have hK'M := Standing.K_le_M hD.hs.standing x
  have hK'c : IsTwoComponentIn K' (centralizer {t} ⊓ centralizer {x}) :=
    (isTwoComponentIn_iff hK'M).mpr (hσ.isPComponent_K hFC hKC i' j')
  have hK'L : GSThmB.layerIn (centralizer {t} ⊓ centralizer {x}) = K' := hσ.pLayer_M hFC hKC i' j'
  have hCC : (centralizer {t} ⊓ centralizer {x}).map (MulAut.conj g).toMonoidHom =
      centralizer {z₁} ⊓ centralizer {α} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, L415.map_conj_centralizer,
      L415.map_conj_centralizer, hgα, hgz, inf_comm]
  refine ⟨K'.map (MulAut.conj g).toMonoidHom, ?_, fun J hJ => ?_, ?_⟩
  · rw [← hCC]
    exact L415.isTwoComponentIn_map_mulEquiv _ hK'c
  · have h1 := L415.isTwoComponentIn_map_mulEquiv (MulAut.conj g⁻¹) hJ
    rw [← hCC, map_map, show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id X by ext; simp [mul_assoc], map_id] at h1
    have h2 := L415.eq_of_layerIn_eq hK'c hK'L h1
    rw [← h2, map_map, show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id X by ext; simp [mul_assoc], map_id]
  · have e := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (K'.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    exact GSThmB.OddQuot.lieModel_of_equiv e (hσ.lieModel_bar_K hFC hKC i' j')

theorem orderOf_alphaF :
    orderOf (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine orderOf_mk_eq_two hodd ?_
  rw [Subgroup.orderOf_mk]
  exact hD.orderOf_alpha

theorem lieModel_layerIn_alpha [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h34 : Harris81Lemma34Input)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    (hM : IsComponent (layer (MBar z₁))) (hEs : IsSimpleGroup ↥(layer (MBar z₁)))
    (hF : IsOfType (HarrisF p) ↥(layer (MBar z₁)))
    (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁)) :
    (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁) ∉
        centralizer ((layer (MBar z₁) : Subgroup (MBar z₁)) : Set (MBar z₁)) ∧
      Blueprint.LieModel ↥(GSThmB.layerIn (layer (MBar z₁) ⊓
        centralizer {(QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁)})) .PSL 2 p (f / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (layer (MBar z₁)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar z₁)
    infer_instance
  have hq : IsQuasisimple ↥(layer (MBar z₁)) := hM.1
  obtain ⟨hOE, hZs⟩ := oddCore_fusionZStar_component hM
  obtain ⟨J₀, hJ₀, hJ₀u, hJ₀L⟩ := hD.exists_J₀ hFC hKC hnβ
  obtain ⟨hJC, hJpc, ⟨eJ⟩⟩ := L415.isPComponent_barOf hD.alpha_mem_F hD.orderOf_alpha hJ₀
  have huniqF := L415.eq_barOf_of_unique hD.alpha_mem_F hD.orderOf_alpha hJ₀u
  have hJE := L415.barOf_le_layer hD.alpha_mem_F hD.orderOf_alpha
    (hD.schreierSections_F hnab hK hSch) hJ₀
  obtain ⟨hJc, -, hlay⟩ := L415.layerIn_inf_eq_of_unique hJE hJC hJpc huniqF
  have hJbL : Blueprint.LieModel (↥(barOf (centralizer {z₁}) J₀) ⧸
      pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀)) .PSL 2 p (f / 2) :=
    GSThmB.OddQuot.lieModel_of_equiv eJ hJ₀L
  have : IsSimpleGroup (↥(barOf (centralizer {z₁}) J₀) ⧸
      pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀)) := isSimpleGroup_of_lieModel_psl2 hJbL
  have hKZ : center (↥(barOf (centralizer {z₁}) J₀) ⧸
      pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀)) = ⊥ :=
    (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hJbL)).2
  have hαE : (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁) ∉
      centralizer ((layer (MBar z₁) : Subgroup (MBar z₁)) : Set (MBar z₁)) := by
    intro hα
    have hEC : layer (MBar z₁) ⊓ centralizer {(QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ :
        MBar z₁)} = layer (MBar z₁) := by
      refine inf_eq_left.mpr fun e he => mem_centralizer_singleton_iff.mpr ?_
      exact mem_centralizer_iff.mp hα e he
    have hJc' := hJc
    rw [hEC] at hJc'
    have hJeq : barOf (centralizer {z₁}) J₀ = layer (MBar z₁) := by
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hEs hJc'.2.1 with h | h
      · exfalso
        have hnt : Nontrivial (↥(barOf (centralizer {z₁}) J₀) ⧸
            pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀)) := IsSimpleGroup.toNontrivial
        obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(barOf (centralizer {z₁}) J₀) ⧸
          pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀))
        apply hab
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        have ha : (a : MBar z₁) = 1 := by
          have h1 : (⟨a, hJE a.2⟩ : ↥(layer (MBar z₁))) ∈
              (barOf (centralizer {z₁}) J₀).subgroupOf (layer (MBar z₁)) := a.2
          rw [h, mem_bot] at h1
          exact congrArg Subtype.val h1
        have hb : (b : MBar z₁) = 1 := by
          have h1 : (⟨b, hJE b.2⟩ : ↥(layer (MBar z₁))) ∈
              (barOf (centralizer {z₁}) J₀).subgroupOf (layer (MBar z₁)) := b.2
          rw [h, mem_bot] at h1
          exact congrArg Subtype.val h1
        rw [show a = 1 from Subtype.ext ha, show b = 1 from Subtype.ext hb]
      · refine le_antisymm hJE fun e he => ?_
        have h1 : (⟨e, he⟩ : ↥(layer (MBar z₁))) ∈
            (barOf (centralizer {z₁}) J₀).subgroupOf (layer (MBar z₁)) := by rw [h]; trivial
        exact h1
    have hOJ : pPrimeCore 2 ↥(barOf (centralizer {z₁}) J₀) = ⊥ := by
      have hsn : (barOf (centralizer {z₁}) J₀).IsSubnormal := by
        rw [hJeq]
        exact hEn.isSubnormal
      exact pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hsn
    have h1 : Nat.card ↥(barOf (centralizer {z₁}) J₀) =
        Nat.card ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hOJ).trans
        QuotientGroup.quotientBot).toEquiv, GH74.card_of_lieModel_PSL (by norm_num) hJbL,
        GH74.card_of_lieModel_PSL (by norm_num) (hD.hs.lieModel_KBar hD.h412)]
    have h2 := Subgroup.card_lt_of_lt hlt
    rw [← hJeq, h1] at h2
    exact absurd h2 (not_lt.mpr hD.card_KBar_le)
  refine ⟨hαE, ?_⟩
  have hT : zpowers (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁) ≤
      normalizer ((layer (MBar z₁) : Subgroup (MBar z₁)) : Set (MBar z₁)) := by
    rw [normalizer_eq_top]
    exact le_top
  have hτE : ⁅layer (MBar z₁), zpowers (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁)⁆ =
      layer (MBar z₁) := by
    rcases commutator_eq_self_or_eq_bot_of_le_normalizer hT hq with h | h
    · exact h
    · exfalso
      apply hαE
      exact mem_centralizer_iff.mpr fun e he => (commutator_eq_bot_iff_le_centralizer.mp h he
        |> mem_centralizer_iff.mp) _ (mem_zpowers _) |>.symm
  have hFE : HarrisF p (↥(layer (MBar z₁)) ⧸ center ↥(layer (MBar z₁))) := by
    obtain ⟨-, Y, _, hY, ⟨eY⟩⟩ := hF
    exact harrisF_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZs.symm).trans eY).symm hY
  have hO := pPrimeCore_eq_bot_of_harris34 h34 hq (isPGroup_center_of_pPrimeCore_eq_bot hOE)
    hD.orderOf_alphaF hτE hJc hKZ hD.hs.prime_p hD.hs.p_ne_two hFE ⟨p, f / 2, hJbL⟩
  rw [hlay]
  exact lieModel_psl2_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO).trans
    QuotientGroup.quotientBot).symm hJbL

end Data415B

end CFSG.ComponentClassification.HarrisLit
