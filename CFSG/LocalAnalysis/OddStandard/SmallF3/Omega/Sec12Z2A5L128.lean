module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Set
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Wr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Clo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127K

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma128K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    CFSG.Assembly.KProper Catalog G → Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X →
      Sec128Alt1 t S L (secV t S L E) ∨ Sec128Alt2 (secV t S L E)

theorem isKGroupCat_secNb {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hK : CFSG.Assembly.KProper Catalog G) {V : Subgroup G} (hV : IsElemAb2 V 8) :
    CFSG.SectionRank.IsKGroupCat ↥(secNb V) := by
  have hne : secN V ≠ ⊤ := by
    intro htop
    have hn : V.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hs.eq_bot_or_eq_top_of_normal V with hb | ht
    · have hc := hV.2
      rw [hb, Subgroup.card_bot] at hc
      norm_num at hc
    · have hc := hV.2
      rw [ht, Subgroup.card_top] at hc
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 := (IsPGroup.of_card hc).isSimpleGroup_iff_card_eq.mp hs
      rw [hc] at h2
      norm_num at h2
  have hKN : CFSG.SectionRank.IsKGroupCat ↥(secN V) :=
    CFSG.ComponentClassification.UnbalancingLocal.kGroupOver_of_kProper
      (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => CFSG.ComponentClassification.UnbalancingLocal.catalog_of_abelian_simple
        S hcomm) hK (secN V) hne
  exact isKGroupCat_autIn hKN

theorem asc82Lemma128K_of (hp : Asc82Pre11) (h123 : Asc82Lemma123) (h124 : Asc82Lemma124)
    (h125a : Asc82Lemma125a) (h125b : Asc82Lemma125b) (h127 : Asc82Lemma127)
    (hZ : Asc82Z2A5K) (hn34 : Asc82S8NoL34X) (hn216 : Asc82S8NoL216) (hdich : Asc82S8Dich)
    (hsplit : Asc82S8Split) : Asc82Lemma128K := by
  intro G _ _ t L S z K1 K2 E X hKP hctx hX
  have hV8 : IsElemAb2 (secV t S L E) 8 := h124 G t L S z K1 K2 E hctx
  have hA5 := (h123 G t L S z K1 K2 E X hctx hX).1
  obtain ⟨hXN, hXt, -⟩ := sec127_X_le hp hctx hX hA5
  obtain ⟨V1, V2, hsup, hinf, hnat1, hnat2⟩ := sec128_alt1_nat hX hA5 hV8.1
  obtain ⟨φ1, hc1⟩ := sec127_natCoord_of hnat1
  obtain ⟨φ2, hc2⟩ := sec127_natCoord_of hnat2
  have h1V : V1 ≤ secV t S L E := le_trans le_sup_left hsup.le
  have hbot : X ⊓ centralizer (secV t S L E : Set G) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← sec127_nat_cent_bot hc1 hA5]
    exact inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h1V))
  have ht1 : betaOf (secV t S L E) t ≠ 1 := by
    intro h1
    have hmem : (∃ b ∈ secNb (secV t S L E),
          (1 : MulAut ↥(secV t S L E)) = b * betaOf (secV t S L E) t * b⁻¹) ∧
        (1 : MulAut ↥(secV t S L E)) ∈ Subgroup.centralizer {betaOf (secV t S L E) t} :=
      ⟨⟨1, Subgroup.one_mem _, by simp [h1]⟩, Subgroup.one_mem _⟩
    exact ((h127 G t L S z K1 K2 E X hctx hX 1).mp hmem).2.2 rfl
  have htN : t ∈ normalizer (secV t S L E : Set G) := by
    by_contra hn
    apply ht1
    rw [betaOf, dif_neg hn]
  have ht2 : t * t = 1 := sec126_mul_self_of_orderOf hctx.involution
  have hτ2 : betaOf (secV t S L E) t * betaOf (secV t S L E) t = 1 := by
    rw [← sec127_betaOf_mul htN htN, ht2, sec127_betaOf_one]
  obtain ⟨hKeq, ⟨e⟩⟩ := h125b G t L S z K1 K2 E hctx
  have hKcard : Nat.card ↥(autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G))
      (secV t S L E)) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, sec127_card_alt5_type]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h2]
  have hKX : autIn X (secV t S L E) ≤
      autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E) :=
    sec127_autIn_mono (le_inf hXN hXt)
  have hKt : betaOf (secV t S L E) t ∈
      autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E) :=
    sec127_mem_autIn_iff.mpr ⟨t,
      Subgroup.mem_inf.mpr ⟨htN, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, htN, rfl⟩
  have hKcomm : ∀ y ∈ autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E),
      betaOf (secV t S L E) t * y = y * betaOf (secV t S L E) t := by
    intro y hy
    have h1 : y ∈ secNb (secV t S L E) ⊓ Subgroup.centralizer {betaOf (secV t S L E) t} := by
      rw [hKeq]
      exact hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp h1.2).symm
  have hA5' : Nonempty (↥(autIn X (secV t S L E)) ≃* ↥(alternatingGroup (Fin 5))) := by
    obtain ⟨eX⟩ := sec128_autIn_equiv hXN hbot
    obtain ⟨eA⟩ := hA5
    exact ⟨eX.symm.trans eA⟩
  have hinv : Sec128Inv (secV t S L E) (secNb (secV t S L E)) (autIn X (secV t S L E))
      (betaOf (secV t S L E) t) :=
    { xy := sec127_autIn_mono hXN
      ty := sec127_mem_secNb_iff.mpr ⟨t, htN, rfl⟩
      sq := hτ2
      ne := ht1
      a5 := hA5'
      tx := sec127_betaOf_not_mem hA5 hXN hbot hXt htN ht1
      comm := fun x hx => hKcomm x (hKX hx)
      cases := fun y hy hyc => by
        have hyK : y ∈ secNb (secV t S L E) ⊓
            Subgroup.centralizer {betaOf (secV t S L E) t} :=
          ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyc⟩
        rw [hKeq] at hyK
        exact sec127_cases_K hA5 hXN hbot hXt htN ht1 hKX hKcard hKt hKcomm hyK
      cent := ⟨(MulEquiv.subgroupCongr hKeq).trans e⟩
      fus := h127 G t L S z K1 K2 E X hctx hX }
  have hD := sec128_cent_two_nat hV8 hsup hinf hc1 hc2
  have hfix := sec128_natfix hV8.1 hsup hinf hXN hc1 hc2
  have hKY := isKGroupCat_secNb hctx.simple hKP hV8
  rcases sec128_dichotomy_of_z2a5K hZ hV8 hinv hKY hD hfix
      (fun Z hXZ => hn34 G (secV t S L E) X V1 V2 Z hV8 hsup hinf hA5 hnat1 hnat2 hXZ)
      (fun Z hXZ => hn216 G (secV t S L E) X V1 V2 Z hV8 hsup hinf hA5 hnat1 hnat2 hXZ)
      (fun Z hXZ hZe => hdich G (secV t S L E) X V1 V2 Z hV8 hsup hinf hA5 hnat1 hnat2 hXZ hZe)
    with ⟨hWrNat, hWrAct⟩ | hAlt2
  · left
    have hC := h125a G t L S z K1 K2 E hctx
    obtain ⟨K, hKN, hKO, hKV, hKsup⟩ := hsplit G (secV t S L E) hV8 hC hWrNat
    exact sec128_wreath_recognition (secV t S L E) hV8 hC hWrAct hKN hKO hKV hKsup
      (sec128_D_data hp hctx hX hA5)
  · right
    exact hAlt2

theorem asc82Lemma128_of_K (h : Asc82Lemma128K) : Asc82Lemma128 :=
  fun G _ _ t L S z K1 K2 E X hctx hX => h G t L S z K1 K2 E X hctx.kProper hctx hX

end CFSG.OddStandard.SmallF3.Omega
