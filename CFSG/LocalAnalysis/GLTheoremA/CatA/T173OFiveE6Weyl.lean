module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173

variable {Ω : Type} [Group Ω] {S B N D K : Subgroup Ω} {x : Ω}

private theorem commute_of_mem_B_of_mem_center_map [Finite Ω] (hcfg : Cfg173 3 S B N D K x)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) {a z : Ω} (ha : a ∈ B)
    (hz : z ∈ (Subgroup.center ↥S).map S.subtype) : a * z = z * a := by
  haveI : S.Normal := hcfg.normal
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hZScard : Nat.card ((Subgroup.center ↥S).map S.subtype) ∣ 3 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hZ
  rcases (Nat.dvd_prime Nat.prime_three).1 hZScard with h1 | h3
  · rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hz
    rw [hz]
    simp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥((Subgroup.center ↥S).map S.subtype) := isCyclic_of_prime_card h3
  have hcardAut : Nat.card (MulAut ↥((Subgroup.center ↥S).map S.subtype)) = 2 := by
    rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]
  haveI : (Subgroup.center ↥S).Characteristic := Subgroup.centerCharacteristic
  have hBZ : B ≤ Subgroup.normalizer
      ((Subgroup.center ↥S).map S.subtype : Set Ω) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (Subgroup.center ↥S))
  let σ : MulAut ↥((Subgroup.center ↥S).map S.subtype) :=
    (Subgroup.normalizerMonoidHom _) (Subgroup.inclusion hBZ ⟨a, ha⟩)
  have hb3 : (⟨a, ha⟩ : ↥B) ^ 3 = 1 := by
    refine Subtype.ext ?_
    exact hcfg.elem.2 a ha
  have hσ3 : σ ^ 3 = 1 := by
    show ((Subgroup.normalizerMonoidHom _) (Subgroup.inclusion hBZ ⟨a, ha⟩)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hb3, map_one, map_one]
  have hdvd3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
  have hdvd2 : orderOf σ ∣ 2 := hcardAut ▸ orderOf_dvd_natCard σ
  have hone : σ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) hdvd3 hdvd2)
  have hσz : σ ⟨z, hz⟩ = ⟨z, hz⟩ := by simpa using DFunLike.congr_fun hone ⟨z, hz⟩
  have hcoe : ((σ ⟨z, hz⟩ : ↥((Subgroup.center ↥S).map S.subtype)) : Ω)
      = a * z * a⁻¹ := by
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe
      ((Subgroup.center ↥S).map S.subtype) (Subgroup.inclusion hBZ ⟨a, ha⟩) ⟨z, hz⟩
    simp only [Subgroup.coe_inclusion] at h
    simpa [σ] using h
  calc a * z = (a * z * a⁻¹) * a := by group
    _ = z * a := by rw [← hcoe, hσz]

private theorem center_map_le_B [Finite Ω] (hcfg : Cfg173 3 S B N D K x)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) :
    (Subgroup.center ↥S).map S.subtype ≤ B := by
  have hZScard : Nat.card ((Subgroup.center ↥S).map S.subtype) ∣ 3 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hZ
  rcases (Nat.dvd_prime Nat.prime_three).1 hZScard with h1 | h3
  · rw [Subgroup.card_eq_one.mp h1]
    exact bot_le
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥((Subgroup.center ↥S).map S.subtype) := isCyclic_of_prime_card h3
  have hZSel : IsElemAbelian 3 ((Subgroup.center ↥S).map S.subtype) := by
    haveI : CommGroup ↥((Subgroup.center ↥S).map S.subtype) := IsCyclic.commGroup
    refine ⟨inferInstance, fun z hz => ?_⟩
    have hd : orderOf z ∣ 3 := by
      rw [← h3]
      exact Subgroup.orderOf_dvd_natCard _ hz
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hEel : IsElemAbelian 3 (B ⊔ (Subgroup.center ↥S).map S.subtype) :=
    hcfg.elem.sup_of_commute hZSel
      (fun a ha z hz => commute_of_mem_B_of_mem_center_map hcfg hZ ha hz)
  obtain ⟨T, hTS, hT2, hBT, hTne⟩ := hcfg.hb
  have hT : T ≠ ⊥ := by
    rintro rfl
    exact hTne (Subgroup.commutator_bot_left B)
  have hZT : (Subgroup.center ↥S).map S.subtype ≤ Subgroup.normalizer (T : Set Ω) := by
    intro z hz
    obtain ⟨hzS, hcz⟩ := (CFSG.LocalCores.mem_map_center_iff S).mp hz
    have hEq : ∀ t ∈ S, z * t * z⁻¹ = t := by
      intro t ht
      have hct : z * t = t * z :=
        (Subgroup.mem_centralizer_iff.mp hcz t ht).symm
      rw [hct]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [hEq t (hTS ht)]
      exact ht
    · intro ht
      have htS : t ∈ S := by
        have he : t = z⁻¹ * (z * t * z⁻¹) * z := by group
        rw [he]
        exact S.mul_mem (S.mul_mem (S.inv_mem hzS) (hTS ht)) hzS
      rwa [hEq t htS] at ht
  have hEq : B ⊔ (Subgroup.center ↥S).map S.subtype = B :=
    GLAIsBmax.eq_of_le hcfg.prime hcfg.bmax le_sup_left hEel hT hT2 (sup_le hBT hZT)
  rw [← hEq]
  exact le_sup_right

section E6


variable [Finite Ω] {F : Type} [Field F] [Finite F]

private theorem pi_conj_WSL (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (ψ : Fin Tag.E6.rank → (Matrix.SpecialLinearGroup (Fin 2) F →* ↥S))
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    {b : ↥B} {c : Fin Tag.E6.rank → Fˣ}
    (hcβ : ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) = rootDiagUnit Tag.E6 c)
    (i : Fin Tag.E6.rank) {bs : ↥S}
    (hbscoe : (bs : Ω) = (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹) :
    ((M.π bs : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      torusElt Tag.E6 F i (c i) * weylElt Tag.E6 F i 1 := by
  have hβinv : ((M.β b⁻¹ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ := by
    rw [map_inv]
    rfl
  have hconj : ((M.π bs : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = ((M.β b⁻¹ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹
        * ((M.π (ψ i WSL) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * ((M.β b⁻¹ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) :=
    M.conj b⁻¹ (ψ i WSL) bs (by rw [hbscoe, Subgroup.coe_inv]; group)
  rw [hconj, hβinv, hcβ, hψ i WSL, simpleRootSL2_WSL,
    show ((rootDiagUnit Tag.E6 c)⁻¹)⁻¹ = rootDiagUnit Tag.E6 c from rfl,
    rootDiagUnit_conj_weylElt_one c i]

private theorem pi_commutator_eq_torus (M : S172DModel S B (adjointGroup Tag.E6 F)
      (hatGroup Tag.E6 F))
    (ψ : Fin Tag.E6.rank → (Matrix.SpecialLinearGroup (Fin 2) F →* ↥S))
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    {b : ↥B} {c : Fin Tag.E6.rank → Fˣ}
    (hcβ : ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) = rootDiagUnit Tag.E6 c)
    (i : Fin Tag.E6.rank) {bs t : ↥S}
    (hbscoe : (bs : Ω) = (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹)
    (ht : (t : Ω) = (bs : Ω) * (((ψ i WSL : ↥S) : Ω))⁻¹) :
    ((M.π t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = torusElt Tag.E6 F i (c i) := by
  have hbsπ := pi_conj_WSL M ψ hψ hcβ i hbscoe
  have ht' : t = bs * (ψ i WSL)⁻¹ := Subtype.ext (by simpa using ht)
  have h1 : M.π t = M.π bs * (M.π (ψ i WSL))⁻¹ := by
    rw [ht', map_mul, map_inv]
  have h2 : ((M.π t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = ((M.π bs : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * ((M.π (ψ i WSL) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ := by
    rw [h1]
    rfl
  rw [h2, hbsπ, hψ i WSL, simpleRootSL2_WSL]
  group

private theorem commutator_WSL_mem_B (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (ψ : Fin Tag.E6.rank → (Matrix.SpecialLinearGroup (Fin 2) F →* ↥S))
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    (hE : ∀ i (g : Matrix.SpecialLinearGroup (Fin 2) F), (∃ γ : Fˣ, γ ^ 3 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) →
      ((ψ i g : ↥S) : Ω) ∈ B)
    (i : Fin Tag.E6.rank) (b : ↥B) :
    (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹ * (((ψ i WSL : ↥S) : Ω))⁻¹ ∈ B := by
  have hZSB : (Subgroup.center ↥S).map S.subtype ≤ B := center_map_le_B hcfg hZ
  haveI : S.Normal := hcfg.normal
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hbβ : ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ M.barB :=
    Subgroup.mem_map_of_mem (hatGroup Tag.E6 F).subtype ⟨b, rfl⟩
  obtain ⟨c, hc3, hcβ⟩ := hdiag _ hbβ
  have hmemS : (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hBN b.2) _).mp (ψ i WSL).2
  set bs : ↥S := ⟨(b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹, hmemS⟩ with hbs
  have hbscoe : (bs : Ω) = (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹ := rfl
  set t₁ : ↥S := bs * (ψ i WSL)⁻¹ with ht₁
  have ht₁coe : (t₁ : Ω) = (bs : Ω) * (((ψ i WSL : ↥S) : Ω))⁻¹ := rfl
  have ht₁π : ((M.π t₁ : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = torusElt Tag.E6 F i (c i) :=
    pi_commutator_eq_torus M ψ hψ hcβ i hbscoe ht₁coe
  have hHSL : ((HSL (c i) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = Matrix.diagonal ![(c i : F), (((c i)⁻¹ : Fˣ) : F)] := by
    rw [coe_HSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal]
  have hgB : ((ψ i (HSL (c i)) : ↥S) : Ω) ∈ B := hE i (HSL (c i)) ⟨c i, hc3 i, hHSL⟩
  have hψπ : ((M.π (ψ i (HSL (c i))) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      torusElt Tag.E6 F i (c i) := by
    rw [hψ i (HSL (c i)), simpleRootSL2_HSL]
  have hker : M.π t₁ = M.π (ψ i (HSL (c i))) := by
    refine Subtype.ext ?_
    rw [ht₁π, hψπ]
  have hcenter : t₁ * (ψ i (HSL (c i)))⁻¹ ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, hker, mul_inv_cancel]
  have hcenterB : ((t₁ * (ψ i (HSL (c i)))⁻¹ : ↥S) : Ω) ∈ B :=
    hZSB (Subgroup.mem_map_of_mem S.subtype hcenter)
  have heq : (t₁ : Ω) = ((t₁ * (ψ i (HSL (c i)))⁻¹ : ↥S) : Ω)
      * ((ψ i (HSL (c i)) : ↥S) : Ω) := by
    rw [← Subgroup.coe_mul]
    congr 1
    group
  rw [← ht₁coe, heq]
  exact B.mul_mem hcenterB hgB

theorem weylElt_mem_piImg_N (hcfg : Cfg173 3 S B N D K x)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (ψ : Fin Tag.E6.rank → (Matrix.SpecialLinearGroup (Fin 2) F →* ↥S))
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    (hE : ∀ i (g : Matrix.SpecialLinearGroup (Fin 2) F), (∃ γ : Fˣ, γ ^ 3 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) →
      ((ψ i g : ↥S) : Ω) ∈ B)
    (i : Fin Tag.E6.rank) :
    weylElt Tag.E6 F i 1 ∈ M.piImg N := by
  have hsN : ((ψ i WSL : ↥S) : Ω) ∈ N := by
    have hxS : x ∈ Subgroup.centralizer (S : Set Ω) :=
      (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers x)
    rw [hcfg.hN, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hle : B.map (MulAut.conj ((ψ i WSL : ↥S) : Ω)).toMonoidHom ≤ B := by
        rintro y ⟨b, hb, rfl⟩
        change (MulAut.conj ((ψ i WSL : ↥S) : Ω)) (b : Ω) ∈ B
        rw [MulAut.conj_apply]
        have hx : (b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹
            * (((ψ i WSL : ↥S) : Ω))⁻¹ ∈ B :=
          commutator_WSL_mem_B hcfg M hZ ψ hψ hdiag hE i ⟨b, hb⟩
        have he : ((ψ i WSL : ↥S) : Ω) * (b : Ω) * (((ψ i WSL : ↥S) : Ω))⁻¹
            = ((b : Ω) * ((ψ i WSL : ↥S) : Ω) * (b : Ω)⁻¹
              * (((ψ i WSL : ↥S) : Ω))⁻¹)⁻¹ * (b : Ω) := by
          group
        rw [he]
        exact B.mul_mem (B.inv_mem hx) hb
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj _).injective).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxS (((ψ i WSL : ↥S)) : Ω) (ψ i WSL).2
  rw [S172DModel.piImg]
  refine Subgroup.mem_map.mpr ⟨M.π (ψ i WSL), ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.mpr hsN)
  · simpa using (hψ i WSL).trans (simpleRootSL2_WSL i)

end E6

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
