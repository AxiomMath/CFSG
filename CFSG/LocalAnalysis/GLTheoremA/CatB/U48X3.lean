module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row49

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.Row49
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 fieldSU4 fieldFactor4
  mem_range_conj_of_fieldFactor4_eq_one)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 (factorization_three_25920)



theorem sylow_central_conj {α : MulAut SU4} (hα3 : α ^ 3 = 1) (hα1 : fieldFactor4 α ≠ 1)
    (hcard : Nat.card (fixSub α) = 25920) {S : Subgroup SU4} (hSF : S ≤ fixSub α)
    (hS : Nat.card S = 81) {z : SU4} (hzS : z ∈ S) (hzc : ∀ q ∈ S, q * z = z * q) :
    ∃ (g : SU4) (a : ZMod 9), g * z * g⁻¹ = tau4 (.ofAdd fun _ => a) ∧
      ∀ x ∈ fixSub (fieldSU4 (fieldFactor4 α)), g⁻¹ * x * g ∈ fixSub α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh⟩ := exists_conj_fieldSU4 hα3 hα1
  have hφ3 : fieldFactor4 α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  set F := fixSub α with hF
  set R : Subgroup SU4 := R₃.map (MulAut.conj h).toMonoidHom with hR
  have hRF : R ≤ F := by
    rintro _ ⟨r, hr, rfl⟩
    show α (h * r * h⁻¹) = h * r * h⁻¹
    rw [hh r, show fieldSU4 (fieldFactor4 α) r = r from R₃_le_fixSub hφ3 hr]
  have h81 : (3 : ℕ) ^ (Nat.card F).factorization 3 = 81 := by
    rw [hcard, factorization_three_25920]; norm_num
  let SR : Sylow 3 ↥F := Sylow.ofCard (R.subgroupOf F) (by
    rw [h81, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj h).injective, card_R₃])
  let SS : Sylow 3 ↥F := Sylow.ofCard (S.subgroupOf F)
    (by rw [h81, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv, hS])
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq ↥F SS SR
  have hSR : (SR : Subgroup ↥F) = R.subgroupOf F := rfl
  have hSS : (SS : Subgroup ↥F) = S.subgroupOf F := rfl
  have key : ∀ x : ↥F, x ∈ R.subgroupOf F ↔ f⁻¹ * x * f ∈ S.subgroupOf F := by
    intro x
    rw [← hSR, ← hSS, ← hf, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj f)⁻¹ • x = f⁻¹ * x * f := by simp [MulAut.smul_def, mul_assoc]
    rw [this]
  set g : SU4 := h⁻¹ * (f : SU4) with hg
  have hz' : g * z * g⁻¹ ∈ R₃ := by
    have h1 := (key (f * ⟨z, hSF hzS⟩ * f⁻¹)).2 (by
      rw [show f⁻¹ * (f * (⟨z, hSF hzS⟩ : ↥F) * f⁻¹) * f = ⟨z, hSF hzS⟩ by group]
      exact Subgroup.mem_subgroupOf.2 hzS)
    obtain ⟨r, hr, hrz⟩ := Subgroup.mem_subgroupOf.1 h1
    have : g * z * g⁻¹ = r := by
      have h2 : h * r * h⁻¹ = (f : SU4) * z * (f : SU4)⁻¹ := hrz
      rw [hg]
      calc h⁻¹ * (f : SU4) * z * (h⁻¹ * (f : SU4))⁻¹
          = h⁻¹ * ((f : SU4) * z * (f : SU4)⁻¹) * h := by group
        _ = r := by rw [← h2]; group
    rwa [this]
  have hc' : ∀ q ∈ R₃, q * (g * z * g⁻¹) = (g * z * g⁻¹) * q := by
    intro q hq
    have hqR : h * q * h⁻¹ ∈ R := ⟨q, hq, rfl⟩
    have h1 := (key ⟨_, hRF hqR⟩).1 (Subgroup.mem_subgroupOf.2 hqR)
    have h3 := hzc _ (Subgroup.mem_subgroupOf.1 h1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc q * (g * z * g⁻¹) = g * (((f : SU4)⁻¹ * (h * q * h⁻¹) * f) * z) * g⁻¹ := by rw [hg]; group
      _ = g * (z * ((f : SU4)⁻¹ * (h * q * h⁻¹) * f)) * g⁻¹ := by rw [h3]
      _ = (g * z * g⁻¹) * q := by rw [hg]; group
  obtain ⟨a, ha⟩ := central_R₃ hz' hc'
  refine ⟨g, a, ha, fun x hx => ?_⟩
  have hx' : α (h * x * h⁻¹) = h * x * h⁻¹ := by
    rw [hh x, mem_fixSub.1 hx]
  have hfF : α (f : SU4) = (f : SU4) := mem_fixSub.1 f.2
  have hgx : g⁻¹ * x * g = (f : SU4)⁻¹ * (h * x * h⁻¹) * (f : SU4) := by
    rw [hg]; group
  rw [hgx, mem_fixSub, map_mul, map_mul, map_inv, hfF, hx']


theorem ipart_fix_model {G : Type} [Group G] [Finite G] (X L : Subgroup G) (b : G)
    (hL : GLAPComponent 3 X L) (hcat : catalogIs (PSimple 3 L) S9.isU4eight)
    (hFO : FieldOn 3 b L) (hb3 : b ^ 3 = 1) (I : Subgroup G) (hI : I = Ipart 3 L b) :
    ∃ γ : MulAut SU4, γ ^ 3 = 1 ∧ fieldFactor4 γ ≠ 1 ∧ Nat.card (fixSub γ) = 25920 ∧
      ∃ ψ : ↥I →* ↥(fixSub γ), Function.Surjective ψ ∧ ¬ 3 ∣ Nat.card ψ.ker ∧ I ≤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hFO.1
  have hZ := center_pquot_eq_bot_of_u48 hL hcat
  let e := pqModelP hZ hcat
  let γ : MulAut SU4 := MulAut.congr e (barAut L b hb)
  have hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L b hb q) := by
    intro q
    change (MulAut.congr e (barAut L b hb)) (e q) = _
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hγ3 : γ ^ 3 = 1 := by
    have h : (MulAut.congr e) (barAut L b hb ^ 3) = 1 := by
      rw [barAut_pow_three L b hb hb3, map_one]
    rwa [map_pow] at h
  let τ : PSimple 3 L ≃* SU4 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  obtain ⟨-, hγ1⟩ := dict_outer hcat hFO τ γ (fun q => hγ q)
  have hff : fieldFactor4 γ ≠ 1 := fun h => hγ1 (mem_range_conj_of_fieldFactor4_eq_one h)
  obtain ⟨hcatF, hcardF⟩ := catalogIs_fixSub hγ3 hff
  set F : Subgroup SU4 := fixSub γ with hFdef
  set Y : Subgroup G := L ⊓ Subgroup.centralizer ({b} : Set G) with hY
  have hYL : Y ≤ L := inf_le_left
  have hπF : ∀ x : ↥Y, (piOf L e) (Subgroup.inclusion hYL x) ∈ F := fun x =>
    gamma_fixed_of_mem hb e γ hγ (Subgroup.inclusion hYL x) x.2.2
  have hsurj : ∀ c ∈ F, ∃ x : ↥Y, (piOf L e) (Subgroup.inclusion hYL x) = c := by
    intro c hc
    obtain ⟨x, rfl⟩ := piOf_surjective L e c
    have hfix : (QuotientGroup.mk (conjL L b hb x) : PQuot 3 L) = QuotientGroup.mk x := by
      have h2 : γ (e (QuotientGroup.mk x)) = e (QuotientGroup.mk x) := hc
      rw [hγ, barAut_mk] at h2
      exact e.injective h2
    obtain ⟨x', hx'c, hx'mk⟩ := exists_cent_lift_outer hb hb3 x hfix
    refine ⟨⟨(x' : G), x'.2, Subgroup.mem_centralizer_singleton_iff.2 hx'c⟩, ?_⟩
    change e (QuotientGroup.mk x') = e (QuotientGroup.mk x)
    rw [hx'mk]
  let ψ : ↥Y →* ↥F := restrictTo (piOf L e) F hYL hπF
  have hψs : Function.Surjective ψ := restrictTo_surjective (piOf L e) F hYL hπF hsurj
  have hψk : ¬ 3 ∣ Nat.card ψ.ker :=
    restrictTo_ker (piOf L e) F hYL hπF (not_three_dvd_card_ker_piOf e)
  have hcardF' : Nat.card ↥F = 25920 := hcardF
  haveI hsimp : IsSimpleGroup ↥F := isSimple_of_u4two hcatF
  have hC : GLAPPrimeCore 3 ↥F = ⊥ := pPrimeCore_eq_bot_of_simple (by rw [hcardF']; norm_num)
  have hS : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥F) := by
    haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥F) := Subgroup.topEquiv.isSimpleGroup
    refine isQuasisimple_of_simple_nonabelian ?_
    intro hcomm
    have hp := (@Group.is_simple_iff_prime_card ↥(⊤ : Subgroup ↥F) _ hcomm).1 inferInstance
    rw [Subgroup.card_top, hcardF'] at hp
    norm_num at hp
  obtain ⟨J, hJ, hJl, himg, -⟩ := layer_of_surj ψ hψs hψk hC ⊤ hS (fun T _ => le_top)
  have hJY : J ≤ Y := hJ.1
  have hJL : J ≤ L := hJY.trans hYL
  let ψJ : ↥J →* ↥F := ψ.comp (Subgroup.inclusion hJY)
  have hψJs : Function.Surjective ψJ := by
    intro c
    have hc : c ∈ (J.subgroupOf Y).map ψ := by rw [himg]; exact Subgroup.mem_top c
    obtain ⟨x, hx, rfl⟩ := hc
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  have hψJk : ¬ 3 ∣ Nat.card ψJ.ker := by
    intro h3
    apply hψk
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective (K := ψJ.ker) (Subgroup.inclusion_injective hJY)]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hIJ : I = J := hI.trans hJl
  subst hIJ
  exact ⟨γ, hγ3, hff, hcardF', ψJ, hψJs, hψJk, hJL⟩

theorem ipart_central_conj {G : Type} [Group G] [Finite G] {I : Subgroup G} {γ : MulAut SU4}
    (hγ3 : γ ^ 3 = 1) (hff : fieldFactor4 γ ≠ 1) (hcardF : Nat.card (fixSub γ) = 25920)
    (ψ : ↥I →* ↥(fixSub γ)) (hψs : Function.Surjective ψ) (hψk : ¬ 3 ∣ Nat.card ψ.ker)
    {y : G} (hyI : y ∈ I) (hyc : IsCentralIn 3 y I) :
    ∃ (g : SU4) (a : ZMod 9), g * ((ψ ⟨y, hyI⟩ : ↥(fixSub γ)) : SU4) * g⁻¹ =
        tau4 (.ofAdd fun _ => a) ∧
      ∀ x ∈ fixSub (fieldSU4 (fieldFactor4 γ)), g⁻¹ * x * g ∈ fixSub γ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, P, hPI, hP3, hyP, hPc, hPmax⟩ := hyc
  obtain ⟨S, hSdef⟩ := sylow_image hPI hP3 hPmax ψ hψs hψk
  set S' : Subgroup SU4 := (S : Subgroup ↥(fixSub γ)).map (fixSub γ).subtype with hS'
  have hS'F : S' ≤ fixSub γ := Subgroup.map_subtype_le _
  have hS'card : Nat.card S' = 81 := by
    rw [hS', Subgroup.card_map_of_injective (fixSub γ).subtype_injective, Sylow.card_eq_multiplicity S,
      hcardF, factorization_three_25920]
    norm_num
  let yI : ↥I := ⟨y, hyI⟩
  have hyJP : yI ∈ P.subgroupOf I := Subgroup.mem_subgroupOf.2 hyP
  have hzS : ((ψ yI : ↥(fixSub γ)) : SU4) ∈ S' := ⟨ψ yI, by rw [hSdef]; exact ⟨yI, hyJP, rfl⟩, rfl⟩
  have hzc : ∀ q ∈ S', q * ((ψ yI : ↥(fixSub γ)) : SU4) = ((ψ yI : ↥(fixSub γ)) : SU4) * q := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hSdef] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpy : (p : G) * y = y * (p : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPc (Subgroup.mem_subgroupOf.1 hp))
    have h2 := congrArg (fun x : ↥I => ((ψ x : ↥(fixSub γ)) : SU4)) (Subtype.ext hpy : p * yI = yI * p)
    simpa [map_mul] using h2
  exact sylow_central_conj hγ3 hff hcardF hS'F hS'card hzS hzc

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X3
