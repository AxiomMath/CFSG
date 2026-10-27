module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafBal
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue74
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Residual

theorem oPrimeResidual_normal_two (X : Type*) [Group X] : (oPrimeResidual 2 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : (oPrimeResidual 2 X).map (MulAut.conj g).toMonoidHom ≤ oPrimeResidual 2 X := by
    unfold oPrimeResidual
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    refine ⟨k, ?_⟩
    show (g * x * g⁻¹) ^ (2 ^ k) = 1
    rw [conj_pow, hk]; simp
  exact hle ⟨n, hn, rfl⟩

theorem exists_two_lift {X Y : Type*} [Group X] [Finite X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) {a : Y} {k : ℕ} (ha : a ^ (2 ^ k) = 1) :
    ∃ c : X, f c = a ∧ ∃ j : ℕ, c ^ (2 ^ j) = 1 := by
  obtain ⟨c, rfl⟩ := hf a
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : f c = 1 := by simpa using ha
    exact ⟨1, by rw [map_one]; exact this.symm, 0, by simp⟩
  have hm : c ^ (2 ^ k) ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow]; exact ha
  have h1 : (c ^ (2 ^ k)) ^ Nat.card f.ker = 1 := by
    have : (⟨c ^ (2 ^ k), hm⟩ : ↥f.ker) ^ Nat.card f.ker = 1 := pow_card_eq_one'
    simpa using congrArg Subtype.val this
  have hcop : Nat.Coprime (Nat.card f.ker) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hk2 : 1 < 2 ^ k := Nat.one_lt_two_pow hk.ne'
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk2
  refine ⟨c ^ (Nat.card f.ker * j), ?_, k, ?_⟩
  · have hdiv : ∃ r, Nat.card f.ker * j = 1 + 2 ^ k * r := ⟨Nat.card f.ker * j / 2 ^ k, by
      have := Nat.mod_add_div (Nat.card f.ker * j) (2 ^ k)
      omega⟩
    obtain ⟨r, hr⟩ := hdiv
    rw [map_pow, hr, pow_add, pow_one, pow_mul, ha, one_pow, mul_one]
  · rw [← pow_mul, show Nat.card f.ker * j * 2 ^ k = 2 ^ k * Nat.card f.ker * j by ring, pow_mul, pow_mul, h1]
    simp

end Residual

section Half

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem mk_mem_oPrimeResidual_of_pgroup {C S' : Subgroup G} (hS : IsPGroup 2 ↥S') (hSC : S' ≤ C)
    (N : Subgroup ↥C) [N.Normal] {s : G} (hs : s ∈ S') :
    QuotientGroup.mk' N ⟨s, hSC hs⟩ ∈ oPrimeResidual 2 (↥C ⧸ N) := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨s, hs⟩
  have h1 : (⟨s, hs⟩ : ↥S') ^ (2 ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have h2 : s ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val h1
  refine Subgroup.subset_closure ⟨m, ?_⟩
  rw [← map_pow]
  have : (⟨s, hSC hs⟩ : ↥C) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using h2)
  rw [this, map_one]

theorem Oz_inf_le {K : Subgroup G} (hKC : K ≤ Cz z) : K ⊓ Oz z ≤ pPrimeCoreOf 2 K :=
  le_pPrimeCoreOf' inf_le_left
    (fun _ hx _ hn => ⟨K.mul_mem (K.mul_mem hx hn.1) (K.inv_mem hx), Oz_conj (hKC hx) hn.2⟩)
    (Odd.of_dvd_nat card_Oz_odd (Subgroup.card_dvd_of_le inf_le_right))

theorem K_image_le_oPrimeResidual (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {k : G} (hk : k ∈ K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨k, (h.comp_isPCompIn hK).1 hk⟩ ∈
      oPrimeResidual 2 (CentralizerBar z) := by
  have hM := m4_of_std hII h
  have hKC : K ≤ Cz z := (h.comp_isPCompIn hK).1
  obtain ⟨-, hK2⟩ := TwoThin.isPCompIn_two_iff.1 (h.comp_isPCompIn hK)
  have hcomp := TwoThin.isComponent_map_barMk hK2
  set Kb : Subgroup (CentralizerBar z) :=
    (K.subgroupOf (Cz z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z))) with hKb
  have hQ : IsQuasisimple ↥Kb := hcomp.1
  have hMn : (oPrimeResidual 2 (CentralizerBar z)).Normal := oPrimeResidual_normal_two _
  have hRn : ((oPrimeResidual 2 (CentralizerBar z)).subgroupOf Kb).Normal := inferInstance
  have hmemKb : ∀ y : G, ∀ hy : y ∈ K,
      QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨y, hKC hy⟩ ∈ Kb :=
    fun y hy => Subgroup.mem_map_of_mem _ hy
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hRn with hr | hr
  · have hmem : (⟨_, hmemKb k hk⟩ : ↥Kb) ∈ (oPrimeResidual 2 (CentralizerBar z)).subgroupOf Kb := by
      rw [hr]; exact Subgroup.mem_top _
    exact hmem
  · exfalso
    obtain ⟨hz2, hz8⟩ := hII G h.simple z h.orderOf_z S K h.sylow (h.comp_isPCompIn hK)
      (h.comp_pRank hK)
    have hS2 : IsPGroup 2 ↥S := hM.S_pgroup
    have hSle : S ⊓ K ≤ S ⊓ zStar K := by
      intro s hs
      refine ⟨hs.1, hs.2, ?_⟩
      have hsC : s ∈ Cz z := hKC hs.2
      have hsM : QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨s, hsC⟩ ∈
          oPrimeResidual 2 (CentralizerBar z) :=
        mk_mem_oPrimeResidual_of_pgroup (S' := S) hS2 hM.S_syl.1 _ hs.1
      have hcen : (⟨_, hmemKb s hs.2⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := hr hsM
      have hsN : s ∈ normalizer (K : Set G) := le_normalizer hs.2
      refine ⟨hsN, TwoThin.mem_normalizer_pPrimeCoreOf hsN, fun x hx => ?_⟩
      have hxs : QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨x, hKC hx⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨s, hsC⟩ =
          QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨s, hsC⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨x, hKC hx⟩ := by
        have := Subgroup.mem_center_iff.1 hcen ⟨_, hmemKb x hx⟩
        exact congrArg Subtype.val this
      have hcx : ⁅x, s⁆ ∈ Cz z := by
        simp only [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hKC hx) hsC) (inv_mem (hKC hx))) (inv_mem hsC)
      have hcomm1 : QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨⁅x, s⁆, hcx⟩ = 1 := by
        have e : (⟨⁅x, s⁆, hcx⟩ : ↥(Cz z)) =
            ⁅(⟨x, hKC hx⟩ : ↥(Cz z)), (⟨s, hsC⟩ : ↥(Cz z))⁆ := rfl
        rw [e, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hxs
      have hOz : ⁅x, s⁆ ∈ Oz z := (hatMk_eq_one_iff (Cz z) ⟨⁅x, s⁆, hcx⟩).1 hcomm1
      have hKm : ⁅x, s⁆ ∈ K := by
        simp only [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hx hs.2) (inv_mem hx)) (inv_mem hs.2)
      exact Oz_inf_le hKC ⟨hKm, hOz⟩
    have := Subgroup.card_le_of_le hSle
    omega

theorem N_image_le (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) :
    ((K₁ ⊔ K₂ ⊔ S).subgroupOf (Cz z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z))) ≤
      oPrimeResidual 2 (CentralizerBar z) := by
  have hM := m4_of_std hII h
  have hK₁C : K₁ ≤ Cz z := (h.comp_isPCompIn (Or.inl rfl)).1
  have hK₂C : K₂ ≤ Cz z := (h.comp_isPCompIn (Or.inr rfl)).1
  have hSC : S ≤ Cz z := hM.S_syl.1
  let Mg : Subgroup G :=
    ((oPrimeResidual 2 (CentralizerBar z)).comap
      (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)))).map (Cz z).subtype
  have hMg : ∀ (g : G) (hg : g ∈ Cz z),
      g ∈ Mg → QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨g, hg⟩ ∈
        oPrimeResidual 2 (CentralizerBar z) := by
    rintro g hg ⟨y, hy, hyg⟩
    have : y = ⟨g, hg⟩ := Subtype.ext hyg
    rw [this] at hy
    exact hy
  have hK₁ : K₁ ≤ Mg := fun k hk =>
    ⟨⟨k, hK₁C hk⟩, K_image_le_oPrimeResidual hII h (Or.inl rfl) hk, rfl⟩
  have hK₂ : K₂ ≤ Mg := fun k hk =>
    ⟨⟨k, hK₂C hk⟩, K_image_le_oPrimeResidual hII h (Or.inr rfl) hk, rfl⟩
  have hS : S ≤ Mg := fun s hs =>
    ⟨⟨s, hSC hs⟩, mk_mem_oPrimeResidual_of_pgroup hM.S_pgroup hSC _ hs, rfl⟩
  have hN : K₁ ⊔ K₂ ⊔ S ≤ Mg := sup_le (sup_le hK₁ hK₂) hS
  rintro _ ⟨⟨n, hnC⟩, hn, rfl⟩
  exact hMg n hnC (hN hn)

end Half

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
