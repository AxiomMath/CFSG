module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.BProg.B3.S3L3Defs
public import CFSG.GH74.Generic.S45.GLevel1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.C3.Layer1 CFSG.ComponentClassification
open scoped commutatorElement

namespace S3Sec29C

variable {G : Type} [Group G] [Finite G]

section Mu

variable {x y : G} {K A B Q D J : Subgroup G}

theorem piC_eq_one_iff {u : G} {M Λ : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hlam : PumpCalc.IsLam x u K Λ) (hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M)
    (hbar : PumpCalc.bar u Λ = PumpCalc.bar u M) (e : kBar M ≃* kBar K) {a : G} (ha : a ∈ Λ) :
    piC x a = 1 ↔ piC u a = 1 := by
  have hΛK : Λ ≤ K := hlam.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hlam.le.trans inf_le_right
  have hax : a ∈ centralizer ({x} : Set G) := hK.1 (hΛK ha)
  have hau : a ∈ centralizer ({u} : Set G) := hΛY ha
  have hsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hK).2.1
      Subgroup.IsSubnormal.top
  have hx1 : piC x a = 1 ↔ a ∈ pPrimeCoreOf 2 K := by
    rw [piC_of_mem x hax]
    constructor
    · intro h1
      exact TwoThin.mem_pPrimeCoreOf_of_barMk_eq_one hK.1 hsub (hΛK ha) hax h1
    · intro h1
      exact PumpCalc.barMk_eq_one_of_mem_pPrimeCoreOf hK.1 hsub h1 hax
  obtain ⟨φ, hφs, -, hφρ⟩ := TwoThin.exists_phi hΛK hΛY hlam.cover
  have hcard : Nat.card ↥(PumpCalc.bar u Λ) = Nat.card (kBar K) := by
    obtain ⟨e1⟩ := PumpCalc.kBar_equiv_bar hMc
    rw [hbar, ← Nat.card_congr e1.toEquiv]
    exact Nat.card_congr e.toEquiv
  have hφb : Function.Bijective φ := (Nat.bijective_iff_surjective_and_card φ).2 ⟨hφs, hcard⟩
  have hu1 : piC u a = 1 ↔ a ∈ pPrimeCoreOf 2 K := by
    rw [piC_of_mem u hau, ← TwoThin.hatMap_eq_one_iff hΛK ⟨a, ha⟩, ← hφρ a ha]
    constructor
    · intro h1
      have : (⟨TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, hau⟩,
          ⟨⟨a, hΛY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩⟩ : ↥(PumpCalc.bar u Λ)) = 1 :=
        Subtype.ext h1
      rw [this, map_one]
    · intro h1
      have := hφb.1 (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
  rw [hx1, hu1]

omit [Finite G] in
theorem exists_equiv_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hker : f.ker = g.ker) :
    ∃ Ξ : B ≃* C, ∀ a, Ξ (f a) = g a := by
  let e1 := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e2 := QuotientGroup.quotientKerEquivOfSurjective g hg
  let e3 : A ⧸ f.ker ≃* A ⧸ g.ker := QuotientGroup.quotientMulEquivOfEq hker
  refine ⟨e1.symm.trans (e3.trans e2), fun a => ?_⟩
  have h1 : e1.symm (f a) = (a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show e2 (e3 (e1.symm (f a))) = g a
  rw [h1]
  rfl

@[expose] noncomputable def alphaHom (v : G) {Λ M : Subgroup G} (hΛC : Λ ≤ centralizer ({v} : Set G))
    (hmem : ∀ a : ↥Λ, proj v (Subgroup.inclusion hΛC a) ∈ S3.imgBar v M) :
    ↥Λ →* ↥(S3.imgBar v M) :=
  ((proj v).comp (Subgroup.inclusion hΛC)).codRestrict (S3.imgBar v M) hmem

omit [Finite G] in
theorem alphaHom_coe (v : G) {Λ M : Subgroup G} (hΛC : Λ ≤ centralizer ({v} : Set G))
    (hmem : ∀ a : ↥Λ, proj v (Subgroup.inclusion hΛC a) ∈ S3.imgBar v M) (a : ↥Λ) :
    ((alphaHom v hΛC hmem a : ↥(S3.imgBar v M)) : CentralizerBar v) = piC v (a : G) := by
  rw [piC_of_mem v (hΛC a.2)]
  rfl

theorem exists_Xi {u : G} {M Λ : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hlam : PumpCalc.IsLam x u K Λ) (hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M)
    (hbar : PumpCalc.bar u Λ = PumpCalc.bar u M) (e : kBar M ≃* kBar K) :
    ∃ Ξ : ↥(S3.imgBar x K) ≃* ↥(S3.imgBar u M), ∀ (c : ↥(S3.imgBar x K)) (a : G), a ∈ Λ →
      (c : CentralizerBar x) = piC x a → ((Ξ c : ↥(S3.imgBar u M)) : CentralizerBar u) = piC u a := by
  have hΛK : Λ ≤ K := hlam.le.trans inf_le_left
  have hΛCu : Λ ≤ centralizer ({u} : Set G) := hlam.le.trans inf_le_right
  have hΛCx : Λ ≤ centralizer ({x} : Set G) := hΛK.trans hK.1
  have hsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hK).2.1
      Subgroup.IsSubnormal.top
  have hmx : ∀ a : ↥Λ, proj x (Subgroup.inclusion hΛCx a) ∈ S3.imgBar x K := fun a =>
    S3.mem_imgBar.2 ⟨Subgroup.inclusion hΛCx a, hΛK a.2, rfl⟩
  have hmu : ∀ a : ↥Λ, proj u (Subgroup.inclusion hΛCu a) ∈ S3.imgBar u M := by
    intro a
    have h1 : proj u (Subgroup.inclusion hΛCu a) ∈ PumpCalc.bar u Λ :=
      ⟨Subgroup.inclusion hΛCu a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
    rw [hbar] at h1
    exact h1
  set αx := alphaHom x hΛCx hmx with hαx
  set αu := alphaHom u hΛCu hmu with hαu
  have hsx : Function.Surjective αx := by
    rintro ⟨c, hc⟩
    obtain ⟨g, hgK, rfl⟩ := S3.mem_imgBar.1 hc
    obtain ⟨l, hl, o, ho, hlo⟩ := hlam.cover (g : G) hgK
    have hlC : l ∈ centralizer ({x} : Set G) := hΛCx hl
    have hoC : o ∈ centralizer ({x} : Set G) := hK.1 (TwoThin.pPrimeCoreOf_le K ho)
    have ho1 : piC x o = 1 := by
      rw [piC_of_mem x hoC]
      exact PumpCalc.barMk_eq_one_of_mem_pPrimeCoreOf hK.1 hsub ho hoC
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    rw [alphaHom_coe]
    show piC x l = proj x g
    have hg' : proj x g = piC x (g : G) := (piC_of_mem x g.2).symm
    have : piC x (g : G) = piC x l * piC x o := by
      rw [hlo, piC_mul x hlC hoC]
    rw [hg', this, ho1, mul_one]
  have hsu : Function.Surjective αu := by
    rintro ⟨c, hc⟩
    have h1 : c ∈ PumpCalc.bar u Λ := by
      rw [hbar]
      exact hc
    obtain ⟨m, hm, hmc⟩ := h1
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    refine ⟨⟨(m : G), hmΛ⟩, Subtype.ext ?_⟩
    rw [alphaHom_coe, piC_of_mem u m.2]
    exact hmc
  have hker : αx.ker = αu.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : αx a = 1 ↔ piC x (a : G) = 1 := by
      rw [← Subtype.coe_inj, alphaHom_coe]
      rfl
    have h2 : αu a = 1 ↔ piC u (a : G) = 1 := by
      rw [← Subtype.coe_inj, alphaHom_coe]
      rfl
    rw [h1, h2]
    exact piC_eq_one_iff hK hlam hMc hbar e a.2
  obtain ⟨Ξ, hΞ⟩ := exists_equiv_of_ker_eq αx αu hsx hsu hker
  refine ⟨Ξ, fun c a ha hca => ?_⟩
  have hc : αx ⟨a, ha⟩ = c := Subtype.ext (by rw [alphaHom_coe]; exact hca.symm)
  rw [← hc, hΞ, alphaHom_coe]

theorem qShape3_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3 A) :
    QShape3 B := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  refine ⟨p, f, hp, hp2, hq, ?_⟩
  rcases h with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)

end Mu

end S3Sec29C

end CFSG.GH74.Generic.BProg.B3
