module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueSetting
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDL

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

@[expose] def SuzSylowFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Blueprint.NativeSporadic.IsSporadic X .Suz →
    ∀ R : Sylow 2 X, IsElemTwo (zGammaThree (R : Subgroup X)) ∧
      Nat.card (zGammaThree (R : Subgroup X)) = 16 ∧
      ∃ Q : Subgroup X, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        (R : Subgroup X) ⊔ centralizer (Q : Set X) = ⊤

@[expose] def TwoSuzSylowFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → Nat.card (center X) = 2 →
    Blueprint.NativeSporadic.IsSporadic (X ⧸ center X) .Suz →
    ∀ R : Sylow 2 X, IsElemTwo (zGammaThree (R : Subgroup X)) ∧
      Nat.card (zGammaThree (R : Subgroup X)) = 32 ∧
      ∃ Q : Subgroup X, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        (R : Subgroup X) ⊔ centralizer (Q : Set X) = ⊤

theorem map_zGammaThree_of_injOn {G H : Type} [Group G] [Group H] (f : G →* H) {D : Subgroup G}
    (hf : Set.InjOn f D) : (zGammaThree D).map f = zGammaThree (D.map f) := by
  have h3le : ⁅⁅D, D⁆, D⁆ ≤ D :=
    commutator_le_of_le (commutator_le_of_le le_rfl le_rfl) le_rfl
  have h3 : (⁅⁅D, D⁆, D⁆ : Subgroup G).map f = ⁅⁅D.map f, D.map f⁆, D.map f⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
  rw [zGammaThree, zGammaThree]
  refine le_antisymm ?_ ?_
  · refine le_trans (Subgroup.map_inf_le _ _ _) (le_inf ?_ ?_)
    · exact inf_le_left.trans h3.le
    · refine inf_le_right.trans ?_
      have hc : (Subgroup.centralizer ((⁅⁅D, D⁆, D⁆ : Subgroup G) : Set G)).map f ≤
          Subgroup.centralizer
            (((⁅⁅D, D⁆, D⁆ : Subgroup G).map f : Subgroup H) : Set H) := by
        simpa only [Subgroup.coe_map] using
          Subgroup.map_centralizer_le_centralizer_image ((⁅⁅D, D⁆, D⁆ : Subgroup G) : Set G) f
      exact hc.trans (le_of_eq (by rw [h3]))
  · rintro y ⟨hy3, hyC⟩
    rw [← h3] at hy3
    obtain ⟨x, hx3, rfl⟩ := Subgroup.mem_map.mp hy3
    refine Subgroup.mem_map.mpr ⟨x, ⟨hx3, ?_⟩, rfl⟩
    change ∀ a ∈ (⁅⁅D, D⁆, D⁆ : Subgroup G), a * x = x * a
    intro a ha
    have hyC' : ∀ c ∈ (⁅⁅D.map f, D.map f⁆, D.map f⁆ : Subgroup H), c * f x = f x * c :=
      fun c hc => (Subgroup.mem_centralizer_iff.mp hyC) c hc
    have hfa : f a ∈ (⁅⁅D, D⁆, D⁆ : Subgroup G).map f := Subgroup.mem_map_of_mem f ha
    rw [h3] at hfa
    have hcomm : f a * f x = f x * f a := hyC' (f a) hfa
    have heq : f (a * x) = f (x * a) := by rw [map_mul, map_mul, hcomm]
    exact hf (D.mul_mem (h3le ha) (h3le hx3)) (D.mul_mem (h3le hx3) (h3le ha)) heq

variable {G : Type} [Group G] [Finite G] {t : G} {P : Subgroup G}

theorem suzSylowData_of_isPComponent
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hPc : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hS : Blueprint.NativeSporadic.IsSporadic (↥P ⧸ Open.fusionZStar ↥P) .Suz) :
    SuzSylowData P t := by
  let U : Subgroup ↥P := pPrimeCore 2 ↥P
  let Pb := ↥P ⧸ U
  let π : ↥P →* Pb := QuotientGroup.mk' U
  have hπker : π.ker = U := QuotientGroup.ker_mk' U
  have hFinPb : Finite Pb := Finite.of_surjective π (QuotientGroup.mk'_surjective U)
  have key : ∀ (n : ℕ), (∀ R : Sylow 2 Pb,
      IsElemTwo (zGammaThree (R : Subgroup Pb)) ∧
        Nat.card (zGammaThree (R : Subgroup Pb)) = n ∧
        ∃ Q : Subgroup Pb, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
          (R : Subgroup Pb) ⊔ centralizer (Q : Set Pb) = ⊤) →
      ∀ D : Subgroup G, IsSylowTwoIn D P → IsElemTwo (zGammaThree D) ∧
        Nat.card (zGammaThree D) = n ∧
        ∃ Q : Subgroup G, Q ≤ D ∧ IsElemTwo Q ∧ 8 ≤ Nat.card Q ∧
          P ≤ D ⊔ (P ⊓ centralizer (Q : Set G)) ⊔ oddIn P := by
    intro n hF D hD
    obtain ⟨hDP, P', hP'⟩ := hD
    let D' : Subgroup ↥P := D.subgroupOf P
    have hD'p : IsPGroup 2 D' := by
      rw [show D' = (P' : Subgroup ↥P) from hP'.symm]
      exact P'.isPGroup'
    let Dbar : Subgroup Pb := D'.map π
    let R : Sylow 2 Pb := P'.mapSurjective (QuotientGroup.mk'_surjective U)
    have hRcoe : (R : Subgroup Pb) = Dbar := by
      rw [Sylow.coe_mapSurjective, hP']
    obtain ⟨hAbar, hcardbar, Qbar, hQbar_le, hQbar_e, hQbar_card, hQbar_sup⟩ := hF R
    rw [hRcoe] at hAbar hcardbar hQbar_le hQbar_sup
    have hinjπ : Set.InjOn π D' := GSThmB.OddQuot.injOn_of_isPGroup hD'p
    have hzD' : (zGammaThree D').map π = zGammaThree Dbar := by
      simpa only [Dbar] using map_zGammaThree_of_injOn π hinjπ
    have hzD : (zGammaThree D').map P.subtype = zGammaThree D := by
      have h := map_zGammaThree_of_injOn P.subtype (P.subtype_injective.injOn (s := D'))
      rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hDP] at h
    have hZ'2 : IsPGroup 2 (zGammaThree D') := hD'p.to_le (zGammaThree_le D')
    have hcardD : Nat.card (zGammaThree D) = n := by
      have h1 : Nat.card (zGammaThree D) = Nat.card (zGammaThree D') := by
        rw [← hzD, Subgroup.card_map_of_injective P.subtype_injective]
      have h2 : Nat.card (zGammaThree D') = Nat.card (zGammaThree Dbar) := by
        rw [← GSThmB.OddQuot.card_map_of_isPGroup hZ'2, hzD']
      rw [h1, h2, hcardbar]
    have hA' : IsElemTwo (zGammaThree D') := by
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        have hx' : π x ∈ zGammaThree Dbar := by
          rw [← hzD']
          exact Subgroup.mem_map_of_mem π hx
        have hy' : π y ∈ zGammaThree Dbar := by
          rw [← hzD']
          exact Subgroup.mem_map_of_mem π hy
        refine hinjπ (D'.mul_mem (zGammaThree_le D' hx) (zGammaThree_le D' hy))
          (D'.mul_mem (zGammaThree_le D' hy) (zGammaThree_le D' hx)) ?_
        rw [map_mul, map_mul]
        exact hAbar.1 (π x) hx' (π y) hy'
      · intro x hx
        have hx' : π x ∈ zGammaThree Dbar := by
          rw [← hzD']
          exact Subgroup.mem_map_of_mem π hx
        refine hinjπ (D'.mul_mem (zGammaThree_le D' hx) (zGammaThree_le D' hx))
          (D'.one_mem) ?_
        rw [map_mul, map_one]
        exact hAbar.2 (π x) hx'
    have hA : IsElemTwo (zGammaThree D) := by
      rw [← hzD]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hA'.1 x hx y hy]
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, hA'.2 x hx, map_one]
    obtain ⟨Z, hZD', hZmap, hZe, hZcard⟩ :=
      HeDL.exists_lift_le (H := ↥P) (R := D') (E := Qbar) hQbar_e hQbar_le
    let Q : Subgroup G := Z.map P.subtype
    have hQD : Q ≤ D := by
      intro q hq
      change q ∈ Z.map P.subtype at hq
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hq
      exact Subgroup.mem_subgroupOf.mp (hZD' hz)
    have hQe : IsElemTwo Q := by
      change IsElemTwo (Z.map P.subtype)
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hZe.1 a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_mul, hZe.2 a ha, map_one]
    have hQcard : Nat.card Q = 8 := by
      change Nat.card (Z.map P.subtype) = 8
      rw [Subgroup.card_map_of_injective P.subtype_injective, hZcard, hQbar_card]
    let C : Subgroup G := P ⊓ centralizer (Q : Set G)
    have hCsub : C.subgroupOf P = Subgroup.centralizer (Z : Set ↥P) := by
      ext x
      change (x : G) ∈ P ⊓ centralizer (Q : Set G) ↔ x ∈ Subgroup.centralizer (Z : Set ↥P)
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, hx⟩ y hy
        exact Subtype.ext (hx _ (Subgroup.mem_map_of_mem P.subtype hy))
      · intro hx
        refine ⟨x.2, fun z hz => ?_⟩
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
        exact congrArg Subtype.val (hx y hy)
    have hCmap : (C.subgroupOf P).map π = Subgroup.centralizer (Qbar : Set Pb) := by
      have hZ2 : IsPGroup 2 Z := hZe.isPGroup
      have hker : ¬ 2 ∣ Nat.card (π.domRestrict (⊤ : Subgroup ↥P)).ker :=
        GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π
          (GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥P)) ⊤
      have hZY : Z ≤ normalizer (⊤ : Set ↥P) := by
        rw [show (⊤ : Set ↥P) = ((⊤ : Subgroup ↥P) : Set ↥P) from rfl,
          Subgroup.normalizer_eq_top]
        exact le_top
      have hmap := GSThmB.OddQuot.map_inf_centralizer π hZ2 hZY hker
      rw [← hCsub, hZmap] at hmap
      simpa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective U)] using hmap
    have hD'bar : D'.map π = Dbar := rfl
    have htop : (D' ⊔ C.subgroupOf P).map π = ⊤ := by
      rw [Subgroup.map_sup, hCmap, hD'bar, hQbar_sup]
    have htopU : (⊤ : Subgroup ↥P) ≤ (D' ⊔ C.subgroupOf P) ⊔ U := by
      intro p _
      have hp' : π p ∈ (D' ⊔ C.subgroupOf P).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.mp hp'
      have hker : y⁻¹ * p ∈ U := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyp, inv_mul_cancel]
      have hp_eq : p = y * (y⁻¹ * p) := by group
      rw [hp_eq]
      exact Subgroup.mul_mem ((D' ⊔ C.subgroupOf P) ⊔ U)
        (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hker)
    have hPle : P ≤ D ⊔ C ⊔ oddIn P := by
      have h := Subgroup.map_mono (f := P.subtype) htopU
      rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hDP, inf_of_le_left inf_le_left] at h
      simpa only [oddIn] using h
    exact ⟨hA, hcardD, Q, hQD, hQe, hQcard.ge, hPle⟩
  rcases suz_cover_of_isPComponent ht hPt hPc hS with ⟨-, hspor, htnP⟩ | ⟨hcenter, hperf, hspor⟩
  · have hF : ∀ R : Sylow 2 Pb, IsElemTwo (zGammaThree (R : Subgroup Pb)) ∧
        Nat.card (zGammaThree (R : Subgroup Pb)) = 16 ∧
        ∃ Q : Subgroup Pb, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
          (R : Subgroup Pb) ⊔ centralizer (Q : Set Pb) = ⊤ :=
      fun R => hF1 Pb hspor R
    refine ⟨?_, ?_, ?_⟩
    · intro D hD
      exact ⟨(key 16 hF D hD).1, by have := (key 16 hF D hD).2.1; omega⟩
    · intro D hD
      obtain ⟨hA, hcard, -⟩ := key 16 hF D hD
      have htnD : t ∉ zGammaThree D := fun htz =>
        htnP (hD.1 (zGammaThree_le D htz))
      have hcomm : ∀ y ∈ zGammaThree D, t * y = y * t := fun y hy =>
        (mem_centralizer_singleton_iff.mp (hPt (hD.1 (zGammaThree_le D hy)))).symm
      have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
      obtain ⟨-, hcard32⟩ := GrS5.elemTwo_zpowers_sup htt hA hcomm htnD
      rw [sup_comm, hcard32, hcard]
    · intro D hD
      exact (key 16 hF D hD).2.2
  · have hF : ∀ R : Sylow 2 Pb, IsElemTwo (zGammaThree (R : Subgroup Pb)) ∧
        Nat.card (zGammaThree (R : Subgroup Pb)) = 32 ∧
        ∃ Q : Subgroup Pb, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
          (R : Subgroup Pb) ⊔ centralizer (Q : Set Pb) = ⊤ :=
      fun R => hF2 Pb hperf hcenter hspor R
    refine ⟨?_, ?_, ?_⟩
    · intro D hD
      exact ⟨(key 32 hF D hD).1, by have := (key 32 hF D hD).2.1; omega⟩
    · intro D hD
      obtain ⟨-, hcard, -⟩ := key 32 hF D hD
      calc 32 = Nat.card (zGammaThree D) := hcard.symm
        _ ≤ Nat.card ↥(zGammaThree D ⊔ zpowers t) :=
          Subgroup.card_le_of_le le_sup_left
    · intro D hD
      exact (key 32 hF D hD).2.2

theorem suzSylowData_of_facts
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    (h : L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P) :
    SuzSylowData P t :=
  suzSylowData_of_isPComponent hF1 hF2 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2

end CFSG.ComponentClassification.GrSLit.L34Sec5S
