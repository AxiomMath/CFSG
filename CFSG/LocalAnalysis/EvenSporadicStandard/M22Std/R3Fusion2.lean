module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Fusion1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutProp21

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem exists_mem_commutator_of_index_two {D : Type*} [Group D]
    (ψ : D →* Equiv.Perm (Fin 6)) (hψ : Function.Surjective ψ) {Λ : Subgroup D}
    (hΛ : Λ.index = 2) (hker : ψ.ker ≤ Λ) {μ : D} (hμ : μ ∈ Λ) :
    ∃ w ∈ commutator D, μ⁻¹ * w ∈ ψ.ker := by
  have h1 : (Λ.map ψ).index = 2 := by rw [Subgroup.index_map_eq Λ hψ hker]; exact hΛ
  have h2 : Λ.map ψ = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two h1
  have h3 : (commutator D).map ψ = alternatingGroup (Fin 6) := by
    have e1 : (commutator D).map ψ = ⁅(⊤ : Subgroup (Equiv.Perm (Fin 6))), ⊤⁆ := by
      show Subgroup.map ψ ⁅(⊤ : Subgroup D), ⊤⁆ = _
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ]
    rw [e1]
    exact alternatingGroup.commutator_perm_eq (by simp)
  have h4 : ψ μ ∈ (commutator D).map ψ := by
    rw [h3, ← h2]
    exact ⟨μ, hμ, rfl⟩
  obtain ⟨w, hw, hwμ⟩ := h4
  refine ⟨w, hw, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hwμ, inv_mul_cancel]

variable {G : Type} [Group G] [Finite G]

theorem fin77aOuterFusion_of_facts
    (hEng : AutSylowEngine6 (Carrier .M22))
    (hCens : AutSylowWith (fun Y _ F => AutCensus Y F) (Carrier .M22))
    (hFacts : AutSylowWith3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32Facts Y S F J)
      (Carrier .M22)) :
    Fin77aOuterSit fun X _ _ z => OuterFusion X z := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hS hz hC
  show OuterFusion (Xbar L1) (QuotientGroup.mk ⟨z, hz⟩)
  obtain ⟨A, b, hLA, hAH, hzA, hAz, hidx, hquot, hcens, hbL, hb2, hb1, hbF, hbN, hfix4, k, hk, l,
    hl, hkl⟩ := hS.exists_fusion_data hEng hCens hFacts
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have hXE := Sup.inf_centralizer_eq hAH hAz
  have hbD : b ∈ normalizer (liftSub F : Set G) ⊓ A := Subgroup.mem_inf.2 ⟨hbN, hLA hbL⟩
  have hDX : normalizer (liftSub F : Set G) ⊓ A ≤ normalizer (L1 : Set G) := by
    intro d hd
    have : d ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) := Subgroup.mem_sup_right hd
    rw [← hXE] at this
    exact (Subgroup.mem_inf.1 this).1
  have hbX : b ∈ normalizer (L1 : Set G) := hDX hbD
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg =>
    (mem_centralizer_singleton_iff.1 (hAH hg)).symm
  have hbz : z * b = b * z := hzc b (hLA hbL)
  have hb'2 : (QuotientGroup.mk ⟨b, hbX⟩ : Xbar L1) * QuotientGroup.mk ⟨b, hbX⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨b, hbX⟩ : ↥(normalizer (L1 : Set G))) * ⟨b, hbX⟩ = 1 := Subtype.ext hb2
    rw [this]
    exact QuotientGroup.mk_one _
  have hb'1 : (QuotientGroup.mk ⟨b, hbX⟩ : Xbar L1) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have hall : Nat.card {y : G // y ∈ liftSub F ∧ b * y = y * b} = 16 := by
      rw [← Sup.one.F_card]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ⟨fun h1 => h1.1, fun h1 => ⟨h1, ?_⟩⟩)
      exact (mem_centralizer_iff.1 h w (Sup.F_le h1)).symm
    rw [hfix4] at hall
    omega
  have hconj : IsConj (QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)
      (QuotientGroup.mk ⟨z, hz⟩ * QuotientGroup.mk ⟨b, hbX⟩) := by
    refine isConj_iff.2 ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((k * z * k⁻¹)⁻¹ * (z * b) : G) ∈ centralizer (L1 : Set G)
    rw [hkl]
    have : (z * b * l)⁻¹ * (z * b) = l⁻¹ := by group
    rw [this]
    exact mem_centralizer_iff.2 fun w hw => Sup.L1_comm w hw l⁻¹ (L1.inv_mem hl)
  obtain ⟨ψ, hψ, hker⟩ := hquot
  obtain ⟨-, -, h3, -, -, -, -, -, -, hout, -⟩ := hcens
  have hne : Nonempty (InvClassD (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) 384 8) :=
    (Nat.card_pos_iff.1 (by omega : 0 < Nat.card
      (InvClassD (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) 384 8))).1
  obtain ⟨⟨μ', hμ'⟩⟩ := hne
  have hμ'L : (μ' : G) ∉ L := hout μ' (Or.inl hμ')
  have hΛ : (L.subgroupOf (normalizer (liftSub F : Set G) ⊓ A)).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨μ', fun β => ?_⟩
    have key := Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨(β : G), (Subgroup.mem_inf.1 β.2).2⟩) (b := ⟨(μ' : G), (Subgroup.mem_inf.1 μ'.2).2⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key ⊢
    by_cases hβ : (β : G) ∈ L
    · refine Or.inr ⟨hβ, fun ha => ?_⟩
      exact hμ'L ((key.1 ha).1 hβ)
    · exact Or.inl ⟨key.2 ⟨fun h => absurd h hβ, fun h => absurd h hμ'L⟩, hβ⟩
  have hkerΛ : ψ.ker ≤ L.subgroupOf (normalizer (liftSub F : Set G) ⊓ A) := by
    intro g hg
    rw [hker] at hg
    exact Subgroup.mem_subgroupOf.2 (liftSub_le F (Subgroup.mem_subgroupOf.1 hg))
  have hμΛ : (⟨b, hbD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A)) ∈
      L.subgroupOf (normalizer (liftSub F : Set G) ⊓ A) := Subgroup.mem_subgroupOf.2 hbL
  obtain ⟨w, hw, hμw⟩ := exists_mem_commutator_of_index_two ψ hψ hΛ hkerΛ hμΛ
  let Φ' : ↥(normalizer (liftSub F : Set G) ⊓ A) →* Xbar L1 :=
    (QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))).comp
      (Subgroup.inclusion hDX)
  have hΦ'z : ∀ d, Φ' d ∈ centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)) := by
    intro d
    rw [mem_centralizer_singleton_iff]
    show (QuotientGroup.mk (⟨(d : G), hDX d.2⟩ : ↥(normalizer (L1 : Set G))) : Xbar L1) *
        QuotientGroup.mk ⟨z, hz⟩ = QuotientGroup.mk ⟨z, hz⟩ * QuotientGroup.mk ⟨(d : G), hDX d.2⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (hzc d (Subgroup.mem_inf.1 d.2).2).symm)
  let Φ : ↥(normalizer (liftSub F : Set G) ⊓ A) →*
      ↥(centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1))) :=
    Φ'.codRestrict _ hΦ'z
  have hker1 : Φ' ((⟨b, hbD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A))⁻¹ * w) = 1 := by
    have hmem : ((⟨b, hbD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A))⁻¹ * w :
        ↥(normalizer (liftSub F : Set G) ⊓ A)) ∈
        (liftSub F).subgroupOf (normalizer (liftSub F : Set G) ⊓ A) := by
      rw [← hker]
      exact hμw
    have h1 := Subgroup.mem_subgroupOf.1 hmem
    show (QuotientGroup.mk (Subgroup.inclusion hDX _) : Xbar L1) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_centralizer_iff.2 fun w' hw' => Sup.L1_comm w' hw' _ (Sup.F_le h1)
  have hΦeq : Φ' ⟨b, hbD⟩ = Φ' w := by
    rw [map_mul, map_inv] at hker1
    exact inv_mul_eq_one.1 hker1
  have hΦw : Φ w ∈ commutator ↥(centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} :
      Set (Xbar L1))) := by
    have h1 : Φ w ∈ (commutator ↥(normalizer (liftSub F : Set G) ⊓ A)).map Φ := ⟨w, hw, rfl⟩
    have h2 : (commutator ↥(normalizer (liftSub F : Set G) ⊓ A)).map Φ ≤
        commutator ↥(centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1))) := by
      show Subgroup.map Φ ⁅⊤, ⊤⁆ ≤ ⁅⊤, ⊤⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  refine ⟨QuotientGroup.mk ⟨b, hbX⟩, ⟨Φ w, hΦw, ?_⟩, hb'2, hb'1, hconj⟩
  show (Φ' w : Xbar L1) = QuotientGroup.mk ⟨b, hbX⟩
  rw [← hΦeq]
  rfl

end CFSG.EvenSporadicStandard.M22Std
