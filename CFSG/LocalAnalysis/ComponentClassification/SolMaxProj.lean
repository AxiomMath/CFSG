module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PumpDown
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitBalanceCore
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props
public import CFSG.LocalAnalysis.ComponentClassification.Sol76TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

section Component

variable {W : Type*} [Group W] [Finite W]

theorem layer_inf_centralizer_normal {K : Subgroup W} (hK : IsComponent K) :
    ((layer W ⊓ centralizer (K : Set W)).subgroupOf (layer W)).Normal := by
  set E := layer W
  have hEK : E ≤ normalizer (K : Set W) := layer_le_normalizer hK
  rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
  refine Sol76.le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
  obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨mul_mem (mul_mem hc hxE) (inv_mem hc), ?_⟩
  rw [mem_centralizer_iff]
  intro k hk
  have hk' : c⁻¹ * k * c ∈ K := by
    have := (mem_normalizer_iff.mp (hEK (inv_mem hc)) k).mp hk
    simpa using this
  have h1 : c⁻¹ * k * c * x = x * (c⁻¹ * k * c) := (mem_centralizer_iff.mp hxC) _ hk'
  calc k * (c * x * c⁻¹) = c * (c⁻¹ * k * c * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
    _ = c * x * c⁻¹ * k := by group

theorem exists_surjective_quot_centralizer {K : Subgroup W} (hK : IsComponent K)
    [((layer W ⊓ centralizer (K : Set W)).subgroupOf (layer W)).Normal] :
    ∃ φ : ↥K →* ↥(layer W) ⧸ (layer W ⊓ centralizer (K : Set W)).subgroupOf (layer W),
      Function.Surjective φ ∧ φ.ker = center ↥K := by
  set E := layer W
  set Z := E ⊓ centralizer (K : Set W)
  have hKE : K ≤ E := component_le_layer hK
  set φ := QuotientGroup.mk' (Z.subgroupOf E)
  refine ⟨φ.comp (Subgroup.inclusion hKE), ?_, ?_⟩
  · intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf E) q
    obtain ⟨u, hu, huc⟩ := Sol76.exists_mem_mul_centralizer hK e.2
    refine ⟨⟨u, hu⟩, ?_⟩
    change φ ⟨u, hKE hu⟩ = φ e
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hKE hu)) e.2, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact (huc k hk).eq
  · ext k
    rw [MonoidHom.mem_ker, mem_center_iff]
    change φ ⟨k, hKE k.2⟩ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro h l
      exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp h).2) l l.2)
    · intro h
      refine mem_inf.mpr ⟨hKE k.2, ?_⟩
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (h ⟨l, hl⟩)

end Component

section Lift

variable {Y : Type*} [Group Y] [Finite Y]

theorem nonempty_fusionZStar_quot_equiv_center {K : Subgroup (Y ⧸ pPrimeCore 2 Y)}
    (hK : K.IsSubnormal) {M : Subgroup Y} (hMK : M.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = K) :
    Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* ↥K ⧸ center ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  have hmem : ∀ l : ↥M, π (M.subtype l) ∈ K := fun l => hMK ▸ mem_map_of_mem π l.2
  let f : ↥M →* ↥K := (π.comp M.subtype).codRestrict K hmem
  have hf_apply : ∀ l : ↥M, (f l : Y ⧸ pPrimeCore 2 Y) = π l := fun _ => rfl
  have hf : Function.Surjective f := by
    rintro ⟨k, hk⟩
    rw [← hMK] at hk
    obtain ⟨l, hl, rfl⟩ := hk
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : f.ker = pPrimeCore 2 ↥M := by
    apply le_antisymm
    · refine le_sSup ⟨f.normal_ker, ?_⟩
      let ι : f.ker →* pPrimeCore 2 Y :=
        { toFun := fun x => ⟨((x : ↥M) : Y), by
            have h1 : f x = 1 := x.2
            have h2 := congrArg Subtype.val h1
            rw [hf_apply] at h2
            exact (QuotientGroup.eq_one_iff _).mp h2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hι : Function.Injective ι := fun a b h => by
        have h2 : ((ι a : pPrimeCore 2 Y) : Y) = ι b := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h2)
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι)
        (pPrimeCore_coprime_card (p := 2) (G := Y))
    · have hO : (pPrimeCore 2 ↥M).map f ≤ pPrimeCore 2 ↥K := by
        refine le_sSup ⟨(pPrimeCore_normal (p := 2) (G := ↥M)).map f hf, ?_⟩
        exact Nat.Coprime.coprime_dvd_right (card_map_dvd _ f)
          (pPrimeCore_coprime_card (p := 2) (G := ↥M))
      have hKO : (pPrimeCore 2 ↥K).map K.subtype ≤ pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) :=
        CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hK
      rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hKO
      intro x hx
      have h1 : f x ∈ pPrimeCore 2 ↥K := hO (mem_map_of_mem f hx)
      have h2 : (f x : Y ⧸ pPrimeCore 2 Y) ∈ (⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)) :=
        hKO (mem_map_of_mem K.subtype h1)
      rw [mem_bot] at h2
      exact MonoidHom.mem_ker.mpr (Subtype.ext h2)
  have eM : ↥M ⧸ pPrimeCore 2 ↥M ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨(Sol78.coreQuotientCenterEquiv ↥M).symm.trans (Sol78.centerQuotCongr eM)⟩

end Lift

section Proj

variable {G : Type} [Group G] [Finite G]

theorem card_fusionZStar_quot_le {Y P M : Subgroup G} (hPY : P ≤ twoLayerIn Y)
    (hP : ⁅P, P⁆ = P) (hPq : IsQuasisimple (↥P ⧸ pPrimeCore 2 ↥P))
    (hM : IsTwoComponentIn M Y) (hmove : ¬ P ≤ coreActionKernel M) :
    Nat.card (↥P ⧸ Open.fusionZStar ↥P) ≤ Nat.card (↥M ⧸ Open.fusionZStar ↥M) ∧
      (Nat.card (↥P ⧸ Open.fusionZStar ↥P) = Nat.card (↥M ⧸ Open.fusionZStar ↥M) →
        Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* ↥M ⧸ Open.fusionZStar ↥M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPY' : P ≤ Y := hPY.trans (map_subtype_le _)
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hPN : P ≤ normalizer (M : Set G) := hPY.trans (twoLayerIn_le_normalizer hM.1 hM.2)
  set O := pPrimeCore 2 ↥Y with hO
  set π := QuotientGroup.mk' O with hπ
  obtain ⟨Kc, hKc, hMsub, hMK, -⟩ := hM.2
  set E := layer (↥Y ⧸ O) with hE
  have := layer_inf_centralizer_normal hKc
  obtain ⟨φK, hφKs, hφKk⟩ := exists_surjective_quot_centralizer hKc
  set Z := E ⊓ centralizer (Kc : Set (↥Y ⧸ O)) with hZ
  set φ := QuotientGroup.mk' (Z.subgroupOf E) with hφ
  let ρ : ↥P →* ↥Y ⧸ O := π.comp (Subgroup.inclusion hPY')
  have hρE : ∀ p : ↥P, ρ p ∈ E := by
    intro p
    refine (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥Y) (p := 2)).le ?_
    refine mem_map_of_mem π ?_
    obtain ⟨y, hy, hyp⟩ := hPY p.2
    have : Subgroup.inclusion hPY' p = y := Subtype.ext hyp.symm
    rw [this]
    exact hy
  let ψ : ↥P →* ↥E ⧸ Z.subgroupOf E := φ.comp (ρ.codRestrict E hρE)
  have hψ : ∀ p : ↥P, ψ p = φ ⟨ρ p, hρE p⟩ := fun _ => rfl
  have hkerψ : ψ.ker ≠ ⊤ := by
    intro h
    apply hmove
    intro p hp
    refine ⟨hPN hp, fun m hm => ?_⟩
    have hpZ : ρ ⟨p, hp⟩ ∈ centralizer (Kc : Set (↥Y ⧸ O)) := by
      have h0 : ψ ⟨p, hp⟩ = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top _)
      rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h0
      exact (mem_inf.mp h0).2
    have hmK : π ⟨m, hM.1 hm⟩ ∈ Kc := by
      rw [← hMK]
      exact mem_map_of_mem π (mem_subgroupOf.mpr hm)
    have hcomm : π ⟨m, hM.1 hm⟩ * π ⟨p, hPY' hp⟩ = π ⟨p, hPY' hp⟩ * π ⟨m, hM.1 hm⟩ :=
      (mem_centralizer_iff.mp hpZ) _ hmK
    have hc : m⁻¹ * p⁻¹ * m * p ∈ M := by
      have h1 : p⁻¹ * m * p ∈ M := by
        have := (mem_normalizer_iff.mp (hPN (inv_mem hp)) m).mp hm
        simpa using this
      have h2 : m⁻¹ * (p⁻¹ * m * p) ∈ M := mul_mem (inv_mem hm) h1
      simpa [mul_assoc] using h2
    have hcY : m⁻¹ * p⁻¹ * m * p ∈ Y := hM.1 hc
    have hcO : (⟨m⁻¹ * p⁻¹ * m * p, hcY⟩ : ↥Y) ∈ O := by
      have e : (⟨m⁻¹ * p⁻¹ * m * p, hcY⟩ : ↥Y) =
          (⟨m, hM.1 hm⟩ : ↥Y)⁻¹ * (⟨p, hPY' hp⟩ : ↥Y)⁻¹ * ⟨m, hM.1 hm⟩ * ⟨p, hPY' hp⟩ := rfl
      have h1 : π (⟨m⁻¹ * p⁻¹ * m * p, hcY⟩ : ↥Y) = 1 := by
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (π ⟨m, hM.1 hm⟩)⁻¹ * (π ⟨p, hPY' hp⟩)⁻¹ * π ⟨m, hM.1 hm⟩ * π ⟨p, hPY' hp⟩
            = (π ⟨m, hM.1 hm⟩)⁻¹ * (π ⟨p, hPY' hp⟩)⁻¹ *
                (π ⟨m, hM.1 hm⟩ * π ⟨p, hPY' hp⟩) := by group
          _ = (π ⟨m, hM.1 hm⟩)⁻¹ * (π ⟨p, hPY' hp⟩)⁻¹ *
                (π ⟨p, hPY' hp⟩ * π ⟨m, hM.1 hm⟩) := by rw [hcomm]
          _ = 1 := by group
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcN : (⟨m⁻¹ * p⁻¹ * m * p, hcY⟩ : ↥Y) ∈ M.subgroupOf Y := hc
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hMsub
    have h2 : (⟨m⁻¹ * p⁻¹ * m * p, hcY⟩ : ↥Y) ∈
        (pPrimeCore 2 ↥(M.subgroupOf Y)).map (M.subgroupOf Y).subtype := by
      rw [h1]
      exact ⟨hcN, hcO⟩
    have h3 := mem_map_of_mem Y.subtype h2
    rw [pPrimeCore_map_subgroupOf 2 M Y hM.1] at h3
    exact h3
  have hleZ : ψ.ker ≤ Open.fusionZStar ↥P :=
    Sol76.le_fusionZStar_of_normal hPperf hPq ψ.normal_ker hkerψ
  have hEZ : Nat.card (↥E ⧸ Z.subgroupOf E) = Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
    obtain ⟨e1⟩ := nonempty_fusionZStar_quot_equiv_center hKc.2 hMK
    have e2 : ↥Kc ⧸ center ↥Kc ≃* ↥E ⧸ Z.subgroupOf E :=
      (QuotientGroup.quotientMulEquivOfEq hφKk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φK hφKs)
    have e3 := Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hM.1)
    rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv, Nat.card_congr e3.toEquiv]
  have h1 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) ≤ Nat.card ψ.range := by
    change (Open.fusionZStar ↥P).index ≤ Nat.card ψ.range
    rw [← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hleZ)
  have h2 : Nat.card ψ.range ≤ Nat.card (↥E ⧸ Z.subgroupOf E) := Subgroup.card_le_card_group _
  refine ⟨h1.trans (h2.trans hEZ.le), fun heq => ?_⟩
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm h2 (hEZ ▸ heq ▸ h1)
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
  have hkereq : ψ.ker = Open.fusionZStar ↥P := by
    apply Subgroup.eq_of_le_of_card_ge hleZ
    have hk := ψ.ker.card_mul_index
    have hz := (Open.fusionZStar ↥P).card_mul_index
    have hidx : ψ.ker.index = (Open.fusionZStar ↥P).index := by
      have e1 : ψ.ker.index = Nat.card (↥E ⧸ Z.subgroupOf E) := by
        rw [index_ker, hrange, card_top]
      rw [e1, hEZ, ← heq]
      rfl
    have hpos : 0 < (Open.fusionZStar ↥P).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at hk
    exact (Nat.eq_of_mul_eq_mul_right hpos (hk.trans hz.symm)).ge
  obtain ⟨e1⟩ := nonempty_fusionZStar_quot_equiv_center hKc.2 hMK
  have e2 : ↥Kc ⧸ center ↥Kc ≃* ↥E ⧸ Z.subgroupOf E :=
    (QuotientGroup.quotientMulEquivOfEq hφKk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φK hφKs)
  have e3 := Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hM.1)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkereq.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).trans
      (e2.symm.trans (e1.symm.trans e3)))⟩

end Proj

end CFSG.ComponentClassification.SolMax
