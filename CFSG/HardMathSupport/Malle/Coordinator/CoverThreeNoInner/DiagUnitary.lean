module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.DiagLinear
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUSetup

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.KFacts (psuConj psuPrimeFormEquiv congr_psuConj)

section Main

theorem coverThreeNoInnerDiagUnitary_of_cores (hcoreI : UnitaryHeisCore)
    (hcoreO : UnitaryOuterHeisCore) : CoverThreeNoInnerDiagUnitary := by
  intro Y _ _ Rb Y₀ h K _ hK _hC hcent hZ ℓ f F _ hU hq2 h3q _hq8 e E hER hEN hEa hEc _hEout hlin
  classical
  have := hU.finite
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set φ := modelAct K e with hφ
  set C := Subgroup.centralizer (K : Set Y) with hCdef
  have hker : φ.ker = C := modelAct_ker hK e
  set B := E.map φ with hB
  have hBa : IsElemAbelian 3 B := CFSG.SectionRank.isElemAbelian_map hEa φ
  have hB9 : Nat.card B ≤ 9 :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range
      (RankTwoGU.three_dvd_card_sub_one hU h3q) B hlin
      (fun x hx y hy => congrArg Subtype.val (hBa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hBa.2
  set S := E ⊓ C with hS
  set Z : Subgroup Y := (Subgroup.center K).map K.subtype with hZdef
  have hZcard : Nat.card Z = Nat.card (Subgroup.center K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hSZ : S ≤ Z := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1]; exact Z.one_mem
    · refine hcent s ⟨hER hs.1, hs.2⟩ ?_
      exact orderOf_eq_prime (hEa.2 s hs.1) h1
  have hS3 : Nat.card S ≤ 3 := by
    refine card_le_three_of_exp_three hSZ (by rw [hZcard]; exact hZ) fun x hx => hEa.2 x hx.1
  set ψ : E →* MulAut (unitaryPSU hU 3) := φ.comp E.subtype with hψ
  have hψker : ψ.ker = S.subgroupOf E := by
    ext x
    simp only [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf, hS, Subgroup.mem_inf, hCdef]
    rw [← hCdef, ← hker, MonoidHom.mem_ker]
    exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
  have hψrange : ψ.range = B := by
    ext a
    simp only [MonoidHom.mem_range, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, hB,
      Subgroup.mem_map]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hxa⟩ => ⟨⟨x, hx⟩, hxa⟩⟩
  have hkr : Nat.card ψ.ker = Nat.card S := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmulcard : Nat.card S * Nat.card B = 27 := by
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hkr, hψrange] at this
    rw [this, hEc]
    norm_num
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hS3' : Nat.card S = 3 := by
    by_contra hne
    have hlt : Nat.card S ≤ 2 := by omega
    nlinarith
  have hB9' : Nat.card B = 9 := by rw [hS3'] at hmulcard; omega
  have hZcomm : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ * z₂ = z₂ * z₁ := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₂ c₁)
  let Ω : Subgroup Y :=
    { carrier := {z | z ∈ Z ∧ z ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => ⟨Z.mul_mem ha.1 hb.1, by
        have : Commute a b := hZcomm a ha.1 b hb.1
        rw [this.mul_pow, ha.2, hb.2, mul_one]⟩
      one_mem' := ⟨Z.one_mem, one_pow 3⟩
      inv_mem' := fun {a} ha => ⟨Z.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩZ : Ω ≤ Z := fun z hz => hz.1
  have hΩ3 : Nat.card Ω ≤ 3 :=
    card_le_three_of_exp_three hΩZ (by rw [hZcard]; exact hZ) fun x hx => hx.2
  have hSΩ : S ≤ Ω := fun s hs => ⟨hSZ hs, hEa.2 s hs.1⟩
  have hSΩeq : S = Ω := Subgroup.eq_of_le_of_card_ge hSΩ (by rw [hS3']; exact hΩ3)
  have hΩS : ∀ z ∈ Z, z ^ 3 = 1 → z ∈ S := fun z hz hz3 => hSΩeq ▸ (⟨hz, hz3⟩ : z ∈ Ω)
  have hSker : ∀ s ∈ S, φ s = 1 := fun s hs => by rw [← MonoidHom.mem_ker, hker]; exact hs.2
  have key : ∀ y ∈ E, φ y ≠ 1 → ∀ x : unitaryPSU hU 3, φ y x = x →
      ∃ k : K, e (QuotientGroup.mk k) = x ∧ ∃ F' : Subgroup Y, F' ≤ E ∧ F'.relIndex E = 3 ∧
        (k : Y) ∈ Subgroup.normalizer (F' : Set Y) := by
    intro y hy hy1 x hx
    have hy3 : y ^ 3 = 1 := hEa.2 y hy
    obtain ⟨k, hkx, z, hzZ, hz3, hkz⟩ := exists_normalizing_lift K e hZ hy3 hx
    have hzS : z ∈ S := hΩS z hzZ hz3
    set L : Subgroup (MulAut (unitaryPSU hU 3)) := Subgroup.zpowers (φ y) with hL
    set F' : Subgroup Y := L.comap φ ⊓ E with hF'
    have hyB : φ y ∈ B := ⟨y, hy, rfl⟩
    have hLB : L ≤ B := (Subgroup.zpowers_le).2 hyB
    have hφy3 : (φ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hordφy : orderOf (φ y) = 3 := orderOf_eq_prime hφy3 hy1
    refine ⟨k, hkx, F', inf_le_right, ?_, ?_⟩
    · rw [hF', Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
      have h1 := (L.subgroupOf B).card_mul_index
      have h2 : Nat.card (L.subgroupOf B) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLB).toEquiv, hL, Nat.card_zpowers,
          hordφy]
      rw [h2, hB9'] at h1
      change (L.subgroupOf B).index = 3
      omega
    · have claim : ∀ k' : Y, k' ∈ K → ∀ z' ∈ S, k' * y * k'⁻¹ = z' * y →
          ∀ x' ∈ F', k' * x' * k'⁻¹ ∈ F' := by
        intro k' hk' z' hz'S hk'z x' hx'
        obtain ⟨hx'L, hx'E⟩ := hx'
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx'L
        set s : Y := x' * (y ^ i)⁻¹ with hs
        have hsE : s ∈ E := E.mul_mem hx'E (E.inv_mem (E.zpow_mem hy i))
        have hφs : φ s = 1 := by
          rw [hs, map_mul, map_inv, map_zpow, hi, mul_inv_cancel]
        have hsC : s ∈ C := by rw [← hker]; exact hφs
        have hxs : x' = s * y ^ i := by rw [hs]; group
        have hks : k' * s * k'⁻¹ = s := by
          have := Subgroup.mem_centralizer_iff.mp hsC k' hk'
          rw [this]; group
        have hzy : Commute z' y :=
          congrArg Subtype.val (hEa.1.is_comm.comm ⟨z', hz'S.1⟩ ⟨y, hy⟩)
        have e1 : k' * (s * y ^ i) * k'⁻¹ = (k' * s * k'⁻¹) * (k' * y * k'⁻¹) ^ i := by
          simp
        have hconj : k' * x' * k'⁻¹ = s * (z' ^ i * y ^ i) := by
          rw [hxs, e1, hks, hk'z, hzy.mul_zpow]
        rw [hconj]
        refine ⟨?_, E.mul_mem hsE (E.mul_mem (E.zpow_mem hz'S.1 i) (E.zpow_mem hy i))⟩
        show φ (s * (z' ^ i * y ^ i)) ∈ L
        have hφ' : φ (s * (z' ^ i * y ^ i)) = φ y ^ i := by
          rw [map_mul φ s, hφs, map_mul φ (z' ^ i), map_zpow φ z', hSker z' hz'S, one_zpow,
            map_zpow φ y, one_mul, one_mul]
        rw [hφ']
        exact Subgroup.zpow_mem_zpowers _ i
      have hzc : (z : Y) * (k : Y) = (k : Y) * z := by
        obtain ⟨c, hc, rfl⟩ := hzZ
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc k)).symm
      have hkzk : (k : Y)⁻¹ * z * k = z := by
        calc (k : Y)⁻¹ * z * k = (k : Y)⁻¹ * (z * k) := by group
          _ = (k : Y)⁻¹ * (k * z) := by rw [hzc]
          _ = z := by group
      have h1 : (k : Y) * y = z * y * k := by
        calc (k : Y) * y = ((k : Y) * y * (k : Y)⁻¹) * k := by group
          _ = z * y * k := by rw [hkz]
      have hkz' : (k : Y)⁻¹ * y * ((k : Y)⁻¹)⁻¹ = z⁻¹ * y := by
        calc (k : Y)⁻¹ * y * ((k : Y)⁻¹)⁻¹ = (k : Y)⁻¹ * y * k := by group
          _ = z⁻¹ * (((k : Y)⁻¹ * z * k) * ((k : Y)⁻¹ * y * k)) := by rw [hkzk]; group
          _ = z⁻¹ * ((k : Y)⁻¹ * (z * y * k)) := by group
          _ = z⁻¹ * ((k : Y)⁻¹ * (k * y)) := by rw [h1]
          _ = z⁻¹ * y := by group
      refine Subgroup.mem_normalizer_iff.2 fun g =>
        ⟨fun hg => claim k k.2 z hzS hkz g hg, fun hg => ?_⟩
      have := claim (k : Y)⁻¹ (K.inv_mem k.2) z⁻¹ (S.inv_mem hzS) hkz' _ hg
      have e' : (k : Y)⁻¹ * ((k : Y) * g * (k : Y)⁻¹) * ((k : Y)⁻¹)⁻¹ = g := by group
      rwa [e'] at this
  have hBa9 : Nat.card B = 3 ^ 2 := by rw [hB9']; norm_num
  have hgenB : PlaneGen B := by
    refine planeGen_of_unitaryDiagAut_equiv hcoreI hcoreO hU h3q (by omega) (psuPrimeFormEquiv hU)
      hBa hBa9 ?_
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨A, rfl⟩ := hlin hb
    exact ⟨_, (congr_psuConj A).symm⟩
  let ρ : K →* unitaryPSU hU 3 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρker : ρ.ker ≤ Subgroup.center K := by
    intro k hk
    have : e (QuotientGroup.mk k) = 1 := hk
    have h2 : (QuotientGroup.mk k : K ⧸ Subgroup.center K) = 1 := (MulEquiv.map_eq_one_iff e).mp this
    exact (QuotientGroup.eq_one_iff k).mp h2
  set 𝒢 : Set K := {k : K | ∃ F' : Subgroup Y, F' ≤ E ∧ F'.relIndex E = 3 ∧
    (k : Y) ∈ Subgroup.normalizer (F' : Set Y)} with h𝒢
  have hmap : (Subgroup.closure 𝒢).map ρ = ⊤ := by
    rw [eq_top_iff, ← hgenB]
    unfold planeClosure
    rw [Subgroup.closure_le]
    rintro x ⟨b, ⟨y, hy, rfl⟩, hb1, hbx⟩
    obtain ⟨k, hkx, F', hF'E, hF'rel, hF'N⟩ := key y hy hb1 x hbx
    exact ⟨k, Subgroup.subset_closure ⟨F', hF'E, hF'rel, hF'N⟩, hkx⟩
  have htop : Subgroup.closure 𝒢 = ⊤ := eq_top_of_map_eq_top_of_perfect ρ hρker hmap
  have hgen : K ≤ Subgroup.closure {k : Y | ∃ F' : Subgroup Y, F' ≤ E ∧ F'.relIndex E = 3 ∧
      k ∈ Subgroup.normalizer (F' : Set Y)} := by
    intro k hk
    have h1 : (⟨k, hk⟩ : K) ∈ Subgroup.closure 𝒢 := by rw [htop]; exact Subgroup.mem_top _
    have h2 : k ∈ (Subgroup.closure 𝒢).map K.subtype := ⟨⟨k, hk⟩, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨k', hk', rfl⟩
    exact hk'
  exact false_of_le_closure_normalizers h hEa hEc hER hEN hgen

theorem coverThreeNoInnerDiagUnitary_of_certs :
    CoverThreeNoInnerDiagUnitary :=
  coverThreeNoInnerDiagUnitary_of_cores unitaryHeisCore (unitaryOuterHeisCore_of_finite_cases
      HeisSmall.outerB12AtCard_five HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven)

end Main

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
