module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.ModelLift
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.WeakCoreKill
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.PlaneGenOuter
public import CFSG.LieType.SeitzGeneration.OuterHeisCoreProof
public import CFSG.LieType.SeitzGeneration.HyperCoverLift
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

section Group

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_le_three_of_exp_three {Z T : Subgroup Y} (hTZ : T ≤ Z)
    (hZ : (Nat.card Z).factorization 3 = 1) (hT : ∀ x ∈ T, x ^ 3 = 1) : Nat.card T ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 T := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hT g g.2⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : Nat.card T ∣ Nat.card Z := Subgroup.card_dvd_of_le hTZ
  rw [hn] at hdvd
  have hpos : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 hdvd
  rw [hZ] at h1
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    _ = 3 := by norm_num

end Group

section Outer

variable {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal] {M : Type*} [Group M]

theorem mem_sup_of_modelAct_mem_inner (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* M) {y : Y}
    (h : modelAct K e y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner M) :
    y ∈ K ⊔ Subgroup.centralizer (K : Set Y) := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨k, hk⟩ := exists_modelAct_eq_conj K e m
  have hc : (k : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
    rw [← modelAct_ker hK e, MonoidHom.mem_ker, map_mul, map_inv, hk, hm, inv_mul_cancel]
  simpa using Subgroup.mul_mem_sup k.2 hc

end Outer

section Main

theorem coverThreeNoInnerDiagLinear_of_planeGen {Y : Type} [Group Y] [Finite Y] (Rb : Sylow 3 Y)
    (Y₀ : Subgroup Y) (h : ReducedNongeneration 3 Y Rb Y₀) (K : Subgroup Y) [K.Normal]
    (hK : Open.IsQuasisimple K) (_hC : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y))
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (hZ : (Nat.card (Subgroup.center K)).factorization 3 = 1) (F : Type) [Field F] [Finite F]
    (h3F : 3 ∣ Nat.card F - 1)
    (hplane : ∀ B : Subgroup (MulAut (projectiveSL 3 F)), IsElemAbelian 3 B → Nat.card B = 3 ^ 2 →
      B ≤ linearAutGroup 3 F →
      ¬ B ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) → PlaneGen B)
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F)
    (E : Subgroup Y) (hER : E ≤ (Rb : Subgroup Y))
    (hEN : E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEout : ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    (hlin : E.map (modelAct K e) ≤ linearAutGroup 3 F) : False := by
  classical
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set φ := modelAct K e with hφ
  set C := Subgroup.centralizer (K : Set Y) with hCdef
  have hker : φ.ker = C := modelAct_ker hK e
  set B := E.map φ with hB
  have hBa : IsElemAbelian 3 B := CFSG.SectionRank.isElemAbelian_map hEa φ
  have hB9 : Nat.card B ≤ 9 :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.card_le_nine_of_le_linearAutGroup h3F B hlin
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
  set ψ : E →* MulAut (projectiveSL 3 F) := φ.comp E.subtype with hψ
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
  have key : ∀ y ∈ E, φ y ≠ 1 → ∀ x : projectiveSL 3 F, φ y x = x →
      ∃ k : K, e (QuotientGroup.mk k) = x ∧ ∃ F' : Subgroup Y, F' ≤ E ∧ F'.relIndex E = 3 ∧
        (k : Y) ∈ Subgroup.normalizer (F' : Set Y) := by
    intro y hy hy1 x hx
    have hy3 : y ^ 3 = 1 := hEa.2 y hy
    obtain ⟨k, hkx, z, hzZ, hz3, hkz⟩ := exists_normalizing_lift K e hZ hy3 hx
    have hzS : z ∈ S := hΩS z hzZ hz3
    set L : Subgroup (MulAut (projectiveSL 3 F)) := Subgroup.zpowers (φ y) with hL
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
  have hBout : ¬ B ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) := by
    intro hBin
    apply hEout
    intro y hy
    exact mem_sup_of_modelAct_mem_inner hK e (hBin ⟨y, hy, rfl⟩)
  have hgenB : PlaneGen B := hplane B hBa hBa9 hlin hBout
  let ρ : K →* projectiveSL 3 F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
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

theorem coverThreeNoInnerDiagLinear_aux {Y : Type} [Group Y] [Finite Y] (Rb : Sylow 3 Y)
    (Y₀ : Subgroup Y) (h : ReducedNongeneration 3 Y Rb Y₀) (K : Subgroup Y) [K.Normal]
    (hK : Open.IsQuasisimple K) (hC : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y))
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (hZ : (Nat.card (Subgroup.center K)).factorization 3 = 1) (F : Type) [Field F] [Finite F]
    (h3F : 3 ∣ Nat.card F - 1) (h4 : 4 < Nat.card F)
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F)
    (E : Subgroup Y) (hER : E ≤ (Rb : Subgroup Y))
    (hEN : E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEout : ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    (hlin : E.map (modelAct K e) ≤ linearAutGroup 3 F) : False :=
  coverThreeNoInnerDiagLinear_of_planeGen Rb Y₀ h K hK hC hcent hZ F h3F
    (fun _ hBa hB9 hlin' _ => planeGen_of_linearAut outerHeisCore h3F h4 hBa hB9 hlin') e E hER hEN
    hEa hEc hEout hlin

@[expose] def CoverThreeNoInnerDiagLinearFour : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ →
    ∀ (K : Subgroup Y) [K.Normal], Open.IsQuasisimple K →
      Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      (Nat.card (Subgroup.center K)).factorization 3 = 1 →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
      ∀ e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F,
      ∀ E : Subgroup Y, E ≤ (Rb : Subgroup Y) → E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) →
        E.map (modelAct K e) ≤ linearAutGroup 3 F → False

theorem coverThreeNoInnerDiagLinearFour_of_core
    (hcore : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 → OuterHeisCoreAt F) :
    CoverThreeNoInnerDiagLinearFour := by
  intro Y _ _ Rb Y₀ h K _ hK hC hcent hZ F _ _ hF e E hER hEN hEa hEc hEout hlin
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hF]
  exact coverThreeNoInnerDiagLinear_of_planeGen Rb Y₀ h K hK hC hcent hZ F h3F
    (fun _ hBa hB9 hlin' hBout => planeGen_of_linearAut_core (hcore F hF) h3F hBa hB9 hlin' hBout)
    e E hER hEN hEa hEc hEout hlin

theorem coverThreeNoInnerDiagLinear_of_four (h4 : CoverThreeNoInnerDiagLinearFour) :
    CoverThreeNoInnerDiagLinear := by
  intro Y _ _ Rb Y₀ h K _ hK hC hcent hZ F _ _ h3F e E hER hEN hEa hEc hEout hlin
  by_cases hF : 4 < Nat.card F
  · exact coverThreeNoInnerDiagLinear_aux Rb Y₀ h K hK hC hcent hZ F h3F hF e E hER hEN hEa hEc
      hEout hlin
  · have hF2 : 1 < Nat.card F := Finite.one_lt_card
    exact h4 Y Rb Y₀ h K hK hC hcent hZ F (by omega) e E hER hEN hEa hEc hEout hlin

end Main

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
