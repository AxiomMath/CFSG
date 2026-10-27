module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.LieType.SeitzGeneration.SeitzStatus
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompGenInner
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2Conj
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFixedNC
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerGen
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwOuterHeis
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwToral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  (not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_twistedE6)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (catEquiv_twistedE6_of_field)

set_option linter.unusedSectionVars false

section Inner

theorem twLayer_inner
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} (hK3 : ringChar K ≠ 3)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEi : E ≤ twistedE6Inn K σ)
    (hs : ∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s ∈ E) (i : Fin 3) :
    L i ≤ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype :=
  twLayer_le_seitzHyperGamma (twLayerModel_of_torusModel twTorusModel_holds)
    twFixedNonCentral_holds twToralPlane_holds twInnerHeisPlane_holds twOuterHeisPlane_holds
    hK3 hσ hKq h3 hq2 hL hE hcard (hEi.trans le_sup_left) hs i

theorem twTorus_inner {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hline : TwE6ThreeA2Line K σ h₀ L T n) {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ twistedE6Inn K σ)
    (hs : ∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s ∈ E) :
    T ≤ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ ⨆ i, L i := by
  obtain ⟨s₀, hs₀, hsig⟩ := hs
  obtain ⟨ℓ, f, h, ρ, hqℓ, ⟨hinj, hrange, -⟩, htor⟩ :=
    twTorusModel_holds K σ q hK3 hσ hKq h3 hq2 h₀ L T n hline
  have h3' : 3 ∣ ℓ ^ f + 1 := by rw [hqℓ]; exact h3
  refine twTorusGroup_le_seitzHyperGamma_sup h3' hline hinj hrange htor hE hEc
    (hEi.trans le_sup_left) hs₀ hsig ?_
  intro ε hε
  have hcomm : ε * MulAut.conj s₀ = MulAut.conj s₀ * ε :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hε⟩ : E) ⟨_, hsig⟩)
  exact twLayer_exists_shift_frames hline hs₀ (hE.2 ε hε) hcomm ρ hrange

theorem innerPlane_of_kfact
    (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ) (hK3 : ringChar K ≠ 3)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ twistedE6Inn K σ)
    (P : Subgroup (MulAut (twistedE6RootGroup K σ))) (hPE : P ≤ E) (hPc : Nat.card P = 3 ^ 2)
    (hP24 : TwE6InnerAll24 K σ P) :
    seitzHyperGamma 3 E = ⊤ := by
  have hComp := twE6ThreeCompGenInner_holds
  classical
  obtain ⟨h₀, L, T, n, hline⟩ := twE6ThreeA2LineStmt_holds K σ q hK3 hσ hKq h3 hq2
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq (by omega)
  let qp : TauCeti.PrimePower := ⟨ringChar K, f, hp, by omega⟩
  have hqp : qp.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hv : (TauCeti.LieTypeIndex.twistedE6 qp).Valid := TauCeti.LieTypeIndex.valid_twistedE6 qp
  obtain ⟨e⟩ := catEquiv_twistedE6_of_field qp hv K (hqp ▸ hKq) σ (hqp ▸ hσ)
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) ⟨_, hv⟩ e.symm
    (by
      show 3 ≠ (TauCeti.LieTypeIndex.twistedE6 qp).characteristic
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact fun h => hK3 h.symm)
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 qp))
    (hE.mono hPE) hPc
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro s ⟨φ, hφP, hφ1, hφs⟩
  have hφE : φ ∈ E := hPE hφP
  obtain ⟨v, rfl⟩ := hEi hφE
  have hv1 : v ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have hv3 : v ^ 3 = 1 := by
    have hc : v ^ 3 ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ x)
        (show MulAut.conj (v ^ 3) = 1 by rw [map_pow]; exact hE.2 _ hφE)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    rw [exceptional_fixed_center_trivial TwistTag.E6 K σ] at hc
    exact Subgroup.mem_bot.1 hc
  obtain ⟨g, hgC, hg⟩ := twE6ThreeA2Conj_holds K σ q hK3 hσ hKq h3 hq2
    (v : ModGL TwistTag.E6.tag K) v.2 h₀ hline.h₀_mem
    (by have := congrArg Subtype.val hv3; simpa using this) hline.h₀_pow
    (hP24 v hφP hv1) hline.finrank_fixed
  obtain ⟨g', hg'⟩ : ∃ g' : twistedE6RootGroup K σ, (g' : ModGL TwistTag.E6.tag K) = g :=
    ⟨⟨g, hgC⟩, rfl⟩
  have hgv : g' * v * g'⁻¹ = ⟨h₀, hline.h₀_mem⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg']
    exact hg
  obtain ⟨c, hc⟩ : ∃ c : MulAut (twistedE6RootGroup K σ), c = MulAut.conj g' := ⟨_, rfl⟩
  have hcI : c ∈ twistedE6Inn K σ := by
    rw [hc]
    exact ⟨g', rfl⟩
  have hE'a : IsElemAbelian 3 (E.map (MulAut.congr c).toMonoidHom) := hE.map _
  have hE'c : Nat.card (E.map (MulAut.congr c).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr c).injective, hEc]
  have hE'i : E.map (MulAut.congr c).toMonoidHom ≤ twistedE6Inn K σ := by
    rintro _ ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply]
    exact mul_mem (mul_mem hcI (hEi hε)) (inv_mem hcI)
  have hP'E : P.map (MulAut.congr c).toMonoidHom ≤ E.map (MulAut.congr c).toMonoidHom :=
    Subgroup.map_mono hPE
  have hP'c : Nat.card (P.map (MulAut.congr c).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr c).injective, hPc]
  have hP'24 : TwE6InnerAll24 K σ (P.map (MulAut.congr c).toMonoidHom) := by
    rw [hc]
    exact twE6InnerAll24_map_conj g' hP24
  have hhP : ∃ s₀ : twistedE6RootGroup K σ, (s₀ : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s₀ ∈ P.map (MulAut.congr c).toMonoidHom := by
    refine ⟨⟨h₀, hline.h₀_mem⟩, rfl, MulAut.conj v, hφP, ?_⟩
    rw [congr_toMonoidHom_apply, hc, ← hgv, map_mul, map_mul, map_inv]
  have hh : ∃ s₀ : twistedE6RootGroup K σ, (s₀ : ModGL TwistTag.E6.tag K) = h₀ ∧
      MulAut.conj s₀ ∈ E.map (MulAut.congr c).toMonoidHom := by
    obtain ⟨s₀, hs₀, hs₀P⟩ := hhP
    exact ⟨s₀, hs₀, hP'E hs₀P⟩
  have hU : ⨆ i, L i ≤ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype :=
    iSup_le fun i => twLayer_inner hK3 hσ hKq h3 hq2 hline hE'a hE'c hE'i hh i
  have hTor := twTorus_inner hK3 hσ hKq h3 hq2 hline hE'a hE'c hE'i hh
  have hCmp := hComp K σ q hK3 hσ hKq h3 hq2 h₀ L T n hline _ hE'a hE'c hE'i _ hP'E hP'c hP'24
    hhP
  have hTU : T ⊔ ⨆ i, L i ≤ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype := sup_le (hTor.trans (sup_le le_rfl hU)) hU
  have hn : n ∈ (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
      (twistedE6RootGroup K σ).subtype := (sup_le le_rfl hTU) hCmp
  have hCent : twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} ≤
      (seitzHyperGamma 3 (E.map (MulAut.congr c).toMonoidHom)).map
        (twistedE6RootGroup K σ).subtype := by
    rw [hline.centralizer_eq]
    exact sup_le hTU ((Subgroup.zpowers_le).2 hn)
  have hcomm : (⟨h₀, hline.h₀_mem⟩ : twistedE6RootGroup K σ) * c s =
      c s * ⟨h₀, hline.h₀_mem⟩ := by
    have hvs : v * s = s * v := by
      have h := hφs
      simp only [MulAut.conj_apply] at h
      exact mul_inv_eq_iff_eq_mul.1 h
    rw [← hgv, hc, MulAut.conj_apply]
    calc g' * v * g'⁻¹ * (g' * s * g'⁻¹) = g' * (v * s) * g'⁻¹ := by group
      _ = g' * (s * v) * g'⁻¹ := by rw [hvs]
      _ = g' * s * g'⁻¹ * (g' * v * g'⁻¹) := by group
  have hcs : ((c s : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈
      twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    refine Subgroup.mem_inf.2 ⟨(c s).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have := congrArg Subtype.val hcomm
    simpa only [Subgroup.coe_mul] using this
  obtain ⟨y, hy, hyc⟩ := hCent hcs
  have hyc' : y = c s := Subtype.ext hyc
  rw [hyc'] at hy
  exact mem_seitzHyperGamma_of_congr hy

end Inner

section Closed

theorem innerPlane_of_core (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEi : E ≤ twistedE6Inn K σ)
    (P : Subgroup (MulAut (twistedE6RootGroup K σ))) (hPE : P ≤ E) (hPc : Nat.card P = 3 ^ 2)
    (hP24 : TwE6InnerAll24 K σ P) :
    seitzHyperGamma 3 E = ⊤ :=
  innerPlane_of_kfact CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    K σ q hK3 hσ hKq h3 hq2 E hE hEc hEi P hPE hPc hP24

end Closed

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
