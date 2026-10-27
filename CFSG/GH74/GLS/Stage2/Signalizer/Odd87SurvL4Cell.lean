module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvL4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympL4Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)
open scoped commutatorElement

theorem FL4.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FL4 Y) : FL4 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hq, hm⟩ := h
  exact ⟨p, f, hp, hf, hp2, hq, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem transport_core_hyp {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {α : MulAut K}
    {α' : MulAut K'} (hαα' : ∀ x, e (α x) = α' (e x)) {XT : Subgroup K}
    (hcomm : Subgroup.closure ((fun x : K => x * (α x)⁻¹) '' (XT : Set K)) = XT)
    (hN : fixSub α ≤ Subgroup.normalizer (XT : Set K)) :
    Subgroup.closure ((fun x : K' => x * (α' x)⁻¹) ''
        ((XT.map e.toMonoidHom : Subgroup K') : Set K')) = XT.map e.toMonoidHom ∧
      fixSub α' ≤ Subgroup.normalizer ((XT.map e.toMonoidHom : Subgroup K') : Set K') := by
  refine ⟨?_, ?_⟩
  · have himg : (fun x : K' => x * (α' x)⁻¹) '' ((XT.map e.toMonoidHom : Subgroup K') : Set K') =
        e.toMonoidHom '' ((fun x : K => x * (α x)⁻¹) '' (XT : Set K)) := by
      rw [Subgroup.coe_map, Set.image_image, Set.image_image]
      refine Set.image_congr fun x _ => ?_
      simp [map_mul, map_inv, hαα']
    rw [himg, ← MonoidHom.map_closure, hcomm]
  · intro y' hy'
    have hy : e.symm y' ∈ fixSub α := by
      have h1 : α' y' = y' := hy'
      show α (e.symm y') = e.symm y'
      apply e.injective
      rw [hαα', MulEquiv.apply_symm_apply, h1]
    have hyN := Subgroup.mem_normalizer_iff.mp (hN hy)
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := hyN (e.symm h')
    simpa [map_mul, map_inv] using this

@[expose] def L4SurvCore : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p₀ f₀ : ℕ), p₀.Prime → p₀ ≠ 2 → Odd f₀ → Nat.card F = p₀ ^ f₀ →
    p₀ ^ f₀ % 8 ≠ 1 → ∀ α : MulAut (projectiveSL 4 F), α * α = 1 → Surv4Orth α →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup (projectiveSL 4 F), IsPGroup p ↥X → X ≠ ⊥ →
      Subgroup.closure ((fun x : projectiveSL 4 F => x * (α x)⁻¹) ''
        (X : Set (projectiveSL 4 F))) = X →
      fixSub α ≤ normalizer (X : Set (projectiveSL 4 F)) → False

theorem cell87Surv_FL4 (hCore : L4SurvCore) : Cell87Surv FL4 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hZ hF hGK
  classical
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  have hzb2 := hd.z2
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKn : K.Normal := layer_normal
  let eq0 : (↥K ⧸ center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hFK : FL4 ↥K := FL4.of_mulEquiv eq0 hF
  let α : MulAut ↥K := layerAut zb
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun s => ?_
    show α (α s) = s
    exact layerAut_layerAut hzb2 s
  have hGKK : ¬ GenericKill ↥K α := by
    intro h
    refine hGK (genericKill_of_mulEquiv eq0 (onCenterQuotient (layerAut zb)) α ?_ h)
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      have h1 : onCenterQuotient (layerAut zb) (QuotientGroup.mk k) =
          QuotientGroup.mk (layerAut zb k) := onCenterQuotient_apply_mk _ _
      rw [h1]
      rfl
  rcases genericKill_or_surv_of_FL4_orth hFK α hα2 with hgk |
    ⟨p0, f0, F, iF, fF, ⟨hp0, hp02, hf01, hf0odd, hq8, hcard⟩, e, α', hαe, hS⟩
  · exact hGKK hgk
  have : Fact p.Prime := ⟨hsig.A.prime⟩
  have hpodd : Odd p := hsig.A.prime.odd_of_ne_two hsig.A.odd
  have hOutK : OutOddCentral ↥K :=
    outOddCentral_of_mulEquiv e.symm (outOddCentral_projectiveSL4 hp0 hp02 hf01 hf0odd hcard)
  have hXK : X ≤ K := by
    refine x_le_layer_of_comm hzb2 hsig.A hsig.op hd.gen fun x hx => ?_
    obtain ⟨n, hn⟩ := hsig.A.pgroup ⟨x, hx⟩
    have hxn : x ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    exact comm_mem_sup_centralizer_of_odd K hOutK x zb (p ^ n) hpodd.pow hxn
  have hfixC : ∀ y ∈ fixSub α, (y : Sec H₀ H₁) ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
    intro y hy
    have h1 : α y = y := hy
    have h2 := congrArg Subtype.val h1
    rw [show ((α y : ↥K) : Sec H₀ H₁) = zb * y * zb⁻¹ from coe_layerAut zb y] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : Sec H₀ H₁) * zb = (zb * y * zb⁻¹) * zb := by rw [h2]
      _ = zb * y := by group
  let XT : Subgroup ↥K := X.subgroupOf K
  have hXp : IsPGroup p ↥XT := hsig.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hXne : XT ≠ ⊥ := by
    intro h
    apply hsig.A.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ XT := hx
    rw [h] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hN : fixSub α ≤ normalizer (XT : Set ↥K) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyN : (y : Sec H₀ H₁) ∈ normalizer (X : Set (Sec H₀ H₁)) :=
      hsig.A.inv _ (Subgroup.mem_top _) (hfixC y hy)
    exact Subgroup.mem_normalizer_iff.mp hyN (x : Sec H₀ H₁)
  have hzN : zb ∈ normalizer (X : Set (Sec H₀ H₁)) := z_mem_normalizer_of_sig4A hsig.A
  have hcomm : Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) = XT := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxA : (x : Sec H₀ H₁) ∈ X := hx
      have hαx : ((α x : ↥K) : Sec H₀ H₁) ∈ X := by
        rw [coe_layerAut]
        exact (Subgroup.mem_normalizer_iff.mp hzN _).mp hxA
      exact XT.mul_mem hx (XT.inv_mem hαx)
    · set T : Subgroup ↥K := Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) with hT
      have hX : X ≤ T.map K.subtype := by
        rw [← hsig.A.comm, Subgroup.commutator_le]
        intro x hx g hg
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hz2' : zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzb2
        rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
        · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
          exact Subgroup.one_mem _
        · rw [zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]
          have hxT : (⟨x, hXK hx⟩ : ↥K) ∈ XT := hx
          refine ⟨(⟨x, hXK hx⟩ : ↥K) * (α ⟨x, hXK hx⟩)⁻¹,
            Subgroup.subset_closure ⟨⟨x, hXK hx⟩, hxT, rfl⟩, ?_⟩
          have hcoe : ((α ⟨x, hXK hx⟩ : ↥K) : Sec H₀ H₁) = zb * x * zb⁻¹ :=
            coe_layerAut zb ⟨x, hXK hx⟩
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
          rw [hcoe, commutatorElement_def, ← hzb]
          group
      intro y hy
      have hyX : (y : Sec H₀ H₁) ∈ X := hy
      obtain ⟨t, ht, hty⟩ := hX hyX
      have : t = y := Subtype.ext hty
      rw [← this]
      exact ht
  obtain ⟨hcomm', hN'⟩ := transport_core_hyp e hαe hcomm hN
  have hα'2 : α' * α' = 1 := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨x, rfl⟩ := e.surjective s
    show α' (α' (e x)) = e x
    rw [← hαe, ← hαe]
    have : α (α x) = x := layerAut_layerAut hzb2 x
    rw [this]
  have hXp' : IsPGroup p ↥(XT.map e.toMonoidHom) :=
    hXp.of_equiv (XT.equivMapOfInjective e.toMonoidHom e.injective)
  have hXne' : XT.map e.toMonoidHom ≠ ⊥ := fun h =>
    hXne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h)
  exact hCore F p0 f0 hp0 hp02 hf0odd hcard hq8 α' hα'2 hS p hsig.A.odd _ hXp' hXne' hcomm' hN'

theorem cell87_FL4 (hInv : InvSec) (hCore : L4SurvCore) : Cell87 FL4 :=
  cell87_FL4_of_surv hInv (cell87Surv_FL4 hCore)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
