module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicRest
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGamma
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.AGLEmbedding

@[expose] def OPrimeCoreLeTwoAt (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ s : K, orderOf s = p →
    Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))) ≤ 2

theorem OPrimeCoreLeTwoAt.of_mulEquiv {p : ℕ} {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : OPrimeCoreLeTwoAt p K') : OPrimeCoreLeTwoAt p K := by
  intro s hs
  have hmap := map_glaPPrimeCoreOf_of_injective p e.toMonoidHom e.injective
    (Subgroup.centralizer ({s} : Set K))
  have hc := map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at hc
  rw [hc] at hmap
  have h' := h (e s) (by rw [← hs]; exact orderOf_injective e.toMonoidHom e.injective s)
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
  exact h'

theorem innerAut_eq_top_of_allInner {K : Type*} [Group K]
    (h : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) : innerAut K = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨g, hg⟩ := h σ
  exact ⟨g, hg.symm⟩

theorem innerAut_eq_top_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : innerAut K' = ⊤) : innerAut K = ⊤ := by
  refine innerAut_eq_top_of_allInner fun σ => ?_
  have : MulAut.congr e σ ∈ innerAut K' := h ▸ Subgroup.mem_top _
  obtain ⟨g', hg'⟩ := this
  refine ⟨e.symm g', ?_⟩
  apply (MulAut.congr e).injective
  rw [← hg']
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem sporadicTwoPairHolds_of_gamma (hB : SporadicBridges) {name : TauCeti.SporadicName}
    {p : ℕ} (hp : p.Prime) (hgen : SporGammaOneAt name p)
    (hinn : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier name) → innerAut S = ⊤)
    (hp3 : ¬ p ^ 3 ∣ Nat.card (NativeSporadic.Carrier name))
    (hO : OPrimeCoreLeTwoAt p (NativeSporadic.Carrier name)) : SporadicTwoPairHolds name p := by
  intro S _ _ _ hnab he
  obtain ⟨e⟩ := he
  refine isLocallyBalancedAbs_two_of_gamma hp (center_eq_bot_of_isSimpleGroup hnab)
    (hinn S ⟨e⟩) (by rw [Nat.card_congr e.toEquiv]; exact hp3) ?_
    (fun s hs => OPrimeCoreLeTwoAt.of_mulEquiv e hO s hs)
  intro T
  exact hgen S ⟨e.trans (hB name).some⟩ T

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
