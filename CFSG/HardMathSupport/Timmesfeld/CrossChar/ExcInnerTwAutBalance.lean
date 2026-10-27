module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

section Aut

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem le_fixSub_of_aut_component (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {E : Subgroup (MulAut K)} {g : MulAut K}
    (hg : g ∈ localDeltaIn p H E) {e : MulAut K} (he : e ∈ E) (he1 : e ≠ 1)
    {L : Subgroup K} (hLC : L ≤ fixSub e) (hLq : CFSG.IsQuasisimple L)
    (hLsn : (L.subgroupOf (fixSub e)).IsSubnormal) (hLp : ¬ Nat.Coprime p (Nat.card L)) :
    L ≤ fixSub g := by
  set C : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)) with hC
  have hcomm : ∀ x ∈ fixSub e, MulAut.conj x * e = e * MulAut.conj x := fun x hx => by
    have h1 : e * MulAut.conj x * e⁻¹ = MulAut.conj (e x) := mul_conj_mul_inv e x
    rw [mem_fixSub.1 hx] at h1
    calc MulAut.conj x * e = e * MulAut.conj x * e⁻¹ * e := by rw [h1]
      _ = e * MulAut.conj x := by group
  have hXC : (fixSub e).map (MulAut.conj : K →* MulAut K) ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hH ⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)⟩
  have hXn : (((fixSub e).map (MulAut.conj : K →* MulAut K)).subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    have hy := (Subgroup.mem_inf.1 y.2).2
    have hye : (y : MulAut K) * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine ⟨(y : MulAut K) x, ?_, ?_⟩
    ·
      have h1 : (e * (y : MulAut K)) x = ((y : MulAut K) * e) x := by rw [hye]
      rw [MulAut.mul_apply, MulAut.mul_apply, mem_fixSub.1 hx] at h1
      exact mem_fixSub.2 h1
    · change MulAut.conj ((y : MulAut K) x) = (y : MulAut K) * (n : MulAut K) * (y : MulAut K)⁻¹
      rw [← mul_conj_mul_inv, ← hxn]
  have hTC : L.map (MulAut.conj : K →* MulAut K) ≤ C := (Subgroup.map_mono hLC).trans hXC
  have hcompL : CFSG.IsComponent ((L.map (MulAut.conj : K →* MulAut K)).subgroupOf C) := by
    refine ⟨?_, isSubnormal_map_subgroupOf _ hLC hLsn hXC hXn⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L.equivMapOfInjective _ hinj).trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hLq
  exact le_fixSub_of_component hp hinj hg he he1 hTC hcompL hLp

theorem localDeltaIn_eq_bot_of_aut_components_rigid (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {E : Subgroup (MulAut K)} (hE : E ≠ ⊥)
    {S : Set K} (hrig : ∀ δ ∈ H, Nat.Coprime p (orderOf δ) → (∀ s ∈ S, δ s = s) → δ = 1)
    (hcomp : ∀ s ∈ S, ∃ e ∈ E, e ≠ 1 ∧ ∃ L : Subgroup K, s ∈ L ∧ L ≤ fixSub e ∧
      CFSG.IsQuasisimple L ∧ (L.subgroupOf (fixSub e)).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)) :
    localDeltaIn p H E = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hE ((Subgroup.eq_bot_iff_forall E).2 hcon)
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    fun f f' h => MulEquiv.ext (congrFun h)
  have hgH : g ∈ H := (Subgroup.mem_inf.1
    (Balance.gLAPPrimeCoreOf_le_self' _ (le_core_of_mem_localDeltaIn hg he₀ he₀1))).1
  refine Subgroup.mem_bot.2
    (hrig g hgH (coprime_orderOf_of_mem_localDeltaIn hp hg he₀ he₀1) fun s hs => ?_)
  obtain ⟨e, he, he1, L, hsL, hLC, hLq, hLsn, hLp⟩ := hcomp s hs
  exact le_fixSub_of_aut_component hp hinj hH hg he he1 hLC hLq hLsn hLp hsL

end Aut

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_subgroupOf {A B R : Subgroup G} (hBA : B ≤ A)
    (hsn : (R.subgroupOf B).IsSubnormal) :
    ((R.subgroupOf A).subgroupOf (B.subgroupOf A)).IsSubnormal := by
  let φ : ↥B →* ↥(B.subgroupOf A) :=
    { toFun := fun x => ⟨⟨x, hBA x.2⟩, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨y, hyA⟩, hyB⟩
    exact ⟨⟨y, hyB⟩, rfl⟩
  convert hsn.map hφ using 1
  ext ⟨⟨y, hyA⟩, hyB⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hy
    exact ⟨⟨y, hyB⟩, hy, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have h1 : (x : G) = y := congrArg (fun z : ↥(B.subgroupOf A) => ((z : A) : G)) hxy
    rw [← h1]
    exact hx

end Subnormal

end CFSG.HardMathSupport.Timmesfeld.CrossChar
