module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.CGT.PushingUpLit.BHS6.SixFour
public import CFSG.CGT.PushingUpLit.BHS7.FifteenComp

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isPGroup_inf_centralizer_of_comm_le {G E V : Subgroup Γ} (hG : CharTwo G) (hEG : E ≤ G)
    (hcomm : ⁅E, pCoreOf 2 G⁆ ≤ V) :
    IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup Γ := pCoreOf 2 G with hW
  have hW2 : IsPGroup 2 ↥W := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G
  rw [IsPGroup.iff_orderOf]
  intro g
  have hgE : (g : Γ) ∈ E := g.2.1
  have hgc : (g : Γ) ∈ Subgroup.centralizer (V : Set Γ) := g.2.2
  have hn0 : orderOf (g : Γ) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  set y : Γ := (g : Γ) ^ (2 ^ k) with hy
  have hord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hyK : y ∈ E ⊓ Subgroup.centralizer (V : Set Γ) :=
    (E ⊓ Subgroup.centralizer (V : Set Γ)).pow_mem g.2 _
  set R₀ : Subgroup Γ := Subgroup.zpowers y with hR₀
  have hR₀E : R₀ ≤ E := (Subgroup.zpowers_le).2 hyK.1
  have hR₀G : R₀ ≤ G := hR₀E.trans hEG
  have hR₀C : R₀ ≤ Subgroup.centralizer (V : Set Γ) := (Subgroup.zpowers_le).2 hyK.2
  have hRnorm : R₀ ≤ Subgroup.normalizer (W : Set Γ) := hR₀G.trans (le_normalizer_pCoreOf_self' G)
  have hcard : Nat.card R₀ = m := by rw [hR₀, Nat.card_zpowers, hord]
  obtain ⟨j, hj⟩ := hW2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R₀) (Nat.card W) := by
    rw [hcard, hj]
    exact Nat.Coprime.pow_right _ hm.coprime_two_right
  have hWR : ⁅W, R₀⁆ ≤ V := by
    calc ⁅W, R₀⁆ ≤ ⁅W, E⁆ := Subgroup.commutator_mono le_rfl hR₀E
      _ = ⁅E, W⁆ := Subgroup.commutator_comm _ _
      _ ≤ V := hcomm
  have hVR : ⁅V, R₀⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hR₀C
  have hdouble : ⁅⁅W, R₀⁆, R₀⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅⁅W, R₀⁆, R₀⁆ ≤ ⁅V, R₀⁆ := Subgroup.commutator_mono hWR le_rfl
      _ = ⊥ := hVR
  have hWR1 : ⁅W, R₀⁆ = ⊥ :=
    GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot W R₀ hRnorm hcop
      hdouble
  have hRW : R₀ ≤ Subgroup.centralizer (W : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hWR1
  have hyW : y ∈ W := hG ⟨hR₀G (Subgroup.mem_zpowers y), hRW (Subgroup.mem_zpowers y)⟩
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.1 hW2) ⟨y, hyW⟩
  have hs' : orderOf y = 2 ^ s := by
    have h1 : orderOf y = orderOf (⟨y, hyW⟩ : ↥W) := Subgroup.orderOf_coe ⟨y, hyW⟩
    rw [h1, hs]
  have hs0 : s = 0 := by
    by_contra hne
    have h2 : 2 ∣ m := by
      rw [← hord, hs']
      exact dvd_pow_self 2 hne
    exact absurd (Nat.odd_iff.1 hm) (by omega)
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe, hkm]
  have : m = 1 := by rw [← hord, hs', hs0, pow_zero]
  rw [this, mul_one]

theorem le_of_isPGroup_of_normal_sylow {R Q X : Subgroup Γ} (hQ : IsSylowTwoOf Q R)
    (hQn : R ≤ Subgroup.normalizer (Q : Set Γ)) (hXR : X ≤ R) (hX : IsPGroup 2 ↥X) : X ≤ Q := by
  obtain ⟨S, hS, hXS⟩ := B6.exists_isSylowTwoOf_ge hX hXR
  obtain ⟨g, hg, hgS⟩ := B6.isSylowTwoOf_exists_conj hS hQ
  have h1 : S = B6.conjSub g⁻¹ Q := by
    rw [hgS, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have h2 : B6.conjSub g⁻¹ Q = Q :=
    B6.conjSub_eq_self ((Subgroup.normalizer (Q : Set Γ)).inv_mem (hQn hg))
  rw [h1, h2] at hXS
  exact hXS

omit [Finite Γ] in
theorem comm_mem_of_forall_gen {G V W : Subgroup Γ} (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    {𝓕 : Set (Subgroup Γ)} (hFG : ∀ F ∈ 𝓕, F ≤ G)
    (hF : ∀ F ∈ 𝓕, ∀ f ∈ F, ∀ q ∈ W, ⁅f, q⁆ ∈ V) :
    ∀ e ∈ (sSup 𝓕 : Subgroup Γ), ∀ q ∈ W, ⁅e, q⁆ ∈ V := by
  let SS : Subgroup Γ :=
    { carrier := {e | e ∈ G ∧ ∀ q ∈ W, ⁅e, q⁆ ∈ V}
      one_mem' := ⟨G.one_mem, fun z _ => by simp [V.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨G.mul_mem ha hb, fun z hz => ?_⟩
        have e : ⁅a * b, z⁆ = a * ⁅b, z⁆ * a⁻¹ * ⁅a, z⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVn ha) _).mp (hb' z hz)) (ha' z hz)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨G.inv_mem ha, fun z hz => ?_⟩
        have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (hVn (G.inv_mem ha)) _).mp
          (V.inv_mem (ha' z hz))
        simpa using h1 }
  have hle : (sSup 𝓕 : Subgroup Γ) ≤ SS := sSup_le fun F hF' e he => ⟨hFG F hF' he, hF F hF' e he⟩
  intro e he q hq
  exact (hle he).2 q hq

end CFSG.CGT.PushingUpLit.SYMB
