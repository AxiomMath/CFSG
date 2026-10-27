module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvGlue
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvInst
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.AutU42
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpacePi
public import CFSG.HardMathSupport.Timmesfeld.Proving.PlaneKernel
public import CFSG.HardMathSupport.Timmesfeld.Proving.TranvCase
public import CFSG.LocalAnalysis.GLTheoremB.Input27_9_3Proof
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.AutStated
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvUnpack
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem orthJ_top_eq_elementaryGroup {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) : orthJ Q ⊤ = elementaryGroup Q := by
  refine le_antisymm (orthJ_le_elementaryGroup Q _) ?_
  exact elementaryGroup_le_of_eichler_mem fun u w _ _ =>
    eichler_mem_orthJ Submodule.mem_top Submodule.mem_top

theorem piDataOf_self {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {p : ℕ}
    (e : ↥K ≃* ↥(elementaryGroup Q)) (h4 : 4 ≤ finrank (ZMod 2) V)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g)) →
        IsSimpleGroup ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          (∃ a b : ↥(orthJ Q (fixSub (Subgroup.zpowers g))), a * b ≠ b * a) ∧
          p ∣ Nat.card ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧
            IsOmegaTwo ε' (n' + 1) ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
            HasFixedPointFreeOrder ε' n' p) :
    PiDataOf p ↥K := by
  have hfix : fixSub (Subgroup.zpowers (1 : V ≃ₗ[ZMod 2] V)) = ⊤ := by
    ext v
    rw [mem_fixSub_zpowers]
    simp
  have := hPi 1 (one_mem _) (one_pow _) (by rw [hfix, finrank_top]; exact h4)
  rw [hfix, orthJ_top_eq_elementaryGroup] at this
  exact PiDataOf.of_mulEquiv e.symm this

theorem transv_generic {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B T D : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (e : ↥K ≃* ↥(elementaryGroup Q)) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hTK : ¬ T ≤ Subgroup.centralizer (K : Set X))
    (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V)
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenterO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ x ∈ elementaryGroup Q, g * x = x * g) → g = 1)
    (hfix : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ x ∈ E, x ^ p = 1) → ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g)) →
        IsSimpleGroup ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          (∃ a b : ↥(orthJ Q (fixSub (Subgroup.zpowers g))), a * b ≠ b * a) ∧
          p ∣ Nat.card ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧
            IsOmegaTwo ε' (n' + 1) ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
            HasFixedPointFreeOrder ε' n' p)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v : V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0) (hf0 : f ≠ 0) (htv : ∀ x, t x = x + f x • v)
    (hTact : ∀ x ∈ T, ActsAsConj e x 1 ∨ ActsAsConj e x t) (hTex : ∃ x ∈ T, ActsAsConj e x t) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ CFSG.LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  by_cases hrange : Nat.card (Proving.planeAct (hDB.trans hBN)).range = p ^ 2
  · exact transv_case_two hp hp2 hB hBN hTN hBT hDB hQ hAut hcenterO hfix hPi ht hv hf0 htv hTact
      hTex hrange
  · have hlt : Nat.card (Proving.planeAct (hDB.trans hBN)).range < p ^ 2 := by
      obtain ⟨j, hj, hj'⟩ := Proving.planeAct_range_card_eq_pow hp (hDB.trans hBN) hD
      rw [hj']
      have hj2 : j ≠ 2 := fun h => hrange (by rw [hj', h])
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    obtain ⟨d, hdD, hd1, hdK⟩ := Proving.exists_ne_one_centralizes_of_range_lt
      (hDB.trans hBN) hD hlt
    have hpi := piDataOf_self e h4 hPi
    obtain ⟨hs, hnc, hdvd, hΩ⟩ := hpi
    have := hs
    refine Proving.transv_conclusion_of_mem_centralizer ?_ ?_ (hBN) hTN hTK hdD hd1 ?_
    · exact Proving.glaPComponent_self hKq (glaPPrimeCore_eq_bot_of_simple hp hdvd)
    · exact isPiGroup_of_simple_data hp hnc hdvd hΩ
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hdK k hk

theorem transv_generic_actsLike {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K B T D : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {G : Type*} [Group G]
    (e₀ : ↥K ≃* G) (e₁ : G ≃* ↥(elementaryGroup Q)) {c : MulAut G}
    (hcard : Nat.card (inducedAutGroup T K) = 2)
    (hact : ActsLike T K e₀ (Subgroup.zpowers c)) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V)
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenterO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ x ∈ elementaryGroup Q, g * x = x * g) → g = 1)
    (hfix : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ x ∈ E, x ^ p = 1) → ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g)) →
        IsSimpleGroup ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          (∃ a b : ↥(orthJ Q (fixSub (Subgroup.zpowers g))), a * b ≠ b * a) ∧
          p ∣ Nat.card ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧
            IsOmegaTwo ε' (n' + 1) ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
            HasFixedPointFreeOrder ε' n' p)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v : V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0) (hf0 : f ≠ 0) (htv : ∀ x, t x = x + f x • v)
    (hc : ∀ y : G, ((e₁ (c y) : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) =
      t * (e₁ y : V ≃ₗ[ZMod 2] V) * t⁻¹) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧
        CFSG.LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  obtain ⟨-, hcases, x0, hx0, hx0c⟩ := actsLike_cases hTN e₀ hcard hact
  refine transv_generic hp hp2 (e₀.trans e₁) hKq hB hBN hTN hBT
    (Proving.not_le_centralizer_of_natCard_inducedAutGroup hcard) hDB hD hQ h4 hAut hcenterO hfix
    hPi ht hv hf0 htv ?_ ⟨x0, hx0, actsAsConj_of_eq (hTN hx0) e₀ e₁ hx0c hc⟩
  intro x hx
  rcases hcases x hx with h | h
  · exact Or.inl (actsAsConj_one_of_eq_one (hTN hx) e₀ e₁ h)
  · exact Or.inr (actsAsConj_of_eq (hTN hx) e₀ e₁ h hc)

open CFSG.LieType.Universal.Spin in
theorem transv_plus {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B T D : Subgroup X} {n : ℕ} (hn : 1 ≤ n) (hfpf : HasFixedPointFreeOrder true n p)
    (e : ↥K ≃* ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))
    (hcard : Nat.card (inducedAutGroup T K) = 2)
    (hLike : ActsLikeTransvection (StatedQuadPlus (n + 1) (ZMod 2)) T K e)
    (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧
        CFSG.LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfpf
  have hn2 : 2 ≤ n := by
    by_contra h
    obtain rfl : n = 1 := by omega
    simp only [typeSign, ite_true] at hdvd
    have : p ∣ 1 := by simpa using hdvd
    exact hp.ne_one (Nat.dvd_one.1 this)
  have hm : 3 ≤ n + 1 := by omega
  have hstd : IsStdSpace true (quadPlus (n + 1) (ZMod 2)) (n + 1) :=
    ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  have hnd := nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)
  obtain ⟨t, htN, hQt, ⟨v, f, hv, hf0, -, htr⟩, hact⟩ := hLike
  refine transv_generic_actsLike hp hp2 e (statedOmegaPlusEquiv hm) hcard hact hKq hB hBN hTN hBT
    hDB hD hnd ?_ (inner_of_mulEquiv (statedOmegaPlusEquiv hm) (aut_inner_plus hp hp2 hn hfpf))
    ?_ ?_ ?_ (t := toLinEquiv _ _ t) ?_ hv hf0 ?_ (statedOmegaPlusEquiv_conj hm t htN)
  · rw [finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  · intro g hg hc
    exact eq_one_of_commute_elementaryGroup_of_isPlusSpace hm hstd hg hc
  · intro E hE hexp
    exact exists_fixed_hypPair_of_hasFpf hnd hp hp2 hn hfpf hstd hE hexp
  · intro g hg hgp hdim
    exact piData_of_fixedSpace hnd hstd hp hp2 hn hfpf hg hgp hdim
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    have := hQt x
    rw [quadPlus_apply, toLinEquiv_apply]
    rw [quadPlus_apply]
    exact this
  · intro x
    exact htr x

open CFSG.LieType.Universal.Spin in
theorem transv_minus {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B T D : Subgroup X} {n : ℕ} (hn : 1 ≤ n) (hfpf : HasFixedPointFreeOrder false n p)
    (e : ↥K ≃* ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))
    (hcard : Nat.card (inducedAutGroup T K) = 2)
    (hLike : ActsLikeTransvection (StatedQuadMinus (n + 1) (ZMod 2) 1 1) T K e)
    (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧
        CFSG.LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  have hm : 2 ≤ n + 1 := by omega
  have hstd : IsStdSpace false (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) :=
    ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have hfr : finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) = 2 * n + 2 := by
    rw [finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  obtain ⟨t, htN, hQt, ⟨v, f, hv, hf0, -, htr⟩, hact⟩ := hLike
  refine transv_generic_actsLike hp hp2 e (statedOmegaMinusEquiv hm) hcard hact hKq hB hBN hTN hBT
    hDB hD hnd ?_ (inner_of_mulEquiv (statedOmegaMinusEquiv hm)
      (aut_inner_minus autU42Five hp hp2 hn hfpf))
    ?_ ?_ ?_ (t := toLinEquiv _ _ t) ?_ hv hf0 ?_ (statedOmegaMinusEquiv_conj hm t htN)
  · rw [hfr]
    omega
  · intro g hg hc
    exact eq_one_of_commute_eichler hnd (by rw [hfr]; omega) fun u w _ _ =>
      hc _ (eichler_mem_elementaryGroup _ u w)
  · intro E hE hexp
    exact exists_fixed_hypPair_of_hasFpf hnd hp hp2 hn hfpf hstd hE hexp
  · intro g hg hgp hdim
    exact piData_of_fixedSpace hnd hstd hp hp2 hn hfpf hg hgp hdim
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    have := hQt x
    rw [quadMinus_apply, toLinEquiv_apply]
    rw [quadMinus_apply]
    exact this
  · intro x
    exact htr x

theorem input27_9_3Transv_proved : CFSG.LocalAnalysis.GLTheoremB.Input27_9_3Transv := by
  intro X _ _ p hp hp2 K hK B hB hBN T _ hTN hBT hact D hDB hD
  obtain ⟨n, hn, ⟨hfpf, e, hcard, hLike⟩ | ⟨hfpf, e, hcard, hLike⟩⟩ := hact
  · exact transv_plus hp hp2 hn hfpf e hcard hLike hK.2.2 hB hBN hTN hBT hDB hD.2
  · exact transv_minus hp hp2 hn hfpf e hcard hLike hK.2.2 hB hBN hTN hBT hDB hD.2

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
