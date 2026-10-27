module

public import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.Steps.G64Tools
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.Goldschmidt.Steps.G62Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter

namespace G64

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem benderM_eq_singleton (hG : GoldSetting G S A) {s : G} (hs : s ≠ 1) {H : Subgroup G}
    (h : ∀ K ∈ benderM s, K = H) : benderM s = {H} := by
  obtain ⟨K, hK⟩ := G62.benderM_nonempty hG hs
  ext L
  refine ⟨fun hL => h L hL, fun hL => ?_⟩
  rw [Set.mem_singleton_iff] at hL
  rw [hL, ← h K hK]
  exact hK

end G64

theorem G64_of (h31 : S_G31) (h38 : S_G38) (h51 : S_G51) (h61 : S_G61) (h62 : S_G62)
    (h63 : S_G63) : S_G64 := by
  intro G _ _ S A hG a ha ha1 H hH
  have hsimple := hG.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHco := isCoatom_of_mem_benderM hH
  have hAH : A ≤ H := G63.le_of_mem_benderM hG ha hH
  have haH : a ∈ H := hAH ha
  have hsq : ∀ b ∈ A, b * b = 1 := fun b hb => by rw [← pow_two]; exact hG.elem.2 b hb
  have haord : orderOf a = 2 := orderOf_eq_prime (hG.elem.2 a ha) ha1
  have hCH := centralizer_le_of_mem_benderM hH
  have haF : a ∈ generalizedFittingSubgroupOf H := by
    by_contra haF
    obtain ⟨A', hS, -, hAA'⟩ := G63.exists_sstar hG hHco.1
    have haA' : a ∈ A' := hAA' ⟨ha, haH⟩
    obtain ⟨p, hp, hp2, hpa⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      refine haF (G64.mem_fstar_of_forall_centralizer h31 hS haA' fun q hq hq2 => ?_)
      have h := hcon q hq hq2
      rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at h
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => h x hx
    set P₀ := qCoreOf (fstarZero H) p with hP₀def
    have hP₀a := G64.commutator_qCoreOf_fstarZero_ne_bot hp hp2 haH haord hpa
    have hAP₀ : A ≤ Subgroup.normalizer (P₀ : Set G) :=
      hAH.trans (le_normalizer_of_isNormalIn (G63.qCoreOf_fstarZero_isNormalIn H p))
    have hP₀odd : Odd (Nat.card P₀) := G62.odd_card_of_isPGroup hp hp2 (qCoreOf_isPGroup _ p)
    obtain ⟨A₁, hA₁A, hidx, hA₁⟩ := G62.exists_hyperplane_commutator_ne_bot hG.elem ha ha1 hAP₀
      hP₀odd (by rwa [Subgroup.commutator_comm])
    have hM : ∀ a₁ ∈ A₁, a₁ ≠ 1 → benderM a₁ = {H} := by
      intro a₁ ha₁ ha₁1
      refine G64.benderM_eq_singleton hG ha₁1 fun H₁ hH₁ => ?_
      by_contra hne
      have hle : P₀ ⊓ Subgroup.centralizer (A₁ : Set G) ≤ P₀ ⊓ H₁ :=
        inf_le_inf_left _ ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₁)).trans
          (centralizer_le_of_mem_benderM hH₁))
      have hQ1 : P₀ ⊓ H₁ ≠ ⊥ := by
        intro h
        apply hA₁
        have h0 : P₀ ⊓ Subgroup.centralizer (A₁ : Set G) = ⊥ := le_bot_iff.mp (h ▸ hle)
        rw [h0, Subgroup.commutator_bot_right]
      obtain ⟨⟨-, hQa⟩, -⟩ := h63 G S A hG a ha ha1 H hH p hp hp2 (Or.inl hpa) a₁ (hA₁A ha₁)
        ha₁1 H₁ hH₁ hne hQ1
      apply hA₁
      rw [Subgroup.commutator_comm]
      exact le_bot_iff.mp (hQa ▸ Subgroup.commutator_mono hle le_rfl)
    obtain ⟨-, hA₁a⟩ := h61 G S A hG a ha ha1 H hH A₁ hA₁A hidx hM
    exact hA₁ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((le_of_eq hA₁a.symm).trans (Subgroup.le_centralizer_iff.mp inf_le_right)))
  refine ⟨haF, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp, hp2, h3⟩, hA4⟩ := hcon
  have h3' : 3 ≤ CFSG.Open.pRank p (qCoreOf H p) := h3
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set P₀ := qCoreOf (fstarZero H) p with hP₀def
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hP₀p : IsPGroup p P₀ := qCoreOf_isPGroup _ p
  have hP₀P : P₀ ≤ P := G63.qCoreOf_fstarZero_le H p
  have hHP₀ : H ≤ Subgroup.normalizer (P₀ : Set G) :=
    le_normalizer_of_isNormalIn (G63.qCoreOf_fstarZero_isNormalIn H p)
  have hU := G63.uniquenessA_of h51 hG ha ha1 hH hp hp2 (Or.inr h3')
  have hP₀nc := G64.not_isCyclic_qCoreOf_fstarZero hp hp2 h3'
  have hP1 : P ≠ ⊥ := fun h => hP₀nc (G63.isCyclic_of_le (h ▸ inferInstance) hP₀P)
  have hFH := G63.not_isPGroup_fstar h62 hG ha ha1 hH hp hp2 hP1
  have hAP₀ : A ≤ Subgroup.normalizer (P₀ : Set G) := hAH.trans hHP₀
  obtain ⟨B, hBA, hBcard, hYnc⟩ :=
    G64.exists_noncyclic_centralizer hp hp2 hG.elem hG.ne_bot hAP₀ hP₀p hP₀nc
  set Y := P₀ ⊓ Subgroup.centralizer (B : Set G) with hYdef
  set A₀ := A ⊓ Subgroup.centralizer (Y : Set G) with hA₀def
  have hYP₀ : Y ≤ P₀ := inf_le_left
  have hBA₀ : B ≤ A₀ := le_inf hBA (Subgroup.le_centralizer_iff.mp inf_le_right)
  have hAFY : ∀ b ∈ A, b ∈ generalizedFittingSubgroupOf H → b ∈ A₀ := fun b hb hbF =>
    ⟨hb, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hYP₀.trans hP₀P))
      (G64.mem_centralizer_qCoreOf_of_mem_fstar hbF (hsq b hb) hp hp2)⟩
  have haA₀ : a ∈ A₀ := hAFY a ha haF
  have hYC : ∀ a₀ ∈ A₀, Y ≤ Subgroup.centralizer ({a₀} : Set G) := fun a₀ ha₀ y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp ha₀.2) y hy)
  have hYp : IsPGroup p Y := hP₀p.to_le hYP₀
  have hM₀ : ∀ a₀ ∈ A₀, a₀ ≠ 1 → benderM a₀ = {H} := by
    intro a₀ ha₀ ha₀1
    refine G64.benderM_eq_singleton hG ha₀1 fun H₀ hH₀ => ?_
    by_contra hne
    have hYH₀ : Y ≤ H₀ := (hYC a₀ ha₀).trans (centralizer_le_of_mem_benderM hH₀)
    have hQ1 : P₀ ⊓ H₀ ≠ ⊥ := fun h =>
      hYnc ((le_bot_iff.mp (h ▸ le_inf hYP₀ hYH₀)) ▸ inferInstance)
    obtain ⟨-, hcyc⟩ := h63 G S A hG a ha ha1 H hH p hp hp2 (Or.inr h3') a₀ ha₀.1 ha₀1 H₀ hH₀
      hne hQ1
    exact hYnc (G63.isCyclic_of_le hcyc (le_inf hYP₀ hYH₀))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    mem_normalizer_inf (hAP₀ hb) (Bender35.mem_normalizer_centralizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (G63.commute_of_mem hG (hBA hx) hb))))
  have hY1 : Y ≠ ⊥ := fun h => hYnc (h ▸ inferInstance)
  obtain ⟨A₁, hA₁A, hidx, hQ1⟩ := G64.exists_hyperplane_inf_ne_bot hG.elem hG.ne_bot hAY
    (G62.odd_card_of_isPGroup hp hp2 hYp) hY1
  set Q := Y ⊓ Subgroup.centralizer (A₁ : Set G) with hQdef
  have hQY : Q ≤ Y := inf_le_left
  have hQP₀ : Q ≤ P₀ := hQY.trans hYP₀
  have hQp : IsPGroup p Q := hYp.to_le hQY
  have hQH₁ : ∀ a₁ ∈ A₁, ∀ H₁ ∈ benderM a₁, Q ≤ H₁ := fun a₁ ha₁ H₁ hH₁ =>
    inf_le_right.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₁)).trans
      (centralizer_le_of_mem_benderM hH₁))
  have hnotall : ¬ ∀ a₁ ∈ A₁, a₁ ≠ 1 → benderM a₁ = {H} := fun h =>
    hA4 (h61 G S A hG a ha ha1 H hH A₁ hA₁A hidx h).1
  by_cases hA₀c : IsCyclic A₀
  ·
    have hA₀card : Nat.card A₀ ≤ 2 := by
      have hexp : Monoid.exponent A₀ ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hG.elem.2 x x.2.1)
      rw [IsCyclic.exponent_eq_card] at hexp
      exact Nat.le_of_dvd two_pos hexp
    have hA8 : Nat.card A = 8 := by
      have h4 := G53.four_le_card_of_goldSetting hG
      have hBle : Nat.card B ≤ 2 := (Subgroup.card_le_of_le hBA₀).trans hA₀card
      have hA2 : IsPGroup 2 A := IsPGroup.of_exponent_dvd_pow (n := 1) (by
        rw [pow_one]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hG.elem.2 x x.2))
      obtain ⟨k, hk⟩ := hA2.exists_card_eq
      rw [hk] at h4 hA4 hBcard ⊢
      have hk2 : 2 ≤ k := by
        by_contra h
        push Not at h
        interval_cases k <;> norm_num at h4
      have hk3 : k ≤ 3 := by
        by_contra h
        push Not at h
        have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right two_pos h
        omega
      interval_cases k
      · exact absurd rfl hA4
      · rfl
    have hzA₀ : Subgroup.zpowers a = A₀ := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr haA₀) (by rw [Nat.card_zpowers, haord]; exact hA₀card)
    have hAF : ∀ b ∈ A, b ∈ generalizedFittingSubgroupOf H → b = 1 ∨ b = a := fun b hb hbF =>
      eq_one_or_eq_of_mem_zpowers haord (hzA₀ ▸ hAFY b hb hbF)
    have hHC := G64.eq_centralizer hG ha ha1 hHco.1 hAH hCH haF hAF
    have hMa := hM₀ a haA₀ ha1
    push Not at hnotall
    obtain ⟨a₁, ha₁, ha₁1, hMa₁⟩ := hnotall
    obtain ⟨n, -, hna⟩ :=
      G64.exists_conj_eq_of_card_eight hG.elem hA8 hG.irreducible ha ha1 (hA₁A ha₁) ha₁1
    set H₁ := H.conjBy n⁻¹ with hH₁def
    have hMa₁' : benderM a₁ = {H₁} := by
      have h := benderM_conj_eq_singleton n⁻¹ hMa
      rwa [inv_inv, hna] at h
    have hH₁ : H₁ ∈ benderM a₁ := by rw [hMa₁']; exact Set.mem_singleton _
    have hne : H₁ ≠ H := fun h => hMa₁ (h ▸ hMa₁')
    set R := qCoreOf (fstarZero H₁) p with hRdef
    have hR : R = P₀.conjBy n⁻¹ := G64.qCoreOf_fstarZero_conjBy H n⁻¹ p
    have hRnc : ¬ IsCyclic R := by
      rw [hR]
      exact fun h => hP₀nc
        ((Subgroup.equivMapOfInjective P₀ _ (MulAut.conj n⁻¹).injective).isCyclic.mpr h)
    have h3₁ : 3 ≤ CFSG.Open.pRank p (qCoreOf H₁ p) := by
      rw [hH₁def, show qCoreOf (H.conjBy n⁻¹) p = _ from qCoreOf_conjugateSubgroup H n⁻¹ p]
      exact h3'.trans (CFSG.SectionRank.pRank_le_map hp.one_lt _ (MulAut.conj n⁻¹).injective _)
    have hRH : IsCyclic (R ⊓ H : Subgroup G) := by
      by_cases hRH1 : R ⊓ H = ⊥
      · rw [hRH1]
        exact inferInstance
      · exact (h63 G S A hG a₁ (hA₁A ha₁) ha₁1 H₁ hH₁ p hp hp2 (Or.inr h3₁) a ha ha1 H hH
          (Ne.symm hne) hRH1).2
    have haY : a ∈ Subgroup.centralizer (Y : Set G) := haA₀.2
    have haQ : Q ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq']
      exact hQY.trans (hYC a haA₀)
    have hQa : ⁅Q, Subgroup.zpowers a⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr haQ
    have haNQ : a ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun x hx =>
          (Subgroup.mem_centralizer_singleton_iff.mp ((hQY.trans (hYC a haA₀)) hx)))
    have hNQ : Subgroup.normalizer (Q : Set G) ≤ H :=
      G63.normalizer_le_of_uniqueness hsimple hHco hU hFH hp hQP₀ hQ1 haNQ
    have hRn := G63.qCoreOf_fstarZero_isNormalIn H₁ p
    have haH₁ : a ∈ H₁ := G63.le_of_mem_benderM hG (hA₁A ha₁) hH₁ ha
    have hres : pResidualOf (Subgroup.zpowers a) p = Subgroup.zpowers a :=
      Bender35.pResidualOf_zpowers_eq hp
        (by rw [haord]; exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hCRQ : ⁅R ⊓ Subgroup.centralizer (Q : Set G), Subgroup.zpowers a⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
      rw [centralizer_zpowers_eq', ← hHC]
      exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNQ)
    have hT := bender1970_1_1_thompson p hp Q (Subgroup.zpowers a) R hQp
      (qCoreOf_isPGroup _ p) hres
      ((hQH₁ a₁ ha₁ H₁ hH₁).trans (le_normalizer_of_isNormalIn hRn))
      (Subgroup.zpowers_le.mpr (le_normalizer_of_isNormalIn hRn haH₁)) hQa hCRQ
    have hRH' : R ≤ H := by
      have h1 : R ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        Subgroup.le_centralizer_iff.mp hT
      rw [centralizer_zpowers_eq', ← hHC] at h1
      exact h1
    exact hRnc (G63.isCyclic_of_le hRH (le_inf le_rfl hRH'))
  ·
    refine hnotall fun a₁ ha₁ ha₁1 => G64.benderM_eq_singleton hG ha₁1 fun H₁ hH₁ => ?_
    by_contra hne
    have hH₁co := isCoatom_of_mem_benderM hH₁
    have hAH₁ : A ≤ H₁ := G63.le_of_mem_benderM hG (hA₁A ha₁) hH₁
    obtain ⟨A'₁, hS₁, hA'₁el, hAA'₁⟩ := G63.exists_sstar hG hH₁co.1
    have hA₀A'₁ : A₀ ≤ A'₁ := fun x hx => hAA'₁ ⟨hx.1, hAH₁ hx.1⟩
    have hQH₁' := hQH₁ a₁ ha₁ H₁ hH₁
    have hQle : Q ≤ ⨅ a₀ : {a₀ : G // a₀ ∈ A₀ ∧ a₀ ≠ 1},
        qCoreOf (H₁ ⊓ Subgroup.centralizer ({a₀.1} : Set G)) p := by
      refine le_iInf fun a₀ => ?_
      have hHa₀ : H ∈ benderM a₀.1 := by rw [hM₀ a₀.1 a₀.2.1 a₀.2.2]; exact Set.mem_singleton _
      have hCa₀H := centralizer_le_of_mem_benderM hHa₀
      have hD : P₀ ⊓ (H₁ ⊓ Subgroup.centralizer ({a₀.1} : Set G)) ≤
          qCoreOf (H₁ ⊓ Subgroup.centralizer ({a₀.1} : Set G)) p :=
        le_qCoreOf_of_normal_isPGroup _ _ p inf_le_right
          ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
            mem_normalizer_inf (hHP₀ (hCa₀H hx.2)) (Subgroup.le_normalizer hx))
          (hP₀p.to_le inf_le_left)
      exact (le_inf hQP₀ (le_inf hQH₁' (hQY.trans (hYC a₀.1 a₀.2.1)))).trans hD
    have hQO : Q ≤ qCoreOf H₁ p :=
      hQle.trans (h38 G H₁ A'₁ hS₁ hA'₁el A₀ hA₀A'₁ hA₀c p hp hp2)
    have hQ'1 : P₀ ⊓ H₁ ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ le_inf hQP₀ hQH₁'))
    obtain ⟨⟨hint, -⟩, -⟩ := h63 G S A hG a ha ha1 H hH p hp hp2 (Or.inr h3') a₁ (hA₁A ha₁)
      ha₁1 H₁ hH₁ hne hQ'1
    exact hQ1 (le_bot_iff.mp (hint ▸ le_inf (le_inf hQP₀ hQH₁') hQO))

end CFSG.Goldschmidt
