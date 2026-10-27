module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedQuot
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedStd
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.Asc77.AscIHExact

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Abstract

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {K J : Subgroup X} {z j a : X}

theorem mem_sup_of_mem_pairNormalizers {a : X} (ha : a ∈ pairNormalizers K J z j) : a ∈ K ⊔ J := by
  have h : pairNormalizers K J z j ≤ K ⊔ J := sup_le_sup inf_le_left inf_le_left
  exact h ha

theorem QuotViol.false_of_commutes (h : QuotViol Φ K J z j a) (hc : Commutes K J) : False := by
  have hcent : pairNormalizers K J z j ≤ Subgroup.centralizer ({j} : Set X) := by
    unfold pairNormalizers
    refine sup_le (inf_le_left.trans fun k hk => ?_) (inf_le_left.trans fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc k hk j h.hj.mem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h.hj.commute_of_mem hx).symm
  have h1 : a * j = j * a := Subgroup.mem_centralizer_singleton_iff.mp (hcent h.ha)
  have h2 : a * j * a⁻¹ = j := by rw [h1]; group
  exact h.ne (h.haj.symm.trans h2)

variable [Finite X] {p f : ℕ} [Fact p.Prime]

theorem QuotViol.false_of_centralizer_comm (hΦ : HypOmegaMod p f Φ) (hex : ExactMembers Φ)
    (h : QuotViol Φ K J z j a) {W : Subgroup X} (hKW : K ≤ W) (hJW : J ≤ W)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, (∀ u ∈ K, x * u = u * x) → (∀ u ∈ K, y * u = u * y) →
      x * y = y * x) : False := by
  set K' : Subgroup X := conjSub a J with hK'
  have hK'Φ : K' ∈ Φ := hΦ.conjInvariant a J h.mem_right
  have hzK' : IsUniqueInvolution K' z := by
    have := h.hj.conj a
    rwa [h.haj] at this
  have haW : a ∈ W := (sup_le hKW hJW) (mem_sup_of_mem_pairNormalizers h.ha)
  have hK'W : K' ≤ W := by
    intro x hx
    rw [hK', mem_conjSub_iff] at hx
    have : a * (a⁻¹ * x * a) * a⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem haW (hJW hx)) (W.inv_mem haW)
    simpa [mul_assoc] using this
  have hKK' : K ≠ K' := fun e => h.hne e.symm
  have hc := hΦ.comm_le_oddCore_of_twin h.mem_left hK'Φ hKK' h.hz hzK'
  rw [oddCoreOf_eq_bot_of_exact hex h.mem_left, bot_inf_eq, le_bot_iff] at hc
  have hcK : ∀ x ∈ K', ∀ u ∈ K, x * u = u * x := by
    intro x hx u hu
    have hmem : ⁅u, x⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hu hx
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  obtain ⟨zz, hzz⟩ := hΦ.classical K' hK'Φ
  obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hzz
  exact hxy (hcomm x (hK'W hx) y (hK'W hy) (hcK x hx) (hcK y hy))

end Abstract

section Components

variable {X : Type} [Group X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {K J : Subgroup X} {z j a : X}

theorem QuotViol.exists_components (D : OmegaLie p f Φ) (h : QuotViol Φ K J z j a) :
    ∃ (i : Fin D.card) (R S : Subgroup (D.model i).K), R ∈ D.cls i ∧ S ∈ D.cls i ∧
      K = R.map (D.hom i) ∧ J = S.map (D.hom i) := by
  obtain ⟨i₁, R, hR, hKR⟩ := D.fundamental K h.mem_left
  obtain ⟨i₂, S, hS, hJS⟩ := D.fundamental J h.mem_right
  by_cases hi : i₁ = i₂
  · subst hi
    exact ⟨i₁, R, S, ⟨hR, hKR ▸ h.mem_left⟩, ⟨hS, hJS ▸ h.mem_right⟩, hKR, hJS⟩
  · exfalso
    apply h.false_of_commutes
    subst hKR hJS
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact D.commute i₁ i₂ hi x y

end Components

section Model

variable {M G : Type} [Group M] [Group G]

theorem t3_nbr_model (ψ : M →* G) (hker : ψ.ker ≤ Subgroup.center M) {F₁ F₂ : Type} [Field F₁]
    [Finite F₁] [Field F₂] [Finite F₂] (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    {R S : Subgroup M} (hR : R ≤ ⁅R, R⁆) (eR : R ≃* SL(2, F₁)) (eS : S ≃* SL(2, F₂))
    {A : Subgroup G} (hA2 : IsPGroup 2 A) (hAS : A ≤ S.map ψ) (hne1 : ∃ x ∈ A, x ≠ 1)
    (hAN : A ≤ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS := by
  set T := S ⊓ A.comap ψ with hT
  have hTS : T ≤ S := inf_le_left
  have hTn : T ≤ Subgroup.normalizer (R : Set M) := by
    intro g hg
    exact ih8_mem_normalizer_of_map hker hR (hAN hg.2)
  have hker2 : ∀ x ∈ S, x ∈ ψ.ker → x * x = 1 := by
    intro x hxS hxk
    have hc := Subgroup.mem_center_iff.mp (hker hxk)
    rcases eq_one_or_eq_sl2Inv_of_central eS hxS (fun y _ => (hc y).symm) with h | h
    · rw [h, mul_one]
    · rw [h]
      exact sl2Inv_mul_self hodd₂ eS
  have hT2 : IsPGroup 2 ↥T := ih8_pGroup_lift hA2 hker2
  obtain ⟨x, hx, hx1⟩ := hne1
  obtain ⟨g, hgS, rfl⟩ := hAS hx
  have hgT : g ∈ T := ⟨hgS, hx⟩
  have hg1 : g ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hinv : ∃ w ∈ T, orderOf w = 2 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨g, hgT⟩
    have h1 : orderOf g = 2 ^ k := by
      rw [← hk, Subgroup.orderOf_mk]
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
      exact hg1 h1
    refine ⟨g ^ 2 ^ (k - 1), T.pow_mem hgT _, ?_⟩
    have hdvd : 2 ^ (k - 1) ∣ orderOf g := by
      rw [h1]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have h2 := orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hdvd
    rw [h1, Nat.pow_div (Nat.sub_le k 1) (by norm_num)] at h2
    rw [h2]
    have h3 : k - (k - 1) = 1 := by omega
    rw [h3, pow_one]
  obtain ⟨w, hwT, hw2⟩ := hinv
  have hwz : w = sl2Inv eS := eq_sl2Inv_of_orderOf_eq_two hodd₂ eS (hTS hwT) hw2
  have hzT : sl2Inv eS ∈ T := hwz ▸ hwT
  have hzN : sl2Inv eS ∈ Subgroup.normalizer (R : Set M) := hTn hzT
  have hRz : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hconj : sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp hRz
  have hord : orderOf (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (sl2Inv eS)) (sl2Inv eR)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact orderOf_sl2Inv hodd₁ eR
  have hcomm := eq_sl2Inv_of_orderOf_eq_two hodd₁ eR hconj hord
  calc sl2Inv eS * sl2Inv eR = (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) * sl2Inv eS := by group
    _ = sl2Inv eR * sl2Inv eS := by rw [hcomm]

end Model

section Classical

variable {p f : ℕ} [Fact p.Prime]

theorem fund_eq_top_of_psl_two {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (hp : p ≠ 2) (ht : t = .PSL) (hk : k = 2) (hadm : StatedLieAdmissible t k p e)
    {R : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D) : R = ⊤ := by
  subst ht hk
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp
    (ih8_isFundTag_mf (by trivial)) hadm (by decide) (by decide) hR
  have hcard : Nat.card ↥R = Nat.card (modelUniv .PSL 2 p e Fact.out).K := by
    rw [Nat.card_congr eR.toEquiv]
    exact Nat.card_congr (Equiv.refl _)
  have := ModelFacts.finite_modelUniv hp Fact.out (ih8_isFundTag_mf (by trivial)) hadm
  exact Subgroup.eq_top_of_card_eq R hcard

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {z j a : X}

theorem QuotViol.false_of_classical (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (D : OmegaLie p f Φ) {i : Fin D.card} (hG2 : D.tag i ≠ .G2) (hD4 : D.tag i ≠ .trialityD4)
    {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i) (hS : S ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a) : False := by
  have hker := D.ker_le_center i
  have hex : ExactMembers Φ := D.exactMembers hp hq hΦ
  have he : 1 ≤ D.exp i := (D.admissible i).2.1
  have hef : D.exp i = f := by
    rcases D.exp_eq i with h' | ⟨h', -⟩
    · exact h'
    · exact absurd h' hD4
  have hq' : 5 ≤ p ^ D.exp i := by rw [hef]; exact hq
  have hodd : Odd (Nat.card (GaloisField p (D.exp i))) := by
    rw [GaloisField.card p (D.exp i) (by omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  by_cases hpsl : D.tag i = .PSL ∧ D.rank i = 2
  · have hRt := fund_eq_top_of_psl_two hp hpsl.1 hpsl.2 (D.admissible i) hR.1
    have hSt := fund_eq_top_of_psl_two hp hpsl.1 hpsl.2 (D.admissible i) hS.1
    rw [hRt, hSt] at h
    exact h.ne (h.hz.eq h.hj)
  have hinjR := D.injOn_fund i hpsl hR.1
  have hinjS := D.injOn_fund i hpsl hS.1
  have hpR : R ≤ ⁅R, R⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp (D.isFundTag i) (D.admissible i) (by omega) R hR.1
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp
    (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i) hG2 hD4 hR.1
  obtain ⟨eS⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp
    (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i) hG2 hD4 hS.1
  have hc₁ : D.hom i (sl2Inv eR) = z := by
    have hmem : D.hom i (sl2Inv eR) ∈ R.map (D.hom i) := Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
    have hsq : D.hom i (sl2Inv eR) * D.hom i (sl2Inv eR) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR, map_one]
    rcases h.hz.unique _ hmem hsq with h1 | h1
    · exact absurd (hinjR _ (sl2Inv_mem eR) h1) (sl2Inv_ne_one hodd eR)
    · exact h1
  have hc₂ : D.hom i (sl2Inv eS) = j := by
    have hmem : D.hom i (sl2Inv eS) ∈ S.map (D.hom i) := Subgroup.mem_map_of_mem _ (sl2Inv_mem eS)
    have hsq : D.hom i (sl2Inv eS) * D.hom i (sl2Inv eS) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eS, map_one]
    rcases h.hj.unique _ hmem hsq with h1 | h1
    · exact absurd (hinjS _ (sl2Inv_mem eS) h1) (sl2Inv_ne_one hodd eS)
    · exact h1
  obtain ⟨U, hU, hUJ, hUN⟩ := h.star.2.2
  have hU2 : IsPGroup 2 U := hΦ.isPGroup_of_mem_USet hp hU
  have hU4 : ∃ x ∈ U, x ≠ 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, h4U⟩ := hΦ.exists_data_of_mem_USet hp hU
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at h4U
    omega
  have hcomm : sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS :=
    t3_nbr_model (D.hom i) hker hodd hodd hpR eR eS hU2 hUJ hU4 hUN
  have hdich := ih8_stdDichotomy (D.isFundTag i) hG2 hD4 (D.admissible i)
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR.1
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hS.1
  rcases hdich.map_of_commute hp hq' (D.hom i) hker hRl hSl (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hcomm.symm with hEq | hC | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact h.ne (h.hz.eq (by rw [hEq]; exact h.hj))
  · exact h.false_of_commutes hC
  · obtain ⟨hKW, hJW⟩ := LinearBlockStandardPair.le_group hW
    have h4F : 4 ≤ Nat.card (GaloisField p (D.exp i)) := by
      rw [GaloisField.card p (D.exp i) (by omega)]
      omega
    exact h.false_of_centralizer_comm hΦ hex hKW hJW fun x hx y hy hxc hyc =>
      LinearBlockStandardPair.centralizer_comm h4F
        (ModelFacts.two_ne_zero_galoisField (D.exp i) hp) hW hx hy hxc hyc
  · obtain ⟨hKW, hJW⟩ := UnitaryBlockStandardPair.le_group hW
    exact h.false_of_centralizer_comm hΦ hex hKW hJW fun x hx y hy hxc hyc =>
      UnitaryBlockStandardPair.centralizer_comm
        (CFSG.LieType.Universal.card_galoisField_two_mul p (D.exp i) he) hq'
        (ModelFacts.two_ne_zero_galoisField (2 * D.exp i) hp) hW hx hy hxc hyc

end Classical

end CFSG.ClassicalInvolution.Asc77.T3Typed
