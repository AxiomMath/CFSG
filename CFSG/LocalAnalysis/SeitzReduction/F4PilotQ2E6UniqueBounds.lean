module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiInnerV
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.EvenSmallLie

section E6Data

@[expose] def zSecondA : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 1, 1]

@[expose] def zSecondB : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 0]

@[expose] def zSecondD : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 0, 0]

@[expose] def zSecondTarget : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 3, 2, 1]

@[expose] def zFullList28 : List (Fin Tag.E6.rank → ℤ) :=
  E6Pilot.zDiagA :: E6Pilot.zDiagB :: E6Pilot.zDiagD :: zSecondA :: zSecondB :: zSecondD ::
    E6Pilot.e6CentList 2

theorem zSecond_check :
    (∀ v ∈ [zSecondA, zSecondB, zSecondD, zSecondTarget], oddDerivIsRootB .E6 v = true) ∧
    E6Pilot.zFrameE + zSecondA = zSecondTarget ∧ E6Pilot.zFrameD + zSecondB = zSecondTarget ∧
    E6Pilot.zFrameG + zSecondD = zSecondTarget ∧
    E6Pilot.zFrameE ≠ zSecondA ∧ E6Pilot.zFrameE ≠ -zSecondA ∧
    E6Pilot.zFrameD ≠ zSecondB ∧ E6Pilot.zFrameD ≠ -zSecondB ∧
    E6Pilot.zFrameG ≠ zSecondD ∧ E6Pilot.zFrameG ≠ -zSecondD := by
  decide +kernel

theorem zFullList28_check : zFullList28.Nodup ∧
    (∀ γ ∈ zFullList28, oddDerivIsRootB .E6 γ = true ∧ 0 < height γ) ∧
    (E6Pilot.e6CentList 2).length = 24 := by
  decide +kernel

end E6Data

section E6Commute


variable {K : Type} [Field K]

theorem commute_zSecond_zRep [CharP K 2] (s u : K) :
    Commute (pinnedX .E6 K zSecondA s * (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u))
      ((oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod) := by
  obtain ⟨hroots, hεa, hδb, hγd, hεa1, hεa2, hδb1, hδb2, hγd1, hγd2⟩ := zSecond_check
  obtain ⟨hF, hroots₀, -⟩ := E6Pilot.zDiag_check
  have hr : ∀ v ∈ [zSecondA, zSecondB, zSecondD, zSecondTarget], IsRoot .E6 v :=
    fun v hv => isRoot_of_oddDerivIsRootB (hroots v hv)
  have hr₀ : ∀ v ∈ [E6Pilot.zDiagA, E6Pilot.zDiagB, E6Pilot.zDiagD, E6Pilot.zFrameG,
      E6Pilot.zFrameD, E6Pilot.zFrameE, E6Pilot.e6R], IsRoot .E6 v :=
    fun v hv => isRoot_of_oddDerivIsRootB (hroots₀ v hv)
  have hA := hr zSecondA (by simp)
  have hB := hr zSecondB (by simp)
  have hD := hr zSecondD (by simp)
  have hrr := hr zSecondTarget (by simp)
  have hγ := hr₀ E6Pilot.zFrameG (by simp)
  have hδ := hr₀ E6Pilot.zFrameD (by simp)
  have hε := hr₀ E6Pilot.zFrameE (by simp)
  have cεB := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameE) (σ := zSecondB)
    (by decide +kernel)
  have cεD := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameE) (σ := zSecondD)
    (by decide +kernel)
  have cδA := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameD) (σ := zSecondA)
    (by decide +kernel)
  have cδD := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameD) (σ := zSecondD)
    (by decide +kernel)
  have cδr := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameD)
    (σ := zSecondTarget) (by decide +kernel)
  have cγA := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameG) (σ := zSecondA)
    (by decide +kernel)
  have cγB := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameG) (σ := zSecondB)
    (by decide +kernel)
  have cγr := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := E6Pilot.zFrameG)
    (σ := zSecondTarget) (by decide +kernel)
  have cAr := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := zSecondA) (σ := zSecondTarget)
    (by decide +kernel)
  have cBr := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := zSecondB) (σ := zSecondTarget)
    (by decide +kernel)
  have cDr := E6Pilot.commute_pinnedX_of_checkB (K := K) (ρ := zSecondD) (σ := zSecondTarget)
    (by decide +kernel)
  have sεA : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameE 1) (pinnedX .E6 K zSecondA s) =
      pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s :=
    E6Pilot.conj_pinnedX_eq_mul_of_charTwo hε hA hεa1 hεa2 hεa hrr s (cAr s s)
  have sδB : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameD 1) (pinnedX .E6 K zSecondB (s + u)) =
      pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondTarget (s + u) :=
    E6Pilot.conj_pinnedX_eq_mul_of_charTwo hδ hB hδb1 hδb2 hδb hrr (s + u) (cBr (s + u) (s + u))
  have sγD : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameG 1) (pinnedX .E6 K zSecondD u) =
      pinnedX .E6 K zSecondD u * pinnedX .E6 K zSecondTarget u :=
    E6Pilot.conj_pinnedX_eq_mul_of_charTwo hγ hD hγd1 hγd2 hγd hrr u (cDr u u)
  have hz : (oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod =
      pinnedX .E6 K E6Pilot.zFrameG 1 *
        (pinnedX .E6 K E6Pilot.zFrameD 1 * pinnedX .E6 K E6Pilot.zFrameE 1) := by
    rw [hF]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have h2 : s + (s + u + u) = 0 := by
    have h20 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (s + u) * h20
  have st1 : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameE 1)
      (pinnedX .E6 K zSecondA s * (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u)) =
      pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s *
        (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u) := by
    simp only [map_mul]
    rw [sεA, E6Pilot.conj_eq_of_commute (cεB 1 (s + u)), E6Pilot.conj_eq_of_commute (cεD 1 u)]
  have st2 : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameD 1)
      (pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s *
        (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u)) =
      pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s *
        (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondTarget (s + u) *
          pinnedX .E6 K zSecondD u) := by
    simp only [map_mul]
    rw [E6Pilot.conj_eq_of_commute (cδA 1 s), E6Pilot.conj_eq_of_commute (cδr 1 s), sδB,
      E6Pilot.conj_eq_of_commute (cδD 1 u)]
  have st3 : MulAut.conj (pinnedX .E6 K E6Pilot.zFrameG 1)
      (pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s *
        (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondTarget (s + u) *
          pinnedX .E6 K zSecondD u)) =
      pinnedX .E6 K zSecondA s * pinnedX .E6 K zSecondTarget s *
        (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondTarget (s + u) *
          (pinnedX .E6 K zSecondD u * pinnedX .E6 K zSecondTarget u)) := by
    simp only [map_mul]
    rw [E6Pilot.conj_eq_of_commute (cγA 1 s), E6Pilot.conj_eq_of_commute (cγr 1 s),
      E6Pilot.conj_eq_of_commute (cγB 1 (s + u)), E6Pilot.conj_eq_of_commute (cγr 1 (s + u)), sγD]
  rw [hz]
  refine (Commute.symm ?_)
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  change MulAut.conj (pinnedX .E6 K E6Pilot.zFrameG 1 *
      (pinnedX .E6 K E6Pilot.zFrameD 1 * pinnedX .E6 K E6Pilot.zFrameE 1))
    (pinnedX .E6 K zSecondA s * (pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u)) = _
  rw [(MulAut.conj : ModGL .E6 K →* MulAut (ModGL .E6 K)).map_mul,
    (MulAut.conj : ModGL .E6 K →* MulAut (ModGL .E6 K)).map_mul, MulAut.mul_apply,
    MulAut.mul_apply, st1, st2, st3]
  have e1 : pinnedX .E6 K zSecondTarget s * (pinnedX .E6 K zSecondB (s + u) *
      pinnedX .E6 K zSecondTarget (s + u) *
      (pinnedX .E6 K zSecondD u * pinnedX .E6 K zSecondTarget u)) =
      pinnedX .E6 K zSecondB (s + u) * pinnedX .E6 K zSecondD u := by
    rw [mul_assoc (pinnedX .E6 K zSecondB (s + u)), (cBr (s + u) s).symm.left_comm,
      (cDr u (s + u)).symm.left_comm, (cDr u s).symm.left_comm, ← pinnedX_add, ← pinnedX_add,
      h2, pinnedX_zero, mul_one]
  rw [mul_assoc, e1]

end E6Commute

section E6Bound


variable {K : Type} [Field K] [Finite K]

theorem pow_dvd_card_centralizer_e6ASRep_two_28 [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    2 ^ (f * 28) ∣
      Nat.card (centralizer ({E6Pilot.e6ASRep K 2} : Set (adjointGroup .E6 K))) := by
  obtain ⟨hnodup, hroot, hlen⟩ := zFullList28_check
  have hinj : Function.Injective zFullList28.get := List.nodup_iff_injective_get.1 hnodup
  have hpos : ∀ i, IsRoot .E6 (zFullList28.get i) ∧ 0 < height (zFullList28.get i) :=
    fun i => ⟨isRoot_of_oddDerivIsRootB (hroot _ (List.get_mem _ _)).1,
      (hroot _ (List.get_mem _ _)).2⟩
  obtain ⟨hU, hψ⟩ := positive_root_product_injectivity .E6 K _ hinj hpos
  let ι : K × K × K × K × (Fin (E6Pilot.e6CentList 2).length → K) →
      Fin zFullList28.length → K :=
    fun x => Fin.cons x.1 (Fin.cons (x.1 + x.2.1) (Fin.cons x.2.1 (Fin.cons x.2.2.1
      (Fin.cons (x.2.2.1 + x.2.2.2.1) (Fin.cons x.2.2.2.1 x.2.2.2.2)))))
  have hι : Function.Injective ι := by
    rintro ⟨s, u, s', u', c⟩ ⟨s₁, u₁, s₁', u₁', c₁⟩ h
    obtain ⟨hs, h1⟩ := Fin.cons_inj.1 h
    obtain ⟨-, h2⟩ := Fin.cons_inj.1 h1
    obtain ⟨hu, h3⟩ := Fin.cons_inj.1 h2
    obtain ⟨hs', h4⟩ := Fin.cons_inj.1 h3
    obtain ⟨-, h5⟩ := Fin.cons_inj.1 h4
    obtain ⟨hu', hc⟩ := Fin.cons_inj.1 h5
    simp only at hs hu hs' hu' hc
    subst hs hu hs' hu' hc
    rfl
  have hprod : ∀ x : K × K × K × K × (Fin (E6Pilot.e6CentList 2).length → K),
      (List.ofFn fun i => pinnedX .E6 K (zFullList28.get i) (ι x i)).prod =
        (pinnedX .E6 K E6Pilot.zDiagA x.1 * (pinnedX .E6 K E6Pilot.zDiagB (x.1 + x.2.1) *
          pinnedX .E6 K E6Pilot.zDiagD x.2.1)) *
        ((pinnedX .E6 K zSecondA x.2.2.1 * (pinnedX .E6 K zSecondB (x.2.2.1 + x.2.2.2.1) *
          pinnedX .E6 K zSecondD x.2.2.2.1)) *
        (List.ofFn fun i => pinnedX .E6 K ((E6Pilot.e6CentList 2).get i) (x.2.2.2.2 i)).prod) := by
    intro x
    simp only [ι, zFullList28, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ,
      List.get_cons_zero, mul_assoc]
    rfl
  refine E6Pilot.pow_dvd_card_centralizer_of_injective Nat.prime_two hK (E6Pilot.e6ASRep K 2)
    (X := K × K × K × K × (Fin (E6Pilot.e6CentList 2).length → K))
    (ψ := fun x => (List.ofFn fun i => pinnedX .E6 K (zFullList28.get i) (ι x i)).prod) ?_
    (hψ.comp hι) (fun x => hU _) fun x => ?_
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin,
      hK, hlen]
    ring
  · rw [hprod]
    refine Commute.mul_left ?_ (Commute.mul_left ?_ ?_)
    · exact E6Pilot.commute_zDiag_zRep x.1 x.2.1
    · exact commute_zSecond_zRep x.2.2.1 x.2.2.2.1
    · refine Commute.list_prod_left _ _ fun y hy => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact E6Pilot.commute_pinnedX_e6ASFrame 2 (List.get_mem _ _) (x.2.2.2.2 i)

theorem two_pow_dvd_card_centralizer_E6_27 {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {w : adjointGroup .E6 K} (hw : orderOf w = 2) :
    2 ^ (27 * f) ∣ Nat.card (centralizer ({w} : Set (adjointGroup .E6 K))) := by
  have : CharP K 2 := by
    have hf : f ≠ 0 := by
      rintro rfl
      have h1 : Nat.card K = 1 := by rw [hK, pow_zero]
      have : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h1).1
      exact zero_ne_one (Subsingleton.elim (0 : K) 1)
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (Nat.one_le_iff_ne_zero.2 hf) hK
  have hw2 : w ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 hw2 hw1
  obtain ⟨κ, hκ⟩ := E6Pilot.mem_innerRepsE6_iff.1 hg
  rw [← E6Pilot.card_centralizer_conj g w, hκ]
  fin_cases κ
  · have h := E6Pilot.pow_dvd_card_centralizer_e6ASRep hK 0
    have hl : (E6Pilot.e6CentList 0).length = 36 := by decide +kernel
    rw [hl] at h
    exact (pow_dvd_pow 2 (by omega)).trans h
  · have h := E6Pilot.pow_dvd_card_centralizer_e6ASRep hK 1
    have hl : (E6Pilot.e6CentList 1).length = 30 := by decide +kernel
    rw [hl] at h
    exact (pow_dvd_pow 2 (by omega)).trans h
  · exact (pow_dvd_pow 2 (by omega)).trans (pow_dvd_card_centralizer_e6ASRep_two_28 hK)

end E6Bound

section TwistedBound


theorem two_pow_dvd_card_centralizer_twistedE6_27 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {w : graphFixedRootGroup TwistTag.E6 K σ} (hw : orderOf w = 2) :
    2 ^ (27 * f) ∣ Nat.card (centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := TwistedE6Pilot.finite_of_card hK
  have : CharP K 2 := TwistedE6Pilot.charP_two_of_card hf hK
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨σE, rfl⟩ := TwistedE6Pilot.exists_ringEquiv_toRingHom_eq σ
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra (GaloisField 2 f) K := ι.toAlgebra
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK
    (fun c => hσ c) (twistedE6FrameReduction hf hK (fun c => hσ c)) hw2 hw1
  rw [← E6Pilot.card_centralizer_conj g w]
  rcases hg with h | h | h
  · have hs : g * w * g⁻¹ = TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK hσ) 0 :=
      Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega)).trans
      (TwistedE6Pilot.two_pow_dvd_card_centralizer_stdRepC_zero hf hK hσ)
  · have hs : g * w * g⁻¹ = TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK hσ) 1 :=
      Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega)).trans
      (TwistedE6Pilot.two_pow_dvd_card_centralizer_classU hf hK hσ)
  · have hs : g * w * g⁻¹ = ⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (TwistedE6Pilot.apply_apply_eq hK hσ)⟩ :=
      Subtype.ext h
    rw [hs]
    exact two_pow_dvd_card_centralizer_twistedE6ClassV (k := GaloisField 2 f) hk hK hσ

end TwistedBound

section F4Bound


theorem four_mul_lt_two_pow_three_mul {f : ℕ} (hf : 1 ≤ f) : 4 * f < 2 ^ (3 * f) := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show 3 * (n + 1) = 3 * n + 3 by ring, pow_add]
    omega

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_two_pow_dvd_card_centralizer_F4_27 (hset : StandardSetting G L) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ¬ 2 ^ (27 * f) ∣ Nat.card (centralizer ({t} : Set G)) := by
  intro h
  have h1 := h.trans (card_centralizer_dvd_F4 hset hK e htC ht hKt)
  obtain ⟨r, hr, hrF⟩ := (CFSG.Timmesfeld.Orders.profile_ordF4 hf).two
  rw [hrF] at h1
  have h2 : 2 ^ (3 * f) ∣ 4 * f * r := by
    have e1 : 2 ^ (27 * f) = 2 ^ (f * 24) * 2 ^ (3 * f) := by rw [← pow_add]; ring_nf
    have e2 : 4 * f * (2 ^ (f * 24) * r) = 2 ^ (f * 24) * (4 * f * r) := by ring
    rw [e1, e2] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).1 h1
  have hcop : Nat.Coprime (2 ^ (3 * f)) r :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hr)
  have h3 : 2 ^ (3 * f) ∣ 4 * f := hcop.dvd_of_dvd_mul_right h2
  have h4 : 2 ^ (3 * f) ≤ 4 * f := Nat.le_of_dvd (by omega) h3
  have h5 := four_mul_lt_two_pow_three_mul hf
  omega

end F4Bound

end CFSG.SeitzReduction.F4Pilot
