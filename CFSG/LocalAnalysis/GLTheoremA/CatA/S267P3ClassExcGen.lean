module

import CFSG.RankThree.PartTwo.Census.TripleCoverLift
import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Excess
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem P3Hyp.false_of_inverted_gens (H : P3Hyp q S B) {X : Type} [Group X]
    (e : PSimple 3 S ≃* X) {ι : Type} (g : ι → X) (hg3 : ∀ i, g i ^ 3 = 1)
    (hinv : ∀ i, ∃ n : X, n * g i * n⁻¹ = (g i)⁻¹)
    (hpair : ∀ i j, g i ≠ g j → Commute (g i) (g j) ∧ ∃ n : X,
      (n * g i * n⁻¹ = g i ∧ n * g j * n⁻¹ = (g j)⁻¹) ∨
        (n * g i * n⁻¹ = g j ∧ n * g j * n⁻¹ = g i))
    {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htg : ∀ i, Commute t (g i))
    (hcard : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range g))) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' : ↥S ⧸ Subgroup.center ↥S ≃* X := (psimpleEquivCenterQuot H).symm.trans e
  set π : ↥S →* X := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)) with hπdef
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥S := by
    ext y
    rw [MonoidHom.mem_ker]
    change e' (QuotientGroup.mk' (Subgroup.center ↥S) y) = 1 ↔ _
    rw [map_eq_one_iff e' e'.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerc : π.ker ≤ Subgroup.center ↥S := hker.le
  set E : Subgroup X := Subgroup.closure (Set.range g) with hE
  have hcomm : ∀ x ∈ E.comap π, ∀ y ∈ E.comap π, x * y = y * x := by
    intro x hx y hy
    refine commute_of_mem_closure hπ hkerc (S := Set.range g) ?_ hx hy
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hne
    rw [← hi, ← hj] at hne
    obtain ⟨hc, n, hn⟩ := hpair i j hne
    refine commute_of_conj hπ hkerc (p := 3) ⟨1, rfl⟩ (x := a) (y := b) (n := n) ?_ ?_ ?_
    · rw [← hi, ← hj]; exact hc
    · rw [← hj]; exact hg3 j
    · rw [← hi, ← hj]; exact hn
  have hlift : ∀ x ∈ E, ∃ y : ↥S, π y = x ∧ y ^ 3 = 1 := fun x hx =>
    exists_lift_pow_eq_one_of_mem_closure hcomm Subgroup.subset_closure
      (fun s ⟨i, hi⟩ => by
        obtain ⟨n, hn⟩ := hinv i
        rw [← hi]
        exact exists_lift_pow_eq_one_of_conj_eq_inv hπ hkerc ⟨1, rfl⟩ (hg3 i) hn) hx
  have htE : ∀ x ∈ E, Commute t x := by
    have hle : E ≤ Subgroup.centralizer {t} :=
      (Subgroup.closure_le _).2 (by
        rintro _ ⟨i, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (htg i).eq.symm)
    exact fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1
    (CFSG.LocalAnalysis.GLTheoremA.SFM5.isPGroup_center_of_glaPPrimeCore_eq_bot H.core)
  have hle := H.twoLocalRank_le
  by_cases hZ : Subgroup.center ↥S = ⊥
  ·
    have h4 : 4 + 0 ≤ localRank 3 ↥S :=
      add_le_localRank_of_lift hπ hkerc Nat.prime_three (by norm_num) (Z := ⊥) bot_le
        (fun z hz => by rw [Subgroup.mem_bot.1 hz, one_pow]) (s := 0)
        (by rw [Subgroup.card_bot, pow_zero]) hcomm hlift ht1 ht2 htE hcard
    have h4' : 4 ≤ GLATwoLocalRank 3 ↥S := h4
    have hCel : IsElemAbelian 3 (B ⊓ centModSubgroup 3 S) := H.elem.mono inf_le_left
    have hCK : B ⊓ centModSubgroup 3 S ≤ Subgroup.centralizer (S : Set Ω) := fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun s hs => (H.comm_of_mem_centMod hb.2 hs).symm
    have h5 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.le_twoLocalRank_of_central
      Nat.prime_three hCel hCK hZ (by norm_num) h4'
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hCel
      (by rw [H.cent, pow_one])] at h5
    omega
  ·
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.eq_bot_of_card_eq _ (by rw [ha, pow_zero]))
    have h5 : 4 + 1 ≤ localRank 3 ↥S :=
      succ_le_localRank_of_lift hπ hkerc Nat.prime_three (by norm_num)
        (by rw [hker, ha]; exact dvd_pow_self 3 ha0) hcomm hlift ht1 ht2 htE hcard
    have h5' : 5 ≤ GLATwoLocalRank 3 ↥S := h5
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le
      Nat.prime_three S
    omega

private theorem ofAdd_single_eq_pow {ι : Type} [DecidableEq ι] (j : ι) (c : ZMod 3) :
    (Multiplicative.ofAdd (Pi.single j c) : Multiplicative (ι → ZMod 3)) =
      (Multiplicative.ofAdd (Pi.single j 1)) ^ c.val := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem P3Hyp.false_of_torus_hom (H : P3Hyp q S B) {X : Type} [Group X]
    (e : PSimple 3 S ≃* X) {m : ℕ} (θ : Multiplicative (Fin m → ZMod 3) →* X)
    (hcard : 3 ^ 4 ≤ Nat.card θ.range)
    (hinv : ∀ j, ∃ n : X, n * θ (.ofAdd (Pi.single j 1)) * n⁻¹ =
      (θ (.ofAdd (Pi.single j 1)))⁻¹)
    (hswap : ∀ j j', j ≠ j' → ∃ n : X,
      n * θ (.ofAdd (Pi.single j 1)) * n⁻¹ = θ (.ofAdd (Pi.single j' 1)) ∧
        n * θ (.ofAdd (Pi.single j' 1)) * n⁻¹ = θ (.ofAdd (Pi.single j 1)))
    {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htθ : ∀ a, Commute t (θ a)) : False := by
  haveI : Finite X := Finite.of_equiv _ e.toEquiv
  set g : Fin m → X := fun j => θ (.ofAdd (Pi.single j 1)) with hg
  have htop : Subgroup.closure (Set.range fun j : Fin m =>
      (Multiplicative.ofAdd (Pi.single j 1) : Multiplicative (Fin m → ZMod 3))) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have ha : a = ∏ j, (Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd a j)) :
        Multiplicative (Fin m → ZMod 3)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      exact (Finset.univ_sum_single (Multiplicative.toAdd a)).symm
    rw [ha]
    refine Subgroup.prod_mem _ fun j _ => ?_
    rw [ofAdd_single_eq_pow]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _
  have hcl : θ.range ≤ Subgroup.closure (Set.range g) := by
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure, ← Set.range_comp]
    exact le_rfl
  refine H.false_of_inverted_gens e g (fun j => ?_) hinv (fun i j hij => ?_) ht1 ht2
    (fun j => htθ _) (hcard.trans (Subgroup.card_le_of_le hcl))
  · change θ _ ^ 3 = 1
    rw [← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
  · have hne : i ≠ j := by
      rintro rfl
      exact hij rfl
    obtain ⟨n, hn⟩ := hswap i j hne
    exact ⟨(Commute.all _ _).map θ, n, Or.inr hn⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
