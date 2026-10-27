module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusSec
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusUnip

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

@[expose] def NActs {A : Type} [Group A] (B N : Subgroup A) (hd : OrthCuts r d)
    (fl : ↥B →* (𝕍 ≃ₗ[K] 𝕍)) : Prop :=
  ∀ n ∈ N, ∃ (σ : K ≃+* K) (F : 𝕍 ≃+ 𝕍) (hF : ∀ (a : K) (v : 𝕍), F (a • v) = σ a • F v),
    (∀ (i : Fin (s + 1)) (v : 𝕍), F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔
      v ∈ tailFlag K (Fin 2 → K) r (d i)) ∧
    (∀ v : 𝕍, IsResPerp hd.last (F v) ↔ IsResPerp hd.last v) ∧
    ∀ x y : ↥B, n * (x : A) * n⁻¹ = (y : A) → fl y = semilinConj F σ hF (fl x)

theorem trivial_sections_of_irred {A : Type} [Group A] [Finite A] {B N : Subgroup A}
    (hcyc : ¬ IsCyclic ↥B) (hirrN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    (hd : OrthCuts r d) (fl : ↥B →* (𝕍 ≃ₗ[K] 𝕍)) (hfl : ∀ x, GoodIso b c hd (fl x))
    (hN : NActs B N hd fl) (l : Fin s) (x : ↥B) :
    ∀ v ∈ tailFlag K (Fin 2 → K) r (d l.succ),
      fl x v - v ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := by
  obtain ⟨v₀, hv₀, hv₀T⟩ := exists_mem_flag_not_mem (K := K) hd l
  have hTl : ∀ x w, fl x w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) ↔
      w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := fun x w => (hfl x).flag l.castSucc w
  have hsc : ∀ x, ∃ a : K, ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
      (tailFlag K (Fin 2 → K) r (d l.castSucc)) (fl x) a := fun x => (hfl x).sec l
  set θ : ↥B →* Kˣ := secChar fl hv₀ hv₀T hTl hsc with hθ
  have hθ1 : ∀ y, θ y = 1 := by
    refine forall_eq_one_of_irred hcyc hirrN hNB θ fun n hn y hy hb => ?_
    obtain ⟨σ, F, hF, hFflag, -, hconj⟩ := hN n hn
    have h1 : ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
        (tailFlag K (Fin 2 → K) r (d l.castSucc)) (fl y) 1 := by
      have := scalarMod_secChar fl hv₀ hv₀T hTl hsc y
      rwa [← hθ, hy, Units.val_one] at this
    have h2 := scalarMod_semilinConj (hF := hF) (hFflag l.succ) (hFflag l.castSucc) h1
    rw [map_one, ← hconj y ⟨_, hb⟩ rfl] at h2
    have h3 := scalarMod_secChar fl hv₀ hv₀T hTl hsc ⟨_, hb⟩
    exact Units.ext (scalarMod_unique h3 h2 hv₀ hv₀T)
  intro v hv
  have h := scalarMod_secChar fl hv₀ hv₀T hTl hsc x v hv
  rwa [← hθ, hθ1 x, Units.val_one, one_smul] at h

theorem trivRes_of_irred {A : Type} [Group A] [Finite A] {B N : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B) (hirrN : IrredOn N B)
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hd : OrthCuts r d) (fl : ↥B →* (𝕍 ≃ₗ[K] 𝕍))
    (hfl : ∀ x, GoodIso b c hd (fl x)) (hN : NActs B N hd fl) (x : ↥B) :
    TrivRes hd.last (fl x) := by
  by_cases hm : 1 ≤ r - d (Fin.last s)
  · obtain ⟨a, ha⟩ := (hfl x).res hm
    exact trivRes_of_scalarMod hd (hfl x).iso ha
  · have hm0 : r - d (Fin.last s) = 0 := by omega
    have hG0 : ∀ y, fl y ∈ G0 (K := K) (r := r) hd.last := fun y =>
      (mem_G0 hd.last).2 ⟨(hfl y).flag (Fin.last s), (hfl y).perp⟩
    let flG0 : ↥B →* ↥(G0 (K := K) (r := r) hd.last) := fl.codRestrict _ hG0
    let θ0 : ↥B →* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := (pmHom hd.last hm0).comp flG0
    have hθ0 : ∀ y, θ0 y = pmHom hd.last hm0 ⟨fl y, hG0 y⟩ := fun y => rfl
    have hθω : ∀ y, θ0 y ∈ omegaRotations b c := by
      intro y
      obtain ⟨j, hj⟩ := hB y
      rw [hθ0]
      refine pmHom_isOmegaTwisted hd.last hm0 hirr (hG0 y) (hfl y).iso
        ((hp.odd_of_ne_two hp2).pow (n := j)) ?_
      rw [← map_pow, hj, map_one]
    let θ : ↥B →* ↥(omegaRotations b c) := θ0.codRestrict _ hθω
    have hθcyc : IsCyclic ↥θ.range := by
      haveI := isCyclic_omegaRotations hirr
      infer_instance
    have hθval : ∀ y, ((θ y : ↥(omegaRotations b c)) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) = θ0 y :=
      fun y => rfl
    have hθ1 : ∀ y, θ y = 1 := by
      refine forall_eq_one_of_irred_cyclic hcyc hirrN hNB θ hθcyc fun n hn y hy hb => ?_
      obtain ⟨σ, F, hF, hFflag, hFperp, hconj⟩ := hN n hn
      have h1 : TrivRes hd.last (fl y) := by
        refine (pmHom_eq_one_iff hd.last hm0 (hG0 y)).1 ?_
        rw [← hθ0]
        have := congrArg Subtype.val hy
        exact this
      have h2 := trivRes_semilinConj (hF := hF) hd.last hFperp (hFflag (Fin.last s)) h1
      rw [← hconj y ⟨_, hb⟩ rfl] at h2
      refine Subtype.ext ?_
      rw [hθval, hθ0]
      exact (pmHom_eq_one_iff hd.last hm0 (hG0 ⟨_, hb⟩)).2 h2
    refine (pmHom_eq_one_iff hd.last hm0 (hG0 x)).1 ?_
    rw [← hθ0]
    exact congrArg Subtype.val (hθ1 x)

theorem forall_fl_eq_one {A : Type} [Group A] [Finite A] {B N : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B) (hirrN : IrredOn N B)
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hd : OrthCuts r d) (fl : ↥B →* (𝕍 ≃ₗ[K] 𝕍))
    (hfl : ∀ x, GoodIso b c hd (fl x)) (hN : NActs B N hd fl) : ∀ x, fl x = 1 := by
  intro x
  have hu := pow_two_pow_eq_one_of_trivial_sections hd (hfl x).iso
    (trivial_sections_of_irred hcyc hirrN hNB hd fl hfl hN · x)
    (trivRes_of_irred hp hp2 hirr hB hcyc hirrN hNB hd fl hfl hN x)
  obtain ⟨j, hj⟩ := hB x
  have hj' : fl x ^ p ^ j = 1 := by rw [← map_pow, hj, map_one]
  exact eq_one_of_pow_two_pow hp hp2 hj' hu

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus
