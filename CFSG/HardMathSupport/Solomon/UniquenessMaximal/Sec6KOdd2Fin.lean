module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Main
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KNoSLReduce

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.QuasithinUnique.Id2519

namespace Odd2

theorem sec8_of_gl3 {L : Type} [Field L] [Finite L] (hL : Nat.card L % 4 = 1) {G : Type}
    [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 3) L) (hρ : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : Matrix.GeneralLinearGroup (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L).det = 1) : Sec8 G := by
  apply Sec8.of_two
  intro B E _ _ _ _ ι f hB hι hf hE
  obtain ⟨A, δ, hA, hδ⟩ := exists_index_two_injective_diag hL hB (ρ.comp ι) (hρ.comp hι)
    (fun t => hdet _)
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    hδ (by rw [map_mul, map_mul, mul_comm])
  have hg : Function.Surjective (f.subgroupMap A) := MonoidHom.subgroupMap_surjective f A
  have hFE : ∀ x : ↥(A.map f), x * x = 1 := fun x => Subtype.ext (hE x)
  have h1 := card_le_card_sq_eq_one hcomm (f.subgroupMap A) hg hFE
  have h2 : Nat.card {a : A // a * a = 1} ≤ 4 := by
    classical
    let T : Finset L := {1, -1}
    have hTc : T.card ≤ 2 := Finset.card_le_two
    have hT : ∀ x : L, x * x = 1 → x ∈ T := by
      intro x hx
      rcases mul_self_eq_one_iff.mp hx with h | h <;> simp [T, h]
    let m : {a : A // a * a = 1} → ↥(T ×ˢ T) := fun s =>
      ⟨δ s.1, Finset.mem_product.2 ⟨hT _ (by
        have := congrArg (fun z : L × L => z.1) (by rw [← map_mul, s.2, map_one] :
          δ s.1 * δ s.1 = 1)
        simpa using this), hT _ (by
        have := congrArg (fun z : L × L => z.2) (by rw [← map_mul, s.2, map_one] :
          δ s.1 * δ s.1 = 1)
        simpa using this)⟩⟩
    have hm : Function.Injective m := by
      intro s s' h
      exact Subtype.ext (hδ (congrArg Subtype.val h))
    calc Nat.card {a : A // a * a = 1} ≤ Nat.card ↥(T ×ˢ T) := Nat.card_le_card_of_injective m hm
      _ = (T ×ˢ T).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = T.card * T.card := Finset.card_product _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul hTc hTc
  have h3 : (A.map f).index ≤ 2 := by
    have hd := Subgroup.index_map_dvd (H := A) hf
    have hne : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hA
  have h4 := Subgroup.card_mul_index (A.map f)
  calc Nat.card E = Nat.card ↥(A.map f) * (A.map f).index := h4.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul (h1.trans h2) h3

theorem sec8_of_det_one {K : Type} [Field K] [Finite K] (hK : Nat.card K % 2 = 1)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (hH : ∀ g ∈ H, ((g : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1) : Sec8 ↥H := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let L := FiniteField.Extension K p 2
  have hcard : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K p 2
  have hL : Nat.card L % 4 = 1 := by
    rw [hcard]
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = 2 * m + 1 := ⟨Nat.card K / 2, by omega⟩
    rw [hm]
    ring_nf
    omega
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  refine sec8_of_gl3 hL ((Matrix.GeneralLinearGroup.map (algebraMap K L)).comp H.subtype) ?_ ?_
  · intro g g' h
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin 3) L =>
      (z : Matrix (Fin 3) (Fin 3) L) i j) h
    exact hinj (by simpa using this)
  · intro g
    show ((algebraMap K L).mapMatrix (g : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) L).det = 1
    rw [← RingHom.map_det, hH g g.2, map_one]

theorem det_eq_one_of_mem_closure {K : Type} [Field K]
    (S : Set (Matrix.GeneralLinearGroup (Fin 3) K))
    (hS : ∀ A ∈ S, ((A : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1)
    {g : Matrix.GeneralLinearGroup (Fin 3) K} (hg : g ∈ Subgroup.closure S) :
    ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have hle : Subgroup.closure S ≤ (Matrix.GeneralLinearGroup.det (n := Fin 3) (R := K)).ker := by
    rw [Subgroup.closure_le]
    intro A hA
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    simpa using hS A hA
  have := hle hg
  rw [MonoidHom.mem_ker] at this
  simpa using congrArg Units.val this

end Odd2

open Odd2

theorem sec8_statedSL {K : Type} [Field K] [Finite K] (hK : Nat.card K % 2 = 1) :
    Sec8 (StatedProj (StatedSL 3 K)) := by
  have : Finite ↥(StatedSL 3 K) := inferInstance
  refine Sec8.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) ?_
  exact sec8_of_det_one hK _ (fun g hg => det_eq_one_of_mem_closure _ (fun A hA => hA) hg)

theorem sec8_statedSU {K : Type} [Field K] [Finite K] (q : ℕ) (hK : Nat.card K % 2 = 1) :
    Sec8 (StatedProj (StatedSU 3 q K)) := by
  have : Finite ↥(StatedSU 3 q K) := inferInstance
  refine Sec8.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) ?_
  exact sec8_of_det_one hK _
    (fun g hg => det_eq_one_of_mem_closure _ (fun A hA => hA.1) hg)

theorem inputL3U3OddNoSec16_holds : InputL3U3OddNoSec16 := by
  intro Y _ _ hY H N _ hE
  have hsec : Sec8 Y := by
    rcases hY with ⟨K, hF, hfin, h3, h2, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hc, hq3, h2, ⟨e⟩⟩
    · let _ := hF
      have := hfin
      exact Sec8.of_injective e.toMonoidHom e.injective (sec8_statedSL h2)
    · let _ := hF
      have := hfin
      refine Sec8.of_injective e.toMonoidHom e.injective (sec8_statedSU q ?_)
      rw [hc, Nat.pow_mod, h2]
  obtain ⟨A, ⟨_, hA2⟩, hAc⟩ := hE
  let B' : Subgroup ↥H := A.comap (QuotientGroup.mk' N)
  let ι : ↥B' →* Y := H.subtype.comp B'.subtype
  let f : ↥B' →* ↥A := MonoidHom.codRestrict ((QuotientGroup.mk' N).comp B'.subtype) A
    (fun b => b.2)
  have hι : Function.Injective ι := H.subtype_injective.comp B'.subtype_injective
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (a : ↥H ⧸ N)
    have hhB : h ∈ B' := by
      show QuotientGroup.mk' N h ∈ A
      rw [QuotientGroup.mk'_apply, hh]
      exact a.2
    exact ⟨⟨h, hhB⟩, Subtype.ext hh⟩
  have hE2 : ∀ x : ↥A, x * x = 1 := fun x => by
    apply Subtype.ext
    have := hA2 x x.2
    simpa [pow_two] using this
  have := hsec ↥B' ↥A ι f hι hf hE2
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
