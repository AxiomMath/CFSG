module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoA
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Module (ZMod 2) K]

@[expose] noncomputable def suzukiAToU [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = x ^ 2 ^ (a + 1)) : SuzukiA K φ →* suzukiU a K where
  toFun p := ⟨suzukiSElt a K p.fst (p.snd + p.fst ^ (2 ^ (a + 1) + 1)),
    suzukiSElt_mem_suzukiU a K _ _⟩
  map_one' := by
    refine Subtype.ext ?_
    change suzukiSElt a K 0 (0 + 0 ^ (2 ^ (a + 1) + 1)) = 1
    rw [zero_pow (Nat.succ_ne_zero _), add_zero, suzukiSElt_zero_zero hK]
  map_mul' p p' := by
    obtain ⟨h2, hadd, -⟩ := suzuki_frob_data a hK
    have key : ∀ x y z w : K, z + w + x * y ^ 2 ^ (a + 1) + (x + y) ^ (2 ^ (a + 1) + 1) =
        z + x ^ (2 ^ (a + 1) + 1) + (w + y ^ (2 ^ (a + 1) + 1)) + x ^ 2 ^ (a + 1) * y := by
      intro x y z w
      rw [pow_succ (x + y), hadd, pow_succ x, pow_succ y]
      linear_combination x * y ^ 2 ^ (a + 1) * h2
    refine Subtype.ext ?_
    change suzukiSElt a K (p.fst + p'.fst) (p.snd + p'.snd + p.fst * φ p'.fst +
        (p.fst + p'.fst) ^ (2 ^ (a + 1) + 1)) =
      suzukiSElt a K p.fst (p.snd + p.fst ^ (2 ^ (a + 1) + 1)) *
        suzukiSElt a K p'.fst (p'.snd + p'.fst ^ (2 ^ (a + 1) + 1))
    rw [suzukiSElt_mul hK, hφ, key]

theorem Suzuki_root_A_isomorphism [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = x ^ 2 ^ (a + 1)) :
    ∃ ι : suzukiU a K ≃* SuzukiA K φ,
      (∀ u v : K, ι ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩ =
        ⟨u, v + u ^ (2 ^ (a + 1) + 1)⟩) ∧
      (∀ x z : K, ((ι.symm ⟨x, z⟩ : suzukiU a K) : suzukiGroup a K) =
        suzukiSElt a K x (z + x ^ (2 ^ (a + 1) + 1))) ∧
      ∀ v : K, ι ⟨suzukiSElt a K 0 v, suzukiSElt_mem_suzukiU a K 0 v⟩ = ⟨0, v⟩ := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  set ψ := suzukiAToU hK φ hφ with hψ
  have hψ_apply : ∀ x z, ((ψ ⟨x, z⟩ : suzukiU a K) : suzukiGroup a K) =
      suzukiSElt a K x (z + x ^ (2 ^ (a + 1) + 1)) := fun _ _ => rfl
  have hinj : Function.Injective ψ := by
    intro p p' h
    have h' := congrArg (fun g : suzukiU a K => (g : suzukiGroup a K)) h
    simp only [hψ_apply] at h'
    obtain ⟨h1, h3⟩ := suzukiSElt_inj.1 h'
    rw [h1] at h3
    exact BinExt.ext h1 (add_right_cancel h3)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨g, hg⟩
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    refine ⟨⟨u, v + u ^ (2 ^ (a + 1) + 1)⟩, Subtype.ext ?_⟩
    rw [hψ_apply]
    refine congrArg (suzukiSElt a K u) ?_
    linear_combination u ^ (2 ^ (a + 1) + 1) * h2
  set e := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩ with he
  have hι : ∀ u v : K, e.symm ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩ =
      ⟨u, v + u ^ (2 ^ (a + 1) + 1)⟩ := by
    intro u v
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    change _ = ((ψ ⟨u, v + u ^ (2 ^ (a + 1) + 1)⟩ : suzukiU a K) : suzukiGroup a K)
    rw [hψ_apply]
    refine congrArg (suzukiSElt a K u) ?_
    linear_combination -(u ^ (2 ^ (a + 1) + 1)) * h2
  refine ⟨e.symm, hι, fun x z => ?_, fun v => ?_⟩
  · rw [MulEquiv.symm_symm]
    exact hψ_apply x z
  · rw [hι, zero_pow (Nat.succ_ne_zero _), add_zero]

end CFSG.LocalAnalysis.ComponentInitial
