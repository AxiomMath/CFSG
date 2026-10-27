module

public import CFSG.Certificates.Kernel.E64FSound
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem good_of_act {x : Γ} {f : ℕ → ℕ} (h : ∀ p < n, act n x p = f p) :
    Good n (tab n x).toArray f := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  have e : (tab n x).toArray.getD p 0 = act n x p := img_tab x p
  rw [e, h p hp]
  exact ⟨rfl, h p hp ▸ act_lt x hp⟩

theorem good_of_tab {x : Γ} {f : ℕ → ℕ} (h : (tab n x).toArray = ((List.range n).map f).toArray) :
    Good n (tab n x).toArray f := by
  refine good_of_act fun p hp => ?_
  rw [← img_tab, h]
  simp [img, Array.getD_eq_getD_getElem?, hp]

theorem good_inv {x : Γ} {f f' : ℕ → ℕ} (h : Good n (tab n x).toArray f)
    (hinv : ∀ p < n, f' (f p) = p) : Good n (tab n x⁻¹).toArray f' := by
  refine good_of_act fun p hp => ?_
  have hq : act n x⁻¹ p < n := act_lt _ hp
  have h1 : act n x (act n x⁻¹ p) = p := by
    rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]
  have h2 : act n x (act n x⁻¹ p) = f (act n x⁻¹ p) := by
    rw [← img_tab]
    exact (h.2 _ hq).1
  rw [← hinv _ hq, ← h2, h1]

end CFSG.KC.SLDc

end
