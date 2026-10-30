module

public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LieType.ChevTwo.OppCl.Toolkit
import CFSG.LieType.ChevTwo.OppCl.SLInduces
import CFSG.LieType.ChevTwo.OppCl.SLAut
import CFSG.LieType.ChevTwo.OppCl.SLAutTwo
import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section SL

variable (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

theorem semilinGroup_map_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) : r 0 = 0 :=
  map_zero (AddMonoidHom.mk' r hr.1)

theorem semilinGroup_map_sub {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) (u v : V) : r (u - v) = r u - r v :=
  map_sub (AddMonoidHom.mk' r hr.1) u v

theorem exists_statedSL_of_sq_zero [CharP F 2] (g : (Fin n → F) →ₗ[F] (Fin n → F))
    (hg : ∀ v, g (g v) = 0) :
    ∃ y : StatedSL n F, ∀ v, natRep (StatedSL n F) y v = v + g v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' (LinearMap.id + g) with hM
  have hMv : ∀ v, Matrix.mulVec M v = v + g v := by
    intro v
    rw [hM, LinearMap.toMatrix'_mulVec]
    simp
  have h2 : ∀ w : Fin n → F, w + w = 0 := fun w => by
    funext i
    simp [CharTwo.add_self_eq_zero]
  have hMM : M * M = 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [← Matrix.mulVec_mulVec, hMv, hMv, map_add, hg, Matrix.one_mulVec, add_zero, add_assoc,
      h2, add_zero]
  have hdet : M.det = 1 := by
    have h1 : M.det ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, ← Matrix.det_mul, hMM, Matrix.det_one]
    exact eq_one_of_pow_char_pow_eq_one 2 h1
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0, Subgroup.subset_closure ?_⟩, fun v => ?_⟩
  · show (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0 : Matrix (Fin n) (Fin n) F).det = 1
    simpa using hdet
  · rw [natRep_apply]
    exact hMv v

theorem raise_SL (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    RaiseProp (fun _ => True) (natRep (StatedSL n F))
      (fun Q => fixFlag (natRep (StatedSL n F)) Q) p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Rh hs _ hRp hRN Q hQ hRQ x hx hx1 hxc
  have hinv : ∀ r ∈ Rh, ∀ k, ∀ v ∈ fixFlag (natRep (StatedSL n F)) Q k,
      r v ∈ fixFlag (natRep (StatedSL n F)) Q k :=
    fun r hr => fixFlag_inv _ r (hs hr) Q (hRQ r hr) (hRQ r⁻¹ (inv_mem hr))
  let N : (Fin n → F) →ₗ[F] (Fin n → F) := natRep (StatedSL n F) x - LinearMap.id
  have hNv : ∀ v, N v = natRep (StatedSL n F) x v - v := fun v => rfl
  have hN : ∀ k, ∀ v ∈ fixFlag (natRep (StatedSL n F)) Q (k + 1),
      N v ∈ fixFlag (natRep (StatedSL n F)) Q k := fun k v hv => hx.2 k v hv
  have hNc : ∀ r ∈ Rh, ∀ v, r (N v) = N (r v) := by
    intro r hr v
    rw [hNv, hNv, semilinGroup_map_sub (hs hr), hxc r hr v]
  have hN0 : ∃ k, ∃ v ∈ fixFlag (natRep (StatedSL n F)) Q k, N v ≠ 0 := by
    obtain ⟨m, hm⟩ := exists_fixFlag_eq_top (natRep (StatedSL n F)) 2 Q hQ
    by_contra hcon
    push Not at hcon
    apply hx1
    apply natRep_injective (StatedSL n F)
    apply LinearMap.ext
    intro v
    have := hcon m v (by rw [hm]; trivial)
    rw [hNv, sub_eq_zero] at this
    rw [this, map_one]
    rfl
  obtain ⟨g, k, hgc, hg2, -, -, v, hv, hgv⟩ := exists_raising p hp2 Rh hs hRp
    (fixFlag (natRep (StatedSL n F)) Q) rfl (fixFlag_mono _ Q) hinv ⊤ ⊥ (fun _ => le_top)
    (fun r hr w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw]
      exact semilinGroup_map_zero (hs hr))
    disjoint_bot_right N hN hNc hN0
  obtain ⟨y, hy⟩ := exists_statedSL_of_sq_zero n F g hg2
  refine ⟨y, fun r hr w => ?_, fun hys => hgv ?_⟩
  · rw [hy, hy, (hs hr).1, hgc r hr w]
  · have h1 := (hys k v hv).1
    rw [hy] at h1
    simpa using sub_mem h1 hv

theorem induced_PSL (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (R : Subgroup (MulAut (StatedProj (StatedSL n F)))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ r : Equiv.Perm (Fin n → F), r ∈ semilinGroup F (Fin n → F) ∧ True ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))
        (natRep (StatedSL n F)) r α := by
  intro α hα
  obtain ⟨k, hk⟩ := hR ⟨α, hα⟩
  have hαk : α ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨A, σ, h⟩ := exists_conj_of_odd_pow n F hn ((Fact.out : p.Prime).odd_of_ne_two hp2).pow α
    hαk
  exact ⟨semilinMap A σ, semilinMap_mem A σ, trivial, induces_of_conj _ A σ α h⟩

theorem induced_PSL_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hF : 4 ≤ Nat.card F)
    (R : Subgroup (MulAut (StatedProj (StatedSL 2 F)))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ r : Equiv.Perm (Fin 2 → F), r ∈ semilinGroup F (Fin 2 → F) ∧ True ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)))
        (natRep (StatedSL 2 F)) r α := by
  intro α _
  obtain ⟨A, σ, h⟩ := exists_conj_two F α
  exact ⟨semilinMap A σ, semilinMap_mem A σ, trivial, induces_of_conj _ A σ α h⟩

end SL

end CFSG.LieType.ChevTwo.OppCl
