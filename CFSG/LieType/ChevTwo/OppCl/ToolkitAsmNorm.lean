module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitBase
import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem normQ_of_induces (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) 2) {ρ : H →* Module.End F V} (hρ : Function.Injective ρ)
    {Q : Subgroup H} (hQ : IsPGroup 2 Q) {R : Subgroup (MulAut (H ⧸ Z))}
    (hRQ : ∀ α ∈ R, (Q.map (QuotientGroup.mk' Z)).map α.toMonoidHom = Q.map (QuotientGroup.mk' Z))
    {r : Equiv.Perm V} {α : MulAut (H ⧸ Z)} (hα : α ∈ R)
    (hr : Induces (QuotientGroup.mk' Z) ρ r α) : NormQ ρ r Q := by
  intro x hx
  obtain ⟨h', hh', hαx⟩ := hr.1 x
  have hy : QuotientGroup.mk' Z h' ∈ Q.map (QuotientGroup.mk' Z) := by
    rw [← hαx]
    have h1 := Subgroup.mem_map_of_mem α.toMonoidHom
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hx)
    rw [hRQ α hα] at h1
    exact h1
  obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
  have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have key : ∀ k : ℕ, ∀ v, r (ρ (x ^ k) v) = ρ (h' ^ k) (r v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      simp only [pow_succ, map_mul, Module.End.mul_apply]
      rw [ih (ρ x v), hh' v]
  have hpow : h' ^ 2 ^ n = 1 := by
    apply eq_of_forall_apply_perm hρ r
    intro v
    have hv := key (2 ^ n) v
    rw [hxn, map_one, Module.End.one_apply] at hv
    rw [map_one, Module.End.one_apply]
    exact hv.symm
  exact ⟨h', CFSG.LieType.BorelTits.mem_of_mk_mem_map Z hZc hZo hQ hy hpow, hh'⟩

end CFSG.LieType.ChevTwo.OppCl.TK
