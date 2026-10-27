module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
import CFSG.GroupTheory.SmallOrderNotSimple
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding.KFactProofs.SmallIdent CFSG.Blueprint Certificates.ONanSmallM11

theorem fixed_iff_of_mem_m11E {e : Equiv.Perm (Fin 11)} (he : e ∈ m11E) (he1 : e ≠ 1)
    (i : Fin 11) : e i = i ↔ i = 0 ∨ i = 1 := by
  simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl he1
  all_goals revert i; decide +kernel

theorem weakTI_m11T0 :
    WeakTI m11T0 := by
  intro g x hx hx1 hxg
  have hne (z : ↥NativeSporadic.M11) (hz : z ≠ 1) : (z : Equiv.Perm (Fin 11)) ≠ 1 :=
    fun h => hz (Subtype.ext h)
  have hxg1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have h1 := fun a => fixed_iff_of_mem_m11E (mem_m11T0_iff_mem_m11E.1 hx) (hne x hx1) a
  have h2 := fun a => fixed_iff_of_mem_m11E (mem_m11T0_iff_mem_m11E.1 hxg) (hne _ hxg1) a
  have key (a : Fin 11) : ((g : Equiv.Perm (Fin 11)) a = 0 ∨ (g : Equiv.Perm (Fin 11)) a = 1) ↔
      a = 0 ∨ a = 1 := by
    rw [← h1, ← h2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  have hinj : (g : Equiv.Perm (Fin 11)) 0 ≠ (g : Equiv.Perm (Fin 11)) 1 :=
    fun h => absurd ((g : Equiv.Perm (Fin 11)).injective h) (by decide)
  rw [normalizer_m11T0, mem_stabilizer_duad_iff g (by decide)]
  rcases (key 0).2 (Or.inl rfl) with h0 | h0 <;> rcases (key 1).2 (Or.inr rfl) with h1 | h1
  · exact absurd (h0.trans h1.symm) hinj
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (h0.trans h1.symm) hinj

theorem signalizerAutAt_mEleven
    {p : ℕ} (hp : p = 3) :
    SignalizerAutAt p (.sporadic .M11) := by
  subst hp
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  refine signalizerAutAt_of_model_weakTI Nat.prime_three ?_ e center_m11 (R := m11T0) ?_
    weakTI_m11T0
  · rintro ⟨d, hd, -⟩
    cases hd
  · rw [card_m11T0, CFSG.Sporadic.Mathieu.card_M11,
      CFSG.GroupTheory.factorization_eq_of_pow_dvd Nat.prime_three (by norm_num) (k := 2)
        (by norm_num) (by norm_num)]
    norm_num

end CFSG.LocalAnalysis.RankFourTheoremC
