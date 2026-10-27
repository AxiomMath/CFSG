module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_conjugate_conjugate (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  simp [mul_assoc]

theorem sec126_card_conjugate (A : Subgroup G) (g : G) :
    Nat.card ↥(CFSG.conjugate A g) = Nat.card ↥A := by
  unfold CFSG.conjugate
  exact (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem sec126_conjugate_sup (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem sec126_conjugate_zpowers (x g : G) :
    CFSG.conjugate (zpowers x) g = zpowers (g⁻¹ * x * g) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem sec126_conjugate_inv_cancel (A : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate A g) g⁻¹ = A := by
  rw [sec126_conjugate_conjugate, mul_inv_cancel]
  ext x
  rw [mem_conjugate_iff]
  simp

theorem sec126_mem_normalizer_of_conjugate_eq {V : Subgroup G} {h : G}
    (hV : CFSG.conjugate V h = V) : h ∈ normalizer (V : Set G) :=
  mem_normalizer_of_conjugate_eq hV

theorem sec126_exists_conj_le [Finite G] {S H K : Subgroup G} (hS : IsSylow2Of S H)
    (hK : IsPGroup 2 K) (hKH : K ≤ H) : ∃ c ∈ H, ∀ k ∈ K, c * k * c⁻¹ ∈ S := by
  obtain ⟨Q, hQ, hKQ⟩ := exists_isSylow2Of_ge hK hKH
  obtain ⟨a, haH, ha⟩ := hS.exists_conj_mem hQ
  refine ⟨a⁻¹, inv_mem haH, fun k hk => ?_⟩
  simpa using (ha k).1 (hKQ hk)

end CFSG.OddStandard.SmallF3.Omega
