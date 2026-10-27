module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure
public import CFSG.LieType.Ree.SuzukiOvoidTorus

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_mulVec_e0 (u v : K) :
    suzukiS a u v *ᵥ ![1, 0, 0, 0] = ![1, u, v, suzukiN a u v] := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiLine_eq_iff {u v c d : K} :
    suzukiLine a K u v = suzukiLine a K c d ↔ u = c ∧ v = d := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  rw [suzukiLine, suzukiLine, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨k, hk⟩ := h
  have h0 := congrFun hk 0
  have h1 := congrFun hk 1
  have h2 := congrFun hk 2
  simp [Units.smul_def] at h0 h1 h2
  rw [h0, Units.val_one, one_mul] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

theorem suzukiLine_ne_suzukiInfty (u v : K) : suzukiLine a K u v ≠ suzukiInfty K := by
  intro h
  rw [suzukiLine, suzukiInfty, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨k, hk⟩ := h
  have h0 := congrFun hk 0
  simp at h0

theorem mem_suzukiOmega_diff_iff {x : ℙ K (Fin 4 → K)} :
    x ∈ suzukiOmega a K \ {suzukiInfty K} ↔ ∃ u v : K, suzukiLine a K u v = x := by
  constructor
  · rintro ⟨(⟨⟨u, v⟩, rfl⟩ | rfl), hx⟩
    · exact ⟨u, v, rfl⟩
    · exact absurd rfl hx
  · rintro ⟨u, v, rfl⟩
    exact ⟨suzukiLine_mem_suzukiOmega a K u v, suzukiLine_ne_suzukiInfty u v⟩

theorem suzukiSElt_smul_suzukiLine
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (c d u v : K) : suzukiSElt a K c d • suzukiLine a K u v =
      suzukiLine a K (c + u) (d + v + c ^ 2 ^ (a + 1) * u) := by
  refine suzuki_smul_mk_eq a _ _ _ 1 ?_
  rw [coe_suzukiSElt, ← suzukiS_mulVec_e0, mulVec_mulVec,
    (suzuki_unipotent_product a hK).1 c d u v, suzukiS_mulVec_e0, one_smul]

theorem suzukiSElt_smul_suzukiInfty (c d : K) :
    suzukiSElt a K c d • suzukiInfty K = suzukiInfty K := by
  refine suzuki_smul_mk_eq a _ _ _ 1 ?_
  rw [coe_suzukiSElt]
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzuki_ovoid_unipotent_action
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ c d : K, suzukiSElt a K c d • suzukiInfty K = suzukiInfty K) ∧
    (∀ c d u v : K, suzukiSElt a K c d • suzukiLine a K u v =
      suzukiLine a K (c + u) (d + v + c ^ 2 ^ (a + 1) * u)) ∧
    (∀ u v c d : K, suzukiLine a K u v = suzukiLine a K c d → u = c ∧ v = d) ∧
    (∀ u v : K, suzukiLine a K u v ≠ suzukiInfty K) ∧
    (∀ g ∈ suzukiU a K, ∀ x ∈ suzukiOmega a K \ {suzukiInfty K},
      g • x ∈ suzukiOmega a K \ {suzukiInfty K}) ∧
    (∀ x ∈ suzukiOmega a K \ {suzukiInfty K}, ∀ y ∈ suzukiOmega a K \ {suzukiInfty K},
      ∃! g : suzukiU a K, (g : suzukiGroup a K) • x = y) ∧
    (suzukiOmega a K).ncard = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  refine ⟨suzukiSElt_smul_suzukiInfty, suzukiSElt_smul_suzukiLine hK,
    fun u v c d h => suzukiLine_eq_iff.1 h, suzukiLine_ne_suzukiInfty, ?_, ?_, ?_⟩
  · intro g hg x hx
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    obtain ⟨u, v, rfl⟩ := mem_suzukiOmega_diff_iff.1 hx
    rw [suzukiSElt_smul_suzukiLine hK]
    exact mem_suzukiOmega_diff_iff.2 ⟨_, _, rfl⟩
  · intro x hx y hy
    obtain ⟨u, v, rfl⟩ := mem_suzukiOmega_diff_iff.1 hx
    obtain ⟨u', v', rfl⟩ := mem_suzukiOmega_diff_iff.1 hy
    refine ⟨⟨suzukiSElt a K (u' - u) (v' - v - (u' - u) ^ 2 ^ (a + 1) * u),
      suzukiSElt_mem_suzukiU a K _ _⟩, ?_, ?_⟩
    · change suzukiSElt a K _ _ • _ = _
      rw [suzukiSElt_smul_suzukiLine hK, suzukiLine_eq_iff]
      constructor <;> ring
    · rintro ⟨g, hg⟩ hgx
      obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hg
      change suzukiSElt a K c d • _ = _ at hgx
      rw [suzukiSElt_smul_suzukiLine hK, suzukiLine_eq_iff] at hgx
      obtain ⟨h1, h2⟩ := hgx
      have hc : c = u' - u := by rw [← h1]; ring
      subst hc
      refine Subtype.ext (congrArg₂ (suzukiSElt a K) rfl ?_)
      rw [← h2]
      ring
  · have hinj : Function.Injective fun p : K × K => suzukiLine a K p.1 p.2 := fun p q h =>
      Prod.ext (suzukiLine_eq_iff.1 h).1 (suzukiLine_eq_iff.1 h).2
    have hdisj : Disjoint (Set.range fun p : K × K => suzukiLine a K p.1 p.2)
        {suzukiInfty K} := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨p, hp⟩
      exact suzukiLine_ne_suzukiInfty p.1 p.2 hp
    rw [suzukiOmega, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_singleton, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj,
      Nat.card_prod, hK, sq]

end CFSG.LieType.Ree
