module

public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.LieType.SeitzGeneration.Coprime
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.GroupTheory

theorem exists_normalized_generating_rSubgroups_of_hasGoodOppositePRadicals
    {K : Type*} [Group K] [Finite K] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hgood : ∀ Q : Subgroup K, Q ≠ ⊥ → IsRadicalPGroup r ⊤ Q → HasGoodOppositePRadicals r ⊤ Q)
    (E : Subgroup (MulAut K)) (hE : IsPGroup 2 E)
    (R : Subgroup K) (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) :
    ∃ U V : Subgroup K, R ≤ U ∧ IsPGroup r U ∧ IsPGroup r V ∧
      (∀ e ∈ E, U.map e.toMonoidHom = U) ∧ (∀ e ∈ E, V.map e.toMonoidHom = V) ∧ U ⊔ V = ⊤ := by
  open CFSG.GH74.GLS.Stage2.OddAut in
  obtain ⟨m, hRm, hstab⟩ := exists_radSeq_stable (p := r) hRr
  have hRU : R ≤ radInf r R := le_radInf R
  have hU_p : IsPGroup r (radInf r R) := by
    rw [hRm]
    exact radSeq_isPGroup hRr m
  have hU_rad : IsRadicalPGroup r ⊤ (radInf r R) := by
    rw [IsRadicalPGroup, top_inf_eq, hRm]
    exact hstab
  have hU_E : ∀ e ∈ E, (radInf r R).map e.toMonoidHom = radInf r R :=
    fun e he => radInf_map_eq e (hER e he)
  generalize radInf r R = U at hRU hU_p hU_rad hU_E
  have hU_ne : U ≠ ⊥ := fun hbot => hR (le_bot_iff.mp (hRU.trans hbot.le))
  have hGood := hgood U hU_ne hU_rad
  obtain ⟨V, hV, hV_E⟩ := hGood.exists_fixed_of_twoGroup hr2 E hE
    (fun e _ => Subgroup.map_top_of_surjective _ e.surjective) hU_E
  refine ⟨U, V, hRU, hU_p, hV.1.isPGroup, hU_E, hV_E, ?_⟩
  obtain ⟨V₀, -, hgen, hconj⟩ := hGood
  obtain ⟨u, hu, rfl⟩ := hconj V hV
  have huU : U.map (MulAut.conj u).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
  rw [← huU, ← Subgroup.map_sup, hgen,
    Subgroup.map_top_of_surjective _ (MulAut.conj u).surjective]

theorem planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals
    {K : Type*} [Group K] [Finite K] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hgood : ∀ Q : Subgroup K, Q ≠ ⊥ → IsRadicalPGroup r ⊤ Q → HasGoodOppositePRadicals r ⊤ Q)
    (E : Subgroup (MulAut K)) (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (R : Subgroup K) (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) : PlaneGen E := by
  obtain ⟨U, V, -, hU_p, hV_p, hU_E, hV_E, htop⟩ :=
    exists_normalized_generating_rSubgroups_of_hasGoodOppositePRadicals hr2 hgood E hE.isPGroup R
      hR hRr hER
  have hA : 2 ^ 2 ≤ Nat.card E := by rw [h4]; norm_num
  have hodd {X : Subgroup K} (hX : IsPGroup r X) : ¬ 2 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow.not_two_dvd_nat
  unfold PlaneGen
  rw [eq_top_iff, ← htop]
  exact sup_le (le_planeClosure_of_invariant_coprime hE hA hU_E (hodd hU_p))
    (le_planeClosure_of_invariant_coprime hE hA hV_E (hodd hV_p))

end CFSG.LieType.SeitzGeneration

