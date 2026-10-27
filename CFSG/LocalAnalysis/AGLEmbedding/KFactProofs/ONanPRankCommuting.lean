module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

noncomputable def powProdHom {p : ℕ} [NeZero p] {C : Type*} [CommGroup C] {r : ℕ}
    (v : Fin r → C) (hv : ∀ i, v i ^ p = 1) : (Fin r → Multiplicative (ZMod p)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

open scoped IsMulCommutative in
theorem le_pRank_of_commuting_pow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {r : ℕ} (u : Fin r → G) (hpow : ∀ i, u i ^ p = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → ZMod p, a ≠ 0 →
      (List.ofFn fun i => u i ^ (a i).val).prod ≠ 1)
    {H : Subgroup G} (hH : ∀ i, u i ∈ H) : r ≤ pRank p H := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ p = 1 := fun i => Subtype.ext (by simpa [v] using hpow i)
  let φ : (Fin r → Multiplicative (ZMod p)) →* G := C.subtype.comp (powProdHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, powProdHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
    funext i
    exact Multiplicative.toAdd.injective (congrFun h0 i)
  have hrange : φ.range ≤ H := by
    rintro _ ⟨a, rfl⟩
    rw [hφ]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact pow_mem (hH i) _
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt mul_comm (fun a => ?_) ?_ φ hinj hrange
  · funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · simp

end CFSG.AGLEmbedding
