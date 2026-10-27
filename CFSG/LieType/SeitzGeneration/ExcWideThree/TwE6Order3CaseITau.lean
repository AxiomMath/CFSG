module

public import Certificates.Data.E6CaseI
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Core
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

theorem node3_eq (k : ℕ) : node3 k = e6Certificate.root k 3 := rfl

theorem three_dvd_iff {k : ℕ} {δ : Fin Tag.E6.rank → ℤ} (h : e6Certificate.root k = δ) :
    (3 : ℤ) ∣ δ 3 ↔ node3 k % 3 = 0 := by
  rw [node3_eq, h]
  exact Int.dvd_iff_emod_eq_zero

theorem pairZ_castL_eq {k : ℕ} (hk : k < e6Certificate.roots.length) (vec : List ℕ) :
    pairZ (RootTables.ofCert e6Certificate) k (castL vec) =
      ∑ x : Fin Tag.E6.rank, e6Certificate.root k x * ((vec.getD x 0 : ℕ) : ℤ) := by
  unfold pairZ castL dotL
  rw [vecs_getD e6Certificate hk, sum_zipWith_ofFn_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [getD_map_natCast]

theorem killBit_iff {r : ℕ} (hr : r < 72) (n : ℕ) :
    killBit (RootTables.ofCert e6Certificate) r n = true ↔
      triPairing (vec3 (τ := .E6) (digits3 .E6 n)) (e6Certificate.root r) = 0 := by
  have h2 : ((pairZ (RootTables.ofCert e6Certificate) r (castL (digits3 .E6 n)) : ℤ) :
      ZMod 3) = triPairing (vec3 (τ := .E6) (digits3 .E6 n)) (e6Certificate.root r) := by
    rw [pairZ_castL_eq (len72 ▸ hr), Int.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [vec3, Int.cast_mul, Int.cast_natCast]
    ring
  unfold killBit
  rw [decide_eq_true_iff, ← h2]
  constructor
  · intro h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  · intro h
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h)

theorem exists_idx (b : Fin Tag.E6.rank → ZMod 3) :
    ∃ n < 729, vec3 (τ := .E6) (digits3 .E6 n) = b := by
  have h729 : 3 ^ Tag.E6.rank = 729 := by decide
  obtain ⟨n, hn, hb⟩ := exists_vec3OfIndex b
  rw [h729] at hn
  exact ⟨n, hn, by rw [vec3_digits3, hb]⟩

theorem card_filter_rootFinset (p : (Fin Tag.E6.rank → ℤ) → Prop) [DecidablePred p] :
    ((rootFinset Tag.E6).filter p).card =
      ((List.range 72).filter fun r => decide (p (e6Certificate.root r))).length := by
  have hset : (rootFinset Tag.E6).filter p =
      (((List.range 72).filter fun r => decide (p (e6Certificate.root r))).map
        e6Certificate.root).toFinset := by
    ext γ
    simp only [Finset.mem_filter, mem_rootFinset, List.mem_toFinset, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hγ, hp⟩
      obtain ⟨r, hr, rfl⟩ := exists_root72 hγ
      exact ⟨r, ⟨hr, hp⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hp⟩, rfl⟩
      exact ⟨isRoot_root72 hr, hp⟩
  rw [hset, List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
  exact root_inj (List.mem_range.1 (List.mem_filter.1 ha).1)
    (List.mem_range.1 (List.mem_filter.1 hb).1) hab

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3
