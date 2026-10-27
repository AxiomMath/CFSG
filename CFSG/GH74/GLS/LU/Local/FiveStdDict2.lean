module

public import CFSG.GH74.GLS.LU.Local.FiveStdDict

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G]

namespace Model

variable {ι : E → G} (hM : Model ι)
include hM

theorem inL_iff {L : List E} {x : E} (hL : V L) (hx : validE x = true) :
    inL x L = true ↔ ι x ∈ S ι L := by
  constructor
  · intro h
    exact mem_S.2 ⟨x, List.contains_iff_mem.1 h, rfl⟩
  · intro hmem
    obtain ⟨y, hy, hyx⟩ := mem_S.1 hmem
    have := hM.inj y x (hL y hy) hx hyx
    subst this
    exact List.contains_iff_mem.2 hy

theorem subL_iff {L M : List E} (hL : V L) (hM' : V M) :
    subL L M = true ↔ S ι L ⊆ S ι M := by
  unfold subL
  rw [List.all_eq_true]
  constructor
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := mem_S.1 hg
    exact (hM.inL_iff hM' (hL x hx)).1 (h x hx)
  · intro h x hx
    exact (hM.inL_iff hM' (hL x hx)).2 (h (mem_S.2 ⟨x, hx, rfl⟩))

theorem eqL_iff {L M : List E} (hL : V L) (hM' : V M) :
    eqL L M = true ↔ S ι L = S ι M := by
  unfold eqL
  rw [Bool.and_eq_true, hM.subL_iff hL hM', hM.subL_iff hM' hL]
  exact Set.Subset.antisymm_iff.symm

theorem V_mulLL {L M : List E} (hL : V L) (hM' : V M) : V (mulLL L M) := by
  intro z hz
  simp only [mulLL, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact hM.valid_mul _ _ (hL x hx) (hM' y hy)

theorem S_mulLL {L M : List E} (hL : V L) (hM' : V M) :
    S ι (mulLL L M) = S ι L * S ι M := by
  ext g
  simp only [mem_S, mulLL, List.mem_flatMap, List.mem_map, Set.mem_mul]
  constructor
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨ι x, ⟨x, hx, rfl⟩, ι y, ⟨y, hy, rfl⟩, (hM.map_mul x y (hL x hx) (hM' y hy)).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨mulE x y, ⟨x, hx, y, hy, rfl⟩, hM.map_mul x y (hL x hx) (hM' y hy)⟩

theorem V_powers {g : E} (hg : validE g = true) (n : ℕ) : V (powers g n) := by
  intro z hz
  simp only [powers, List.mem_map, List.mem_range] at hz
  obtain ⟨i, -, rfl⟩ := hz
  exact hM.valid_powE hg i

theorem S_powers {g : E} (hg : validE g = true) (n : ℕ) :
    S ι (powers g n) = {h | ∃ i < n, h = ι g ^ i} := by
  ext h
  simp only [mem_S, powers, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, hM.map_powE hg i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hM.map_powE hg i⟩

theorem V_ppE {a b : E} (ha : validE a = true) (hb : validE b = true) (m n : ℕ) : V (ppE a b m n) :=
  hM.V_mulLL (hM.V_powers ha m) (hM.V_powers hb n)

theorem S_ppE {a b : E} (ha : validE a = true) (hb : validE b = true) (m n : ℕ) :
    S ι (ppE a b m n) = {h | ∃ i < m, ∃ j < n, h = ι a ^ i * ι b ^ j} := by
  rw [ppE, hM.S_mulLL (hM.V_powers ha m) (hM.V_powers hb n), hM.S_powers ha, hM.S_powers hb]
  ext h
  simp only [Set.mem_mul, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩

theorem V_conjLL {c : E} {L : List E} (hc : validE c = true) (hL : V L) : V (conjLL c L) := by
  intro z hz
  simp only [conjLL, List.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact hM.valid_conjI hc (hL x hx)

theorem S_conjLL {c : E} {L : List E} (hc : validE c = true) (hL : V L) :
    S ι (conjLL c L) = {h | ∃ g ∈ S ι L, h = ι c * g * (ι c)⁻¹} := by
  ext h
  simp only [mem_S, conjLL, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨ι x, ⟨x, hx, rfl⟩, hM.map_conjI hc (hL x hx)⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hM.map_conjI hc (hL x hx)⟩

theorem commE_iff {x y : E} (hx : validE x = true) (hy : validE y = true) :
    commE x y = true ↔ ι x * ι y = ι y * ι x := by
  unfold commE
  rw [beq_iff_eq]
  constructor
  · intro h
    rw [← hM.map_mul _ _ hx hy, ← hM.map_mul _ _ hy hx, h]
  · intro h
    rw [← hM.map_mul _ _ hx hy, ← hM.map_mul _ _ hy hx] at h
    exact hM.inj _ _ (hM.valid_mul _ _ hx hy) (hM.valid_mul _ _ hy hx) h

theorem normG_iff {g : E} {gens L : List E} (hg : validE g = true) (hgens : V gens) (hL : V L) :
    normG g gens L = true ↔ ∀ x ∈ gens, ι g * ι x * (ι g)⁻¹ ∈ S ι L := by
  unfold normG
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    rw [← hM.map_conjI hg (hgens x hx)]
    exact (hM.inL_iff hL (hM.valid_conjI hg (hgens x hx))).1 (h x hx)
  · intro h x hx
    refine (hM.inL_iff hL (hM.valid_conjI hg (hgens x hx))).2 ?_
    rw [hM.map_conjI hg (hgens x hx)]
    exact h x hx

theorem normAll_iff {hs gens L : List E} (hs' : V hs) (hgens : V gens) (hL : V L) :
    normAll hs gens L = true ↔ ∀ h ∈ hs, ∀ x ∈ gens, ι h * ι x * (ι h)⁻¹ ∈ S ι L := by
  unfold normAll
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    exact (hM.normG_iff (hs' k hk) hgens hL).1 (h k hk)
  · intro h k hk
    exact (hM.normG_iff (hs' k hk) hgens hL).2 (h k hk)

theorem cenG_iff {g : E} {gens : List E} (hg : validE g = true) (hgens : V gens) :
    cenG g gens = true ↔ ∀ x ∈ gens, ι g * ι x = ι x * ι g := by
  unfold cenG
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    exact (hM.commE_iff hg (hgens x hx)).1 (h x hx)
  · intro h x hx
    exact (hM.commE_iff hg (hgens x hx)).2 (h x hx)

end Model

theorem nodupL_iff {L : List E} : nodupL L = true ↔ L.Nodup := by
  unfold nodupL
  rw [List.all_eq_true]
  constructor
  · intro h
    rw [List.nodup_iff_count_le_one]
    intro x
    by_cases hx : x ∈ L
    · have := h x hx
      simp only [beq_iff_eq] at this
      have hc : List.count x L = (L.filter fun y => y == x).length := by
        rw [List.count_eq_countP, List.countP_eq_length_filter]
      omega
    · rw [List.count_eq_zero_of_not_mem hx]
      omega
  · intro h x hx
    simp only [beq_iff_eq]
    have hc : List.count x L = (L.filter fun y => y == x).length := by
      rw [List.count_eq_countP, List.countP_eq_length_filter]
    rw [← hc]
    exact List.count_eq_one_of_mem h hx

end CFSG.GH74.GLS.LU.Local.FiveStd
