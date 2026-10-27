module

public import CFSG.ClassicalInvolution.Q3.M11Multiplier

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv

section Words

@[expose] def m11Letter : ℕ → Perm (Fin 11)
  | 0 => m11gA
  | 1 => m11gB
  | 2 => m11gA⁻¹
  | _ => m11gB⁻¹

@[expose] def m11Eval : List ℕ → Perm (Fin 11)
  | [] => 1
  | g :: w => m11Letter g * m11Eval w

private def m11InvWords : List (List ℕ) :=
  [[], [0], [1], [3], [1, 0], [3, 0], [0, 1], [1, 1], [0, 3], [1, 1, 0], [0, 3, 0], [1, 0, 1],
    [3, 0, 1], [0, 1, 1], [1, 0, 3], [3, 0, 3], [0, 1, 1, 0], [1, 0, 3, 0], [3, 0, 3, 0],
    [0, 1, 0, 1], [1, 1, 0, 1], [0, 3, 0, 1], [0, 1, 0, 3], [0, 3, 0, 3], [1, 0, 1, 1, 0],
    [3, 0, 1, 1, 0], [1, 1, 0, 3, 0], [0, 3, 0, 3, 0], [1, 0, 1, 0, 1], [3, 0, 1, 0, 1],
    [0, 1, 1, 0, 1], [1, 0, 3, 0, 1], [3, 0, 3, 0, 1], [1, 0, 1, 0, 3], [3, 0, 1, 0, 3],
    [1, 0, 3, 0, 3], [3, 0, 3, 0, 3], [0, 1, 0, 1, 1, 0], [0, 3, 0, 1, 1, 0], [0, 1, 1, 0, 3, 0],
    [1, 0, 3, 0, 3, 0], [3, 0, 3, 0, 3, 0], [0, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 1],
    [0, 3, 0, 1, 0, 1], [0, 1, 0, 3, 0, 1], [1, 1, 0, 3, 0, 1], [0, 3, 0, 3, 0, 1],
    [0, 1, 0, 1, 0, 3], [1, 1, 0, 1, 0, 3], [0, 3, 0, 1, 0, 3], [0, 1, 0, 3, 0, 3],
    [1, 1, 0, 3, 0, 3], [0, 3, 0, 3, 0, 3], [3, 0, 1, 0, 1, 1, 0], [1, 0, 3, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 3, 0], [3, 0, 1, 1, 0, 3, 0], [0, 1, 0, 3, 0, 3, 0], [1, 1, 0, 3, 0, 3, 0],
    [0, 3, 0, 3, 0, 3, 0], [1, 0, 1, 0, 1, 0, 1], [3, 0, 1, 0, 1, 0, 1], [0, 1, 1, 0, 1, 0, 1],
    [1, 0, 3, 0, 1, 0, 1], [3, 0, 3, 0, 1, 0, 1], [1, 0, 1, 0, 3, 0, 1], [3, 0, 1, 0, 3, 0, 1],
    [0, 1, 1, 0, 3, 0, 1], [1, 0, 3, 0, 3, 0, 1], [3, 0, 3, 0, 3, 0, 1], [1, 0, 1, 0, 1, 0, 3],
    [0, 1, 1, 0, 1, 0, 3], [1, 0, 3, 0, 1, 0, 3], [3, 0, 3, 0, 1, 0, 3], [1, 0, 1, 0, 3, 0, 3],
    [3, 0, 1, 0, 3, 0, 3], [0, 1, 1, 0, 3, 0, 3], [1, 0, 3, 0, 3, 0, 3], [0, 3, 0, 1, 0, 1, 1, 0],
    [0, 1, 0, 3, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0, 3, 0], [1, 1, 0, 1, 1, 0, 3, 0],
    [0, 3, 0, 1, 1, 0, 3, 0], [1, 0, 1, 0, 3, 0, 3, 0], [3, 0, 1, 0, 3, 0, 3, 0],
    [0, 1, 1, 0, 3, 0, 3, 0], [1, 0, 3, 0, 3, 0, 3, 0], [3, 0, 3, 0, 3, 0, 3, 0],
    [0, 1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 1, 0, 1], [0, 3, 0, 1, 0, 1, 0, 1],
    [3, 0, 1, 1, 0, 1, 0, 1], [0, 1, 0, 3, 0, 1, 0, 1], [1, 1, 0, 3, 0, 1, 0, 1],
    [0, 1, 0, 1, 0, 3, 0, 1], [1, 1, 0, 1, 0, 3, 0, 1], [0, 3, 0, 1, 0, 3, 0, 1],
    [1, 0, 1, 1, 0, 3, 0, 1], [3, 0, 1, 1, 0, 3, 0, 1], [1, 1, 0, 3, 0, 3, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 3], [1, 0, 1, 1, 0, 1, 0, 3], [3, 0, 1, 1, 0, 1, 0, 3],
    [1, 1, 0, 3, 0, 1, 0, 3], [0, 3, 0, 3, 0, 1, 0, 3], [1, 1, 0, 1, 0, 3, 0, 3],
    [0, 3, 0, 1, 0, 3, 0, 3], [1, 0, 3, 0, 1, 0, 1, 1, 0], [3, 0, 3, 0, 1, 0, 1, 1, 0],
    [3, 0, 1, 0, 3, 0, 1, 1, 0], [0, 1, 0, 1, 0, 3, 0, 3, 0], [1, 1, 0, 1, 0, 3, 0, 3, 0],
    [1, 0, 1, 1, 0, 3, 0, 3, 0], [3, 0, 1, 1, 0, 3, 0, 3, 0], [1, 1, 0, 3, 0, 3, 0, 3, 0],
    [0, 3, 0, 3, 0, 3, 0, 3, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1], [3, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1, 0, 1], [0, 3, 0, 1, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 3, 0, 1],
    [3, 0, 1, 0, 1, 0, 3, 0, 1], [1, 0, 3, 0, 1, 0, 3, 0, 1], [3, 0, 3, 0, 1, 0, 3, 0, 1],
    [0, 1, 0, 1, 1, 0, 3, 0, 1], [0, 1, 1, 0, 3, 0, 3, 0, 1], [1, 0, 1, 0, 1, 0, 1, 0, 3],
    [1, 1, 0, 1, 1, 0, 1, 0, 3], [0, 3, 0, 1, 1, 0, 1, 0, 3], [0, 1, 1, 0, 3, 0, 1, 0, 3],
    [1, 0, 3, 0, 3, 0, 1, 0, 3], [0, 1, 1, 0, 1, 0, 3, 0, 3], [3, 0, 3, 0, 1, 0, 3, 0, 3],
    [0, 1, 0, 3, 0, 1, 0, 1, 1, 0], [1, 1, 0, 3, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 3, 0, 3, 0], [0, 1, 1, 0, 1, 0, 3, 0, 3, 0],
    [0, 1, 0, 1, 1, 0, 3, 0, 3, 0], [1, 1, 0, 1, 1, 0, 3, 0, 3, 0],
    [0, 3, 0, 1, 1, 0, 3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 3, 0, 3, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [3, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [3, 0, 3, 0, 1, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 3, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 3, 0, 1], [1, 1, 0, 3, 0, 1, 0, 3, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 3, 0, 1], [3, 0, 1, 0, 1, 1, 0, 3, 0, 1],
    [3, 0, 1, 1, 0, 3, 0, 3, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1, 0, 3],
    [0, 1, 1, 0, 1, 1, 0, 1, 0, 3], [3, 0, 3, 0, 1, 1, 0, 1, 0, 3],
    [1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0],
    [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0], [3, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0],
    [1, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0], [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1], [1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1],
    [0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0], [0, 3, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0],
    [3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1]]

private theorem m11Letter_mem (g : ℕ) : m11Letter g ∈ NativeSporadic.M11 := by
  have ha : m11gA ∈ NativeSporadic.M11 := m11a.2
  have hb : m11gB ∈ NativeSporadic.M11 := m11b.2
  unfold m11Letter
  split
  · exact ha
  · exact hb
  · exact Subgroup.inv_mem _ ha
  · exact Subgroup.inv_mem _ hb

theorem m11Eval_mem (w : List ℕ) : m11Eval w ∈ NativeSporadic.M11 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons g w ih => exact Subgroup.mul_mem _ (m11Letter_mem g) ih

private theorem m11InvWords_length : m11InvWords.length = 165 := by decide +kernel

private theorem m11InvWords_nodup :
    (m11InvWords.map fun w => m11Eval w * m11SdX ^ 4 * (m11Eval w)⁻¹).Nodup := by
  decide +kernel

private theorem m11Sd_involutions : ∀ p : Fin 8 × Fin 2, m11SdMap p ^ 2 = 1 → m11SdMap p ≠ 1 →
    ∃ w ∈ m11InvWords, m11Eval w * m11SdX ^ 4 * (m11Eval w)⁻¹ = m11SdMap p := by
  decide +kernel

end Words

section Class

@[expose] def m11SdZ : ↥NativeSporadic.M11 := ⟨m11SdX ^ 4, Subgroup.pow_mem _ m11SdX_mem 4⟩

@[expose] def m11Conj (w : List ℕ) : ↥NativeSporadic.M11 := ⟨m11Eval w, m11Eval_mem w⟩

@[simp] theorem coe_m11Conj (w : List ℕ) : (m11Conj w : Perm (Fin 11)) = m11Eval w := rfl

private theorem le_ncard_conjugatesOf_m11SdZ : 165 ≤ (conjugatesOf m11SdZ).ncard := by
  set l := m11InvWords.map fun w => m11Conj w * m11SdZ * (m11Conj w)⁻¹ with hl
  have hnd : l.Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    rw [hl, List.map_map]
    exact m11InvWords_nodup
  have hlen : l.length = 165 := by rw [hl, List.length_map, m11InvWords_length]
  have hsub : (l.toFinset : Set ↥NativeSporadic.M11) ⊆ conjugatesOf m11SdZ := by
    intro c hc
    rw [Finset.mem_coe, List.mem_toFinset, hl, List.mem_map] at hc
    obtain ⟨w, -, rfl⟩ := hc
    exact isConj_iff.mpr ⟨m11Conj w, rfl⟩
  calc 165 = l.toFinset.card := by rw [List.toFinset_card_of_nodup hnd, hlen]
    _ = (l.toFinset : Set ↥NativeSporadic.M11).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (conjugatesOf m11SdZ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

end Class

section Sylow

private theorem exists_conj_mem_m11SdS {z : ↥NativeSporadic.M11} (hz : orderOf z = 2) :
    ∃ g s : ↥NativeSporadic.M11, s ∈ m11SdS ∧ g * s * g⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 m11SdS := IsPGroup.of_card (n := 4) (by rw [card_m11SdS]; norm_num)
  have hidx : ¬ 2 ∣ m11SdS.index := by
    have h := Subgroup.card_mul_index m11SdS
    rw [card_m11SdS, card_m11_kernel] at h
    have : m11SdS.index = 495 := by omega
    rw [this]
    norm_num
  have hA : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; norm_num)
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 (hS.toSylow hidx) P
  have hzP : z ∈ ((g • hS.toSylow hidx : Sylow 2 ↥NativeSporadic.M11) : Subgroup _) := by
    rw [hg]
    exact hP (Subgroup.mem_zpowers z)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzP
  obtain ⟨s, hs, hsz⟩ := hzP
  exact ⟨g, s, hs, by simpa [MulAut.smul_def, MulAut.conj_apply] using hsz⟩

end Sylow

theorem isConj_m11SdZ_of_orderOf_eq_two {z : ↥NativeSporadic.M11} (hz : orderOf z = 2) :
    IsConj m11SdZ z := by
  obtain ⟨g, s, hs, rfl⟩ := exists_conj_mem_m11SdS hz
  have hs2 : orderOf s = 2 := by
    rw [← hz]
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    simpa [MulAut.conj_apply] using this.symm
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact absurd (orderOf_one.symm.trans hs2) (by norm_num)
  have hssq : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem hs
  have hp2 : m11SdMap p ^ 2 = 1 := by
    rw [hp]
    simpa using congrArg Subtype.val hssq
  have hp1 : m11SdMap p ≠ 1 := by
    rw [hp]
    exact fun h => hs1 (Subtype.ext h)
  obtain ⟨w, -, hw⟩ := m11Sd_involutions p hp2 hp1
  have hws : m11Conj w * m11SdZ * (m11Conj w)⁻¹ = s := Subtype.ext (hw.trans hp)
  refine isConj_iff.mpr ⟨g * m11Conj w, ?_⟩
  rw [← hws]
  group

theorem card_centralizer_le_of_orderOf_eq_two {z : ↥NativeSporadic.M11} (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11)) ≤ 48 := by
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11))
  rw [Subgroup.index_centralizer_eq_ncard, card_m11_kernel] at h1
  have hc : conjugatesOf m11SdZ = conjugatesOf z :=
    isConj_iff_conjugatesOf_eq.mp (isConj_m11SdZ_of_orderOf_eq_two hz)
  have h2 := le_ncard_conjugatesOf_m11SdZ
  rw [hc] at h2
  by_contra hcon
  have h3 := Nat.mul_le_mul (not_le.mp hcon) h2
  omega

end CFSG.ClassicalInvolution.Q3
