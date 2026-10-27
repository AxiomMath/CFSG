module

public import CFSG.LargeExtraspecial.S111ABasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

theorem exists_of_mem_V (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g} (hL : LinCase S g ht)
    {x : G} (hx : x ∈ V S g t) (hx1 : x ≠ 1) (hxz : x ≠ S.z) :
    ∃ m : S.M, S.ρ m ∈ Rbar S g t ∧ x = (m : G) * g * S.z * ((m : G) * g)⁻¹ := by
  have hxQ : x ∈ S.QG := hx.1
  have hv0 : S.cl x ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hxQ).mp h with h' | h'
    · exact hx1 h'
    · exact hxz h'
  have horb := hL.mem_orbit ⟨S.cl x, hx.2⟩ (fun h => hv0 (congrArg Subtype.val h))
  obtain ⟨m, hm, hmx⟩ := exists_of_mem_orbit horb H.conj_mem
  have hmQ := conj_mem_QG' S m.2 H.conj_mem
  rcases (S.cl_eq_cl_iff hmQ hxQ).mp hmx.symm with e | e
  · exact ⟨m, hm, e⟩
  · obtain ⟨q, hq, hqm⟩ := S.exists_mul_conj_eq_mul_z hmQ (conj_ne_z' S m.2 H.conj_ne)
    refine ⟨⟨q, S.QG_le_M hq⟩ * m, ?_, ?_⟩
    · rw [map_mul, (S.ρ_eq_one_iff _).mpr hq, one_mul]
      exact hm
    · rw [e, ← hqm]
      simp [mul_assoc]

theorem incClosed_V (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g} (hL : LinCase S g ht) :
    IncClosed S (V S g t) where
  le_QG := V_le_QG
  z_mem := z_mem_V
  conj := fun x hx hx1 => by
    by_cases hxz : x = S.z
    · exact ⟨1, by rw [hxz]; group⟩
    obtain ⟨m, -, rfl⟩ := exists_of_mem_V H hL hx hx1 hxz
    exact ⟨(m : G) * g, rfl⟩
  le_Qa := fun k hk => by
    by_cases hkz : k * S.z * k⁻¹ = S.z
    · rw [S.Qa_eq_QG_of_conj_eq hkz]
      exact V_le_QG
    obtain ⟨m, hm, e⟩ := exists_of_mem_V H hL hk (conj_z_ne_one S k) hkz
    rw [S.Qa_eq_of_conj_eq e]
    exact V_le_Qa_mul H hL.le_Qa hm

theorem conj_mem_V (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : g * S.z * g⁻¹ ∈ V S g t :=
  ⟨H.conj_mem, cl_a_mem_Vt ht⟩

theorem card_V_ge (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (hR : Rbar S g t ≠ S.Lbar g) :
    8 ≤ Nat.card (V S g t) := by
  have h2 := two_le_finrank_Vt H ht hR
  change 8 ≤ Nat.card (S.clPre (Vt S g t))
  rw [S.card_clPre, S.card_submodule]
  calc 8 = 2 * 2 ^ 2 := by norm_num
    _ ≤ 2 * 2 ^ finrank (ZMod 2) (Vt S g t) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h2)

theorem Cfg111.exists (hy : Hyp S g) (hirr : ¬ S.IsReducible)
    (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) (hn : ¬ Timmesfeld11_1Stmt S) :
    ∃ A : Subgroup G, Cfg111 S g A := by
  obtain ⟨t, ht, ht1, hR⟩ := hT
  have hL := (hy.lin ht ht1).resolve_left hR
  obtain ⟨A, ⟨hA, haA⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup G | IncClosed S B ∧ g * S.z * g⁻¹ ∈ B} (fun B => Nat.card B)
    (Set.toFinite _) ⟨_, incClosed_V hy.hyp4 hL, conj_mem_V hy.hyp4 ht⟩
  exact ⟨A, hy, hirr, ⟨t, ht, ht1, hR⟩, hn, hA, haA, fun B hB hgB => hmax B ⟨hB, hgB⟩⟩

theorem Cfg111.eight_le_card (C : Cfg111 S g A) : 8 ≤ Nat.card A := by
  obtain ⟨t, ht, ht1, hR⟩ := C.exT
  have hL := (C.hy.lin ht ht1).resolve_left hR
  exact (card_V_ge C.hy.hyp4 ht hR).trans
    (C.max _ (incClosed_V C.hy.hyp4 hL) (conj_mem_V C.hy.hyp4 ht))

end CFSG.LargeExtraspecial.S11
