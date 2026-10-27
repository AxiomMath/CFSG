module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RB

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

variable {G : Type} [Group G]

section Rank

theorem card_le_sixteen_of_pRank [Finite G] (hrank : CFSG.pRank 2 G = 4) {B : Subgroup G}
    (hB : IsElementaryAbelian 2 ↥B) : Nat.card ↥B ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥B := by
    have := hB
    exact IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hk4 : k ≤ 4 := hrank ▸ CFSG.LieType.SteinbergBR.le_pRank_of_card Nat.one_lt_two B hB hk
  calc Nat.card ↥B = 2 ^ k := hk
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    _ = 16 := by norm_num

theorem exists_ea_card_sixteen [Finite G] {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hrank : CFSG.pRank 2 ↥(centralizer ({x} : Set G)) = 4) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨A, hA, hAcard⟩ : ∃ A : Subgroup ↥C, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ 4 := by
    set s : Set ℕ := {r : ℕ | ∃ A : Subgroup ↥C, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r}
      with hs
    have hbdd : BddAbove s := by
      refine ⟨Nat.card ↥C, ?_⟩
      rintro r ⟨A, -, hA⟩
      have h1 : r < 2 ^ r := Nat.lt_pow_self (by norm_num)
      have h2 : Nat.card ↥A ≤ Nat.card ↥C := Subgroup.card_le_card_group A
      omega
    have hne : s.Nonempty := by
      rcases s.eq_empty_or_nonempty with h | h
      · exfalso
        have h0 : sSup s = 0 := by rw [h, csSup_empty]; rfl
        have h4 : sSup s = 4 := hrank
        omega
      · exact h
    have hmem := Nat.sSup_mem hne hbdd
    have h4 : sSup s = 4 := hrank
    rw [h4] at hmem
    exact hmem
  have hAel : IsElementaryAbelian 2 ↥A := hA
  set E₀ : Subgroup G := A.map C.subtype with hE₀
  have hE₀el : IsElementaryAbelian 2 ↥E₀ := by
    have := hAel
    exact IsElementaryAbelian.map_subtype
  have hE₀card : Nat.card ↥E₀ = 16 := by
    rw [hE₀, Subgroup.card_map_of_injective C.subtype_injective, hAcard]
    norm_num
  have hE₀C : E₀ ≤ C := Subgroup.map_subtype_le A
  have hE₀p : IsPGroup 2 ↥E₀ := by
    have := hE₀el
    exact IsElementaryAbelian.isPGroup 2 ↥E₀
  obtain ⟨T', hE₀T', hT'C, hT'p, hT'idx⟩ := P34.exists_sylow_ge (N := C) hE₀C hE₀p
  have hT' : IsSylowOf 2 T' C := isSylowOf_iff.2 ⟨hT'C, hT'p, hT'idx⟩
  obtain ⟨k, hkC, hk⟩ := hT.exists_mem_conj hT'
  refine ⟨E₀.map (MulAut.conj k⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have := (hk e).1 (hE₀T' he)
    simpa [MulAut.conj_apply, mul_assoc] using this
  · have := hE₀el
    exact IsElementaryAbelian.map (MulAut.conj k⁻¹).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hE₀card]

theorem thompsonJ2_le_thompsonJ2 {T V : Subgroup G} (hJV : thompsonJ2 T ≤ V)
    (hE : ∃ E : Subgroup G, E ≤ T ∧ IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16)
    (hB : ∀ B : Subgroup G, IsElementaryAbelian 2 ↥B → Nat.card ↥B ≤ 16) :
    thompsonJ2 T ≤ thompsonJ2 V := by
  obtain ⟨E, hET, hEel, hEcard⟩ := hE
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  have hAV : A ≤ V := (le_thompsonJ2 hAT hAel hAmax).trans hJV
  refine le_thompsonJ2 hAV hAel fun B hBV hBel => ?_
  have h16 : 16 ≤ Nat.card ↥A := hEcard ▸ hAmax E hET hEel
  exact (hB B hBel).trans h16

end Rank

namespace Frame39

variable {x y : G} {K T V W S P₀ : Subgroup G} {f z a f₁ : G}
  (F : Frame39 x y K T V W f z S a P₀ f₁)

include F

section Fin

variable [Finite G]

theorem J_le_C₀ : thompsonJ2 T ≤ T ⊓ centralizer ({f} : Set G) := by
  rw [F.h37a]
  refine sup_le (fun p hp => ⟨hp.1, mem_centralizer_singleton_iff.2 (F.cfg.mem.2.2.1 p hp).symm⟩)
    (sup_le (zpowers_le.2 ⟨F.cfg.mem.1, mem_centralizer_singleton_iff.2 rfl⟩)
      (zpowers_le.2 ⟨F.x_mem, mem_centralizer_singleton_iff.2 F.cfg.hxf⟩))

theorem J_le_v₁ : thompsonJ2 T ≤ v₁ T f a := F.J_le_C₀.trans le_sup_left

theorem card_Klein : Nat.card ↥(zpowers f ⊔ zpowers x) = 4 := by
  have hcomm : Commute f x := F.cfg.hxf.symm
  have hnorm : zpowers x ≤ normalizer ((zpowers f : Subgroup G) : Set G) := by
    refine le_trans (zpowers_le.2 ?_) (Subgroup.centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact (hcomm.zpow_left k).eq
  have hdisj : Disjoint (zpowers f) (zpowers x) := by
    refine Subgroup.disjoint_def.2 ?_
    intro g hgf hgx
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers F.hf2 hgf with h1 | h1
    · exact h1
    · rcases Thm1P310.eq_one_or_eq_of_mem_zpowers F.hx2 hgx with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) F.cfg.mem.2.2.2.1
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, F.cfg.hf2, F.cfg.hx2]

theorem card_J : Nat.card ↥(thompsonJ2 T) = 4 * Nat.card ↥(T ⊓ K) := by
  have hnorm : zpowers f ⊔ zpowers x ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine le_trans (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_))
      (Subgroup.centralizer_le_normalizer _)
    · rw [mem_centralizer_iff]
      intro p hp
      exact (F.cfg.mem.2.2.1 p hp).symm
    · rw [mem_centralizer_iff]
      intro p hp
      exact F.x_comm p hp.1
  have hdisj : Disjoint (T ⊓ K) (zpowers f ⊔ zpowers x) := disjoint_iff.2 F.h37b
  rw [F.h37a, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    F.card_Klein, mul_comm]

theorem sixty_four_le_card_T (h8 : 8 ≤ Nat.card ↥(T ⊓ K)) : 64 ≤ Nat.card ↥T := by
  have h1 := F.card_C₀
  have h2 : Nat.card ↥(thompsonJ2 T) ≤ Nat.card ↥(T ⊓ centralizer ({f} : Set G)) :=
    Subgroup.card_le_of_le F.J_le_C₀
  have h3 := F.card_J
  omega

end Fin

end Frame39

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
