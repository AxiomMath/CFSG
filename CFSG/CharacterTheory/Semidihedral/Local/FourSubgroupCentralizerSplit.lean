module

public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralOddComplement

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G]

theorem kleinFour_le_centralizer (V : Subgroup G) [IsKleinFour V] :
    V ≤ Subgroup.centralizer (V : Set G) := fun _ hv =>
  Subgroup.mem_centralizer_iff.mpr fun _ hh => kleinFour_mul_comm V hh hv

theorem kleinFour_sylow_of_centralizer [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (V : Subgroup G) [IsKleinFour V] :
    ∃ P : Sylow 2 (Subgroup.centralizer (V : Set G)),
      (P : Subgroup (Subgroup.centralizer (V : Set G))) =
        V.subgroupOf (Subgroup.centralizer (V : Set G)) := by
  set C := Subgroup.centralizer (V : Set G) with hCdef
  have hVC : V ≤ C := kleinFour_le_centralizer V
  have hV2 : IsPGroup 2 (V.subgroupOf C) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, IsKleinFour.card_four]
    norm_num)
  obtain ⟨P, hVP⟩ := hV2.exists_le_sylow
  have hP2 : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map C.subtype
  obtain ⟨S₀, hPS₀⟩ := hP2.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S₀
  have hVP' : V ≤ (P : Subgroup C).map C.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVC]
    exact Subgroup.map_mono hVP
  have hVS₀ : V ≤ ((g • S : Sylow 2 G) : Subgroup G) := hVP'.trans hPS₀
  have : IsKleinFour (V.subgroupOf ((g • S : Sylow 2 G) : Subgroup G)) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVS₀).symm
  obtain ⟨x, hxV, hxz⟩ := kleinFour_exists_not_mem hn (f.trans (S.equivSMul g)) (V.subgroupOf _)
  obtain ⟨-, hcent, -⟩ := kleinFour_eq_closure hn (f.trans (S.equivSMul g)) _ x hxV hxz
  have hP'V : (P : Subgroup C).map C.subtype ≤ V := by
    intro p hp
    have hpS₀ := hPS₀ hp
    have hpC : p ∈ C := by
      obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hp
      exact c.2
    have hcen : (⟨p, hpS₀⟩ : ((g • S : Sylow 2 G) : Subgroup G)) ∈
        Subgroup.centralizer
          ((V.subgroupOf ((g • S : Sylow 2 G) : Subgroup G) : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpC) h (Subgroup.mem_subgroupOf.mp hh))
    rw [hcent] at hcen
    exact Subgroup.mem_subgroupOf.mp hcen
  refine ⟨P, le_antisymm ?_ hVP⟩
  intro c hc
  rw [Subgroup.mem_subgroupOf]
  exact hP'V (Subgroup.mem_map_of_mem _ hc)

theorem hall_eq_of_odd_mem {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (hNodd : Odd (Nat.card N)) {k : ℕ} (hk : N.index = 2 ^ k)
    (hmem : ∀ x : H, x ∈ N ↔ Odd (orderOf x)) (N' : Subgroup H) (hN'odd : Odd (Nat.card N'))
    {a : ℕ} (ha : N'.index = 2 ^ a) : N' = N := by
  have hle : N' ≤ N := fun x hx => (hmem x).mpr
    (Odd.of_dvd_nat hN'odd (by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _))
  have hrel := Subgroup.relIndex_mul_index hle
  rw [hk, ha] at hrel
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hrel)
  have hodd : Odd (N'.relIndex N) := Odd.of_dvd_nat hNodd (Subgroup.index_dvd_card _)
  rw [hc] at hodd
  have hc0 : c = 0 := by
    by_contra hc0
    exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' hc0).mpr even_two)
  rw [hc0, pow_zero] at hc
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hc)

theorem semidihedral_four_subgroup_centralizer_split [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (V : Subgroup G) (hV : IsKleinFour V) :
    let C := Subgroup.centralizer (V : Set G)
    V ≤ C ∧ (∃ P : Sylow 2 C, (P : Subgroup C) = V.subgroupOf C) ∧
    V.subgroupOf C ≤ Subgroup.center C ∧
    ∃ N : Subgroup C, N.Normal ∧ (Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∧
      (∀ N' : Subgroup C, Odd (Nat.card N') → (∃ k : ℕ, N'.index = 2 ^ k) → N' = N) ∧
      N.Characteristic ∧ (∀ x : C, x ∈ N ↔ Odd (orderOf x)) ∧
      KleinFourOddKernel.IsInternalDirectProduct (V.subgroupOf C) N ∧
      ∃ e : V.subgroupOf C × N ≃* C, ∀ a b, e (a, b) = (a : C) * (b : C) := by
  intro C
  have hVC : V ≤ C := kleinFour_le_centralizer V
  obtain ⟨P, hP⟩ := kleinFour_sylow_of_centralizer n hn S f V
  have hcenter : V.subgroupOf C ≤ Subgroup.center C := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 _ (Subgroup.mem_subgroupOf.mp hv)).symm
  have : IsKleinFour (V.subgroupOf C) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVC).symm
  have hS : Nonempty (DihedralGroup (2 ^ (2 - 1)) ≃* (P : Subgroup C)) := by
    show Nonempty (DihedralGroup 2 ≃* (P : Subgroup C))
    rw [hP]
    exact IsKleinFour.nonempty_mulEquiv
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsKleinFour.card_four]
    norm_num)
  obtain ⟨⟨t, htV⟩, ht1⟩ := exists_ne (1 : V)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htc : (⟨t, hVC htV⟩ : C) ∈ Subgroup.center C :=
    hcenter (Subgroup.mem_subgroupOf.mpr htV)
  have ht2 : orderOf (⟨t, hVC htV⟩ : C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact kleinFour_orderOf V htV ht1'
  obtain ⟨N, hNnormal, ⟨hNodd, k, hk⟩, -, hchar, hmem, hmul, hinf, -⟩ :=
    Principal.dihedral_central_involution_normal_odd_complement P le_rfl hS ⟨_, htc, ht2⟩
  have hcompl : (V.subgroupOf C).IsComplement' N := by
    have h := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hmul
    rw [hP] at h
    exact h.symm
  refine ⟨hVC, ⟨P, hP⟩, hcenter, N, hNnormal, ⟨hNodd, k, hk⟩,
    fun N' hN'odd ⟨a, ha⟩ => hall_eq_of_odd_mem N hNodd hk hmem N' hN'odd ha, hchar, hmem,
    ⟨hcompl, fun a b => (Subgroup.mem_center_iff.mp (hcenter a.2) b).symm⟩,
    OddFieldLift.internalDirectEquiv _ _ hcenter hcompl, fun a b => rfl⟩

end CFSG.Semidihedral.Local
