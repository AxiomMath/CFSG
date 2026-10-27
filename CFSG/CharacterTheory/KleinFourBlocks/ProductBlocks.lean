module

public import CFSG.CharacterTheory.KleinFourBlocks.DefectZero
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct

public section

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.DirectProduct CFSG.PSL2Table

namespace CFSG.KleinFourBlocks

theorem blockOf_prod_of_signed (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ : ∀ ε ∈ BlocksIrr Z, ε 1 = 1 ∧ ∀ a, ε a = 1 ∨ ε a = -1) {L : Type} [Group L]
    [Fintype L] {ε : Z → ℂ} (hε : ε ∈ BlocksIrr Z) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksBlockOf m (Z × L) (outerProductCharacter ε θ) =
      {χ | ∃ ε' ∈ BlocksIrr Z, ∃ θ' ∈ BlocksBlockOf m L θ, χ = outerProductCharacter ε' θ'} := by
  obtain ⟨hbij, -⟩ := direct_product_irreducible_character_families Z L
  have hmem : ∀ ε' ∈ BlocksIrr Z, ∀ θ' ∈ BlocksIrr L,
      outerProductCharacter ε' θ' ∈ BlocksIrr (Z × L) := fun ε' hε' θ' hθ' =>
    hbij.mapsTo (show (ε', θ') ∈ BlocksIrr Z ×ˢ BlocksIrr L from ⟨hε', hθ'⟩)
  have hχ := hmem ε hε θ hθ
  obtain ⟨hε1, hεv⟩ := hZ ε hε
  ext χ
  constructor
  · intro hχ'
    obtain ⟨⟨ε', θ'⟩, ⟨hε', hθ'⟩, hχeq⟩ := hbij.surjOn hχ'.1
    change outerProductCharacter ε' θ' = χ at hχeq
    subst hχeq
    refine ⟨ε', hε', θ', ?_, rfl⟩
    obtain ⟨hε'1, -⟩ := hZ ε' hε'
    apply mem_blockOf_of_centralChar_congr m hm L hθ hθ'
    intro zL hzL
    have := sameBlock_centralChar_congr m hm (Z × L) hχ hχ' (isCentralR_lift m hm hzL)
    rwa [centralChar_outerProduct_lift hε'1, centralChar_outerProduct_lift hε1] at this
  · rintro ⟨ε', hε', θ', hθ', rfl⟩
    obtain ⟨hε'1, hε'v⟩ := hZ ε' hε'
    apply mem_blockOf_of_centralChar_congr m hm (Z × L) hχ (hmem ε' hε' θ' hθ'.1)
    intro z hz
    rw [centralChar_outerProduct hε'1, centralChar_outerProduct hε1, ← Finset.sum_sub_distrib]
    apply localMaxIdeal_sum m hm
    intro a _
    have hR := centralChar_localRing m hm hθ (isCentralR_slice m hz a)
    have hM := sameBlock_centralChar_congr m hm L hθ hθ' (isCentralR_slice m hz a)
    have hsplit : ε' a * BlocksCentralChar θ' (fun x => z (a, x)) -
        ε a * BlocksCentralChar θ (fun x => z (a, x)) =
        (BlocksCentralChar θ' (fun x => z (a, x)) - BlocksCentralChar θ (fun x => z (a, x))) *
          ε' a + (ε' a - ε a) * BlocksCentralChar θ (fun x => z (a, x)) := by
      ring
    rw [hsplit]
    refine localMaxIdeal_add m hm (localMaxIdeal_mul_localRing m hm hM ?_)
      (localMaxIdeal_mul_localRing m hm ?_ hR)
    · rcases hε'v a with h | h <;> rw [h]
      · exact localRing_one m hm
      · exact localRing_neg m (localRing_one m hm)
    · rcases hε'v a with h | h <;> rcases hεv a with h' | h' <;> rw [h, h']
      · simpa using localMaxIdeal_zero m hm
      · exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (localRing_one m hm) (by ring)
      · exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (localRing_neg m (localRing_one m hm))
          (by ring)
      · simpa using localMaxIdeal_zero m hm

theorem charP_two_of_two_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) : CharP (BlocksAlgInt ⧸ m) 2 := by
  have : Nontrivial (BlocksAlgInt ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  rw [← map_ofNat (Ideal.Quotient.mk m) 2]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h2

theorem le_map_sylow_of_normal {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} [hPn : P.Normal]
    (hP : IsPGroup p P) {g : G} (hPg : P ≤ Subgroup.centralizer ({g} : Set G))
    (S : Sylow p (Subgroup.centralizer ({g} : Set G))) :
    P ≤ (S : Subgroup (Subgroup.centralizer ({g} : Set G))).map
      (Subgroup.centralizer ({g} : Set G)).subtype := by
  have : (P.subgroupOf (Subgroup.centralizer ({g} : Set G))).Normal := hPn.subgroupOf _
  have hQ : IsPGroup p (P.subgroupOf (Subgroup.centralizer ({g} : Set G))) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPg).symm
  calc P = (P.subgroupOf (Subgroup.centralizer ({g} : Set G))).map
        (Subgroup.centralizer ({g} : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPg).symm
    _ ≤ _ := Subgroup.map_mono (hQ.le_sylow_of_normal S)

theorem le_centralizer_of_isConj {G : Type*} [Group G] {P : Subgroup G} [hPn : P.Normal] {x g : G}
    (hx : x ∈ Subgroup.centralizer (P : Set G)) (hg : IsConj g x) :
    P ≤ Subgroup.centralizer ({g} : Set G) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hg
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hp' : c * p * c⁻¹ ∈ P := hPn.conj_mem p hp c
  have h1 := Subgroup.mem_centralizer_iff.mp hx _ hp'
  rw [← hc] at h1
  have h2 : c * (p * h) * c⁻¹ = c * (h * p) * c⁻¹ :=
    calc c * (p * h) * c⁻¹ = (c * p * c⁻¹) * (c * h * c⁻¹) := by group
      _ = (c * h * c⁻¹) * (c * p * c⁻¹) := h1
      _ = c * (h * p) * c⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem classCoefficients_mk_one_prod {Z L : Type} [Group Z] [DecidableEq Z] [Group L] (z : L) :
    classCoefficients (ConjClasses.mk ((1 : Z), z)) =
      fun p : Z × L => if p.1 = 1 then classCoefficients (ConjClasses.mk z) p.2 else 0 := by
  funext ⟨a, x⟩
  by_cases ha : a = 1
  · subst ha
    have h : ConjClasses.mk ((1 : Z), x) = ConjClasses.mk ((1 : Z), z) ↔
        ConjClasses.mk x = ConjClasses.mk z := by
      simp only [ConjClasses.mk_eq_mk_iff_isConj]
      exact ⟨fun h => (MonoidHom.snd Z L).map_isConj h, fun h => (MonoidHom.inr Z L).map_isConj h⟩
    by_cases hc : ConjClasses.mk x = ConjClasses.mk z
    · have hc' := h.mpr hc
      simp [classCoefficients, hc, hc']
    · have hc' : ¬ ConjClasses.mk ((1 : Z), x) = ConjClasses.mk ((1 : Z), z) :=
        fun h' => hc (h.mp h')
      simp [classCoefficients, hc, hc']
  · have h : ConjClasses.mk (a, x) ≠ ConjClasses.mk ((1 : Z), z) := by
      intro h
      have := (MonoidHom.fst Z L).map_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp h)
      exact ha (isConj_one_left.mp this)
    simp [classCoefficients, h, ha]

theorem blockDefect_outer_of_blockDefect_bot (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]
    [h2 : CharP (BlocksAlgInt ⧸ m) 2] {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ2 : IsPGroup 2 Z) {ε : Z → ℂ} (hε : ε ∈ BlocksIrr Z) (hε1 : ε 1 = 1) {L : Type}
    [Group L] [Fintype L] {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hbot : blockDefect 2 m θ ⊥) :
    blockDefect 2 m (outerProductCharacter ε θ) ((⊤ : Subgroup Z).prod (⊥ : Subgroup L)) := by
  set P : Subgroup (Z × L) := (⊤ : Subgroup Z).prod (⊥ : Subgroup L)
  have : P.Normal := inferInstance
  have hP2 : IsPGroup 2 P := by
    rintro ⟨⟨a, x⟩, hax⟩
    have hx : x = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hax).2
    obtain ⟨n, hn⟩ := hZ2 a
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simpa using hn
    · simp [hx]
  have hχ0 : outerProductCharacter ε θ ∈ BlocksIrr (Z × L) :=
    outerProductCharacter_mem_blocksIrr hε hθ
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨K_L, ⟨z, hz, S, hS⟩, hω⟩, -⟩ := hbot
    subst hz
    refine ⟨ConjClasses.mk ((1 : Z), z), ⟨(1, z), rfl, ?_⟩, ?_⟩
    · have hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
        have hbot' : (S : Subgroup (Subgroup.centralizer ({z} : Set L))) = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hS
        have hS1 : Nat.card (S : Subgroup (Subgroup.centralizer ({z} : Set L))) = 1 := by
          rw [hbot']
          exact Subgroup.card_bot
        rw [Sylow.card_eq_multiplicity] at hS1
        intro hdvd
        have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hdvd
        rw [Nat.pow_eq_one] at hS1
        omega
      have hPC : P ≤ Subgroup.centralizer ({((1 : Z), z)} : Set (Z × L)) := by
        intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hp2 : p.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hp).2
        ext <;> simp [hp2]
      obtain ⟨S'⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({((1 : Z), z)} : Set (Z × L)))) :=
        inferInstance
      refine ⟨S', le_antisymm ?_ (le_map_sylow_of_normal hP2 hPC S')⟩
      intro y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr ?_⟩
      obtain ⟨n, hn⟩ := S'.isPGroup' ⟨s, hs⟩
      have hn1 : s ^ 2 ^ n = 1 := by
        have := congrArg (fun t : (S' : Subgroup (Subgroup.centralizer
          ({((1 : Z), z)} : Set (Z × L)))) => (t : Subgroup.centralizer
            ({((1 : Z), z)} : Set (Z × L)))) hn
        simpa using this
      have hn2 : (s : Z × L).2 ^ 2 ^ n = 1 := by
        have := congrArg (fun t : Subgroup.centralizer ({((1 : Z), z)} : Set (Z × L)) =>
          (t : Z × L).2) hn1
        simpa using this
      have hcomm : (s : Z × L).2 ∈ Subgroup.centralizer ({z} : Set L) := by
        have h' := Subgroup.mem_centralizer_iff.mp s.2 (1, z) rfl
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact congrArg Prod.snd h'
      set x : Subgroup.centralizer ({z} : Set L) := ⟨(s : Z × L).2, hcomm⟩ with hx
      have hxpow : x ^ 2 ^ n = 1 := Subtype.ext (by simpa [hx] using hn2)
      have hcop : Nat.Coprime (2 ^ n) (Nat.card (Subgroup.centralizer ({z} : Set L))) :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      have hord : orderOf x = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hxpow) (orderOf_dvd_natCard x)
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
    · rw [classCoefficients_mk_one_prod, centralChar_outerProduct_lift hε1]
      exact hω
  · intro K hK other hother
    have hKx : ∃ x, ConjClasses.mk x = K ∧ x ∈ Subgroup.centralizer (P : Set (Z × L)) := by
      by_contra hno
      exact hK ((CFSG.BlockBasics.normal_p_subgroup_class_vanishing 2 Nat.prime_two m hm
        (Z × L) P hP2 _ ⟨_, hχ0, rfl⟩).1 K (fun x hx hxP => hno ⟨x, hx, hxP⟩) _
          (mem_blockOf_self m hχ0))
    obtain ⟨x, hxK, hxP⟩ := hKx
    obtain ⟨g, hg, S, rfl⟩ := hother
    have hconj : IsConj g x := ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans hxK.symm)
    refine ⟨1, fun y hy => ?_⟩
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : (MulAut.conj (1 : Z × L)).toMonoidHom y' = y' := by simp
    rw [h1]
    exact le_map_sylow_of_normal hP2 (le_centralizer_of_isConj hxP hconj) S hy'

theorem blockDefect_prod_of_defect_zero (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ2 : IsPGroup 2 Z) (hZ : ∀ ε ∈ BlocksIrr Z, ε 1 = 1 ∧ ∀ a, ε a = 1 ∨ ε a = -1)
    {L : Type} [Group L] [Fintype L] {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hdeg : ∃ d : ℕ, θ 1 = d ∧ 2 ^ (Nat.card L).factorization 2 ∣ d) {ε : Z → ℂ}
    (hε : ε ∈ BlocksIrr Z) :
    ∀ χ ∈ BlocksBlockOf m (Z × L) (outerProductCharacter ε θ),
      blockDefect 2 m χ ((⊤ : Subgroup Z).prod (⊥ : Subgroup L)) := by
  have : CharP (BlocksAlgInt ⧸ m) 2 := charP_two_of_two_mem m hm h2
  intro χ hχ
  rw [blockOf_prod_of_signed m hm h2 hZ hε hθ, blockOf_eq_singleton_of_defect_zero m hθ hdeg] at hχ
  obtain ⟨ε', hε', θ', hθ', rfl⟩ := hχ
  have hθ'θ : θ' = θ := hθ'
  subst hθ'θ
  exact blockDefect_outer_of_blockDefect_bot m hZ2 hε' (hZ ε' hε').1 hθ
    (blockDefect_bot_of_defect_zero m hθ hdeg)

end CFSG.KleinFourBlocks
