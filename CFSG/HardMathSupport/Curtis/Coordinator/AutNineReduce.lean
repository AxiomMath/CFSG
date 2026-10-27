module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
import CFSG.HardMathSupport.Curtis.Coordinator.AutBounds
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVMain
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
import CFSG.HardMathSupport.Curtis.Proving.NineDvdCentralizer

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem relIndex_le_nine_of_inner {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hU : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U)
    (hUL : U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (h27 : ¬ 3 ^ 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 9 :=
  relIndex_centralizer_le_of_le_sup (k := 2) Nat.prime_three hU hUL hU3 h27

omit [Finite G] in
theorem le_sup_of_not_three_dvd {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hU : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U)
    (hOut : ¬ 3 ∣ Nat.card (Outer ↥(barM M L))) :
    U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  le_sup_centralizer_of_isPGroup_of_not_dvd Nat.prime_three hU hU3 hOut

theorem not_dvd_card_quotient_center_of {X : Type*} [Group X] {n : ℕ}
    (hX : Nat.card X = n) (hn : ¬ 3 ^ 3 ∣ n) : ¬ 3 ^ 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
  intro h
  apply hn
  rw [← hX, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
  exact h.mul_right _

theorem not_dvd_card_alternatingGroup {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ 3 ^ 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide

theorem exists_mul_of_mem_sup_centralizer {Y : Type} [Group Y] {L : Subgroup Y} {u : Y}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), u = l * c := by
  have hCN : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    CFSG.AGLEmbedding.ToralCensus.le_normalizer_centralizer L
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hu
  obtain ⟨l, hl, c, hc, rfl⟩ := hu
  exact ⟨l, hl, c, hc, rfl⟩

theorem false_of_alt_of_not_nine_dvd {u : ↥M ⧸ CFSG.pCore 2 ↥M} {m : ℕ} (hm : 6 ≤ m)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin m))
    (hu : u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hu3 : u ^ 3 = 1) (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L)
    (h9 : ¬ 9 ∣ Nat.card (blockPL M S L)) : False := by
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hu
  have hlc : Commute l c := (Subgroup.mem_centralizer_iff.mp hc) l hl
  have hZ : Subgroup.center ↥(barM M L) = ⊥ := by
    have h4 : 4 ≤ Nat.card (Fin m) := by rw [Nat.card_fin]; omega
    have hc0 := alternatingGroup.center_eq_bot h4
    rw [eq_bot_iff] at hc0 ⊢
    intro z hz
    have : e z ∈ Subgroup.center (alternatingGroup (Fin m)) :=
      Subgroup.mem_center_iff.mpr fun g => by
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) g']
    have h1 := hc0 this
    rw [Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hl3 : l ^ 3 = 1 := by
    have h1 : l ^ 3 * c ^ 3 = 1 := by rw [← hlc.mul_pow]; exact hu3
    have hcen : (⟨l ^ 3, Subgroup.pow_mem _ hl 3⟩ : ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hc3 : c ^ 3 ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        Subgroup.pow_mem _ hc 3
      have hl3c : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply Subtype.ext
      change (g : ↥M ⧸ CFSG.pCore 2 ↥M) * l ^ 3 = l ^ 3 * g
      rw [hl3c]
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hc3)) g g.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [one_mul] at huC
    exact huC hc
  set l' : ↥(barM M L) := ⟨l, hl⟩
  have hl'3 : orderOf l' = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hl3)
    · intro h
      exact hl1 (congrArg Subtype.val h)
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h9L : 9 ∣ Nat.card ↥(barM M L) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have h6 : Nat.factorial 6 ∣ Nat.factorial m := Nat.factorial_dvd_factorial hm
    obtain ⟨k, hk⟩ := h6
    rw [hk, show Nat.factorial 6 = 2 * 360 by rfl, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    exact Dvd.dvd.mul_right (by norm_num) k
  have hC9 := CFSG.HardMathSupport.Curtis.Proving.nine_dvd_card_centralizer_of_orderOf_eq_three
    h9L hl'3
  have hmap : (Subgroup.centralizer ({l'} : Set ↥(barM M L))).map (barM M L).subtype ≤
      blockPL M S L := by
    rintro _ ⟨x, hx, rfl⟩
    refine hfix x x.2 ?_
    have hxl : x * l' = l' * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxl' : (x : ↥M ⧸ CFSG.pCore 2 ↥M) * l = l * x := congrArg Subtype.val hxl
    have hxc : (x : ↥M ⧸ CFSG.pCore 2 ↥M) * c = c * x :=
      (Subgroup.mem_centralizer_iff.mp hc) x x.2
    change l * c * (x : ↥M ⧸ CFSG.pCore 2 ↥M) * (l * c)⁻¹ = x
    calc l * c * (x : ↥M ⧸ CFSG.pCore 2 ↥M) * (l * c)⁻¹
        = l * (c * x) * c⁻¹ * l⁻¹ := by group
      _ = l * (x * c) * c⁻¹ * l⁻¹ := by rw [hxc]
      _ = (l * x) * l⁻¹ := by group
      _ = (x * l) * l⁻¹ := by rw [hxl']
      _ = x := by group
  apply h9
  refine hC9.trans ?_
  rw [← Subgroup.card_map_of_injective (barM M L).subtype_injective]
  exact Subgroup.card_dvd_of_le hmap

theorem le_four_of_quotient_perm {J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {n : ℕ}
    (hJ : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ J → ⁅V, V⁆ = V →
      Nat.Coprime 3 (Nat.card V))
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) : n ≤ 4 := by
  by_contra h
  exact false_of_surjective_perm_of_three (by omega) hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' _)) (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem citedBlockThreeAutNine_of_census (hC : KFactFixCensusPerfThree)
    (hT : CitedBlockTransvectionPLType) : CitedBlockThreeAutNine := by
  intro G _ _ M S L hK hA hL h93 hX hS hperf u hu hu3 huC hfix U hU hU3
  have hperfPL : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W) := fun W hW hWW =>
    coprime_card_blockPL_of_perfect hL hperf W hW hWW
  have := barM_isPerfect hL
  have := barM_nontrivial_center_quotient hL
  have := barM_nontrivial hL
  have hodd := odd_card_center_barM_of_isWeakSBlock hL
  have hinner : ¬ 3 ∣ Nat.card (Outer ↥(barM M L)) →
      ¬ 3 ^ 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 9 :=
    fun hO h27 => relIndex_le_nine_of_inner hU hU3 (le_sup_of_not_three_dvd hU hU3 hO) h27
  have hasix : Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 9 := by
    rintro hZ3 ⟨e⟩
    refine relIndex_le_nine_of_inner hU hU3 (fun y hy => ?_) ?_
    · obtain ⟨k, hk⟩ := hU3 ⟨y, hy⟩
      exact (kFactBlockThreeASix_holds G M L hL.toIsTwoPrimeComponent hZ3 ⟨e⟩).1 y (hU hy)
        ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Nat.card_congr e.toEquiv]
      exact not_dvd_card_alternatingGroup (by norm_num)
  rcases h93 with h1 | h2 | h3 | h4 | ⟨-, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ |
      ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2', h4', -, φ, -⟩
  · exact absurd h1 hX
  ·
    obtain ⟨-, hsurv⟩ := hC _ (barM M L) (blockPL M S L) u
      (fixPerfThreeHyp_of_nineThreeTwo hA hL hS h2 hperf hu hu3 huC hfix)
    rcases hsurv with ⟨d, hd, ⟨e⟩⟩ | ⟨hZ3, he⟩ | he
    · have hc := statedClassicalModel_psl_two_seven hd e
      refine hinner (fun h3 => not_three_dvd_card_outer_of_psl_seven hc
        (h3.trans (card_outer_dvd_card_outer_centerQuotient _))) ?_
      rw [card_eq_of_psl_two_seven hc]
      norm_num
    · exact hasix hZ3 he
    · obtain ⟨e⟩ := he
      refine hinner (not_three_dvd_card_outer_of_center_alt e) ?_
      rw [Nat.card_congr e.toEquiv]
      exact not_dvd_card_alternatingGroup (by norm_num)
  ·
    obtain ⟨hOrth, hU4, -, -, hA8⟩ := hT G M S L hK hA hL hX hS h3
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      rcases hdm with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact false_of_quotient_sp_of_three (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperfPL e'
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact false_of_quotient_sp_of_three (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperfPL e'
      · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
        exact false_of_surjective_perm_of_three (n := 6) (by norm_num) hperfPL e6.toMonoidHom
          e6.surjective
    · have hn' : n = 5 ∨ n = 6 := by
        rcases hn with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · obtain ⟨e6⟩ := hA8 ⟨e⟩
          exact (false_of_surjective_perm_of_three (n := 6) (by norm_num) hperfPL e6.toMonoidHom
            e6.surjective).elim
      refine hinner (not_three_dvd_card_outer_of_alt e)
        (not_dvd_card_quotient_center_of (Nat.card_congr e.toEquiv) ?_)
      rcases hn' with rfl | rfl <;> exact not_dvd_card_alternatingGroup (by norm_num)
  ·
    obtain ⟨-, hZ3, he, -⟩ := h4
    exact hasix hZ3 he
  ·
    exact hinner (not_three_dvd_card_outer_of_alt e)
      (not_dvd_card_quotient_center_of (Nat.card_congr e.toEquiv)
        (not_dvd_card_alternatingGroup (by norm_num)))
  ·
    have hn4 := le_four_of_quotient_perm hperfPL eP
    have hn5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
    refine hinner (not_three_dvd_card_outer_of_center_alt e) ?_
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_alternatingGroup (by omega)
  ·
    exfalso
    have hn4 := le_four_of_quotient_perm hperfPL eP
    have hn5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
    exact false_of_alt_of_not_nine_dvd (m := 4 * n) (by omega) e
      (mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
        (not_three_dvd_card_outer_of_alt e) hu (by rw [pow_one]; exact hu3)) hu3 huC hfix
      (fun h9 => (not_nine_dvd_card_of_quotient_perm hperfPL eP) h9)
  ·
    exfalso
    refine false_of_surjective_perm_of_three (n := N - 2 * r) (by omega) hperfPL
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))) ?_
    exact Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))

end CFSG.HardMathSupport.Curtis.Coordinator
