module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterY
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterTypes
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterFFDefs
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterPerfect
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterDefs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open scoped commutatorElement
open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem nine_dvd_two_pow_sub_one {e : ℕ} (he : Even e) (h3 : 3 ∣ e) : 9 ∣ 2 ^ e - 1 := by
  obtain ⟨m, rfl⟩ : 6 ∣ e := by
    obtain ⟨k, hk⟩ := he
    omega
  have h : 2 ^ (6 * m) = 64 ^ m := by rw [pow_mul]; norm_num
  rw [h]
  have := Nat.sub_dvd_pow_sub_pow 64 1 m
  rw [one_pow] at this
  exact (show 9 ∣ 64 - 1 by norm_num).trans this

theorem three_dvd_two_pow_sub_one {e : ℕ} (he : Even e) : 3 ∣ 2 ^ e - 1 := by
  obtain ⟨k, rfl⟩ := he
  have h : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h]
  have := Nat.sub_dvd_pow_sub_pow 4 1 k
  rw [one_pow] at this
  exact (show 3 ∣ 4 - 1 by norm_num).trans this

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem blockPL_conj_mem (hA : Asc81bHyp M S) {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hxL : x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ j ∈ blockPL M S L, x * j * x⁻¹ ∈ blockPL M S L := by
  rw [blockPL_eq_inf_normalizer hA.twoRadical.1 hA.twoCore_le]
  rintro j ⟨hjL, hjS⟩
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxL j).mp hjL,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxS hjS) (Subgroup.inv_mem _ hxS)⟩

theorem barM_inf_eq (hA : Asc81bHyp M S) :
    barM M (S ⊓ L) = barM M S ⊓ barM M L := by
  refine le_antisymm (le_inf (barM_mono inf_le_left) (barM_mono inf_le_right)) ?_
  intro m ⟨hmS, hmL⟩
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hmL
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hlS : (l : G) ∈ S := coe_mem_of_mk_mem_barM hA.twoCore_le l hmS
  exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hlS, hlL⟩, rfl⟩

theorem toral_setup (hZ : KFactFixCensusCenter)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (h93 : NineThreeConclusion M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    (h3A6 : ¬ (Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))))
    {ζ : ↥M ⧸ CFSG.pCore 2 ↥M} (hζL : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hu3 : u ^ 3 = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) :
    ∃ (e : ℕ) (ψ : ↥(barM M L) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 e)) (d : ℕ),
      Even e ∧ 2 ≤ e ∧ CompParab (barM M L) (blockPL M S L) ∧
        pCoreOf 2 (blockPL M S L) = barM M S ⊓ barM M L ∧
        ToralCfg (barM M L) (blockPL M S L) ψ d u := by
  have hodd := odd_card_center_barM_of_isWeakSBlock hL
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    set z : ↥(barM M L) := ⟨ζ, hζL⟩ with hz
    have hzc : z ∈ Subgroup.center ↥(barM M L) := (mem_center_iff_mem_centralizer z).mpr hζC
    have hz3 : z ^ 3 = 1 := Subtype.ext (by simpa [hz] using hζ3)
    have hz1 : z ≠ 1 := fun h => hζ1 (by simpa [hz] using congrArg Subtype.val h)
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have : orderOf (⟨z, hzc⟩ : ↥(Subgroup.center ↥(barM M L))) = 3 := by
      rw [← hord]; exact Subgroup.orderOf_mk _ _
    rw [← this]
    exact orderOf_dvd_natCard _
  have h2 := nineThreeTwo_of_center hL h93 hX h3A6 hodd h3
  have hCP := compParab_of_nineThreeTwo hA hL hS h2
  obtain ⟨e, he, he2, ⟨ψ⟩⟩ := hZ _ (barM M L) (blockPL M S L) hCP hcyc h3 h3A6 u hu hu3 huC hfix
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ', d, hd, hJ⟩ := exists_setup hCP ψ
  exact ⟨e, ψ', d, he, he2, hCP, h2.2.2.symm.trans (barM_inf_eq hA), ⟨hd, hJ, hu, hu3, huC, hfix⟩⟩

theorem field_facts {e : ℕ} (he : Even e) (he2 : 2 ≤ e) :
    Nat.card (GaloisField 2 e) = 2 ^ e ∧
      ∃ ω : GaloisField 2 e, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  refine ⟨hk, ?_⟩
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd (K := GaloisField 2 e) (d := 3)
    (by rw [hk]; exact three_dvd_two_pow_sub_one he)
  exact ⟨ω, hω.ne_one (by norm_num), hω.pow_eq_one⟩

theorem blockPL_le_normalizer (hA : Asc81bHyp M S) :
    blockPL M S L ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [blockPL_eq_inf_normalizer hA.twoRadical.1 hA.twoCore_le]
  exact inf_le_right

theorem citedBlockToralThreeCenter_of (hZ : KFactFixCensusCenter)
    (hFF : CitedBlockToralCenterFF) : CitedBlockToralThreeCenter := by
  intro G _ _ M S L hK hA hL h93 hX hS hcyc h3A6 ζ hζL hζC hζ3 hζ1 u hu hu3 huC hfix
  obtain ⟨e, ψ, d, he, he2, -, -, cfg⟩ :=
    toral_setup hZ hA hL h93 hX hS hcyc h3A6 hζL hζC hζ3 hζ1 hu hu3 huC hfix
  obtain ⟨hk, ω, hω1, hω3⟩ := field_facts he he2
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun x hx hC _ => toral_a ψ ζ hζL hζC hζ3 hζ1 x hx hC, toral_b cfg hω1 hω3, ?_⟩
  intro X hX3 hXL hXS hXu hX81 hmax
  have hc1 : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    by_cases h9 : 9 ∣ Nat.card (GaloisField 2 e) - 1
    · intro a ha b hb
      have hab := toral_c1_nine cfg hω1 hω3 h9 (blockPL_le_normalizer hA) hX3 hXL hXS hXu hX81
        hmax a ha b hb
      have : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hab]; group
      rw [this]
      exact Subgroup.one_mem _
    · have h3f : ¬ 3 ∣ e := fun h3 => h9 (by rw [hk]; exact nine_dvd_two_pow_sub_one he h3)
      exact toral_c1_small cfg hω1 hω3 (by omega) hk h3f h9
        (fun x hxQ hxL j hj => blockPL_conj_mem hA hxL hxQ j hj) hX3 hXL hXS hXu
  have hc1' : ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hc1 a ha b hb
  exact ⟨hc1', hFF G M S L hK hA hL h93 hX hS hcyc h3A6 ζ hζL hζC hζ3 hζ1 u hu hu3 huC hfix X hX3
    hXL hXS hXu hX81 hmax hc1'⟩

open CFSG.AGLEmbedding.ParabPrime in
theorem citedBlockToralThreeCenterFix_of
    (hZ : KFactFixCensusCenter) (hG : GlueVhyp) : CitedBlockToralThreeCenterFix := by
  intro G _ _ M S L hK hA hL h93 hX hS hcyc h3A6 ζ hζL hζC hζ3 hζ1 u hu hu3 huC hfix hV
  obtain ⟨e, ψ, d, he, he2, hCP, hpc, cfg⟩ :=
    toral_setup hZ hA hL h93 hX hS hcyc h3A6 hζL hζC hζ3 hζ1 hu hu3 huC hfix
  obtain ⟨hk, ω, hω1, hω3⟩ := field_facts he he2
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQJ : ∀ x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ∀ j ∈ blockPL M S L, x * j * x⁻¹ ∈ blockPL M S L :=
    fun x hxQ hxL j hj => blockPL_conj_mem hA hxL hxQ j hj
  have hjoin : u ∈ perfectJoin (blockPL M S L) ⊔
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rcases hV with ⟨V, hVV, hVL, hVS, huV⟩ | hV3
    · refine hG _ (barM M L) (blockPL M S L) hCP V hVV hVL ?_ huV
      intro x hx
      rw [hpc]
      exact Subgroup.mem_normalizer_iff.mpr fun h => by
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hVS hx) h,
          Subgroup.mem_normalizer_iff.mp (hVL hx) h]
    · exfalso
      obtain ⟨W, hWJ, hW, h3W⟩ := exists_perfect_three_dvd_of_compParab hCP he2 (projEquiv ψ)
      exact absurd (Nat.Coprime.eq_one_of_dvd (hV3 W hWJ hW) h3W) (by norm_num)
  refine ⟨toralF_a (Q := Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M))) cfg
    blockPL_le_barM hQJ hjoin, fun huL => ?_⟩
  by_cases h9 : 9 ∣ Nat.card (GaloisField 2 e) - 1
  · right
    intro Y X hY3 hYL hXY hXS hXu hmax y hy
    exact toralF_b_big cfg hω1 hω3 h9 (blockPL_le_normalizer hA) huL hY3 hYL hXY hXS hXu hmax y hy
  · left
    have h3f : ¬ 3 ∣ e := fun h3 => h9 (by rw [hk]; exact nine_dvd_two_pow_sub_one he h3)
    exact toralF_b_small cfg hω1 hω3 (by omega) hk h3f h9 hQJ huL

end CFSG.HardMathSupport.Curtis.Coordinator
