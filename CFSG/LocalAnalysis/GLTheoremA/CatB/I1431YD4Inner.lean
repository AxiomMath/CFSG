module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LD4S
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

open Module Matrix CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

theorem finrank_fixV_add_movV {t : StatedSp 4 (ZMod 2)} (ht3 : t ^ 3 = 1) :
    finrank (ZMod 2) (fixV t) + finrank (ZMod 2) (movV t) = 8 := by
  have h : finrank (ZMod 2) (fixV t ⊔ movV t : Submodule (ZMod 2) VV) +
      finrank (ZMod 2) (fixV t ⊓ movV t : Submodule (ZMod 2) VV) =
      finrank (ZMod 2) (fixV t) + finrank (ZMod 2) (movV t) :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  rw [fixV_sup_movV ht3, fixV_inf_movV, finrank_bot, finrank_top] at h
  have h8 : finrank (ZMod 2) VV = 8 := I2016Sp.finrank_V8
  omega

theorem mem_normalizer_of_inv_conj {G : Type} [Group G] {T : Subgroup G} {g : G} (hg3 : g ^ 3 = 1)
    (hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ T) : g ∈ Subgroup.normalizer (T : Set G) := by
  have hg2 : g⁻¹ = g ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hg3]
  have hgg : g * g = g⁻¹ := by rw [hg2, sq]
  have hg' : g⁻¹ * g⁻¹ = g := by
    calc g⁻¹ * g⁻¹ = g ^ 2 * g ^ 2 := by rw [hg2]
      _ = g ^ 3 * g := by group
      _ = g := by rw [hg3, one_mul]
  have h1 : ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro t ht
    have h2 := hTg _ (hTg t ht)
    have e : g⁻¹ * (g⁻¹ * t * g) * g = g * t * g⁻¹ := by
      calc g⁻¹ * (g⁻¹ * t * g) * g = (g⁻¹ * g⁻¹) * t * (g * g) := by group
        _ = g * t * g⁻¹ := by rw [hg', hgg]
    rwa [e] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact h1 h hh
  · intro hh
    have := hTg _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rwa [e] at this

theorem hasA6Quot_map {G G' : Type} [Group G] [Group G'] (φ : G →* G') (hφ : Function.Injective φ)
    {A : Subgroup G} (h : I2016.HasA6Quot A) : I2016.HasA6Quot (A.map φ) := by
  obtain ⟨A₀, S₆, hS₆, f, hA₀A, hcat, hfs⟩ := h
  let e : ↥(A₀.map φ) ≃* ↥A₀ := (Subgroup.equivMapOfInjective A₀ φ hφ).symm
  exact ⟨A₀.map φ, S₆, hS₆, f.comp e.toMonoidHom, Subgroup.map_mono hA₀A, hcat,
    hfs.comp e.surjective⟩

theorem noT_inner_om8 (hcard : Nat.card ↥Om8 = 3 ^ 5 * 716800)
    {g : ↥Om8} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {H T : Subgroup ↥Om8}
    (hH : H ≤ Subgroup.centralizer ({g} : Set ↥Om8)) (hA6 : I2016.HasA6Quot H)
    (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 ↥T) (hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ T)
    (hHT : H ≤ Subgroup.normalizer (T : Set ↥Om8)) : False := by
  have hA6c := hA6
  obtain ⟨A₀, S, hSg, f, hA₀H, hSc, hf⟩ := hA6
  obtain ⟨hSsimp, hS360⟩ := CatB.I1431YU5.isA6_isSimpleGroup hSc
  haveI : IsSimpleGroup S := hSsimp
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS360]; norm_num)
  haveI : Group.IsPerfect S := isPerfect_of_simple (by rw [hS360]; norm_num)
  obtain ⟨L, hLA, hLperf, φ, hφ⟩ := exists_perfect_sub f hf
  haveI := hLperf
  have hLH : L ≤ H := hLA.trans hA₀H
  have hLg : ∀ l ∈ L, l * g = g * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hH (hLH hl))
  have hg3' : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have h360 : 360 ∣ Nat.card L := hS360 ▸ Subgroup.card_dvd_of_surjective hφ
  have h27 : 27 ∣ Nat.card ↥(L ⊔ Subgroup.zpowers g) := dvd_card_sup_zpowers hg3 hg1 hLg hS360 φ hφ
  have h25920 : 25920 ≤ Nat.card ↥(Subgroup.centralizer ({g} : Set ↥Om8)) := by
    rcases U42Cat.centSplitOn_Om8 g hg3' with hno | ⟨K₀, hK₀⟩
    · exfalso
      exact hno L (fun l hl => Subgroup.mem_centralizer_singleton_iff.2 (hLg l hl)) hLperf
        ((by norm_num : 5 ∣ 360).trans h360)
    · calc 25920 = Nat.card K₀ := hK₀.2.2.2.2.symm
        _ ≤ _ := Subgroup.card_le_of_le hK₀.1
  have hincl : Function.Injective (Subgroup.inclusion om8_le_sp8) := Subgroup.inclusion_injective _
  have ht3 : (Subgroup.inclusion om8_le_sp8 g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have ht1 : Subgroup.inclusion om8_le_sp8 g ≠ 1 := fun h => hg1 (hincl (by rw [h, map_one]))
  obtain ⟨s₀', hdimF, hs4⟩ := U4Sp8.dimension_count ht3 ht1
  obtain ⟨s₀, hC⟩ := U4Sp8.exists_class_spSupported ht3 ht1
  generalize hA₀def : spSupported (Subgroup.inclusion om8_le_sp8 g) {(Polynomial.X - 1 : Polynomial (ZMod 2))} = A₀' at hC
  generalize hA₁def : spSupported (Subgroup.inclusion om8_le_sp8 g) {q2} = A₁' at hC
  generalize hmdef : primaryMultiplicity (spEnd (Subgroup.inclusion om8_le_sp8 g)) q2 = m at hC hs4
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    have h1 := hC.one_le
    have h4 := hC.sum_eq
    omega
  have hbound : Nat.card ↥(Subgroup.centralizer ({g} : Set ↥Om8)) ≤ Nat.card ↥A₀' * Nat.card ↥A₁' := by
    refine le_trans ?_ (card_sup_le hC.commute)
    rw [← hC.centralizer_eq]
    refine Nat.card_le_card_of_injective
      (fun x : ↥(Subgroup.centralizer ({g} : Set ↥Om8)) =>
        (⟨Subgroup.inclusion om8_le_sp8 x.1, ?_⟩ :
          ↥(Subgroup.centralizer ({Subgroup.inclusion om8_le_sp8 g} : Set ↥(StatedSp 4 (ZMod 2))))))
      ?_
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    · intro x y hxy
      exact Subtype.ext (hincl (congrArg Subtype.val hxy))
  rcases hm with rfl | rfl | rfl | rfl
  ·
    have hF : finrank (ZMod 2) (fixV (Subgroup.inclusion om8_le_sp8 g)) = 6 := by
      have h : finrank (ZMod 2) (fixV (Subgroup.inclusion om8_le_sp8 g)) = 2 * s₀' := hdimF
      have : s₀' = 3 := by omega
      rw [h, this]
    have hM : finrank (ZMod 2) (movV (Subgroup.inclusion om8_le_sp8 g)) = 2 := by
      have := finrank_fixV_add_movV ht3
      omega
    have hEN : L ⊔ Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set ↥Om8) :=
      sup_le (fun l hl => hHT (hLH hl))
        ((Subgroup.zpowers_le).2 (mem_normalizer_of_inv_conj hg3 hTg))
    obtain ⟨R₀, hR0, hts, hinvR⟩ :=
      U42Cat.omTSFact_holds (L ⊔ Subgroup.zpowers g) T hT2 hT1 hEN
    exact m1_core hcard hg3 hM h27 hR0 hts (fun y hy x hx => hinvR y hy x hx)
  · obtain rfl : s₀ = 2 := by have := hC.sum_eq; omega
    have := I2016Sp.card_product_two hC
    omega
  · obtain rfl : s₀ = 1 := by have := hC.sum_eq; omega
    have := I2016Sp.card_product_three hC
    omega
  ·
    obtain rfl : s₀ = 0 := by have := hC.sum_eq; omega
    refine I2016Sp.noT_of_fpf I2016Sp.fpfIrrGap_holds ht3 ht1 hC
      (A := H.map (Subgroup.inclusion om8_le_sp8)) ?_ (hasA6Quot_map _ hincl hA6c)
      (T := T.map (Subgroup.inclusion om8_le_sp8)) ?_ ?_ ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 (hH hh))
    · exact fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hincl).1 h)
    · exact hT2.map _
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨g⁻¹ * t * g, hTg t ht, by simp⟩
    · exact (Subgroup.map_mono hHT).trans (Subgroup.le_normalizer_map _)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

end
