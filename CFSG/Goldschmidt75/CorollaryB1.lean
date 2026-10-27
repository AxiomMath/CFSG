module

public import CFSG.Goldschmidt75.B1Main

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normal_perfRes_centralizer_of_oddCore_eq_bot
    (T : Sylow 2 G) {S : Subgroup G}
    (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T) (hO : goldschmidtOddCore G = ⊥) :
    (perfRes (centralizer (S : Set G))).Normal := by
  set L := perfRes (centralizer (S : Set G)) with hL
  set A := S ⊓ L with hA
  have hAn : A.Normal := normal_inf_perfRes T hST hS hO
  set q := QuotientGroup.mk' A with hq
  set Y := (goldschmidtOddCore (G ⧸ A)).comap q with hY
  have hX := commutator_normalClosure_le_comap T hST hS hAn
  have hLR := perfRes_le_normalClosure T hST hS
  have hLperf := commutator_perfRes (centralizer (S : Set G))
  have hLA : L ≤ centralizer (A : Set G) := (perfRes_le _).trans (centralizer_le inf_le_left)
  have hYn : Y.Normal := (goldschmidtOddCore_normal _).comap q
  have hQn : (Y ⊓ centralizer (A : Set G)).Normal := normal_inf_normal _ _
  have hA2 : IsPGroup 2 A := T.isPGroup'.to_le (inf_le_left.trans hST)
  have hodd : Odd (A.subgroupOf (Y ⊓ centralizer (A : Set G))).index := by
    let φ : (Y ⊓ centralizer (A : Set G) : Subgroup G) →* G ⧸ A :=
      q.comp (Y ⊓ centralizer (A : Set G)).subtype
    have hker : φ.ker = A.subgroupOf (Y ⊓ centralizer (A : Set G)) := by
      ext x
      simp [φ, hq, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hrange : φ.range ≤ goldschmidtOddCore (G ⧸ A) := by
      rintro _ ⟨x, rfl⟩
      exact (mem_inf.mp x.2).1
    rw [← hker, Subgroup.index_ker]
    exact Odd.of_dvd_nat odd_card_oddCore (Subgroup.card_dvd_of_le hrange)
  have hQA := le_of_le_centralizer_of_odd hO hQn inf_le_right hA2 hodd
  have hYL : ⁅Y, L⁆ ≤ A := by
    rw [commutator_le]
    intro y hy l hl
    apply hQA
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, mul_assoc y, mul_assoc y]
      refine Y.mul_mem hy ?_
      have := hYn.conj_mem _ (inv_mem hy) l
      simpa [mul_assoc] using this
    · rw [mem_centralizer_iff]
      intro a ha
      have hl' := mem_centralizer_iff.mp (hLA hl)
      have ha' : y⁻¹ * a * y ∈ A := by
        have := hAn.conj_mem a ha y⁻¹
        simpa using this
      have e1 : l⁻¹ * a = a * l⁻¹ := by
        calc l⁻¹ * a = l⁻¹ * (a * l) * l⁻¹ := by group
          _ = l⁻¹ * (l * a) * l⁻¹ := by rw [hl' a ha]
          _ = a * l⁻¹ := by group
      have e2 : (y⁻¹ * a * y) * l = l * (y⁻¹ * a * y) := hl' _ ha'
      rw [commutatorElement_def]
      calc a * (y * l * y⁻¹ * l⁻¹) = y * ((y⁻¹ * a * y) * l) * y⁻¹ * l⁻¹ := by group
        _ = y * (l * (y⁻¹ * a * y)) * y⁻¹ * l⁻¹ := by rw [e2]
        _ = y * l * y⁻¹ * (a * l⁻¹) := by group
        _ = y * l * y⁻¹ * (l⁻¹ * a) := by rw [e1]
        _ = y * l * y⁻¹ * l⁻¹ * a := by group
  have hAL : ⁅A, L⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hLA
  have hLY : ⁅L, Y⁆ = ⊥ := by
    have h2 : ⁅⁅Y, L⁆, L⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hYL le_rfl).trans hAL.le)
    have h1 : ⁅⁅L, Y⁆, L⁆ = ⊥ := by rw [commutator_comm L Y]; exact h2
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hLperf] at h3
  set G₀ := normalClosure (S : Set G) with hG₀
  have hG₀L : ⁅G₀, L⁆ = ⊥ := by
    have hle : ⁅G₀, L⁆ ≤ Y := (commutator_mono le_rfl hLR).trans hX
    have hYL' : ⁅Y, L⁆ = ⊥ := by rw [commutator_comm]; exact hLY
    have h2 : ⁅⁅G₀, L⁆, L⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hle le_rfl).trans hYL'.le)
    have h1 : ⁅⁅L, G₀⁆, L⁆ = ⊥ := by rw [commutator_comm L G₀]; exact h2
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hLperf] at h3
    rw [commutator_comm]
    exact h3
  have hG₀C : G₀ ≤ centralizer (L : Set G) := commutator_eq_bot_iff_le_centralizer.mp hG₀L
  refine ⟨fun l hl g => ?_⟩
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure T hST hS g
  have hn : g * m⁻¹ ∈ normalizer (S : Set G) := by
    refine mem_normalizer_of_forall (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : m⁻¹ * x * m ∈ conjSub m S := by
        rw [mem_conjSub]
        simpa [mul_assoc] using hx
      rw [← hmeq, mem_conjSub] at h1
      simpa [mul_assoc] using h1
    · have h1 : g⁻¹ * x * g ∈ conjSub g S := by
        rw [mem_conjSub]
        simpa [mul_assoc] using hx
      rw [hmeq, mem_conjSub] at h1
      simpa [mul_assoc] using h1
  have hnL := normalizer_le_normalizer_perfRes_centralizer S hn
  have hml : m * l * m⁻¹ = l := by
    have := mem_centralizer_iff.mp (hG₀C hm) l hl
    rw [← this]
    group
  have e : g * l * g⁻¹ = (g * m⁻¹) * (m * l * m⁻¹) * (g * m⁻¹)⁻¹ := by group
  rw [e, hml]
  exact (mem_normalizer_iff.mp hnL l).mp hl

theorem centralizer_map_oddCore (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    centralizer ((S.map (QuotientGroup.mk' (goldschmidtOddCore G)) : Subgroup _) : Set _) =
      (centralizer (S : Set G)).map (QuotientGroup.mk' (goldschmidtOddCore G)) := by
  set O := goldschmidtOddCore G with hO
  set q := QuotientGroup.mk' O with hq
  refine le_antisymm (fun gb hgb => ?_) ?_
  · have hgbN : gb ∈ normalizer ((S.map q : Subgroup (G ⧸ O)) : Set (G ⧸ O)) :=
      centralizer_le_normalizer _ hgb
    rw [normalizer_map O T hST hS] at hgbN
    obtain ⟨n, hn, rfl⟩ := hgbN
    refine ⟨n, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    have h1 : n * s * n⁻¹ ∈ S := (mem_normalizer_iff.mp hn s).mp hs
    have h2 : q (n * s * n⁻¹) = q s := by
      have h3 : q s * q n = q n * q s := mem_centralizer_iff.mp hgb (q s) ⟨s, hs, rfl⟩
      rw [map_mul, map_mul, map_inv, ← h3]
      group
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    have h4 := eq_one_of_mem_odd_of_mem_sylow T odd_card_oddCore h2
      (mul_mem (inv_mem (hST h1)) (hST hs))
    have h5 : n * s * n⁻¹ = s := inv_mul_eq_one.mp h4
    calc s * n = n * s * n⁻¹ * n := by rw [h5]
      _ = n * s := by group
  · rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc s hs]

theorem corollaryB1
    (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    ((CFSG.perfectResidual (centralizer (S : Set G))).map (centralizer (S : Set G)).subtype ⊔
      goldschmidtOddCore G).Normal := by
  set O := goldschmidtOddCore G with hO
  set q := QuotientGroup.mk' O with hq
  have h := normal_perfRes_centralizer_of_oddCore_eq_bot (sylowMap O T) (S := S.map q)
    (by rw [coe_sylowMap]; exact map_mono hST) (stronglyClosed_map O T hST hS)
    oddCore_quotient_eq_bot
  rw [centralizer_map_oddCore T hST hS, ← map_perfRes] at h
  have h2 := h.comap q
  rw [comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact h2

theorem goldschmidtB1_simple
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {B : Subgroup G} (hBS : B ≤ S) (hB : B ≠ ⊥)
    (hBsc : fusionStronglyClosed (B : Set G) S) :
    (CFSG.perfectResidual (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype = ⊥ := by
  obtain ⟨a₀, b₀, hab⟩ := hnonab
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (h ▸ mem_top b₀) a₀) hab
  have hO : goldschmidtOddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (goldschmidtOddCore G) with h | h
    · exact h
    · have hodd : Odd (Nat.card G) := by
        have := odd_card_oddCore (G := G)
        rwa [h, Subgroup.card_top] at this
      have hsol := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      exact absurd ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a₀ b₀) hab
  have hn := corollaryB1 S hBS hBsc
  rw [hO, sup_bot_eq] at hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.perfectResidual
      (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype) with h | h
  · exact h
  · exfalso
    apply hB
    have hC : centralizer (B : Set G) = ⊤ := top_le_iff.mp (h ▸ perfRes_le _)
    rw [eq_bot_iff, ← hZ]
    intro b hb
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (hC ▸ mem_top g) b hb).symm

theorem goldschmidtB1_simple_not_mem
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {B : Subgroup G} (hBS : B ≤ S) (hB : B ≠ ⊥)
    (hBsc : fusionStronglyClosed (B : Set G) S) {z : G} (hz : orderOf z = 2) :
    z ∉ (CFSG.perfectResidual (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype := by
  rw [goldschmidtB1_simple hnonab S hBS hB hBsc, mem_bot]
  intro h
  rw [h, orderOf_one] at hz
  exact absurd hz (by norm_num)

end CFSG.Goldschmidt75
