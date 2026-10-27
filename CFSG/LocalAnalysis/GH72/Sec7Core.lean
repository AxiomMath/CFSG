module

public import CFSG.LocalAnalysis.GH72.Sec7Tools
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH72

open Subgroup

namespace Sec7

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_centralizer {H : Subgroup G} {k : G} (hk : k ∈ normalizer (H : Set G)) :
    k ∈ normalizer (centralizer (H : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp
    (normal_subgroupOf_centralizer_normalizer _) hk

theorem quasisimple_commutator_of_simple {K K₀ T C M₁ : Subgroup G} {L : Type*} [Group L]
    [IsSimpleGroup L] (hLperf : commutator L = ⊤) (hK₀K : K₀ ≤ K)
    (hK₀ : (K₀.subgroupOf K).Normal) (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O K).subgroupOf K₀) (hTK₀ : T ≤ K₀)
    (hTc : T ≤ centralizer (O K : Set G)) (hTO : ¬ T ≤ O K)
    (hCdef : C = K₀ ⊓ centralizer (O K : Set G)) (hM₁def : M₁ = ⁅C, C⁆) :
    M₁ ≤ K₀ ∧ M₁ ≤ centralizer (O K : Set G) ∧ (M₁.subgroupOf K).Normal ∧ ⁅M₁, M₁⁆ = M₁ ∧
      CFSG.Open.IsQuasisimple M₁ ∧ O M₁ = M₁ ⊓ O K ∧
      (∃ g : M₁ →* L, Function.Surjective g ∧ g.ker = (O M₁).subgroupOf M₁) ∧
      Odd (M₁.relIndex K₀) := by
  have hCK₀ : C ≤ K₀ := hCdef ▸ inf_le_left
  have hCc : C ≤ centralizer (O K : Set G) := hCdef ▸ inf_le_right
  have hKK₀ : K ≤ normalizer (K₀ : Set G) := (normal_subgroupOf_iff_le_normalizer hK₀K).mp hK₀
  have hKO : K ≤ normalizer (O K : Set G) := CFSG.GH72.le_normalizer_O K
  have hKC : K ≤ normalizer (C : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun c hc => ?_
    rw [SetLike.mem_coe, hCdef] at hc ⊢
    exact ⟨(mem_normalizer_iff.mp (hKK₀ hk) c).mp hc.1,
      (mem_normalizer_iff.mp (mem_normalizer_centralizer (hKO hk)) c).mp hc.2⟩
  have hK₀C : K₀ ≤ normalizer (C : Set G) := hK₀K.trans hKC
  have hCn : (C.subgroupOf K₀).Normal := (normal_subgroupOf_iff_le_normalizer hCK₀).mpr hK₀C
  have hfC : (C.subgroupOf K₀).map f = ⊤ := by
    have : ((C.subgroupOf K₀).map f).Normal := hCn.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf K₀).map f) with h | h
    · refine absurd (fun t ht => ?_) hTO
      have htC : (⟨t, hTK₀ ht⟩ : K₀) ∈ C.subgroupOf K₀ := by
        rw [mem_subgroupOf, hCdef]
        exact ⟨hTK₀ ht, hTc ht⟩
      have h1 : f ⟨t, hTK₀ ht⟩ = 1 := by
        rw [← mem_bot, ← h]
        exact mem_map_of_mem f htC
      have h2 : (⟨t, hTK₀ ht⟩ : K₀) ∈ f.ker := h1
      rw [hker] at h2
      exact h2
    · exact h
  have hM₁C : M₁ ≤ C := hM₁def ▸ commutator_le_self C
  have hM₁K₀ : M₁ ≤ K₀ := hM₁C.trans hCK₀
  have hKM₁ : K ≤ normalizer (M₁ : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_map_conj_eq]
    have hc := mem_normalizer_iff_map_conj_eq.mp (hKC hk)
    rw [hM₁def, map_commutator, hc]
  have hM₁n : (M₁.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hM₁K₀.trans hK₀K)).mpr hKM₁
  have hmap : (C.subgroupOf K₀).map K₀.subtype = C := by
    rw [subgroupOf_map_subtype, inf_of_le_left hCK₀]
  have hM₁map : M₁ = (⁅C.subgroupOf K₀, C.subgroupOf K₀⁆).map K₀.subtype := by
    rw [map_commutator, hmap, hM₁def]
  have hM₁sub : M₁.subgroupOf K₀ = ⁅C.subgroupOf K₀, C.subgroupOf K₀⁆ := by
    rw [hM₁map]
    exact comap_map_eq_self_of_injective K₀.subtype_injective _
  have hfM₁ : (M₁.subgroupOf K₀).map f = ⊤ := by
    rw [hM₁sub, map_commutator, hfC, ← _root_.commutator_def, hLperf]
  set g : M₁ →* L := f.comp (inclusion hM₁K₀) with hgdef
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (hfM₁ ▸ mem_top y : y ∈ (M₁.subgroupOf K₀).map f)
    exact ⟨⟨x, hx⟩, hxy⟩
  have hgker : g.ker = (O K).subgroupOf M₁ := by
    ext x
    rw [MonoidHom.mem_ker, hgdef, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    rfl
  have hOM₁ : O M₁ = M₁ ⊓ O K := by
    apply le_antisymm
    · exact le_inf (O_le M₁) (O_le_O_of_normal (hM₁K₀.trans hK₀K) hM₁n)
    · refine le_O_of_normal inf_le_left ?_ ?_
      · have h : (M₁ ⊓ O K).subgroupOf M₁ = g.ker := by
          rw [hgker, inf_subgroupOf_left]
        rw [h]
        exact g.normal_ker
      · exact Odd.of_dvd_nat (card_O_odd K) (card_dvd_of_le inf_le_right)
  have hdec : ∀ c ∈ C, ∃ u ∈ M₁, ∃ z ∈ C, (∀ k ∈ C, Commute z k) ∧ c = u * z := by
    intro c hc
    obtain ⟨⟨m, hm⟩, hmc⟩ := hgs (f ⟨c, hCK₀ hc⟩)
    have hz : m⁻¹ * c ∈ O K := by
      have h1 : f ⟨m⁻¹ * c, mul_mem (inv_mem (hM₁K₀ hm)) (hCK₀ hc)⟩ = 1 := by
        have : (⟨m⁻¹ * c, mul_mem (inv_mem (hM₁K₀ hm)) (hCK₀ hc)⟩ : K₀) =
            (⟨m, hM₁K₀ hm⟩ : K₀)⁻¹ * ⟨c, hCK₀ hc⟩ := rfl
        rw [this, map_mul, map_inv]
        exact inv_mul_eq_one.mpr hmc
      have h2 : (⟨m⁻¹ * c, mul_mem (inv_mem (hM₁K₀ hm)) (hCK₀ hc)⟩ : K₀) ∈ f.ker := h1
      rw [hker] at h2
      exact h2
    refine ⟨m, hm, m⁻¹ * c, mul_mem (inv_mem (hM₁C hm)) hc, fun k hk => ?_, by group⟩
    exact (mem_centralizer_iff.mp (hCc hk)) _ hz
  have hperf : ⁅M₁, M₁⁆ = M₁ := by
    have h := commutator_le_of_forall_mul hM₁C hdec
    rw [← hM₁def] at h
    exact le_antisymm (commutator_le_self M₁) h
  have hcenter : center M₁ = g.ker := by
    apply le_antisymm
    · have : ((center M₁).map g).Normal := (center M₁).normal_of_characteristic.map g hgs
      have hbot : (center M₁).map g = ⊥ :=
        eq_bot_of_normal_of_comm hLperf inferInstance (by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [← map_mul, ← map_mul, (mem_center_iff.mp hy x).symm])
      exact (Subgroup.map_eq_bot_iff _).mp hbot
    · intro x hx
      rw [hgker] at hx
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hM₁C.trans hCc y.2)) _ hx).symm
  have hquasi : CFSG.Open.IsQuasisimple M₁ :=
    ⟨Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf),
      (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hgs))).mpr inferInstance⟩
  have hodd : Odd (M₁.relIndex K₀) := by
    have hn : (M₁.subgroupOf K₀).Normal :=
      (normal_subgroupOf_iff_le_normalizer hM₁K₀).mpr (hK₀K.trans hKM₁)
    let q := QuotientGroup.mk' (M₁.subgroupOf K₀)
    let r : (O K).subgroupOf K₀ →* K₀ ⧸ M₁.subgroupOf K₀ := q.comp ((O K).subgroupOf K₀).subtype
    have hr : Function.Surjective r := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨⟨m, hm⟩, hmx⟩ := hgs (f x)
      have hz : (⟨m, hM₁K₀ hm⟩ : K₀)⁻¹ * x ∈ (O K).subgroupOf K₀ := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
        exact inv_mul_eq_one.mpr hmx
      refine ⟨⟨_, hz⟩, ?_⟩
      show q ((⟨m, hM₁K₀ hm⟩ : K₀)⁻¹ * x) = q x
      have h1 : q ⟨m, hM₁K₀ hm⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hm
      rw [map_mul, map_inv, h1, inv_one, one_mul]
    have hdvd := Subgroup.card_dvd_of_surjective (f := r) hr
    rw [relIndex, index]
    refine Odd.of_dvd_nat ?_ hdvd
    have hc : Nat.card ((O K).subgroupOf K₀) = Nat.card (O K ⊓ K₀ : Subgroup G) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective K₀.subtype_injective]
    rw [hc]
    exact Odd.of_dvd_nat (card_O_odd K) (card_dvd_of_le inf_le_left)
  exact ⟨hM₁K₀, hM₁C.trans hCc, hM₁n, hperf, hquasi, hOM₁, ⟨g, hgs, by rw [hgker, hOM₁,
    inf_subgroupOf_left]⟩, hodd⟩

theorem covers_of_common_quotient {K M M₀ K₀ : Subgroup G} {L : Type*} [Group L]
    [IsSimpleGroup L] (hLperf : commutator L = ⊤) (hK₀def : K₀ = (K ⊓ M₀) ⊔ O K)
    (f₁ : K₀ →* L) (hf₁ : Function.Surjective f₁) (hker₁ : f₁.ker = (O K).subgroupOf K₀)
    (f₂ : M₀ →* L) (hf₂ : Function.Surjective f₂) (hker₂ : f₂.ker = (O M).subgroupOf M₀) :
    Covers K M₀ (O M) := by
  have : Finite L := Finite.of_surjective f₂ hf₂
  set P := K ⊓ M₀ with hPdef
  have hPK₀ : P ≤ K₀ := hK₀def ▸ le_sup_left
  have hOK₀ : O K ≤ K₀ := hK₀def ▸ le_sup_right
  have hPM₀ : P ≤ M₀ := inf_le_right
  set ψ : P →* L := f₁.comp (inclusion hPK₀) with hψdef
  set φ : P →* L := f₂.comp (inclusion hPM₀) with hφdef
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hf₁ y
    have hx : (x : G) ∈ ((P ⊔ O K : Subgroup G) : Set G) := by
      rw [← hK₀def]
      exact x.2
    rw [coe_mul_of_left_le_normalizer_right P (O K)
      (inf_le_left.trans (CFSG.GH72.le_normalizer_O K))] at hx
    obtain ⟨p, hp, o, ho, hpo⟩ := hx
    refine ⟨⟨p, hp⟩, ?_⟩
    have hxo : x = (⟨p, hPK₀ hp⟩ : K₀) * ⟨o, hOK₀ ho⟩ := Subtype.ext hpo.symm
    have ho1 : f₁ ⟨o, hOK₀ ho⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker₁]
      exact ho
    rw [hxo, map_mul, ho1, mul_one]
    rfl
  have hker : φ.ker ≤ ψ.ker := by
    have hn : (φ.ker.map ψ).Normal := φ.normal_ker.map ψ hψ
    have hodd : Odd (Nat.card (φ.ker.map ψ)) := by
      refine Odd.of_dvd_nat ?_ (card_map_dvd _ ψ)
      have hk : φ.ker = (O M).subgroupOf P := by
        ext x
        rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker₂]
        rfl
      have hc : Nat.card ((O M).subgroupOf P) = Nat.card (O M ⊓ P : Subgroup G) := by
        rw [← subgroupOf_map_subtype, card_map_of_injective P.subtype_injective]
      rw [hk, hc]
      exact Odd.of_dvd_nat (card_O_odd M) (card_dvd_of_le inf_le_left)
    exact (Subgroup.map_eq_bot_iff _).mp (eq_bot_of_normal_of_odd hLperf hn hodd)
  have hφ := surjective_of_ker_le φ ψ hψ hker le_rfl
  intro m hm
  obtain ⟨⟨x, hx⟩, hxm⟩ := hφ (f₂ ⟨m, hm⟩)
  have hz : x⁻¹ * m ∈ O M := by
    have h1 : (⟨x, hPM₀ hx⟩ : M₀)⁻¹ * ⟨m, hm⟩ ∈ f₂.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr hxm
    rw [hker₂] at h1
    exact h1
  have : m = x * (x⁻¹ * m) := by group
  rw [this]
  exact mul_mem (mem_sup_left hx) (mem_sup_right hz)

theorem le_centralizer_of_forall_inf {E Y : Subgroup G} [hY : IsKleinFour Y]
    (hE : Odd (Nat.card E)) (hYE : Y ≤ normalizer (E : Set G))
    (h : ∀ y ∈ Y, y ≠ 1 → Y ≤ centralizer ((E ⊓ C y : Subgroup G) : Set G)) :
    Y ≤ centralizer (E : Set G) := by
  have hY2 : ∀ y ∈ Y, y * y = 1 := by
    intro y hy
    have h1 : (⟨y, hy⟩ : Y) * ⟨y, hy⟩ = 1 := by
      rw [← pow_two, ← IsKleinFour.exponent_two (G := Y)]
      exact Monoid.pow_exponent_eq_one _
    exact congrArg Subtype.val h1
  have : Nontrivial Y :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨⟨a₁, ha₁⟩, ha₁1⟩ := exists_ne (1 : Y)
  have ha₁1' : a₁ ≠ 1 := fun h => ha₁1 (Subtype.ext h)
  have hlt : zpowers a₁ < Y := by
    refine lt_of_le_of_ne ((zpowers_le).mpr ha₁) fun heq => ?_
    have h4 : Nat.card Y = 4 := IsKleinFour.card_four
    have h2 : Nat.card (zpowers a₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hY2 a₁ ha₁) ha₁1'
    rw [heq, h4] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨a₂, ha₂, ha₂z⟩ := SetLike.exists_of_lt hlt
  have ha₂1 : a₂ ≠ 1 := fun h => ha₂z (h ▸ one_mem _)
  have ha₁₂ : a₁ ≠ a₂ := fun h => ha₂z (h ▸ mem_zpowers a₁)
  have hinv : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right (hY2 a₂ ha₂)
  have ha₃1 : a₁ * a₂ ≠ 1 := fun h => ha₁₂ (by rw [← hinv]; exact eq_inv_of_mul_eq_one_left h)
  have ha₁₃ : a₁ ≠ a₁ * a₂ := fun h => ha₂1 (by simpa using h)
  have ha₂₃ : a₂ ≠ a₁ * a₂ := fun h => ha₁1' (by simpa using h)
  have hdec := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers hE hYE ha₁ ha₂
    (mul_mem ha₁ ha₂) ha₁1' ha₂1 ha₃1 ha₁₂ ha₁₃ ha₂₃
  intro y hy
  rw [mem_centralizer_iff]
  intro e he
  have he' : e ∈ (E : Set G) := he
  rw [hdec] at he'
  obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := he'
  have k₁ := mem_centralizer_iff.mp (h a₁ ha₁ ha₁1' hy) c₁ hc₁
  have k₂ := mem_centralizer_iff.mp (h a₂ ha₂ ha₂1 hy) c₂ hc₂
  have k₃ := mem_centralizer_iff.mp (h _ (mul_mem ha₁ ha₂) ha₃1 hy) c₃ hc₃
  rw [show c₁ * c₂ * c₃ * y = c₁ * c₂ * (c₃ * y) by group, k₃,
    show c₁ * c₂ * (y * c₃) = c₁ * (c₂ * y) * c₃ by group, k₂,
    show c₁ * (y * c₂) * c₃ = (c₁ * y) * c₂ * c₃ by group, k₁]
  group

end Sec7

end CFSG.GH72
