module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24Check
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGoodE

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs

open CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
open scoped Pointwise

theorem arith_class (n : ℕ) (h : n * 11385 ≤ 244823040) : n ≤ 21504 := by omega

theorem arith_trio (n : ℕ) (h : n * 3795 ≤ 244823040) : n ≤ 64512 := by omega

theorem arith_index (m : ℕ) (h : 1024 * m = 244823040) : ¬ 2 ∣ m := by omega

theorem evalW_mem {G : Type*} [Group G] (H : Subgroup G) (S : List G) (hS : ∀ g ∈ S, g ∈ H) :
    ∀ w : List ℤ, evalW S w ∈ H := by
  intro w
  induction w with
  | nil => exact H.one_mem
  | cons z w ih =>
    have hget : ∀ i, S.getD i 1 ∈ H := by
      intro i
      by_cases hi : i < S.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hS _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact H.one_mem
    simp only [evalW]
    refine H.mul_mem ?_ ih
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)

theorem m24_localPair :
    LocalPair X24 := by
  classical
  obtain ⟨hs0len, hs0sort, hs01, hs0gen, hs0pow⟩ := s0_facts
  obtain ⟨hA1len, hZ2len, hA2len, ha2gen, ha2cl⟩ := a_facts
  obtain ⟨hK1len, hK1sort, hK1z, hK1nrm, hz1, hA1two, hzA1⟩ := k1_facts
  obtain ⟨hcr, hclen, hclsort⟩ := class_facts
  obtain ⟨htr, htrlen, htrsort⟩ := trio_facts
  obtain ⟨hT0len, hT0sort, hT0fix, hT0N⟩ := t0_facts
  obtain ⟨hK2len, hK2sort, hK2nrm⟩ := k2_facts
  obtain ⟨hQ1len, hQ1sort, hQ1K, hQ11, hQ1mul, hQ1nrm, hQ1pow, hQ1cent, hQ1A3, hQ1r⟩ := q1_facts
  obtain ⟨hQ2sort, hQ2K, hQ21, hQ2mul, hQ2nrm, hQ2pow, hQ2cent, hQ2A3, hQ2r⟩ := q2_facts
  obtain ⟨hgenmem, hwA, hwB⟩ := gen_facts
  have hsub0 := closureListH_subset tabX tabX_eq hkey s0gen 40
  have hS0nd : S0X.Nodup := nodup_of_strictAsc enc S0X hs0sort
  have hS0gen' : ∀ x ∈ S0X, ∀ g ∈ s0gen, x * g ∈ S0X := fun x hx g hg =>
    (mem_map_enc enc_injective).1 (hs0gen x hx g hg)
  set S₀ : Subgroup X24 := Subgroup.closure {g | g ∈ s0gen} with hS₀def
  have hS₀ : ∀ x, x ∈ S₀ ↔ x ∈ S0X := subgroupOfGens_exists s0gen S0X hsub0 hs01 hS0gen'
  have hS₀card : Nat.card ↥S₀ = 1024 := by rw [card_of_list hS0nd hS₀, hs0len]
  have hS₀2 : IsPGroup 2 S₀ := by
    intro g
    exact ⟨10, Subtype.ext (hs0pow _ ((hS₀ _).1 g.2))⟩
  have hXcard : Nat.card X24 = 244823040 := card_M24
  have hS₀i : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.card_mul_index S₀
    rw [hS₀card, hXcard] at h
    exact arith_index _ h
  have hA₁ : ∀ y, y ∈ canonZ S₀ ↔ y ∈ A1X := by
    intro y
    rw [mem_canonZ, hS₀]
    simp only [A1X, List.mem_filter, List.all_eq_true, beq_iff_eq]
    refine and_congr_right fun hyS => ?_
    constructor
    · intro h s hs
      have hsS : s ∈ S₀ := Subgroup.subset_closure hs
      have := h s hsS
      rw [this]
    · intro h
      have hcomm : ∀ g ∈ s0gen, y * g = g * y := fun g hg => by
        have := h g hg
        exact (enc_injective this).symm
      have hle : S₀ ≤ Subgroup.centralizer {y} := by
        rw [hS₀def, Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h' hh'
        rw [Set.mem_singleton_iff] at hh'
        rw [hh']
        exact hcomm g hg
      intro s hs
      have := Subgroup.mem_centralizer_iff.1 (hle hs) y rfl
      exact this.symm
  have hclS : S₀ = Subgroup.closure {g | g ∈ s0gen} := hS₀def
  have hZ₂ : ∀ y, y ∈ z2Set S₀ ↔ y ∈ Z2X := by
    intro y
    constructor
    · rintro ⟨hyS, hy⟩
      refine List.mem_filter.2 ⟨(hS₀ y).1 hyS, List.all_eq_true.2 fun s hs => ?_⟩
      have hsS : s ∈ S₀ := Subgroup.subset_closure hs
      have := (hA₁ _).1 (hy s hsS)
      exact List.contains_iff_mem.2 (List.mem_map.2 ⟨_, this, rfl⟩)
    · intro hy
      obtain ⟨hyS, hall⟩ := List.mem_filter.1 hy
      refine ⟨(hS₀ y).2 hyS, ?_⟩
      refine comm_mem_of_gens S₀ (canonZ S₀) s0gen hclS (fun z hz s hs => ?_) y ?_
      · exact (mem_canonZ.1 hz).2 s hs
      · intro s hs
        have := List.all_eq_true.1 hall s hs
        obtain ⟨c, hc, hce⟩ := List.mem_map.1 (List.contains_iff_mem.1 this)
        rw [(hA₁ _), ← enc_injective hce]
        exact hc
  have hA₂ : ∀ y, y ∈ canonC2 S₀ ↔ y ∈ A2X := by
    intro y
    rw [mem_canonC2, hS₀]
    simp only [A2X, List.mem_filter, List.all_eq_true, beq_iff_eq]
    refine and_congr_right fun hyS => ?_
    constructor
    · intro h w hw
      have hwz := (hZ₂ w).2 hw
      have := h w ((hS₀ w).2 (List.mem_filter.1 hw).1) hwz.2
      rw [this]
    · intro h w hwS hwz
      have hw : w ∈ Z2X := (hZ₂ w).1 ⟨hwS, hwz⟩
      exact enc_injective (h w hw)
  have hnodupK1 : K1X.Nodup := nodup_of_strictAsc enc K1X hK1sort
  have hzA : zX ∈ A1X := (mem_map_enc enc_injective).1 hzA1
  have hK₁ : ∀ x, x ∈ Subgroup.normalizer (canonZ S₀ : Set X24) ↔ x ∈ K1X := by
    intro x
    rw [mem_normalizer_of_lists (canonZ S₀) A1X hA₁ x]
    constructor
    · intro h
      have hx : x * zX * x⁻¹ = zX := by
        have h1 := (h zX hzA).1
        rcases hA1two _ h1 with h2 | h2
        · exfalso
          apply hz1
          have h3 : x * zX * x⁻¹ = 1 := enc_injective h2
          calc zX = x⁻¹ * (x * zX * x⁻¹) * x := by group
            _ = 1 := by rw [h3]; group
        · exact enc_injective h2
      have hcard : Nat.card ↥{y : X24 | y * zX * y⁻¹ = zX} ≤ K1X.length := by
        have h := card_centralizer_mul_le hcr (nodup_of_strictAsc enc classRes.1 hclsort)
        rw [hclen, hXcard] at h
        rw [hK1len]
        exact arith_class _ h
      exact mem_list_of_card_le {y : X24 | y * zX * y⁻¹ = zX} K1X hnodupK1
        (fun y hy => enc_injective (hK1z y hy)) hcard x hx
    · intro h a ha
      have := hK1nrm x h a ha
      exact ⟨(mem_map_enc enc_injective).1 this.1, (mem_map_enc enc_injective).1 this.2⟩
  have hnodupT0 : T0X.Nodup := nodup_of_strictAsc enc T0X hT0sort
  have hnodupK2 : K2X.Nodup := nodup_of_strictAsc enc K2X hK2sort
  have horb : ∀ i j, j ∈ orbL A2X i ↔ ∃ a ∈ canonC2 S₀, a • i = j := by
    intro i j
    simp only [orbL, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hA₂ a).2 ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hA₂ a).1 ha, rfl⟩
  have hτ : ∀ i, orbL A2X i ∈ trio := fun i => by
    simp only [trio, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨i, rfl⟩
  have hτ' : ∀ B ∈ trio, ∃ i, orbL A2X i = B := by
    intro B hB
    simp only [trio, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and] at hB
    exact hB
  have hstab : ∀ x, x ∈ Subgroup.normalizer (canonC2 S₀ : Set X24) → x ∈ T0X := by
    intro x hx
    have hfix : x • trio = trio := smul_partition_eq (canonC2 S₀) trio (orbL A2X) horb hτ hτ' hx
    have hcard : Nat.card ↥(↑(MulAction.stabilizer X24 trio) : Set X24) ≤ T0X.length := by
      have h := card_stab_mul_le htr (nodup_of_strictAsc encTrioN trioRes.1 htrsort)
      rw [htrlen, hXcard] at h
      rw [hT0len]
      exact arith_trio _ h
    exact mem_list_of_card_le (↑(MulAction.stabilizer X24 trio) : Set X24) T0X hnodupT0
      (fun y hy => MulAction.mem_stabilizer_iff.2 (hT0fix y hy)) hcard x
      (MulAction.mem_stabilizer_iff.2 hfix)
  have hgens₂ : ∀ a ∈ a2gen, a ∈ A2X := fun a ha => (mem_map_enc enc_injective).1 (ha2gen a ha)
  have hcl₂ : ∀ y ∈ A2X, y ∈ Subgroup.closure {x | x ∈ a2gen} := fun y hy =>
    closureListH_subset tabX tabX_eq hkey a2gen 40 y ((mem_map_enc enc_injective).1 (ha2cl y hy))
  have hnt := mem_normalizer_of_gens enc enc_injective (canonC2 S₀) A2X a2gen hA₂ hgens₂ hcl₂
  have hsub₂ : ∀ x ∈ K2X, x ∈ Subgroup.normalizer (canonC2 S₀ : Set X24) := fun x hx =>
    (hnt x).2 (hK2nrm x hx)
  have hK₂ : ∀ x, x ∈ Subgroup.normalizer (canonC2 S₀ : Set X24) ↔ x ∈ K2X := by
    have hT0Nnd : T0N.Nodup := hnodupT0.filter _
    have hcard : Nat.card ↥(↑(Subgroup.normalizer (canonC2 S₀ : Set X24)) : Set X24) ≤
        K2X.length := by
      have h := card_le_length_of_sub (↑(Subgroup.normalizer (canonC2 S₀ : Set X24)) : Set X24)
        T0N hT0Nnd (fun x hx => List.mem_filter.2 ⟨hstab x hx, (hnt x).1 hx⟩)
      rw [hT0N] at h
      rw [hK2len]
      exact h
    intro x
    exact ⟨fun hx => mem_list_of_card_le
      (↑(Subgroup.normalizer (canonC2 S₀ : Set X24)) : Set X24) K2X hnodupK2 hsub₂ hcard x hx,
      fun hx => hsub₂ x hx⟩
  have hgood₁ : GoodLocal (Subgroup.normalizer (canonZ S₀ : Set X24)) := by
    refine goodLocal_of_gens enc enc_injective _ K1X hK₁ hnodupK1 k1gen
      (fun x hx => closureListH_subset tabX tabX_eq hkey k1gen 60 x hx) Q1X
      (nodup_of_strictAsc enc Q1X hQ1sort)
      (fun q hq => (mem_map_enc enc_injective).1 (hQ1K q hq)) hQ11 hQ1mul hQ1nrm hQ1pow hQ1cent
      hQ1A3 ?_
    rw [hQ1r]
    exact fun n hn => not_dvd_chi0_168 n hn
  have hgood₂ : GoodLocal (Subgroup.normalizer (canonC2 S₀ : Set X24)) := by
    refine goodLocal_of_gens enc enc_injective _ K2X hK₂ hnodupK2 k2gen
      (fun x hx => closureListH_subset tabX tabX_eq hkey k2gen 60 x hx) A2X
      (nodup_of_strictAsc enc A2X hQ2sort)
      (fun q hq => (mem_map_enc enc_injective).1 (hQ2K q hq)) hQ21 hQ2mul hQ2nrm hQ2pow hQ2cent
      hQ2A3 ?_
    rw [hQ2r]
    exact not_dvd_chi0_of_lt (by norm_num) (by norm_num)
  have hne₁ : Subgroup.normalizer (canonZ S₀ : Set X24) ≠ ⊤ := by
    intro h
    have hc := card_of_list hnodupK1 hK₁
    rw [h, Subgroup.card_top, hXcard, hK1len] at hc
    exact absurd hc (by norm_num)
  have hne₂ : Subgroup.normalizer (canonC2 S₀ : Set X24) ≠ ⊤ := by
    intro h
    have hc := card_of_list hnodupK2 hK₂
    rw [h, Subgroup.card_top, hXcard, hK2len] at hc
    exact absurd hc (by norm_num)
  have hsup : Subgroup.normalizer (canonZ S₀ : Set X24) ⊔
      Subgroup.normalizer (canonC2 S₀ : Set X24) = ⊤ := by
    set J' : Subgroup (Equiv.Perm (Fin 24)) :=
      (Subgroup.normalizer (canonZ S₀ : Set X24) ⊔
        Subgroup.normalizer (canonC2 S₀ : Set X24)).map NativeSporadic.M24.subtype with hJ'
    have hjg : ∀ g ∈ jLetters, g ∈ J' := by
      intro g hg
      have := List.all_eq_true.1 hgenmem g hg
      obtain ⟨x, hx, hxg⟩ := List.any_eq_true.1 this
      rw [beq_iff_eq] at hxg
      have hxg' : x.1 = g := encPerm_injective (by norm_num) hxg
      refine ⟨x, ?_, hxg'⟩
      rcases List.mem_append.1 hx with h | h
      · exact Subgroup.mem_sup_left ((hK₁ x).2 h)
      · exact Subgroup.mem_sup_right ((hK₂ x).2 h)
    have hword : ∀ w : List ℤ, evalW jLetters w ∈ J' := evalW_mem J' jLetters hjg
    have hMle : NativeSporadic.M24 ≤ J' := by
      have hcl : Subgroup.closure ({m24gA, m24gB} : Set (Equiv.Perm (Fin 24))) ≤ J' := by
        rw [Subgroup.closure_le]
        intro g hg
        rcases hg with rfl | rfl
        · rw [← hwA]
          exact hword wordA
        · rw [← hwB]
          exact hword wordB
      rwa [← m24_eq] at hcl
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hMle x.2
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  refine ⟨S₀, _, _, hS₀2, hS₀i, ?_, ?_, hne₁, hne₂, hsup, hgood₁, hgood₂⟩
  · exact fun α hα => canonical_normalizer canonZ canonZ_map α hα
  · exact fun α hα => canonical_normalizer canonC2 canonC2_map α hα

end CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Blueprint

theorem pairsFor_M24 :
    PairsFor (TypeSporadic .M24) := by
  have : Finite (NativeSporadic.Carrier .M24) := inferInstanceAs (Finite M24Pairs.X24)
  exact pairsFor_of_localPair .M24 M24Pairs.m24_localPair

end CFSG.QuasithinUnique.Vol2Native.L239
