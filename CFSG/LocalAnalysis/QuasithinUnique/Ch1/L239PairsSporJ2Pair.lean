module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2Check
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGoodE

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs

open CFSG.Open
open scoped Pointwise

theorem j2_localPair :
    LocalPair XJ := by
  classical
  obtain ⟨hs0len, hs0sort, hs01, hs0gen, hs0pow⟩ := s0_facts
  obtain ⟨hA1len, hZ2len, hA2len, ha2gen, ha2cl⟩ := a_facts
  obtain ⟨hK1len, hK1sort, hK1nrm, hK1fix⟩ := k1_facts
  obtain ⟨hr1, hr1len, hr1sort⟩ := orb1_facts
  obtain ⟨hK2len, hK2sort, hK2nrm, hK2fix⟩ := k2_facts
  obtain ⟨hr2, hr2len, hr2sort⟩ := orb2_facts
  obtain ⟨hQ1len, hQ1sort, hQ1K, hQ11, hQ1mul, hQ1nrm, hQ1pow, hQ1cent, hQ1E⟩ := q1_facts
  obtain ⟨hQ2sort, hQ2K, hQ21, hQ2mul, hQ2nrm, hQ2pow, hQ2cent, hQ2A3, hQ2r⟩ := q2_facts
  obtain ⟨hgenmem, hwA, hwB⟩ := gen_facts
  have hsub0 := closureListH_subset tabX tabX_eq hkey s0gen 40
  have hS0nd : S0X.Nodup := nodup_of_strictAsc enc S0X hs0sort
  have hS0gen' : ∀ x ∈ S0X, ∀ g ∈ s0gen, x * g ∈ S0X := fun x hx g hg =>
    (mem_map_enc enc_injective).1 (hs0gen x hx g hg)
  set S₀ : Subgroup XJ := Subgroup.closure {g | g ∈ s0gen} with hS₀def
  have hS₀ : ∀ x, x ∈ S₀ ↔ x ∈ S0X := subgroupOfGens_exists s0gen S0X hsub0 hs01 hS0gen'
  have hS₀card : Nat.card ↥S₀ = 128 := by rw [card_of_list hS0nd hS₀, hs0len]
  have hS₀2 : IsPGroup 2 S₀ := by
    intro g
    exact ⟨3, Subtype.ext (hs0pow _ ((hS₀ _).1 g.2))⟩
  have hXcard : Nat.card XJ = 604800 := card_PC
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
  have hK₁ : ∀ x, x ∈ Subgroup.normalizer (canonZ S₀ : Set XJ) ↔ x ∈ K1X := by
    intro x
    constructor
    · intro hx
      have hxF : x • F1X = F1X := smul_fixSet_eq (canonZ S₀) A1X hA₁ hx
      have hcard : Nat.card ↥(↑(MulAction.stabilizer XJ F1X) : Set XJ) ≤ K1X.length := by
        have h := card_stab_mul_le hr1 (nodup_of_strictAsc maskF orb1.1 hr1sort)
        rw [hr1len, hXcard] at h
        rw [hK1len]
        exact arith_class _ h
      exact mem_list_of_card_le (↑(MulAction.stabilizer XJ F1X) : Set XJ) K1X hnodupK1
        (fun y hy => MulAction.mem_stabilizer_iff.2 (hK1fix y hy)) hcard x
        (MulAction.mem_stabilizer_iff.2 hxF)
    · intro h
      rw [mem_normalizer_of_lists (canonZ S₀) A1X hA₁ x]
      intro a ha
      have := hK1nrm x h a ha
      exact ⟨(mem_map_enc enc_injective).1 this.1, (mem_map_enc enc_injective).1 this.2⟩
  have hnodupK2 : K2X.Nodup := nodup_of_strictAsc enc K2X hK2sort
  have hgens₂ : ∀ a ∈ a2gen, a ∈ A2X := fun a ha => (mem_map_enc enc_injective).1 (ha2gen a ha)
  have hcl₂ : ∀ y ∈ A2X, y ∈ Subgroup.closure {x | x ∈ a2gen} := fun y hy =>
    closureListH_subset tabX tabX_eq hkey a2gen 40 y ((mem_map_enc enc_injective).1 (ha2cl y hy))
  have hnt := mem_normalizer_of_gens enc enc_injective (canonC2 S₀) A2X a2gen hA₂ hgens₂ hcl₂
  have hK₂ : ∀ x, x ∈ Subgroup.normalizer (canonC2 S₀ : Set XJ) ↔ x ∈ K2X := by
    intro x
    constructor
    · intro hx
      have hxF : x • F2X = F2X := smul_fixSet_eq (canonC2 S₀) A2X hA₂ hx
      have hcard : Nat.card ↥(↑(MulAction.stabilizer XJ F2X) : Set XJ) ≤ K2X.length := by
        have h := card_stab_mul_le hr2 (nodup_of_strictAsc maskF orb2.1 hr2sort)
        rw [hr2len, hXcard] at h
        rw [hK2len]
        exact arith_lines _ h
      exact mem_list_of_card_le (↑(MulAction.stabilizer XJ F2X) : Set XJ) K2X hnodupK2
        (fun y hy => MulAction.mem_stabilizer_iff.2 (hK2fix y hy)) hcard x
        (MulAction.mem_stabilizer_iff.2 hxF)
    · intro h
      exact (hnt x).2 (hK2nrm x h)
  have hgood₁ : GoodLocal (Subgroup.normalizer (canonZ S₀ : Set XJ)) :=
    goodLocal_of_gens_E enc enc_injective _ K1X hK₁ k1gen
      (fun x hx => closureListH_subset tabX tabX_eq hkey k1gen 40 x hx) Q1X
      (fun q hq => (mem_map_enc enc_injective).1 (hQ1K q hq)) hQ11 hQ1mul hQ1nrm hQ1pow hQ1cent
      hQ1E
  have hgood₂ : GoodLocal (Subgroup.normalizer (canonC2 S₀ : Set XJ)) := by
    refine goodLocal_of_gens enc enc_injective _ K2X hK₂ hnodupK2 k2gen
      (fun x hx => closureListH_subset tabX tabX_eq hkey k2gen 40 x hx) A2X
      (nodup_of_strictAsc enc A2X hQ2sort)
      (fun q hq => (mem_map_enc enc_injective).1 (hQ2K q hq)) hQ21 hQ2mul hQ2nrm hQ2pow hQ2cent
      hQ2A3 ?_
    rw [hQ2r]
    exact not_dvd_chi0_of_lt (by norm_num) (by norm_num)
  have hne₁ : Subgroup.normalizer (canonZ S₀ : Set XJ) ≠ ⊤ := by
    intro h
    have hc := card_of_list hnodupK1 hK₁
    rw [h, Subgroup.card_top, hXcard, hK1len] at hc
    exact absurd hc (by norm_num)
  have hne₂ : Subgroup.normalizer (canonC2 S₀ : Set XJ) ≠ ⊤ := by
    intro h
    have hc := card_of_list hnodupK2 hK₂
    rw [h, Subgroup.card_top, hXcard, hK2len] at hc
    exact absurd hc (by norm_num)
  have hsup : Subgroup.normalizer (canonZ S₀ : Set XJ) ⊔
      Subgroup.normalizer (canonC2 S₀ : Set XJ) = ⊤ := by
    set J' : Subgroup XJ := Subgroup.normalizer (canonZ S₀ : Set XJ) ⊔
      Subgroup.normalizer (canonC2 S₀ : Set XJ) with hJ'
    have hjg : ∀ g ∈ jLetters, g ∈ J' := by
      intro g hg
      have := List.all_eq_true.1 hgenmem g hg
      obtain ⟨x, hx, hxg⟩ := List.any_eq_true.1 this
      rw [beq_iff_eq] at hxg
      have hxg' : x = g := enc_injective hxg
      rw [← hxg']
      rcases List.mem_append.1 hx with h | h
      · exact Subgroup.mem_sup_left ((hK₁ x).2 h)
      · exact Subgroup.mem_sup_right ((hK₂ x).2 h)
    have hword : ∀ w : List ℤ, evalW jLetters w ∈ J' := evalW_mem J' jLetters hjg
    have hpa : paC ∈ J' := by
      rw [← hwA]
      exact hword wordA
    have hpb : pbC ∈ J' := by
      rw [← hwB]
      exact hword wordB
    have hcl : Subgroup.closure ({paC, pbC} : Set XJ) ≤ J' := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact hpa
      · exact hpb
    rw [closure_paC_pbC] at hcl
    exact top_le_iff.1 hcl
  refine ⟨S₀, _, _, hS₀2, hS₀i, ?_, ?_, hne₁, hne₂, hsup, hgood₁, hgood₂⟩
  · exact fun α hα => canonical_normalizer canonZ canonZ_map α hα
  · exact fun α hα => canonical_normalizer canonC2 canonC2_map α hα

end CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
