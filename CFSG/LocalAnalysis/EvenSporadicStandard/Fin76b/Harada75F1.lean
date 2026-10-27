module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

@[expose] def phi {S : Type} [Group S] (U : Subgroup S) : Subgroup S := (frattini U).map U.subtype

theorem comm_mem_phi {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {U : Subgroup S} {x y : S}
    (hx : x ∈ U) (hy : y ∈ U) : x * y * x⁻¹ * y⁻¹ ∈ phi U :=
  Subgroup.mem_map_of_mem U.subtype (comm_mem_frattini (hS.to_subgroup U) ⟨x, hx⟩ ⟨y, hy⟩)

theorem sq_mem_phi {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {U : Subgroup S} {x : S}
    (hx : x ∈ U) : x ^ 2 ∈ phi U := by
  have hsq : (⟨x, hx⟩ : U) ^ 2 ∈ frattini U :=
    mem_frattini_of_forall fun _ hM => (coatom_props (hS.to_subgroup U) hM).1 ⟨x, hx⟩
  exact Subgroup.mem_map_of_mem U.subtype hsq

theorem card_phi {S : Type} [Group S] (U : Subgroup S) :
    Nat.card (phi U) = Nat.card (frattini U) :=
  Subgroup.card_map_of_injective U.subtype_injective

theorem rank_le_of_card_le_mul_phi {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (U : Subgroup S) (m : ℕ) (h : Nat.card U ≤ 2 ^ m * Nat.card (phi U)) : Group.rank U ≤ m := by
  rw [card_phi] at h
  exact rank_le_of_card_le_mul_frattini (hS.to_subgroup U) m h

theorem genLE4_of_rank_le_four {S : Type} [Group S] [Finite S]
    (h : ∀ U : Subgroup S, Group.rank U ≤ 4) : GenLE4 S := by
  intro U
  obtain ⟨Y, hYcard, hYcl⟩ := Group.rank_spec ↥U
  refine ⟨Y.map (Function.Embedding.subtype (fun x : S => x ∈ U)), ?_, ?_⟩
  · rw [Finset.card_map, hYcard]
    exact h U
  · rw [Finset.coe_map]
    calc Subgroup.closure ((Function.Embedding.subtype (fun x : S => x ∈ U)) '' (Y : Set U))
        = Subgroup.closure (U.subtype '' (Y : Set U)) := rfl
      _ = Subgroup.map U.subtype (Subgroup.closure (Y : Set U)) :=
          (MonoidHom.map_closure _ _).symm
      _ = Subgroup.map U.subtype ⊤ := by rw [hYcl]
      _ = U := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_gen_mod_normal {N : Type} [Group N] [Finite N] (hN : IsPGroup 2 N) (K : Subgroup N)
    [K.Normal] {k : ℕ} (hcard : Nat.card N ≤ 2 ^ k * Nat.card K) :
    ∃ Y : Finset N, Y.card ≤ k ∧ ∀ n : N, ∃ y ∈ Subgroup.closure (Y : Set N), y⁻¹ * n ∈ K := by
  classical
  have hP : IsPGroup 2 (N ⧸ K) := hN.to_quotient K
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hidx : Nat.card (N ⧸ K) * Nat.card K = Nat.card N := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_mul_card K
  have hcardP : Nat.card (N ⧸ K) ≤ 2 ^ k := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    rw [hidx]
    exact hcard
  have hrank : Group.rank (N ⧸ K) ≤ k := rank_le_of_card_le_two_pow k _ hP hcardP
  obtain ⟨Z, hZcard, hZcl⟩ := Group.rank_spec (N ⧸ K)
  set f : N ⧸ K → N := Function.surjInv (QuotientGroup.mk_surjective (s := K)) with hf_def
  have hf : ∀ p : N ⧸ K, ((f p : N) : N ⧸ K) = p := fun p => Function.surjInv_eq _ p
  set Y : Finset N := Z.image f with hY_def
  refine ⟨Y, (Finset.card_image_le (s := Z) (f := f)).trans (hZcard.le.trans hrank), ?_⟩
  have himage : (QuotientGroup.mk' K) '' (Y : Set N) = (Z : Set (N ⧸ K)) := by
    rw [hY_def, Finset.coe_image, Set.image_image]
    simp [hf]
  have hmap : Subgroup.map (QuotientGroup.mk' K) (Subgroup.closure (Y : Set N)) = ⊤ := by
    rw [MonoidHom.map_closure, himage, hZcl]
  intro n
  have hg : (n : N ⧸ K) ∈ Subgroup.map (QuotientGroup.mk' K) (Subgroup.closure (Y : Set N)) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp hg
  rw [QuotientGroup.mk'_apply] at hyn
  exact ⟨y, hy, QuotientGroup.eq.mp hyn⟩

theorem rank_le_add_of_frattini_aux {G Q : Type} [Group G] [Finite G] [Group Q] (hG : IsPGroup 2 G)
    (π : G →* Q) (M : Subgroup G) {m k : ℕ} (hm : Group.rank π.range ≤ m)
    (hM : M ≤ π.ker ⊓ frattini G) (hk : Nat.card π.ker ≤ 2 ^ k * Nat.card M) :
    Group.rank G ≤ m + k := by
  classical
  obtain ⟨Y₁, hY₁card, hY₁cl⟩ := Group.rank_spec π.range
  set f1 : π.range → G := Function.surjInv (MonoidHom.rangeRestrict_surjective π) with hf1_def
  have hf1 : ∀ r : π.range, π.rangeRestrict (f1 r) = r := fun r => Function.surjInv_eq _ r
  set X₀ : Finset G := Y₁.image f1 with hX₀_def
  have hX₀card : X₀.card ≤ m :=
    (Finset.card_image_le (s := Y₁) (f := f1)).trans (hY₁card.le.trans hm)
  have hX₀img : π.rangeRestrict '' (X₀ : Set G) = (Y₁ : Set π.range) := by
    rw [hX₀_def, Finset.coe_image, Set.image_image]
    simp [hf1]
  have hmapX₀ : Subgroup.map π.rangeRestrict (Subgroup.closure (X₀ : Set G)) = ⊤ := by
    rw [MonoidHom.map_closure, hX₀img, hY₁cl]
  have hX₀cov : ∀ g : G, ∃ x ∈ Subgroup.closure (X₀ : Set G), x⁻¹ * g ∈ π.ker := by
    intro g
    have hg : π.rangeRestrict g ∈
        Subgroup.map π.rangeRestrict (Subgroup.closure (X₀ : Set G)) := by
      rw [hmapX₀]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
    have hπ : π x = π g := congrArg Subtype.val hxg
    refine ⟨x, hx, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, hπ, inv_mul_cancel]
  have : (frattini G).Normal := inferInstance
  have hMker : M ≤ π.ker := hM.trans inf_le_left
  have hMΦ : M ≤ frattini G := hM.trans inf_le_right
  have hMcard : Nat.card M ≤ Nat.card ((frattini G).subgroupOf π.ker) := by
    have e : Nat.card (M.subgroupOf π.ker) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMker).toEquiv
    rw [← e]
    exact Subgroup.card_le_of_le (Subgroup.subgroupOf_mono π.ker hMΦ)
  have hkK : Nat.card π.ker ≤ 2 ^ k * Nat.card ((frattini G).subgroupOf π.ker) :=
    hk.trans (Nat.mul_le_mul_left _ hMcard)
  obtain ⟨Y₂, hY₂card, hY₂cov⟩ := exists_gen_mod_normal (hG.to_subgroup π.ker)
    ((frattini G).subgroupOf π.ker) hkK
  set Y₂' : Finset G := Y₂.image Subtype.val with hY₂'_def
  have hY₂'card : Y₂'.card ≤ k :=
    (Finset.card_image_le (s := Y₂) (f := Subtype.val)).trans hY₂card
  have hY₂'cov : ∀ g ∈ π.ker, ∃ y ∈ Subgroup.closure (Y₂' : Set G), y⁻¹ * g ∈ frattini G := by
    intro g hg
    obtain ⟨y, hy, hyg⟩ := hY₂cov ⟨g, hg⟩
    refine ⟨(y : G), ?_, ?_⟩
    · have hmem : (y : G) ∈ Subgroup.map π.ker.subtype (Subgroup.closure (Y₂ : Set π.ker)) :=
        Subgroup.mem_map_of_mem _ hy
      rw [MonoidHom.map_closure] at hmem
      have himg : π.ker.subtype '' (Y₂ : Set π.ker) = (Y₂' : Set G) := by
        rw [hY₂'_def, Finset.coe_image]
        rfl
      rwa [himg] at hmem
    · have h2 : (y : G)⁻¹ * g ∈ frattini G := hyg
      exact h2
  have hall : Subgroup.closure ((X₀ ∪ Y₂' : Finset G) : Set G) ⊔ frattini G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx, hxg⟩ := hX₀cov g
    obtain ⟨y, hy, hyg⟩ := hY₂'cov (x⁻¹ * g) hxg
    have hx' : x ∈ Subgroup.closure ((X₀ ∪ Y₂' : Finset G) : Set G) :=
      Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_left) hx
    have hy' : y ∈ Subgroup.closure ((X₀ ∪ Y₂' : Finset G) : Set G) :=
      Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_right) hy
    have hg : g = (x * y) * (y⁻¹ * (x⁻¹ * g)) := by group
    rw [hg]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hx' hy')) (Subgroup.mem_sup_right hyg)
  have hgen : Subgroup.closure ((X₀ ∪ Y₂' : Finset G) : Set G) = ⊤ :=
    frattini_nongenerating hall
  calc Group.rank G ≤ (X₀ ∪ Y₂').card := Group.rank_le hgen
    _ ≤ X₀.card + Y₂'.card := Finset.card_union_le _ _
    _ ≤ m + k := Nat.add_le_add hX₀card hY₂'card

theorem rank_le_add_of_frattini {S Q : Type} [Group S] [Finite S] [Group Q] (hS : IsPGroup 2 S)
    (π : S →* Q) (U M : Subgroup S) {m k : ℕ} (hm : Group.rank (U.map π) ≤ m)
    (hM : M ≤ U ⊓ π.ker) (hMphi : M ≤ phi U)
    (hk : Nat.card (U ⊓ π.ker : Subgroup S) ≤ 2 ^ k * Nat.card M) : Group.rank U ≤ m + k := by
  classical
  have hMU : M ≤ U := hM.trans inf_le_left
  have hrange : (π.comp U.subtype).range = U.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hm' : Group.rank (π.comp U.subtype).range ≤ m :=
    (Subgroup.rank_congr hrange).le.trans hm
  have hker : (π.comp U.subtype).ker = (U ⊓ π.ker).subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card (π.comp U.subtype).ker = Nat.card (U ⊓ π.ker : Subgroup S) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ π.ker ≤ U)).toEquiv
  have hcardM : Nat.card (M.subgroupOf U) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMU).toEquiv
  have hM' : M.subgroupOf U ≤ (π.comp U.subtype).ker ⊓ frattini U := by
    intro x hx
    have hxM : (x : S) ∈ M := hx
    have hxφ : (x : S) ∈ (frattini U).map U.subtype := hMphi hxM
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxφ
    have hyx' : y = x := Subtype.ext hyx
    have hxker : (x : S) ∈ π.ker := (Subgroup.mem_inf.mp (hM hxM)).2
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hxker)
    · rw [← hyx']
      exact hy
  exact rank_le_add_of_frattini_aux (hS.to_subgroup U) (π.comp U.subtype) (M.subgroupOf U) hm'
    hM' (by rw [hcardker, hcardM]; exact hk)

end CFSG.EvenSporadicStandard.Fin76b
