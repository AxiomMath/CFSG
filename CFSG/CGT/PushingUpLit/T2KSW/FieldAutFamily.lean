module

public import CFSG.CGT.PushingUpLit.T2KSW.WCover

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.ABGLocalTools CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

structure IsFamily (L T A : Subgroup G) : Prop where
  le_Dc : A ≤ Dc L T
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  normal : T ≤ Subgroup.normalizer (A : Set G)
  WE_le : oTwoIn L ⊔ Ec L T ≤ A

@[expose] def IsMaximalFamily (L T A : Subgroup G) : Prop :=
  IsFamily L T A ∧ ∀ A' : Subgroup G, IsFamily L T A' → A ≤ A' → A' = A

theorem Ec_comm_of_sec4 (hs : Sec4 G L M T n) {a b : G} (ha : a ∈ Ec L T) (hb : b ∈ Ec L T) :
    a * b = b * a :=
  congrArg Subtype.val (hs.S_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite G] in
theorem oTwoIn_Ec_comm {w e : G} (hw : w ∈ oTwoIn L) (he : e ∈ Ec L T) : w * e = e * w :=
  Subgroup.mem_centralizer_iff.1 he.2 w (oTwoIn_le L hw)

omit [Finite G] in
theorem sup_comm_of_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hn : A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 : a * b = b * a := hAB a ha b hb
      have : a * b * a⁻¹ = b := by rw [h1]; group
      rw [this]
      exact hb
    · intro hb
      have h1 : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := hAB a ha _ hb
      have h2 : a * b * a⁻¹ = b := by
        have : a * (a * b * a⁻¹) = a * b := by rw [h1]; group
        exact mul_left_cancel this
      rwa [h2] at hb
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hn).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_mul hn).1 hy
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hA a ha a' ha', hB b hb b' hb']
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
    _ = a' * b' * (a * b) := by group

theorem exists_mem_comm_mem {A C : Subgroup G} (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (hCT : C ≤ T) (hAn : T ≤ Subgroup.normalizer (A : Set G))
    (hCn : T ≤ Subgroup.normalizer (C : Set G)) (hCA : ¬ C ≤ A) :
    ∃ y ∈ C, y ∉ A ∧ ∀ t ∈ T, ⁅y, t⁆ ∈ A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAnorm : (A.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAT).2 hAn
  have hCnorm : (C.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).2 hCn
  let π : ↥T →* ↥T ⧸ A.subgroupOf T := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hq : IsPGroup 2 (↥T ⧸ A.subgroupOf T) := hT.of_surjective π hπs
  have : Group.IsNilpotent (↥T ⧸ A.subgroupOf T) := hq.isNilpotent
  set N : Subgroup (↥T ⧸ A.subgroupOf T) := (C.subgroupOf T).map π with hN
  have hNn : N.Normal := Subgroup.Normal.map hCnorm π hπs
  obtain ⟨y₀, hy₀C, hy₀A⟩ := Set.not_subset.1 hCA
  have hNne : N ≠ ⊥ := by
    intro hbot
    have h1 : π ⟨y₀, hCT hy₀C⟩ ∈ N := Subgroup.mem_map_of_mem _ hy₀C
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact hy₀A h1
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
  obtain ⟨hzN, hzZ⟩ := Subgroup.mem_inf.1 hzmem
  obtain ⟨y', hy'C, rfl⟩ := Subgroup.mem_map.1 hzN
  have hy'C' : (y' : G) ∈ C := hy'C
  refine ⟨y', hy'C', fun hyA => hz1 ?_, fun t ht => ?_⟩
  · apply Subtype.ext
    show π y' = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyA
  · have h1 := Subgroup.mem_center_iff.1 hzZ (π ⟨t, ht⟩)
    have h2 : π ⁅y', ⟨t, ht⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2

theorem isFamily_WE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    IsFamily L T (oTwoIn L ⊔ Ec L T) where
  le_Dc := sup_le (oTwoIn_le_Dc hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hs.sylow) Ec_le_Dc
  comm := sup_comm_of_comm (fun _ ha _ hb => oTwoIn_Ec_comm ha hb)
    (fun _ ha _ ha' => oTwoIn_comm hs.hyp.natBlock ha ha')
    (fun _ hb _ hb' => Ec_comm_of_sec4 hs hb hb')
  normal := fun _ ht => mem_normalizer_sup
    (normalizer_le_normalizer_oTwoIn L (hs.hyp.normal hE1 (hs.sylow.le ht)))
    (mem_normalizer_Ec (hs.hyp.normal hE1) (hs.sylow.le ht) (Subgroup.le_normalizer ht))
  WE_le := le_rfl

theorem exists_maximalFamily {A₀ : Subgroup G} (h₀ : IsFamily L T A₀) :
    ∃ A, IsMaximalFamily L T A ∧ A₀ ≤ A := by
  obtain ⟨A, ⟨hA, hA₀⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | IsFamily L T K ∧ A₀ ≤ K} (fun K => Nat.card K) (Set.toFinite _)
    ⟨A₀, h₀, le_rfl⟩
  refine ⟨A, ⟨hA, fun A' hA' hAA' => ?_⟩, hA₀⟩
  exact (Subgroup.eq_of_le_of_card_ge hAA' (hmax A' ⟨hA', hA₀.trans hAA'⟩)).symm

theorem exists_isMaximalFamily (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    ∃ A, IsMaximalFamily L T A :=
  (exists_maximalFamily (isFamily_WE hs hE1)).imp fun _ h => h.1

omit [Finite G] in
theorem blockU_le_family {A : Subgroup G} (hA : IsFamily L T A) : blockU L ≤ A :=
  (blockU_le_oTwoIn L).trans (le_sup_left.trans hA.WE_le)

omit [Finite G] in
theorem Ec_le_family {A : Subgroup G} (hA : IsFamily L T A) : Ec L T ≤ A :=
  le_sup_right.trans hA.WE_le

theorem family_Dc_inf_centralizer_eq (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) :
    Dc L T ⊓ Subgroup.centralizer (A : Set G) = A := by
  have hMN := hs.hyp.normal hE1
  have hAD := hA.1.le_Dc
  apply le_antisymm
  · by_contra hcon
    set C := Dc L T ⊓ Subgroup.centralizer (A : Set G) with hC
    have hCT : C ≤ T := inf_le_left.trans Dc_le_T
    have hAT : A ≤ T := hAD.trans Dc_le_T
    have hCn : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
      mem_normalizer_inf (mem_normalizer_Dc hMN (hs.sylow.le ht) (Subgroup.le_normalizer ht))
        (mem_normalizer_centralizer (hA.1.normal ht))
    obtain ⟨y, hyC, hyA, hyT⟩ :=
      exists_mem_comm_mem hs.sylow.isPGroup hAT hCT hA.1.normal hCn hcon
    have hyD : y ∈ Dc L T := hyC.1
    have hyZ : y ∈ Subgroup.centralizer (A : Set G) := hyC.2
    have hzp : Subgroup.zpowers y ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.zpowers_le.2 hyZ
    have hty : ∀ t ∈ T, t * y * t⁻¹ ∈ A ⊔ Subgroup.zpowers y := by
      intro t ht
      have h1 : ⁅y, t⁆ ∈ A := hyT t ht
      have h2 : ⁅t, y⁆ ∈ A := by
        rw [← commutatorElement_inv]
        exact A.inv_mem h1
      have e : t * y * t⁻¹ = ⁅t, y⁆ * y := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    have hmap : ∀ t ∈ T, ∀ z ∈ A ⊔ Subgroup.zpowers y, t * z * t⁻¹ ∈ A ⊔ Subgroup.zpowers y := by
      intro t ht z hz
      have hnA : A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := fun a ha => by
        rw [Subgroup.mem_normalizer_iff]
        intro b
        have hb : ∀ b ∈ Subgroup.zpowers y, a * b = b * a := fun b hb =>
          Subgroup.mem_centralizer_iff.1 (hzp hb) a ha
        constructor
        · intro hbm
          have : a * b * a⁻¹ = b := by rw [hb b hbm]; group
          rw [this]
          exact hbm
        · intro hbm
          have h1 : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := hb _ hbm
          have h2 : a * b * a⁻¹ = b := by
            have : a * (a * b * a⁻¹) = a * b := by rw [h1]; group
            exact mul_left_cancel this
          rwa [h2] at hbm
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hnA).1 hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have e : t * (a * y ^ k) * t⁻¹ = (t * a * t⁻¹) * (t * y * t⁻¹) ^ k := by
        rw [conj_zpow]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1
        (hA.1.normal ht) a).1 ha)) (zpow_mem (hty t ht) k)
    have hfam : IsFamily L T (A ⊔ Subgroup.zpowers y) :=
      { le_Dc := sup_le hAD (Subgroup.zpowers_le.2 hyD)
        comm := sup_comm_of_comm (fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hzp hb) a ha)
          hA.1.comm (fun b hb b' hb' => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
            obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
            exact (Commute.zpow_zpow_self y k l).eq)
        normal := fun t ht => by
          rw [Subgroup.mem_normalizer_iff]
          intro z
          refine ⟨hmap t ht z, fun hz => ?_⟩
          have := hmap t⁻¹ (T.inv_mem ht) _ hz
          simpa [mul_assoc] using this
        WE_le := hA.1.WE_le.trans le_sup_left }
    have hAA := hA.2 _ hfam le_sup_left
    exact hyA (hAA ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  · exact le_inf hAD (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb =>
      hA.1.comm b hb a ha)

theorem family_T_inf_centralizer_eq (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) :
    T ⊓ Subgroup.centralizer (A : Set G) = A := by
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    rw [← family_Dc_inf_centralizer_eq hs hE1 hA]
    exact ⟨⟨hxT, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (blockU_le_family hA.1))
      hxC⟩, hxC⟩
  · rw [← family_Dc_inf_centralizer_eq hs hE1 hA] at *
    exact fun a ha => ⟨Dc_le_T (hA.1.le_Dc ha), Subgroup.mem_centralizer_iff.2 fun b hb =>
      hA.1.comm b hb a ha⟩

theorem conj_mem_of_family (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsFamily L T A) {l a : G} (hl : l ∈ L) (ha : a ∈ A) : l * a * l⁻¹ ∈ A := by
  have hMN := hs.hyp.normal hE1
  have haD : a ∈ T ⊓ cenW L M := by
    rw [← Dc_eq_inf_cenW hs.hyp.natBlock hMN hs.sylow]
    exact hA.le_Dc ha
  have h1 : ⁅a, l⁆ ∈ oTwoIn L := ((mem_cenW_of_le hMN).1 haD.2).2 l hl
  have h2 : ⁅l, a⁆ ∈ A := by
    rw [← commutatorElement_inv]
    exact A.inv_mem (le_sup_left.trans hA.WE_le h1)
  have e : l * a * l⁻¹ = ⁅l, a⁆ * a := by simp only [commutatorElement_def]; group
  rw [e]
  exact A.mul_mem h2 ha

theorem family_le_normalizer (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsFamily L T A) : L ≤ Subgroup.normalizer (A : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_of_family hs hE1 hA hl ha, fun ha => ?_⟩
  have := conj_mem_of_family hs hE1 hA (L.inv_mem hl) ha
  simpa [mul_assoc] using this

theorem family_ne_bot (hs : Sec4 G L M T n) {A : Subgroup G} (hA : IsFamily L T A) : A ≠ ⊥ := by
  intro h
  apply hs.hyp.blockU_ne_bot
  rw [eq_bot_iff]
  exact (blockU_le_family hA).trans h.le

theorem family_isPGroup (hs : Sec4 G L M T n) {A : Subgroup G} (hA : IsFamily L T A) :
    IsPGroup 2 A := hs.sylow.isPGroup.to_le (hA.le_Dc.trans Dc_le_T)

theorem family_normalizer_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsFamily L T A) : Subgroup.normalizer (A : Set G) ≤ M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (A : Set G)) :=
    ⟨A, family_ne_bot hs hA, family_isPGroup hs hA, rfl⟩
  obtain ⟨N, hAN, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) :=
      ⟨hNmax, fun l hl => hAN (family_le_normalizer hs hE1 hA hl)⟩
    rw [hs.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hAN

theorem family_centralizer_le_M (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsFamily L T A) : Subgroup.centralizer (A : Set G) ≤ M := by
  intro x hx
  have h1 : x ∈ Subgroup.centralizer (blockU L : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (blockU_le_family hA)) hx
  have h2 := Subgroup.centralizer_le_normalizer (blockU L : Set G) h1
  rwa [hs.hyp.normalizer_blockU_eq hE1] at h2

theorem family_isSylowOf_centralizer (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) :
    CFSG.ABGLocalTools.IsSylowOf 2 A (Subgroup.centralizer (A : Set G)) := by
  set K : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G) with hK
  have hTK : T ≤ K := fun t ht => ⟨hs.sylow.le ht, hA.1.normal ht⟩
  have hTK' : CFSG.ABGLocalTools.IsSylowOf 2 T K := hs.sylow.of_le hTK inf_le_left
  have hNK : Subgroup.centralizer (A : Set G) ≤ K := fun x hx =>
    ⟨family_centralizer_le_M hs hE1 hA.1 hx, Subgroup.centralizer_le_normalizer _ hx⟩
  have hKN : K ≤ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := fun k hk =>
    mem_normalizer_centralizer hk.2
  have := hTK'.inf_of_le_normalizer hNK hKN
  rwa [family_T_inf_centralizer_eq hs hE1 hA] at this

theorem family_sq_mem_Ec (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsFamily L T A) {a : G} (ha : a ∈ A) : a ^ 2 ∈ Ec L T :=
  Dc_sq_mem_Ec hs.hyp.natBlock (hs.hyp.normal hE1) hs.sylow (hA.le_Dc ha)

theorem family_pow_four_eq_one (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsFamily L T A) {a : G} (ha : a ∈ A) : a ^ 4 = 1 := by
  have h := hs.S_elem.2 (a ^ 2) (family_sq_mem_Ec hs hE1 hA ha)
  rw [← pow_mul] at h
  exact h

theorem blockU_inf_Ec (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    blockU L ⊓ Ec L T = blockZ L := by
  apply le_antisymm
  · rintro x ⟨hxV, hxE⟩
    exact ⟨hxV, hxE.2⟩
  · intro x hx
    exact ⟨blockZ_le_blockU L hx, NatBlock.blockU_le_sylow hs.hyp.le (hs.hyp.normal hE1) hs.sylow
      (blockZ_le_blockU L hx), NatBlock.blockZ_le_centralizer L hx⟩

theorem card_sup_blockU_Ec (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    Nat.card ↥(blockU L ⊔ Ec L T) = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    (NatBlock.blockU_le_sylow hs.hyp.le (hs.hyp.normal hE1) hs.sylow).trans
      (le_normalizer_Ec (hs.hyp.normal hE1) hs.sylow.le)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hVn
  have h2 := hs.hyp.natBlock.card_blockU
  rw [inf_comm, blockU_inf_Ec hs hE1, sup_comm] at h1
  have hpos : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h2]
  ring

theorem family_card_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {A : Subgroup G}
    (hA : IsFamily L T A) : (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) ≤ Nat.card ↥A := by
  rw [← card_sup_blockU_Ec hs hE1]
  exact Subgroup.card_le_of_le (sup_le (blockU_le_family hA) (Ec_le_family hA))

theorem family_eq_sup_of_card_eq (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsFamily L T A) (h : Nat.card ↥A = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) :
    A = blockU L ⊔ Ec L T := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le (blockU_le_family hA) (Ec_le_family hA)) ?_
  rw [h, card_sup_blockU_Ec hs hE1]

end CFSG.CGT.PushingUpLit.T2KSW
