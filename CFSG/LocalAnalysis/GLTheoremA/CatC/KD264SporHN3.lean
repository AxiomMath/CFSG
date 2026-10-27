module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264HN3Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426SporKleinU
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.HN
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Parts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426SporCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open Equiv CFSG.Sporadic.HNSchreier CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven

theorem centralizer_sup_zpowers {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union, SetLike.mem_coe,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun y hy => hy ▸ h a (Or.inl (Subgroup.mem_zpowers a)),
      fun y hy => hy ▸ h b (Or.inr (Subgroup.mem_zpowers b))⟩
  · rintro ⟨h1, h2⟩ y (hy | hy)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.zpow_left (h1 a rfl) k)).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.zpow_left (h2 b rfl) k)).eq

theorem map_conj_centralizer_sub {G : Type*} [Group G] (g : G) (S : Subgroup G) :
    (Subgroup.centralizer (S : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨s, hs, rfl⟩
    calc g * s * g⁻¹ * (g * y * g⁻¹) = g * (s * y) * g⁻¹ := by group
      _ = g * (y * s) * g⁻¹ := by rw [hy s hs]
      _ = g * y * g⁻¹ * (g * s * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, fun s hs => ?_, by group⟩
    have e := hx (g * s * g⁻¹) ⟨s, hs, rfl⟩
    calc s * (g⁻¹ * x * g) = g⁻¹ * ((g * s * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [e]
      _ = g⁻¹ * x * g * s := by group

section Generic

variable {G : Type} [Group G] [Finite G] {X : Type} [Fintype X] [DecidableEq X] [MulAction G X]
  (ι : alternatingGroup (Fin 12) →* G) (hι : Function.Injective ι) {s1 s3 : G}

include hι in
theorem exists_conj_s1_gen (hcls : ∀ x : G, orderOf x = 3 → IsConj s1 x ∨ IsConj s3 x)
    (hX : Fintype.card X = 1140000)
    (hfix3 : (Finset.univ.filter fun x : X => s3 • x = x).card = 60)
    {A : Subgroup G} (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A) :
    ∃ x ∈ A, IsConj s1 x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  by_contra h
  push Not at h
  have hf : ∀ a ∈ A, a ≠ 1 → Nat.card (MulAction.fixedBy X a) = 60 := by
    intro a ha ha1
    have ho : orderOf a = 3 := orderOf_eq_prime (hA.2 a ha) ha1
    rcases hcls a ho with hc | hc
    · exact absurd hc (h a ha)
    · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [nat_card_fixedBy, card_filter_conj, hfix3]
  have hd := sum_fixed_dvd A hn hf
  rw [hX] at hd
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    omega
  have h81 : 81 ∣ 3 ^ n := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.pow_dvd_pow 3 hn4
  obtain ⟨t, ht⟩ := h81
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht; exact absurd ht (by positivity)
    · exact h0
  rw [ht] at hd
  have hd81 : 81 ∣ 1140000 + (81 * t - 1) * 60 := (Dvd.intro t rfl).trans hd
  have e : 1140000 + (81 * t - 1) * 60 = 1139940 + 81 * (60 * t) := by
    have : 81 * t - 1 + 1 = 81 * t := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [e, add_comm] at hd81
  have := (Nat.dvd_add_right (Dvd.intro (60 * t) rfl)).1 hd81
  exact absurd this (by norm_num)

include hι in
theorem glaPComponent_alt3_gen (hC : Subgroup.centralizer ({s1} : Set G) =
      Subgroup.zpowers s1 ⊔ alt3.map ι)
    (hcomm : ∀ x ∈ alt3.map ι, x * s1 = s1 * x) :
    GLAPComponent 3 (Subgroup.centralizer ({s1} : Set G)) (alt3.map ι) := by
  set L := alt3.map ι with hL
  have hle : L ≤ Subgroup.centralizer ({s1} : Set G) := by rw [hC]; exact le_sup_right
  haveI hs3 : IsSimpleGroup alt3 := alt3_simple
  haveI hsL : IsSimpleGroup ↥L :=
    @MulEquiv.isSimpleGroup _ _ _ _ hs3 (alt3.equivMapOfInjective ι hι).symm
  have hcardL : Nat.card L = 181440 := by
    rw [hL, Subgroup.card_map_of_injective hι, card_alt3]
  have hpL : ¬ (Nat.card ↥L).Prime := by rw [hcardL]; norm_num
  have hnc : ∃ a b : ↥L, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥L) hpL
  have hperf : commutator ↥L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  have hq : CFSG.Open.IsQuasisimple ↥L := Seven.isQuasisimple_of_simple hperf hnc
  refine CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hq
    (by rw [hcardL]; norm_num) hle ?_
  have hN : Subgroup.centralizer ({s1} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [hC]
    refine sup_le (Subgroup.zpowers_le.2 ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e := hcomm h hh
      have : s1 * h * s1⁻¹ = h := by
        calc s1 * h * s1⁻¹ = (h * s1) * s1⁻¹ := by rw [e]
          _ = h := by group
      rw [this]; exact hh
    · intro hh
      have e := hcomm _ hh
      have : h = s1 * h * s1⁻¹ := by
        calc h = s1⁻¹ * ((s1 * h * s1⁻¹) * s1) := by group
          _ = s1⁻¹ * (s1 * (s1 * h * s1⁻¹)) := by rw [e]
          _ = s1 * h * s1⁻¹ := by group
      rw [this]; exact hh
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hN

include hι in
theorem exists_F9_gen (hCs : Subgroup.centralizer ({s1} : Set G) =
      (Subgroup.centralizer {tri012A}).map ι) (hιs : ι tri012A = s1)
    {A : Subgroup G} (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A)
    (hAC : A ≤ Subgroup.centralizer ({s1} : Set G)) (hs : s1 ∈ A) :
    ∃ F : Subgroup G, F ≤ A ∧ Nat.card F = 3 ^ 2 ∧ ∃ J0 : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer (F : Set G)) J0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange : A ≤ ι.range := by
    intro a ha
    have := hAC ha
    rw [hCs] at this
    obtain ⟨b, -, rfl⟩ := this
    exact ⟨b, rfl⟩
  set A2 : Subgroup (alternatingGroup (Fin 12)) := A.comap ι with hA2
  have hA2map : A2.map ι = A := Subgroup.map_comap_eq_self hrange
  have hA2card : Nat.card A2 = Nat.card A := by
    rw [← hA2map, Subgroup.card_map_of_injective hι]
  have hA2el : IsElemAbelian 3 A2 := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hι ?_)⟩⟩, fun a ha => hι ?_⟩
    · have := congrArg Subtype.val (hA.1.is_comm.comm ⟨ι a, a.2⟩ ⟨ι b, b.2⟩)
      simpa using this
    · rw [map_pow, hA.2 _ ha, map_one]
  have hA2C : A2 ≤ Subgroup.centralizer {tri012A} := by
    intro a ha
    have := hAC ha
    rw [hCs] at this
    obtain ⟨b, hb, hba⟩ := this
    rwa [← hι hba]
  obtain ⟨σ, hσA2, hσ1, hσt, hσt2, K, hK⟩ :=
    exists_comp_of_elemAbelian hA2el hA2C (hA2card ▸ h81)
  set y := ι σ with hy
  have hyA : y ∈ A := hσA2
  have hs3 : s1 ^ 3 = 1 := hA.2 _ hs
  have hs1 : s1 ≠ 1 := by
    rw [← hιs, ← map_one ι]
    intro h
    have h2 := congrArg (fun z : alternatingGroup (Fin 12) => (z : Perm (Fin 12)) 0) (hι h)
    simp only [tri012A_val, tri012_apply0, Subgroup.coe_one, Perm.one_apply] at h2
    exact absurd h2 (by decide)
  have hyt : y ≠ s1 := by
    rw [← hιs]; exact fun h => hσt (hι h)
  have hyt2 : y ≠ s1 ^ 2 := by
    rw [← hιs, ← map_pow]; exact fun h => hσt2 (hι h)
  have hy1 : y ≠ 1 := by
    rw [← map_one ι]; exact fun h => hσ1 (hι h)
  have hcomm : s1 * y = y * s1 :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨s1, hs⟩ ⟨y, hyA⟩)
  refine ⟨Subgroup.zpowers s1 ⊔ Subgroup.zpowers y,
    sup_le (Subgroup.zpowers_le.2 hs) (Subgroup.zpowers_le.2 hyA), ?_, K.map ι, ?_⟩
  · rw [CFSG.LocalAnalysis.GLTheoremA.KD1426SporKlein.card_sup_zpowers hs3 hs1 (hA.2 y hyA)
      hy1 hyt hyt2 hcomm]
    norm_num
  rw [centralizer_sup_zpowers]
  have heq : (Subgroup.centralizer {tri012A} ⊓ Subgroup.centralizer {σ}).map ι =
      Subgroup.centralizer ({s1} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hιs, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 hg1]
      · rw [Subgroup.mem_centralizer_singleton_iff, hy, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 hg2]
    · intro g hg
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
      rw [hCs] at hg1
      obtain ⟨h, hh, rfl⟩ := hg1
      refine ⟨h, Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      apply hι
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hg2
  rw [← heq]
  exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map Nat.prime_three ι
    (by rw [(MonoidHom.ker_eq_bot_iff ι).2 hι, inf_bot_eq, Subgroup.card_bot];
        exact Nat.coprime_one_right 3) hK

include hι in
theorem kd264RowData_gen (hcls : ∀ x : G, orderOf x = 3 → IsConj s1 x ∨ IsConj s3 x)
    (hX : Fintype.card X = 1140000)
    (hfix3 : (Finset.univ.filter fun x : X => s3 • x = x).card = 60)
    (hC : Subgroup.centralizer ({s1} : Set G) = Subgroup.zpowers s1 ⊔ alt3.map ι)
    (hcomm : ∀ x ∈ alt3.map ι, x * s1 = s1 * x)
    (hCs : Subgroup.centralizer ({s1} : Set G) = (Subgroup.centralizer {tri012A}).map ι)
    (hιs : ι tri012A = s1) (ho1 : orderOf s1 = 3) : KD264RowData 3 G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro A hA hmax k hk1 hk2 hpk
  have hS81 : IsElemAbelian 3 ((Subgroup.closure (Set.range blockA)).map ι) :=
    isElemAbelian_blocks.map ι
  have hc81 : 81 ≤ Nat.card ((Subgroup.closure (Set.range blockA)).map ι) := by
    rw [Subgroup.card_map_of_injective hι]; exact card_blocks
  have h81 : 81 ≤ Nat.card A := hc81.trans (hmax _ hS81)
  obtain ⟨x, hxA, hxc⟩ := exists_conj_s1_gen ι hι hcls hX hfix3 hA h81
  obtain ⟨c, hc⟩ := isConj_iff.1 hxc
  interval_cases k
  · refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.2 hxA, ?_,
      (alt3.map ι).map (MulAut.conj c).toMonoidHom, ?_⟩
    · rw [Nat.card_zpowers, ← hc, show c * s1 * c⁻¹ = MulAut.conj c s1 from rfl,
        MulEquiv.orderOf_eq, ho1, pow_one]
    · rw [Seven.centralizer_zpowers_eq, ← hc, ← map_conj_centralizer]
      exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three
        (MulAut.conj c) (glaPComponent_alt3_gen ι hι hC hcomm)
  · set A' := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'
    have hA'el : IsElemAbelian 3 A' := hA.map _
    have hA'card : Nat.card A' = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    have hs : s1 ∈ A' := ⟨x, hxA, by
      show c⁻¹ * x * c⁻¹⁻¹ = s1
      rw [← hc]; group⟩
    have hA'C : A' ≤ Subgroup.centralizer ({s1} : Set G) := by
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (hA'el.1.is_comm.comm ⟨a, ha⟩ ⟨s1, hs⟩))
    obtain ⟨F', hF'A, hF'c, J', hJ'⟩ :=
      exists_F9_gen ι hι hCs hιs hA'el (hA'card ▸ h81) hA'C hs
    refine ⟨F'.map (MulAut.conj c).toMonoidHom, ?_, ?_, J'.map (MulAut.conj c).toMonoidHom, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := ha
      obtain ⟨d, hd, rfl⟩ := hF'A hb
      show c * (c⁻¹ * d * c⁻¹⁻¹) * c⁻¹ ∈ A
      have : c * (c⁻¹ * d * c⁻¹⁻¹) * c⁻¹ = d := by group
      rw [this]; exact hd
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hF'c]
    · rw [← map_conj_centralizer_sub]
      exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three
        (MulAut.conj c) hJ'

end Generic

section HN


set_option maxRecDepth 100000 in
theorem kd264RowData_HN_three : KD264RowData 3 ↥JH := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  obtain ⟨hC, -, hcomm⟩ := CJ_s1_structure
  have hX : Fintype.card X = 1140000 := by rw [Fintype.card_fin]; rfl
  exact kd264RowData_gen (X := X) iotaA iotaA_injective (s3 := sJ 2)
    (fun x hx => (order_three_classes x).1 hx) hX fix_s3_card hC hcomm CJ_s1_eq iotaA_tri012
    (orderOf_sJ (by norm_num))

end HN

section Rows


set_option maxRecDepth 100000 in
theorem kd264SporAt_HN_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 3 .HN := by
  haveI hHN : IsSimpleGroup NativeSporadic.HN := CFSG.Sporadic.HN.isSimpleGroup_HN
  haveI : IsSimpleGroup ↥JH := @MulEquiv.isSimpleGroup _ _ _ _ hHN hnEquivJ.symm
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥JH).Prime := by rw [card_JH]; norm_num
  have hnc : ∃ x y : ↥JH, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥JH) hp
  have hb : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := hnEquivJ.symm.trans e
  have hrd : KD264RowData 3 ↥JH := kd264RowData_HN_three
  refine kd264SporAt_of_model (p := 3) (s := .HN) (Q := ↥JH) hOut Nat.prime_three (by decide) ?_
    ?_ ?_
  · exact hnc
  · exact hb
  · intro _ _ _
    exact hrd

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3
