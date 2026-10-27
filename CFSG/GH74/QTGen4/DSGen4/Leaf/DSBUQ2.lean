module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex
public import CFSG.GH74.E2.Cl2Rank
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniFaithful
public import CFSG.GH74.QTGen4.DSGen4.Leaf.RankBounds

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBUQ2

variable {G : Type} [Group G]

theorem comm_mem_of_index_two {H : Subgroup G} (h : H.index = 2) (x y : G) : ⁅x, y⁆ ∈ H := by
  have hn : H.Normal := Subgroup.normal_of_index_eq_two h
  have h1 : x * y * x⁻¹ ∈ H ↔ y ∈ H := by
    constructor
    · intro hm
      have h2 := hn.conj_mem _ hm x⁻¹
      have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [e] at h2
      exact h2
    · intro hy
      exact hn.conj_mem _ hy x
  have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
  rw [e, Subgroup.mul_mem_iff_of_index_two h, h1, Subgroup.inv_mem_iff]

theorem comm_mem_of_relIndex_two {S H : Subgroup G} (h : H.relIndex S = 2) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) : ⁅x, y⁆ ∈ H := by
  have h' : (H.subgroupOf S).index = 2 := h
  have h2 := comm_mem_of_index_two h' (⟨x, hx⟩ : S) ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf] at h2
  have e : ((⁅(⟨x, hx⟩ : S), (⟨y, hy⟩ : S)⁆ : S) : G) = ⁅x, y⁆ :=
    map_commutatorElement S.subtype _ _
  rw [e] at h2
  exact h2

theorem not_three_distinct {Φ : Subgroup G} (hΦ : Nat.card Φ = 2) {a b c : G} (ha : a ∈ Φ)
    (hb : b ∈ Φ) (hc : c ∈ Φ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  obtain ⟨u, v, -, huniv⟩ := Nat.card_eq_two_iff.mp hΦ
  have key : ∀ z : Φ, z = u ∨ z = v := by
    intro z
    have hz : z ∈ ({u, v} : Set Φ) := by
      rw [huniv]
      exact Set.mem_univ z
    simpa using hz
  have ha' := key ⟨a, ha⟩
  have hb' := key ⟨b, hb⟩
  have hc' := key ⟨c, hc⟩
  have hab' : (⟨a, ha⟩ : Φ) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have hac' : (⟨a, ha⟩ : Φ) ≠ ⟨c, hc⟩ := fun h => hac (congrArg Subtype.val h)
  have hbc' : (⟨b, hb⟩ : Φ) ≠ ⟨c, hc⟩ := fun h => hbc (congrArg Subtype.val h)
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rcases hc' with h3 | h3
  all_goals first
    | exact hab' (h1.trans h2.symm)
    | exact hac' (h1.trans h3.symm)
    | exact hbc' (h2.trans h3.symm)

theorem sq_eq_one_of_card_two {Φ : Subgroup G} (hΦ : Nat.card Φ = 2) {x : G} (hx : x ∈ Φ) :
    x ^ 2 = 1 := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : Φ)
  rw [hΦ, ← Subgroup.orderOf_coe] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem mem_center_of_card_two {Φ : Subgroup G} (hΦ : Nat.card Φ = 2) {P : Subgroup G}
    (hP : P ≤ Subgroup.normalizer (Φ : Set G)) {x g : G} (hx : x ∈ Φ) (hg : g ∈ P) :
    g * x = x * g := by
  have hy : g * x * g⁻¹ ∈ Φ := (Subgroup.mem_normalizer_iff.mp (hP hg) x).mp hx
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
    rw [h] at e
    simpa using e
  by_cases hxy : g * x * g⁻¹ = x
  · calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hxy]
  · exfalso
    exact not_three_distinct hΦ (Subgroup.one_mem Φ) hx hy (Ne.symm hx1) (Ne.symm hy1)
      (fun h => hxy h.symm)

theorem normalizer_inf_centralizer {Z S : Subgroup G} {g : G}
    (hZ : g ∈ Subgroup.normalizer (Z : Set G)) (hS : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer ((Z ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ Subgroup.normalizer (Z : Set G) →
      g' ∈ Subgroup.normalizer (S : Set G) → ∀ x ∈ Z ⊓ Subgroup.centralizer (S : Set G),
        g' * x * g'⁻¹ ∈ Z ⊓ Subgroup.centralizer (S : Set G) := by
    intro g' hZ' hS' x hx
    obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hZ' x).mp hxZ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro s hs
    have hs' : g'⁻¹ * s * g' ∈ S := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hS') s).mp hs
      rwa [inv_inv] at h1
    have hc := hxC _ hs'
    calc s * (g' * x * g'⁻¹) = g' * ((g'⁻¹ * s * g') * x) * g'⁻¹ := by group
      _ = g' * (x * (g'⁻¹ * s * g')) * g'⁻¹ := by rw [hc]
      _ = (g' * x * g'⁻¹) * s := by group
  refine Subgroup.mem_normalizer_iff.mpr (fun x => ⟨key g hZ hS x, fun hx => ?_⟩)
  have h := key g⁻¹ (Subgroup.inv_mem _ hZ) (Subgroup.inv_mem _ hS) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  have ha := Subgroup.mem_normalizer_iff.mp (hA hg)
  have hb := Subgroup.mem_normalizer_iff.mp (hB hg)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ha x, hb x]

theorem comm_mem_of_normal {Q L : Subgroup G} (hQL : L ≤ Subgroup.normalizer (Q : Set G))
    {z s : G} (hz : z ∈ Q) (hs : s ∈ L) : ⁅z, s⁆ ∈ Q := by
  have h1 : s * z * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQL hs) z).mp hz
  have e : ⁅z, s⁆ = z * (s * z * s⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem hz (Q.inv_mem h1)

theorem comm_mem_dsFrattini [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ dsFrattini Q := by
  have h1 : (⁅(⟨x, hx⟩ : Q), (⟨y, hy⟩ : Q)⁆ : Q) ∈ frattini Q :=
    CFSG.GH74.E2.dsub_le_frattini hQ
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨x, hx⟩ : Q))
        (Subgroup.mem_top (⟨y, hy⟩ : Q)))
  have h2 := Subgroup.mem_map_of_mem Q.subtype h1
  have e : Q.subtype ⁅(⟨x, hx⟩ : Q), (⟨y, hy⟩ : Q)⁆ = ⁅x, y⁆ :=
    map_commutatorElement Q.subtype _ _
  rw [e] at h2
  exact h2

theorem dsFrattini_le_self (Q : Subgroup G) : dsFrattini Q ≤ Q := Subgroup.map_subtype_le _

theorem le_normalizer_dsFrattini {P Q : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) :
    P ≤ Subgroup.normalizer (dsFrattini Q : Set G) :=
  hPQ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini ↥Q))

theorem map_top_subtype' (Q : Subgroup G) : Subgroup.map Q.subtype ⊤ = Q := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_ne_bot [Finite4 G] [DSLeaf LeafRankBounds] {P Q : Subgroup G}
    (hQ32 : Nat.card Q = 32) (hQ : IsPGroup 2 Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hΦ : Nat.card (dsFrattini Q) = 2)
    (hirr : ∀ X : Subgroup G, dsFrattini Q ≤ X → X ≤ Q → P ≤ Subgroup.normalizer (X : Set G) →
      X = dsFrattini Q ∨ X = Q) :
    ⁅Q, Q⁆ ≠ ⊥ := by
  intro hab
  have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hab, Subgroup.mem_bot, commutatorElement_def] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hcomm' : ∀ x y : Q, Commute x y := fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)
  let f : Q →* Q :=
    { toFun := fun x => x ^ 2
      map_one' := by simp
      map_mul' := fun x y => (hcomm' x y).mul_pow 2 }
  have hK0 : ∀ x : G, x ∈ f.ker.map Q.subtype ↔ x ∈ Q ∧ x ^ 2 = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy2 : y ^ 2 = 1 := MonoidHom.mem_ker.mp hy
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy2
      simpa using this
    · rintro ⟨hx, hx2⟩
      refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      show (⟨x, hx⟩ : Q) ^ 2 = 1
      apply Subtype.ext
      simpa using hx2
  have hK0le : f.ker.map Q.subtype ≤ Q := Subgroup.map_subtype_le _
  have hΦK0 : dsFrattini Q ≤ f.ker.map Q.subtype := fun x hx =>
    (hK0 x).mpr ⟨dsFrattini_le_self Q hx, sq_eq_one_of_card_two hΦ hx⟩
  have hPK0 : P ≤ Subgroup.normalizer ((f.ker.map Q.subtype : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hQx : x ∈ Q ↔ g * x * g⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp (hPQ hg) x
    have hsq : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
      simp only [sq]
      group
    have hconj1 : ∀ y : G, g * y * g⁻¹ = 1 ↔ y = 1 := by
      intro y
      constructor
      · intro hy
        have e : y = g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ := by group
        rw [hy] at e
        simpa using e
      · intro hy
        rw [hy]
        group
    rw [hK0, hK0, ← hQx, hsq, hconj1]
  rcases hirr _ hΦK0 hK0le hPK0 with hK | hK
  ·
    have hcardf : Nat.card f.ker = 2 := by
      have e : Nat.card ↥(f.ker.map Q.subtype) = Nat.card ↥f.ker :=
        Subgroup.card_map_of_injective Q.subtype_injective
      rw [← e, hK, hΦ]
    have hidx := Subgroup.card_mul_index f.ker
    rw [hcardf, hQ32] at hidx
    have hrange : f.range ≤ frattini Q := by
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      show x ^ 2 ∈ frattini Q
      rw [sq]
      exact CFSG.GH74.E2.mul_self_mem_frattini hQ x
    have hfr : Nat.card (frattini Q) = 2 := by
      have e : Nat.card ↥((frattini Q).map Q.subtype) = Nat.card ↥(frattini Q) :=
        Subgroup.card_map_of_injective Q.subtype_injective
      rw [← e]
      exact hΦ
    have hle := Subgroup.card_le_of_le hrange
    have hidx2 := Subgroup.index_ker f
    omega
  ·
    have hEA : IsElemAbelian 2 Q := by
      unfold IsElemAbelian
      refine ⟨IsMulCommutative.mk ⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩, fun x hx => ?_⟩
      have hxK : x ∈ f.ker.map Q.subtype := by
        rw [hK]
        exact hx
      exact ((hK0 x).mp hxK).2
    have := (rank_bounds (G := G)).2 Q hEA
    omega

theorem center_eq_of_irr [Finite4 G] [DSLeaf LeafRankBounds] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ32 : Nat.card Q = 32) (hQ : IsPGroup 2 Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hΦ : Nat.card (dsFrattini Q) = 2)
    (hirr : ∀ X : Subgroup G, dsFrattini Q ≤ X → X ≤ Q → P ≤ Subgroup.normalizer (X : Set G) →
      X = dsFrattini Q ∨ X = Q)
    (hcentΦ : ∀ x ∈ dsFrattini Q, ∀ g ∈ P, g * x = x * g) :
    (Subgroup.center ↥Q).map Q.subtype = dsFrattini Q := by
  have hNA := commutator_ne_bot hQ32 hQ hPQ hΦ hirr
  apply le_antisymm
  · have hMQ : (Subgroup.center ↥Q).map Q.subtype ≤ Q := Subgroup.map_subtype_le _
    have hMN : P ≤ Subgroup.normalizer (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G) :=
      hPQ.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (Subgroup.center ↥Q))
    rcases hirr ((Subgroup.center ↥Q).map Q.subtype ⊔ dsFrattini Q) le_sup_right
        (sup_le hMQ (dsFrattini_le_self Q))
        (F1.le_normalizer_sup hMN (le_normalizer_dsFrattini hPQ)) with h | h
    · exact le_sup_left.trans h.le
    · exfalso
      have hQM : Q ≤ (Subgroup.center ↥Q).map Q.subtype := DSBA5.le_of_sup_dsFrattini_eq hMQ h
      apply hNA
      apply eq_bot_iff.mpr
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hQM hx)
      have hzc := Subgroup.mem_center_iff.mp hz
      have hyz : y * (z : G) = (z : G) * y := by
        have := congrArg Subtype.val (hzc ⟨y, hy⟩)
        simpa using this
      have hzx' : (z : G) = x := hzx
      rw [Subgroup.mem_bot, ← hzx', commutatorElement_def]
      rw [← hyz]
      group
  · intro x hx
    have hxQ : x ∈ Q := dsFrattini_le_self Q hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hcentΦ x hx g.1 (hQP g.2)

theorem isSpecialPow_of {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ32 : Nat.card Q = 32)
    (hZ : (Subgroup.center ↥Q).map Q.subtype = dsFrattini Q)
    (hC : ⁅Q, Q⁆ = dsFrattini Q) (hΦ : Nat.card (dsFrattini Q) = 2) :
    IsSpecialPow 2 2 2 ↥Q := by
  have hcomm : commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    have h1 : Subgroup.map Q.subtype (commutator ↥Q) = ⁅Q, Q⁆ := by
      show Subgroup.map Q.subtype ⁅(⊤ : Subgroup ↥Q), ⊤⁆ = _
      rw [Subgroup.map_commutator, map_top_subtype']
    rw [hZ, h1, hC]
  have hfrat : frattini ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    exact hZ.symm
  unfold IsSpecialPow IsSpecialPGroup
  refine ⟨⟨hQ, Or.inr ⟨hcomm, hfrat, fun z hz => ?_⟩⟩, ?_, ?_⟩
  · have hzΦ : (z : G) ∈ dsFrattini Q := by
      rw [← hZ]
      exact Subgroup.mem_map_of_mem Q.subtype hz
    apply Subtype.ext
    have := sq_eq_one_of_card_two hΦ hzΦ
    simpa using this
  · rw [hQ32]
    norm_num
  · rw [← Subgroup.card_map_of_injective Q.subtype_injective, hZ, hΦ]

theorem commutator_eq_of [Finite4 G] [DSLeaf LeafRankBounds] {P Q : Subgroup G}
    (hQ32 : Nat.card Q = 32) (hQ : IsPGroup 2 Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hΦ : Nat.card (dsFrattini Q) = 2)
    (hirr : ∀ X : Subgroup G, dsFrattini Q ≤ X → X ≤ Q → P ≤ Subgroup.normalizer (X : Set G) →
      X = dsFrattini Q ∨ X = Q) :
    ⁅Q, Q⁆ = dsFrattini Q := by
  have hNA := commutator_ne_bot hQ32 hQ hPQ hΦ hirr
  have hle : ⁅Q, Q⁆ ≤ dsFrattini Q :=
    Subgroup.commutator_le.mpr (fun x hx y hy => comm_mem_dsFrattini hQ hx hy)
  have hgt : 1 < Nat.card ↥⁅Q, Q⁆ := (Subgroup.one_lt_card_iff_ne_bot _).mpr hNA
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

end DSBUQ2

open DSBUQ2

theorem leafDSBUQ2 [DSLeaf LeafDSBUQ1] [DSLeaf LeafDSBUQQ] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafM7] [DSLeaf LeafFrattiniChief] : LeafDSBUQ2 := by
  intro G _ _ L1 L2 S h cU
  haveI : DSLeaf LeafFrattiniFaithful := ⟨leafFrattiniFaithful⟩
  haveI : DSLeaf LeafRankBounds := ⟨leafRankBounds⟩
  obtain ⟨hpc1, hZ1Q1, -, -, hcard1, hnat1, hcardQ2, hcardZ⟩ := dsbuq1 h cU
  obtain ⟨hQQ, hrelQ1, hZ1notQ2⟩ := dsbuqq h cU
  obtain ⟨hS2, hrelS, hd3B, -⟩ := dsbs3_vertex h
  have hZ1card : Nat.card ↥(dsZi L1 S) = 16 := by
    rw [← hZ1Q1, ← hpc1, hcard1]
  have hQ1S : dsQ L1 L2 S ≤ S := le_sup_left.trans hQQ.le
  have hQ2S : dsQ L2 L1 S ≤ S := le_sup_right.trans hQQ.le
  have hZ1S : dsZi L1 S ≤ S := by
    rw [← hZ1Q1]
    exact hQ1S
  have hQ1Z : pCoreOf 2 L1 = dsZi L1 S := hpc1.trans hZ1Q1
  have hA1 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hL1N : L1 ≤ Subgroup.normalizer (dsZi L1 S : Set G) := by
    rw [← hQ1Z]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1
  have hcardS : Nat.card ↥S = 2 * Nat.card ↥(dsQ L2 L1 S) := by
    have h1 := Subgroup.relIndex_mul_card (dsQ L2 L1 S) S
    rw [inf_eq_left.mpr hQ2S, hrelS] at h1
    exact h1.symm
  have hSyl1 : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  obtain ⟨⟨d, hdB, hd3⟩, hcardS1⟩ := DSBA5.three_and_card hSyl1 hA1.quot
  have hcSL1 : Nat.card ↥(S ⊓ L1) = 4 * 16 := by
    rw [hcardS1, hcard1]
  have hSL1 : S ⊓ L1 = S := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have hSle : S ≤ L1 := inf_eq_left.mp hSL1
  have hSyl : IsSylowTwoOf S L1 := by
    rw [hSL1] at hSyl1
    exact hSyl1
  have hdB' : d ∈ L1 ⊓ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := hdB
  have hdL1 : d ∈ L1 := hdB'.1
  have hdN : d ∈ Subgroup.normalizer (S : Set G) := by
    have h1 := hdB'.2
    rwa [hSL1] at h1
  obtain ⟨k, hkL2, hk3⟩ : ∃ k ∈ L2, orderOf k = 3 := by
    obtain ⟨e2⟩ := h.s3
    have hp6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have h3 : 3 ∣ Nat.card (oTwoQuot ↥L2) := by
      rw [Nat.card_congr e2.toEquiv, hp6]
      norm_num
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := oTwoQuot ↥L2) 3 h3
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L2) c
    have h3x : 3 ∣ orderOf x := by
      have := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥L2)) x
      rw [hx, hc] at this
      exact this
    refine ⟨(x ^ (orderOf x / 3) : ↥L2), (x ^ (orderOf x / 3)).2, ?_⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos x).ne' h3x
  have hP2N : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (L2 : Set G) :=
    F1.parabolic_le_normalizer h.hyp.symm
  have hCT : CharTwo (L2 ⊔ bigB L2 L1 S) := F1.parabolic_charTwo h.hyp.symm
  have hB1 : borelOf L1 S ≤ bigB L2 L1 S := le_sup_of_le_left le_sup_right
  have hdP : d ∈ L2 ⊔ bigB L2 L1 S := (le_sup_right : bigB L2 L1 S ≤ L2 ⊔ bigB L2 L1 S) (hB1 hdB)
  have hS3 : S3Par L2 (L2 ⊔ bigB L2 L1 S) d :=
    ⟨le_sup_left, hP2N, hCT, h.s3, hdP, hd3, fun l hl => hd3B d hdB hd3 l hl⟩
  obtain ⟨hidx16, -, htype⟩ := m7 hS3 hkL2 hk3
  have hidx16' : (dsFrattini (dsQ L2 L1 S)).relIndex (dsQ L2 L1 S) = 16 := hidx16
  have hQ2P2 : dsQ L2 L1 S ≤ L2 ⊔ bigB L2 L1 S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hP2Q2 : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L2 L1 S)
  have hQpg : IsPGroup 2 (dsQ L2 L1 S) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L2 ⊔ bigB L2 L1 S)
  have hSP2 : S ≤ L2 ⊔ bigB L2 L1 S := (le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right
  have hΦle : dsFrattini (dsQ L2 L1 S) ≤ dsQ L2 L1 S := dsFrattini_le_self _
  have hΦcard : Nat.card ↥(dsFrattini (dsQ L2 L1 S)) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (dsFrattini (dsQ L2 L1 S)) (dsQ L2 L1 S)
    rw [inf_eq_left.mpr hΦle, hidx16', hcardQ2] at h1
    omega
  have hΦN : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (dsFrattini (dsQ L2 L1 S) : Set G) :=
    le_normalizer_dsFrattini hP2Q2
  have hΦcent : ∀ x ∈ dsFrattini (dsQ L2 L1 S), ∀ g ∈ L2 ⊔ bigB L2 L1 S, g * x = x * g :=
    fun x hx g hg => DSBUQ2.mem_center_of_card_two hΦcard hΦN hx hg
  have hΦZ : dsFrattini (dsQ L2 L1 S) = dsZ S := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      have hxS : x ∈ S := hQ2S (hΦle hx)
      have hxc : x ∈ centerOf S := by
        show x ∈ S ⊓ Subgroup.centralizer (S : Set G)
        refine Subgroup.mem_inf.mpr ⟨hxS, Subgroup.mem_centralizer_iff.mpr (fun s hs => ?_)⟩
        exact hΦcent x hx s (hSP2 hs)
      have hmem : x ∈ {y : G | y ∈ centerOf S ∧ y ^ 2 = 1} :=
        ⟨hxc, sq_eq_one_of_card_two hΦcard hx⟩
      exact Subgroup.subset_closure hmem
    · exact (hcardZ.trans hΦcard.symm).le
  obtain ⟨hZ1A5, -, hZS, -⟩ := zi_chief (⟨h.hyp, DSBHyp.bnorm h⟩ : ZSetting L1 L2 S) hA1.quot cU
  have hnatZ : ¬ NatSec L1 ⊥ (dsZi L1 S) := by
    rw [← hZ1Q1, ← hpc1]
    exact hnat1
  obtain ⟨hX3, hr2, hr8, -, -, hFF3⟩ := (m3 hZ1A5 hSyl).2 hnatZ
  have hcardA : Nat.card ↥⁅dsZi L1 S, S⁆ = 8 := by
    have h1 := hr8
    rw [Subgroup.relIndex_bot_left, sup_bot_eq] at h1
    exact h1
  have hZSN : L1 ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (dsZ S : Set G) := by
    intro g hg
    obtain ⟨hgL1, hgS⟩ := Subgroup.mem_inf.mp hg
    rw [hZS]
    exact normalizer_inf_centralizer (hL1N hgL1) hgS
  have hXmem := hX3 (dsZ S) bot_le (dsZ_le_dsZi L1 S) hZSN
  have hΦB : dsFrattini (dsQ L2 L1 S) = ⁅⁅dsZi L1 S, S⁆, S⁆ := by
    rcases hXmem with h0 | h0 | h0 | h0
    · exfalso
      rw [h0, Subgroup.card_bot] at hcardZ
      omega
    · rw [hΦZ, h0, sup_bot_eq]
    · exfalso
      rw [h0, sup_bot_eq, hcardA] at hcardZ
      omega
    · exfalso
      rw [h0, hZ1card] at hcardZ
      omega
  have hrelZ : (dsZi L1 S ⊓ dsQ L2 L1 S).relIndex (dsZi L1 S) = 2 := by
    rw [← hZ1Q1]
    exact hrelQ1
  have hH : ⁅dsZi L1 S, S⁆ = dsZi L1 S ⊓ dsQ L2 L1 S := by
    have hle : ⁅dsZi L1 S, S⁆ ≤ dsZi L1 S ⊓ dsQ L2 L1 S := by
      rw [Subgroup.commutator_le]
      intro z hz s hs
      refine Subgroup.mem_inf.mpr ⟨comm_mem_of_normal hL1N hz (hSle hs), ?_⟩
      exact comm_mem_of_relIndex_two hrelS (hZ1S hz) hs
    have hcardI : Nat.card ↥(dsZi L1 S ⊓ dsQ L2 L1 S) = 8 := by
      have h1 := Subgroup.relIndex_mul_card (dsZi L1 S ⊓ dsQ L2 L1 S) (dsZi L1 S)
      rw [inf_eq_left.mpr (inf_le_left : dsZi L1 S ⊓ dsQ L2 L1 S ≤ dsZi L1 S), hrelZ] at h1
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hFFd : ∀ y ∈ dsZi L1 S ⊓ dsQ L2 L1 S, ⁅y, d⁆ ∈ dsFrattini (dsQ L2 L1 S) →
      y ∈ dsFrattini (dsQ L2 L1 S) := by
    intro y hy hyd
    have hdN' : d ∈ L1 ⊓ Subgroup.normalizer (S : Set G) := Subgroup.mem_inf.mpr ⟨hdL1, hdN⟩
    have hf := hFF3 d hdN' hd3
    have hyI : y ∈ ⁅dsZi L1 S, S⁆ ⊔ ⊥ := by
      rw [sup_bot_eq, hH]
      exact hy
    have hydI : ⁅y, d⁆ ∈ ⁅⁅dsZi L1 S, S⁆, S⁆ ⊔ ⊥ := by
      rw [sup_bot_eq, ← hΦB]
      exact hyd
    have h2 := hf y hyI hydI
    rw [sup_bot_eq, ← hΦB] at h2
    exact h2
  have hII : S3Type2 (L2 ⊔ bigB L2 L1 S) k d := by
    rcases htype with h2 | h1
    · exact h2
    · exfalso
      obtain ⟨W1, W2, hΦW1, hW1Q, hΦW2, hW2Q, hPW1, hPW2, -, hjoin, -, -, hLW1, -, hdW2, -, -⟩ := h1
      have hW2N : W2 ≤ Subgroup.normalizer (W1 : Set G) := hW2Q.trans (hQ2P2.trans hPW1)
      obtain ⟨t, htZ, htnot⟩ : ∃ t ∈ dsZi L1 S, t ∉ dsQ L2 L1 S :=
        SetLike.not_le_iff_exists.mp hZ1notQ2
      have htS : t ∈ S := hZ1S htZ
      have htP2 : t ∈ L2 ⊔ bigB L2 L1 S := hSP2 htS
      have hS2' : S = dsQ L2 L1 S ⊔ (S ⊓ L2) := by
        rw [sup_comm]
        exact hS2
      have htS' : t ∈ dsQ L2 L1 S ⊔ (S ⊓ L2) := by
        rw [← hS2']
        exact htS
      have hN_SL2 : S ⊓ L2 ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
        (inf_le_left : S ⊓ L2 ≤ S).trans (hSP2.trans hP2Q2)
      obtain ⟨q, hqQ2, s, hsSL2, hts⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hN_SL2).mp htS'
      have hsL2 : s ∈ L2 := (Subgroup.mem_inf.mp hsSL2).2
      have hcW1 : ∀ a ∈ W1, ⁅a, t⁆ ∈ dsFrattini (dsQ L2 L1 S) := by
        intro a ha
        have haQ2 : a ∈ dsQ L2 L1 S := hW1Q ha
        have haq : ⁅a, q⁆ ∈ dsFrattini (dsQ L2 L1 S) :=
          comm_mem_dsFrattini hQpg haQ2 hqQ2
        have has : ⁅a, s⁆ ∈ dsFrattini (dsQ L2 L1 S) := by
          have h1 := hLW1 s hsL2 a ha
          have e2 : ⁅a, s⁆ = (⁅s, a⁆)⁻¹ := (commutatorElement_inv s a).symm
          rw [e2]
          exact Subgroup.inv_mem _ h1
        have hconj : q * ⁅a, s⁆ * q⁻¹ ∈ dsFrattini (dsQ L2 L1 S) :=
          (Subgroup.mem_normalizer_iff.mp (hΦN (hQ2P2 hqQ2)) ⁅a, s⁆).mp has
        have e : ⁅a, t⁆ = ⁅a, q⁆ * (q * ⁅a, s⁆ * q⁻¹) := by
          rw [hts]
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ haq hconj
      have hcW2 : ∀ b ∈ W2, ⁅b, t⁆ ∈ W2 := by
        intro b hb
        have htN : t * b * t⁻¹ ∈ W2 := (Subgroup.mem_normalizer_iff.mp (hPW2 htP2) b).mp hb
        have e : ⁅b, t⁆ = b * (t * b * t⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ htN)
      have hcX : ∀ x ∈ dsQ L2 L1 S, ⁅x, t⁆ ∈ W2 := by
        intro x hx
        have hx' : x ∈ W1 ⊔ W2 := by
          rw [hjoin]
          exact hx
        obtain ⟨a, ha, b, hb, hxab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hW2N).mp hx'
        rw [hxab]
        have e : ⁅a * b, t⁆ = (a * ⁅b, t⁆ * a⁻¹) * ⁅a, t⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have haP2 : a ∈ L2 ⊔ bigB L2 L1 S := hQ2P2 (hW1Q ha)
        have hA : a * ⁅b, t⁆ * a⁻¹ ∈ W2 :=
          (Subgroup.mem_normalizer_iff.mp (hPW2 haP2) ⁅b, t⁆).mp (hcW2 b hb)
        exact Subgroup.mul_mem _ hA (hΦW2 (hcW1 a ha))
      have hdiag : ∀ x ∈ dsQ L2 L1 S, ⁅x, t⁆ ∈ dsZi L1 S ⊓ dsQ L2 L1 S := by
        intro x hx
        have hxS : x ∈ S := hQ2S hx
        refine Subgroup.mem_inf.mpr ⟨?_, comm_mem_of_relIndex_two hrelS hxS htS⟩
        have h1 := comm_mem_of_normal hL1N htZ (hSle hxS)
        have e : ⁅x, t⁆ = ⁅t, x⁆⁻¹ := (commutatorElement_inv t x).symm
        rw [e]
        exact Subgroup.inv_mem _ h1
      have hall : ∀ x ∈ dsQ L2 L1 S, ⁅x, t⁆ ∈ dsFrattini (dsQ L2 L1 S) := by
        intro x hx
        have hy := hdiag x hx
        have hdy : ⁅d, ⁅x, t⁆⁆ ∈ dsFrattini (dsQ L2 L1 S) := hdW2 _ (hcX x hx)
        apply hFFd _ hy
        have e : ⁅⁅x, t⁆, d⁆ = ⁅d, ⁅x, t⁆⁆⁻¹ := (commutatorElement_inv d ⁅x, t⁆).symm
        rw [e]
        exact Subgroup.inv_mem _ hdy
      have hcond : ∀ q' ∈ dsQ L2 L1 S, ⁅t, q'⁆ ∈ dsFrattini (dsQ L2 L1 S) := by
        intro q' hq'
        have e : ⁅t, q'⁆ = ⁅q', t⁆⁻¹ := (commutatorElement_inv q' t).symm
        rw [e]
        exact Subgroup.inv_mem _ (hall q' hq')
      exact htnot (frattini_faithful hCT t htP2 hcond)
  obtain ⟨hFFk, -, hirr⟩ := hII
  have hR : dsQ L2 L1 S ⊓ L2 = pCoreOf 2 L2 := F1.inf_pCoreOf_parabolic_eq h.hyp.symm
  have hRN : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer ((dsQ L2 L1 S ⊓ L2 : Subgroup G) : Set G) :=
    le_normalizer_inf hP2Q2 hP2N
  have hXN : L2 ⊔ bigB L2 L1 S ≤
      Subgroup.normalizer (((dsQ L2 L1 S ⊓ L2) ⊔ dsFrattini (dsQ L2 L1 S) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hRN hΦN
  have hXle : (dsQ L2 L1 S ⊓ L2) ⊔ dsFrattini (dsQ L2 L1 S) ≤ dsQ L2 L1 S :=
    sup_le inf_le_left hΦle
  have hΦle' : dsFrattini (dsQ L2 L1 S) ≤ (dsQ L2 L1 S ⊓ L2) ⊔ dsFrattini (dsQ L2 L1 S) :=
    le_sup_right
  have hpcL2 : pCoreOf 2 L2 = dsQ L2 L1 S := by
    rcases hirr _ hΦle' hXle hXN with hX | hX
    · exfalso
      have hRΦ : dsQ L2 L1 S ⊓ L2 ≤ dsFrattini (dsQ L2 L1 S) := le_sup_left.trans hX.le
      have hQΦ : dsQ L2 L1 S ≤ dsFrattini (dsQ L2 L1 S) := by
        intro e he
        have heP2 : e ∈ L2 ⊔ bigB L2 L1 S := hQ2P2 he
        have hkP2 : k ∈ L2 ⊔ bigB L2 L1 S := Subgroup.mem_sup_left hkL2
        have hcQ : ⁅e, k⁆ ∈ dsQ L2 L1 S := comm_mem_of_normal hP2Q2 he hkP2
        have hcL : ⁅e, k⁆ ∈ L2 := by
          have h1 : ⁅k, e⁆ ∈ L2 := comm_mem_of_normal hP2N hkL2 heP2
          have e2 : ⁅e, k⁆ = ⁅k, e⁆⁻¹ := (commutatorElement_inv k e).symm
          rw [e2]
          exact Subgroup.inv_mem _ h1
        have hmem : ⁅e, k⁆ ∈ dsFrattini (dsQ L2 L1 S) :=
          hRΦ (Subgroup.mem_inf.mpr ⟨hcQ, hcL⟩)
        exact hFFk e he hmem
      have hEq : dsQ L2 L1 S = dsFrattini (dsQ L2 L1 S) := le_antisymm hQΦ hΦle
      have h32 : Nat.card ↥(dsFrattini (dsQ L2 L1 S)) = 32 := by
        rw [← hEq]
        exact hcardQ2
      omega
    · have hRQ : dsQ L2 L1 S ≤ dsQ L2 L1 S ⊓ L2 :=
        DSBA5.le_of_sup_dsFrattini_eq inf_le_left hX
      have hQL2 : dsQ L2 L1 S ≤ L2 := hRQ.trans inf_le_right
      rw [← hR]
      exact inf_eq_left.mpr hQL2
  have hZc := center_eq_of_irr hQ2P2 hcardQ2 hQpg hP2Q2 hΦcard hirr hΦcent
  have hCc := commutator_eq_of hcardQ2 hQpg hP2Q2 hΦcard hirr
  refine ⟨hpcL2, hΦZ, ?_⟩
  rw [hpcL2]
  exact isSpecialPow_of hQpg hcardQ2 hZc hCc hΦcard

end CFSG.GH74.QTGen4.DSGen4
