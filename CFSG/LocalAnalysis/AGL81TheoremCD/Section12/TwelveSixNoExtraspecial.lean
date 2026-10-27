module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKCtx
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BarBlocks
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
import CFSG.GroupTheory.PRankCommutingSup
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.ConjTransport
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.L3TwoPowAutThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem isL3TwoPow_of_mulEquiv {n : ℕ} {X Y : Type} [Group X] [Group Y]
    (h : IsL3TwoPow n X) (e : X ≃* Y) : IsL3TwoPow n Y := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

private theorem pRank_zpowers_of_orderOf_eq_three {Y : Type} [Group Y] [Finite Y] {w : Y}
    (hw : orderOf w = 3) : CFSG.Open.pRank 3 (Subgroup.zpowers w) = 1 := by
  refine le_antisymm ?_ ?_
  · exact CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three (Subgroup.isCyclic_zpowers w)
  · refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl (Subgroup.zpowers w))
      (CFSG.Open.isElemAbelian_zpowers (p := 3) ?_) ?_
    · rw [← hw]
      exact pow_orderOf_eq_one w
    · rw [Nat.card_zpowers, hw]
      norm_num

private theorem card_le_three_of_isPGroup_of_pow_eq_one {Y : Type} [Group Y] [Finite Y]
    {A : Subgroup Y} (hAp : IsPGroup 3 A) (hAexp : ∀ x : ↥A, x ^ 3 = 1)
    (hA1 : CFSG.Open.pRank 3 A ≤ 1) : Nat.card ↥A ≤ 3 := by
  have hcyc : IsCyclic ↥A :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hAp le_rfl hA1
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hAexp g)
  rw [hg] at h3
  exact Nat.le_of_dvd (by norm_num) h3

private noncomputable def prodJoinHom {Y : Type} [Group Y] (A B : Subgroup Y)
    (hc : A ≤ Subgroup.centralizer (B : Set Y)) : ↥A × ↥B →* Y :=
  MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => (Subgroup.mem_centralizer_iff.mp (hc a.2) b b.2).symm)

private theorem prodJoinHom_apply {Y : Type} [Group Y] {A B : Subgroup Y}
    (hc : A ≤ Subgroup.centralizer (B : Set Y)) (a : ↥A) (b : ↥B) :
    prodJoinHom A B hc (a, b) = (a : Y) * (b : Y) :=
  MonoidHom.noncommCoprod_apply _ _ _ _

private theorem prodJoinHom_injective {Y : Type} [Group Y] {A B : Subgroup Y}
    (hc : A ≤ Subgroup.centralizer (B : Set Y)) (hAB : A ⊓ B = ⊥) :
    Function.Injective (prodJoinHom A B hc) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hxy
  simp only [prodJoinHom_apply] at hxy
  have heq : (a₂ : Y)⁻¹ * a₁ = b₂ * (b₁ : Y)⁻¹ := by
    calc (a₂ : Y)⁻¹ * a₁ = (a₂ : Y)⁻¹ * (a₁ * b₁) * (b₁ : Y)⁻¹ := by group
      _ = (a₂ : Y)⁻¹ * (a₂ * b₂) * (b₁ : Y)⁻¹ := by rw [hxy]
      _ = b₂ * (b₁ : Y)⁻¹ := by group
  have hone : (a₂ : Y)⁻¹ * a₁ = 1 := by
    have hmem : (a₂ : Y)⁻¹ * a₁ ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a₂.2) a₁.2, heq ▸ B.mul_mem b₂.2 (B.inv_mem b₁.2)⟩
    simpa [hAB] using hmem
  have h2 : (b₂ : Y) * (b₁ : Y)⁻¹ = 1 := by rw [← heq, hone]
  exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp hone).symm)
    (Subtype.ext (mul_inv_eq_one.mp h2).symm)

private theorem prodJoinHom_range {Y : Type} [Group Y] {A B : Subgroup Y}
    (hc : A ≤ Subgroup.centralizer (B : Set Y)) :
    (prodJoinHom A B hc).range = A ⊔ B := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro y ⟨⟨a, b⟩, rfl⟩
    rw [prodJoinHom_apply]
    exact Subgroup.mul_mem_sup a.2 b.2
  · intro a ha
    exact ⟨(⟨a, ha⟩, 1), by simp [prodJoinHom_apply]⟩
  · intro b hb
    exact ⟨(1, ⟨b, hb⟩), by simp [prodJoinHom_apply]⟩

private theorem card_comap_prodJoinHom {Y : Type} [Group Y] [Finite Y]
    {A B H : Subgroup Y} (hc : A ≤ Subgroup.centralizer (B : Set Y)) (hAB : A ⊓ B = ⊥)
    (hH : H ≤ A ⊔ B) :
    Nat.card ↥(H.comap (prodJoinHom A B hc)) = Nat.card ↥H := by
  have hmap : (H.comap (prodJoinHom A B hc)).map (prodJoinHom A B hc) = H := by
    rw [Subgroup.map_comap_eq, prodJoinHom_range hc]
    exact inf_eq_right.mpr hH
  have h : Nat.card ↥((H.comap (prodJoinHom A B hc)).map (prodJoinHom A B hc)) =
      Nat.card ↥(H.comap (prodJoinHom A B hc)) :=
    Subgroup.card_map_of_injective (prodJoinHom_injective hc hAB)
  rw [hmap] at h
  exact h.symm

private theorem pow_eq_one_comap_prodJoinHom {Y : Type} [Group Y]
    {A B H : Subgroup Y} (hc : A ≤ Subgroup.centralizer (B : Set Y)) (hAB : A ⊓ B = ⊥)
    (hHexp : ∀ x : ↥H, x ^ 3 = 1) :
    ∀ x : ↥(H.comap (prodJoinHom A B hc)), x ^ 3 = 1 := by
  intro x
  have hmem : prodJoinHom A B hc (x : ↥A × ↥B) ∈ H := x.2
  have h1 : (prodJoinHom A B hc (x : ↥A × ↥B)) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (hHexp ⟨_, hmem⟩)
  have h2 : prodJoinHom A B hc ((x : ↥A × ↥B) ^ 3) = 1 := by
    rw [map_pow]
    exact h1
  exact Subtype.ext (prodJoinHom_injective hc hAB (by
    show prodJoinHom A B hc ((x : ↥A × ↥B) ^ 3) = prodJoinHom A B hc 1
    rw [h2, map_one]))

private theorem isPGroup_map_of_isPGroup {X Z : Type} [Group X] [Group Z]
    {K : Subgroup X} {f : X →* Z} (hK : IsPGroup 3 K) : IsPGroup 3 ↥(K.map f) :=
  hK.map f

private theorem pow_eq_one_map_of_forall {X Z : Type} [Group X] [Group Z]
    {K : Subgroup X} {f : X →* Z} (h : ∀ x : ↥K, x ^ 3 = 1) :
    ∀ y : ↥(K.map f), y ^ 3 = 1 := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  apply Subtype.ext
  change (f x) ^ 3 = 1
  rw [← map_pow]
  have hx3 : (⟨x, hx⟩ : ↥K) ^ 3 = 1 := h ⟨x, hx⟩
  rw [show x ^ 3 = 1 from congrArg Subtype.val hx3, map_one]

private theorem card_le_card_map_fst_mul_card_map_snd {X Z : Type} [Group X] [Group Z]
    [Finite X] [Finite Z] {K : Subgroup (X × Z)} :
    Nat.card ↥K ≤ Nat.card ↥(K.map (MonoidHom.fst X Z)) *
      Nat.card ↥(K.map (MonoidHom.snd X Z)) := by
  let f : ↥K → ↥(K.map (MonoidHom.fst X Z)) × ↥(K.map (MonoidHom.snd X Z)) := fun k =>
    (⟨((k : X × Z).1), Subgroup.mem_map.mpr ⟨k, k.2, rfl⟩⟩,
      ⟨((k : X × Z).2), Subgroup.mem_map.mpr ⟨k, k.2, rfl⟩⟩)
  have hinj : Function.Injective f := by
    intro k l hkl
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => (z.1 : X)) hkl) (congrArg (fun z => (z.2 : Z)) hkl)
  have h := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_prod] at h

private theorem map_subtype_pow_eq_one {Y : Type} [Group Y] {A : Subgroup Y}
    {A' : Subgroup A} (h : ∀ x : ↥A', x ^ 3 = 1) :
    ∀ x : ↥(A'.map A.subtype), x ^ 3 = 1 := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subtype.ext (by
    have h' := h ⟨a, ha⟩
    have h2 := congrArg (fun z : A => (z : Y)) (congrArg Subtype.val h')
    simpa using h2)

private theorem exists_projections_of_le_sup {Y : Type} [Group Y] [Finite Y]
    {A B H : Subgroup Y} (hc : A ≤ Subgroup.centralizer (B : Set Y)) (hAB : A ⊓ B = ⊥)
    (hH : H ≤ A ⊔ B) (hHp : IsPGroup 3 H) (hHexp : ∀ x : ↥H, x ^ 3 = 1) :
    ∃ A' B' : Subgroup Y, A' ≤ A ∧ B' ≤ B ∧ IsPGroup 3 A' ∧ IsPGroup 3 B' ∧
      (∀ x : ↥A', x ^ 3 = 1) ∧ (∀ x : ↥B', x ^ 3 = 1) ∧
      Nat.card ↥H ≤ Nat.card ↥A' * Nat.card ↥B' := by
  let K : Subgroup (↥A × ↥B) := H.comap (prodJoinHom A B hc)
  have hKcard : Nat.card ↥K = Nat.card ↥H := card_comap_prodJoinHom hc hAB hH
  have hKp : IsPGroup 3 ↥K := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    exact IsPGroup.iff_card.mpr ⟨k, hKcard.trans hk⟩
  have hKexp : ∀ x : ↥K, x ^ 3 = 1 := pow_eq_one_comap_prodJoinHom hc hAB hHexp
  refine ⟨(K.map (MonoidHom.fst ↥A ↥B)).map A.subtype,
    (K.map (MonoidHom.snd ↥A ↥B)).map B.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · exact Subgroup.map_subtype_le _
  · exact isPGroup_map_of_isPGroup (isPGroup_map_of_isPGroup hKp)
  · exact isPGroup_map_of_isPGroup (isPGroup_map_of_isPGroup hKp)
  · exact map_subtype_pow_eq_one (pow_eq_one_map_of_forall hKexp)
  · exact map_subtype_pow_eq_one (pow_eq_one_map_of_forall hKexp)
  · calc Nat.card ↥H = Nat.card ↥K := hKcard.symm
      _ ≤ Nat.card ↥(K.map (MonoidHom.fst ↥A ↥B)) *
          Nat.card ↥(K.map (MonoidHom.snd ↥A ↥B)) := card_le_card_map_fst_mul_card_map_snd
      _ = Nat.card ↥((K.map (MonoidHom.fst ↥A ↥B)).map A.subtype) *
          Nat.card ↥((K.map (MonoidHom.snd ↥A ↥B)).map B.subtype) := by
          rw [Subgroup.card_map_of_injective A.subtype_injective,
            Subgroup.card_map_of_injective B.subtype_injective]

private theorem exists_left_card_le_of_le_sup {Y : Type} [Group Y] [Finite Y]
    {A B H : Subgroup Y} (hc : A ≤ Subgroup.centralizer (B : Set Y)) (hAB : A ⊓ B = ⊥)
    (hH : H ≤ A ⊔ B) (hHp : IsPGroup 3 H) (hHexp : ∀ x : ↥H, x ^ 3 = 1)
    (hB1 : CFSG.Open.pRank 3 B ≤ 1) :
    ∃ H' : Subgroup Y, H' ≤ A ∧ IsPGroup 3 H' ∧ (∀ x : ↥H', x ^ 3 = 1) ∧
      Nat.card ↥H ≤ 3 * Nat.card ↥H' := by
  obtain ⟨A', B', hA', hB', hA'p, hB'p, hA'exp, hB'exp, hcard⟩ :=
    exists_projections_of_le_sup hc hAB hH hHp hHexp
  have hB'1 : CFSG.Open.pRank 3 B' ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hB').trans hB1
  have hB'card : Nat.card ↥B' ≤ 3 :=
    card_le_three_of_isPGroup_of_pow_eq_one hB'p hB'exp hB'1
  refine ⟨A', hA', hA'p, hA'exp, ?_⟩
  calc Nat.card ↥H ≤ Nat.card ↥A' * Nat.card ↥B' := hcard
    _ ≤ Nat.card ↥A' * 3 := Nat.mul_le_mul_left _ hB'card
    _ = 3 * Nat.card ↥A' := Nat.mul_comm _ _

private theorem triple_conj_eq_self {Y : Type} [Group Y] {b : Y} (hb : b ^ 3 = 1) (x : Y) :
    b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = x := by
  have h2 : b⁻¹ ^ 3 = 1 := by rw [inv_pow, hb, inv_one]
  calc b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹
      = (b * b * b) * x * (b⁻¹ * b⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = b ^ 3 * x * b⁻¹ ^ 3 := by
        rw [pow_three, pow_three]
        group
    _ = x := by rw [hb, h2, one_mul, mul_one]

private theorem exists_mulAut_conj_barM {L : Subgroup G} {b : G} (hbM : b ∈ M)
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ φ : MulAut ↥(barM M L), φ ^ 3 = 1 ∧ ∀ x : ↥(barM M L),
      ((φ x : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
          (x : ↥M ⧸ CFSG.pCore 2 ↥M) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩)⁻¹ := by
  classical
  let bbar : ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩
  have hLmap : Subgroup.map (MulAut.conj b).toMonoidHom L = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hbN
  have hbar : Subgroup.map (MulAut.conj bbar).toMonoidHom (barM M L) = barM M L := by
    have h := CFSG.AGLEmbedding.barM_map_conj hbM L
    rw [hLmap] at h
    exact h.symm
  let φ : MulAut ↥(barM M L) :=
    ((MulAut.conj bbar).subgroupMap (barM M L)).trans (MulEquiv.subgroupCongr hbar)
  have hbbar3 : bbar ^ 3 = 1 := by
    rw [← map_pow]
    have h : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [h, map_one]
  have hφ : ∀ x : ↥(barM M L),
      ((φ x : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
        bbar * (x : ↥M ⧸ CFSG.pCore 2 ↥M) * bbar⁻¹ := by
    intro x
    rw [show ((φ x : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
        (((MulEquiv.subgroupMap (MulAut.conj bbar) (barM M L)) x :
          ↥((barM M L).map (MulAut.conj bbar).toMonoidHom)) :
            ↥M ⧸ CFSG.pCore 2 ↥M) from rfl,
      MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  refine ⟨φ, ?_, hφ⟩
  refine MulEquiv.ext fun x => ?_
  show φ (φ (φ x)) = x
  apply Subtype.ext
  rw [hφ, hφ, hφ]
  exact triple_conj_eq_self hbbar3 _

private theorem exists_orderOf_three_commute {L : Subgroup G} {n : ℕ} {b : G}
    (hbM : b ∈ M)
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hcomp : CFSG.AGLEmbedding.IsTwoPrimeComponent M L)
    (htype : IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    ∃ w : ↥(barM M L), orderOf w = 3 ∧
      Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) ((w : ↥M ⧸ CFSG.pCore 2 ↥M)) := by
  classical
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hcomp.le hcomp.inf_twoCore
  have htype' : IsL3TwoPow n ↥(barM M L) := isL3TwoPow_of_mulEquiv htype e
  obtain ⟨φ, hφ3, hφ⟩ := exists_mulAut_conj_barM hbM hbN hb3
  obtain ⟨w, hword, hwfix⟩ :=
    exists_orderOf_three_fixed_of_isL3TwoPow htype' φ hφ3
  refine ⟨w, hword, ?_⟩
  have hconj : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
      (w : ↥M ⧸ CFSG.pCore 2 ↥M) * (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩)⁻¹ =
      (w : ↥M ⧸ CFSG.pCore 2 ↥M) := by
    have h := congrArg Subtype.val hwfix
    rwa [hφ w] at h
  have hcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
      (w : ↥M ⧸ CFSG.pCore 2 ↥M) =
      (w : ↥M ⧸ CFSG.pCore 2 ↥M) * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ := by
    have := congrArg (fun z => z * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) hconj
    simpa [mul_assoc] using this
  exact hcomm

private noncomputable def blockAction (D : Subgroup G) (S : Set (Subgroup G))
    (hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S) :
    ↥D →* Equiv.Perm ↥S where
  toFun d :=
    { toFun := fun L => ⟨L.1.map (MulAut.conj (d : G)).toMonoidHom, hS d L.1 L.2⟩
      invFun := fun L => ⟨L.1.map (MulAut.conj ((d : G)⁻¹)).toMonoidHom,
        hS ⟨(d : G)⁻¹, D.inv_mem d.2⟩ L.1 L.2⟩
      left_inv := by
        intro L
        apply Subtype.ext
        exact CFSG.GroupTheory.map_conj_map_conj_inv (d : G) L.1
      right_inv := by
        intro L
        apply Subtype.ext
        simpa using CFSG.GroupTheory.map_conj_map_conj_inv ((d : G)⁻¹) L.1 }
  map_one' := by
    refine Equiv.ext fun L => ?_
    apply Subtype.ext
    show Subgroup.map (MulAut.conj ((1 : ↥D) : G)) (L : Subgroup G) = (L : Subgroup G)
    rw [show ((1 : ↥D) : G) = 1 from rfl,
      show MulAut.conj (1 : G) = 1 from map_one (MulAut.conj : G →* MulAut G)]
    change Subgroup.map (MonoidHom.id G) (L : Subgroup G) = (L : Subgroup G)
    simp
  map_mul' := by
    intro d e
    refine Equiv.ext fun L => ?_
    apply Subtype.ext
    exact (CFSG.GroupTheory.map_conj_map_conj (d : G) (e : G) L.1).symm

private theorem nat_card_set_three_le (A B C : Subgroup G) :
    Nat.card ↥({A, B, C} : Set (Subgroup G)) ≤ 3 := by
  rw [Nat.card_coe_set_eq]
  calc ({A, B, C} : Set (Subgroup G)).ncard
      ≤ ({B, C} : Set (Subgroup G)).ncard + 1 := Set.ncard_insert_le A {B, C}
    _ ≤ ({C} : Set (Subgroup G)).ncard + 1 + 1 := by
        have := Set.ncard_insert_le B ({C} : Set (Subgroup G))
        omega
    _ = 3 := by simp

private theorem blockAction_range_isPGroup {D : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S)
    (hDcard : Nat.card ↥D = 3 ^ 5) : IsPGroup 3 ↥(blockAction D S hS).range := by
  rw [IsPGroup.iff_card]
  have hdvd : Nat.card ↥(blockAction D S hS).range ∣ 3 ^ 5 := by
    rw [← hDcard]
    exact Subgroup.card_range_dvd _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨j, hj⟩

private theorem blockAction_range_card_le_three {D : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S)
    (hDcard : Nat.card ↥D = 3 ^ 5) (hScard : Nat.card ↥S ≤ 3) :
    Nat.card ↥(blockAction D S hS).range ≤ 3 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (blockAction_range_isPGroup hS hDcard)
  have hPerm : Nat.card (Equiv.Perm ↥S) ∣ 6 := by
    rw [Nat.card_perm]
    have h0 : 0 ≤ Nat.card ↥S := Nat.zero_le _
    have h2 : Nat.card ↥S ≤ 3 := hScard
    interval_cases Nat.card ↥S <;> norm_num
  have hdvd : Nat.card ↥(blockAction D S hS).range ∣ 6 := by
    refine (Subgroup.card_dvd_of_le (le_top : _ ≤ ⊤)).trans ?_
    simpa using hPerm
  have hj1 : j ≤ 1 := by
    by_contra h
    have hj2 : 2 ≤ j := by omega
    have h9 : 9 ∣ Nat.card ↥(blockAction D S hS).range := by
      rw [hj]
      exact pow_dvd_pow 3 hj2
    have : 9 ∣ 6 := h9.trans hdvd
    norm_num at this
  calc Nat.card ↥(blockAction D S hS).range = 3 ^ j := hj
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
    _ = 3 := by norm_num

private theorem blockAction_ker_card_ge {D : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S)
    (hDcard : Nat.card ↥D = 3 ^ 5) (hScard : Nat.card ↥S ≤ 3) :
    81 ≤ Nat.card ↥(blockAction D S hS).ker := by
  have h := Subgroup.card_ker_mul_card_range (blockAction D S hS)
  have h243 : Nat.card ↥D = 243 := by rw [hDcard]; norm_num
  rw [h243] at h
  have h1 : 0 < Nat.card ↥(blockAction D S hS).range := Nat.card_pos
  have h2 := blockAction_range_card_le_three hS hDcard hScard
  interval_cases Nat.card ↥(blockAction D S hS).range <;> omega

private theorem blockAction_ker_normalizes {D : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S)
    {L : Subgroup G} (hL : L ∈ S) :
    (blockAction D S hS).ker.map D.subtype ≤ Subgroup.normalizer (L : Set G) := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
  have h := congrArg (fun σ : Equiv.Perm ↥S => (σ ⟨L, hL⟩ : ↥S)) hk
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
    have h2 := congrArg (fun z : ↥S => (z : Subgroup G)) h
    simpa [blockAction] using h2)

private theorem exists_kernel_subgroup (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {D : Subgroup G} (hDM : D ≤ M) (hD3 : IsPGroup 3 D)
    (hDpow : ∀ x : ↥D, x ^ 3 = 1) (hDcard : Nat.card ↥D = 3 ^ 5) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup 3 B ∧ (∀ x : ↥B, x ^ 3 = 1) ∧
      81 ≤ Nat.card ↥B ∧ B ≤ Subgroup.normalizer (L₁ : Set G) ∧
      B ≤ Subgroup.normalizer (L₂ : Set G) ∧ B ≤ Subgroup.normalizer (L₃ : Set G) := by
  classical
  let S : Set (Subgroup G) := ({L₁, L₂, L₃} : Set (Subgroup G))
  have hS : ∀ d : ↥D, ∀ L ∈ S, L.map (MulAut.conj (d : G)).toMonoidHom ∈ S :=
    fun d L hL => hc.data.map_conj_mem (hDM d.2) hL
  let B : Subgroup G := (blockAction D S hS).ker.map D.subtype
  have hBD : B ≤ D := Subgroup.map_subtype_le _
  have hBcard : Nat.card ↥B = Nat.card ↥(blockAction D S hS).ker :=
    Subgroup.card_map_of_injective D.subtype_injective
  refine ⟨B, hBD.trans hDM, hD3.to_le hBD, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subtype.ext (by simpa using congrArg Subtype.val (hDpow k))
  · rw [hBcard]
    exact blockAction_ker_card_ge hS hDcard (nat_card_set_three_le L₁ L₂ L₃)
  · exact blockAction_ker_normalizes hS (by simp [S])
  · exact blockAction_ker_normalizes hS (by simp [S])
  · exact blockAction_ker_normalizes hS (by simp [S])

private theorem pRank_two_of_zpowers {Y : Type} [Group Y] [Finite Y] {w₁ w₂ : Y}
    (h1 : orderOf w₁ = 3) (h2 : orderOf w₂ = 3) (hc : Commute w₁ w₂)
    (hd : Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂ = ⊥) :
    CFSG.Open.pRank 3 (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) = 2 := by
  have hc' : Subgroup.zpowers w₁ ≤ Subgroup.centralizer (Subgroup.zpowers w₂ : Set Y) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc
  have hnot : ¬ 3 ∣ Nat.card ↥(Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂) := by
    rw [hd, Subgroup.card_bot]
    norm_num
  rw [CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd (p := 3)
    Nat.prime_three hc' hnot,
    pRank_zpowers_of_orderOf_eq_three h1, pRank_zpowers_of_orderOf_eq_three h2]

private theorem pRank_three_of_zpowers {Y : Type} [Group Y] [Finite Y] {w₁ w₂ w₃ : Y}
    (h1 : orderOf w₁ = 3) (h2 : orderOf w₂ = 3) (h3 : orderOf w₃ = 3)
    (hc12 : Commute w₁ w₂) (hc13 : Commute w₁ w₃) (hc23 : Commute w₂ w₃)
    (hd12 : Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂ = ⊥)
    (hd123 : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ⊓ Subgroup.zpowers w₃ = ⊥) :
    CFSG.Open.pRank 3 (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔ Subgroup.zpowers w₃) = 3 := by
  have hcW : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ≤
      Subgroup.centralizer (Subgroup.zpowers w₃ : Set Y) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hc13
    · refine Subgroup.zpowers_le.mpr ?_
      rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hc23
  have hnot : ¬ 3 ∣ Nat.card ↥((Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ⊓
      Subgroup.zpowers w₃) := by
    rw [hd123, Subgroup.card_bot]
    norm_num
  rw [CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd (p := 3)
    Nat.prime_three hcW hnot, pRank_two_of_zpowers h1 h2 hc12 hd12,
    pRank_zpowers_of_orderOf_eq_three h3]

private theorem four_le_pRank_of_zpowers {Y : Type} [Group Y] [Finite Y] {z w₁ w₂ w₃ : Y}
    (hz : orderOf z = 3) (h1 : orderOf w₁ = 3) (h2 : orderOf w₂ = 3) (h3 : orderOf w₃ = 3)
    (hz1 : Commute z w₁) (hz2 : Commute z w₂) (hz3 : Commute z w₃)
    (h12 : Commute w₁ w₂) (h13 : Commute w₁ w₃) (h23 : Commute w₂ w₃)
    (hd12 : Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂ = ⊥)
    (hd123 : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ⊓ Subgroup.zpowers w₃ = ⊥)
    (hdz : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔ Subgroup.zpowers w₃) ⊓
      Subgroup.zpowers z = ⊥) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have hcW : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔ Subgroup.zpowers w₃) ≤
      Subgroup.centralizer (Subgroup.zpowers z : Set Y) := by
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hz1.symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hz2.symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hz3.symm
  have hnot : ¬ 3 ∣ Nat.card ↥((Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔
      Subgroup.zpowers w₃) ⊓ Subgroup.zpowers z) := by
    rw [hdz, Subgroup.card_bot]
    norm_num
  have hrank : CFSG.Open.pRank 3 ((Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔
      Subgroup.zpowers w₃) ⊔ Subgroup.zpowers z) = 4 := by
    rw [CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd (p := 3)
      Nat.prime_three hcW hnot, pRank_three_of_zpowers h1 h2 h3 h12 h13 h23 hd12 hd123,
      pRank_zpowers_of_orderOf_eq_three hz]
  calc 4 = CFSG.Open.pRank 3 ((Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔
        Subgroup.zpowers w₃) ⊔ Subgroup.zpowers z) := hrank.symm
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
        CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top

private theorem barM_inf_barM_eq_bot {M A B : Subgroup G}
    (hc : barM M A ≤ Subgroup.centralizer (barM M B : Set _))
    (hZ : Subgroup.center ↥(barM M B) = ⊥) : barM M A ⊓ barM M B = ⊥ := by
  refine le_bot_iff.mp ?_
  calc barM M A ⊓ barM M B
      ≤ barM M B ⊓ Subgroup.centralizer (barM M B : Set _) :=
        le_inf inf_le_right (fun x hx => hc hx.1)
    _ = ⊥ := by
        rw [← CFSG.center_map_subtype_eq_inf_centralizer (barM M B), hZ, Subgroup.map_bot]

private theorem barM_sup_inf_barM_eq_bot {M A B C : Subgroup G}
    (hc : barM M A ⊔ barM M B ≤ Subgroup.centralizer (barM M C : Set _))
    (hZ : Subgroup.center ↥(barM M C) = ⊥) : (barM M A ⊔ barM M B) ⊓ barM M C = ⊥ := by
  refine le_bot_iff.mp ?_
  calc (barM M A ⊔ barM M B) ⊓ barM M C
      ≤ barM M C ⊓ Subgroup.centralizer (barM M C : Set _) :=
        le_inf inf_le_right (fun x hx => hc hx.1)
    _ = ⊥ := by
        rw [← CFSG.center_map_subtype_eq_inf_centralizer (barM M C), hZ, Subgroup.map_bot]

theorem TwelveSixKCtx.barM_blocks_independent
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    barM M L₁ ⊓ barM M L₂ = ⊥ ∧ barM M L₁ ⊓ barM M L₃ = ⊥ ∧
      barM M L₂ ⊓ barM M L₃ = ⊥ ∧ (barM M L₁ ⊔ barM M L₂) ⊓ barM M L₃ = ⊥ := by
  have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
  have hZ₁ : Subgroup.center ↥(barM M L₁) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hc.data.mem₁.toIsTwoPrimeComponent
      ⟨n₁, hc.data.odd₁, hc.data.type₁⟩
  have hZ₂ : Subgroup.center ↥(barM M L₂) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hc.data.mem₂.toIsTwoPrimeComponent
      ⟨n₂, hc.data.odd₂, hc.data.type₂⟩
  have hZ₃ : Subgroup.center ↥(barM M L₃) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hc.data.mem₃.toIsTwoPrimeComponent
      ⟨n₃, hc.data.odd₃, hc.data.type₃⟩
  refine ⟨barM_inf_barM_eq_bot ?_ hZ₂, barM_inf_barM_eq_bot ?_ hZ₃,
    barM_inf_barM_eq_bot ?_ hZ₃, barM_sup_inf_barM_eq_bot ?_ hZ₃⟩
  · exact barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₂ hne.1
  · exact barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₃ hne.2.1
  · exact barM_le_centralizer_barM_of_ne hc.data.mem₂ hc.data.mem₃ hne.2.2
  · exact sup_le (barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₃ hne.2.1)
      (barM_le_centralizer_barM_of_ne hc.data.mem₂ hc.data.mem₃ hne.2.2)

private theorem zpowers_inf_barM_jSub_eq_bot {z : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hz : orderOf z = 3) (hzJ : z ∉ barM M (jSub M H)) :
    Subgroup.zpowers z ⊓ barM M (jSub M H) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro x hx
  by_contra hx1
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hz]
      exact orderOf_dvd_of_mem_zpowers hx.1
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hx.1
  have heq : Subgroup.zpowers x = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hxle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hz])
  have hxJ : Subgroup.zpowers x ≤ barM M (jSub M H) := Subgroup.zpowers_le.mpr hx.2
  rw [heq] at hxJ
  exact hzJ (hxJ (Subgroup.mem_zpowers z))

private theorem zpowers_inf_zpowers_eq_bot {Y : Type} [Group Y] {A B : Subgroup Y} {w₁ w₂ : Y}
    (h1 : w₁ ∈ A) (h2 : w₂ ∈ B) (hd : A ⊓ B = ⊥) :
    Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂ = ⊥ :=
  le_bot_iff.mp ((inf_le_inf (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)).trans
    (le_of_eq hd))

private theorem sup_zpowers_inf_zpowers_eq_bot {Y : Type} [Group Y] {A B C : Subgroup Y}
    {w₁ w₂ w₃ : Y} (h1 : w₁ ∈ A) (h2 : w₂ ∈ B) (h3 : w₃ ∈ C) (hd : (A ⊔ B) ⊓ C = ⊥) :
    (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ⊓ Subgroup.zpowers w₃ = ⊥ :=
  le_bot_iff.mp ((inf_le_inf (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left h1))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right h2)))
    (Subgroup.zpowers_le.mpr h3)).trans (le_of_eq hd))

private theorem inf_eq_bot_of_le_of_inf_eq_bot {Y : Type} [Group Y] {A B z : Subgroup Y}
    (hA : A ≤ B) (hz : B ⊓ z = ⊥) : A ⊓ z = ⊥ :=
  le_bot_iff.mp ((inf_le_inf hA le_rfl).trans (le_of_eq hz))

private theorem false_of_fixed_points (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {z w₁ w₂ w₃ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hz : orderOf z = 3) (h1 : orderOf w₁ = 3) (h2 : orderOf w₂ = 3) (h3 : orderOf w₃ = 3)
    (h1L : w₁ ∈ barM M L₁) (h2L : w₂ ∈ barM M L₂) (h3L : w₃ ∈ barM M L₃)
    (hzJ : z ∉ barM M (jSub M H))
    (hz1 : Commute z w₁) (hz2 : Commute z w₂) (hz3 : Commute z w₃)
    (h12 : Commute w₁ w₂) (h13 : Commute w₁ w₃) (h23 : Commute w₂ w₃) : False := by
  obtain ⟨hd12, -, -, hd123⟩ := hc.barM_blocks_independent
  have hWJ : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔ Subgroup.zpowers w₃) ≤
      barM M (jSub M H) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (barM_mono (le_jSub hc.data.mem₁) h1L))
      (Subgroup.zpowers_le.mpr (barM_mono (le_jSub hc.data.mem₂) h2L)))
      (Subgroup.zpowers_le.mpr (barM_mono (le_jSub hc.data.mem₃) h3L))
  have hZJ := zpowers_inf_barM_jSub_eq_bot hz hzJ
  have hW12 : Subgroup.zpowers w₁ ⊓ Subgroup.zpowers w₂ = ⊥ :=
    zpowers_inf_zpowers_eq_bot h1L h2L hd12
  have hW123 : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) ⊓ Subgroup.zpowers w₃ = ⊥ :=
    sup_zpowers_inf_zpowers_eq_bot h1L h2L h3L hd123
  have hWZ : (Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ ⊔ Subgroup.zpowers w₃) ⊓
      Subgroup.zpowers z = ⊥ :=
    inf_eq_bot_of_le_of_inf_eq_bot hWJ (by rw [inf_comm]; exact hZJ)
  have h4 := four_le_pRank_of_zpowers hz h1 h2 h3 hz1 hz2 hz3 h12 h13 h23 hW12 hW123 hWZ
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) =
      CFSG.Open.pRank 3 M := by
    rw [CFSG.SectionRank.pRank_quotient_two_group (CFSG.pCore 2 ↥M)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) Nat.prime_three (by norm_num)]
    exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup M).symm
  rw [htop] at h4
  have h3M : CFSG.Open.pRank 3 M ≤ 3 := hc.h3
  omega

private theorem orderOf_barM_eq_three {B : Subgroup G} (hBM : B ≤ M)
    (hBpow : ∀ x : ↥B, x ^ 3 = 1) {b : G} (hb : b ∈ B)
    (hzJ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩ ∉ barM M (jSub M H)) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩) = 3 := by
  have hb3G : b ^ 3 = 1 := by
    have := congrArg Subtype.val (hBpow ⟨b, hb⟩)
    simpa using this
  have hz3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h : (⟨b, hBM hb⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3G)
    rw [h, map_one]
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hz3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (by
      intro h1
      exact hzJ (h1 ▸ (barM M (jSub M H)).one_mem))
  · exact h

private theorem mem_barM_jSub_of_mem (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {B : Subgroup G} (hBM : B ≤ M)
    (hBpow : ∀ x : ↥B, x ^ 3 = 1) (hBN₁ : B ≤ Subgroup.normalizer (L₁ : Set G))
    (hBN₂ : B ≤ Subgroup.normalizer (L₂ : Set G))
    (hBN₃ : B ≤ Subgroup.normalizer (L₃ : Set G)) {b : G} (hb : b ∈ B) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩ ∈ barM M (jSub M H) := by
  by_contra hzJ
  have hz : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hBM hb⟩) = 3 :=
    orderOf_barM_eq_three hBM hBpow hb hzJ
  have hb3G : b ^ 3 = 1 := by
    have := congrArg Subtype.val (hBpow ⟨b, hb⟩)
    simpa using this
  obtain ⟨w₁, hw₁ord, hw₁comm⟩ := exists_orderOf_three_commute (M := M) (L := L₁) (n := n₁)
    (hBM hb) (hBN₁ hb) hb3G hc.data.mem₁.toIsTwoPrimeComponent hc.data.type₁
  obtain ⟨w₂, hw₂ord, hw₂comm⟩ := exists_orderOf_three_commute (M := M) (L := L₂) (n := n₂)
    (hBM hb) (hBN₂ hb) hb3G hc.data.mem₂.toIsTwoPrimeComponent hc.data.type₂
  obtain ⟨w₃, hw₃ord, hw₃comm⟩ := exists_orderOf_three_commute (M := M) (L := L₃) (n := n₃)
    (hBM hb) (hBN₃ hb) hb3G hc.data.mem₃.toIsTwoPrimeComponent hc.data.type₃
  have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
  have h12 : Commute ((w₁ : ↥M ⧸ CFSG.pCore 2 ↥M)) ((w₂ : ↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have hcc := barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₂ hne.1
    exact ((Subgroup.mem_centralizer_iff.mp (hcc w₁.2)) _ w₂.2).symm
  have h13 : Commute ((w₁ : ↥M ⧸ CFSG.pCore 2 ↥M)) ((w₃ : ↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have hcc := barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₃ hne.2.1
    exact ((Subgroup.mem_centralizer_iff.mp (hcc w₁.2)) _ w₃.2).symm
  have h23 : Commute ((w₂ : ↥M ⧸ CFSG.pCore 2 ↥M)) ((w₃ : ↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have hcc := barM_le_centralizer_barM_of_ne hc.data.mem₂ hc.data.mem₃ hne.2.2
    exact ((Subgroup.mem_centralizer_iff.mp (hcc w₂.2)) _ w₃.2).symm
  exact false_of_fixed_points hc hz (by rw [Subgroup.orderOf_coe, hw₁ord])
    (by rw [Subgroup.orderOf_coe, hw₂ord]) (by rw [Subgroup.orderOf_coe, hw₃ord])
    w₁.2 w₂.2 w₃.2 hzJ hw₁comm hw₂comm hw₃comm h12 h13 h23

private theorem pow_eq_one_barM_of_forall {B : Subgroup G} (hBM : B ≤ M)
    (h : ∀ x : ↥B, x ^ 3 = 1) : ∀ y : ↥(barM M B), y ^ 3 = 1 := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyB : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
  have h3 : (y : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (h ⟨(y : G), hyB⟩)
  have hyM3 : (y : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  refine Subtype.ext ?_
  show ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) y) ^ 3 = 1
  rw [← map_pow, hyM3, map_one]

private theorem card_barM_le_twenty_seven (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {B : Subgroup G} (hBM : B ≤ M) (hB3 : IsPGroup 3 B)
    (hBpow : ∀ x : ↥B, x ^ 3 = 1) (hBJ : barM M B ≤ barM M (jSub M H)) :
    Nat.card ↥(barM M B) ≤ 27 := by
  obtain ⟨hd12, -, -, hd123⟩ := hc.barM_blocks_independent
  have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
  have hBbar3 : IsPGroup 3 (barM M B) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB3
    exact IsPGroup.iff_card.mpr ⟨k, by
      rw [CFSG.AGLEmbedding.card_barM_of_isPGroup Nat.prime_three (by norm_num) hBM hB3]
      exact hk⟩
  have hBbar_exp : ∀ x : ↥(barM M B), x ^ 3 = 1 := pow_eq_one_barM_of_forall hBM hBpow
  have hcA : barM M L₁ ⊔ barM M L₂ ≤ Subgroup.centralizer (barM M L₃ : Set _) :=
    sup_le (barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₃ hne.2.1)
      (barM_le_centralizer_barM_of_ne hc.data.mem₂ hc.data.mem₃ hne.2.2)
  have hcA' : barM M L₁ ≤ Subgroup.centralizer (barM M L₂ : Set _) :=
    barM_le_centralizer_barM_of_ne hc.data.mem₁ hc.data.mem₂ hne.1
  have hleH : barM M B ≤ (barM M L₁ ⊔ barM M L₂) ⊔ barM M L₃ := by
    rw [← TwelveFiveData.barM_jSub_eq hc.data]
    exact hBJ
  obtain ⟨H', hH'A, hH'p, hH'exp, hcard1⟩ :=
    exists_left_card_le_of_le_sup hcA hd123 hleH hBbar3 hBbar_exp
      (hc.hm3 L₃ hc.data.mem₃).le
  obtain ⟨H'', hH''A, hH''p, hH''exp, hcard2⟩ :=
    exists_left_card_le_of_le_sup hcA' hd12 hH'A hH'p hH'exp
      (hc.hm3 L₂ hc.data.mem₂).le
  have hH''card : Nat.card ↥H'' ≤ 3 :=
    card_le_three_of_isPGroup_of_pow_eq_one hH''p hH''exp
      ((CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hH''A).trans
        (hc.hm3 L₁ hc.data.mem₁).le)
  calc Nat.card ↥(barM M B) ≤ 3 * Nat.card ↥H' := hcard1
    _ ≤ 3 * (3 * Nat.card ↥H'') := Nat.mul_le_mul_left 3 hcard2
    _ ≤ 3 * (3 * 3) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 3 hH''card)
    _ = 27 := by norm_num

theorem TwelveSixKCtx.not_extraspecial (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 3 R) :
    ¬ (CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
        Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3) := by
  classical
  rintro ⟨-, hDcard, hDexp⟩
  set D : Subgroup G := omegaOnePSub 3 R with hDdef
  have hDcard' : Nat.card ↥D = 3 ^ 5 := by rw [hDdef]; exact hDcard
  have hDR : D ≤ R := by
    rw [hDdef, omegaOnePSub]
    exact (Subgroup.closure_le R).2 fun x hx => hx.1
  have hDM : D ≤ M := hDR.trans hRM
  have hD3 : IsPGroup 3 D := hR.to_le hDR
  have hDpow : ∀ x : ↥D, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hDexp])
  obtain ⟨B, hBM, hB3, hBpow, hB81, hBN₁, hBN₂, hBN₃⟩ :=
    exists_kernel_subgroup hc hDM hD3 hDpow hDcard'
  have hBJ : barM M B ≤ barM M (jSub M H) := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_barM_jSub_of_mem hc hBM hBpow hBN₁ hBN₂ hBN₃
      (Subgroup.mem_subgroupOf.mp hy)
  have h27 := card_barM_le_twenty_seven hc hBM hB3 hBpow hBJ
  have hBbar_card : Nat.card ↥(barM M B) = Nat.card ↥B :=
    CFSG.AGLEmbedding.card_barM_of_isPGroup Nat.prime_three (by norm_num) hBM hB3
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
