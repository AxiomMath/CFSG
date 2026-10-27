module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem pRank_add_le_pRank_sup_of_commute_aux_bot {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q (⊥ : Subgroup Y) = 0 := by
  refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le hq.one_lt fun E hE _ => ?_)
  rw [le_bot_iff.1 hE]
  simp

theorem pRank_add_le_pRank_sup_of_commute {q : ℕ} (hq : q.Prime) {A B : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    CFSG.Open.pRank q A + CFSG.Open.pRank q B ≤ CFSG.Open.pRank q (A ⊔ B) := by
  have h := pRank_add_le_pRank_sup_add_pRank_inf hcomm hq
  rwa [hAB, pRank_add_le_pRank_sup_of_commute_aux_bot hq, add_zero] at h

theorem nonTrans_of_normal_aux_le_pElement {E : Subgroup Y} (hE : IsPGroup 3 E) :
    E ≤ pElementSubgroup 3 (⊤ : Subgroup Y) := by
  intro x hx
  obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
  have hxk : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hxk)
  exact Subgroup.subset_closure ⟨mem_top x, j, hj⟩

theorem nonTrans_of_normal {S : Subgroup Y} [S.Normal]
    (hle : pElementSubgroup 3 (⊤ : Subgroup Y) ≤ S)
    (hS : ∀ E : Subgroup ↥S, IsElemAbelian 3 E → Nat.card E = 9 → ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧
      ∀ φ : MulAut ↥S, E.map φ.toMonoidHom = E → φ a ≠ b) :
    ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 9 → NonTrans1517 E := by
  intro E hE hcard
  have hES : E ≤ S := (nonTrans_of_normal_aux_le_pElement hE.isPGroup).trans hle
  have hcard' : Nat.card (E.subgroupOf S) = 9 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  obtain ⟨a, ha, b, hb, ha1, hb1, hφ⟩ := hS _ (hE.subgroupOf S) hcard'
  refine ⟨(a : Y), ha, (b : Y), hb, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h), ?_⟩
  intro g hg hgab
  refine hφ (MulAut.conjNormal g) ?_ (Subtype.ext ?_)
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : Y) ∈ E := hy
      show g * (y : Y) * g⁻¹ ∈ E
      exact (Subgroup.mem_normalizer_iff.1 hg _).1 hy'
    · intro hx
      have hx' : (x : Y) ∈ E := hx
      refine ⟨(MulAut.conjNormal g)⁻¹ x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_inv_apply]
      refine (Subgroup.mem_normalizer_iff.1 hg _).2 ?_
      have : g * (g⁻¹ * (x : Y) * g) * g⁻¹ = x := by group
      rw [this]
      exact hx'
  · rw [MulAut.conjNormal_apply]
    exact hgab

theorem out1517_of_data421_aux_card_le {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {E N : Subgroup G} (hE : IsElemAbelian p E) (hEN : E ≤ N) :
    Nat.card E ≤ p ^ CFSG.Open.pRank p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.le_pRank hp.one_lt hEN hE hk)

theorem out1517_of_data421_aux_pRank_map_le {p : ℕ} (hp : p.Prime) {A B : Type*} [Group A]
    [Finite A] [Group B] [Finite B] (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    CFSG.Open.pRank p (H.map f) ≤ CFSG.Open.pRank p H := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEH hE => ?_
  have hE' : IsElemAbelian p (E.comap f) := hE.comap hf
  have hle : E.comap f ≤ H := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hEH hx
    rw [← hf hyx]
    exact hy
  have hmap : (E.comap f).map f = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact hEH.trans (Subgroup.map_le_range f H)
  calc Nat.card E = Nat.card ((E.comap f).map f) := by rw [hmap]
    _ = Nat.card (E.comap f) := Subgroup.card_map_of_injective hf
    _ ≤ p ^ CFSG.Open.pRank p H := out1517_of_data421_aux_card_le hp hE' hle

theorem out1517_of_data421_aux_card_le_sup {p : ℕ} (hp : p.Prime) {S C : Subgroup Y} [S.Normal]
    (hSC : S ⊓ C = ⊥) {E : Subgroup Y} (hE : IsElemAbelian p E) (hEH : E ≤ S ⊔ C) :
    Nat.card E ≤ p ^ (CFSG.Open.pRank p S + CFSG.Open.pRank p C) := by
  let q : Y →* Y ⧸ S := QuotientGroup.mk' S
  have hcard : Nat.card E = Nat.card (E.map q) * Nat.card (E ⊓ S : Subgroup Y) := by
    have h := Subgroup.relIndex_mul_card q.ker E
    rw [Subgroup.relIndex_ker, inf_comm, QuotientGroup.ker_mk'] at h
    exact h.symm
  have h1 : Nat.card (E ⊓ S : Subgroup Y) ≤ p ^ CFSG.Open.pRank p S :=
    out1517_of_data421_aux_card_le hp (hE.mono inf_le_left) inf_le_right
  let g : ↥C →* Y ⧸ S := q.comp C.subtype
  have hg : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h2 : (x : Y) ∈ S := (QuotientGroup.eq_one_iff _).1 hx
    have h3 : (x : Y) ∈ S ⊓ C := ⟨h2, x.2⟩
    rw [hSC, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  have hmapC : (⊤ : Subgroup ↥C).map g = C.map q := by
    rw [show (⊤ : Subgroup ↥C).map g = ((⊤ : Subgroup ↥C).map C.subtype).map q from
      (Subgroup.map_map _ _ _).symm, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hEq : E.map q ≤ C.map q := by
    have h4 : (S ⊔ C).map q = C.map q := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk']),
        bot_sup_eq]
    exact h4 ▸ Subgroup.map_mono hEH
  have h5 : Nat.card (E.map q) ≤ p ^ CFSG.Open.pRank p C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    calc Nat.card (E.map q) ≤ p ^ CFSG.Open.pRank p ((⊤ : Subgroup ↥C).map g) :=
          out1517_of_data421_aux_card_le hp (hE.map q) (hmapC ▸ hEq)
      _ ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
          Nat.pow_le_pow_right hp.pos (out1517_of_data421_aux_pRank_map_le hp g hg ⊤)
  calc Nat.card E = Nat.card (E.map q) * Nat.card (E ⊓ S : Subgroup Y) := hcard
    _ ≤ p ^ CFSG.Open.pRank p C * p ^ CFSG.Open.pRank p S := Nat.mul_le_mul h5 h1
    _ = p ^ (CFSG.Open.pRank p S + CFSG.Open.pRank p C) := by rw [pow_add, mul_comm]

theorem out1517_of_data421_aux_mem_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Y}
    [S.Normal]
    (hOut : ∀ φ : MulAut ↥S, ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : ↥S →* MulAut ↥S).range)
    {y : Y} (hy : y ^ p = 1) : y ∈ S ⊔ Subgroup.centralizer (S : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have ho : orderOf y = p := orderOf_eq_prime hy hy1
  obtain ⟨k, s, hs⟩ := hOut (MulAut.conjNormal y)
  have h1 : MulAut.conjNormal (y ^ (2 ^ k)) = (MulAut.conjNormal (s : Y) : MulAut ↥S) := by
    rw [map_pow, MulAut.conjNormal_val, hs]
  have hc : (s : Y)⁻¹ * y ^ (2 ^ k) ∈ Subgroup.centralizer (S : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h2 := congrArg (fun φ : MulAut ↥S => (φ ⟨t, ht⟩ : Y)) h1
    simp only [MulAut.conjNormal_apply] at h2
    calc t * ((s : Y)⁻¹ * y ^ (2 ^ k))
        = (s : Y)⁻¹ * (s * t * (s : Y)⁻¹) * y ^ (2 ^ k) := by group
      _ = (s : Y)⁻¹ * (y ^ (2 ^ k) * t * (y ^ (2 ^ k))⁻¹) * y ^ (2 ^ k) := by rw [h2]
      _ = (s : Y)⁻¹ * y ^ (2 ^ k) * t := by group
  have hmem : y ^ (2 ^ k) ∈ S ⊔ Subgroup.centralizer (S : Set Y) := by
    have : y ^ (2 ^ k) = (s : Y) * ((s : Y)⁻¹ * y ^ (2 ^ k)) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right hc)
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) := by
    rw [ho]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hmem m

theorem out1517_of_data421_aux_inf_centralizer {S : Subgroup Y} (hZ : Subgroup.center ↥S = ⊥) :
    S ⊓ Subgroup.centralizer (S : Set Y) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have hxc : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 g g.2)
  rw [hZ, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxc)

theorem out1517_of_data421_aux_three_le_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup Y} [S.Normal] (hZ : Subgroup.center ↥S = ⊥)
    (hpY : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y))
    (hOut : CFSG.Open.pRank p (⊤ : Subgroup ↥S) = 3 ∨
      ∀ φ : MulAut ↥S, ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : ↥S →* MulAut ↥S).range) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥S) +
      CFSG.Open.pRank p (Subgroup.centralizer (S : Set Y)) := by
  rcases hOut with h | h
  · omega
  · obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup Y)
    have hEH : E ≤ S ⊔ Subgroup.centralizer (S : Set Y) := fun x hx =>
      out1517_of_data421_aux_mem_sup hp hp2 h (hE.2 x hx)
    have h1 := out1517_of_data421_aux_card_le_sup hp
      (out1517_of_data421_aux_inf_centralizer hZ) hE hEH
    rw [hcard] at h1
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup S] at h2
    omega

theorem out1517_of_data421_aux_map_centralizer {S D : Subgroup Y} (hDS : D ≤ S) :
    (Subgroup.centralizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S)).map S.subtype ≤
      Subgroup.centralizer (D : Set Y) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hz ⟨d, hDS hd⟩ hd)

theorem out1517_of_data421_aux_not_isPSolvable {p : ℕ} (hp : p.Prime) {S D : Subgroup Y}
    (hDS : D ≤ S)
    (h : ¬ CFSG.HallHigman.IsPSolvable p
      ↥(Subgroup.centralizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S))) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer (D : Set Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hsolv
  refine h ?_
  have h1 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    hsolv (out1517_of_data421_aux_map_centralizer hDS)
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).symm h1

theorem out1517_of_data421_aux_rank_centralizer {p : ℕ} (hp : p.Prime) {S D : Subgroup Y}
    (hZ : Subgroup.center ↥S = ⊥) (hDS : D ≤ S) :
    CFSG.Open.pRank p (Subgroup.centralizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S)) +
      CFSG.Open.pRank p (Subgroup.centralizer (S : Set Y)) ≤
      CFSG.Open.pRank p (Subgroup.centralizer (D : Set Y)) := by
  set CS := (Subgroup.centralizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S)).map S.subtype with hCS
  have hCSS : CS ≤ S := Subgroup.map_subtype_le _
  have h1 : CFSG.Open.pRank p (Subgroup.centralizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S)) ≤
      CFSG.Open.pRank p CS :=
    CFSG.SectionRank.pRank_le_map hp.one_lt S.subtype S.subtype_injective _
  have hcomm : ∀ a ∈ CS, ∀ b ∈ Subgroup.centralizer (S : Set Y), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a (hCSS ha)
  have hinf : CS ⊓ Subgroup.centralizer (S : Set Y) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ S ⊓ Subgroup.centralizer (S : Set Y) := ⟨hCSS hx.1, hx.2⟩
    rwa [out1517_of_data421_aux_inf_centralizer hZ] at hx'
  have h2 := pRank_add_le_pRank_sup_of_commute hp hcomm hinf
  have h3 : CS ⊔ Subgroup.centralizer (S : Set Y) ≤ Subgroup.centralizer (D : Set Y) :=
    sup_le (out1517_of_data421_aux_map_centralizer hDS)
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDS))
  exact (Nat.add_le_add_right h1 _).trans (h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt h3))

theorem out1517_of_data421_aux_isSylowOf_of_le {p : ℕ} (hp : p.Prime) {P K N : Subgroup Y}
    (h : CFSG.ABGLocalTools.IsSylowOf p P N) (hPK : P ≤ K) (hKN : K ≤ N) :
    CFSG.ABGLocalTools.IsSylowOf p P K := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, hP, hdvd⟩ := h
  exact ⟨hPK, hP, fun hd => hdvd (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex P K N hPK hKN)))⟩

theorem out1517_of_data421_aux_isSylowOf_subgroupOf {p : ℕ} (hp : p.Prime) {P K S : Subgroup Y}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (hKS : K ≤ S) :
    CFSG.ABGLocalTools.IsSylowOf p (P.subgroupOf S) (K.subgroupOf S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hPK, hP, hdvd⟩ := h
  exact ⟨Subgroup.comap_mono hPK, hP.comap_subtype, by
    rwa [Subgroup.relIndex_subgroupOf hKS]⟩

theorem out1517_of_data421_aux_normalizer_subgroupOf {S D : Subgroup Y} (hDS : D ≤ S) :
    Subgroup.normalizer ((D.subgroupOf S : Subgroup ↥S) : Set ↥S) =
      (Subgroup.normalizer (D : Set Y)).subgroupOf S := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ S
    · exact h ⟨y, hy⟩
    · refine ⟨fun hyD => absurd (hDS hyD) hy, fun hxy => absurd ?_ hy⟩
      have hS := S.mul_mem (S.mul_mem (S.inv_mem x.2) (hDS hxy)) x.2
      have : (x : Y)⁻¹ * ((x : Y) * y * (x : Y)⁻¹) * (x : Y) = y := by group
      rwa [this] at hS
  · intro h y
    exact h y

theorem out1517_of_data421_aux_sylowShape {S D : Subgroup Y} (hDS : D ≤ S)
    (hle : ∀ P : Subgroup Y, IsPGroup 3 P → P ≤ S)
    (h : SylowShape1517 (D.subgroupOf S)) : SylowShape1517 D := by
  intro P hP
  have hPS : P ≤ S := hle P hP.isPGroup
  have hPK : P ≤ Subgroup.normalizer (D : Set Y) ⊓ S := le_inf hP.le hPS
  have hP1 := out1517_of_data421_aux_isSylowOf_of_le Nat.prime_three hP hPK inf_le_left
  have hP2 := out1517_of_data421_aux_isSylowOf_subgroupOf Nat.prime_three hP1 (inf_le_right)
  rw [Subgroup.inf_subgroupOf_right, ← out1517_of_data421_aux_normalizer_subgroupOf hDS] at hP2
  have hmap : (P.subgroupOf S).map S.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPS]
  let e : ↥(P.subgroupOf S) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPS
  obtain ⟨hshape, hrk⟩ := h _ hP2
  have hrank : 3 ≤ CFSG.Open.pRank 3 P := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) S.subtype S.subtype_injective
      (P.subgroupOf S)
    rw [hmap] at h1
    exact hrk.trans h1
  refine ⟨?_, hrank⟩
  rcases hshape with ⟨hel, hcard⟩ | hcyc
  · refine Or.inl ⟨?_, ?_⟩
    · have := hel.map S.subtype
      rwa [hmap] at this
    · rw [← hcard]
      exact (Nat.card_congr e.toEquiv).symm
  · refine Or.inr ?_
    haveI := hcyc
    exact isCyclic_of_surjective _ (Subgroup.centerCongr e).surjective

theorem out1517_of_data421_of_rank (hK4143 : K4143) {p : ℕ} (hp : p.Prime)
    {S : Subgroup Y} [S.Normal] (hq : CFSG.Open.IsQuasisimple ↥S)
    (hZ : Subgroup.center ↥S = ⊥) (hshape : IsK4143Shape ↥S)
    (h3S : CFSG.Open.pRank 3 S = 3) (h3Y : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 3)
    (he : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥S) +
      CFSG.Open.pRank p (Subgroup.centralizer (S : Set Y)))
    (hD : Data421 ↥S p) : Out1517 Y p ∧ pElementSubgroup 3 (⊤ : Subgroup Y) ≤ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : pElementSubgroup 3 (⊤ : Subgroup Y) ≤ S := hK4143 Y S inferInstance hq hZ hshape h3S h3Y
  refine ⟨?_, hle⟩
  have hP3 : ∀ P : Subgroup Y, IsPGroup 3 P → P ≤ S := fun P hP =>
    (nonTrans_of_normal_aux_le_pElement hP).trans hle
  have hD3 : ∀ D : Subgroup Y, Nat.card D = 3 → D ≤ S := fun D hDc =>
    hP3 D (IsPGroup.of_card (n := 1) (by rw [hDc]; norm_num))
  have hcardsub : ∀ D : Subgroup Y, D ≤ S → Nat.card (D.subgroupOf S) = Nat.card D :=
    fun D hDS => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv
  have key : ∀ D : Subgroup Y, Nat.card D = 3 →
      (2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set Y)) ∧
        ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer (D : Set Y))) ∨
      (SylowShape1517 D ∧ 1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set Y))) := by
    intro D hDc
    have hDS := hD3 D hDc
    have hrank := out1517_of_data421_aux_rank_centralizer hp hZ hDS
    rcases hD.each (D.subgroupOf S) (by rw [hcardsub D hDS]; exact hDc) with ⟨h2, hns⟩ | ⟨hsh, h1⟩
    · exact Or.inl ⟨by omega, out1517_of_data421_aux_not_isPSolvable hp hDS hns⟩
    · exact Or.inr ⟨out1517_of_data421_aux_sylowShape hDS hP3 hsh, by omega⟩
  refine ⟨fun D hDc => ?_, fun E hE hE9 => ?_, fun D hDc hnot => ?_⟩
  · have h1 : 1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set Y)) := by
      rcases key D hDc with ⟨h2, -⟩ | ⟨-, h1⟩ <;> omega
    obtain ⟨F, hFC, hF, hFcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.centralizer (D : Set Y))
    have hdvd : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p (by omega)
    exact hdvd.trans (Subgroup.card_dvd_of_le hFC)
  · have hES : E ≤ S := hP3 E hE.isPGroup
    have hE9' : Nat.card (E.subgroupOf S) = 9 := by rw [hcardsub E hES]; exact hE9
    obtain ⟨D', hD'E, hD'3, h2, hns⟩ := hD.caseA _ (hE.subgroupOf S) hE9'
    have hDS : D'.map S.subtype ≤ S := Subgroup.map_subtype_le D'
    have hsub : (D'.map S.subtype).subgroupOf S = D' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective D'
    have hDc : Nat.card (D'.map S.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective S.subtype_injective]
      exact hD'3
    have hDE : D'.map S.subtype ≤ E := by
      rintro _ ⟨z, hz, rfl⟩
      exact hD'E hz
    have hrank := out1517_of_data421_aux_rank_centralizer hp hZ hDS
    rw [hsub] at hrank
    refine ⟨D'.map S.subtype, hDE, hDc, ?_, ?_⟩
    · omega
    · exact out1517_of_data421_aux_not_isPSolvable hp hDS (by rw [hsub]; exact hns)
  · rcases key D hDc with ⟨h2, hns⟩ | ⟨hsh, -⟩
    · exact absurd ⟨hDc, h2, hns⟩ hnot
    · exact hsh

theorem out1517_of_data421_of_ne_two_gen (hK4143 : K4143) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup Y} [S.Normal] (hq : CFSG.Open.IsQuasisimple ↥S)
    (hZ : Subgroup.center ↥S = ⊥) (hshape : IsK4143Shape ↥S)
    (h3S : CFSG.Open.pRank 3 S = 3) (h3Y : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 3)
    (hpY : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y))
    (hOut : CFSG.Open.pRank p (⊤ : Subgroup ↥S) = 3 ∨
      ∀ φ : MulAut ↥S, ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : ↥S →* MulAut ↥S).range)
    (hD : Data421 ↥S p) : Out1517 Y p ∧ pElementSubgroup 3 (⊤ : Subgroup Y) ≤ S :=
  out1517_of_data421_of_rank hK4143 hp hq hZ hshape h3S h3Y
    (out1517_of_data421_aux_three_le_gen hp hp2 hZ hpY hOut) hD

end CFSG.LocalAnalysis.RankThreeUC.S15
