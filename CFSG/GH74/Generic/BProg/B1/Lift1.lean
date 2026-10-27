module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.BProg.B1.Lift0

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg Subgroup

section Restrict

variable {G : Type} [Group G]

theorem centralizer_closure_pair_le_left (x y : G) :
    centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) ≤ centralizer ({x} : Set G) := by
  rw [centralizer_closure_pair]
  exact inf_le_left

@[expose] noncomputable def projRes {x : G} {Y : Subgroup G} (h : Y ≤ centralizer ({x} : Set G)) :
    ↥Y →* CentralizerBar x :=
  (proj x).comp (Subgroup.inclusion h)

theorem projRes_apply {x : G} {Y : Subgroup G} (h : Y ≤ centralizer ({x} : Set G)) (z : ↥Y) :
    projRes h z = proj x ⟨(z : G), h z.2⟩ := rfl

theorem range_projRes {x : G} {Y : Subgroup G} (h : Y ≤ centralizer ({x} : Set G)) :
    (projRes h).range = imgBar x Y := by
  unfold projRes imgBar
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem map_proj_subgroupOf_eq {x : G} {Y J : Subgroup G} (h : Y ≤ centralizer ({x} : Set G))
    (hJ : J ≤ Y) :
    (J.subgroupOf (centralizer ({x} : Set G))).map (proj x) = (J.subgroupOf Y).map (projRes h) := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨(c : G), hJ hc⟩, hc, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨(z : G), h z.2⟩, hz, rfl⟩

theorem isSubnormal_imgBar {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) : (imgBar x K).IsSubnormal := by
  obtain ⟨Kb, ⟨-, hKb⟩, -, hmap, -⟩ := hK.2
  change ((K.subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))))).IsSubnormal
  rw [hmap]
  exact hKb

theorem isSubnormal_centralizer_inf_imgBar {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (b : CentralizerBar x) :
    ((centralizer ({b} : Set (CentralizerBar x)) ⊓ imgBar x K).subgroupOf
      (centralizer ({b} : Set (CentralizerBar x)))).IsSubnormal := by
  rw [Subgroup.inf_subgroupOf_left]
  exact (isSubnormal_imgBar hK).subgroupOf

theorem liftAt_pre_eq {x y : G} (Lb : Subgroup (CentralizerBar x)) :
    ((Lb.comap (proj x)).map (centralizer ({x} : Set G)).subtype) ⊓ centralizer ({y} : Set G) =
      (Lb.comap (projRes (centralizer_closure_pair_le_left x y))).map
        (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)).subtype := by
  ext g
  constructor
  · rintro ⟨⟨c, hcLb, rfl⟩, hgy⟩
    have hgY : (c : G) ∈ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) := by
      rw [centralizer_closure_pair]
      exact Subgroup.mem_inf.2 ⟨c.2, hgy⟩
    exact ⟨⟨(c : G), hgY⟩, hcLb, rfl⟩
  · rintro ⟨⟨g, hgY⟩, hz, rfl⟩
    have hgY' := hgY
    rw [centralizer_closure_pair] at hgY'
    exact ⟨⟨⟨g, (Subgroup.mem_inf.1 hgY').1⟩, hz, rfl⟩, (Subgroup.mem_inf.1 hgY').2⟩

end Restrict

section Lift1

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_card_ker_projRes {x : G} {Y : Subgroup G} (h : Y ≤ centralizer ({x} : Set G)) :
    ¬ 2 ∣ Nat.card (projRes h).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact not_two_dvd_card_ker_comp_mk (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
    (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card)

theorem imgBar_centralizer_closure_pair {x y : G} (hxy : x * y = y * x) (hy : orderOf y = 2) :
    imgBar x (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)) =
      centralizer ({bar x y} : Set (CentralizerBar x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyC : y ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxy.symm
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set u : ↥C := ⟨y, hyC⟩ with hu
  have hbar : bar x y = proj x u := bar_of_mem hyC
  have hyY : y ∈ (closure ({x, y} : Set G) : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  ext c
  constructor
  · intro hc
    obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff, hbar, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hg y hyY).symm
  · intro hc
    have hou : orderOf u = 2 := by rw [hu, Subgroup.orderOf_mk]; exact hy
    obtain ⟨g, hgc, hg⟩ := centralizer_quotient_of_pGroup (pPrimeCore 2 ↥C)
      (Nat.coprime_two_left.1 pPrimeCore_coprime_card) (A := zpowers u)
      (isPGroup_two_zpowers_of_orderOf hou) (c := c) (by
        intro a ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        have hcomm : Commute c (bar x y) := (Subgroup.mem_centralizer_singleton_iff.1 hc)
        have := (Commute.zpow_right hcomm n).eq
        rw [map_zpow]
        change proj x u ^ n * c = c * proj x u ^ n
        rw [← hbar]
        exact this.symm)
    refine mem_imgBar.2 ⟨g, ?_, hgc⟩
    rw [centralizer_closure_pair]
    refine Subgroup.mem_inf.2 ⟨g.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hg u (Subgroup.mem_zpowers u)).symm

theorem isPCompIn_centralizer_of_isPCompIn_inf {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (b : CentralizerBar x)
    {Lb : Subgroup (CentralizerBar x)}
    (hLb : IsPCompIn 2 (centralizer ({b} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb) :
    IsPCompIn 2 (centralizer ({b} : Set (CentralizerBar x))) Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPCompIn_of_isSubnormal 2 inf_le_left (isSubnormal_centralizer_inf_imgBar hK b) hLb

theorem isPCompIn_liftAt {x y : G} (hxy : x * y = y * x) (hy : orderOf y = 2) {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {Lb : Subgroup (CentralizerBar x)}
    (hLb : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb) :
    IsPCompIn 2 (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)) (liftAt x y Lb) ∧
      ((liftAt x y Lb).subgroupOf (centralizer ({x} : Set G))).map (proj x) = Lb := by
  set Y : Subgroup G := centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) with hY
  have hYC : Y ≤ centralizer ({x} : Set G) := centralizer_closure_pair_le_left x y
  have hrange : (projRes hYC).range = centralizer ({bar x y} : Set (CentralizerBar x)) := by
    rw [range_projRes]
    exact imgBar_centralizer_closure_pair hxy hy
  have hLb' : IsPCompIn 2 (projRes hYC).range Lb := by
    rw [hrange]
    exact isPCompIn_centralizer_of_isPCompIn_inf hK _ hLb
  obtain ⟨hJ, hJmap⟩ := exists_isPCompIn_lift_of_odd_ker (projRes hYC)
    (not_two_dvd_card_ker_projRes hYC) hLb'
  have hlift : liftAt x y Lb = oPrimeResidualOf 2 ((Lb.comap (projRes hYC)).map Y.subtype) := by
    unfold liftAt
    rw [liftAt_pre_eq Lb]
  rw [hlift]
  refine ⟨hJ, ?_⟩
  rw [map_proj_subgroupOf_eq hYC hJ.1]
  exact hJmap

end Lift1

section Lift1b

variable {G : Type} [Group G]

theorem nbhdSemisimple_of_dsemisimple {x y : G} {Lb : Subgroup (CentralizerBar x)} {L : Subgroup G}
    (hlift : liftAt x y Lb ≤ oPrimeResidualOf 2 L)
    (hss : ∀ d ∈ closure ({x, y} : Set G), d ≠ 1 →
      ⁅oPrimeResidualOf 2 L, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) :
    NbhdSemisimple x y Lb := fun d hd hd1 =>
  le_bot_iff.1 ((Subgroup.commutator_mono hlift le_rfl).trans (hss d hd hd1).le)

end Lift1b

end CFSG.GH74.Generic.BProg.B1
