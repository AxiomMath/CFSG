module

public import CFSG.GH74.GLS.Balance.OResidual
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74.GLS Subgroup

section Coprime

variable {X : Type} [Group X] [Finite X]

theorem map_centralizer_eq_centralizer_map_of_isPGroup (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) {A : Subgroup X} (hA : IsPGroup 2 ↥A) :
    (centralizer (A : Set X)).map (QuotientGroup.mk' N) =
      centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥A) := ⟨hA⟩
  exact (centralizer_map_quotient_eq_map_centralizer 2 A N inferInstance
    (Nat.coprime_two_left.2 hN)).symm

theorem centralizer_quotient_of_pGroup (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N))
    {A : Subgroup X} (hA : IsPGroup 2 ↥A) {c : X ⧸ N}
    (hc : ∀ a ∈ A, QuotientGroup.mk' N a * c = c * QuotientGroup.mk' N a) :
    ∃ g : X, QuotientGroup.mk' N g = c ∧ ∀ a ∈ A, a * g = g * a := by
  have hmem : c ∈ centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact hc a ha
  rw [← map_centralizer_eq_centralizer_map_of_isPGroup N hN hA] at hmem
  obtain ⟨g, hg, hgc⟩ := hmem
  exact ⟨g, hgc, fun a ha => Subgroup.mem_centralizer_iff.1 hg a ha⟩

omit [Finite X] in
theorem not_two_dvd_card_ker_comp_mk {H : Type*} [Group H] (ι : H →* X) (hι : Function.Injective ι)
    (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N)) :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' N).comp ι).ker := by
  have hker : ((QuotientGroup.mk' N).comp ι).ker = N.comap ι := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [hker]
  intro h2
  have hdvd := Subgroup.card_comap_dvd_of_injective N ι hι
  exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 (h2.trans hdvd))

end Coprime

section Small

variable {G : Type*} [Group G]

theorem centralizer_closure_pair (x y : G) :
    centralizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext g
  simp [Subgroup.mem_centralizer_iff]

theorem isPGroup_two_zpowers_of_orderOf {g : G} (hg : orderOf g = 2) :
    IsPGroup 2 ↥(zpowers g) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; rfl)

theorem oPrimeResidualOf_le_oPrimeResidualOf_self (P : Subgroup G) :
    oPrimeResidualOf 2 P ≤ oPrimeResidualOf 2 (oPrimeResidualOf 2 P) := by
  refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
  exact Balance.mem_oPrimeResidualOf_of_two_element
    (Balance.mem_oPrimeResidualOf_of_two_element hv h2) h2

end Small

section PComp

variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

open CFSG.Open CFSG.ComponentClassification

theorem isPCompIn_iff_lBalance {H L : Subgroup G} :
    IsPCompIn p H L ↔ L ≤ H ∧ lBalanceIsPComponent p H L :=
  ⟨fun h => ⟨h.1, (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p H L h.1).1 h.2⟩,
    fun h => ⟨h.1, (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p H L h.1).2 h.2⟩⟩

theorem lBalance_of_relative_normal {Y M L : Subgroup G} (hYM : Y ≤ M) [(Y.subgroupOf M).Normal]
    (hLY : L ≤ Y) (hL : lBalanceIsPComponent p Y L) : lBalanceIsPComponent p M L := by
  have hLM : L ≤ M := hLY.trans hYM
  have h1 := (LBalance.pComponent_nested_iff p Y M L hYM hLY).2 hL
  have h2 := LBalance.pComponent_normal_extension p (Y.subgroupOf M) (L.subgroupOf M) h1
  exact (LBalance.pComponent_nested_iff p M M L le_rfl hLM).1
    (by rw [Subgroup.subgroupOf_self]; exact h2)

theorem lBalance_top_of_isSubnormal {Q : Type*} [Group Q] [Finite Q] {A : Subgroup Q}
    (hA : A.IsSubnormal) :
    ∀ L : Subgroup Q, lBalanceIsPComponent p A L → lBalanceIsPComponent p ⊤ L := by
  induction hA with
  | top => intro L hL; exact hL
  | step A B hAB hB hN ih =>
    intro L hL
    exact ih L (lBalance_of_relative_normal p hAB (LBalance.subnormal_le hL.1) hL)

theorem isPCompIn_of_isSubnormal {Y M L : Subgroup G} (hYM : Y ≤ M)
    (hsub : (Y.subgroupOf M).IsSubnormal) (hL : IsPCompIn p Y L) : IsPCompIn p M L := by
  obtain ⟨hLY, hl⟩ := (isPCompIn_iff_lBalance p).1 hL
  have hLM : L ≤ M := hLY.trans hYM
  have h1 := (LBalance.pComponent_nested_iff p Y M L hYM hLY).2 hl
  have h2 := lBalance_top_of_isSubnormal p hsub _ h1
  refine (isPCompIn_iff_lBalance p).2 ⟨hLM, ?_⟩
  exact (LBalance.pComponent_nested_iff p M M L le_rfl hLM).1
    (by rw [Subgroup.subgroupOf_self]; exact h2)

theorem isPCompIn_of_normal {Y M L : Subgroup G} (hYM : Y ≤ M) [(Y.subgroupOf M).Normal]
    (hL : IsPCompIn p Y L) : IsPCompIn p M L :=
  isPCompIn_of_isSubnormal p hYM (inferInstance : (Y.subgroupOf M).Normal).isSubnormal hL

theorem pLayerOf_eq_lBalancePLayer (H : Subgroup G) : pLayerOf p H = lBalancePLayer p H := by
  unfold pLayerOf lBalancePLayer
  congr 1
  ext L
  exact (isPCompIn_iff_lBalance p).trans ⟨fun h => h.2, fun h => ⟨LBalance.subnormal_le h.1, h⟩⟩

omit [Finite G] [Fact p.Prime] in
theorem pLayerOf_le (H : Subgroup G) : pLayerOf p H ≤ H :=
  sSup_le fun _ hL => hL.1

theorem pLayerOf_subgroupOf_normal (H : Subgroup G) : ((pLayerOf p H).subgroupOf H).Normal := by
  rw [pLayerOf_eq_lBalancePLayer, LBalance.Asm.lBalancePLayer_eq_map,
    show ((pLayer ↥H p).map H.subtype).subgroupOf H = pLayer ↥H p from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := ↥H) (p := p)
  infer_instance

theorem isPCompIn_of_isPCompIn_pLayerOf {H L : Subgroup G} (hL : IsPCompIn p (pLayerOf p H) L) :
    IsPCompIn p H L :=
  have := pLayerOf_subgroupOf_normal p H
  isPCompIn_of_normal p (pLayerOf_le p H) hL

end PComp

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_trans {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (h1 : (A.subgroupOf B).IsSubnormal) (h2 : (B.subgroupOf C).IsSubnormal) :
    (A.subgroupOf C).IsSubnormal := by
  let e : ↥(B.subgroupOf C) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBC
  have hle : A.subgroupOf C ≤ B.subgroupOf C := fun a ha => hAB ha
  refine Subgroup.IsSubnormal.trans hle ?_ h2
  have : (A.subgroupOf C).subgroupOf (B.subgroupOf C) = (A.subgroupOf B).comap e.toMonoidHom := by
    ext z
    rfl
  rw [this]
  exact h1.comap _

theorem isSubnormal_subgroupOf_inf {A B S : Subgroup G} (h : (A.subgroupOf B).IsSubnormal) :
    ((A ⊓ S).subgroupOf (B ⊓ S)).IsSubnormal := by
  let ι : ↥(B ⊓ S) →* ↥B := Subgroup.inclusion inf_le_left
  have : (A ⊓ S).subgroupOf (B ⊓ S) = (A.subgroupOf B).comap ι := by
    ext z
    constructor
    · intro hz
      exact (Subgroup.mem_inf.1 hz).1
    · intro hz
      exact Subgroup.mem_inf.2 ⟨hz, z.2.2⟩
  rw [this]
  exact h.comap _

theorem isSubnormal_of_isPCompIn {p : ℕ} {H L : Subgroup G} (h : IsPCompIn p H L) :
    (L.subgroupOf H).IsSubnormal := by
  obtain ⟨_, _, hsub, _, _⟩ := h.2
  exact hsub

end Subnormal

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem exists_isPCompIn_lift_of_odd_ker {Y : Subgroup G} {Q : Type*} [Group Q] (φ : ↥Y →* Q)
    (hker : ¬ 2 ∣ Nat.card φ.ker) {Jb : Subgroup Q} (hJb : IsPCompIn 2 φ.range Jb) :
    IsPCompIn 2 Y (oPrimeResidualOf 2 ((Jb.comap φ).map Y.subtype)) ∧
      ((oPrimeResidualOf 2 ((Jb.comap φ).map Y.subtype)).subgroupOf Y).map φ = Jb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  set f : ↥Y →* ↥φ.range := φ.rangeRestrict with hf
  have hfs : Function.Surjective f := φ.rangeRestrict_surjective
  have hfk : ¬ 2 ∣ Nat.card f.ker := by rwa [hf, MonoidHom.ker_rangeRestrict]
  obtain ⟨-, hinv, -⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      f hfs hfk
  obtain ⟨hJc, hJmap⟩ := hinv _ hJb.2
  set S : Set ↥Y := {z | z ∈ (Jb.subgroupOf φ.range).comap f ∧ ∃ k : ℕ, orderOf z = 2 ^ k} with hS
  set J' : Subgroup ↥Y := Subgroup.closure S with hJ'
  set P : Subgroup G := (Jb.comap φ).map Y.subtype with hP
  have hJJ' : J'.map Y.subtype = oPrimeResidualOf 2 P := by
    apply le_antisymm
    · rw [hJ', MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨z, ⟨hzJ, k, hk⟩, rfl⟩
      refine Balance.mem_oPrimeResidualOf_of_two_element ⟨z, hzJ, rfl⟩ ⟨k, ?_⟩
      have hzk : z ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one z
      simpa using congrArg Subtype.val hzk
    · refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
      obtain ⟨z, hz, rfl⟩ := hv
      obtain ⟨k, hk⟩ := h2
      have hzk : z ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hzk)
      exact ⟨z, Subgroup.subset_closure ⟨hz, j, hj⟩, rfl⟩
  have hsubOf : (oPrimeResidualOf 2 P).subgroupOf Y = J' := by
    rw [← hJJ']
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective J'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hJJ']
    exact Subgroup.map_subtype_le _
  · rw [hsubOf]
    exact hJc
  · rw [hsubOf]
    have hφ : φ = φ.range.subtype.comp f := rfl
    rw [hφ, ← Subgroup.map_map, hJmap, Subgroup.map_subgroupOf_eq_of_le hJb.1]

end Lift

end CFSG.GH74.Generic.BProg.B1
