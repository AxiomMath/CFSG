module

public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7StepOdd

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Card

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem card_oddQuot_of_witness (hw : A7Witness K) : Nat.card (OddQuot K) = 5040 := by
  obtain ⟨π, z, hcov, -⟩ := exists_cover_of_witness hw
  exact hcov.card_E

end Card

section Member

variable {Y : Type} [Group Y] [Finite Y]

theorem IsClassical2A7.inf_center_eq_bot (hO : classicalInvolutionOddCore Y = ⊥) {L : Subgroup Y}
    {z : Y} (h : IsClassical2A7 ⊤ L z) (hz : z ∉ Subgroup.center Y) :
    L ⊓ Subgroup.center Y = ⊥ := by
  obtain ⟨π, zbar, hcov, hcenter⟩ := exists_cover_of_witness h.witness
  refine eq_bot_iff.mpr fun a ⟨haL, haZ⟩ => ?_
  rw [Subgroup.mem_bot]
  set ρ : L →* L ⧸ classicalInvolutionOddCore L := QuotientGroup.mk' _ with hρ
  set z' : L := ⟨z, h.mem⟩ with hz'
  set a' : L := ⟨a, haL⟩ with ha'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hρz'ne : ρ z' ≠ 1 := by
    intro h1
    have h2 := orderOf_mk_oddCore_eq_two hz'2
    change orderOf (ρ z') = 2 at h2
    rw [h1, orderOf_one] at h2
    omega
  have hcenz : ∀ l : L, l * z' = z' * l := fun l => Subtype.ext (h.mul_comm_of_mem l.2)
  have hcen : ∀ l : L, l * a' = a' * l := fun l =>
    Subtype.ext (Subgroup.mem_center_iff.mp haZ l.1)
  have hρcen : ∀ c : L, (∀ l : L, l * c = c * l) →
      ρ c ∈ Subgroup.center (L ⧸ classicalInvolutionOddCore L) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul, hc l]
  have hρzz : ρ z' = zbar := ((hcenter (ρ z')).mp (hρcen z' hcenz)).resolve_left hρz'ne
  have hca := (hcenter (ρ a')).mp (hρcen a' hcen)
  have hcenter2 : ∀ x ∈ Subgroup.center Y, ∃ k, orderOf x = 2 ^ k := fun x hx => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_center_of_corefree hO)) ⟨x, hx⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hOtriv : ∀ x : L, x ∈ classicalInvolutionOddCore L → (x : Y) ∈ Subgroup.center Y →
      x = 1 := by
    intro x hxO hxZ
    obtain ⟨k, hk⟩ := hcenter2 _ hxZ
    rw [Subgroup.orderOf_coe] at hk
    exact eq_one_of_mem_odd_of_orderOf_eq_two_pow hOodd hxO hk
  rcases hca with h1 | h1
  ·
    have h3 : a' ∈ classicalInvolutionOddCore L := (QuotientGroup.eq_one_iff _).mp h1
    exact congrArg Subtype.val (hOtriv a' h3 haZ)
  ·
    exfalso
    have h2 : ρ a' = ρ z' := h1.trans hρzz.symm
    have h3 : a'⁻¹ * z' ∈ classicalInvolutionOddCore L := by
      apply (QuotientGroup.eq_one_iff _).mp
      show ρ (a'⁻¹ * z') = 1
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have hz'sq : z' * z' = 1 := by rw [← sq, ← hz'2]; exact pow_orderOf_eq_one z'
    have hcomm : Commute z' a'⁻¹ := (Commute.inv_right (show Commute z' a' from hcen z'))
    have h4 : (a'⁻¹ * z') * (a'⁻¹ * z') = a'⁻¹ * a'⁻¹ := by
      rw [Commute.mul_mul_mul_comm hcomm, hz'sq, mul_one]
    have h5 : a'⁻¹ * a'⁻¹ ∈ classicalInvolutionOddCore L := h4 ▸ Subgroup.mul_mem _ h3 h3
    have h6 : ((a'⁻¹ * a'⁻¹ : L) : Y) ∈ Subgroup.center Y := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haZ) (Subgroup.inv_mem _ haZ)
    have h7 := hOtriv _ h5 h6
    rw [h7] at h4
    have h8 : (a'⁻¹ * z') ^ 2 = 1 := by rw [sq]; exact h4
    have h9 : orderOf (a'⁻¹ * z') ∣ 2 := orderOf_dvd_of_pow_eq_one h8
    have h10 : Odd (orderOf (a'⁻¹ * z')) :=
      hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ h3)
    have h11 : orderOf (a'⁻¹ * z') = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h9 with h | h
      · exact h
      · rw [h] at h10; exact absurd h10 (by decide)
    have h12 : a'⁻¹ * z' = 1 := orderOf_eq_one_iff.mp h11
    have h13 : z' = a' := by
      have := congrArg (fun x => a' * x) h12
      simpa using this
    apply hz
    have := congrArg Subtype.val h13
    rw [hz', ha'] at this
    simp only at this
    rw [this]
    exact haZ

theorem IsClassical2A7.map_centerQuotient (hO : classicalInvolutionOddCore Y = ⊥) {L : Subgroup Y}
    {z : Y} (h : IsClassical2A7 ⊤ L z) (hz : z ∉ Subgroup.center Y) :
    IsClassical2A7 ⊤ (L.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) z) where
  orderOf_eq_two := by
    have h1 : QuotientGroup.mk' (Subgroup.center Y) z ≠ 1 := fun h' =>
      hz ((QuotientGroup.eq_one_iff z).mp h')
    have h2 : QuotientGroup.mk' (Subgroup.center Y) z ^ 2 = 1 := by
      rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
    exact orderOf_eq_prime h2 h1
  mem := Subgroup.mem_map_of_mem _ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (QuotientGroup.mk' (Subgroup.center Y))
  subnormal := by
    set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
    set Ct : Subgroup Y := (Subgroup.centralizer ({π z} : Set (Y ⧸ Subgroup.center Y))).comap π
      with hCt
    have hCC : Subgroup.centralizer ({z} : Set Y) ≤ Ct := fun c hc => by
      rw [hCt, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    have hsub0 : IsSubnormal L (Subgroup.centralizer ({z} : Set Y)) := by
      have h1 := h.subnormal
      rwa [top_inf_eq] at h1
    have hsub : IsSubnormal L Ct :=
      isSubnormal_trans hsub0
        (IsSubnormal.step hCC (centralizer_subgroupOf_normal_comap_center z)
          (IsSubnormal.refl Ct))
    have := CFSG.ComponentClassification.Components.chain_map π hsub
    rw [top_inf_eq]
    rwa [hCt, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      at this
  witness := by
    set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
    have hinj : Function.Injective (π.subgroupMap L) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine eq_bot_iff.mpr fun x hx => ?_
      rw [Subgroup.mem_bot]
      have hxc : (x : Y) ∈ Subgroup.center Y :=
        (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
      have hmem : (x : Y) ∈ L ⊓ Subgroup.center Y := ⟨x.2, hxc⟩
      rw [h.inf_center_eq_bot hO hz, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    let eL : L ≃* L.map π :=
      MulEquiv.ofBijective (π.subgroupMap L) ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
    exact A7Witness.of_mulEquiv eL h.witness

theorem inClass2A7_centerQuotient (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)}
    (hΛ : InClass2A7 Λ)
    (hz : ∀ L ∈ Λ, ∀ z, IsClassical2A7 ⊤ L z → z ∉ Subgroup.center Y) :
    InClass2A7 (Subgroup.map (QuotientGroup.mk' (Subgroup.center Y)) '' Λ) where
  nonempty := hΛ.nonempty.image _
  conjInvariant := by
    rintro n _ ⟨L, hL, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ n
    exact ⟨conjSub y L, hΛ.conjInvariant.toConjInvariant y L hL,
      (conjSub_map (QuotientGroup.mk' _) y L).symm⟩
  generated := by
    set π := QuotientGroup.mk' (Subgroup.center Y)
    have h : ⨆ M ∈ Subgroup.map π '' Λ, M = (⨆ L ∈ Λ, L).map π := by
      refine le_antisymm (iSup₂_le fun M hM => ?_) ?_
      · obtain ⟨L, hL, rfl⟩ := hM
        exact Subgroup.map_mono (le_iSup₂ (f := fun (L : Subgroup Y) (_ : L ∈ Λ) => L) L hL)
      · rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun L hL => ?_
        exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂
          (f := fun (M : Subgroup (Y ⧸ Subgroup.center Y)) (_ : M ∈ Subgroup.map π '' Λ) => M)
          (L.map π) ⟨L, hL, rfl⟩)
    rw [h, hΛ.generated, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  classical := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hzL⟩ := hΛ.classical L hL
    exact ⟨_, hzL.map_centerQuotient hO (hz L hL z hzL)⟩

end Member

section CentralInvolution

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_singleton_top_of_central_involution (hqs : CFSG.Open.IsQuasisimple Y)
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ)
    {L₀ : Subgroup Y} (hL₀ : L₀ ∈ Λ) {z : Y} (h : IsClassical2A7 ⊤ L₀ z)
    (hzc : z ∈ Subgroup.center Y) :
    Λ = {⊤} ∧ A7Witness (⊤ : Subgroup Y) := by
  have hcent : Subgroup.centralizer ({z} : Set Y) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hzc
  have hsub : IsSubnormal L₀ ⊤ := by
    have h1 := h.subnormal
    rwa [hcent, top_inf_eq] at h1
  have := h.perfect
  have hL₀top : L₀ = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hqs L₀
      hsub with h0 | h0
    · exfalso
      have hz : z ∈ L₀ := h.mem
      rw [h0, Subgroup.mem_bot] at hz
      have := h.orderOf_eq_two
      rw [hz, orderOf_one] at this
      omega
    · exact h0
  have hOL : classicalInvolutionOddCore L₀ = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hO L₀ hsub
  have hcard : Nat.card Y = 5040 := by
    have h1 : Nat.card (OddQuot L₀) = 5040 := card_oddQuot_of_witness h.witness
    have h2 : Nat.card (OddQuot L₀) = Nat.card L₀ := by
      refine Nat.card_congr ?_
      exact (QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot |>.toEquiv
    rw [← h1, h2, hL₀top, Subgroup.card_top]
  refine ⟨?_, hL₀top ▸ h.witness⟩
  ext M
  constructor
  · intro hM
    obtain ⟨z', hz'⟩ := hΛ.classical M hM
    have h1 : Nat.card Y ≤ Nat.card M := by
      rw [hcard, ← card_oddQuot_of_witness hz'.witness]
      exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    exact Set.mem_singleton_iff.mpr (Subgroup.eq_top_of_le_card M h1)
  · intro hM
    rw [Set.mem_singleton_iff.mp hM, ← hL₀top]
    exact hL₀

end CentralInvolution

section Quasisimple

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem a7System_singleton_top (hperf : Group.IsPerfect Y) (hw : A7Witness (⊤ : Subgroup Y)) :
    A7System Y {⊤} :=
  ⟨{ card := 1
     comp := fun _ => ⊤
     perfect := fun _ => Group.IsPerfect.ofSurjective
       (f := (Subgroup.topEquiv (G := Y)).symm.toMonoidHom) (MulEquiv.surjective _)
     witness := fun _ => hw
     commute := fun i j h => absurd (Subsingleton.elim i j) h
     generate := iSup_const
     members := (Set.range_const).symm }⟩

theorem a7SystemMod_of_quasisimple (hcore : CoreStep2A7) (hBelow : CITBelow2A7 (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ)
    (hqs : CFSG.Open.IsQuasisimple Y) : A7SystemMod Λ := by
  by_cases hc : ∃ L ∈ Λ, ∃ z, IsClassical2A7 ⊤ L z ∧ z ∈ Subgroup.center Y
  · obtain ⟨L, hL, z, hz, hzc⟩ := hc
    obtain ⟨hΛeq, hw⟩ := eq_singleton_top_of_central_involution hqs hO hΛ hL hz hzc
    refine a7SystemMod_of_a7System_corefree hO ?_
    rw [hΛeq]
    exact a7System_singleton_top ⟨hqs.1⟩ hw
  · push Not at hc
    exfalso
    have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hqs.2
    set π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _ with hπ
    have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hYperf : Group.IsPerfect Y := ⟨hqs.1⟩
    have hGperf : Group.IsPerfect (Y ⧸ Subgroup.center Y) :=
      Group.IsPerfect.ofSurjective (f := π) hπsurj
    have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      exact Group.IsPerfect.not_isSolvable (Y ⧸ Subgroup.center Y)
        (IsSimpleGroup.comm_iff_isSolvable.mp hcomm)
    obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
    obtain ⟨z₀, hz₀⟩ := hΛ.classical L₀ hL₀
    have hz₀' := hz₀.map_centerQuotient hO (hc L₀ hL₀ z₀ hz₀)
    have hBelow' : CITBelow2A7 (Nat.card (Y ⧸ Subgroup.center Y)) :=
      CITBelow2A7.mono (Nat.card_le_card_of_surjective π hπsurj) hBelow
    exact hcore (Y ⧸ Subgroup.center Y) hnab _ _ hz₀' hBelow'

end Quasisimple

end CFSG.ClassicalInvolution.Hat2A7
