module

public import CFSG.ClassicalInvolution.Generic.InductionSL2
public import CFSG.ClassicalInvolution.Generic.StepOdd
public import CFSG.ClassicalInvolution.Generic.StepSplit
public import CFSG.ClassicalInvolution.Generic.StepDefs

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open scoped MatrixGroups

section Center

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_center_of_corefree (hO : classicalInvolutionOddCore Y = ⊥) :
    IsPGroup 2 (Subgroup.center Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  rw [Subgroup.orderOf_mk]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g) (orderOf_pos g).ne'
  refine ⟨k, ?_⟩
  have hy : orderOf (g ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hkm ▸ dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hycen : g ^ (2 ^ k) ∈ Subgroup.center Y := Subgroup.pow_mem _ hg _
  have hnormal : (Subgroup.zpowers (g ^ (2 ^ k))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hycen)
  have hodd : Odd (Nat.card (Subgroup.zpowers (g ^ (2 ^ k)))) := by
    rw [Nat.card_zpowers, hy]; exact hm
  have hle : Subgroup.zpowers (g ^ (2 ^ k)) ≤ classicalInvolutionOddCore Y :=
    CFSG.ComponentClassification.OddCore.maximal Y _ hnormal hodd
  rw [hO] at hle
  have h1 : g ^ (2 ^ k) = 1 :=
    Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hy
  rw [hkm, ← hy, mul_one]

end Center

section Member

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem odd_natCard_galoisField (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Odd (Nat.card (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem eq_one_of_mem_odd_of_orderOf_eq_two_pow {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Odd (Nat.card N)) {x : G} (hx : x ∈ N) {k : ℕ} (hk : orderOf x = 2 ^ k) : x = 1 := by
  have hdvd : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard _ hx
  have hodd : Odd (orderOf x) := hN.of_dvd_nat hdvd
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem IsClassicalMember.inf_center_eq_bot (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hO : classicalInvolutionOddCore Y = ⊥) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (hz : z ∉ Subgroup.center Y) :
    L ⊓ Subgroup.center Y = ⊥ := by
  have hodd := odd_natCard_galoisField hp2 hq
  obtain ⟨e⟩ := h.nonempty_equiv
  refine eq_bot_iff.mpr fun a ⟨haL, haZ⟩ => ?_
  rw [Subgroup.mem_bot]
  set ρ : L →* L ⧸ classicalInvolutionOddCore L := QuotientGroup.mk' _ with hρ
  set z' : L := ⟨z, h.mem⟩ with hz'
  set a' : L := ⟨a, haL⟩ with ha'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hρz' : ρ z' = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e (ρ z')).mp (orderOf_mk_oddCore_eq_two hz'2)
  have hcen : ∀ l : L, l * a' = a' * l := fun l =>
    Subtype.ext (Subgroup.mem_center_iff.mp haZ l.1)
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
  have hρa : ρ a' ∈ Subgroup.center (L ⧸ classicalInvolutionOddCore L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul, hcen l]
  have hρa' := (mem_center_iff_of_equiv_sl2 e (ρ a')).mp hρa
  rcases (mem_center_sl2_iff _).mp hρa' with h1 | h1
  ·
    have h2 : ρ a' = 1 := (MulEquiv.map_eq_one_iff e).mp h1
    have h3 : a' ∈ classicalInvolutionOddCore L := (QuotientGroup.eq_one_iff _).mp h2
    exact congrArg Subtype.val (hOtriv a' h3 haZ)
  ·
    exfalso
    have h2 : ρ a' = ρ z' := by rw [hρz']; exact e.eq_symm_apply.mpr h1
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

omit [Finite Y] in
theorem centralizer_subgroupOf_normal_comap_center (z : Y) :
    ((Subgroup.centralizer ({z} : Set Y)).subgroupOf
      ((Subgroup.centralizer ({QuotientGroup.mk' (Subgroup.center Y) z} :
        Set (Y ⧸ Subgroup.center Y))).comap (QuotientGroup.mk' (Subgroup.center Y)))).Normal := by
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  rw [Subgroup.normal_subgroupOf_iff (fun c hc => by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hc])]
  intro c y hc hy
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hy
  have hw : (y * z)⁻¹ * (z * y) ∈ Subgroup.center Y := QuotientGroup.eq.mp hy
  set w := (y * z)⁻¹ * (z * y) with hwdef
  have hzy : z * y = y * z * w := by rw [hwdef]; group
  have hwc : w * c = c * w := (Subgroup.mem_center_iff.mp hw c).symm
  have hzc : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hyzy : y⁻¹ * z * y = z * w := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z * w) := by rw [hzy]
      _ = z * w := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * c * y⁻¹ * z = y * c * (y⁻¹ * z * y) * y⁻¹ := by group
    _ = y * c * (z * w) * y⁻¹ := by rw [hyzy]
    _ = y * (c * z) * w * y⁻¹ := by group
    _ = y * (z * c) * w * y⁻¹ := by rw [hzc]
    _ = y * z * (c * w) * y⁻¹ := by group
    _ = y * z * (w * c) * y⁻¹ := by rw [hwc]
    _ = (y * z * w) * c * y⁻¹ := by group
    _ = z * y * c * y⁻¹ := by rw [hzy]
    _ = z * (y * c * y⁻¹) := by group

theorem IsClassicalMember.map_centerQuotient (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hO : classicalInvolutionOddCore Y = ⊥) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (hz : z ∉ Subgroup.center Y) :
    IsClassicalMember p f (L.map (QuotientGroup.mk' (Subgroup.center Y)))
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
    have hsub : IsSubnormal L Ct :=
      isSubnormal_trans h.subnormal
        (IsSubnormal.step hCC (centralizer_subgroupOf_normal_comap_center z)
          (IsSubnormal.refl Ct))
    have := CFSG.ComponentClassification.Components.chain_map π hsub
    rwa [hCt, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      at this
  nonempty_equiv := by
    set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
    obtain ⟨e'⟩ := h.nonempty_equiv
    have hinj : Function.Injective (π.subgroupMap L) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine eq_bot_iff.mpr fun x hx => ?_
      rw [Subgroup.mem_bot]
      have hxc : (x : Y) ∈ Subgroup.center Y :=
        (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
      have hmem : (x : Y) ∈ L ⊓ Subgroup.center Y := ⟨x.2, hxc⟩
      rw [h.inf_center_eq_bot hp2 hq hO hz, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    let eL : L ≃* L.map π :=
      MulEquiv.ofBijective (π.subgroupMap L) ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
    have hO' : (classicalInvolutionOddCore L).map eL.toMonoidHom =
        classicalInvolutionOddCore (L.map π) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant eL
    exact ⟨(QuotientGroup.congr _ _ eL hO').symm.trans e'⟩

theorem inClass_centerQuotient (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ)
    (hz : ∀ L ∈ Λ, ∀ z, IsClassicalMember p f L z → z ∉ Subgroup.center Y) :
    InClass p f (Subgroup.map (QuotientGroup.mk' (Subgroup.center Y)) '' Λ) where
  nonempty := hΛ.nonempty.image _
  conjInvariant := by
    rintro n _ ⟨L, hL, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ n
    exact ⟨conjSub y L, hΛ.conjInvariant y L hL, (conjSub_map (QuotientGroup.mk' _) y L).symm⟩
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
    exact ⟨_, hzL.map_centerQuotient hp2 hq hO (hz L hL z hzL)⟩

end Member

section Orbit

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [IsSimpleGroup G]

theorem inClass_conjugates {L : Subgroup G} {z : G} (h : IsClassicalMember p f L z) :
    InClass p f (Set.range fun g : G => conjSub g L) where
  nonempty := ⟨L, 1, conjSub_one L⟩
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul n g L⟩
  generated := by
    have hinv : ConjInvariant (Set.range fun g : G => conjSub g L) := by
      rintro n _ ⟨g, rfl⟩
      exact ⟨n * g, conjSub_mul n g L⟩
    have hnormal := normal_biSup hinv
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (⨆ M ∈ Set.range fun g : G => conjSub g L, M) with h0 | h0
    · exfalso
      have hz : z ∈ ⨆ M ∈ Set.range fun g : G => conjSub g L, M :=
        (le_iSup₂_of_le L ⟨1, conjSub_one L⟩ le_rfl : L ≤ _) h.mem
      rw [h0, Subgroup.mem_bot] at hz
      exact h.ne_one hz
    · exact h0
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g * z * g⁻¹, h.conj g⟩

end Orbit

section CentralInvolution

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem eq_singleton_top_of_central_involution (hqs : CFSG.Open.IsQuasisimple Y)
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ)
    {L₀ : Subgroup Y} (hL₀ : L₀ ∈ Λ) {z : Y} (h : IsClassicalMember p f L₀ z)
    (hzc : z ∈ Subgroup.center Y) :
    Λ = {⊤} ∧ Nonempty (Y ≃* SL(2, GaloisField p f)) := by
  have hcent : Subgroup.centralizer ({z} : Set Y) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hzc
  have hsub : IsSubnormal L₀ ⊤ := hcent ▸ h.subnormal
  have := h.perfect
  have hL₀top : L₀ = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hqs L₀
      hsub with h0 | h0
    · exfalso
      have hz : z ∈ L₀ := h.mem
      rw [h0, Subgroup.mem_bot] at hz
      exact h.ne_one hz
    · exact h0
  have hOL : classicalInvolutionOddCore L₀ = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hO L₀ hsub
  obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hOL
  let eY : Y ≃* SL(2, GaloisField p f) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hL₀top.symm).trans eL)
  refine ⟨?_, ⟨eY⟩⟩
  ext M
  constructor
  · intro hM
    obtain ⟨z', hz'⟩ := hΛ.classical M hM
    have h1 := hz'.card_ge
    rw [← Nat.card_congr eY.toEquiv] at h1
    exact Set.mem_singleton_iff.mpr (Subgroup.eq_top_of_le_card M h1)
  · intro hM
    rw [Set.mem_singleton_iff.mp hM, ← hL₀top]
    exact hL₀

end CentralInvolution

section NonCentral

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem eq_top_of_perfect_of_sup_center {G : Type*} [Group G] (hG : commutator G = ⊤)
    {M : Subgroup G} (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ M ⊔ Subgroup.center G := h ▸ Subgroup.mem_top x
  have hy : y ∈ M ⊔ Subgroup.center G := h ▸ Subgroup.mem_top y
  obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have h1 : ∀ g : G, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.mp hz₁ g).symm
  have h2 : ∀ g : G, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.mp hz₂ g).symm
  rw [commutatorElement_def]
  have hA : c₁ * z₁ * (c₂ * z₂) = c₁ * c₂ * (z₁ * z₂) :=
    Commute.mul_mul_mul_comm (h1 c₂) c₁ z₂
  have hB : c₂ * z₂ * (c₁ * z₁) = c₂ * c₁ * (z₂ * z₁) :=
    Commute.mul_mul_mul_comm (h2 c₁) c₂ z₁
  have hz : z₁ * z₂ = z₂ * z₁ := h1 z₂
  have : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        (c₁ * z₁ * (c₂ * z₂)) * (c₂ * z₂ * (c₁ * z₁))⁻¹ := by group
      _ = (c₁ * c₂ * (z₁ * z₂)) * (c₂ * c₁ * (z₂ * z₁))⁻¹ := by rw [hA, hB]
      _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by rw [hz]; group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.mul_mem hc₁ hc₂) (M.inv_mem hc₁)) (M.inv_mem hc₂)

theorem lieSystem_of_quasisimple_noncentral (hcore : CoreStep p f)
    (hfund : ClassicalIsFundamental p f) (hlift : CentralLift p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) (hqs : CFSG.Open.IsQuasisimple Y)
    (hz : ∀ L ∈ Λ, ∀ z, IsClassicalMember p f L z → z ∉ Subgroup.center Y) :
    LieSystem p f Y Λ := by
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hqs.2
  set π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _ with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
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
  have hz₀' := hz₀.map_centerQuotient hp2 hq hO (hz L₀ hL₀ z₀ hz₀)
  have hBelow' : CITBelowU p f (Nat.card (Y ⧸ Subgroup.center Y)) :=
    CITBelowU.mono p f (Nat.card_le_card_of_surjective π hπsurj) hBelow
  obtain ⟨D⟩ := hcore hp2 hq (Y ⧸ Subgroup.center Y) hnab _ _ hz₀' hBelow'
  obtain ⟨t, n, e, hp, ψ, hψsurj, hψker, hFT, hadm, hexp⟩ := D.exists_model_of_simple hnab
  obtain ⟨ψ', hψ'⟩ := hlift hp2 t n e hp hFT hadm Y (Y ⧸ Subgroup.center Y) hnab π ψ hπsurj
    hψsurj hYperf (by rw [hπker]; exact isPGroup_center_of_corefree hO) hπker.le hψker
  have hsup : ψ'.range ⊔ Subgroup.center Y = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hψsurj (π y)
    have hk' : π (ψ' k) = π y := by rw [← hk, ← hψ']; rfl
    have hmem : (ψ' k)⁻¹ * y ∈ Subgroup.center Y := QuotientGroup.eq.mp hk'
    have hy : y = ψ' k * ((ψ' k)⁻¹ * y) := by group
    rw [hy]
    exact Subgroup.mul_mem_sup ⟨k, rfl⟩ hmem
  have hψ'surj : Function.Surjective ψ' :=
    MonoidHom.range_eq_top.mp (eq_top_of_perfect_of_sup_center hqs.1 hsup)
  have hψ'ker : ψ'.ker ≤ Subgroup.center _ := by
    intro x hx
    have h1 : ψ x = 1 := by
      rw [← hψ']
      change π (ψ' x) = 1
      rw [MonoidHom.mem_ker.mp hx, map_one]
    exact hψker.le (MonoidHom.mem_ker.mpr h1)
  have hfundΛ : ∀ L ∈ Λ, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      L = R.map ψ' := fun L hL => by
    obtain ⟨z, hzL⟩ := hΛ.classical L hL
    exact hfund hp2 hq t n e hp hFT hadm hexp Y ψ' hψ'surj hψ'ker L z hzL
  have hmeets : ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, R.map ψ' ∈ Λ := by
    obtain ⟨R, hR, hLR⟩ := hfundΛ L₀ hL₀
    exact ⟨R, hR, by rw [← hLR]; exact hL₀⟩
  exact ⟨LieSystemData.single hp hFT hadm hexp ψ' hψ'surj hψ'ker hfundΛ hmeets⟩

theorem lieSystemMod_of_quasisimple (hcore : CoreStep p f) (hfund : ClassicalIsFundamental p f)
    (hlift : CentralLift p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) (hqs : CFSG.Open.IsQuasisimple Y) :
    LieSystemMod p f Λ := by
  by_cases hc : ∃ L ∈ Λ, ∃ z, IsClassicalMember p f L z ∧ z ∈ Subgroup.center Y
  · obtain ⟨L, hL, z, hz, hzc⟩ := hc
    obtain ⟨hΛeq, ⟨e⟩⟩ := eq_singleton_top_of_central_involution hqs hO hΛ hL hz hzc
    have h := LieSystemMod.congr e.symm (sl2_lieSystemMod p f hp2 hq)
    have himg : Subgroup.map e.symm.toMonoidHom ''
        ({⊤} : Set (Subgroup SL(2, GaloisField p f))) = {⊤} := by
      rw [Set.image_singleton, Subgroup.map_top_of_surjective _ e.symm.surjective]
    rw [himg] at h
    rw [hΛeq]
    exact h
  · push Not at hc
    exact lieSystemMod_of_lieSystem_corefree hO
      (lieSystem_of_quasisimple_noncentral hcore hfund hlift hp2 hq hBelow hO hΛ hqs
        fun L hL z hz hzc => hc L hL z hz hzc)

end NonCentral

end CFSG.ClassicalInvolution.Generic
