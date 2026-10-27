module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.Q3.Step

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Member

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem odd_natCard_zmod_three : Odd (Nat.card (ZMod 3)) := by
  rw [Nat.card_zmod]
  decide

theorem IsClassicalMember3.inf_center_eq_bot (hO : classicalInvolutionOddCore Y = ⊥)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z) (hz : z ∉ Subgroup.center Y) :
    L ⊓ Subgroup.center Y = ⊥ := by
  have hodd := odd_natCard_zmod_three
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
  · have h2 : ρ a' = 1 := (MulEquiv.map_eq_one_iff e).mp h1
    have h3 : a' ∈ classicalInvolutionOddCore L := (QuotientGroup.eq_one_iff _).mp h2
    exact congrArg Subtype.val (hOtriv a' h3 haZ)
  · exfalso
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

theorem IsClassicalMember3.map_centerQuotient (hO : classicalInvolutionOddCore Y = ⊥)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z) (hz : z ∉ Subgroup.center Y) :
    IsClassicalMember3 (L.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) z) where
  orderOf_eq_two := by
    have h1 : QuotientGroup.mk' (Subgroup.center Y) z ≠ 1 := fun h' =>
      hz ((QuotientGroup.eq_one_iff z).mp h')
    have h2 : QuotientGroup.mk' (Subgroup.center Y) z ^ 2 = 1 := by
      rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
    exact orderOf_eq_prime h2 h1
  mem := Subgroup.mem_map_of_mem _ h.mem
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
      rw [h.inf_center_eq_bot hO hz, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    let eL : L ≃* L.map π :=
      MulEquiv.ofBijective (π.subgroupMap L) ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
    have hO' : (classicalInvolutionOddCore L).map eL.toMonoidHom =
        classicalInvolutionOddCore (L.map π) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant eL
    exact ⟨(QuotientGroup.congr _ _ eL hO').symm.trans e'⟩

theorem inClass3_centerQuotient (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)}
    (hΛ : InClass3 Λ)
    (hz : ∀ L ∈ Λ, ∀ z, IsClassicalMember3 L z → z ∉ Subgroup.center Y) :
    InClass3 (Subgroup.map (QuotientGroup.mk' (Subgroup.center Y)) '' Λ) where
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
    exact ⟨_, hzL.map_centerQuotient hO (hz L hL z hzL)⟩

theorem IsClassicalMember3.not_mem_center_of_quasisimple (hqs : CFSG.Open.IsQuasisimple Y)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z) : z ∉ Subgroup.center Y := by
  intro hzc
  have hcent : Subgroup.centralizer ({z} : Set Y) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hzc
  have hsub : IsSubnormal L ⊤ := hcent ▸ h.subnormal
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hqs L hsub with
    hle | htop
  · exact h.not_le_center hle
  · have hsolv : Group.IsSolvable ↥(⊤ : Subgroup Y) := htop ▸ h.isSolvable
    have hY : Group.IsSolvable Y := by
      let e : Y ≃* (⊤ : Subgroup Y) := Subgroup.topEquiv.symm
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hperf : Group.IsPerfect Y := ⟨hqs.1⟩
    have hnt : Nontrivial Y := by
      have h1 : 24 ≤ Nat.card Y :=
        h.card_ge.trans (Nat.card_le_card_of_injective _ Subtype.val_injective)
      exact Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (by norm_num) h1)
    exact Group.IsPerfect.not_isSolvable Y hY

end Member

section Orbit

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem inClass3_conjugates {L : Subgroup G} {z : G} (h : IsClassicalMember3 L z) :
    InClass3 (Set.range fun g : G => conjSub g L) where
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

section Simple

theorem LieSystemData3.exists_surjective_of_simple {ι G : Type} [Group G] [IsSimpleGroup G]
    {Φ : Set (Subgroup G)} (D : LieSystemData3 ι G Φ) : ∃ i, Function.Surjective (D.hom i) := by
  by_contra hne
  push Not at hne
  have hbot : ∀ i, (D.hom i).range = ⊥ := fun i => by
    have := D.range_normal i
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.hom i).range).resolve_right
      fun h => hne i (MonoidHom.range_eq_top.mp h)
  have h : (⨆ i, (D.hom i).range : Subgroup G) = ⊥ := by simp [hbot]
  rw [D.generate] at h
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have h1 : a ∈ (⊤ : Subgroup G) := trivial
  have h2 : b ∈ (⊤ : Subgroup G) := trivial
  rw [h, Subgroup.mem_bot] at h1 h2
  exact hab (h1.trans h2.symm)

theorem ker_eq_center_of_surjective_simple {K G : Type} [Group K] [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (ψ : K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) : ψ.ker = Subgroup.center K := by
  refine le_antisymm hker fun x hx => ?_
  have hc : ψ x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx k]
  rw [CFSG.ComponentClassification.Helpers.center_eq_bot G hnab, Subgroup.mem_bot] at hc
  exact hc

end Simple

@[expose] def SolvableConnected3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass3 Λ →
    classicalInvolutionOddCore Y = ⊥ → NonCommConnected Λ → Group.IsSolvable Y →
    Nonempty (Y ≃* SL(2, ZMod 3)) ∧ Λ = {⊤}

@[expose] def QuasisimpleConnected3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → NonCommConnected Λ → ¬ Group.IsSolvable Y →
      CFSG.Open.IsQuasisimple Y

@[expose] def CoreStep3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      LieSystem3 G (Set.range fun g : G => conjSub g K)

@[expose] def ClassicalIsFundamental3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ (L : Subgroup X) (z : X), IsClassicalMember3 L z →
        (∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 hp).D, L = R.map ψ) ∧ Nat.card L = 24

@[expose] def M11Branch3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass3 Λ →
    CFSG.Open.IsQuasisimple Y → classicalInvolutionOddCore Y = ⊥ →
    (∃ ψ : ↥CFSG.Blueprint.NativeSporadic.M11 →* (Y ⧸ Subgroup.center Y),
      Function.Surjective ψ) → LieSystem3 Y Λ

section Assembly

variable {Y : Type} [Group Y] [Finite Y]

theorem lieSystem3_of_component (hfund : ClassicalIsFundamental3) (hlift : CentralLift 3)
    (hM11 : M11Branch3) (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)}
    (hΛ : InClass3 Λ) (hqs : CFSG.Open.IsQuasisimple Y)
    (hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a)
    (c : CompData) (hc : c.Valid) (ψ : c.G →* Y ⧸ Subgroup.center Y)
    (hψsurj : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center _) : LieSystem3 Y Λ := by
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hqs.2
  set π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _ with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  rcases hc with ⟨t, n, hFT, hadm, rfl⟩ | rfl | rfl
  ·
    have hYperf : Group.IsPerfect Y := ⟨hqs.1⟩
    have hψker' : ψ.ker = Subgroup.center _ :=
      ker_eq_center_of_surjective_simple hnab ψ hψsurj hψker
    obtain ⟨ψ', hψ'⟩ := hlift (by norm_num) t n 1 Nat.prime_three hFT hadm Y _ hnab π ψ hπsurj
      hψsurj hYperf (by rw [hπker]; exact isPGroup_center_of_corefree hO) hπker.le hψker'
    have hsup : ψ'.range ⊔ Subgroup.center Y = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨k, hk⟩ := hψsurj (π y)
      have hk' : π (ψ' k) = π y := by rw [← hk, ← hψ']; rfl
      have hmem : (ψ' k)⁻¹ * y ∈ Subgroup.center Y := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hk', inv_mul_cancel]
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
      exact hψker (MonoidHom.mem_ker.mpr h1)
    have hfundΛ : ∀ L ∈ Λ, (∃ R ∈ fundamentalSubgroups t
        (modelUniv t n 3 1 Nat.prime_three).D, L = R.map ψ') ∧ Nat.card L = 24 := by
      intro L hL
      obtain ⟨z, hz⟩ := hΛ.classical L hL
      exact hfund t n Nat.prime_three hFT hadm Y ψ' hψ'surj hψ'ker L z hz
    obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
    refine ⟨Unit, inferInstance, ⟨{
      kind := fun _ => CompData.model t n
      valid := fun _ => Or.inl ⟨t, n, hFT, hadm, rfl⟩
      hom := fun _ => ψ'
      ker_le_center := fun _ => hψ'ker
      commute := fun i j h => absurd (Subsingleton.elim i j) h
      generate := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, rfl⟩ := hψ'surj x
        exact Subgroup.mem_iSup_of_mem () ⟨y, rfl⟩
      fundamental := fun L hL => ⟨(), (hfundΛ L hL).1⟩
      meets := fun _ => by
        obtain ⟨R, hR, hLR⟩ := (hfundΛ L₀ hL₀).1
        exact ⟨R, hR, by rw [← hLR]; exact hL₀⟩
      card_eq := fun L hL => (hfundΛ L hL).2 }⟩⟩
  ·
    exfalso
    have hsolv : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
      have := isSolvable_sl2Three
      Group.isSolvable_of_surjective (f := ψ) hψsurj
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  ·
    exact hM11 Y Λ hΛ hqs hO ⟨ψ, hψsurj⟩

theorem lieSystem3_of_quasisimple (hcore : CoreStep3) (hfund : ClassicalIsFundamental3)
    (hlift : CentralLift 3) (hM11 : M11Branch3)
    (hBelow : CIT3Below (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ) (hqs : CFSG.Open.IsQuasisimple Y) :
    LieSystem3 Y Λ := by
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
  have hz : ∀ L ∈ Λ, ∀ z, IsClassicalMember3 L z → z ∉ Subgroup.center Y :=
    fun L _ z hz => hz.not_mem_center_of_quasisimple hqs
  obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
  obtain ⟨z₀, hz₀⟩ := hΛ.classical L₀ hL₀
  have hz₀' := hz₀.map_centerQuotient hO (hz L₀ hL₀ z₀ hz₀)
  have hBelow' : CIT3Below (Nat.card (Y ⧸ Subgroup.center Y)) :=
    CIT3Below.mono (Nat.card_le_card_of_surjective π hπsurj) hBelow
  obtain ⟨ι, hι, ⟨D⟩⟩ := hcore (Y ⧸ Subgroup.center Y) hnab _ _ hz₀' hBelow'
  obtain ⟨i, hsurj⟩ := D.exists_surjective_of_simple
  exact lieSystem3_of_component hfund hlift hM11 hO hΛ hqs hnab (D.kind i) (D.valid i) (D.hom i)
    hsurj (D.ker_le_center i)

end Assembly

theorem connectedBranch3_of_parts (hS : SolvableConnected3) (hQ : QuasisimpleConnected3)
    (hcore : CoreStep3) (hfund : ClassicalIsFundamental3) (hlift : CentralLift 3)
    (hM11 : M11Branch3) : ConnectedBranch3 := by
  intro Y _ _ hBelow hO Λ hΛ hconn
  by_cases hsolv : Group.IsSolvable Y
  · obtain ⟨⟨e⟩, hΛeq⟩ := hS Y Λ hΛ hO hconn hsolv
    rw [hΛeq]
    exact lieSystem3_of_equiv_sl2Three e.symm
  · exact lieSystem3_of_quasisimple hcore hfund hlift hM11 hBelow hO hΛ
      (hQ Y hBelow hO Λ hΛ hconn hsolv)

end CFSG.ClassicalInvolution.Q3
