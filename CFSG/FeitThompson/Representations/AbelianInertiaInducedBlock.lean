module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.ClassFunctionInductionTransitivity
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.AbelianQuotientExtensionInducedFamily
import CFSG.FeitThompson.Representations.NormalInducedBlockPartition
import CFSG.FeitThompson.Representations.CoprimeDegreeInvariantCharExtends

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace AbelianInertiaBlock

variable {L : Type*} [Group L] {H U : Subgroup L} [H.Normal] {lam : H → ℂ}

theorem mem_inf_inertiaGroup_iff {u : L} :
    u ∈ U ⊓ inertiaGroup H lam ↔
      u ∈ U ∧ ∀ h : H, lam (MulAut.conjNormal u⁻¹ h) = lam h := by
  rw [Subgroup.mem_inf, mem_inertiaGroup_iff_forall_conj]

theorem inertiaGroup_eq_sup (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤) :
    inertiaGroup H lam = H ⊔ (U ⊓ inertiaGroup H lam) := by
  have hHI : H ≤ inertiaGroup H lam := le_inertiaGroup H (Irr_subset_classFun hlam)
  refine le_antisymm (fun g hg => ?_) (sup_le hHI inf_le_right)
  obtain ⟨h, hh, u, hu, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top g : g ∈ H ⊔ U)
  have huI : u ∈ inertiaGroup H lam := by
    have he : u = h⁻¹ * (h * u) := by group
    rw [he]
    exact (inertiaGroup H lam).mul_mem ((inertiaGroup H lam).inv_mem (hHI hh)) hg
  exact Subgroup.mul_mem_sup hh ⟨hu, huI⟩

theorem isComplement'_subgroupOf_inertiaGroup (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤)
    (hinf : H ⊓ U = ⊥) :
    ((U ⊓ inertiaGroup H lam).subgroupOf (inertiaGroup H lam)).IsComplement'
      (H.subgroupOf (inertiaGroup H lam)) := by
  have : (H.subgroupOf (inertiaGroup H lam)).Normal := ‹H.Normal›.subgroupOf _
  refine isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_
  · rw [← Subgroup.subgroupOf_sup (le_inertiaGroup H (Irr_subset_classFun hlam)) inf_le_right,
      ← inertiaGroup_eq_sup hlam hsup, Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf]
    have hb : H ⊓ (U ⊓ inertiaGroup H lam) = ⊥ :=
      le_antisymm (le_trans (le_inf inf_le_left (le_trans inf_le_right inf_le_left)) hinf.le) bot_le
    rw [hb]
    simp

theorem index_subgroupOf_inertiaGroup (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤)
    (hinf : H ⊓ U = ⊥) :
    (H.subgroupOf (inertiaGroup H lam)).index
      = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) := by
  rw [(isComplement'_subgroupOf_inertiaGroup (U := U) hlam hsup hinf).index_eq_card]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ inertiaGroup H lam ≤ _)).toEquiv

theorem isMulCommutative_quotient
    [IsMulCommutative ((U ⊓ inertiaGroup H lam : Subgroup L) : Type _)]
    (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤) (hinf : H ⊓ U = ⊥) :
    IsMulCommutative (inertiaGroup H lam ⧸ H.subgroupOf (inertiaGroup H lam)) := by
  have : (H.subgroupOf (inertiaGroup H lam)).Normal := ‹H.Normal›.subgroupOf _
  have : IsMulCommutative
      ((U ⊓ inertiaGroup H lam).subgroupOf (inertiaGroup H lam) : Type _) :=
    isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ inertiaGroup H lam ≤ _))
  exact isMulCommutative_of_mulEquiv
    (isComplement'_subgroupOf_inertiaGroup (U := U) hlam hsup hinf).QuotientMulEquiv

omit [H.Normal] in
theorem coe_subgroupOfEquivOfLe {K : Subgroup L} (hHK : H ≤ K) (x : H.subgroupOf K) :
    ((Subgroup.subgroupOfEquivOfLe hHK x : H) : L) = ((x : K) : L) := rfl

noncomputable abbrev lamSub (hlam : lam ∈ Irr H) : H.subgroupOf (inertiaGroup H lam) → ℂ :=
  lam ∘ Subgroup.subgroupOfEquivOfLe (le_inertiaGroup H (Irr_subset_classFun hlam))

theorem lamSub_mem_Irr (hlam : lam ∈ Irr H) :
    lamSub hlam ∈ Irr (H.subgroupOf (inertiaGroup H lam)) :=
  FrobeniusInduction.mem_Irr_comp_mulEquiv hlam _

theorem lamSub_one (hlam : lam ∈ Irr H) : lamSub hlam 1 = lam 1 := by
  change lam (Subgroup.subgroupOfEquivOfLe _ 1) = lam 1
  rw [map_one]

theorem lamSub_invariant (U : Subgroup L) (hlam : lam ∈ Irr H)
    (u : (U ⊓ inertiaGroup H lam).subgroupOf (inertiaGroup H lam))
    (h : H.subgroupOf (inertiaGroup H lam)) :
    lamSub hlam (MulAut.conjNormal (u : inertiaGroup H lam)⁻¹ h) = lamSub hlam h := by
  have hHI := le_inertiaGroup H (Irr_subset_classFun hlam)
  have hu : ((u : inertiaGroup H lam) : L) ∈ inertiaGroup H lam :=
    (Subgroup.mem_subgroupOf.1 u.2).2
  have key := mem_inertiaGroup_iff_forall_conj.1 hu (Subgroup.subgroupOfEquivOfLe hHI h)
  have hcast : Subgroup.subgroupOfEquivOfLe hHI
      (MulAut.conjNormal (u : inertiaGroup H lam)⁻¹ h)
      = MulAut.conjNormal (((u : inertiaGroup H lam) : L))⁻¹
        (Subgroup.subgroupOfEquivOfLe hHI h) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, coe_subgroupOfEquivOfLe, coe_subgroupOfEquivOfLe,
      MulAut.conjNormal_apply]
    push_cast
    ring_nf
  change lam (Subgroup.subgroupOfEquivOfLe hHI
      (MulAut.conjNormal (u : inertiaGroup H lam)⁻¹ h))
    = lam (Subgroup.subgroupOfEquivOfLe hHI h)
  rw [hcast]
  exact key

theorem exists_extension [Finite L] (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤) (hinf : H ⊓ U = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card U)) :
    ∃ eta ∈ Irr (inertiaGroup H lam),
      resClassFun (H.subgroupOf (inertiaGroup H lam)) eta = lamSub hlam := by
  have hHI : H ≤ inertiaGroup H lam := le_inertiaGroup H (Irr_subset_classFun hlam)
  have : (H.subgroupOf (inertiaGroup H lam)).Normal := ‹H.Normal›.subgroupOf _
  obtain ⟨d, -, hdeg, hddvd⟩ := Irr.exists_degree hlam
  have hcardUI : Nat.card ((U ⊓ inertiaGroup H lam).subgroupOf (inertiaGroup H lam))
      = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ inertiaGroup H lam ≤ _)).toEquiv
  refine exists_mem_Irr_resClassFun_eq (d := d)
    (U := (U ⊓ inertiaGroup H lam).subgroupOf (inertiaGroup H lam))
    (lamSub_mem_Irr hlam) ((lamSub_one hlam).trans hdeg) ?_ ?_ ?_ (lamSub_invariant U hlam)
  · rw [← Subgroup.subgroupOf_sup hHI (inf_le_right : U ⊓ inertiaGroup H lam ≤ _),
      ← inertiaGroup_eq_sup hlam hsup, Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf]
    have hb : H ⊓ (U ⊓ inertiaGroup H lam) = ⊥ :=
      le_antisymm (le_trans (le_inf inf_le_left (le_trans inf_le_right inf_le_left)) hinf.le) bot_le
    rw [hb]
    simp
  · rw [hcardUI]
    exact Nat.Coprime.coprime_dvd_left hddvd
      (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left : U ⊓ inertiaGroup H lam ≤ U)) hcop)

variable [Fintype L]

theorem indClassFun_sum (K : Subgroup L) {ι : Type*} (s : Finset ι) (F : ι → K → ℂ) :
    indClassFun K (∑ i ∈ s, F i) = ∑ i ∈ s, indClassFun K (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, indClassFun_add, ih, Finset.sum_insert ha]

theorem inductionTransitivity_indClassFun_eq (K : Subgroup L) (θ : K → ℂ) :
    InductionTransitivity.indClassFun K θ = indClassFun K θ := by
  classical
  funext y
  rw [InductionTransitivity.indClassFun_apply, indClassFun_eq_sum_extendByZero]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  by_cases hx : x⁻¹ * y * x ∈ K
  · rw [InductionTransitivity.extendByZero_of_mem _ _ hx, extendByZero_apply_dite, dif_pos hx]
  · rw [InductionTransitivity.extendByZero_of_notMem _ _ hx, extendByZero_of_notMem _ _ hx]

omit [H.Normal] in
theorem indClassFun_indClassFun (K : Subgroup L) [Fintype K] (hHK : H ≤ K) (f : H → ℂ) :
    indClassFun K (indClassFun (H.subgroupOf K) (f ∘ Subgroup.subgroupOfEquivOfLe hHK))
      = indClassFun H f := by
  rw [← inductionTransitivity_indClassFun_eq, ← inductionTransitivity_indClassFun_eq,
    ← inductionTransitivity_indClassFun_eq]
  exact InductionTransitivity.indClassFun_indClassFun H K hHK f

theorem indClassFun_ne_zero (K : Subgroup L) {θ : K → ℂ} (hθ : θ 1 ≠ 0) :
    indClassFun K θ ≠ 0 := by
  intro h
  have h1 := NormalInducedFamily.indClassFun_one_eq_index_mul K θ
  rw [h] at h1
  have hidx : (K.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  simp only [Pi.zero_apply] at h1
  exact absurd h1.symm (by simpa using mul_ne_zero hidx hθ)

theorem mem_Irr_of_cfInner_self_eq_card {ι : Type*} {s : Finset ι} {F : ι → L → ℂ}
    (hchar : ∀ i ∈ s, ∃ n : irrFinset L → ℕ, (∃ ψ, n ψ ≠ 0) ∧
      F i = ∑ ψ : irrFinset L, (n ψ : ℂ) • (ψ : L → ℂ))
    (hnorm : cfInner (∑ i ∈ s, F i) (∑ i ∈ s, F i) = (s.card : ℂ)) :
    ∀ i ∈ s, F i ∈ Irr L := by
  classical
  have hex : ∀ i : ι, ∃ n : irrFinset L → ℕ, i ∈ s →
      ((∃ ψ, n ψ ≠ 0) ∧ F i = ∑ ψ : irrFinset L, (n ψ : ℂ) • (ψ : L → ℂ)) := by
    intro i
    by_cases h : i ∈ s
    · obtain ⟨n, h1, h2⟩ := hchar i h
      exact ⟨n, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose n hn using hex
  set c : ι → ι → ℕ := fun i j => ∑ ψ : irrFinset L, n i ψ * n j ψ with hc
  have hcf : ∀ i ∈ s, ∀ j ∈ s, cfInner (F i) (F j) = (c i j : ℂ) := fun i hi j hj =>
    cfInner_eq_natCast_sum_mul (hn i hi).2 (hn j hj).2
  have hsum : ∑ i ∈ s, ∑ j ∈ s, c i j = s.card := by
    have h : ((∑ i ∈ s, ∑ j ∈ s, c i j : ℕ) : ℂ) = (s.card : ℂ) := by
      push_cast
      rw [← hnorm, cfInner_sum_left]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [cfInner_sum_right]
      exact Finset.sum_congr rfl fun j hj => (hcf i hi j hj).symm
    exact_mod_cast h
  have hcii : ∀ i ∈ s, 1 ≤ c i i := by
    intro i hi
    obtain ⟨ψ, hψ⟩ := (hn i hi).1
    calc 1 ≤ n i ψ * n i ψ := Nat.one_le_iff_ne_zero.2 (by positivity)
      _ ≤ c i i := Finset.single_le_sum (f := fun ψ => n i ψ * n i ψ)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ ψ)
  have hdiag : ∀ i ∈ s, c i i ≤ ∑ j ∈ s, c i j := fun i hi =>
    Finset.single_le_sum (f := fun j => c i j) (fun _ _ => Nat.zero_le _) hi
  have hcard : ∑ i ∈ s, 1 = s.card := by simp
  have heq1 : ∑ i ∈ s, c i i = s.card :=
    le_antisymm (hsum ▸ Finset.sum_le_sum hdiag) (hcard ▸ Finset.sum_le_sum hcii)
  have hone : ∀ i ∈ s, c i i = 1 := fun i hi =>
    ((Finset.sum_eq_sum_iff_of_le hcii).1 (by rw [hcard, heq1]) i hi).symm
  intro i hi
  obtain ⟨ψ₀, hψ₀⟩ := (hn i hi).1
  have hzero : ∀ ψ, ψ ≠ ψ₀ → n i ψ = 0 := by
    intro ψ hne
    by_contra h
    have h1 : 1 ≤ n i ψ * n i ψ := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 1 ≤ n i ψ₀ * n i ψ₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hpair : n i ψ * n i ψ + n i ψ₀ * n i ψ₀ ≤ c i i := by
      have hsub := Finset.sum_le_sum_of_subset (f := fun ψ => n i ψ * n i ψ)
        (Finset.subset_univ ({ψ, ψ₀} : Finset (irrFinset L)))
      rwa [Finset.sum_pair hne] at hsub
    rw [hone i hi] at hpair
    omega
  have hn1 : n i ψ₀ = 1 := by
    have hle : n i ψ₀ * n i ψ₀ ≤ c i i :=
      Finset.single_le_sum (f := fun ψ => n i ψ * n i ψ) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ ψ₀)
    rw [hone i hi] at hle
    rcases Nat.lt_or_ge (n i ψ₀) 2 with h | h
    · omega
    · exfalso; nlinarith
  have hFi : F i = (ψ₀ : L → ℂ) := by
    rw [(hn i hi).2, Finset.sum_eq_single_of_mem ψ₀ (Finset.mem_univ ψ₀)
      (fun ψ _ hne => by rw [hzero ψ hne]; simp), hn1]
    simp
  rw [hFi]
  exact mem_irrFinset.1 ψ₀.2

theorem exists_finset_Irr_indClassFun (hlam : lam ∈ Irr H) (hsup : H ⊔ U = ⊤) (hinf : H ⊓ U = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card U))
    [IsMulCommutative ((U ⊓ inertiaGroup H lam : Subgroup L) : Type _)] :
    ∃ S : Finset (L → ℂ), ↑S ⊆ Irr L ∧
      S.card = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) ∧
      indClassFun H lam = ∑ χ ∈ S, χ ∧
      ∀ χ ∈ S, χ 1 = ((inertiaGroup H lam).index : ℂ) * lam 1 := by
  classical
  set I := inertiaGroup H lam with hI
  have hHI : H ≤ I := le_inertiaGroup H (Irr_subset_classFun hlam)
  have : Fintype I := Fintype.ofFinite _
  have : (H.subgroupOf I).Normal := ‹H.Normal›.subgroupOf _
  have : IsMulCommutative (I ⧸ H.subgroupOf I) := isMulCommutative_quotient hlam hsup hinf
  obtain ⟨eta, hetaIrr, hetares⟩ := exists_extension hlam hsup hinf hcop
  set Q := I ⧸ H.subgroupOf I with hQ
  set s : Finset (Q → ℂ) := irrFinset Q with hs
  set F : (Q → ℂ) → L → ℂ :=
    fun β => indClassFun I (eta * (β ∘ (QuotientGroup.mk : I → Q))) with hF
  have hFapply : ∀ β, F β = indClassFun I (eta * (β ∘ (QuotientGroup.mk : I → Q))) := fun _ => rfl
  have hsum : indClassFun H lam = ∑ β ∈ s, F β := by
    rw [hF, ← indClassFun_sum,
      ← AbelianQuotientExtension.indClassFun_resClassFun_eq_sum (Irr_subset_classFun hetaIrr),
      hetares]
    exact (indClassFun_indClassFun I hHI lam).symm
  have hcard : s.card = (H.subgroupOf I).index :=
    AbelianQuotientExtension.card_irrFinset_quotient
  have hnorm : cfInner (∑ β ∈ s, F β) (∑ β ∈ s, F β) = (s.card : ℂ) := by
    rw [← hsum, cfInner_self_indClassFun H hlam, hcard]
    rfl
  have hchar : ∀ β ∈ s, ∃ n : irrFinset L → ℕ, (∃ ψ, n ψ ≠ 0) ∧
      F β = ∑ ψ : irrFinset L, (n ψ : ℂ) • (ψ : L → ℂ) := by
    intro β hβ
    have hβI : eta * (β ∘ (QuotientGroup.mk : I → Q)) ∈ Irr I :=
      AbelianQuotientExtension.mul_comp_mk_mem_Irr hetaIrr (mem_irrFinset.1 hβ)
    obtain ⟨n, hn⟩ := exists_multiplicities_indClassFun hβI
    refine ⟨n, ?_, hn⟩
    rcases em (∃ ψ, n ψ ≠ 0) with hne | hall
    · exact hne
    · exfalso
      have hall' : ∀ ψ, n ψ = 0 := fun ψ => not_not.1 fun h => hall ⟨ψ, h⟩
      have hz : F β = 0 := by rw [hFapply, hn]; simp [hall']
      refine indClassFun_ne_zero I ?_ hz
      rw [AbelianQuotientExtension.mul_comp_mk_one (mem_irrFinset.1 hβ), hetares, lamSub_one hlam]
      exact apply_one_ne_zero_of_mem_Irr hlam
  have hIrr : ∀ β ∈ s, F β ∈ Irr L := mem_Irr_of_cfInner_self_eq_card hchar hnorm
  have hinj : ∀ β ∈ s, ∀ γ ∈ s, F β = F γ → β = γ :=
    AbelianQuotientExtension.injOn_of_cfInner_self_eq_card s F hIrr hnorm
  have hdeg : ∀ β ∈ s, F β 1 = (I.index : ℂ) * lam 1 := by
    intro β hβ
    rw [hFapply, NormalInducedFamily.indClassFun_one_eq_index_mul,
      AbelianQuotientExtension.mul_comp_mk_one (mem_irrFinset.1 hβ), hetares, lamSub_one hlam]
  refine ⟨s.image F, ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hχ
    obtain ⟨β, hβ, rfl⟩ := hχ
    exact hIrr β hβ
  · rw [Finset.card_image_of_injOn hinj, hcard,
      index_subgroupOf_inertiaGroup (U := U) hlam hsup hinf]
  · rw [Finset.sum_image hinj, hsum]
  · intro χ hχ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hχ
    exact hdeg β hβ

end AbelianInertiaBlock

end CFSG.FeitThompson
