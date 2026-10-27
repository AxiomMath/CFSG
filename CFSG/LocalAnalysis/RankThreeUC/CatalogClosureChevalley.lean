module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable (τ : Tag) (K : Type) [Field K] [CharP K 2]

theorem twoLocalClosure_adjoint_eq_top (E : Subgroup (adjointGroup τ K))
    (hE : ∀ α, IsRoot τ α → ∀ e ∈ E, ∀ g ∈ rootSubgroup τ K α,
      ((e : (Module.End K (RootModule τ K))ˣ) * g * (e : (Module.End K (RootModule τ K))ˣ)⁻¹) ∈
        rootSubgroup τ K α) :
    twoLocalClosure E = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine twoLocalClosure_eq_top_of_invariant_two_subgroups E
    {S | ∃ α, IsRoot τ α ∧ S = (rootSubgroup τ K α).subgroupOf (adjointGroup τ K)} ?_ ?_
  · rintro S ⟨α, hα, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    ·
      intro hbot
      have hmem : pinnedX τ K α 1 ∈ rootSubgroup τ K α := Subgroup.subset_closure ⟨1, rfl⟩
      have hmemA : pinnedX τ K α 1 ∈ adjointGroup τ K := pinnedX_mem_adjointGroup α 1
      have h1 : (⟨pinnedX τ K α 1, hmemA⟩ : adjointGroup τ K) ∈
          (rootSubgroup τ K α).subgroupOf (adjointGroup τ K) := hmem
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : pinnedX τ K α 1 = 1 := congrArg Subtype.val h1
      have h3 : pinnedX τ K α 1 = pinnedX τ K α 0 := by rw [h2, pinnedX_zero]
      exact one_ne_zero (pinnedX_injective τ K α h3)
    · intro g
      by_cases hg1 : (g : adjointGroup τ K) = 1
      · exact ⟨0, by simp [Subtype.ext_iff, hg1]⟩
      · refine ⟨1, ?_⟩
        have hmem : ((g : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) ∈
            rootSubgroup τ K α := g.2
        have hne : ((g : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) ≠ 1 := by
          intro h
          exact hg1 (Subtype.ext h)
        have hord := orderOf_eq_of_mem_rootSubgroup (p := 2) hmem hne
        have hpow : ((g : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) ^ 2 = 1 := by
          rw [← hord]; exact pow_orderOf_eq_one _
        apply Subtype.ext; apply Subtype.ext
        simpa using hpow
    · intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hE α hα e he _ hh
      · intro hh
        have hh' : ((e : (Module.End K (RootModule τ K))ˣ) *
            (h : (Module.End K (RootModule τ K))ˣ) *
            (e : (Module.End K (RootModule τ K))ˣ)⁻¹) ∈ rootSubgroup τ K α := hh
        have := hE α hα e⁻¹ (E.inv_mem he) _ hh'
        show (h : (Module.End K (RootModule τ K))ˣ) ∈ rootSubgroup τ K α
        simpa [mul_assoc] using this
  ·
    apply Subgroup.map_injective (adjointGroup τ K).subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    have key : (⨆ S ∈ {S | ∃ α, IsRoot τ α ∧
        S = (rootSubgroup τ K α).subgroupOf (adjointGroup τ K)},
        S).map (adjointGroup τ K).subtype = rootSpan τ K {α | IsRoot τ α} := by
      simp only [Subgroup.map_iSup]
      apply le_antisymm
      · refine iSup_le fun S => iSup_le fun hS => ?_
        obtain ⟨α, hα, rfl⟩ := hS
        refine le_iSup₂_of_le α hα ?_
        rw [Subgroup.subgroupOf_map_subtype]
        exact inf_le_left
      · refine iSup₂_le fun α hα => ?_
        refine le_iSup_of_le ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)) ?_
        refine le_iSup_of_le ⟨α, hα, rfl⟩ ?_
        rw [Subgroup.subgroupOf_map_subtype]
        exact le_inf le_rfl (rootSubgroup_le_adjointGroup α)
    rw [key, ← adjointGroup_eq_rootSpan]


omit [CharP K 2] in
theorem torusGroup_le_normalizer_rootSubgroup (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) :
    torusGroup τ K ≤ normalizer (rootSubgroup τ K α : Set (Module.End K (RootModule τ K))ˣ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  have hconj : ∀ (u : Kˣ) (g : (Module.End K (RootModule τ K))ˣ), g ∈ rootSubgroup τ K α →
      torusElt τ K i u * g * (torusElt τ K i u)⁻¹ ∈ rootSubgroup τ K α := by
    intro u g hg
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [root_torus_conjugation i hα u c]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  have hinv : (torusElt τ K i t)⁻¹ = torusElt τ K i t⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← torusElt_mul, mul_inv_cancel, torusElt_one]
  intro g
  refine ⟨hconj t g, fun hg => ?_⟩
  have := hconj t⁻¹ _ hg
  rw [← hinv, inv_inv] at this
  simpa [mul_assoc] using this


theorem twoLocalClosure_torus_eq_top (E : Subgroup (adjointGroup τ K))
    (hE : ∀ e ∈ E, ((e : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) ∈ torusGroup τ K) :
    twoLocalClosure E = ⊤ :=
  twoLocalClosure_adjoint_eq_top τ K E fun α hα e he g hg =>
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup τ K α hα
      (hE e he)) g).1 hg


omit [CharP K 2] in
theorem torusElt_pow' (i : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    torusElt τ K i (t ^ n) = torusElt τ K i t ^ n := by
  induction n with
  | zero => simp [torusElt_one]
  | succ n ih => rw [pow_succ, torusElt_mul, ih, pow_succ]

omit [CharP K 2] in
theorem torusElt_pow_rootVec (i : Fin τ.rank) (t : Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (n : ℕ) :
    ((torusElt τ K i t ^ n : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        (rootVec τ K α) =
      ((t ^ (n * ∑ j, τ.cartan i j * α j) : Kˣ) : K) • rootVec τ K α := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, torusElt_rootVec i t hα, map_smul, ih,
      smul_smul]
    congr 1
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    push_cast
    ring


theorem exists_rankTwo_torus_closure [Finite K] (i j : Fin τ.rank)
    (hji : τ.cartan j i = 0) (hij : τ.cartan i j = 0)
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card Kˣ) :
    ∃ E : Subgroup (adjointGroup τ K), IsPGroup p E ∧ 2 ≤ CFSG.Open.pRank p E ∧
      twoLocalClosure E = ⊤ := by
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  let a : adjointGroup τ K := ⟨torusElt τ K i ζ, torusElt_mem_adjointGroup i ζ⟩
  let b : adjointGroup τ K := ⟨torusElt τ K j ζ, torusElt_mem_adjointGroup j ζ⟩
  have ha : a ^ p = 1 := Subtype.ext (by
    show (torusElt τ K i ζ) ^ p = 1
    rw [← torusElt_pow', hζp, torusElt_one])
  have hb : b ^ p = 1 := Subtype.ext (by
    show (torusElt τ K j ζ) ^ p = 1
    rw [← torusElt_pow', hζp, torusElt_one])
  have hab : Commute a b := Subtype.ext (torusElt_mul_comm i j ζ ζ)
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let f : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* adjointGroup τ K :=
    { toFun := fun x => a ^ (Multiplicative.toAdd x.1).val * b ^ (Multiplicative.toAdd x.2).val
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, ZMod.val_add]
        rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
        have e := (hab.symm.pow_pow (Multiplicative.toAdd x.2).val
          (Multiplicative.toAdd y.1).val).eq
        calc _ = a ^ (Multiplicative.toAdd x.1).val * (a ^ (Multiplicative.toAdd y.1).val *
              b ^ (Multiplicative.toAdd x.2).val) * b ^ (Multiplicative.toAdd y.2).val := by
              simp only [mul_assoc]
          _ = a ^ (Multiplicative.toAdd x.1).val * (b ^ (Multiplicative.toAdd x.2).val *
              a ^ (Multiplicative.toAdd y.1).val) * b ^ (Multiplicative.toAdd y.2).val := by
              rw [e]
          _ = _ := by simp only [mul_assoc] }
  have hsum : ∀ (k l : Fin τ.rank), ∑ m, τ.cartan k m * (Pi.single l (1 : ℤ) : Fin τ.rank → ℤ) m =
      τ.cartan k l := by
    intro k l; simp [Pi.single_apply]
  have hvne : ∀ l : Fin τ.rank, rootVec τ K (Pi.single l 1) ≠ 0 := by
    intro l h
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ l)] at h
    exact one_ne_zero (Finsupp.single_eq_zero.1 h)
  have hcoef : ∀ (l : Fin τ.rank) (c : K), c • rootVec τ K (Pi.single l 1) =
      rootVec τ K (Pi.single l 1) → c = 1 := by
    intro l c h
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ l)] at h
    have := DFunLike.congr_fun h (Sum.inr ⟨Pi.single l 1, isRoot_single τ l⟩)
    simpa using this
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x1, x2⟩ hx
    have hx' : (torusElt τ K i ζ) ^ (Multiplicative.toAdd x1).val *
        (torusElt τ K j ζ) ^ (Multiplicative.toAdd x2).val = 1 := congrArg Subtype.val hx
    have hi := isRoot_single τ i
    have hj := isRoot_single τ j
    have hdiv : ∀ m : ℕ, m < p → (ζ ^ ((m : ℤ) * 2) : Kˣ) = 1 → m = 0 := by
      intro m hm hz
      have h1 : (p : ℤ) ∣ (m : ℤ) * 2 := by
        rw [← hζ]; exact orderOf_dvd_iff_zpow_eq_one.2 hz
      have h2 : p ∣ m * 2 := by exact_mod_cast h1
      rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h | h
      · exact Nat.eq_zero_of_dvd_of_lt h hm
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h) hp2
    have e1 := congrArg (fun g : (Module.End K (RootModule τ K))ˣ =>
      (g : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single i 1))) hx'
    have e2 := congrArg (fun g : (Module.End K (RootModule τ K))ˣ =>
      (g : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single j 1))) hx'
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at e1 e2
    rw [torusElt_pow_rootVec τ K j ζ hi, map_smul, torusElt_pow_rootVec τ K i ζ hi, smul_smul,
      hsum, hsum, hji, Tag.cartan_self] at e1
    rw [torusElt_pow_rootVec τ K j ζ hj, map_smul, torusElt_pow_rootVec τ K i ζ hj, smul_smul,
      hsum, hsum, hij, Tag.cartan_self] at e2
    have c1 := hcoef i _ e1
    have c2 := hcoef j _ e2
    simp only [mul_zero, zpow_zero, Units.val_one, one_mul, mul_one] at c1 c2
    have u1 : (ζ ^ (((Multiplicative.toAdd x1).val : ℤ) * 2) : Kˣ) = 1 :=
      Units.ext (by simpa using c1)
    have u2 : (ζ ^ (((Multiplicative.toAdd x2).val : ℤ) * 2) : Kˣ) = 1 :=
      Units.ext (by simpa using c2)
    have z1 := hdiv _ (ZMod.val_lt _) u1
    have z2 := hdiv _ (ZMod.val_lt _) u2
    refine Prod.ext ?_ ?_
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).1 z1)
    · exact Multiplicative.toAdd.injective (by simpa using (ZMod.val_eq_zero _).1 z2)
  refine ⟨f.range, ?_, ?_, ?_⟩
  ·
    intro g
    obtain ⟨x, hx⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hx, ← map_pow]
    have : x ^ p = 1 := by
      refine Prod.ext ?_ ?_
      · apply Multiplicative.toAdd.injective
        simp [toAdd_pow, nsmul_eq_mul]
      · apply Multiplicative.toAdd.injective
        simp [toAdd_pow, nsmul_eq_mul]
    rw [this, map_one]
  ·
    refine CFSG.SectionRank.le_pRank_of_injective (A := Multiplicative (ZMod p) ×
      Multiplicative (ZMod p)) hp.out.one_lt (fun x y => mul_comm x y) ?_ ?_ f hinj le_rfl
    · intro x
      refine Prod.ext ?_ ?_
      · apply Multiplicative.toAdd.injective
        simp [toAdd_pow, nsmul_eq_mul]
      · apply Multiplicative.toAdd.injective
        simp [toAdd_pow, nsmul_eq_mul]
    · rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]; ring
  ·
    apply twoLocalClosure_torus_eq_top τ K
    intro e he
    obtain ⟨x, rfl⟩ := he
    have hai : (torusElt τ K i ζ) ∈ torusGroup τ K := Subgroup.subset_closure ⟨(i, ζ), rfl⟩
    have hbj : (torusElt τ K j ζ) ∈ torusGroup τ K := Subgroup.subset_closure ⟨(j, ζ), rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hai _) (Subgroup.pow_mem _ hbj _)


variable [Finite K]

theorem exists_closure_top_of_chevalley_iso {G : Type} [Group G] [Finite G]
    (e : G ≃* adjointGroup τ K) (i j : Fin τ.rank) (hji : τ.cartan j i = 0)
    (hij : τ.cartan i j = 0) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card Kˣ) :
    ∃ E : Subgroup G, IsPGroup p E ∧ 2 ≤ CFSG.Open.pRank p E ∧ twoLocalClosure E = ⊤ := by
  obtain ⟨E, hE, hr, hc⟩ := exists_rankTwo_torus_closure τ K i j hji hij p hp2 hdvd
  refine ⟨E.map e.symm.toMonoidHom, hE.map _, ?_, ?_⟩
  · exact hr.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp.out
      e.symm.toMonoidHom e.symm.injective E)
  · refine top_le_iff.mp ?_
    have := map_twoLocalClosure_le e.symm E
    rw [hc, Subgroup.map_top] at this
    have hr : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.symm.toEquiv.surjective
    rw [hr] at this
    exact this


theorem not_rankThreeUC_of_chevalley_iso {G : Type} [Group G] [Finite G] (hS : Standing G)
    (e : G ≃* adjointGroup τ K) (i j : Fin τ.rank) (hji : τ.cartan j i = 0)
    (hij : τ.cartan i j = 0) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card Kˣ) : ¬ rankThreeUC G := by
  intro hUC
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨E, hE, hr, hc⟩ := exists_closure_top_of_chevalley_iso τ K e i j hji hij p hp2 hdvd
  exact twoLocalClosure_ne_top hS hUC hp hE hr hc

end CFSG.LocalAnalysis.RankThreeUC
