module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux0
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem exists_finset_pow_eq {L : Type} [Field L] [IsAlgClosed L] (m : ℕ) (hm : 2 ≤ m)
    (hm0 : (m : L) = 0) (e : L) (he : e ≠ 0) :
    ∃ A : Finset L, m ≤ A.card ∧ ∀ a ∈ A, e * a ^ m = a := by
  classical
  set p : Polynomial L := Polynomial.C e * Polynomial.X ^ m - Polynomial.X with hp
  have hdeg : p.natDegree = m := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X_pow m e he
    · rw [Polynomial.natDegree_C_mul_X_pow m e he, Polynomial.natDegree_X]
      omega
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
    omega
  have hder : Polynomial.derivative p = -1 := by
    rw [hp, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow, Polynomial.derivative_X,
      hm0, mul_zero, Polynomial.C_0, zero_mul, zero_sub]
  have hsep : p.Separable := by
    rw [Polynomial.separable_def, hder]
    exact isCoprime_one_right.neg_right
  refine ⟨p.roots.toFinset, ?_, fun a ha => ?_⟩
  · rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def] at ha
    simpa [hp, sub_eq_zero] using ha

theorem exists_root_pow {L : Type} [Field L] [IsAlgClosed L] (m : ℕ) (hm : 2 ≤ m) (e : L)
    (he : e ≠ 0) (κ : L) : ∃ c : L, e * c ^ m + κ = c := by
  classical
  set p : Polynomial L := Polynomial.C e * Polynomial.X ^ m - Polynomial.X + Polynomial.C κ with hp
  have hdeg : p.natDegree = m := by
    rw [hp, Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X_pow m e he
    · rw [Polynomial.natDegree_C_mul_X_pow m e he, Polynomial.natDegree_X]
      omega
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree (p := p) (by
      intro h
      rw [h] at hdeg
      simp at hdeg
      omega), hdeg]
    exact_mod_cast (by omega : m ≠ 0))
  refine ⟨c, ?_⟩
  simp only [hp, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hc
  linear_combination hc

theorem odd_card (hodd : ringChar K ≠ 2) : Odd (Nat.card K) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn]
  exact (hp.eq_two_or_odd'.resolve_left hodd).pow

theorem natCast_card_eq_zero (L : Type) [Field L] [Algebra K L] : ((Nat.card K : ℕ) : L) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have h : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  rw [← map_natCast (algebraMap K L), h, map_zero]


@[expose] def SigFixed (D : LangLevi Tag.F4 K wF) (x : ModGL Tag.F4 D.L) : Prop :=
  canonicalRep (coxeterSystem Tag.F4) D.L wF * Units.map (entrywiseHom D.Fr) x *
    (canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹ = x

theorem fixed_conj (D : LangLevi Tag.F4 K wF) {x : ModGL Tag.F4 D.L} (hfix : SigFixed D x) :
    Units.map (entrywiseHom D.Fr) (D.g * x * D.g⁻¹) = D.g * x * D.g⁻¹ := by
  have h := D.lang
  have h2 : canonicalRep (coxeterSystem Tag.F4) D.L wF * Units.map (entrywiseHom D.Fr) x *
      (canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹ = x := hfix
  rw [map_mul, map_mul, map_inv, h]
  calc D.g * canonicalRep (coxeterSystem Tag.F4) D.L wF * Units.map (entrywiseHom D.Fr) x *
        (D.g * canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹
      = D.g * (canonicalRep (coxeterSystem Tag.F4) D.L wF * Units.map (entrywiseHom D.Fr) x *
          (canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹) * D.g⁻¹ := by group
    _ = D.g * x * D.g⁻¹ := by rw [h2]

theorem sigma_fixed_rational (D : LangLevi Tag.F4 K wF) {x : ModGL Tag.F4 D.L}
    (hx : x ∈ adjointGroup Tag.F4 D.L) (hfix : SigFixed D x) :
    ∃ x₀ ∈ adjointGroup Tag.F4 K,
      baseChangeGL (algebraMap K D.L) x₀ = D.g * x * D.g⁻¹ := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hg : D.g ∈ adjointGroup Tag.F4 D.L := parabolicLevi_le_adjointGroup _ _ _ D.g_mem
  have hxh : D.g * x * D.g⁻¹ ∈ adjointGroup Tag.F4 D.L := mul_mem (mul_mem hg hx) (inv_mem hg)
  obtain ⟨x₀, hx₀, hb⟩ := Subgroup.mem_map.1
    (mem_map_adjointGroup_F4_of_frobenius_fixed D.Fr D.hFr hxh (fixed_conj D hfix))
  exact ⟨x₀, hx₀, hb⟩

theorem exists_radList (τ : Tag) : ∃ l : List (Fin τ.rank → ℤ), l.Nodup ∧
    ∀ α, α ∈ l ↔ α ∈ parabolicRadicalRoots τ (Jθ τ) :=
  exists_list_of_finite ((finite_setOf_isRoot τ).subset fun _ h => h.1.1)

theorem exists_rational_Qθ (D : LangLevi Tag.F4 K wF) {y : ModGL Tag.F4 D.L}
    (hy : y ∈ Qθ Tag.F4 D.L) (hfix : Units.map (entrywiseHom D.Fr) y = y) :
    ∃ y₀ ∈ Qθ Tag.F4 K, baseChangeGL (algebraMap K D.L) y₀ = y := by
  classical
  obtain ⟨l, hl, hlS⟩ := exists_radList Tag.F4
  have hpos : ∀ α ∈ l, IsRoot Tag.F4 α ∧ 0 < height α := fun α hα => ((hlS α).1 hα).1
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq D.L (S := parabolicRadicalRoots Tag.F4 (Jθ Tag.F4))
    (fun α hα => hα.1)
    (fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr) hl hlS hy
  have hFy : (l.map fun α => pinnedX Tag.F4 D.L α (D.Fr (c α))).prod = y := by
    rw [← hfix, ← hc, map_list_prod, List.map_map]
    congr 2
    funext α
    simp [Function.comp, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX]
  have heq := pinnedX_list_prod_injective l hl hpos (fun α => D.Fr (c α)) c (hFy.trans hc.symm)
  have hrat : ∀ α ∈ l, ∃ d : K, algebraMap K D.L d = c α := fun α hα =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← D.hFr]; exact heq α hα)
  choose! d hd using hrat
  refine ⟨(l.map fun α => pinnedX Tag.F4 K α (d α)).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan ((hlS α).1 hα) (d α)
  · rw [map_list_prod, List.map_map, ← hc]
    congr 1
    refine List.map_congr_left fun α hα => ?_
    simp only [Function.comp, baseChangeGL_pinnedX, hd α hα]

theorem sigma_fixed_rational_Qθ (D : LangLevi Tag.F4 K wF) {x : ModGL Tag.F4 D.L}
    (hx : x ∈ Qθ Tag.F4 D.L) (hfix : SigFixed D x) :
    ∃ x₀ ∈ Qθ Tag.F4 K, baseChangeGL (algebraMap K D.L) x₀ = D.g * x * D.g⁻¹ := by
  have hnorm := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.F4) (K := D.L)
    (Jθ Tag.F4) (parabolicLevi_le_parabolicSubgroup (Jθ Tag.F4) D.g_mem)
  have hxh : D.g * x * D.g⁻¹ ∈ Qθ Tag.F4 D.L := (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx
  exact exists_rational_Qθ D hxh (fixed_conj D hfix)

theorem mem_frame_of_rational (D : LangLevi Tag.F4 K wF) {S : Set (Fin Tag.F4.rank → ℤ)}
    {x : ModGL Tag.F4 D.L} (hx : x ∈ rootSpan Tag.F4 D.L S) {x₀ : ModGL Tag.F4 K}
    (h0 : x₀ ∈ adjointGroup Tag.F4 K)
    (hb : baseChangeGL (algebraMap K D.L) x₀ = D.g * x * D.g⁻¹) : x₀ ∈ D.frame S := by
  refine (TwBasicAux.mem_frame_iff D S x₀).2 ⟨h0, ?_⟩
  rw [hb]
  have e : D.g⁻¹ * (D.g * x * D.g⁻¹) * D.g = x := by group
  rw [e]
  exact hx

theorem frame_S₂_le_Lθ (D : LangLevi Tag.F4 K wF) :
    D.frame TwClass.f4Six.S₂ ≤ Lθ Tag.F4 K := by
  intro x hx
  have hUθ : Uθ Tag.F4 K ≤ D.frame TwClass.f4Six.S₁ :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.highRoot_mem_S₁ TwClass.f4Six)
      (Pθ_le_normalizer_Uθ Tag.F4 D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))
  have hUneg : Heis.Uneg Tag.F4 K ≤ D.frame TwClass.f4Six.S₁ :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.neg_highRoot_mem_S₁ TwClass.f4Six)
      (Lθ_le_normalizer_Uneg Tag.F4 D.L D.g_mem)
  have hc := TwBasicAux.frame_commute TwClass.f4Six D
  have hxG : x ∈ adjointGroup Tag.F4 K := ((TwBasicAux.mem_frame_iff D _ x).1 hx).1
  exact Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.F4 K hxG
    (fun u hu => (hc u (hUθ hu) x hx).symm) (fun u hu => (hc u (hUneg hu) x hx).symm)

theorem exists_sigmaFixed_single (D : LangLevi Tag.F4 K wF) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) (hwγ : wF • γ = γ) (hK : 3 ≤ Nat.card K) :
    ∃ T : Finset D.L, 3 ≤ T.card ∧ ∀ t ∈ T, SigFixed D (pinnedX Tag.F4 D.L γ t) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L wF hγ
  have hε0 : ε ≠ 0 := fun h => by rw [h] at hε; simp at hε
  obtain ⟨T, hT, hTe⟩ := exists_finset_pow_eq (L := D.L) (Nat.card K) (by omega)
    (natCast_card_eq_zero D.L) ε hε0
  refine ⟨T, by omega, fun t ht => ?_⟩
  unfold SigFixed
  rw [CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, hconj, hwγ, D.hFr, hTe t ht]

theorem exists_sigmaFixed_pair (D : LangLevi Tag.F4 K wF) {δ₁ δ₂ γ : Fin Tag.F4.rank → ℤ}
    (h₁ : IsRoot Tag.F4 δ₁) (h₂ : IsRoot Tag.F4 δ₂) (hγ : IsRoot Tag.F4 γ)
    (hw₁ : wF • δ₁ = δ₂) (hw₂ : wF • δ₂ = δ₁) (hwγ : wF • γ = γ) (N : ℤ)
    (hcomm : ∀ a b : D.L, pinnedX Tag.F4 D.L δ₁ a * pinnedX Tag.F4 D.L δ₂ b *
        pinnedX Tag.F4 D.L δ₁ (-a) * pinnedX Tag.F4 D.L δ₂ (-b) =
      pinnedX Tag.F4 D.L γ ((N : D.L) * a * b))
    (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2) :
    ∃ (e : D.L) (A : Finset D.L), e ≠ 0 ∧ 2 * Nat.card K + 2 < A.card ∧
      ∀ a ∈ A, ∃ c : D.L, SigFixed D (pinnedX Tag.F4 D.L γ c * pinnedX Tag.F4 D.L δ₁ a *
        pinnedX Tag.F4 D.L δ₂ (e * a ^ Nat.card K)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ε₁, hε₁, h₁c⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L wF h₁
  obtain ⟨ε₂, hε₂, h₂c⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L wF h₂
  obtain ⟨ε₃, hε₃, h₃c⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L wF hγ
  have hε₁0 : ε₁ ≠ 0 := fun h => by rw [h] at hε₁; simp at hε₁
  have hε₂0 : ε₂ ≠ 0 := fun h => by rw [h] at hε₂; simp at hε₂
  have hε₃0 : ε₃ ≠ 0 := fun h => by rw [h] at hε₃; simp at hε₃
  set q := Nat.card K with hq
  have hq0 : (q : D.L) = 0 := natCast_card_eq_zero D.L
  have hε₁q : ε₁ ^ q = ε₁ := by
    obtain ⟨k, hk⟩ := odd_card hodd
    rw [← hq] at hk
    rw [hk, pow_succ, pow_mul, sq, hε₁, one_pow, one_mul]
  obtain ⟨A, hA, hAe⟩ := exists_finset_pow_eq (L := D.L) (q ^ 2) (by nlinarith)
    (by rw [Nat.cast_pow, hq0]; simp) (ε₂ * ε₁) (mul_ne_zero hε₂0 hε₁0)
  refine ⟨ε₁, A, hε₁0, by nlinarith, fun a ha => ?_⟩
  set b := ε₁ * a ^ q with hb
  obtain ⟨c, hc⟩ := exists_root_pow (L := D.L) q (by omega) ε₃ hε₃0 (-((N : D.L) * a * b))
  refine ⟨c, ?_⟩
  unfold SigFixed
  set n := canonicalRep (coxeterSystem Tag.F4) D.L wF with hn
  have hba : ε₂ * b ^ q = a := by
    have h := hAe a ha
    rw [hb, mul_pow, hε₁q, ← pow_mul, ← sq, ← mul_assoc]
    exact h
  have hswap : pinnedX Tag.F4 D.L δ₂ b * pinnedX Tag.F4 D.L δ₁ a =
      pinnedX Tag.F4 D.L γ (-((N : D.L) * a * b)) * (pinnedX Tag.F4 D.L δ₁ a *
        pinnedX Tag.F4 D.L δ₂ b) := by
    have h := hcomm a b
    rw [← pinnedX_neg, ← pinnedX_neg] at h
    rw [← pinnedX_neg, ← h]
    group
  simp only [map_mul, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, D.hFr]
  calc n * (pinnedX Tag.F4 D.L γ (c ^ q) * pinnedX Tag.F4 D.L δ₁ (a ^ q) *
        pinnedX Tag.F4 D.L δ₂ (b ^ q)) * n⁻¹
      = (n * pinnedX Tag.F4 D.L γ (c ^ q) * n⁻¹) * (n * pinnedX Tag.F4 D.L δ₁ (a ^ q) * n⁻¹) *
        (n * pinnedX Tag.F4 D.L δ₂ (b ^ q) * n⁻¹) := by group
    _ = pinnedX Tag.F4 D.L γ (ε₃ * c ^ q) * pinnedX Tag.F4 D.L δ₂ (ε₁ * a ^ q) *
        pinnedX Tag.F4 D.L δ₁ (ε₂ * b ^ q) := by
        rw [h₃c, h₁c, h₂c, hwγ, hw₁, hw₂]
    _ = pinnedX Tag.F4 D.L γ (ε₃ * c ^ q) * (pinnedX Tag.F4 D.L δ₂ b *
        pinnedX Tag.F4 D.L δ₁ a) := by rw [hba, ← hb, mul_assoc]
    _ = pinnedX Tag.F4 D.L γ c * pinnedX Tag.F4 D.L δ₁ a * pinnedX Tag.F4 D.L δ₂ b := by
        rw [hswap, ← mul_assoc, ← mul_assoc, ← pinnedX_add, hc, mul_assoc]

theorem isRoot_r3 : IsRoot Tag.F4 r3 := isRoot_single Tag.F4 2
theorem isRoot_r4 : IsRoot Tag.F4 r4 := isRoot_single Tag.F4 3
theorem isRoot_r34 : IsRoot Tag.F4 (r3 + r4) := by
  have h : (r3 + r4 : Fin Tag.F4.rank → ℤ) ∈ rootFinset Tag.F4 := by
    unfold r3 r4; decide +kernel
  exact mem_rootFinset.1 h
theorem isRoot_neg_r3 : IsRoot Tag.F4 (-r3) := IsRoot.neg isRoot_r3
theorem isRoot_neg_r4 : IsRoot Tag.F4 (-r4) := IsRoot.neg isRoot_r4
theorem isRoot_neg_r34 : IsRoot Tag.F4 (-(r3 + r4)) := IsRoot.neg isRoot_r34
theorem isRoot_alpha1 : IsRoot Tag.F4 alpha1 := mem_rootFinset.1 (by decide +kernel)
theorem isRoot_root1342 : IsRoot Tag.F4 root1342 := mem_rootFinset.1 (by decide +kernel)

theorem wF_neg_r3 : wF • (-r3) = -r4 := by rw [smul_neg, wF_r3]
theorem wF_neg_r4 : wF • (-r4) = -r3 := by rw [smul_neg, wF_r4]
theorem wF_neg_r34 : wF • (-(r3 + r4)) = -(r3 + r4) := by rw [smul_neg, wF_r34]

theorem f4ShortList_S₂ : ∀ α ∈ f4ShortList, α ∈ rootFinset Tag.F4 ∧
    ∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → α i = 0 := by decide +kernel

theorem mem_S₂ {α : Fin Tag.F4.rank → ℤ} (h : α ∈ f4ShortList) : α ∈ TwClass.f4Six.S₂ :=
  ⟨mem_rootFinset.1 (f4ShortList_S₂ α h).1, (f4ShortList_S₂ α h).2⟩

theorem f4LongList_S₁ : ∀ β ∈ f4LongList, β ∈ rootFinset Tag.F4 ∧
    ∀ α ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → α i = 0) →
      CFSG.LieType.Steinberg.Adjoint.iform β α = 0 := by decide +kernel

theorem mem_S₁ {β : Fin Tag.F4.rank → ℤ} (h : β ∈ f4LongList) : β ∈ TwClass.f4Six.S₁ :=
  ⟨mem_rootFinset.1 (f4LongList_S₁ β h).1, fun α hα =>
    (f4LongList_S₁ β h).2 α (mem_rootFinset.2 hα.1) hα.2⟩

theorem r3_mem : r3 ∈ f4ShortList := by unfold r3; decide +kernel
theorem r4_mem : r4 ∈ f4ShortList := by unfold r4; decide +kernel
theorem r34_mem : (r3 + r4) ∈ f4ShortList := by unfold r3 r4; decide +kernel
theorem neg_r3_mem : (-r3) ∈ f4ShortList := by unfold r3; decide +kernel
theorem neg_r4_mem : (-r4) ∈ f4ShortList := by unfold r4; decide +kernel
theorem neg_r34_mem : (-(r3 + r4)) ∈ f4ShortList := by unfold r3 r4; decide +kernel
theorem alpha1_mem : alpha1 ∈ f4LongList := by decide +kernel
theorem root1342_mem : root1342 ∈ f4LongList := by decide +kernel
theorem theta_mem' : highRoot Tag.F4 ∈ f4LongList := by
  rw [← theta_eq]; decide +kernel

theorem commPairs_eq_single' {α β : Fin Tag.F4.rank → ℤ}
    (h : ∀ p ∈ commCandidates, p.1 • α + p.2 • β ∈ rootFinset .F4 ↔ p = (1, 1)) :
    commPairs .F4 α β = [(1, 1)] := by
  classical
  have hc : ∀ p ∈ commCandidates, decide (IsRoot Tag.F4 (p.1 • α + p.2 • β)) =
      decide (p = (1, 1)) := fun p hp => by
    rw [decide_eq_decide, ← mem_rootFinset (τ := Tag.F4)]
    exact h p hp
  unfold commPairs
  rw [List.filter_congr hc]
  decide

theorem comm_of_commPairs {γ μ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ)
    (hμ : IsRoot Tag.F4 μ) (hne : γ ≠ μ) (hne' : γ ≠ -μ) (hcp : commPairs .F4 γ μ = [(1, 1)]) :
    ∃ N : ℤ, ∀ (R : Type) [CommRing R] (a b : R),
      pinnedX Tag.F4 R γ a * pinnedX Tag.F4 R μ b * pinnedX Tag.F4 R γ (-a) *
        pinnedX Tag.F4 R μ (-b) = pinnedX Tag.F4 R (γ + μ) ((N : R) * a * b) := by
  obtain ⟨-, hF⟩ := ActionAux.f4CommConst_spec hγ hμ hne hne'
  refine ⟨ActionAux.f4CommConst γ μ (1, 1), fun R _ a b => ?_⟩
  have h := hF R a b
  rw [hcp] at h
  simpa [one_smul, pow_one] using h

theorem pair_comm_s2 : ∃ N : ℤ, ∀ (R : Type) [CommRing R] (a b : R),
    pinnedX Tag.F4 R r3 a * pinnedX Tag.F4 R r4 b * pinnedX Tag.F4 R r3 (-a) *
      pinnedX Tag.F4 R r4 (-b) = pinnedX Tag.F4 R (r3 + r4) ((N : R) * a * b) :=
  comm_of_commPairs isRoot_r3 isRoot_r4 (by unfold r3 r4; decide +kernel)
    (by unfold r3 r4; decide +kernel) (commPairs_eq_single' (by unfold r3 r4; decide +kernel))

theorem pair_comm_s2_neg : ∃ N : ℤ, ∀ (R : Type) [CommRing R] (a b : R),
    pinnedX Tag.F4 R (-r3) a * pinnedX Tag.F4 R (-r4) b * pinnedX Tag.F4 R (-r3) (-a) *
      pinnedX Tag.F4 R (-r4) (-b) = pinnedX Tag.F4 R (-(r3 + r4)) ((N : R) * a * b) := by
  obtain ⟨N, hN⟩ := comm_of_commPairs isRoot_neg_r3 isRoot_neg_r4
    (by unfold r3 r4; decide +kernel) (by unfold r3 r4; decide +kernel)
    (commPairs_eq_single' (by unfold r3 r4; decide +kernel))
  refine ⟨N, fun R _ a b => ?_⟩
  have h := hN R a b
  rw [← neg_add] at h
  exact h

theorem pair_comm_s1 : ∃ N : ℤ, ∀ (R : Type) [CommRing R] (a b : R),
    pinnedX Tag.F4 R alpha1 a * pinnedX Tag.F4 R root1342 b * pinnedX Tag.F4 R alpha1 (-a) *
      pinnedX Tag.F4 R root1342 (-b) = pinnedX Tag.F4 R (highRoot Tag.F4) ((N : R) * a * b) := by
  obtain ⟨N, hN⟩ := comm_of_commPairs isRoot_alpha1 isRoot_root1342 (by decide +kernel)
    (by decide +kernel) (commPairs_eq_single' (by decide +kernel))
  have e : (alpha1 + root1342 : Fin Tag.F4.rank → ℤ) = highRoot Tag.F4 := by decide +kernel
  refine ⟨N, fun R _ a b => ?_⟩
  rw [← e]
  exact hN R a b

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
