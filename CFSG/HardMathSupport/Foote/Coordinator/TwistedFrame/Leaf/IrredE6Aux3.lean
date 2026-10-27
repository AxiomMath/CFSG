module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem comm_split {G : Type*} [Group G] {a b c d : G} (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    (a * c) * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (c * d * c⁻¹ * d⁻¹) := by
  have hY : Commute a (c * d * c⁻¹) := (hac.mul_right had).mul_right hac.inv_right
  have hZ : Commute b (c * d * c⁻¹ * d⁻¹) :=
    ((hbc.mul_right hbd).mul_right hbc.inv_right).mul_right hbd.inv_right
  calc (a * c) * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * (d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * b * ((c * d * c⁻¹) * a⁻¹) * d⁻¹ * b⁻¹ := by rw [← hbc.eq]; group
    _ = a * b * (a⁻¹ * (c * d * c⁻¹)) * d⁻¹ * b⁻¹ := by rw [hY.inv_left.eq.symm]
    _ = a * b * a⁻¹ * ((c * d * c⁻¹ * d⁻¹) * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (c * d * c⁻¹ * d⁻¹)) := by rw [hZ.inv_left.eq.symm]
    _ = (a * b * a⁻¹ * b⁻¹) * (c * d * c⁻¹ * d⁻¹) := by group

section Lang

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

@[expose] def SigFix (x : ModGL τ D.L) : Prop :=
  canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) x *
    (canonicalRep (coxeterSystem τ) D.L w)⁻¹ = x

theorem frob_conj {x : ModGL τ D.L} (hfix : SigFix D x) :
    Units.map (entrywiseHom D.Fr) (D.g * x * D.g⁻¹) = D.g * x * D.g⁻¹ := by
  have h := D.lang
  have h2 : canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) x *
      (canonicalRep (coxeterSystem τ) D.L w)⁻¹ = x := hfix
  rw [map_mul, map_mul, map_inv, h]
  calc D.g * canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) x *
        (D.g * canonicalRep (coxeterSystem τ) D.L w)⁻¹
      = D.g * (canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) x *
          (canonicalRep (coxeterSystem τ) D.L w)⁻¹) * D.g⁻¹ := by group
    _ = D.g * x * D.g⁻¹ := by rw [h2]

theorem sigFix_transport (x₀ : ModGL τ K) :
    SigFix D (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x₀ * D.g) := by
  unfold SigFix
  have h := D.lang
  have hb : Units.map (entrywiseHom D.Fr) (baseChangeGL (algebraMap K D.L) x₀) =
      baseChangeGL (algebraMap K D.L) x₀ :=
    units_map_entrywiseHom_baseChangeGL_algebraMap D.Fr D.hFr x₀
  rw [map_mul, map_mul, map_inv, h, hb]
  group

theorem sigma_pinnedX {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : D.L, ε * ε = 1 ∧ ∀ c : D.L,
      canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) (pinnedX τ D.L α c) *
        (canonicalRep (coxeterSystem τ) D.L w)⁻¹ =
      pinnedX τ D.L (w • α) (ε * c ^ Nat.card K) := by
  obtain ⟨ε, hε, hc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L w hα
  refine ⟨ε, hε, fun c => ?_⟩
  rw [CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, hc, D.hFr]

theorem exists_rational_Qθ_sig {x : ModGL τ D.L} (hx : x ∈ Qθ τ D.L) (hfix : SigFix D x) :
    ∃ x₀ ∈ Qθ τ K, baseChangeGL (algebraMap K D.L) x₀ = D.g * x * D.g⁻¹ := by
  have hnorm := parabolicSubgroup_le_normalizer_parabolicRadical (τ := τ) (K := D.L)
    (Jθ τ) (parabolicLevi_le_parabolicSubgroup (Jθ τ) D.g_mem)
  have hxh : D.g * x * D.g⁻¹ ∈ Qθ τ D.L := (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx
  exact exists_rational_Qθ D hxh (frob_conj D hfix)

theorem Fr_bijective : Function.Bijective D.Fr := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  exact frobenius_bijective D.Fr D.hFr

theorem fixedFieldImage_eq_map :
    fixedFieldImage τ (RingEquiv.ofBijective D.Fr (Fr_bijective D)) =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K D.L)) := by
  rw [fixedFieldImage_eq_closure, map_baseChangeGL_adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨a, rfl⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (L := D.L)
        (c := c) (by rw [← D.hFr]; exact hc)
      exact ⟨i, a, Or.inl rfl⟩
    · obtain ⟨a, rfl⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (L := D.L)
        (c := c) (by rw [← D.hFr]; exact hc)
      exact ⟨i, a, Or.inr rfl⟩
  · rintro ⟨i, a, rfl | rfl⟩
    · refine ⟨i, algebraMap K D.L a, ?_, Or.inl rfl⟩
      exact congrArg (fun f => f a) (frobenius_comp_algebraMap D.Fr D.hFr)
    · refine ⟨i, algebraMap K D.L a, ?_, Or.inr rfl⟩
      exact congrArg (fun f => f a) (frobenius_comp_algebraMap D.Fr D.hFr)

theorem exists_rational_comm {y₁ y₂ : ModGL τ D.L} (h₁ : y₁ ∈ adjointGroup τ D.L)
    (h₂ : y₂ ∈ adjointGroup τ D.L) (f₁ : SigFix D y₁) (f₂ : SigFix D y₂) :
    ∃ l ∈ adjointGroup τ K, baseChangeGL (algebraMap K D.L) l =
      D.g * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * D.g⁻¹ := by
  set σ : D.L ≃+* D.L := RingEquiv.ofBijective D.Fr (Fr_bijective D) with hσ
  have hσfr : (σ : D.L →+* D.L) = D.Fr := RingHom.ext fun _ => rfl
  have hg : D.g ∈ adjointGroup τ D.L := parabolicLevi_le_adjointGroup τ D.L (Jθ τ) D.g_mem
  have hΓ : ∀ y, y ∈ adjointGroup τ D.L → SigFix D y →
      D.g * y * D.g⁻¹ ∈ entrywiseFixedGroup τ σ := by
    intro y hy hf
    have hm : D.g * y * D.g⁻¹ ∈ adjointGroup τ D.L := mul_mem (mul_mem hg hy) (inv_mem hg)
    refine ⟨hm, ?_⟩
    show Units.map (entrywiseHom (σ : D.L →+* D.L)) (D.g * y * D.g⁻¹) = D.g * y * D.g⁻¹
    rw [hσfr]
    exact frob_conj D hf
  have ha := hΓ y₁ h₁ f₁
  have hb := hΓ y₂ h₂ f₂
  set a := D.g * y₁ * D.g⁻¹
  set b := D.g * y₂ * D.g⁻¹
  have h := entrywiseFixedGroup_quotient_comm (τ := τ) (σ := σ)
    (QuotientGroup.mk ⟨a⁻¹, inv_mem ha⟩) (QuotientGroup.mk ⟨b⁻¹, inv_mem hb⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h2 : (a⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * a⁻¹) ∈ fixedFieldImage τ σ := h
  have e : D.g * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * D.g⁻¹ = ((a⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * a⁻¹))⁻¹ := by
    simp only [a, b]
    group
  have h3 := (fixedFieldImage τ σ).inv_mem h2
  rw [← e, fixedFieldImage_eq_map] at h3
  obtain ⟨l, hl, hle⟩ := h3
  exact ⟨l, hl, hle⟩

end Lang

section E6

variable {K : Type} [Field K] [Finite K] (D : LangLevi Tag.E6 K wE)

theorem frame_S₂_le_Lθ : D.frame TwClass.e6Six.S₂ ≤ Lθ Tag.E6 K := by
  intro x hx
  have hUθ : Uθ Tag.E6 K ≤ D.frame TwClass.e6Six.S₁ :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.highRoot_mem_S₁ TwClass.e6Six)
      (Pθ_le_normalizer_Uθ Tag.E6 D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))
  have hUneg : Heis.Uneg Tag.E6 K ≤ D.frame TwClass.e6Six.S₁ :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.neg_highRoot_mem_S₁ TwClass.e6Six)
      (Lθ_le_normalizer_Uneg Tag.E6 D.L D.g_mem)
  have hc := TwBasicAux.frame_commute TwClass.e6Six D
  have hxG : x ∈ adjointGroup Tag.E6 K := ((TwBasicAux.mem_frame_iff D _ x).1 hx).1
  exact Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.E6 K hxG
    (fun u hu => (hc u (hUθ hu) x hx).symm) (fun u hu => (hc u (hUneg hu) x hx).symm)

theorem S1_facts : ∀ β ∈ ([highRoot Tag.E6, a2, b2] : List V6), β ∈ rootFinset Tag.E6 ∧
    ∀ α ∈ rootFinset Tag.E6, (∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → α i = 0) →
      CFSG.LieType.Steinberg.Adjoint.iform β α = 0 := by
  decide +kernel

theorem mem_S₁ {β : V6} (h : β ∈ ([highRoot Tag.E6, a2, b2] : List V6)) :
    β ∈ TwClass.e6Six.S₁ :=
  ⟨mem_rootFinset.1 (S1_facts β h).1, fun α hα =>
    (S1_facts β h).2 α (mem_rootFinset.2 hα.1) hα.2⟩

theorem exists_sigFix_S1 (hK : 3 ≤ Nat.card K) :
    ∃ (e : D.L) (A : Finset D.L), e ≠ 0 ∧ Nat.card K < A.card ∧ ∀ a ∈ A, ∃ c : D.L,
      SigFix D (pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
        pinnedX Tag.E6 D.L b2 (e * a ^ Nat.card K)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ε₁, hε₁, h₁c⟩ := sigma_pinnedX D (mem_rootFinset.1 (a2_mem_Deg1.1 |> fun h =>
    mem_rootFinset.2 h))
  obtain ⟨ε₂, hε₂, h₂c⟩ := sigma_pinnedX D (b2_mem_Deg1.1)
  obtain ⟨ε₃, hε₃, h₃c⟩ := sigma_pinnedX D (isRoot_highRoot Tag.E6)
  have hε₁0 : ε₁ ≠ 0 := fun h => by rw [h] at hε₁; simp at hε₁
  have hε₂0 : ε₂ ≠ 0 := fun h => by rw [h] at hε₂; simp at hε₂
  have hε₃0 : ε₃ ≠ 0 := fun h => by rw [h] at hε₃; simp at hε₃
  set q := Nat.card K with hq
  have hq0 : (q : D.L) = 0 := natCast_card_eq_zero K D.L
  obtain ⟨A, hA, hAe⟩ := exists_finset_pow_eq (E := D.L) (q ^ 2) (by nlinarith)
    (by rw [Nat.cast_pow, hq0]; simp) (ε₂ * ε₁ ^ q) (mul_ne_zero hε₂0 (pow_ne_zero _ hε₁0))
  have hsum : a2 + b2 = highRoot Tag.E6 := by rw [b2_eq]; abel
  have hne : a2 ≠ b2 := a2_ne_b2
  have hne' : a2 ≠ -b2 := by
    intro h
    have h1 := congrFun h 1
    have h2 : b2 1 = 1 := (mem_Deg1_E6.1 b2_mem_Deg1).2
    have h3 : a2 1 = 1 := (mem_Deg1_E6.1 a2_mem_Deg1).2
    rw [Pi.neg_apply, h2, h3] at h1
    omega
  obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6
    a2_mem_Deg1.1 b2_mem_Deg1.1 hne hne').1 (by rw [hsum]; exact isRoot_highRoot _)
  set N : ℤ := commConst Tag.E6 a2 b2 (1, 1)
  have hcomm : ∀ a b : D.L, pinnedX Tag.E6 D.L a2 a * pinnedX Tag.E6 D.L b2 b *
      pinnedX Tag.E6 D.L a2 (-a) * pinnedX Tag.E6 D.L b2 (-b) =
      pinnedX Tag.E6 D.L (highRoot Tag.E6) ((N : D.L) * a * b) := by
    intro a b
    have h := hform D.L a b
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, hsum] at h
    exact h
  refine ⟨ε₁, A, hε₁0, by nlinarith, fun a ha => ?_⟩
  set b := ε₁ * a ^ q with hb
  obtain ⟨c, hc⟩ := exists_root_pow (E := D.L) q (by omega) ε₃ hε₃0 (-((N : D.L) * a * b))
  refine ⟨c, ?_⟩
  unfold SigFix
  set n := canonicalRep (coxeterSystem Tag.E6) D.L wE with hn
  have hba : ε₂ * b ^ q = a := by
    have h := hAe a ha
    rw [hb, mul_pow, ← pow_mul, ← sq, ← mul_assoc]
    exact h
  have hswap : pinnedX Tag.E6 D.L b2 b * pinnedX Tag.E6 D.L a2 a =
      pinnedX Tag.E6 D.L (highRoot Tag.E6) (-((N : D.L) * a * b)) *
        (pinnedX Tag.E6 D.L a2 a * pinnedX Tag.E6 D.L b2 b) := by
    have h := hcomm a b
    rw [← pinnedX_neg, ← pinnedX_neg] at h
    rw [← pinnedX_neg, ← h]
    group
  have hF : ∀ x y z : ModGL Tag.E6 D.L, n * Units.map (entrywiseHom D.Fr) (x * y * z) * n⁻¹ =
      (n * Units.map (entrywiseHom D.Fr) x * n⁻¹) * (n * Units.map (entrywiseHom D.Fr) y * n⁻¹) *
        (n * Units.map (entrywiseHom D.Fr) z * n⁻¹) := by
    intro x y z
    rw [map_mul, map_mul]
    group
  rw [hF, h₃c, h₁c, h₂c, wE_theta, wE_a2, wE_b2]
  calc pinnedX Tag.E6 D.L (highRoot Tag.E6) (ε₃ * c ^ q) * pinnedX Tag.E6 D.L b2 (ε₁ * a ^ q) *
        pinnedX Tag.E6 D.L a2 (ε₂ * b ^ q)
      = pinnedX Tag.E6 D.L (highRoot Tag.E6) (ε₃ * c ^ q) * (pinnedX Tag.E6 D.L b2 b *
        pinnedX Tag.E6 D.L a2 a) := by rw [hba, ← hb, mul_assoc]
    _ = pinnedX Tag.E6 D.L (highRoot Tag.E6) c * pinnedX Tag.E6 D.L a2 a *
          pinnedX Tag.E6 D.L b2 b := by
        rw [hswap, ← mul_assoc, ← mul_assoc, ← pinnedX_add, hc, mul_assoc]

theorem exists_sigFix_pair (hK : 3 ≤ Nat.card K) {γ : V6} (hγ : IsRoot Tag.E6 γ)
    (hcomm : ∀ a b : D.L, pinnedX Tag.E6 D.L γ a * pinnedX Tag.E6 D.L (wE • γ) b =
      pinnedX Tag.E6 D.L (wE • γ) b * pinnedX Tag.E6 D.L γ a) :
    ∃ (e : D.L) (A : Finset D.L), e ≠ 0 ∧ Nat.card K ^ 2 ≤ A.card ∧ ∀ s ∈ A,
      SigFix D (pinnedX Tag.E6 D.L γ s * pinnedX Tag.E6 D.L (wE • γ) (e * s ^ Nat.card K)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ε₁, hε₁, h₁c⟩ := sigma_pinnedX D hγ
  obtain ⟨ε₂, hε₂, h₂c⟩ := sigma_pinnedX D (IsRoot.smul hγ wE)
  have hε₁0 : ε₁ ≠ 0 := fun h => by rw [h] at hε₁; simp at hε₁
  have hε₂0 : ε₂ ≠ 0 := fun h => by rw [h] at hε₂; simp at hε₂
  set q := Nat.card K with hq
  have hq0 : (q : D.L) = 0 := natCast_card_eq_zero K D.L
  obtain ⟨A, hA, hAe⟩ := exists_finset_pow_eq (E := D.L) (q ^ 2) (by nlinarith)
    (by rw [Nat.cast_pow, hq0]; simp) (ε₂ * ε₁ ^ q) (mul_ne_zero hε₂0 (pow_ne_zero _ hε₁0))
  refine ⟨ε₁, A, hε₁0, hA, fun s hs => ?_⟩
  unfold SigFix
  have hba : ε₂ * (ε₁ * s ^ q) ^ q = s := by
    have h := hAe s hs
    rw [mul_pow, ← pow_mul, ← sq, ← mul_assoc]
    exact h
  rw [map_mul]
  calc canonicalRep (coxeterSystem Tag.E6) D.L wE * (Units.map (entrywiseHom D.Fr)
        (pinnedX Tag.E6 D.L γ s) * Units.map (entrywiseHom D.Fr)
          (pinnedX Tag.E6 D.L (wE • γ) (ε₁ * s ^ q))) *
        (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹
      = (canonicalRep (coxeterSystem Tag.E6) D.L wE * Units.map (entrywiseHom D.Fr)
          (pinnedX Tag.E6 D.L γ s) * (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) D.L wE * Units.map (entrywiseHom D.Fr)
          (pinnedX Tag.E6 D.L (wE • γ) (ε₁ * s ^ q)) *
          (canonicalRep (coxeterSystem Tag.E6) D.L wE)⁻¹) := by group
    _ = pinnedX Tag.E6 D.L (wE • γ) (ε₁ * s ^ q) * pinnedX Tag.E6 D.L γ s := by
        rw [h₁c, h₂c, wE_invol, hba]
    _ = pinnedX Tag.E6 D.L γ s * pinnedX Tag.E6 D.L (wE • γ) (ε₁ * s ^ q) := (hcomm _ _).symm

end E6

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
