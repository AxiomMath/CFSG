module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelSetting

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

noncomputable abbrev planeImage (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V))
    (π : Submodule K' N) : Subgroup (V ≃ₗ[K] V) :=
  ((sigmaGroup QN π).subgroupOf (elementaryGroup QN)).map ρ

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_triple_coeff {a b c : N} (h : LinearIndependent K' ![a, b, c]) {s t u : K'}
    (h0 : s • a + t • b + u • c = 0) : s = 0 ∧ t = 0 ∧ u = 0 := by
  have := Fintype.linearIndependent_iff.mp h ![s, t, u] (by
    simpa [Fin.sum_univ_three] using h0)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_pair_01 {a b c : N} (h : LinearIndependent K' ![a, b, c]) :
    LinearIndependent K' ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := cpl_triple_coeff h (s := s) (t := t) (u := 0) (by simpa using hst)
  exact ⟨this.1, this.2.1⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_pair_02 {a b c : N} (h : LinearIndependent K' ![a, b, c]) :
    LinearIndependent K' ![a, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := cpl_triple_coeff h (s := s) (t := 0) (u := t) (by simpa using hst)
  exact ⟨this.1, this.2.2⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_pair_12 {a b c : N} (h : LinearIndependent K' ![a, b, c]) :
    LinearIndependent K' ![b, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := cpl_triple_coeff h (s := 0) (t := s) (u := t) (by simpa using hst)
  exact ⟨this.2.1, this.2.2⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_pair_smul {u v : N} (h : LinearIndependent K' ![u, v]) {μ : K'}
    (hμ : μ ≠ 0) : LinearIndependent K' ![u, μ • v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have h' := h s (t * μ) (by rw [mul_smul]; exact hst)
  exact ⟨h'.1, (mul_eq_zero.mp h'.2).resolve_right hμ⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem cpl_ne_one (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) : s ≠ 1 :=
  fun h => not_isLongRootElement_one hnd (h ▸ hs)

private theorem cpl_natCard_ne_zero {α : Type*} [Zero α] [Finite α] :
    Nat.card {x : α // x ≠ 0} + 1 = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have : 0 < Fintype.card α := Fintype.card_pos
  omega

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [FiniteDimensional K V] [Finite K] in
private theorem OmegaSetting.cpl_sub_mem_of_rhoE_eq (hs : OmegaSetting QN Qf ρ)
    {a u w b : N} (ha : QN a = 0) (hu : QN u = 0) (hw : QN w = 0) (hau : polar QN a u = 0)
    (haw : polar QN a w = 0) (hli : LinearIndependent K' ![a, b]) (h : rhoE ρ a u = rhoE ρ a w) :
    ∃ κ : K', u - w = κ • a := by
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have h' : eichler QN a u = eichler QN a w := congrArg Subtype.val (hs.inj h)
  obtain ⟨x, hx1, -⟩ := exists_polar_pair hndN hli 1 0
  have h1 := DFunLike.congr_fun h' x
  rw [eichler_apply_of_singular ha hu hau, eichler_apply_of_singular ha hw haw, hx1,
    one_smul, one_smul] at h1
  exact ⟨polar QN x w - polar QN x u, by rw [sub_smul]; linear_combination (norm := module) h1⟩

omit [FiniteDimensional K V] in
private theorem cpl_card_le_of_movedSpace_eq (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {A : Submodule K V} (hA2 : finrank K A = 2) (hsing : ∀ w ∈ A, Qf w = 0) {ι : Type*}
    [Finite ι] (s : ι → V ≃ₗ[K] V) (hsiso : ∀ i v, Qf (s i v) = Qf v)
    (hsA : ∀ i, movedSpace (s i) = A) (hsinj : Function.Injective s) :
    Nat.card ι + 1 ≤ Nat.card K := by
  obtain ⟨a₁, a₂, -, -, hli, hspan⟩ := exists_basis_of_finrank_eq_two hA2
  have hex : ∀ i, ∃ c : K, c ≠ 0 ∧
      ∀ v, s i v = v + c • (polar Qf v a₁ • a₂ + polar Qf v a₂ • a₁) :=
    fun i => exists_siegel_scalar hnd (hsiso i) hli (by rw [hsA i]; exact hspan)
      (fun w hw => hsing w (by rwa [hsA i] at hw))
  choose c hc0 hc using hex
  have hinj : Function.Injective fun i => (⟨c i, hc0 i⟩ : {x : K // x ≠ 0}) := by
    intro i j hij
    have hcij : c i = c j := congrArg Subtype.val hij
    apply hsinj
    ext v
    rw [hc i v, hc j v, hcij]
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 := cpl_natCard_ne_zero (α := K)
  omega

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_pair_of_polar {u v z : N} (hu : u ≠ 0) (huz : polar QN u z = 0)
    (hvz : polar QN v z ≠ 0) : LinearIndependent K' ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : t * polar QN v z = 0 := by
    have h := congrArg (fun x => polar QN x z) hst
    simpa [polar_add_left, polar_smul_left_eq, huz] using h
  have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right hvz
  subst ht
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_triple_of_polar {a d u z : N} (hli : LinearIndependent K' ![a, d])
    (haz : polar QN a z = 0) (hdz : polar QN d z = 0) (huz : polar QN u z ≠ 0) :
    LinearIndependent K' ![a, d, u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h2 : g 2 * polar QN u z = 0 := by
    have h := congrArg (fun x => polar QN x z) hg
    simpa [polar_add_left, polar_smul_left_eq, haz, hdz] using h
  have hg2 : g 2 = 0 := (mul_eq_zero.mp h2).resolve_right huz
  rw [hg2, zero_smul, add_zero] at hg
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hli (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hg2

omit [Finite K'] [FiniteDimensional K' N] in
private theorem cpl_qf_zero_span_triple {a d u : N} (ha : QN a = 0) (hd : QN d = 0)
    (hu : QN u = 0) (had : polar QN a d = 0) (hau : polar QN a u = 0) (hdu : polar QN d u = 0) :
    ∀ w ∈ Submodule.span K' ({a, d, u} : Set N), QN w = 0 := by
  have hda : polar QN d a = 0 := by rw [polar_comm]; exact had
  have hua : polar QN u a = 0 := by rw [polar_comm]; exact hau
  have hud : polar QN u d = 0 := by rw [polar_comm]; exact hdu
  intro w hw
  refine map_eq_zero_of_mem_span (S := {a, d, u}) ?_ ?_ hw
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | assumption | exact SiegelRT1.polar_self_eq_zero _

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem cpl_finrank_span_triple {a d u : N} (h : LinearIndependent K' ![a, d, u]) :
    finrank K' (Submodule.span K' ({a, d, u} : Set N)) = 3 := by
  have h3 := finrank_span_eq_card h
  rw [show Set.range ![a, d, u] = ({a, d, u} : Set N) by
    ext x; simp [eq_comm]; tauto] at h3
  simpa using h3

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem cpl_rhoE_mem (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {u w : N}
    (hu : QN u = 0) (hw : QN w = 0) (huw : polar QN u w = 0) (hli : LinearIndependent K' ![u, w])
    {π : Submodule K' N} (hu' : u ∈ π) (hw' : w ∈ π) : rhoE ρ u w ∈ planeImage ρ π := by
  have hu0 : u ≠ 0 := by simpa using hli.ne_zero 0
  have hwu : w ∉ Submodule.span K' ({u} : Set N) := fun hmem => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact (LinearIndependent.pair_iff' hu0).mp hli c hc
  obtain ⟨h1, h2⟩ := isLongRootElement_eichler hnd hu hw huw hu0 hwu
  refine Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr
    (isLongRootElement_mem_sigmaGroup h1 ?_))
  rw [h2, Submodule.span_le]
  exact Set.insert_subset_iff.mpr ⟨hu', Set.singleton_subset_iff.mpr hw'⟩

omit [Finite K'] [Finite K] in
private theorem OmegaSetting.cpl_axisInf_inf_eq_bot (hs : OmegaSetting QN Qf ρ) {a d u w : N}
    (ha : QN a = 0) (hd : QN d = 0) (hu : QN u = 0) (hw : QN w = 0) (had : polar QN a d = 0)
    (hau : polar QN a u = 0) (haw : polar QN a w = 0) (hdu : polar QN d u = 0)
    (hdw : polar QN d w = 0) (huw : polar QN u w ≠ 0) (hli : LinearIndependent K' ![a, d]) :
    axisInf (planeImage ρ (Submodule.span K' {a, d, u})) ⊓
      axisInf (planeImage ρ (Submodule.span K' {a, d, w})) = ⊥ := by
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have ha0 : a ≠ 0 := by simpa using hli.ne_zero 0
  have hd0 : d ≠ 0 := by simpa using hli.ne_zero 1
  have hw' : QN ((polar QN u w)⁻¹ • w) = 0 := by rw [map_smul_eq_sq, hw, mul_zero]
  have hw'a : polar QN a ((polar QN u w)⁻¹ • w) = 0 := by rw [polar_smul_right_eq, haw, mul_zero]
  have hw'd : polar QN ((polar QN u w)⁻¹ • w) d = 0 := by
    rw [polar_smul_left_eq, polar_comm QN w d, hdw, mul_zero]
  have hud : polar QN u d = 0 := by rw [polar_comm]; exact hdu
  have hbc : polar QN u ((polar QN u w)⁻¹ • w) ≠ 0 := by
    rw [polar_smul_right_eq]; exact mul_ne_zero (inv_ne_zero huw) huw
  have hlab : LinearIndependent K' ![a, u] := cpl_pair_of_polar ha0 haw huw
  have hlcd : LinearIndependent K' ![(polar QN u w)⁻¹ • w, d] :=
    LinearIndependent.pair_symm_iff.mpr (cpl_pair_of_polar hd0 hdu (by
      rw [polar_smul_left_eq, polar_comm QN w u]; exact mul_ne_zero (inv_ne_zero huw) huw))
  have hbot := hs.movedSpace_rhoE_inf_eq_bot ha hu hw' hd hau hw'd hw'a had hud hbc hlab hlcd hli
  have h1 : axisInf (planeImage ρ (Submodule.span K' {a, d, u})) ≤ movedSpace (rhoE ρ a u) :=
    axisInf_le ⟨rhoE ρ a u, cpl_rhoE_mem hndN ha hu hau hlab (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)),
      cpl_ne_one hs.nd (hs.isLongRootElement_rhoE ha hu hau hlab), rfl⟩
  have h2 : axisInf (planeImage ρ (Submodule.span K' {a, d, w})) ≤
      movedSpace (rhoE ρ ((polar QN u w)⁻¹ • w) d) :=
    axisInf_le ⟨rhoE ρ ((polar QN u w)⁻¹ • w) d, cpl_rhoE_mem hndN hw' hd hw'd hlcd
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) (Submodule.subset_span (by simp)),
      cpl_ne_one hs.nd (hs.isLongRootElement_rhoE hw' hd hw'd hlcd), rfl⟩
  exact eq_bot_iff.mpr (hbot ▸ inf_le_inf h1 h2)

omit [FiniteDimensional K V] in
theorem OmegaSetting.not_forall_movedSpace_rhoE_eq (hs : OmegaSetting QN Qf ρ) {a b b' : N}
    (ha : QN a = 0) (hb : QN b = 0) (hb' : QN b' = 0) (hab : polar QN a b = 0)
    (hab' : polar QN a b' = 0) (hli : LinearIndependent K' ![a, b, b']) (A : Submodule K V) :
    ¬ ∀ μ : K', μ ≠ 0 → movedSpace (rhoE ρ a (μ • b)) = A ∧ movedSpace (rhoE ρ a (μ • b')) = A := by
  intro hA
  let x : {μ : K' // μ ≠ 0} ⊕ {μ : K' // μ ≠ 0} → N :=
    Sum.elim (fun μ => μ.1 • b) (fun μ => μ.1 • b')
  have hxQ : ∀ i, QN (x i) = 0 := by
    rintro (μ | μ)
    · simp only [x, Sum.elim_inl, map_smul_eq_sq, hb, mul_zero]
    · simp only [x, Sum.elim_inr, map_smul_eq_sq, hb', mul_zero]
  have hxB : ∀ i, polar QN a (x i) = 0 := by
    rintro (μ | μ)
    · simp only [x, Sum.elim_inl, polar_smul_right_eq, hab, mul_zero]
    · simp only [x, Sum.elim_inr, polar_smul_right_eq, hab', mul_zero]
  have hxli : ∀ i, LinearIndependent K' ![a, x i] := by
    rintro (μ | μ)
    · exact cpl_pair_smul (cpl_pair_01 hli) μ.2
    · exact cpl_pair_smul (cpl_pair_02 hli) μ.2
  have hxS : ∀ i, IsLongRootElement Qf (rhoE ρ a (x i)) := fun i =>
    hs.isLongRootElement_rhoE ha (hxQ i) (hxB i) (hxli i)
  have hxA : ∀ i, movedSpace (rhoE ρ a (x i)) = A := by
    rintro (μ | μ)
    · exact (hA μ.1 μ.2).1
    · exact (hA μ.1 μ.2).2
  let i₀ : {μ : K' // μ ≠ 0} ⊕ {μ : K' // μ ≠ 0} := Sum.inl ⟨1, one_ne_zero⟩
  have hA2 : finrank K A = 2 := by
    rw [← hxA i₀]
    exact (hxS i₀).finrank_movedSpace hs.nd
  have hsing : ∀ w ∈ A, Qf w = 0 := fun w hw =>
    (hxS i₀).qf_eq_zero_of_mem_movedSpace (by rwa [hxA i₀])
  have hinj : Function.Injective fun i => rhoE ρ a (x i) := by
    intro i j hij
    obtain ⟨κ, hκ⟩ := hs.cpl_sub_mem_of_rhoE_eq ha (hxQ i) (hxQ j) (hxB i) (hxB j)
      (cpl_pair_01 hli) hij
    rcases i with ⟨μ, hμ⟩ | ⟨μ, hμ⟩ <;> rcases j with ⟨ν, hν⟩ | ⟨ν, hν⟩ <;>
      simp only [x, Sum.elim_inl, Sum.elim_inr] at hκ
    · have := cpl_triple_coeff hli (s := -κ) (t := μ - ν) (u := 0)
        (by linear_combination (norm := module) hκ)
      exact congrArg Sum.inl (Subtype.ext (sub_eq_zero.mp this.2.1))
    · have := cpl_triple_coeff hli (s := -κ) (t := μ) (u := -ν)
        (by linear_combination (norm := module) hκ)
      exact absurd this.2.1 hμ
    · have := cpl_triple_coeff hli (s := -κ) (t := -ν) (u := μ)
        (by linear_combination (norm := module) hκ)
      exact absurd (neg_eq_zero.mp this.2.1) hν
    · have := cpl_triple_coeff hli (s := -κ) (t := 0) (u := μ - ν)
        (by linear_combination (norm := module) hκ)
      exact congrArg Sum.inr (Subtype.ext (sub_eq_zero.mp this.2.2))
  have hcard := cpl_card_le_of_movedSpace_eq hs.nd hA2 hsing (fun i => rhoE ρ a (x i))
    (fun i v => (hxS i).isometry v) hxA hinj
  rw [Nat.card_sum] at hcard
  have h1 := cpl_natCard_ne_zero (α := K')
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  rw [hs.card] at h1
  omega

theorem OmegaSetting.movedSpace_rhoE_ne (hs : OmegaSetting QN Qf ρ) {a b b' : N}
    (ha : QN a = 0) (hb : QN b = 0) (hb' : QN b' = 0) (hab : polar QN a b = 0)
    (hab' : polar QN a b' = 0) (hli : LinearIndependent K' ![a, b, b'])
    (hax : ∀ μ : K', movedSpace (rhoE ρ a (μ • b)) ≤ movedSpace (rhoE ρ a b))
    (hax' : ∀ μ : K', movedSpace (rhoE ρ a (μ • b')) ≤ movedSpace (rhoE ρ a b')) :
    movedSpace (rhoE ρ a b) ≠ movedSpace (rhoE ρ a b') := by
  intro heq
  have hfin : ∀ {u : N}, QN u = 0 → polar QN a u = 0 → LinearIndependent K' ![a, u] →
      finrank K (movedSpace (rhoE ρ a u)) = 2 := fun hu hau hl =>
    (hs.isLongRootElement_rhoE ha hu hau hl).finrank_movedSpace hs.nd
  have hb2 := hfin hb hab (cpl_pair_01 hli)
  have hb2' := hfin hb' hab' (cpl_pair_02 hli)
  refine hs.not_forall_movedSpace_rhoE_eq ha hb hb' hab hab' hli (movedSpace (rhoE ρ a b))
    fun μ hμ => ⟨?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq (hax μ) ?_
    rw [hb2, hfin (by rw [map_smul_eq_sq, hb, mul_zero])
      (by rw [polar_smul_right_eq, hab, mul_zero]) (cpl_pair_smul (cpl_pair_01 hli) hμ)]
  · refine Submodule.eq_of_le_of_finrank_eq ((hax' μ).trans heq.symm.le) ?_
    rw [hb2, hfin (by rw [map_smul_eq_sq, hb', mul_zero])
      (by rw [polar_smul_right_eq, hab', mul_zero]) (cpl_pair_smul (cpl_pair_02 hli) hμ)]

theorem OmegaSetting.movedSpace_rhoE_le_sup_of_copl (hs : OmegaSetting QN Qf ρ) {a b c : N}
    (ha : QN a = 0) (hb : QN b = 0) (hc : QN c = 0) (hab : polar QN a b = 0)
    (hac : polar QN a c = 0) (hbc : polar QN b c = 0) (hli : LinearIndependent K' ![a, b, c])
    (hcopl : Copl (planeImage ρ (Submodule.span K' {a, b, c})))
    (hne : movedSpace (rhoE ρ a b) ≠ movedSpace (rhoE ρ a c)) :
    movedSpace (rhoE ρ b c) ≤ movedSpace (rhoE ρ a b) ⊔ movedSpace (rhoE ρ a c) := by
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have hE := hs.isSiegelFamily_map (π := Submodule.span K' ({a, b, c} : Set N))
    (cpl_qf_zero_span_triple ha hb hc hab hac hbc) (cpl_finrank_span_triple hli)
  have ha₁ : a ∈ Submodule.span K' ({a, b, c} : Set N) := Submodule.subset_span (by simp)
  have hb₁ : b ∈ Submodule.span K' ({a, b, c} : Set N) := Submodule.subset_span (by simp)
  have hc₁ : c ∈ Submodule.span K' ({a, b, c} : Set N) := Submodule.subset_span (by simp)
  have hl_ab := cpl_pair_01 hli
  have hl_ac := cpl_pair_02 hli
  have hl_bc := cpl_pair_12 hli
  have hm_ab := cpl_rhoE_mem (ρ := ρ) hndN ha hb hab hl_ab ha₁ hb₁
  have hm_ac := cpl_rhoE_mem (ρ := ρ) hndN ha hc hac hl_ac ha₁ hc₁
  have hm_bc := cpl_rhoE_mem (ρ := ρ) hndN hb hc hbc hl_bc hb₁ hc₁
  have hA₁ : movedSpace (rhoE ρ a b) ∈ axes (planeImage ρ (Submodule.span K' {a, b, c})) :=
    ⟨_, hm_ab, cpl_ne_one hs.nd (hs.isLongRootElement_rhoE ha hb hab hl_ab), rfl⟩
  have hA₂ : movedSpace (rhoE ρ a c) ∈ axes (planeImage ρ (Submodule.span K' {a, b, c})) :=
    ⟨_, hm_ac, cpl_ne_one hs.nd (hs.isLongRootElement_rhoE ha hc hac hl_ac), rfl⟩
  have h3 := (hE.pair hs.nd hA₁ hA₂ hne).2.2.1
  have hU3 := hE.finrank_commutatorSpace_of_copl hs.nd hcopl
  have heq : movedSpace (rhoE ρ a b) ⊔ movedSpace (rhoE ρ a c) =
      commutatorSpace (planeImage ρ (Submodule.span K' {a, b, c})) :=
    Submodule.eq_of_le_of_finrank_eq (sup_le (le_commutatorSpace_of_mem_axes hA₁)
      (le_commutatorSpace_of_mem_axes hA₂)) (by rw [h3, hU3])
  rw [heq]
  exact movedSpace_le_commutatorSpace hm_bc

omit [CharP K 2] [FiniteDimensional K V] in
theorem card_le_of_finrank_eq_one {A : Submodule K V} (hA : finrank K A = 2) {ι : Type*}
    [Finite ι] (P : ι → Submodule K V) (hP1 : ∀ i, finrank K (P i) = 1) (hPA : ∀ i, P i ≤ A)
    (hinj : Function.Injective P) : Nat.card ι ≤ Nat.card K + 1 := by
  classical
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfA : Module.Finite K A := Module.finite_of_finrank_pos (by omega)
  have hfP : ∀ i, Module.Finite K (P i) := fun i =>
    Module.finite_of_finrank_pos (by rw [hP1 i]; omega)
  have : Finite A := Module.finite_of_finite K
  have : ∀ i, Finite (P i) := fun i => haveI := hfP i; Module.finite_of_finite K
  have hA' : Nat.card A = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := A), hA]
  have hP' : ∀ i, Nat.card (P i) = Nat.card K := fun i => by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := P i), hP1 i, pow_one]
  have hne : ∀ p : (Σ i, {x : P i // x ≠ 0}), ((p.2.1 : P p.1) : V) ≠ 0 := fun p h0 =>
    p.2.2 (Subtype.ext h0)
  let f : (Σ i, {x : P i // x ≠ 0}) → {x : A // x ≠ 0} := fun p =>
    ⟨⟨p.2.1.1, hPA p.1 p.2.1.2⟩, fun h => hne p (congrArg Subtype.val h)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
    have hxy : (x : V) = y := congrArg (fun p : {x : A // x ≠ 0} => ((p.1 : A) : V)) h
    have hx0 : (x : V) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    have hspan : ∀ k (z : P k), (z : V) ≠ 0 → P k = Submodule.span K {(z : V)} := fun k z hz =>
      (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr z.2)
        (by rw [finrank_span_singleton hz, hP1 k])).symm
    have hij : i = j := hinj (by rw [hspan i x hx0, hspan j y (hxy ▸ hx0), hxy])
    subst hij
    have hxy' : x = y := Subtype.ext hxy
    subst hxy'
    rfl
  have h1 := Nat.card_le_card_of_injective f hf
  have := Fintype.ofFinite ι
  rw [Nat.card_sigma] at h1
  have hm : ∀ i, Nat.card {x : P i // x ≠ 0} = Nat.card K - 1 := fun i => by
    have := cpl_natCard_ne_zero (α := P i)
    rw [hP' i] at this
    omega
  have hcardA := cpl_natCard_ne_zero (α := A)
  rw [hA'] at hcardA
  simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card (α := ι)]
  obtain ⟨m, hm'⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [hm'] at h1 hcardA ⊢
  simp only [Nat.add_sub_cancel] at h1
  by_contra hlt
  have hlt' : m + 3 ≤ Fintype.card ι := by omega
  have hm1 : 1 ≤ m := by omega
  have := Nat.mul_le_mul_right m hlt'
  nlinarith

theorem OmegaSetting.exists_copl (hs : OmegaSetting QN Qf ρ) {a d : N} (ha : QN a = 0)
    (hd : QN d = 0) (had : polar QN a d = 0) (hli : LinearIndependent K' ![a, d]) {ι : Type*}
    [Finite ι] (z : ι → N) (hz : ∀ i, QN (z i) = 0) (hza : ∀ i, polar QN a (z i) = 0)
    (hzd : ∀ i, polar QN d (z i) = 0) (hzz : ∀ i j, i ≠ j → polar QN (z i) (z j) ≠ 0)
    (hcard : Nat.card K + 1 < Nat.card ι) :
    ∃ i, Copl (planeImage ρ (Submodule.span K' {a, d, z i})) := by
  by_contra hno
  have hno' := not_exists.mp hno
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have : Nontrivial ι := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hli3 : ∀ i, LinearIndependent K' ![a, d, z i] := fun i => by
    obtain ⟨j, hj⟩ := exists_ne i
    exact cpl_triple_of_polar hli (hza j) (hzd j) (hzz i j hj.symm)
  have hE : ∀ i, IsSiegelFamily Qf (planeImage ρ (Submodule.span K' {a, d, z i})) := fun i =>
    hs.isSiegelFamily_map (π := Submodule.span K' ({a, d, z i} : Set N))
      (cpl_qf_zero_span_triple ha hd (hz i) had (hza i) (hzd i)) (cpl_finrank_span_triple (hli3 i))
  let P : ι → Submodule K V := fun i => axisInf (planeImage ρ (Submodule.span K' {a, d, z i}))
  have hP1 : ∀ i, finrank K (P i) = 1 := fun i =>
    (hE i).finrank_axisInf_of_conc hs.nd (((hE i).conc_or_copl hs.nd).resolve_right (hno' i))
  have hS : IsLongRootElement Qf (rhoE ρ a d) := hs.isLongRootElement_rhoE ha hd had hli
  have hPA : ∀ i, P i ≤ movedSpace (rhoE ρ a d) := fun i =>
    axisInf_le ⟨rhoE ρ a d, cpl_rhoE_mem hndN ha hd had hli (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)), cpl_ne_one hs.nd hS, rfl⟩
  have hinj : Function.Injective P := by
    intro i j hP
    by_contra hij
    have h : P i ⊓ P j = ⊥ := hs.cpl_axisInf_inf_eq_bot ha hd (hz i) (hz j) had (hza i) (hza j)
      (hzd i) (hzd j) (hzz i j hij) hli
    rw [← hP, inf_idem] at h
    have := hP1 i
    rw [h, finrank_bot] at this
    omega
  have := card_le_of_finrank_eq_one (hS.finrank_movedSpace hs.nd) P hP1 (fun i => hPA i) hinj
  omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
