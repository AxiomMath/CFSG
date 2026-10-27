
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase
public import CFSG.Monster.B.TwoA.Census.CosetEnumGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.Sp8Xi

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Census CFSG.Monster.ScalarKernel Matrix

theorem conjQ_eq_of_gen {P R : Pvis} (hconj : ∀ k < 24, conjQ P (gQ k) = conjQ R (gQ k)) (r : Q) :
    conjQ P r = conjQ R r := by
  have hr : r ∈ Subgroup.closure (gQ '' {k | k < 24}) := by
    rw [closure_gQ]
    exact Subgroup.mem_top r
  induction hr using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    exact hconj k hk
  | one => exact (map_one (conjQ P)).trans (map_one (conjQ R)).symm
  | mul a b _ _ ha hb =>
    exact (map_mul (conjQ P) a b).trans
      ((congrArg₂ (· * ·) ha hb).trans (map_mul (conjQ R) a b).symm)
  | inv a _ ha =>
    exact (map_inv (conjQ P) a).trans ((congrArg (·⁻¹) ha).trans (map_inv (conjQ R) a).symm)

theorem pvis_eq_of_conj {P R : Pvis}
    (hlat : (P : GL SpinIdx ℚ × latticeO).2 = (R : GL SpinIdx ℚ × latticeO).2)
    (hconj : ∀ k < 24, conjQ P (gQ k) = conjQ R (gQ k)) (η : Bool) (c : ℕ)
    (hkey : theta P (keyVec (Model.Key.W η c)) = theta R (keyVec (Model.Key.W η c))) :
    P = R := by
  have hcomm : ∀ g ∈ Q, (g : Matrix SpinIdx SpinIdx ℚ) *
      (((P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹ : GL SpinIdx ℚ) :
        Matrix SpinIdx SpinIdx ℚ) =
      (((P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹ : GL SpinIdx ℚ) :
        Matrix SpinIdx SpinIdx ℚ) * g := by
    intro g hg
    have h1 : (P : GL SpinIdx ℚ × latticeO).1⁻¹ * g * (P : GL SpinIdx ℚ × latticeO).1 =
        (R : GL SpinIdx ℚ × latticeO).1⁻¹ * g * (R : GL SpinIdx ℚ × latticeO).1 :=
      congrArg Subtype.val (conjQ_eq_of_gen hconj ⟨g, hg⟩)
    have h2 : g * ((P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹) =
        (P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹ * g :=
      calc g * ((P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹)
          = (P : GL SpinIdx ℚ × latticeO).1 * ((P : GL SpinIdx ℚ × latticeO).1⁻¹ * g *
              (P : GL SpinIdx ℚ × latticeO).1) * (R : GL SpinIdx ℚ × latticeO).1⁻¹ := by group
        _ = (P : GL SpinIdx ℚ × latticeO).1 * ((R : GL SpinIdx ℚ × latticeO).1⁻¹ * g *
              (R : GL SpinIdx ℚ × latticeO).1) * (R : GL SpinIdx ℚ × latticeO).1⁻¹ := by rw [h1]
        _ = (P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹ * g := by group
    exact (Units.val_mul g _).symm.trans ((congrArg Units.val h2).trans (Units.val_mul _ g))
  obtain ⟨s, hs⟩ := exists_scalar_of_commute_Q hcomm
  have hMN : (((P : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      s • (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := by
    have e : (((P : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
        (((P : GL SpinIdx ℚ × latticeO).1 * (R : GL SpinIdx ℚ × latticeO).1⁻¹ : GL SpinIdx ℚ) :
          Matrix SpinIdx SpinIdx ℚ) *
        (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [e, hs, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hrow := spin_rows_of_theta hlat η c hkey
  rw [hMN, Matrix.vecMul_smul] at hrow
  have hs1 : s = 1 := by
    by_contra hne
    have h0 : Evec η c ᵥ* (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) :
        Matrix SpinIdx SpinIdx ℚ) = 0 := by
      have h3 : (s - 1) • (Evec η c ᵥ* (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) :
          Matrix SpinIdx SpinIdx ℚ)) = 0 := by
        rw [sub_smul, one_smul, hrow, sub_self]
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
    have hE : Evec η c ᵥ* (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) :
        Matrix SpinIdx SpinIdx ℚ) ᵥ* ((((R : GL SpinIdx ℚ × latticeO).1⁻¹ : GL SpinIdx ℚ)) :
          Matrix SpinIdx SpinIdx ℚ) = Evec η c := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [h0, zero_vecMul] at hE
    have h1 := congrFun hE (boolZ η, π₀ (toC c))
    simp [Evec, E] at h1
  rw [hs1, one_smul] at hMN
  exact pvis_eq hMN hlat

theorem conjQ_xiSignPair (y : Model.Pauli) :
    conjQ xiSignPair (pauliQ y) = pauliQ (Model.conjYN 1 (Model.conjXiN y)) := by
  rw [xiSignPair, conjQ_mul, conjQ_xi_toQ]
  exact conjQ_sign_toQ 1 _

theorem conjQ_lhs (y : Model.Pauli) : conjQ (slPair * xiSignPair) (pauliQ y) =
    pauliQ (Model.conjYN 1 (Model.conjXiN (Model.conjYN 3 y))) := by
  rw [conjQ_mul, conjQ_slPair_pauliQ, conjQ_xiSignPair]

theorem conjQ_rhs (q y : Model.Pauli) :
    conjQ (xiSignPair * rhoPair (pauliQ q) * slPair) (pauliQ y) =
      pauliQ (Model.conjYN 3 (Model.conjPauliN q (Model.conjYN 1 (Model.conjXiN y)))) := by
  rw [conjQ_mul, conjQ_mul, conjQ_xiSignPair, conjQ_rhoPair_toQ, conjQ_slPair_pauliQ]

theorem theta_lhs_key {η : Bool} {c : ℕ}
    (hl : (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)]).all
      (fun e => e.1.1 != 0) = true) :
    theta (slPair * xiSignPair) (keyVec (Model.Key.W η c)) =
      interp (1 * 64 * 64) (Model.actVec Model.keyActXi
        (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)])) := by
  rw [List.all_eq_true] at hl
  have hv : ∀ e ∈ [(Model.Key.W η c, (1 : ℤ))], KeyValid e.1 := fun e he => by
    rw [List.mem_singleton] at he
    subst he
    exact fun h0 => absurd (show (2 : ℕ) = 0 from h0) (by decide)
  exact (theta_mul_apply _ _ _).trans ((congrArg (theta xiSignPair)
    ((congrArg (theta slPair) (keyVec_eq_interp _)).trans
      (interp_actVec _ (theta slPair) 1 _ fun e he => theta_slPair_key _ (hv e he)))).trans
    (interp_actVec _ (theta xiSignPair) _ _ fun e he =>
      theta_xi_key _ (keyValid_of_ne (hl e he))))

theorem theta_rhs_key (q : Model.Pauli) {η : Bool} {c : ℕ}
    (hr : (Model.actVec (Model.keyActPauli q)
      (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)])).all (fun e => e.1.1 != 0) = true) :
    theta (xiSignPair * rhoPair (pauliQ q) * slPair) (keyVec (Model.Key.W η c)) =
      interp (1 * 64 * 64 * 64) (Model.actVec (Model.keyActSign 3)
        (Model.actVec (Model.keyActPauli q)
          (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)]))) := by
  rw [List.all_eq_true] at hr
  have hv : ∀ e ∈ [(Model.Key.W η c, (1 : ℤ))], KeyValid e.1 := fun e he => by
    rw [List.mem_singleton] at he
    subst he
    exact fun h0 => absurd (show (2 : ℕ) = 0 from h0) (by decide)
  exact (theta_mul_apply _ _ _).trans ((congrArg (theta slPair)
    ((theta_mul_apply _ _ _).trans ((congrArg (theta (rhoPair (pauliQ q)))
      ((congrArg (theta xiSignPair) (keyVec_eq_interp _)).trans
        (interp_actVec _ (theta xiSignPair) 1 _ fun e he => theta_xi_key _ (hv e he)))).trans
      (interp_actVec _ (theta (rhoPair (pauliQ q))) _ _ fun e _ =>
        theta_rhoPair_key _ _)))).trans
    (interp_actVec _ (theta slPair) _ _ fun e he =>
      theta_slPair_key _ (keyValid_of_ne (hr e he))))

@[expose] def WK (κ : Model.Key) : Prop := κ.1 = 2 ∧ κ.2.2 < 4096

@[expose] def NW (κ : Model.Key) : Prop :=
  κ.1 = 2 ∧ κ.2.1 < 2 ∧ κ.2.2 < 4096 ∧ Model.pi0N κ.2.2 = κ.2.2

theorem NW.wk {κ : Model.Key} (h : NW κ) : WK κ := ⟨h.1, h.2.2.1⟩

theorem nw_W (η : Bool) {c : ℕ} (hc : c < 4096) (hn : Model.pi0N c = c) : NW (Model.Key.W η c) :=
  ⟨rfl, by cases η <;> simp [Model.Key.W], hc, hn⟩

theorem shiftN_lt {a c : ℕ} (ha : a < 4096) (hc : c < 4096) : Model.shiftN a c < 4096 := by
  unfold Model.shiftN
  exact Rep4371Row.pi0_lt (Nat.xor_lt_two_pow (n := 12) hc ha)

theorem shiftN_norm (a c : ℕ) : Model.pi0N (Model.shiftN a c) = Model.shiftN a c := by
  unfold Model.shiftN
  exact Rep4371Row.pi0_pi0 _

theorem eYN_nw (a : ℕ) (ha : a < 4096) (η : Bool) {c : ℕ} (hc : c < 4096) :
    NW (Model.Key.W (Model.eYN a η c).2.1 (Model.eYN a η c).2.2) := by
  cases η
  · exact nw_W _ (shiftN_lt ha (Rep4371Row.pi0_lt hc)) (shiftN_norm _ _)
  · exact nw_W _ (Rep4371Row.pi0_lt hc) (Rep4371Row.pi0_pi0 c)

theorem ePauliN_nw (q : Model.Pauli) (hq : q.a < 4096) (η : Bool) {c : ℕ} (hc : c < 4096) :
    NW (Model.Key.W (Model.ePauliN q η c).2.1 (Model.ePauliN q η c).2.2) :=
  nw_W _ (shiftN_lt hq (Rep4371Row.pi0_lt hc)) (shiftN_norm _ _)

theorem mem_actVec {act : Model.Key → List (Model.Key × ℤ)} {v : List (Model.Key × ℤ)}
    {P R : Model.Key → Prop} (hv : ∀ e ∈ v, P e.1) (hact : ∀ κ, P κ → ∀ f ∈ act κ, R f.1) :
    ∀ e ∈ Model.actVec act v, R e.1 := by
  intro e he
  unfold Model.actVec at he
  obtain ⟨e', he', hf⟩ := List.mem_flatMap.1 he
  obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hf
  exact hact e'.1 (hv e' he') f hf'

theorem sign_keys (a : ℕ) (ha : a < 4096) :
    ∀ κ, WK κ → ∀ f ∈ Model.keyActSign a κ, NW f.1 := by
  rintro ⟨t, e, c⟩ ⟨ht, hc⟩ f hf
  dsimp only at ht hc
  subst ht
  change f ∈ [Model.signedTerm (Model.Key.W (Model.eYN a (e != 0) c).2.1
    (Model.eYN a (e != 0) c).2.2) ((Model.eYN a (e != 0) c).1 ^^ (Model.wordN a).testBit 0)] at hf
  rw [List.mem_singleton] at hf
  subst hf
  exact eYN_nw a ha _ hc

theorem pauli_keys (q : Model.Pauli) (hq : q.a < 4096) :
    ∀ κ, WK κ → ∀ f ∈ Model.keyActPauli q κ, NW f.1 := by
  rintro ⟨t, e, c⟩ ⟨ht, hc⟩ f hf
  dsimp only at ht hc
  subst ht
  change f ∈ [Model.signedTerm (Model.Key.W (Model.ePauliN q (e != 0) c).2.1
    (Model.ePauliN q (e != 0) c).2.2) (Model.ePauliN q (e != 0) c).1] at hf
  rw [List.mem_singleton] at hf
  subst hf
  exact ePauliN_nw q hq _ hc

theorem xi_keys : ∀ κ, WK κ → ∀ f ∈ Model.keyActXi κ, NW f.1 := by
  rintro ⟨t, e, c⟩ ⟨ht, hc⟩ f hf
  dsimp only at ht hc
  subst ht
  change f ∈ [false, true].flatMap (fun f => (List.range 64).map fun ν =>
      (Model.Key.W (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1
          (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).2.1
        (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1
          (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).2.2,
        -(Model.xiGammaN c f * Model.sgnI ((Model.xiGTerm ((e != 0) ^^ f) c ν).1 ^^
          (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1
            (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).1)))) at hf
  obtain ⟨b, -, hb⟩ := List.mem_flatMap.1 hf
  obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 hb
  have hν' : ν < 4096 := by
    have := List.mem_range.1 hν
    omega
  exact eYN_nw 1 (by decide) _ (shiftN_lt hν' (Rep4371Row.pi0_lt hc))

@[expose] def kidx (κ : Model.Key) : SpinIdx := (boolZ (κ.2.1 != 0), π₀ (toC κ.2.2))

@[expose] def kcoord (κ : Model.Key) (x : SpaceB) : ℚ := x.2.2 (kidx κ) 0

theorem kidx_inj {κ κ' : Model.Key} (h : NW κ) (h' : NW κ') (he : kidx κ = kidx κ') : κ = κ' := by
  obtain ⟨t, e, c⟩ := κ
  obtain ⟨t', e', c'⟩ := κ'
  obtain ⟨ht, he2, hc, hn⟩ := h
  obtain ⟨ht', he2', hc', hn'⟩ := h'
  dsimp only at ht he2 hc hn ht' he2' hc' hn'
  subst ht ht'
  unfold kidx at he
  obtain ⟨h1, h2⟩ := Prod.mk.inj he
  have h1' := boolZ_injective h1
  dsimp only at h1' h2
  have h2' : toC (Model.pi0N c) = toC (Model.pi0N c') := by
    rw [← coe_π₀_toC, ← coe_π₀_toC, h2]
  rw [hn, hn'] at h2'
  have hcc := toC_injective hc hc' h2'
  have hee : e = e' := by
    interval_cases e <;> interval_cases e' <;> first | rfl | exact absurd h1' (by decide)
  rw [hee, hcc]

theorem kcoord_keyVec {κ κ' : Model.Key} (h : NW κ) (h' : NW κ') :
    kcoord κ (keyVec κ') = if κ' = κ then 1 else 0 := by
  obtain ⟨t', e', c'⟩ := κ'
  have ht' : t' = 2 := h'.1
  subst ht'
  have hk : keyVec (2, e', c') = inW (tensor (Evec (e' != 0) c') wvec) := keyVec_two 0 e' c'
  rw [kcoord, hk]
  change Evec (e' != 0) c' (kidx κ) * wvec 0 = _
  have hw : wvec 0 = 1 := by simp [wvec]
  rw [hw, mul_one, Evec, E, Pi.single_apply]
  by_cases hk2 : (2, e', c') = κ
  · rw [if_pos hk2, if_pos]
    rw [← hk2]
    rfl
  · rw [if_neg hk2, if_neg]
    intro hi
    exact hk2 (kidx_inj h' h (by rw [hi]; rfl))

theorem kcoord_add (κ : Model.Key) (x y : SpaceB) : kcoord κ (x + y) = kcoord κ x + kcoord κ y :=
  rfl

theorem kcoord_smul (κ : Model.Key) (a : ℚ) (x : SpaceB) : kcoord κ (a • x) = a * kcoord κ x :=
  rfl

theorem kcoord_interp {κ : Model.Key} (h : NW κ) (D : ℚ) :
    ∀ v : List (Model.Key × ℤ), (∀ e ∈ v, NW e.1) →
      kcoord κ (interp D v) = (Model.coeffOf κ v : ℚ) / D
  | [], _ => by
    rw [interp_nil]
    simp [kcoord, Model.coeffOf]
  | e :: v, hv => by
    rw [interp_cons, kcoord_add, kcoord_smul, kcoord_keyVec h (hv e List.mem_cons_self),
      kcoord_interp h D v fun f hf => hv f (List.mem_cons_of_mem _ hf), coeffOf_cons]
    split_ifs <;> push_cast <;> ring

theorem eqModel_of_interp {D₁ D₂ : ℤ} (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0) {v₁ v₂ : List (Model.Key × ℤ)}
    (hv₁ : ∀ e ∈ v₁, NW e.1) (hv₂ : ∀ e ∈ v₂, NW e.1) (h : interp D₁ v₁ = interp D₂ v₂) :
    Model.eqModel D₁ v₁ D₂ v₂ = true := by
  unfold Model.eqModel
  rw [List.all_eq_true]
  intro e he
  have hκ : NW e.1 := by
    rcases List.mem_append.1 he with h' | h'
    · exact hv₁ e h'
    · exact hv₂ e h'
  have hc := congrArg (kcoord e.1) h
  rw [kcoord_interp hκ _ v₁ hv₁, kcoord_interp hκ _ v₂ hv₂] at hc
  have hD₁ : (D₁ : ℚ) ≠ 0 := Int.cast_ne_zero.2 h₁
  have hD₂ : (D₂ : ℚ) ≠ 0 := Int.cast_ne_zero.2 h₂
  rw [div_eq_div_iff hD₁ hD₂] at hc
  rw [beq_iff_eq]
  exact_mod_cast hc

theorem gQ_conj_eq (q : Model.Pauli)
    (hlab : ∀ k < 24, Model.conjYN 1 (Model.conjXiN (Model.conjYN 3 (genPauli k))) =
      Model.conjYN 3 (Model.conjPauliN q (Model.conjYN 1 (Model.conjXiN (genPauli k))))) :
    ∀ k < 24, conjQ (slPair * xiSignPair) (gQ k) =
      conjQ (xiSignPair * rhoPair (pauliQ q) * slPair) (gQ k) := by
  intro k hk
  exact (conjQ_lhs (genPauli k)).trans
    ((congrArg pauliQ (hlab k hk)).trans (conjQ_rhs q (genPauli k)).symm)

theorem lat_eq (q : Model.Pauli) : ((slPair * xiSignPair : Pvis) : GL SpinIdx ℚ × latticeO).2 =
    ((xiSignPair * rhoPair (pauliQ q) * slPair : Pvis) : GL SpinIdx ℚ × latticeO).2 := by
  rw [pvis_snd_mul, pvis_snd_mul, pvis_snd_mul, rhoPair_snd, slPair_snd, xiSignPair_snd, mul_one]
  exact gO3_comm_xi

theorem xiKeyRow_model_of {q : Model.Pauli} {η : Bool} {c : ℕ}
    (h : Native.Sp8.xiKeyRow q η c = true) :
    (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)]).all
        (fun e => e.1.1 != 0) = true ∧
      (Model.actVec (Model.keyActPauli q)
        (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)])).all (fun e => e.1.1 != 0) = true ∧
      Model.eqModel 4096 (Model.actVec Model.keyActXi
          (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)])) 262144
        (Model.actVec (Model.keyActSign 3) (Model.actVec (Model.keyActPauli q)
          (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)]))) = true := by
  simp only [Native.Sp8.xiKeyRow, Native.Sp8.noAKeys, Bool.and_eq_true] at h
  rw [native_actVec, native_keyActSign, native_keyActXi, native_keyActPauli, native_eqModel,
    native_Key_W] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem slPair_mul_xi_of_checks (q : Model.Pauli)
    (hlab : ∀ k < 24, Model.conjYN 1 (Model.conjXiN (Model.conjYN 3 (genPauli k))) =
      Model.conjYN 3 (Model.conjPauliN q (Model.conjYN 1 (Model.conjXiN (genPauli k)))))
    {η : Bool} {c : ℕ} (hkey : Native.Sp8.xiKeyRow q η c = true) :
    slPair * xiSignPair = xiSignPair * rhoPair (pauliQ q) * slPair := by
  obtain ⟨hl, hr, he⟩ := xiKeyRow_model_of hkey
  have L := theta_lhs_key hl
  have R := theta_rhs_key q hr
  have e1 : ((1 : ℚ) * 64 * 64) = ((4096 : ℤ) : ℚ) := by norm_num
  have e2 : ((1 : ℚ) * 64 * 64 * 64) = ((262144 : ℤ) : ℚ) := by norm_num
  rw [e1] at L
  rw [e2] at R
  exact pvis_eq_of_conj (lat_eq q) (gQ_conj_eq q hlab) η c
    (L.trans ((eqModel_sound (by norm_num) (by norm_num) he).trans R.symm))

theorem all_ne_of_nw {v : List (Model.Key × ℤ)} (h : ∀ e ∈ v, NW e.1) :
    v.all (fun e => e.1.1 != 0) = true := by
  rw [List.all_eq_true]
  intro e he
  rw [(h e he).1]
  rfl

theorem xiKeyRow_of_eq (q : Model.Pauli) (hq : q.a < 4096)
    (hP : slPair * xiSignPair = xiSignPair * rhoPair (pauliQ q) * slPair) (η : Bool) {c : ℕ}
    (hc : c < 4096) : Native.Sp8.xiKeyRow q η c = true := by
  have hW : ∀ e ∈ [(Model.Key.W η c, (1 : ℤ))], WK e.1 := fun e he => by
    rw [List.mem_singleton] at he
    subst he
    exact ⟨rfl, hc⟩
  have hl := mem_actVec hW (sign_keys 3 (by decide))
  have hr1 := mem_actVec hW xi_keys
  have hr2 := mem_actVec hr1 fun κ h => pauli_keys q hq κ h.wk
  have hv₁ := mem_actVec hl fun κ h => xi_keys κ h.wk
  have hv₂ := mem_actVec hr2 fun κ h => sign_keys 3 (by decide) κ h.wk
  have L := theta_lhs_key (all_ne_of_nw hl)
  have R := theta_rhs_key q (all_ne_of_nw hr2)
  rw [hP] at L
  have e1 : ((1 : ℚ) * 64 * 64) = ((4096 : ℤ) : ℚ) := by norm_num
  have e2 : ((1 : ℚ) * 64 * 64 * 64) = ((262144 : ℤ) : ℚ) := by norm_num
  rw [e1] at L
  rw [e2] at R
  have he := eqModel_of_interp (by norm_num) (by norm_num) hv₁ hv₂ (L.symm.trans R)
  simp only [Native.Sp8.xiKeyRow, Native.Sp8.noAKeys, Bool.and_eq_true]
  rw [native_actVec, native_keyActSign, native_keyActXi, native_keyActPauli, native_eqModel,
    native_Key_W]
  exact ⟨⟨all_ne_of_nw hl, all_ne_of_nw hr2⟩, he⟩

theorem xiKeyCheck_of_checks (q : Model.Pauli) (hq : q.a < 4096)
    (hlab : ∀ k < 24, Model.conjYN 1 (Model.conjXiN (Model.conjYN 3 (genPauli k))) =
      Model.conjYN 3 (Model.conjPauliN q (Model.conjYN 1 (Model.conjXiN (genPauli k)))))
    {η : Bool} {c : ℕ} (hkey : Native.Sp8.xiKeyRow q η c = true) :
    Native.Sp8.xiKeyCheck q = true := by
  have hP := slPair_mul_xi_of_checks q hlab hkey
  unfold Native.Sp8.xiKeyCheck
  rw [List.all_eq_true]
  intro c' hc'
  rw [List.all_eq_true]
  intro η' _
  exact xiKeyRow_of_eq q hq hP η' (List.mem_range.1 hc')

end CFSG.KC.Sp8Xi

end
