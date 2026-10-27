module

public import CFSG.CGT.PushingUpLit.BHS.SLCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
  CFSG.SL2MinimalFaithful CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem card_SL2_eq {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_le_of_isPGroup_of_dvd {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) {n m : ℕ}
    (hm : Odd m) (hd : Nat.card H ∣ 2 ^ n * m) : Nat.card H ≤ 2 ^ n := by
  obtain ⟨a, ha⟩ := hH.exists_card_eq
  rw [ha] at hd ⊢
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have : 2 ^ a ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right hd
  exact Nat.le_of_dvd (by positivity) this

theorem eq_one_of_pow_two_pow_eq_one {F : Type*} [Field F] [CharP F 2] {d : F} {k : ℕ}
    (h : d ^ 2 ^ k = 1) : d = 1 := by
  have h1 : (d - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

section Faithful

variable {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2]
  {E : Subgroup (MulAut W)}

omit [Finite W] [CharP F 2] in
theorem card_E_of_slNatData (D : SLNatData E F) :
    Nat.card E = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr D.θ.toEquiv, card_SL2_eq]

omit [Finite W] in
theorem odd_card_sq_sub_one_of_charTwo : Odd (Nat.card F ^ 2 - 1) := by
  obtain ⟨n, hn, hFn⟩ := card_eq_two_pow (k := F)
  rw [hFn]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  have h3 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  rcases h2 with ⟨c, hc⟩
  refine ⟨c - 1, ?_⟩
  have : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hc; omega
    · exact h0
  omega

theorem card_le_of_isPGroup_of_slNatData (D : SLNatData E F)
    {P : Subgroup (MulAut W)} (hPE : P ≤ E) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card F := by
  obtain ⟨n, hn, hFn⟩ := card_eq_two_pow (k := F)
  have hdvd : Nat.card P ∣ Nat.card E := Subgroup.card_dvd_of_le hPE
  rw [card_E_of_slNatData D] at hdvd
  have := card_le_of_isPGroup_of_dvd hP (n := n) (m := Nat.card F ^ 2 - 1)
    odd_card_sq_sub_one_of_charTwo (by rw [hFn] at hdvd ⊢; exact hdvd)
  rw [hFn]
  exact this

omit [Finite W] [Finite F] [CharP F 2] in
theorem psi_conj_slPerm (D : SLNatData E F)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) F,
      (D.psi x)⁻¹ * slPerm F g * D.psi x = slPerm F g' := by
  set e : ↥E := D.θ.symm g with he
  have hxe : (x : MulAut W)⁻¹ * (e : MulAut W) * (x : MulAut W) ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (E : Set (MulAut W))).inv_mem x.2) e).mp e.2
    simpa using this
  refine ⟨D.θ ⟨(x : MulAut W)⁻¹ * (e : MulAut W) * (x : MulAut W), hxe⟩, ?_⟩
  have h1 : D.psi ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ = slPerm F g := by
    rw [D.psi_of_mem, he, MulEquiv.apply_symm_apply]
  have h2 := D.psi_of_mem ⟨(x : MulAut W)⁻¹ * (e : MulAut W) * (x : MulAut W), hxe⟩
  rw [← h2, ← h1, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite W] [CharP F 2] in
theorem exists_semilinear_psi (D : SLNatData E F)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) :
    ∃ σ : F ≃+* F, IsSemilinearWith (D.psi x) σ :=
  exists_isSemilinearWith_of_normalizes (D.psi x) (D.psi_add x) (psi_conj_slPerm D x)

omit [Finite W] in
theorem mem_of_psi_fixes_line (D : SLNatData E F)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) {k : ℕ} (hx : x ^ 2 ^ k = 1)
    {v₀ : Fin 2 → F} (hv₀ : v₀ ≠ 0) (hfix : ∀ c : F, D.psi x (c • v₀) = c • v₀) :
    (x : MulAut W) ∈ E := by
  obtain ⟨σ, hσ⟩ := exists_semilinear_psi D x
  have hσid : ∀ c : F, σ c = c := by
    intro c
    have h1 := hσ c v₀
    have h2 := hfix 1
    rw [one_smul] at h2
    rw [hfix c, h2] at h1
    obtain ⟨i, hi⟩ : ∃ i, v₀ i ≠ 0 := by
      by_contra hcon
      exact hv₀ (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h3 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact (mul_right_cancel₀ hi h3).symm
  have hσ1 : σ = RingEquiv.refl F := RingEquiv.ext hσid
  subst hσ1
  set π := D.psi x with hπ
  have hadd : ∀ v v' : Fin 2 → F, π (v + v') = π v + π v' := D.psi_add x
  have hMv : ∀ w, (columnMat π).mulVec w = π w := fun w => by
    have := columnMat_mulVec hadd hσ w
    simpa using this
  have hdetpow : ∀ j : ℕ, columnDet (π ^ j) = columnDet π ^ j := by
    intro j
    induction j with
    | zero => simp [columnDet_one]
    | succ j ih =>
      rw [pow_succ', columnDet_mul hadd hσ (π ^ j), RingEquiv.refl_apply, ih, pow_succ']
  have hπpow : π ^ 2 ^ k = 1 := by rw [hπ, ← map_pow, hx, map_one]
  have hdet1 : columnDet π = 1 := by
    apply eq_one_of_pow_two_pow_eq_one (k := k)
    rw [← hdetpow, hπpow, columnDet_one]
  have hdet : (columnMat π).det = 1 := by rw [det_columnMat, hdet1]
  set g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨columnMat π, hdet⟩ with hg
  have hslπ : slPerm F g = π := by
    ext w : 1
    rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact hMv w
  have hmem : D.psi ⟨(D.θ.symm g : MulAut W), Subgroup.le_normalizer (D.θ.symm g).2⟩ = π := by
    rw [D.psi_of_mem, MulEquiv.apply_symm_apply, hslπ]
  have hxeq : x = ⟨(D.θ.symm g : MulAut W), Subgroup.le_normalizer (D.θ.symm g).2⟩ :=
    D.psi_injective (by rw [hmem])
  rw [hxeq]
  exact (D.θ.symm g).2

omit [Finite W] [Finite F] in
theorem eq_one_of_commute_of_sq_eq_one (D : SLNatData E F)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W))))
    (hc : ∀ e ∈ E, (x : MulAut W) * e = e * (x : MulAut W)) (h2 : x ^ 2 = 1) :
    (x : MulAut W) = 1 := by
  set π := D.psi x with hπ
  have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, π * slPerm F g = slPerm F g * π := by
    intro g
    set e : ↥E := D.θ.symm g with he
    have h1 : D.psi ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ = slPerm F g := by
      rw [D.psi_of_mem, he, MulEquiv.apply_symm_apply]
    rw [← h1, hπ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc e e.2)
  let c : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.mk' π (D.psi_add x)
  have hcv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      c ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (g : Matrix (Fin 2) (Fin 2) F).mulVec (c v) := by
    intro g v
    have h := congrArg (fun p : Equiv.Perm (Fin 2 → F) => p v) (hcomm g)
    simp only [Equiv.Perm.mul_apply, slPerm_apply, Matrix.SpecialLinearGroup.smul_def] at h
    exact h
  obtain ⟨a, ha⟩ := exists_scalar_of_commutes_sl2 c hcv
  have hπa : ∀ v, π v = a • v := ha
  have hπ2 : π * π = 1 := by rw [hπ, ← map_mul, ← pow_two, h2, map_one]
  have ha2 : a * a = 1 := by
    have h1 := congrArg (fun p : Equiv.Perm (Fin 2 → F) => p (Pi.single 0 1)) hπ2
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hπa] at h1
    have h3 := congrFun h1 0
    simpa [smul_smul] using h3
  have ha1 : a = 1 := eq_one_of_pow_two_pow_eq_one (k := 1) (by simpa [pow_two] using ha2)
  have hπ1 : D.psi x = 1 := by
    ext v : 1
    rw [← hπ, hπa, ha1, one_smul]
    rfl
  exact D.eq_one_of_psi_eq_one hπ1

theorem sl_core_of_ne_bot (D : SLNatData E F) {A : Subgroup (MulAut W)}
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W))) (hA : IsElemAbelian2 A) (hne : A ≠ ⊥)
    (hAw : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    A ≤ E ∧ Nat.card A = Nat.card F ∧ IsQuadratic A ∧
      Nat.card W = Nat.card A * Nat.card (fixV A) := by
  refine sl_core D hAN hA hAw fun hEA => hne ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hcomm : ∀ e ∈ E, a * e = e * a := fun e he => by
    have : ⁅e, a⁆ ∈ (⁅E, A⁆ : Subgroup (MulAut W)) := Subgroup.commutator_mem_commutator he ha
    rw [hEA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have h2 : (⟨a, hAN ha⟩ : ↥(Subgroup.normalizer (E : Set (MulAut W)))) ^ 2 = 1 :=
    Subtype.ext (hA.2 a ha)
  exact eq_one_of_commute_of_sq_eq_one D ⟨a, hAN ha⟩ hcomm h2

omit [CharP F 2] in
theorem exists_line_beta_fixV (D : SLNatData E F) (hF : 2 ≤ Nat.card F) {U : Subgroup (MulAut W)}
    (hUE : U ≤ E) (hUne : U ≠ ⊥) (hcardU : Nat.card U = Nat.card F)
    (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) :
    ∃ v₀ : Fin 2 → F, v₀ ≠ 0 ∧
      ∀ c : F, ∃ w ∈ fixV U, D.β w = Multiplicative.ofAdd (c • v₀) := by
  classical
  obtain ⟨⟨u₀, hu₀U⟩, hu₀'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUne
  have hu₀ : u₀ ≠ 1 := fun h => hu₀' (Subtype.ext h)
  have hu₀E : (u₀ : MulAut W) ∈ E := hUE hu₀U
  set e₀ : ↥E := ⟨(u₀ : MulAut W), hu₀E⟩ with he₀
  have he₀ne : e₀ ≠ 1 := fun h => hu₀ (congrArg Subtype.val h)
  set g₀ := D.θ e₀ with hg₀
  have hg₀ne : g₀ ≠ 1 := fun h => he₀ne (D.θ.injective (by rw [← hg₀, h, map_one]))
  let K : Submodule F (Fin 2 → F) :=
    { carrier := {v | (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v = v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [Matrix.mulVec_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        simp only [Set.mem_ofPred_eq] at *
        rw [Matrix.mulVec_smul, hv] }
  have hKne : K ≠ ⊤ := by
    intro h
    apply hg₀ne
    apply eq_one_of_forall_smul_vec
    intro v
    have : v ∈ K := by rw [h]; trivial
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact this
  have hKrank : Module.finrank F K < 2 := by
    have := Submodule.finrank_lt hKne
    simpa [Module.finrank_fin_fun] using this
  have hKcard : Nat.card K ≤ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    calc Nat.card F ^ Module.finrank F K ≤ Nat.card F ^ 1 :=
          Nat.pow_le_pow_right Nat.card_pos (by omega)
      _ = Nat.card F := pow_one _
  set L : Subgroup (Multiplicative (Fin 2 → F)) := (fixV U).map D.β with hL
  have hLK : ∀ d ∈ L, Multiplicative.toAdd d ∈ K := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := D.equivar' e₀ w
    have h2 : (e₀ : MulAut W) w = w := hw (e₀ : MulAut W) hu₀U
    rw [h2] at h1
    show (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (D.β w)) =
      Multiplicative.toAdd (D.β w)
    have := h1.symm
    rwa [Matrix.SpecialLinearGroup.smul_def] at this
  have hind : (fixV U).index = Nat.card U := by
    have h1 : Nat.card (fixV U) * (fixV U).index = Nat.card W := Subgroup.card_mul_index _
    have hpos : 0 < Nat.card (fixV U) := Nat.card_pos
    rw [hW, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨-, -, h3⟩ := D.index_chain U
  have hLidx : L.index ≤ Nat.card F := by
    rw [hL]; rw [← hcardU, ← hind]; exact h3
  have hLcard : Nat.card F ≤ Nat.card L := by
    have h1 : Nat.card L * L.index = Nat.card (Multiplicative (Fin 2 → F)) :=
      Subgroup.card_mul_index L
    rw [SLNatData.card_dual (F := F)] at h1
    have h2 : Nat.card F * Nat.card F ≤ Nat.card L * Nat.card F := by
      calc Nat.card F * Nat.card F = Nat.card F ^ 2 := (sq _).symm
        _ = Nat.card L * L.index := h1.symm
        _ ≤ Nat.card L * Nat.card F := Nat.mul_le_mul_left _ hLidx
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  let ι : L → K := fun d => ⟨Multiplicative.toAdd (d : Multiplicative (Fin 2 → F)), hLK d d.2⟩
  have hιinj : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    exact Multiplicative.toAdd.injective (congrArg (fun k : ↥K => (k : Fin 2 → F)) h)
  have hιbij : Function.Bijective ι :=
    hιinj.bijective_of_nat_card_le (hKcard.trans hLcard)
  have hKcard' : 2 ≤ Nat.card K := by
    have := Nat.card_congr (Equiv.ofBijective ι hιbij)
    omega
  obtain ⟨v₀, hv₀K, hv₀ne⟩ : ∃ v₀ ∈ K, v₀ ≠ 0 := by
    by_contra hcon
    have hall : ∀ x ∈ K, x = 0 := fun x hx => by
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩
    have hsub : Subsingleton K := ⟨fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  refine ⟨v₀, hv₀ne, fun c => ?_⟩
  obtain ⟨d, hd⟩ := hιbij.2 ⟨c • v₀, K.smul_mem c hv₀K⟩
  obtain ⟨w, hw, hwd⟩ := d.2
  refine ⟨w, hw, ?_⟩
  rw [hwd]
  apply Multiplicative.toAdd.injective
  exact congrArg Subtype.val hd

theorem sl_family (D : SLNatData E F) (hF : 2 ≤ Nat.card F)
    {Q : Subgroup (MulAut W)} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (E : Set (MulAut W)))
    {𝒜 : Set (Subgroup (MulAut W))} (hne : 𝒜.Nonempty)
    (h𝒜 : ∀ A ∈ 𝒜, A ≤ Q ∧ IsElemAbelian2 A ∧ A ≠ ⊥ ∧
      Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ U : Subgroup (MulAut W), U ≤ E ∧ Nat.card U = Nat.card F ∧ (∀ A ∈ 𝒜, A = U) ∧
      ¬ fixV U ≤ fixV E ∧
      ∀ Q'' : Subgroup (MulAut W), IsPGroup 2 Q'' →
        Q'' ≤ Subgroup.normalizer (E : Set (MulAut W)) → fixV U ≤ fixV Q'' →
          Q'' ≤ E ∧ Nat.card Q'' ≤ Nat.card F := by
  classical
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨hA₀Q, hA₀e, hA₀ne, hA₀w⟩ := h𝒜 A₀ hA₀
  obtain ⟨hA₀E, hA₀card, -, hA₀W⟩ := sl_core_of_ne_bot D (hA₀Q.trans hQN) hA₀e hA₀ne hA₀w
  refine ⟨A₀, hA₀E, hA₀card, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨hAQ, hAe, hAne, hAw⟩ := h𝒜 A hA
    obtain ⟨hAE, hAcard, -, -⟩ := sl_core_of_ne_bot D (hAQ.trans hQN) hAe hAne hAw
    have hsupQ : A ⊔ A₀ ≤ Q := sup_le hAQ hA₀Q
    have hsupE : A ⊔ A₀ ≤ E := sup_le hAE hA₀E
    have hle := card_le_of_isPGroup_of_slNatData D hsupE (hQ.to_le hsupQ)
    have h1 : A = A ⊔ A₀ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAcard]; exact hle)
    have h2 : A₀ = A ⊔ A₀ :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hA₀card]; exact hle)
    exact h1.trans h2.symm
  · intro hle
    have hidx : (fixV E).index ∣ (fixV A₀).index := Subgroup.index_dvd_of_le hle
    have h1 : (fixV A₀).index = Nat.card A₀ := by
      have h1 : Nat.card (fixV A₀) * (fixV A₀).index = Nat.card W := Subgroup.card_mul_index _
      have hpos : 0 < Nat.card (fixV A₀) := Nat.card_pos
      rw [hA₀W, mul_comm] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    have h2 : (fixV E).index = Nat.card F ^ 2 := by
      have hker : fixV E = D.β.ker := by
        ext w
        rw [MonoidHom.mem_ker]
        exact (D.ker_iff w).symm
      rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr D.surj, Subgroup.card_top,
        SLNatData.card_dual (F := F)]
    rw [h1, hA₀card, h2] at hidx
    have := Nat.le_of_dvd Nat.card_pos hidx
    nlinarith
  · intro Q'' hQ'' hQ''N hfix
    obtain ⟨v₀, hv₀, hline⟩ := exists_line_beta_fixV D hF hA₀E hA₀ne hA₀card hA₀W
    have hQ''E : Q'' ≤ E := by
      intro q hq
      have hqN : q ∈ Subgroup.normalizer (E : Set (MulAut W)) := hQ''N hq
      obtain ⟨k, hk⟩ := hQ'' ⟨q, hq⟩
      have hx : (⟨q, hqN⟩ : ↥(Subgroup.normalizer (E : Set (MulAut W)))) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hk
      refine mem_of_psi_fixes_line D ⟨q, hqN⟩ hx hv₀ fun c => ?_
      obtain ⟨w, hw, hwβ⟩ := hline c
      have h1 := D.psi_spec ⟨q, hqN⟩ w
      have h2 : q w = w := hfix hw q hq
      rw [h2, hwβ] at h1
      simpa using h1.symm
    exact ⟨hQ''E, card_le_of_isPGroup_of_slNatData D hQ''E hQ''⟩

end Faithful

end CFSG.CGT.PushingUpLit.BHS6
