module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3L4
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.U4

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.L4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

section Torus

variable {ℓ e : ℕ} {L : Type} [Field L] (h : UnitaryFieldData ℓ e L)

abbrev SU4 : Subgroup (GL (Fin 4) L) := gramSU h ((1 : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)

abbrev PU4 : Type := primeFormP h ((1 : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)

@[expose] noncomputable def normU : Lˣ →* Lˣ :=
  MonoidHom.id Lˣ * Units.map h.bar.toMonoidHom

theorem coe_normU (x : Lˣ) : ((normU h x : Lˣ) : L) = h.norm x := rfl

theorem toGL_torusHom_mem {v : Lˣ × (Lˣ × Lˣ)} (hv : ∀ i, h.norm (torusDiag v i) = 1) :
    Matrix.SpecialLinearGroup.toGL (torusHom v) ∈ SU4 h := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_torusHom, Units.val_one, Matrix.mul_one,
      diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hv i
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact (torusHom v).2

theorem norm_torusDiag {u : Lˣ} (hu : h.norm (u : L) = 1) {v : Lˣ × (Lˣ × Lˣ)}
    (hv : v ∈ torusDom u) (i : Fin 4) : h.norm (torusDiag v i) = 1 := by
  have hN : ∀ x : Lˣ, x ∈ Subgroup.zpowers u → normU h x = 1 := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, Units.ext (show ((normU h u : Lˣ) : L) = ((1 : Lˣ) : L) from hu), _root_.one_zpow]
  have h1 := hN _ hv.1
  have h2 := hN _ hv.2.1
  have h3 := hN _ hv.2.2
  have hdiv : ∀ x y : Lˣ, normU h x = 1 → normU h y = 1 → h.norm ((x : L) / y) = 1 :=
    fun x y hx hy => by
      rw [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← coe_normU, map_mul,
        map_inv, hx, hy, inv_one, mul_one, Units.val_one]
  fin_cases i
  · change h.norm (v.1 : L) = 1
    rw [← coe_normU, h1, Units.val_one]
  · exact hdiv _ _ h2 h1
  · exact hdiv _ _ h3 h2
  · change h.norm (1 / (v.2.2 : L)) = 1
    rw [← Units.val_one]
    exact hdiv _ _ (map_one _) h3

@[expose] noncomputable def torusSU {u : Lˣ} (hu : h.norm (u : L) = 1) :
    ↥(torusDom u) →* SU4 h :=
  ((Matrix.SpecialLinearGroup.toGL.comp torusHom).comp (torusDom u).subtype).codRestrict _
    fun v => toGL_torusHom_mem h (norm_torusDiag h hu v.2)

theorem eq_one_of_torusDiag {F : Type} [Field F] {v : Fˣ × (Fˣ × Fˣ)} (hv3 : v ^ 3 = 1) {c : F}
    (hc4 : c ^ 4 = 1) (hc : ∀ i, torusDiag v i = c) : v = 1 := by
  have h3 : (v.1 : F) ^ 3 = 1 := by
    have := congrArg (fun w : Fˣ × (Fˣ × Fˣ) => (w.1 : F)) hv3
    simpa using this
  have hc0 : (v.1 : F) = c := hc 0
  have hx1 : (v.1 : F) = 1 := by
    have h4 : (v.1 : F) ^ 4 = 1 := by rw [hc0]; exact hc4
    have : (v.1 : F) ^ 4 = (v.1 : F) ^ 3 * v.1 := pow_succ _ 3
    rw [h4, h3, one_mul] at this
    exact this.symm
  have hy1 : (v.2.1 : F) = 1 := by
    have := hc 1
    change (v.2.1 : F) / v.1 = c at this
    rw [← hc0, hx1, div_one] at this
    exact this
  have hz1 : (v.2.2 : F) = 1 := by
    have := hc 2
    change (v.2.2 : F) / v.2.1 = c at this
    rw [← hc0, hy1, hx1, div_one] at this
    exact this
  exact Prod.ext (Units.ext hx1) (Prod.ext (Units.ext hy1) (Units.ext hz1))

variable {ω : L} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hN : h.norm ω = 1) (h2 : (2 : L) ≠ 0)

@[expose] noncomputable def torusPU (hN : h.norm ω = 1) :
    ↥(torusDom (ωU (ω_ne_zero hω3))) →* PU4 h :=
  (QuotientGroup.mk' _).comp (torusSU h (u := ωU (ω_ne_zero hω3)) hN)

include hω3 in
theorem torusPU_injective : Function.Injective (torusPU h hω3 hN) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hs := (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨c, -, hc4, hcx⟩ := hs
  have hcx' := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) hcx
  change diagonal (torusDiag (x : Lˣ × (Lˣ × Lˣ))) = _ at hcx'
  rw [Matrix.GeneralLinearGroup.coe_scalar] at hcx'
  have hx3 : (x : Lˣ × (Lˣ × Lˣ)) ^ 3 = 1 := (isElemAbelian_torusDom hω3).2 _ x.2
  have hc4' : (c : L) ^ 4 = 1 := by
    have := congrArg Units.val hc4
    simpa using this
  apply Subtype.ext
  exact eq_one_of_torusDiag hx3 hc4' fun i => by
    have := congrFun (congrFun hcx' i) i
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this

@[expose] noncomputable def tSU : SU4 h :=
  ⟨Matrix.SpecialLinearGroup.toGL tTorus, toGL_torusHom_mem h fun i => by
    fin_cases i <;> simp [torusDiag, UnitaryFieldData.norm]⟩

include h2 in
theorem tPU_ne_one : (QuotientGroup.mk' _ (tSU h) : PU4 h) ≠ 1 := by
  intro ht
  obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff _).1 ht
  have hc' := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) hc
  change diagonal (torusDiag ((-1 : Lˣ), ((1 : Lˣ), (1 : Lˣ)))) = _ at hc'
  rw [Matrix.GeneralLinearGroup.coe_scalar] at hc'
  have e0 := congrFun (congrFun hc' 0) 0
  have e2 := congrFun (congrFun hc' 2) 2
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, torusDiag] at e0 e2
  apply h2
  linear_combination e2 - e0

include hω hω3 hN h2 in
theorem three_le_twoLocalRank_PU [Finite L] : 3 ≤ GLATwoLocalRank 3 (PU4 h) := by
  set E : Subgroup (PU4 h) := (torusPU h hω3 hN).range with hE
  set t : PU4 h := QuotientGroup.mk' _ (tSU h) with ht
  set T : Subgroup (PU4 h) := Subgroup.zpowers t with hT
  have hEc : Nat.card E = 3 ^ 3 := by
    rw [hE, ← Nat.card_congr (MonoidHom.ofInjective (torusPU_injective h hω3 hN)).toEquiv,
      card_torusDom hω hω3]
  have hEl : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      change (a : PU4 h) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext ((isElemAbelian_torusDom hω3).2 _ x.2)
      rw [this, map_one]
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← map_pow]
    have : tSU h ^ 2 = 1 := Subtype.ext (by
      change Matrix.SpecialLinearGroup.toGL (tTorus (F := L)) ^ 2 = 1
      rw [← map_pow, tTorus_sq, map_one])
    rw [this, map_one]
  have hT1 : T ≠ ⊥ := fun hb => tPU_ne_one h h2 (by
    have := Subgroup.mem_zpowers t
    rw [← hT, hb, Subgroup.mem_bot] at this
    exact this)
  have hT2 : IsPGroup 2 T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [hT, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht2 (tPU_ne_one h h2)
  have hEN : E ≤ Subgroup.normalizer (T : Set (PU4 h)) := by
    rintro _ ⟨v, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine (Commute.zpow_left ?_ k).eq
    change Commute (QuotientGroup.mk' _ (tSU h)) (QuotientGroup.mk' _ (torusSU h _ v))
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toGL (tTorus (F := L)) *
        Matrix.SpecialLinearGroup.toGL (torusHom (v : Lˣ × (Lˣ × Lˣ))) =
      Matrix.SpecialLinearGroup.toGL (torusHom (v : Lˣ × (Lˣ × Lˣ))) *
        Matrix.SpecialLinearGroup.toGL (tTorus (F := L))
    rw [← map_mul, ← map_mul, tTorus, torusHom_comm]
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    (by norm_num : 1 < 3) hT1 hT2 hEl hEN hEc

end Torus

theorem concC_of_twistedA3
    {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 Q, hv⟩).Group)
    (h3 : 3 ∣ Q.card + 1) : S267ConcBCDE 3 q S B := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
  haveI : Fact Q.p.Prime := ⟨hp⟩
  haveI : CharP K Q.p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  have h : UnitaryFieldData Q.p Q.exponent K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have h3' : 3 ∣ Q.p ^ Q.exponent + 1 := by rwa [TauCeti.PrimePower.card_def] at h3
  have hQ5 : 5 ≤ Q.p ^ Q.exponent :=
    (hp.five_le_of_ne_two_of_ne_three hp2 hp3).trans (Nat.le_self_pow (by omega) _)
  have hg : ¬ 3 ∣ Nat.gcd 4 (Q.p ^ Q.exponent + 1) := fun hd =>
    absurd ((hd.trans (Nat.gcd_dvd_left _ _) : 3 ∣ 4)) (by norm_num)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hK
      (by decide : Even 4) (by norm_num) (by omega)
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact hg
  let e₂ : PU4 h ≃* StatedProj (StatedSU 4 (Q.p ^ Q.exponent) K) :=
    (nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 4))).some.trans
      (unitaryPSUEquiv h (by norm_num))
  let ε : ↥S ≃* PU4 h := ((psimpleEquiv H hZ).symm.trans e₁).trans e₂.symm
  have hKu : 3 ∣ Nat.card Kˣ := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    obtain ⟨k, hk⟩ := h3'
    have h1 : 1 ≤ Q.p ^ Q.exponent := by omega
    have : (Q.p ^ Q.exponent) ^ 2 - 1 = (Q.p ^ Q.exponent - 1) * (Q.p ^ Q.exponent + 1) := by
      zify [h1, Nat.one_le_pow 2 _ (by omega : 0 < Q.p ^ Q.exponent)]
      ring
    rw [this, hk]
    exact Dvd.dvd.mul_left (dvd_mul_right 3 k) _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hKu
  have hω3 : (u : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hω : (u : K) ≠ 1 := fun hu1 => by
    have : u = 1 := Units.ext hu1
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hNω : h.norm (u : K) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
    obtain ⟨k, hk⟩ := h3'
    rw [hk, pow_mul, hω3, one_pow]
  have h2K : (2 : K) ≠ 0 := by
    have hc : ((2 : ℕ) : K) ≠ 0 := fun hc => hp2 ((Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_two).1 ((CharP.cast_eq_zero_iff K Q.p 2).1 hc))
    exact_mod_cast hc
  have hn4 : 3 ≤ 4 := by norm_num
  have hq4 : ¬(4 = 3 ∧ Q.p ^ Q.exponent = 2) := by omega
  have hW : 3 ≤ GLATwoLocalRank 3 ↥S := by
    have hr := CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ε Nat.prime_three
    change 3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥S
    rw [hr]
    exact three_le_twoLocalRank_PU h hω hω3 hNω h2K
  have hF : ∀ β : MulAut ↥S, CFSG.RankThree.PartOne.CTP.IsOuterOfOrder 3 β →
      ∃ (M : Type) (_ : Group M) (_ : Finite M), 3 ≤ GLATwoLocalRank 3 M ∧
        Subgroup.center M = ⊥ ∧ ∃ ψ : M →* ↥S, Function.Injective ψ ∧ ∀ m, β (ψ m) = ψ m := by
    rintro β ⟨hβo, hβout⟩
    set a := MulAut.congr ε β with ha
    have hao : orderOf a = 3 := by rw [ha, MulEquiv.orderOf_eq, hβo]
    have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
    set σ := primeFormFieldFactor h isPrimeFormGram_one hn4 hq4 a with hσdef
    have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, ha3, map_one]
    have hσ : orderOf σ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hσ3) with h1 | h1
      · exfalso
        have hσ1 : σ = 1 := orderOf_eq_one_iff.1 h1
        have hD : a ∈ primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn4 hq4]
          exact hσ1
        obtain ⟨x, hx⟩ := CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn4
          hq4 Nat.prime_three hg hD ha3
        apply hβout (ε.symm x)
        apply (MulAut.congr ε).injective
        rw [congr_conj, MulEquiv.apply_symm_apply, hx]
      · exact h1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent
        h hn4 hq4 Nat.prime_three (by norm_num) (by omega) a hao σ rfl hσ
    have haeq : a = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
        (primeFormConjHom h _ M)⁻¹ := by
      rw [← hM]
      group
    set h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
      (by norm_num) hσ with hh₀
    have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three
      (by norm_num) hσ
    have hσω : σ (u : K) = u := fix_cube_root hσ hω hω3
    set ω₀ : CFSG.LieType.Chevalley.fixSubfield σ := ⟨u, hσω⟩ with hω₀
    have hω₀3 : ω₀ ^ 3 = 1 := Subtype.ext (by simpa using hω3)
    have hω₀1 : ω₀ ≠ 1 := fun h1 => hω (congrArg Subtype.val h1)
    have hN₀ : h₀.norm ω₀ = 1 := Subtype.ext (by
      rw [← CFSG.RankThree.Classical.norm_subtype h h₀ hbar ω₀]
      exact hNω)
    have h2₀ : (2 : CFSG.LieType.Chevalley.fixSubfield σ) ≠ 0 := fun h0 =>
      h2K (by rw [← map_ofNat (CFSG.LieType.Chevalley.fixSubfield σ).subtype 2, h0, map_zero])
    have hq0 : ¬(4 = 3 ∧ Q.p ^ (Q.exponent / 3) = 2) := by omega
    haveI := h₀.finite
    have hsimple := CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h₀ hn4 hq0
    have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one h₀ hn4 hq0
    have hZ₀ : Subgroup.center (PU4 h₀) = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (PU4 h₀)) with hb | ht
      · exact hb
      · exfalso
        apply hnc
        intro x y
        have hx : x ∈ Subgroup.center (PU4 h₀) := by rw [ht]; trivial
        exact (Subgroup.mem_center_iff.1 hx y).symm
    refine ⟨PU4 h₀, inferInstance, inferInstance,
      three_le_twoLocalRank_PU h₀ hω₀1 hω₀3 hN₀ h2₀, hZ₀,
      (ε.symm.toMonoidHom.comp (primeFormConjHom h _ M).toMonoidHom).comp
        (CFSG.RankThree.Classical.subfieldPSU h h₀ hbar 4), ?_, ?_⟩
    · exact ε.symm.injective.comp ((primeFormConjHom h _ M).injective.comp
        (CFSG.RankThree.Classical.subfieldPSU_injective h h₀ hbar 4 (by norm_num)))
    · intro m
      have key : ∀ z, β (ε.symm z) = ε.symm (a z) := fun z => by
        rw [ha, MulAut.congr_apply]
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      have hfix := CFSG.RankThree.Classical.range_subfieldPSU_le h 4 h₀ hbar ⟨m, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [key, haeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      congr 2
  obtain ⟨hsup, hinf⟩ := H.eq_sup hZ hW hF
  exact Or.inr (Or.inl ⟨H.card, hsup, hinf, H.center_pQuot_eq_bot hZ, Q, hQq,
    Or.inr ⟨⟨.lie ⟨_, hv⟩, rfl, ⟨e⟩⟩, h3⟩⟩)

theorem p3At_twistedA_three_of_dvd_add_one
    {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid) (h3 : 3 ∣ Q.card + 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exact Or.inr (concC_of_twistedA3 H (by simpa using hchar) hv e h3)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.U4

end
