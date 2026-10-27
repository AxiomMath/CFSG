module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.TauCetiBridge.Twisted CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof TauCeti Matrix

theorem not_three_dvd_prime_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (k : ℕ) : ¬ 3 ∣ ℓ ^ k :=
  fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

section Fixed

variable {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}

theorem card_le_nine_of_fixedPoints_of_ne_three (hp3 : q.p ≠ 3)
    (E : Subgroup (D4Tripled.points (d4Closure q hv))) [Finite E]
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hfix : ∀ g ∈ E, (d4Index q hv).steinberg g = g) : Nat.card E ≤ 9 := by
  set L := d4Closure q hv with hL
  have hchar : d4Char q hv = q.p := d4Char_eq q hv
  have : CharP L q.p := hchar ▸ inferInstance
  have h3 : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L q.p] at h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h')
  set β : Fin 3 → ↥E →* Matrix.GeneralLinearGroup (Fin 8) L := fun k =>
    (blkHom k).comp ((Subgroup.inclusion (points_le_blockGL L)).comp E.subtype) with hβ
  have hβval : ∀ k (x : ↥E), ((β k x : Matrix.GeneralLinearGroup (Fin 8) L) :
      Matrix (Fin 8) (Fin 8) L) = blk k (((x : D4Tripled.points L) :
        Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) := fun _ _ => rfl
  have hcl : ∀ x : ↥E, CliffEq (((x : D4Tripled.points L) :
      Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) := fun x =>
    cliffEq_of_mem_points L _ (x : D4Tripled.points L).2
  refine card_le_nine_of_triality h3 (fun x y => hE.1.1.comm x y)
    (fun x => Subtype.ext (hE.2 x x.2)) β (fun x hx => ?_) (castM formMat)
    det_formMat_map_ne_zero muR nuR muR_smul_left muR_smul_right nuR_smul_right
    (fun x v s => ?_) (fun x v u => ?_) nuR_muR_add (d4Fr q hv) q.card
    (by rw [PrimePower.card_def]; exact not_three_dvd_prime_pow q.prime_p hp3 _)
    (d4Fr_apply q hv) trialityBlkPerm (fun x j r c => ?_)
  ·
    have hM := d4_points_isBlockDiag L _ (x : D4Tripled.points L).2
    have h1 := eq_one_of_blk hM fun k => by
      rw [← hβval, hx k, Units.val_one]
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  · rw [hβval, hβval, hβval]
    exact mulVec_muR (hcl x) v s
  · rw [hβval, hβval, hβval]
    exact mulVec_nuR (hcl x) v u
  · rw [hβval, hβval, d4Fr_apply]
    exact steinberg_fixed_blk _ (hfix x x.2) j r c

end Fixed

section Lift

variable {Q R : Type*} [Group Q] [Group R]

theorem exists_elemAbelian_lift_of_center_pow_sixteen (ψ : Q →* R)
    (hψs : Function.Surjective ψ) (hker : ∀ y, ψ y = 1 → y ^ 16 = 1 ∧ y ∈ Subgroup.center Q)
    (E₀ : Subgroup R) (hE₀3 : ∀ e ∈ E₀, e ^ 3 = 1)
    (hE₀c : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e) :
    ∃ F' : Subgroup Q, Nat.card F' = Nat.card E₀ ∧ (∀ y ∈ F', y ^ 3 = 1) ∧
      ∀ y ∈ F', ∀ y' ∈ F', y * y' = y' * y := by
  classical
  have hEt3 : ∀ a ∈ E₀.comap ψ, ψ (a ^ 3) = 1 := fun a ha => by rw [map_pow]; exact hE₀3 _ ha
  have hEtc : ∀ a ∈ E₀.comap ψ, ∀ b ∈ E₀.comap ψ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨c, hc⟩ : ∃ c, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
    have hψc : ψ c = 1 := by
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, hE₀c _ ha _ hb]
      group
    obtain ⟨hc16, hcz⟩ := hker c hψc
    obtain ⟨-, ha3z⟩ := hker (a ^ 3) (hEt3 a ha)
    have hstep : ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = c ^ n * b := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : c ^ n ∈ Subgroup.center Q := Subgroup.pow_mem _ hcz n
        calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
              group
          _ = a * (c ^ n * b) * a⁻¹ := by rw [ih]
          _ = c ^ n * (a * b * a⁻¹) := by
              rw [← mul_assoc a (c ^ n) b, Subgroup.mem_center_iff.1 hcn a]
              group
          _ = c ^ (n + 1) * b := by rw [hc, pow_succ]; group
    have hc3 : c ^ 3 = 1 := by
      have e1 := hstep 3
      rw [← Subgroup.mem_center_iff.1 ha3z b, mul_inv_cancel_right] at e1
      have e2 : c ^ 3 * b = 1 * b := by rw [one_mul]; exact e1.symm
      exact mul_right_cancel e2
    have hc1 : c = 1 := by
      calc c = c ^ 16 * ((c ^ 3)⁻¹) ^ 5 := by group
        _ = 1 := by rw [hc16, hc3]; group
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [← hc, hc1, one_mul]
  let s : ↥(E₀.comap ψ) →* Q :=
    { toFun := fun a => (a : Q) ^ 16
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]
        exact Commute.mul_pow (hEtc _ a.2 _ b.2) 16 }
  have hψ16 : ∀ a ∈ E₀.comap ψ, ψ (a ^ 16) = ψ a := by
    intro a ha
    have h3 := hE₀3 _ ha
    rw [map_pow, show (16 : ℕ) = 3 * 5 + 1 from rfl, pow_succ, pow_mul, h3, one_pow, one_mul]
  have hF'3 : ∀ y ∈ s.range, y ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    change ((a : Q) ^ 16) ^ 3 = 1
    rw [← pow_mul, show 16 * 3 = 3 * 16 from rfl, pow_mul]
    exact (hker _ (hEt3 _ a.2)).1
  have hF'Et : ∀ y ∈ s.range, y ∈ E₀.comap ψ := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.pow_mem _ a.2 16
  refine ⟨s.range, ?_, hF'3, fun y hy y' hy' => hEtc _ (hF'Et _ hy) _ (hF'Et _ hy')⟩
  refine Nat.card_congr (Equiv.ofBijective (fun y : s.range => (⟨ψ y, hF'Et _ y.2⟩ : E₀))
    ⟨fun y y' hyy' => ?_, ?_⟩)
  · have e1 : ψ ((y : Q) * (y' : Q)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact congrArg Subtype.val hyy'
    obtain ⟨z, hz⟩ : ∃ z, z = (y : Q) * (y' : Q)⁻¹ := ⟨_, rfl⟩
    rw [← hz] at e1
    have hz3 : z ^ 3 = 1 := hz ▸ hF'3 _ (mul_mem y.2 (inv_mem y'.2))
    have hz16 := (hker _ e1).1
    have hz1 : z = 1 := by
      calc z = z ^ 16 * ((z ^ 3)⁻¹) ^ 5 := by group
        _ = 1 := by rw [hz16, hz3]; group
    rw [hz] at hz1
    exact Subtype.ext (mul_inv_eq_one.1 hz1)
  · rintro ⟨e, he⟩
    obtain ⟨a, ha⟩ := hψs e
    have haEt : a ∈ E₀.comap ψ := by
      change ψ a ∈ E₀
      rw [ha]
      exact he
    refine ⟨⟨s ⟨a, haEt⟩, ⟨a, haEt⟩, rfl⟩, Subtype.ext ?_⟩
    change ψ (a ^ 16) = e
    rw [hψ16 a haEt, ha]

end Lift

section Kernel


theorem pow_sixteen_eq_one_of_pushDown (L : Type) [Field L] (h2 : (2 : L) ≠ 0)
    (z : ↥(D4Tripled.points L)) (hz : (d4PushDown L).π z = 1) : z ^ 16 = 1 := by
  set M := ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) with hMdef
  have hc := (d4PushDown L).ker_iff z |>.1 hz
  have hdiag : ∀ a b, a ≠ b → M a b = 0 := fun a b hab =>
    d4_isDiag_of_commute h2 (D4PushDown.commute_diag_of hc) hab
  have hconst : ∀ a b, d4Blk a = d4Blk b → M a a = M b b := fun a b hab =>
    d4_diag_eq_of_commute hdiag (fun i => (hc i).1) (fun i => (hc i).2) hab
  set c : Fin 3 → L := fun k => M (blkIdx k 0) (blkIdx k 0) with hcdef
  have hMa : ∀ a, M a a = c (d4Blk a) := by
    intro a
    obtain ⟨⟨k, r⟩, rfl⟩ := blkIdx_bijective.2 a
    rw [d4Blk_blkIdx]
    exact hconst _ _ (by rw [d4Blk_blkIdx, d4Blk_blkIdx])
  have hblk : ∀ k, blk k M = c k • (1 : Matrix (Fin 8) (Fin 8) L) := by
    intro k
    ext r s
    rw [blk_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hrs : r = s
    · subst hrs
      rw [hMa, d4Blk_blkIdx, Matrix.one_apply_eq, mul_one]
    · rw [hdiag _ _ ((blkIdx_injective k).ne hrs), Matrix.one_apply_ne hrs, mul_zero]
  have hcl : CliffEq M := cliffEq_of_mem_points L (z : Matrix.GeneralLinearGroup (Fin 24) L) z.2
  have hlc : ∀ (u : L) a, lcMu (u • (1 : Matrix (Fin 8) (Fin 8) L)) a = u • castM (muMat a) ∧
      lcNu (u • (1 : Matrix (Fin 8) (Fin 8) L)) a = u • castM (nuMat a) := by
    intro u a
    rw [lcMu_smul, lcMu_one, lcNu_smul, lcNu_one]
    exact ⟨rfl, rfl⟩
  have h20 : c 2 = c 0 * c 1 := by
    have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) L => A 0 0) ((hcl 3).1)
    simp only [hblk, (hlc _ _).1, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h
    have h1 : (castM (muMat 3) : Matrix (Fin 8) (Fin 8) L) 0 0 = 1 := by
      rw [castM_apply]
      norm_num [muMat]
    rw [h1, mul_one, mul_one] at h
    exact h
  have h10 : c 1 = c 0 * c 2 := by
    have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) L => A 0 0) ((hcl 4).2)
    simp only [hblk, (hlc _ _).2, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h
    have h1 : (castM (nuMat 4) : Matrix (Fin 8) (Fin 8) L) 0 0 = 1 := by
      rw [castM_apply]
      norm_num [nuMat]
    rw [h1, mul_one, mul_one] at h
    exact h
  have hdet := det_eq_one_of_mem_points L (z : Matrix.GeneralLinearGroup (Fin 24) L) z.2
  have hMdiag : M = Matrix.diagonal fun a => c (d4Blk a) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, hMa]
    · rw [hdiag a b hab, Matrix.diagonal_apply_ne _ hab]
  have hprod : (∏ a : Fin 24, c (d4Blk a)) = c 0 ^ 8 * c 1 ^ 8 * c 2 ^ 8 := by
    rw [show (∏ a : Fin 24, c (d4Blk a)) = ∏ p : Fin 3 × Fin 8, c (d4Blk (blkIdx p.1 p.2)) from
      (Fintype.prod_bijective _ blkIdx_bijective _ _ fun _ => rfl).symm]
    simp only [d4Blk_blkIdx, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fin.prod_univ_three]
  rw [← hMdef, hMdiag, Matrix.det_diagonal, hprod] at hdet
  have hc1 : c 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num), mul_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  have hc0 : c 0 ^ 2 = 1 := by
    have : c 1 = c 0 ^ 2 * c 1 := by
      calc c 1 = c 0 * c 2 := h10
        _ = c 0 * (c 0 * c 1) := by rw [h20]
        _ = c 0 ^ 2 * c 1 := by ring
    have h' : (c 0 ^ 2 - 1) * c 1 = 0 := by linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hc1)
  have h0 : c 0 ^ 16 = 1 := by
    rw [show (16 : ℕ) = 2 * 8 from rfl, pow_mul, hc0, one_pow]
  have h1 : c 1 ^ 16 = 1 := by
    rw [h20] at hdet
    have e : c 0 ^ 8 * c 1 ^ 8 * (c 0 * c 1) ^ 8 = c 0 ^ 16 * c 1 ^ 16 := by ring
    rw [e, h0, one_mul] at hdet
    exact hdet
  have hall : ∀ k, c k ^ 16 = 1 := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · change c 2 ^ 16 = 1
      rw [h20, mul_pow, h0, h1, one_mul]
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, ← hMdef, hMdiag, Matrix.diagonal_pow]
  ext a b
  simp only [Pi.pow_apply, hall, Matrix.diagonal_apply, Matrix.one_apply, OneMemClass.coe_one,
    Units.val_one]

theorem card_le_nine_of_graphFixedRootGroup_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ TwistTag.D4.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (F : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  classical
  let q : PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hv : (LieTypeIndex.trialityD4 q).Valid := LieTypeIndex.valid_trialityD4 q
  have hpℓ : d4Char q hv = ℓ := d4Char_eq q hv
  have : CharP K (d4Char q hv) :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (hpℓ ▸ hℓ) (k := f * 3) (by omega) (by rw [hK, hpℓ, pow_mul]; rfl)
  let : Algebra (ZMod (d4Char q hv)) K := ZMod.algebra K (d4Char q hv)
  have : Algebra.IsAlgebraic (ZMod (d4Char q hv)) K :=
    Algebra.IsAlgebraic.of_finite (ZMod (d4Char q hv)) K
  let ι : K →ₐ[ZMod (d4Char q hv)] d4Closure q hv := IsAlgClosed.lift
  let : Algebra K (d4Closure q hv) := ι.toRingHom.toAlgebra
  have : IsScalarTower (ZMod (d4Char q hv)) K (d4Closure q hv) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic K (d4Closure q hv) :=
    Algebra.IsAlgebraic.tower_top (K := ZMod (d4Char q hv)) K
  have : IsAlgClosure K (d4Closure q hv) := ⟨inferInstance, inferInstance⟩
  have hFr : ∀ c, d4Fr q hv c = c ^ (ℓ ^ f) := fun c => by
    rw [d4Fr_apply q hv c, PrimePower.card_def]
  have : CharP (d4Closure q hv) ℓ := hpℓ ▸ inferInstance
  have h2 : (2 : d4Closure q hv) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : d4Closure q hv) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (d4Closure q hv) ℓ] at h0'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h0')
  have h := (d4PushDown (d4Closure q hv)).isTwistedIsogeny_steinberg (q := q) (hv := hv) hℓ2
  have hperf := commutator_derived_eq (d4Closure q hv) (d4Fr q hv) hℓ hf hK hσ hFr
  have hker : ∀ y, h.derivedMap hperf y = 1 →
      y ^ 16 = 1 ∧ y ∈ Subgroup.center ↥(commutator ↥(fixedSubgroup (d4Index q hv).steinberg)) := by
    intro y hy
    have hπ : (d4PushDown (d4Closure q hv)).π
        ((y : ↥(fixedSubgroup (d4Index q hv).steinberg)) : D4Tripled.points (d4Closure q hv)) =
          1 :=
      (h.coe_derivedMap hperf y).symm.trans (congrArg Subtype.val hy)
    refine ⟨Subtype.ext (Subtype.ext ?_), Subgroup.mem_center_iff.2 fun w => ?_⟩
    · simpa using pow_sixteen_eq_one_of_pushDown (d4Closure q hv) h2 _ hπ
    · have hc := Subgroup.mem_center_iff.1 (h.ker _ hπ)
        ((w : ↥(fixedSubgroup (d4Index q hv).steinberg)) : D4Tripled.points (d4Closure q hv))
      exact Subtype.ext (Subtype.ext hc)
  have φ₀ := rootGroupEquivDerived (d4Closure q hv) (d4Fr q hv) hℓ hf hK hσ hFr
  have hE₀3 : ∀ e ∈ F.map φ₀.toMonoidHom, e ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF.2 x hx, map_one]
  have hE₀c : ∀ e ∈ F.map φ₀.toMonoidHom, ∀ e' ∈ F.map φ₀.toMonoidHom, e * e' = e' * e := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hF.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨F', hcard', hF'3, hF'c⟩ := exists_elemAbelian_lift_of_center_pow_sixteen
    (h.derivedMap hperf) (h.derivedMap_surjective hperf) hker _ hE₀3 hE₀c
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hcardE₀ : Nat.card (F.map φ₀.toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective φ₀.injective
  obtain ⟨F'G, hF'G⟩ : ∃ F'G : Subgroup (D4Tripled.points (d4Closure q hv)),
      F'G = (F'.map (commutator ↥(fixedSubgroup (d4Index q hv).steinberg)).subtype).map
        (fixedSubgroup (d4Index q hv).steinberg).subtype := ⟨_, rfl⟩
  have hcardG : Nat.card F'G = Nat.card F' := by
    rw [hF'G, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hmemG : ∀ x ∈ F'G, ∃ y ∈ F', ((y : ↥(fixedSubgroup (d4Index q hv).steinberg)) :
      D4Tripled.points (d4Closure q hv)) = x := by
    rw [hF'G]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  have : Finite F'G :=
    Nat.finite_of_card_ne_zero (by rw [hcardG, hcard', hcardE₀]; exact Nat.card_pos.ne')
  have hF'Gab : CFSG.Assembly.IsElemAbelian 3 F'G := by
    refine ⟨⟨⟨fun x x' => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hmemG x x.2
      obtain ⟨y', hy', hyx'⟩ := hmemG x' x'.2
      change (x : D4Tripled.points (d4Closure q hv)) * x' = x' * x
      rw [← hyx, ← hyx']
      exact congrArg (fun w : ↥(commutator ↥(fixedSubgroup (d4Index q hv).steinberg)) =>
        ((w : ↥(fixedSubgroup (d4Index q hv).steinberg)) : D4Tripled.points (d4Closure q hv)))
        (hF'c _ hy _ hy')
    · obtain ⟨y, hy, rfl⟩ := hmemG x hx
      exact congrArg (fun w : ↥(commutator ↥(fixedSubgroup (d4Index q hv).steinberg)) =>
        ((w : ↥(fixedSubgroup (d4Index q hv).steinberg)) : D4Tripled.points (d4Closure q hv)))
        (hF'3 y hy)
  have hfixG : ∀ g ∈ F'G, (d4Index q hv).steinberg g = g := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := hmemG g hg
    exact mem_fixedSubgroup.1 (y : ↥(fixedSubgroup (d4Index q hv).steinberg)).2
  have h9 := card_le_nine_of_fixedPoints_of_ne_three (q := q) (hv := hv) hℓ3 F'G hF'Gab hfixG
  rwa [hcardG, hcard', hcardE₀] at h9

end Kernel

section Cat


theorem card_le_nine_of_graphFixedRootGroup_ne_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ TwistTag.D4.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (F : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  by_cases h2 : ℓ = 2
  · subst h2
    exact card_le_nine_of_graphFixedRootGroup hf hK hσ F hF
  · exact card_le_nine_of_graphFixedRootGroup_odd hℓ h2 hℓ3 hf hK hσ F hF


theorem rankLE2_three_cat_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq3 : q.p ≠ 3) :
    RankLE2 3 (Cat ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  refine RankLE2.of_mulEquiv e.symm fun F hF => ?_
  exact (card_le_nine_of_graphFixedRootGroup_ne_three q.prime_p hq3 q.exponent_pos hK hσ F
    ⟨hF.1, hF.2⟩).trans (by norm_num)

end Cat

end CFSG.HardMathSupport.Timmesfeld.CrossChar
