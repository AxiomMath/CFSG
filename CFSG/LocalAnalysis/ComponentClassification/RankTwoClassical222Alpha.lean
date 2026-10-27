module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCJ

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.of_eq_mul_scalar {x : G} {X Y : GL ι K} (hX : Represents e x X) (hY : Y ∈ H)
    {c : Kˣ} (hc : X = Y * Matrix.GeneralLinearGroup.scalar ι c) : Represents e x Y := by
  obtain ⟨hxA, hXH, hx⟩ := hX
  refine ⟨hxA, hY, hx.trans ?_⟩
  rw [QuotientGroup.eq, mem_subgroupOf]
  refine ⟨c⁻¹, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, _root_.mul_inv_rev, map_inv,
    inv_mul_cancel_right]

theorem deltaCentral_alpha_of [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hp2 : p ^ 2 = 1) {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hkey : ∀ X ∈ H, X * M = M * X →
      (∀ g ∈ H, g * M * g⁻¹ * M = M * (g * M * g⁻¹) → X * (g * M * g⁻¹) = g * M * g⁻¹ * X) →
      ∃ Y ∈ H, (∃ c : Kˣ, X = Y * Matrix.GeneralLinearGroup.scalar ι c) ∧
        ∃ a : K, (Y : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)) :
    DeltaCentral A p (alphaGroup e p) := by
  intro x hx hxΔ hx2
  obtain ⟨hxA, hxp⟩ := mem_inf.mp hx
  have hxp' : x * p = p * x := mem_centralizer_singleton_iff.mp hxp
  obtain ⟨X, hX⟩ := exists_represents e hxA
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hXM : X * M = M * X := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hX.mul_comm_of_commute hpM hM2' hxp')
  obtain ⟨Y, hYH, ⟨c, hc⟩, a, ha⟩ := hkey X hX.2.1 hXM fun g hg hgM => by
    obtain ⟨b, hb⟩ := exists_represents_of_mem (e := e) hg
    have hrep := hpM.conj hb
    have hb2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
    have hcomm : p * (b * p * b⁻¹) = b * p * b⁻¹ * p :=
      commute_of_represents hZ hpM hrep hb2 hgM.symm
    have hmem : b * p * b⁻¹ ∈ conjCommuting A p := ⟨b, hb.1, rfl, hcomm.symm⟩
    have hxc : b * p * b⁻¹ * x = x * (b * p * b⁻¹) := mem_centralizer_iff.mp hxΔ _ hmem
    have hgM2 : (g * M * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hM2', mul_one, mul_inv_cancel]
    exact Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hX.mul_comm_of_commute hrep hgM2 hxc.symm)
  exact subset_closure ⟨hx2, M, Y, hpM, hM2, hX.of_eq_mul_scalar hYH hc, a, ha⟩

section Aut

variable [CharP K 2] {F : Type} [Field F] [Finite F] (ιF : F →+* K) {M : GL ι K}
  (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0) {φ : Multiplicative F →* G}

@[expose] def ActsByScalar (φ : Multiplicative F →* G) (a : G) (l : F) : Prop :=
  ∀ t : F, a * φ (Multiplicative.ofAdd t) * a⁻¹ = φ (Multiplicative.ofAdd (l * t))

variable {ιF hE}

omit [Finite F] in
theorem ActsByScalar.mul {a b : G} {l l' : F} (ha : ActsByScalar φ a l) (hb : ActsByScalar φ b l') :
    ActsByScalar φ (a * b) (l * l') := fun t => by
  rw [_root_.mul_inv_rev, show a * b * φ (Multiplicative.ofAdd t) * (b⁻¹ * a⁻¹) =
    a * (b * φ (Multiplicative.ofAdd t) * b⁻¹) * a⁻¹ by group, hb, ha, mul_assoc]

omit [Finite F] in
theorem ActsByScalar.inv {a : G} {l : F} (hl : l ≠ 0) (ha : ActsByScalar φ a l) :
    ActsByScalar φ a⁻¹ l⁻¹ := fun t => by
  have h := ha (l⁻¹ * t)
  rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul] at h
  rw [inv_inv, ← h]
  group

omit [Finite F] in
theorem ActsByScalar.eq {a : G} {l l' : F} (hφ : Function.Injective φ) (ha : ActsByScalar φ a l)
    (ha' : ActsByScalar φ a l') : l = l' := by
  have h := (ha 1).symm.trans (ha' 1)
  have h1 := hφ h
  rw [mul_one, mul_one] at h1
  exact h1

omit [CharP K 2] [Finite F] in
theorem actsByScalar_of_conj (hZ : Odd (Nat.card (center ↥A)))
    (hφ : ∀ t : F, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
      Represents e (φ (Multiplicative.ofAdd t)) (unipGL ((M : Matrix ι ι K) - 1) hE (ιF t)))
    {a : G} {X : GL ι K} (ha : Represents e a X) {l : F}
    (hX : (X : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
      ιF l • ((M : Matrix ι ι K) - 1)) : ActsByScalar φ a l := fun t => by
  have h1 : Represents e (a * φ (Multiplicative.ofAdd t) * a⁻¹)
      (unipGL ((M : Matrix ι ι K) - 1) hE (ιF (l * t))) := by
    have h := (hφ t).2.conj ha
    have heq : X * unipGL ((M : Matrix ι ι K) - 1) hE (ιF t) * X⁻¹ =
        unipGL ((M : Matrix ι ι K) - 1) hE (ιF (l * t)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, Matrix.mul_add, Matrix.mul_one,
        Matrix.add_mul, Units.mul_inv, Matrix.mul_smul, Matrix.smul_mul, hX, smul_smul, map_mul,
        mul_comm (ιF t)]
    rwa [heq] at h
  have h2 : (a * φ (Multiplicative.ofAdd t) * a⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, conj_pow, (hφ t).1, mul_one, mul_inv_cancel]
  exact eq_of_represents hZ h1 (hφ (l * t)).2 h2 (k' := 1) (by rw [pow_one]; exact (hφ (l * t)).1)

omit [Finite F] in
theorem exists_actsByScalar_of_mem_normalizer (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hM2 : orderOf M = 2) (hinj : Function.Injective φ) (hrange : φ.range = alphaGroup e p)
    (hφ : ∀ t : F, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
      Represents e (φ (Multiplicative.ofAdd t)) (unipGL ((M : Matrix ι ι K) - 1) hE (ιF t)))
    {a : G} (haA : a ∈ A) (han : a ∈ normalizer (alphaGroup e p : Set G)) :
    ∃ l : F, l ≠ 0 ∧ ActsByScalar φ a l := by
  classical
  obtain ⟨X, hX⟩ := exists_represents e haA
  have hφ1 : φ (Multiplicative.ofAdd 1) ∈ alphaGroup e p := hrange ▸ ⟨_, rfl⟩
  have hmem : a * φ (Multiplicative.ofAdd 1) * a⁻¹ ∈ alphaGroup e p :=
    (mem_normalizer_iff.mp han _).mp hφ1
  rw [← hrange] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hne : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    have hM1 : M = 1 := Units.ext (Subsingleton.elim _ _)
    rw [hM1, orderOf_one] at hM2
    omega
  have h1 := (hφ 1).2.conj hX
  have h2 := (hφ (Multiplicative.toAdd s)).2
  rw [ofAdd_toAdd, hs] at h2
  obtain ⟨c, hc⟩ := h1.exists_scalar h2
  set U := X * unipGL ((M : Matrix ι ι K) - 1) hE (ιF 1) * X⁻¹ with hU
  have hU2 : U ^ 2 = 1 := by rw [hU, conj_pow, unipGL_sq, mul_one, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := by
    have h3 : (unipGL ((M : Matrix ι ι K) - 1) hE (ιF (Multiplicative.toAdd s))) ^ 2 = 1 :=
      unipGL_sq _ _
    have hcomm : Commute U (Matrix.GeneralLinearGroup.scalar ι c) :=
      (Matrix.GeneralLinearGroup.scalar_commute c U).symm
    rw [hc, hcomm.mul_pow, hU2, one_mul, ← map_pow] at h3
    apply Units.ext
    have h4 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) h3
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h4
    have h5 : Matrix.scalar ι ((c ^ 2 : Kˣ) : K) = Matrix.scalar ι (1 : K) := by
      rw [h4]; exact (Matrix.scalar_apply (1 : K)).trans Matrix.diagonal_one |>.symm
    rw [Matrix.scalar_inj] at h5
    exact h5
  have hc1 : c = 1 := by
    have h3 : ((c : K) - 1) ^ 2 = 0 := by
      have h4 := congrArg Units.val hc2
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h4
      rw [sub_sq, h4, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
        CharTwo.add_self_eq_zero]
    exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
  rw [hc1, map_one, mul_one] at hc
  have hXN : (X : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
      ιF (Multiplicative.toAdd s) • ((M : Matrix ι ι K) - 1) := by
    have h3 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
    simp only [hU, Units.val_mul, coe_unipGL, map_one, one_smul, Matrix.mul_add, Matrix.mul_one,
      Matrix.add_mul, Units.mul_inv] at h3
    exact add_left_cancel h3.symm
  refine ⟨Multiplicative.toAdd s, fun h0 => ?_, actsByScalar_of_conj hZ hφ hX hXN⟩
  have h3 : s = 1 := by rw [← ofAdd_toAdd s, h0, ofAdd_zero]
  rw [h3, map_one] at hs
  have h4 : φ (Multiplicative.ofAdd 1) = 1 := by
    calc φ (Multiplicative.ofAdd 1) = a⁻¹ * (a * φ (Multiplicative.ofAdd 1) * a⁻¹) * a := by
          group
      _ = 1 := by rw [← hs]; group
  have h5 := hinj (h4.trans (map_one φ).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd h5)

theorem regularOn_autCyclic_alpha_of [Finite G] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hM2 : orderOf M = 2) (hinj : Function.Injective φ) (hrange : φ.range = alphaGroup e p)
    (hφ : ∀ t : F, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
      Represents e (φ (Multiplicative.ofAdd t)) (unipGL ((M : Matrix ι ι K) - 1) hE (ιF t)))
    (htorus : ∀ l : F, l ≠ 0 → ∃ d ∈ H,
      (d : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((d⁻¹ : GL ι K) : Matrix ι ι K) =
        ιF l • ((M : Matrix ι ι K) - 1)) :
    RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (Nat.card F - 1) := by
  classical
  set α := alphaGroup e p with hαdef
  have hmemα : ∀ y, y ∈ α ↔ ∃ t : F, y = φ (Multiplicative.ofAdd t) := fun y => by
    rw [← hrange]
    exact ⟨fun ⟨s, hs⟩ => ⟨Multiplicative.toAdd s, by rw [ofAdd_toAdd, hs]⟩,
      fun ⟨t, ht⟩ => ⟨_, ht.symm⟩⟩
  have hφ0 : ∀ t : F, φ (Multiplicative.ofAdd t) = 1 → t = 0 := fun t h => by
    have h1 := hinj (h.trans (map_one φ).symm)
    exact congrArg Multiplicative.toAdd h1
  have hnorm : ∀ {a : G} {l : F}, l ≠ 0 → ActsByScalar φ a l → a ∈ normalizer (α : Set G) :=
    fun {a l} hl ha => mem_normalizer_iff.mpr fun y => by
      rw [hmemα, hmemα]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨l * t, ha t⟩
      · rintro ⟨s, hs⟩
        refine ⟨l⁻¹ * s, ?_⟩
        have h1 := (ha.inv hl) s
        rw [inv_inv] at h1
        rw [← h1, ← hs]
        group
  have hlift : ∀ l : F, l ≠ 0 → ∃ a ∈ A, ActsByScalar φ a l := fun l hl => by
    obtain ⟨d, hdH, hd⟩ := htorus l hl
    obtain ⟨a, ha⟩ := exists_represents_of_mem (e := e) hdH
    exact ⟨a, ha.1, actsByScalar_of_conj hZ hφ ha hd⟩
  have hcent : ∀ {a : G} {l : F}, ActsByScalar φ a l → (a ∈ centralizer (α : Set G) ↔ l = 1) :=
    fun {a l} ha => by
      constructor
      · intro hc
        have h1 := mem_centralizer_iff.mp hc (φ (Multiplicative.ofAdd 1))
          ((hmemα _).mpr ⟨1, rfl⟩)
        have h2 : a * φ (Multiplicative.ofAdd 1) * a⁻¹ = φ (Multiplicative.ofAdd 1) := by
          rw [← h1]; group
        rw [ha 1, mul_one] at h2
        have h3 := hinj h2
        exact congrArg Multiplicative.toAdd h3
      · rintro rfl
        refine mem_centralizer_iff.mpr fun y hy => ?_
        obtain ⟨t, rfl⟩ := (hmemα y).mp hy
        have h1 := ha t
        rw [one_mul] at h1
        calc φ (Multiplicative.ofAdd t) * a =
            a * φ (Multiplicative.ofAdd t) * a⁻¹ * a := by rw [h1]
          _ = a * φ (Multiplicative.ofAdd t) := by group
  have hscal : ∀ a : ↥(A ⊓ normalizer (α : Set G)), ∃ l : F, l ≠ 0 ∧ ActsByScalar φ a l :=
    fun a => exists_actsByScalar_of_mem_normalizer hZ hM2 hinj hrange hφ (mem_inf.mp a.2).1
      (mem_inf.mp a.2).2
  choose μ hμ0 hμ using hscal
  have hμmul : ∀ a b, μ (a * b) = μ a * μ b := fun a b =>
    ActsByScalar.eq hinj (hμ (a * b)) ((hμ a).mul (hμ b))
  let μu : ↥(A ⊓ normalizer (α : Set G)) →* Fˣ :=
    { toFun := fun a => Units.mk0 (μ a) (hμ0 a)
      map_one' := Units.ext (ActsByScalar.eq hinj (hμ 1) fun t => by simp)
      map_mul' := fun a b => Units.ext (hμmul a b) }
  have hμu : ∀ a, ((μu a : Fˣ) : F) = μ a := fun _ => rfl
  refine ⟨⟨fun j hj j' hj' => ?_, fun a ha j hj haj => ?_⟩, ?_, ?_⟩
  · obtain ⟨t, rfl⟩ := (hmemα j).mp hj.1
    obtain ⟨t', rfl⟩ := (hmemα j').mp hj'.1
    have ht : t ≠ 0 := fun h => hj.2 (by rw [h, ofAdd_zero, map_one])
    have ht' : t' ≠ 0 := fun h => hj'.2 (by rw [h, ofAdd_zero, map_one])
    obtain ⟨a, haA, ha⟩ := hlift (t' * t⁻¹) (mul_ne_zero ht' (inv_ne_zero ht))
    refine ⟨a, mem_inf.mpr ⟨haA, hnorm (mul_ne_zero ht' (inv_ne_zero ht)) ha⟩, ?_⟩
    rw [ha t, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  · obtain ⟨t, rfl⟩ := (hmemα j).mp hj.1
    have ht : t ≠ 0 := fun h => hj.2 (by rw [h, ofAdd_zero, map_one])
    have h1 := hμ ⟨a, ha⟩
    rw [h1 t] at haj
    have h2 := hinj haj
    have h3 : μ ⟨a, ha⟩ * t = 1 * t := by rw [one_mul]; exact congrArg Multiplicative.toAdd h2
    exact (hcent h1).mpr (mul_right_cancel₀ ht h3)
  · have hker : (A ⊓ centralizer (α : Set G)).subgroupOf (A ⊓ normalizer (α : Set G)) =
        μu.ker := by
      ext a
      rw [mem_subgroupOf, MonoidHom.mem_ker, Units.ext_iff, hμu, Units.val_one, mem_inf]
      exact ⟨fun h => ((hcent (hμ a)).mp h.2), fun h => ⟨(mem_inf.mp a.2).1, (hcent (hμ a)).mpr h⟩⟩
    have hsurj : Function.Surjective μu := fun l => by
      obtain ⟨a, haA, ha⟩ := hlift (l : F) l.ne_zero
      refine ⟨⟨a, mem_inf.mpr ⟨haA, hnorm l.ne_zero ha⟩⟩, Units.ext ?_⟩
      rw [hμu]
      exact ActsByScalar.eq hinj (hμ _) ha
    rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, Nat.card_units]
  · have hpow : ∀ {a : G} {l : F}, ActsByScalar φ a l → ∀ k : ℕ, ActsByScalar φ (a ^ k) (l ^ k) :=
      fun {a l} ha k => by
        induction k with
        | zero => exact fun t => by simp
        | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul ha
    have hodd : Odd (Nat.card Fˣ) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
      have hx2 : (ιF (x : F) - 1) ^ 2 = 0 := by
        have h1 : (x : F) ^ 2 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
        rw [sub_sq, ← map_pow, h1, map_one, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero,
          one_pow, CharTwo.add_self_eq_zero]
      have hx1 : x = 1 := Units.ext (ιF.injective (by
        rw [Units.val_one, map_one]
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hx2)))
      rw [hx1, orderOf_one] at hx
      omega
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hgo : orderOf g = Nat.card Fˣ := by
      rw [← Nat.card_zpowers]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv hg)
    obtain ⟨a₀, ha₀A, ha₀⟩ := hlift (g : F) g.ne_zero
    obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a₀).ne'
    refine ⟨a₀ ^ 2 ^ s, mem_inf.mpr ⟨pow_mem ha₀A _, hnorm (pow_ne_zero _ g.ne_zero)
      (hpow ha₀ _)⟩, ?_, fun a ha => ?_⟩
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨r, hsr⟩, hsr,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hr
    have hgen : Subgroup.zpowers (g ^ 2 ^ s) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, Nat.Coprime.orderOf_pow, hgo]
      rw [hgo]
      exact Nat.Coprime.pow_right _ hodd.coprime_two_right
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (y := μu ⟨a, ha⟩)).mpr (by
      rw [hgen]; exact mem_top _)
    refine ⟨k, ?_⟩
    have h1 := ((hpow (hpow ha₀ (2 ^ s)) k).inv (pow_ne_zero _ (pow_ne_zero _ g.ne_zero))).mul
      (hμ ⟨a, ha⟩)
    refine (hcent h1).mpr ?_
    rw [← hμu, ← hk, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ g.ne_zero))]

end Aut

end CFSG.ComponentClassification.RankTwoClassical
