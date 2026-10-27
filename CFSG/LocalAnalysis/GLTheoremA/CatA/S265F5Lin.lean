module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5LinBlk
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {k : Type} [Field k] [Finite k]

theorem card_le_mul_card_inf_linear {ℓ f n p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP k ℓ] (hK : Nat.card k = ℓ ^ f)
    {B : Subgroup (MulAut (projectiveSL n k))} (hB : ∀ b ∈ B, b ^ p = 1) :
    Nat.card B ≤ p * Nat.card (B ⊓ linearAutGroup n k : Subgroup _) := by
  classical
  obtain ⟨-, -, -, -, -, hnorm, -, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  haveI := hnorm
  let π : MulAut (projectiveSL n k) →* MulAut (projectiveSL n k) ⧸ linearAutGroup n k :=
    QuotientGroup.mk' (linearAutGroup n k)
  let φ : B →* MulAut (projectiveSL n k) ⧸ linearAutGroup n k := π.comp B.subtype
  have hker : Nat.card φ.ker = Nat.card (B ⊓ linearAutGroup n k : Subgroup _) := by
    have h1 : φ.ker = (linearAutGroup n k).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    rw [h1, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  haveI : IsCyclic (k ≃+* k) := by
    obtain ⟨σ₀, -, -, htop, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩
  let ψ : (k ≃+* k) →* MulAut (projectiveSL n k) ⧸ linearAutGroup n k := π.comp (fieldAut n k)
  haveI : IsCyclic ψ.range := isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hle : φ.range ≤ ψ.range := by
    rintro _ ⟨b, rfl⟩
    have hb : (b : MulAut (projectiveSL n k)) ∈ semilinearAutGroup n k :=
      LinearFlag.mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) (hB b b.2)
    obtain ⟨A, τ, hAτ⟩ := mem_semilinearAutGroup_iff.1 hb
    refine ⟨τ, ?_⟩
    show π (fieldAut n k τ) = π b
    have hA1 : π (LinearFlag.conjAut n k A) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_linearAutGroup_iff.2 ⟨A, rfl⟩)
    rw [hAτ, map_mul, hA1, one_mul]
  haveI : IsCyclic φ.range := Subgroup.isCyclic_of_le hle
  have hrange : Nat.card φ.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
    apply Subtype.ext
    show φ b ^ p = 1
    rw [← map_pow, show b ^ p = 1 from Subtype.ext (hB b b.2), map_one]
  rw [← Subgroup.card_ker_mul_card_range φ, hker, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos hrange)

theorem glaPLayer_ne_bot_of_fieldAut_conjAut_prime [CharP k 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : k ≃+* k} (hpk₀ : p ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {M : GL (Fin p) k} (hM1 : LinearFlag.conjAut p k M ≠ 1)
    (hMp : LinearFlag.conjAut p k M ^ p = 1)
    (hcomm : fieldAut p k σ * LinearFlag.conjAut p k M = LinearFlag.conjAut p k M * fieldAut p k σ)
    {t : projectiveSL p k} (ht : orderOf t = 2) (hfix : LinearFlag.conjAut p k M t = t) :
    GLAPLayer p (fixSubgroup (fieldAut p k σ) ⊓ fixSubgroup (LinearFlag.conjAut p k M)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set k₀ := semilinearFixedSubfield σ with hk₀def
  have hσk₀ : ∀ c ∈ k₀, σ c = c := fun c hc => RingHom.mem_eqLocusField.mp hc
  have htr := (LinearFlag.standard_automorphism_transport (K := k) (n := p)).2.2.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hn : p < 2 * p := by
    have := hp.pos
    omega
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨U, hUt, hU2⟩ := exists_lift_sq_eq_one_of_odd hpodd ht2
  set u := Matrix.SpecialLinearGroup.toGL U with hu
  have hu1 : u ≠ 1 := by
    intro h
    have hU : U = 1 := Matrix.SpecialLinearGroup.toGL_injective (by rw [← hu, h, map_one])
    rw [hU, map_one] at hUt
    rw [← hUt, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, ← sq, hU2, map_one]
  have hMu : M * u = u * M := mul_comm_of_conjAut_proj_eq_of_odd hpodd hU2 (by rw [hUt]; exact hfix)
  obtain ⟨a, ha⟩ := KD264Lie.exists_eq_scalar_of_conjAut_eq_one (n := p) hp.two_le
    (show LinearFlag.conjAut p k (M ^ p) = 1 by rw [map_pow, hMp])
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_comm_involution hp hn hu1 hu2 hMu ha
  set M' := GeneralLinearGroup.scalar (Fin p) μ⁻¹ * M with hM'
  have hM'p : M' ^ p = 1 := by
    rw [hM', CFSG.HardMathSupport.Timmesfeld.CrossChar.scalar_mul_pow, ha, ← map_mul, inv_pow, hμ,
      inv_mul_cancel, map_one]
  have hcM' : LinearFlag.conjAut p k M' = LinearFlag.conjAut p k M := by
    rw [hM', map_mul, LinearFlag.conjAut_scalar, one_mul]
  have hM'u : M' * u = u * M' := by
    rw [hM', mul_assoc, hMu, ← mul_assoc, ← mul_assoc, GeneralLinearGroup.scalar_commute μ⁻¹ u]
  have hM'1 : LinearFlag.conjAut p k M' ≠ 1 := by rwa [hcM']
  have hσc : LinearFlag.conjAut p k (GeneralLinearGroup.map (σ : k →+* k) M') =
      LinearFlag.conjAut p k M' := by
    rw [← htr σ M', hcM', hcomm, mul_inv_cancel_right]
  obtain ⟨lam, hlam⟩ := KD264Lie.exists_eq_scalar_of_conjAut_eq_one (n := p) hp.two_le
    (show LinearFlag.conjAut p k (M'⁻¹ * GeneralLinearGroup.map (σ : k →+* k) M') = 1 by
      rw [map_mul, map_inv, hσc, inv_mul_cancel])
  have hσM : GeneralLinearGroup.map (σ : k →+* k) M' =
      M' * GeneralLinearGroup.scalar (Fin p) lam := by
    rw [← hlam, mul_inv_cancel_left]
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd (F := k₀) hp hpk₀
  have hζk : IsPrimitiveRoot (ζ : k) p := hζ.map_of_injective k₀.subtype.injective
  have hμp : ∀ x : k, x ^ p = 1 → σ x = x := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := hζk.eq_pow_of_pow_eq_one hx
    rw [map_pow, hσk₀ _ ζ.2]
  have hlam1 : lam = 1 := eq_one_of_map_eq_mul_scalar hp hn hζk hμp hu1 hu2 hM'u hM'p hσM
  have hσM' : GeneralLinearGroup.map (σ : k →+* k) M' = M' := by
    rw [hσM, hlam1, map_one, mul_one]
  have hmem : ∀ i j, (M' : Matrix (Fin p) (Fin p) k) i j ∈ k₀ := by
    intro i j
    have := congrArg (fun g : GL (Fin p) k => (g : Matrix (Fin p) (Fin p) k) i j) hσM'
    simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom] at this
    exact RingHom.mem_eqLocusField.mpr this
  obtain ⟨M₀, hM₀⟩ := exists_gl_subfield_eq hmem
  have hM₀p : M₀ ^ p = 1 := map_subtype_injective k₀ (by rw [map_pow, hM₀, hM'p, map_one])
  obtain ⟨R, d₀, hR⟩ := exists_conj_eq_diagonal_of_pow_eq_one hp hζ hM₀p
  set Q := GeneralLinearGroup.map k₀.subtype R with hQ
  have hQdiag : ((Q * M' * Q⁻¹ : GL (Fin p) k) : Matrix (Fin p) (Fin p) k) =
      diagonal (fun l => (d₀ l : k)) := by
    rw [hQ, ← hM₀, ← map_inv, ← map_mul, ← map_mul]
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hR]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  obtain ⟨a, a', hda, haa'⟩ := Function.not_injective_iff.1
    (not_injective_of_conj_eq_diagonal hu1 hu2 hM'u hQdiag)
  have hd0p : ∀ l, (d₀ l : k) ^ p = 1 := diagonal_pow_eq_one hM'p hQdiag
  obtain ⟨c, hdc⟩ : ∃ c, (d₀ c : k) ≠ d₀ a := by
    by_contra hcon
    have hcon' : ∀ l, (d₀ l : k) = d₀ a := fun l => by_contra fun h => hcon ⟨l, h⟩
    apply hM'1
    have hda0 : (d₀ a : k) ≠ 0 := by
      intro h0
      have h1 := hd0p a
      rw [h0, zero_pow hp.ne_zero] at h1
      exact zero_ne_one h1
    have hsc : Q * M' * Q⁻¹ = GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ hda0) := by
      apply Units.ext
      rw [hQdiag, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      congr 1
      funext l
      exact hcon' l
    have hM'sc : M' = GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ hda0) := by
      calc M' = Q⁻¹ * (Q * M' * Q⁻¹) * Q := by group
        _ = _ := by rw [hsc, ← GeneralLinearGroup.scalar_commute _ Q⁻¹, inv_mul_cancel_right]
    rw [hM'sc, LinearFlag.conjAut_scalar]
  have hcore := glaPLayer_ne_bot_of_diagonal_block hp hp2 hpk₀ hQdiag haa' hda hdc
  have hσQ : GeneralLinearGroup.map (σ : k →+* k) Q = Q := by
    ext i j
    simp only [hQ, Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom]
    exact hσk₀ _ ((R : Matrix (Fin p) (Fin p) k₀) i j).2
  have hfconj : LinearFlag.conjAut p k Q * fieldAut p k σ * (LinearFlag.conjAut p k Q)⁻¹ =
      fieldAut p k σ := by
    calc LinearFlag.conjAut p k Q * fieldAut p k σ * (LinearFlag.conjAut p k Q)⁻¹
        = (fieldAut p k σ * LinearFlag.conjAut p k Q * (fieldAut p k σ)⁻¹) * fieldAut p k σ *
            (LinearFlag.conjAut p k Q)⁻¹ := by rw [htr σ Q, hσQ]
      _ = fieldAut p k σ := by group
  have hcX : LinearFlag.conjAut p k (Q * M' * Q⁻¹) = LinearFlag.conjAut p k Q *
      LinearFlag.conjAut p k M * (LinearFlag.conjAut p k Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hcM']
  apply HDescLinRes.glaPLayer_ne_bot_of_conj hp (LinearFlag.conjAut p k Q)
  rw [hfconj, ← hcX]
  exact hcore

theorem glaPLayer_ne_bot_of_field_linear_prime [CharP k 2] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he1 : 1 ≤ e) (hK : Nat.card k = 2 ^ e) (hpe : p ∣ 2 ^ (e / p) - 1)
    {x c : MulAut (projectiveSL p k)} (hxp : x ^ p = 1) (hxL : x ∉ linearAutGroup p k)
    (hcL : c ∈ linearAutGroup p k) (hc1 : c ≠ 1) (hcp : c ^ p = 1) (hcomm : x * c = c * x)
    {t : projectiveSL p k} (ht : orderOf t = 2) (hct : c t = t) :
    GLAPLayer p (fixSubgroup x ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨-, -, -, -, -, -, -, hord⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two he1
      hp3 hK
  have hxo : orderOf x = p := orderOf_eq_prime hxp (fun h => hxL (h ▸ Subgroup.one_mem _))
  obtain ⟨-, σ, -, ⟨h, hhL, hxh⟩, hk₀⟩ := hord p hp hp2 x
    (LinearFlag.mem_semilinearAutGroup_of_pow_odd hp3 (hp.odd_of_ne_two hp2) hxp) hxL hxo
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.1 hhL
  obtain ⟨M, rfl⟩ := mem_linearAutGroup_iff.1 hcL
  set g := LinearFlag.conjAut p k H with hg
  set M' := H⁻¹ * M * H with hM'
  have hcM' : LinearFlag.conjAut p k M' = g⁻¹ * LinearFlag.conjAut p k M * g := by
    rw [hM', map_mul, map_mul, map_inv]
  have hfσ : fieldAut p k σ = g⁻¹ * x * g := by
    rw [hxh]
    group
  have hpk₀ : p ∣ Nat.card (semilinearFixedSubfield σ) - 1 := by
    rw [hk₀]
    exact hpe
  have hM1 : LinearFlag.conjAut p k M' ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1
    calc LinearFlag.conjAut p k M = g * (g⁻¹ * LinearFlag.conjAut p k M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hMp : LinearFlag.conjAut p k M' ^ p = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := LinearFlag.conjAut p k M) (i := p)
    rw [inv_inv] at this
    rw [this, hcp]
    group
  have hcomm' : fieldAut p k σ * LinearFlag.conjAut p k M' =
      LinearFlag.conjAut p k M' * fieldAut p k σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * LinearFlag.conjAut p k M * g)
        = g⁻¹ * (x * LinearFlag.conjAut p k M) * g := by group
      _ = g⁻¹ * (LinearFlag.conjAut p k M * x) * g := by rw [hcomm]
      _ = g⁻¹ * LinearFlag.conjAut p k M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 :=
    (orderOf_injective (g⁻¹ : MulAut (projectiveSL p k)).toMonoidHom (MulEquiv.injective _) t).trans
      ht
  have hfix' : LinearFlag.conjAut p k M' (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldAut_conjAut_prime hp hp2 hpk₀ hM1 hMp hcomm' ht' hfix'
  apply HDescLinRes.glaPLayer_ne_bot_of_conj hp g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = fieldAut p k σ by rw [hfσ, inv_inv],
    show g⁻¹ * LinearFlag.conjAut p k M * g⁻¹⁻¹ = LinearFlag.conjAut p k M' by rw [hcM', inv_inv]]
  exact hred

theorem exists_layer_of_linear_model_prime {T : Type} [Group T] [Finite T] [CharP k 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he1 : 1 ≤ e) (hK : Nat.card k = 2 ^ e)
    (hpe : p ∣ 2 ^ (e / p) - 1) (eT : T ≃* projectiveSL p k) {β : MulAut T} (hβp : β ^ p = 1)
    (hβL : MulAut.congr eT β ∉ linearAutGroup p k)
    (Eb : Subgroup (MulAut T)) (hEp : ∀ c ∈ Eb, c ^ p = 1)
    (hEcomm : ∀ c ∈ Eb, β * c = c * β) (hpE : p ^ 2 ≤ Nat.card Eb) {t : T} (ht : orderOf t = 2)
    (hEt : ∀ c ∈ Eb, c t = t) :
    ∃ c ∈ Eb, c ∉ Subgroup.zpowers β ∧ GLAPLayer p (fixSubgroup β ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut (projectiveSL p k)) :=
    Finite.of_injective (fun (g : MulAut (projectiveSL p k)) (w : projectiveSL p k) => g w)
      (fun g h hgh => MulEquiv.ext (congrFun hgh))
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hφinj : Function.Injective (MulAut.congr eT).toMonoidHom := (MulAut.congr eT).injective
  have hcard' : Nat.card (Eb.map (MulAut.congr eT).toMonoidHom) = Nat.card Eb :=
    Subgroup.card_map_of_injective hφinj
  have hEp' : ∀ c ∈ Eb.map (MulAut.congr eT).toMonoidHom, c ^ p = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hEp c hc, map_one]
  have hbound := card_le_mul_card_inf_linear Nat.prime_two he1 hp3 hp hp2 hK
    (B := Eb.map (MulAut.congr eT).toMonoidHom) hEp'
  have hne : (Eb.map (MulAut.congr eT).toMonoidHom ⊓ linearAutGroup p k :
      Subgroup (MulAut (projectiveSL p k))) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, hcard'] at hbound
    have h2 : p * p ≤ p * 1 := by
      rw [← sq]
      exact hpE.trans hbound
    have h3 := Nat.le_of_mul_le_mul_left h2 hp.pos
    have h4 := hp.one_lt
    omega
  obtain ⟨⟨c', hc'⟩, hc'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hc'E, hc'L⟩ := Subgroup.mem_inf.1 hc'
  obtain ⟨c, hcE, rfl⟩ := hc'E
  have hcL : MulAut.congr eT c ∈ linearAutGroup p k := hc'L
  have hc1 : MulAut.congr eT c ≠ 1 := fun h => hc'1 (Subtype.ext h)
  have hxp : MulAut.congr eT β ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hcp : MulAut.congr eT c ^ p = 1 := by rw [← map_pow, hEp c hcE, map_one]
  have hxc : MulAut.congr eT β * MulAut.congr eT c = MulAut.congr eT c * MulAut.congr eT β := by
    rw [← map_mul, ← map_mul, hEcomm c hcE]
  have hxo : Nat.card (Subgroup.zpowers (MulAut.congr eT β)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp (fun h => hβL (h ▸ Subgroup.one_mem _))
  have hxL := CFSG.LocalAnalysis.GLTheoremA.S265.s265_inf_zpowers_bot hp hxo hβL
  refine ⟨c, hcE, ?_, ?_⟩
  · intro hcβ
    apply hc1
    have hmem : MulAut.congr eT c ∈
        (linearAutGroup p k ⊓ Subgroup.zpowers (MulAut.congr eT β) : Subgroup _) := by
      refine Subgroup.mem_inf.2 ⟨hcL, ?_⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcβ
      exact Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow (MulAut.congr eT) β i).symm⟩
    rw [hxL] at hmem
    exact Subgroup.mem_bot.1 hmem
  · apply S265F3.glaPLayer_ne_bot_of_congr hp eT
    have ht' : orderOf (eT t) = 2 := (orderOf_injective eT.toMonoidHom eT.injective t).trans ht
    have hct : MulAut.congr eT c (eT t) = eT t := by
      show eT (c (eT.symm (eT t))) = eT t
      rw [MulEquiv.symm_apply_apply, hEt c hcE]
    exact glaPLayer_ne_bot_of_field_linear_prime hp hp2 he1 hK hpe hxp hβL hcL hc1 hcp hxc ht' hct

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
