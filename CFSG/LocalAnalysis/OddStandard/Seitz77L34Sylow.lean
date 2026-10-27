module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sylow
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.Seitz77.L34

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

@[expose] def ofCoords (a b c : F4) : ↥(unipAll F4) := ⟨unipU F4 a b c, a, b, c, rfl⟩

theorem coe_ofCoords (a b c : F4) : (ofCoords a b c : SpecialLinearGroup (Fin 3) F4) =
    unipU F4 a b c := rfl

theorem exists_ofCoords (x : ↥(unipAll F4)) : ∃ a b c, x = ofCoords a b c := by
  obtain ⟨a, b, c, h⟩ := x.2
  exact ⟨a, b, c, Subtype.ext h.symm⟩

theorem ofCoords_mul (a b c a' b' c' : F4) :
    ofCoords a b c * ofCoords a' b' c' = ofCoords (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (unipU_mul a b c a' b' c')

theorem ofCoords_inj {a b c a' b' c' : F4} :
    ofCoords a b c = ofCoords a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => unipU_inj (congrArg Subtype.val h), fun ⟨h1, h2, h3⟩ => by rw [h1, h2, h3]⟩

theorem ofCoords_zero : ofCoords 0 0 0 = 1 := Subtype.ext unipU_zero

theorem omega_cube : F4.ω * F4.ω * F4.ω = 1 := by decide

theorem omega_cases (x : F4) : x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by
  revert x
  decide

@[expose] def torusDelta : SpecialLinearGroup (Fin 3) F4 :=
  ⟨Matrix.diagonal ![1, F4.ω, F4.ω * F4.ω], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa [mul_assoc] using omega_cube⟩

theorem coe_torusDelta :
    (torusDelta : Matrix (Fin 3) (Fin 3) F4) = Matrix.diagonal ![1, F4.ω, F4.ω * F4.ω] := rfl

theorem torusDelta_mul_unipU (a b c : F4) :
    torusDelta * unipU F4 a b c =
      unipU F4 (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c) * torusDelta := by
  have h3 := omega_cube
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_torusDelta, Matrix.mul_apply, Matrix.diagonal_apply, coe_unipU]
  · linear_combination (-a) * h3
  · linear_combination (-c) * h3
  · linear_combination (-(F4.ω * b)) * h3

theorem torusDelta_pow_three : torusDelta ^ 3 = 1 := by
  have h3 := omega_cube
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, coe_torusDelta, Matrix.mul_apply, Matrix.diagonal_apply]
  · exact h3
  · linear_combination (F4.ω * F4.ω * F4.ω + 1) * h3

theorem exists_mulEquiv_of_range_eq {X Y P : Type*} [Group X] [Group Y] [Group P] {f : X →* P}
    {g : Y →* P} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : ∃ φ : X ≃* Y, ∀ x, g (φ x) = f x := by
  refine ⟨(MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr h).trans
    (MonoidHom.ofInjective hg).symm), fun x => ?_⟩
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  simp [MonoidHom.ofInjective_apply]

theorem eq_one_of_two_power_of_odd {A : Type*} [Group A] {y v k : A} (hy : y = v * k)
    (hv : ∃ n, orderOf v = 2 ^ n) (hy2 : ∃ m, orderOf y = 2 ^ m) (hk : Commute v k)
    (hodd : Odd (orderOf k)) : k = 1 := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨m, hm⟩ := hy2
  have h1 : v ^ 2 ^ max n m = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hn]
    exact pow_dvd_pow 2 (le_max_left _ _)
  have h2 : y ^ 2 ^ max n m = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    exact pow_dvd_pow 2 (le_max_right _ _)
  have h3 : k ^ 2 ^ max n m = 1 := by
    rw [hy, hk.mul_pow, h1, one_mul] at h2
    exact h2
  have h4 : orderOf k ∣ 2 ^ max n m := orderOf_dvd_of_pow_eq_one h3
  have h5 : orderOf k = 1 :=
    Nat.Coprime.eq_one_of_dvd (hodd.coprime_two_right.pow_right _) h4
  exact orderOf_eq_one_iff.mp h5

variable {A : Type*} [Group A] [Finite A]

theorem exists_chart_of_hom {q : A →* LinearFlag.projectiveSL 3 F4} (hq : Function.Surjective q)
    (hker : q.ker ≤ center A) (hodd : Odd (Nat.card q.ker))
    (hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160) (V : Sylow 2 A) :
    ∃ (ι : ↥(unipAll F4) →* A) (h : A), Function.Injective ι ∧ ι.range = (V : Subgroup A) ∧
      h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      ∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (LinearFlag.projectiveSL 3 F4) := Finite.of_surjective q hq
  have hUcard : Nat.card (projUnip F4) = 64 := by
    rw [card_projUnip, natCard_F4]
  have hU2 : IsPGroup 2 (projUnip F4) := IsPGroup.of_card (n := 6) (by rw [hUcard]; norm_num)
  have hUidx : ¬ 2 ∣ (projUnip F4).index := by
    have h := Subgroup.card_mul_index (projUnip F4)
    rw [hUcard, hP] at h
    have : (projUnip F4).index = 315 := by omega
    rw [this]
    norm_num
  let U₂ : Sylow 2 (LinearFlag.projectiveSL 3 F4) := hU2.toSylow hUidx
  obtain ⟨V₀, hV₀⟩ := Sylow.mapSurjective_surjective hq 2 U₂
  have hV₀map : (V₀ : Subgroup A).map q = projUnip F4 := by
    have := congrArg (fun P : Sylow 2 (LinearFlag.projectiveSL 3 F4) => P.toSubgroup) hV₀
    simpa [U₂] using this
  have hkodd : ∀ k : A, q k = 1 → Odd (orderOf k) := fun k hk => by
    have hk' : k ∈ q.ker := hk
    have := orderOf_dvd_natCard (⟨k, hk'⟩ : q.ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have h2elt : ∀ x ∈ (V₀ : Subgroup A), ∃ m, orderOf x = 2 ^ m := fun x hx => by
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp V₀.isPGroup' ⟨x, hx⟩
    exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
  have hinj₀ : Function.Injective (q.comp (V₀ : Subgroup A).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    obtain ⟨m, hm⟩ := h2elt x x.2
    have := eq_one_of_two_power_of_odd (y := (x : A)) (v := 1) (k := (x : A)) (one_mul _).symm
      ⟨0, by simp⟩ ⟨m, hm⟩ (Commute.one_left _) (hkodd _ hx)
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  let ρ : ↥(unipAll F4) →* LinearFlag.projectiveSL 3 F4 :=
    (LinearFlag.proj 3 F4).comp (unipAll F4).subtype
  have hρinj : Function.Injective ρ := by
    intro u u' h
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
    obtain ⟨a', b', c', rfl⟩ := exists_ofCoords u'
    exact ofCoords_inj.2 (unipU_eq_of_proj_eq h)
  have hrange : (q.comp (V₀ : Subgroup A).subtype).range = ρ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hV₀map]
    simp only [ρ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_of_range_eq hinj₀ hρinj hrange
  let ι₀ : ↥(unipAll F4) →* A := (V₀ : Subgroup A).subtype.comp φ₀.symm.toMonoidHom
  have hι₀inj : Function.Injective ι₀ :=
    (V₀ : Subgroup A).subtype_injective.comp φ₀.symm.injective
  have hι₀range : ι₀.range = (V₀ : Subgroup A) := by
    rw [MonoidHom.range_eq_map]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact (φ₀.symm u).2
    · intro hx
      exact ⟨φ₀ ⟨x, hx⟩, trivial, by simp [ι₀]⟩
  have hmemV₀ : ∀ u, ι₀ u ∈ (V₀ : Subgroup A) := fun u => by
    rw [← hι₀range]
    exact ⟨u, rfl⟩
  have hqι₀ : ∀ u, q (ι₀ u) = ρ u := fun u => by
    have := hφ₀ (φ₀.symm u)
    simpa [ι₀] using this.symm
  obtain ⟨h₀, hh₀⟩ := hq (LinearFlag.proj 3 F4 torusDelta)
  have hconj : ∀ a b c : F4, h₀ * ι₀ (ofCoords a b c) * h₀⁻¹ =
      ι₀ (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
    intro a b c
    set u := ofCoords a b c with hu
    set u' := ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c) with hu'
    have hq1 : q (h₀ * ι₀ u * h₀⁻¹) = q (ι₀ u') := by
      rw [map_mul, map_mul, map_inv, hh₀, hqι₀, hqι₀, mul_inv_eq_iff_eq_mul]
      show LinearFlag.proj 3 F4 torusDelta * LinearFlag.proj 3 F4 (unipU F4 a b c) =
        LinearFlag.proj 3 F4 (unipU F4 (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) *
          LinearFlag.proj 3 F4 torusDelta
      rw [← map_mul, ← map_mul, torusDelta_mul_unipU]
    set k := (ι₀ u')⁻¹ * (h₀ * ι₀ u * h₀⁻¹) with hk
    have hkq : q k = 1 := by rw [hk, map_mul, map_inv, hq1, inv_mul_cancel]
    have hkc : k ∈ center A := hker hkq
    have hyk : h₀ * ι₀ u * h₀⁻¹ = ι₀ u' * k := by rw [hk]; group
    have hv2 : ∃ n, orderOf (ι₀ u') = 2 ^ n := h2elt _ (hmemV₀ u')
    have hy2 : ∃ m, orderOf (h₀ * ι₀ u * h₀⁻¹) = 2 ^ m := by
      obtain ⟨m, hm⟩ := h2elt _ (hmemV₀ u)
      exact ⟨m, by rw [← (SemiconjBy.conj_mk h₀ (ι₀ u)).orderOf_eq]; exact hm⟩
    have := eq_one_of_two_power_of_odd hyk hv2 hy2 (Subgroup.mem_center_iff.mp hkc (ι₀ u'))
      (hkodd k hkq)
    rw [hyk, this, mul_one]
  have hodd₀ : Odd (orderOf h₀) := by
    have h3 : q (h₀ ^ 3) = 1 := by
      rw [map_pow, hh₀, ← map_pow, torusDelta_pow_three, map_one]
    have hdvd : orderOf h₀ ∣ 3 * orderOf (h₀ ^ 3) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact (Odd.mul (by decide) (hkodd _ h3)).of_dvd_nat hdvd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A V₀ V
  have hVeq : (V : Subgroup A) = (V₀ : Subgroup A).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hcompat : ∀ a b c : F4, g * h₀ * g⁻¹ * ((MulAut.conj g).toMonoidHom.comp ι₀
      (ofCoords a b c)) * (g * h₀ * g⁻¹)⁻¹ = (MulAut.conj g).toMonoidHom.comp ι₀
      (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
    intro a b c
    have := congrArg (fun x => g * x * g⁻¹) (hconj a b c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this ⊢
    rw [← this]
    group
  refine ⟨(MulAut.conj g).toMonoidHom.comp ι₀, g * h₀ * g⁻¹,
    (MulAut.conj g).injective.comp hι₀inj, ?_, ?_, ?_, hcompat⟩
  · rw [MonoidHom.range_comp, hι₀range, hVeq]
  · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ ((MulAut.conj g).toMonoidHom.comp ι₀).range := by
      rw [MonoidHom.range_comp, hι₀range, ← hVeq]
      exact hn
    obtain ⟨u, rfl⟩ := hn'
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
    rw [hcompat]
    have : ((MulAut.conj g).toMonoidHom.comp ι₀) (ofCoords (F4.ω * F4.ω * a)
        (F4.ω * F4.ω * b) (F4.ω * c)) ∈ ((MulAut.conj g).toMonoidHom.comp ι₀).range := ⟨_, rfl⟩
    rw [MonoidHom.range_comp, hι₀range, ← hVeq] at this
    exact this
  · rw [← (SemiconjBy.conj_mk g h₀).orderOf_eq]
    exact hodd₀

theorem exists_chart (hZ : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* PSL3Four.S) (V : Sylow 2 A) :
    ∃ (ι : ↥(unipAll F4) →* A) (h : A), Function.Injective ι ∧ ι.range = (V : Subgroup A) ∧
      h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      ∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
  let q : A →* LinearFlag.projectiveSL 3 F4 :=
    theta.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center A)))
  have hq : Function.Surjective q :=
    theta.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : q.ker = center A := by
    ext x
    simp [q]
  have hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160 := by
    rw [Nat.card_congr theta.toEquiv, card_S]
  exact exists_chart_of_hom hq hker.le (by rw [hker]; exact hZ) hP V

theorem exists_chart_of_isSylowOf {G : Type*} [Group G] [Finite G]
    {A V : Subgroup G} (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 V A) :
    ∃ (ι : ↥(unipAll F4) →* G) (h : G), Function.Injective ι ∧ ι.range = V ∧ h ∈ A ∧
      Odd (orderOf h) ∧ ∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
  obtain ⟨Q, hQ⟩ := hV
  obtain ⟨ι, h, hι, hr, -, hodd, hact⟩ := exists_chart hZ e Q
  refine ⟨A.subtype.comp ι, (h : G), A.subtype_injective.comp hι, ?_, h.2, ?_, fun a b c => ?_⟩
  · rw [MonoidHom.range_comp, hr, ← hQ]
  · rw [Subgroup.orderOf_coe]
    exact hodd
  · have := congrArg A.subtype (hact a b c)
    simpa using this

@[expose] def U1 : Subgroup ↥(unipAll F4) := (unipOne F4).subgroupOf (unipAll F4)

@[expose] def U2 : Subgroup ↥(unipAll F4) := (unipTwo F4).subgroupOf (unipAll F4)

theorem ofCoords_mem_U1 {a b c : F4} : ofCoords a b c ∈ U1 ↔ b = 0 := by
  rw [U1, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a', c', h⟩
    exact (unipU_inj h).2.1.symm
  · rintro rfl
    exact ⟨a, c, rfl⟩

theorem ofCoords_mem_U2 {a b c : F4} : ofCoords a b c ∈ U2 ↔ a = 0 := by
  rw [U2, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b', c', h⟩
    exact (unipU_inj h).1.symm
  · rintro rfl
    exact ⟨b, c, rfl⟩

theorem ofCoords_inv (a b c : F4) :
    (ofCoords a b c)⁻¹ = ofCoords (-a) (-b) (-c + a * b) :=
  Subtype.ext (unipU_inv a b c)

theorem ofCoords_comm_central (a b c z : F4) :
    ofCoords a b c * ofCoords 0 0 z = ofCoords 0 0 z * ofCoords a b c := by
  rw [ofCoords_mul, ofCoords_mul, ofCoords_inj]
  refine ⟨by ring, by ring, by ring⟩

theorem ofCoords_conj_one (a' b' c' a c : F4) :
    ofCoords a' b' c' * ofCoords a 0 c * (ofCoords a' b' c')⁻¹ = ofCoords a 0 (c - a * b') := by
  rw [mul_inv_eq_iff_eq_mul, ofCoords_mul, ofCoords_mul, ofCoords_inj]
  refine ⟨by ring, by ring, by ring⟩

theorem ofCoords_conj_two (a' b' c' b c : F4) :
    ofCoords a' b' c' * ofCoords 0 b c * (ofCoords a' b' c')⁻¹ = ofCoords 0 b (c + a' * b) := by
  rw [mul_inv_eq_iff_eq_mul, ofCoords_mul, ofCoords_mul, ofCoords_inj]
  refine ⟨by ring, by ring, by ring⟩

instance : U1.Normal := ⟨fun n hn g => by
  obtain ⟨a', b', c', rfl⟩ := exists_ofCoords g
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords n
  rw [ofCoords_mem_U1] at hn
  subst hn
  rw [ofCoords_conj_one, ofCoords_mem_U1]⟩

instance : U2.Normal := ⟨fun n hn g => by
  obtain ⟨a', b', c', rfl⟩ := exists_ofCoords g
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords n
  rw [ofCoords_mem_U2] at hn
  subst hn
  rw [ofCoords_conj_two, ofCoords_mem_U2]⟩

theorem card_U1 : Nat.card U1 = 16 := by
  have e : F4 × F4 ≃ U1 :=
    Equiv.ofBijective (fun p => ⟨ofCoords p.1 0 p.2, ofCoords_mem_U1.2 rfl⟩)
      ⟨fun p q h => by
        obtain ⟨h1, -, h3⟩ := ofCoords_inj.1 (congrArg Subtype.val h)
        exact Prod.ext h1 h3, fun x => by
        obtain ⟨y, hx⟩ := x
        obtain ⟨a, b, c, rfl⟩ := exists_ofCoords y
        rw [ofCoords_mem_U1] at hx
        subst hx
        exact ⟨(a, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, natCard_F4]

theorem card_U2 : Nat.card U2 = 16 := by
  have e : F4 × F4 ≃ U2 :=
    Equiv.ofBijective (fun p => ⟨ofCoords 0 p.1 p.2, ofCoords_mem_U2.2 rfl⟩)
      ⟨fun p q h => by
        obtain ⟨-, h2, h3⟩ := ofCoords_inj.1 (congrArg Subtype.val h)
        exact Prod.ext h2 h3, fun x => by
        obtain ⟨y, hx⟩ := x
        obtain ⟨a, b, c, rfl⟩ := exists_ofCoords y
        rw [ofCoords_mem_U2] at hx
        subst hx
        exact ⟨(b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, natCard_F4]

theorem card_U1_inf_U2 : Nat.card ↥(U1 ⊓ U2) = 4 := by
  have e : F4 ≃ ↥(U1 ⊓ U2) :=
    Equiv.ofBijective (fun c => ⟨ofCoords 0 0 c, ofCoords_mem_U1.2 rfl, ofCoords_mem_U2.2 rfl⟩)
      ⟨fun p q h => (ofCoords_inj.1 (congrArg Subtype.val h)).2.2, fun x => by
        obtain ⟨y, h1, h2⟩ := x
        obtain ⟨a, b, c, rfl⟩ := exists_ofCoords y
        have h1' : ofCoords a b c ∈ U1 := h1
        have h2' : ofCoords a b c ∈ U2 := h2
        rw [ofCoords_mem_U1] at h1'
        rw [ofCoords_mem_U2] at h2'
        subst h1' h2'
        exact ⟨c, rfl⟩⟩
  rw [← Nat.card_congr e, natCard_F4]

theorem mem_center_iff_ofCoords {a b c : F4} :
    ofCoords a b c ∈ center ↥(unipAll F4) ↔ a = 0 ∧ b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 := h (ofCoords 0 1 0)
    have h2 := h (ofCoords 1 0 0)
    rw [ofCoords_mul, ofCoords_mul, ofCoords_inj] at h1 h2
    constructor
    · have := h1.2.2
      linear_combination -this
    · have := h2.2.2
      linear_combination this
  · rintro ⟨rfl, rfl⟩ g
    obtain ⟨a', b', c', rfl⟩ := exists_ofCoords g
    exact ofCoords_comm_central a' b' c' c

theorem U1_inf_U2 : U1 ⊓ U2 = center ↥(unipAll F4) := by
  ext x
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
  rw [Subgroup.mem_inf, ofCoords_mem_U1, ofCoords_mem_U2, mem_center_iff_ofCoords, and_comm]

theorem U1_sup_U2 : U1 ⊔ U2 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
  have h : ofCoords a b c = ofCoords a 0 0 * ofCoords 0 b (c - a * b) := by
    rw [ofCoords_mul, ofCoords_inj]
    refine ⟨by ring, by ring, by ring⟩
  rw [h]
  exact Subgroup.mul_mem_sup (ofCoords_mem_U1.2 rfl) (ofCoords_mem_U2.2 rfl)

section Transport

open CFSG.Open

variable {X A : Type*} [Group X] [Group A]

theorem isElemAbelian_of_forall {E : Subgroup A} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h2 : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, h2⟩

theorem comm_of_isElemAbelian {E : Subgroup A} (hE : IsElemAbelian 2 E) {x y : A} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

theorem isElemAbelian_map (ι : X →* A) {U : Subgroup X} (hU : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.map ι) := CFSG.Open.IsElemAbelian.map hU _

theorem isElemAbelian_comap {ι : X →* A} (hι : Function.Injective ι) {E : Subgroup A}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.comap ι) := CFSG.Open.IsElemAbelian.comap hE hι

theorem normal_map_subgroupOf {ι : X →* A} {V : Subgroup A} (hr : ι.range = V) (U : Subgroup X)
    [U.Normal] : ((U.map ι).subgroupOf V).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u₁, hu₁, hn1⟩ := hn
  have hg : (g : A) ∈ ι.range := hr ▸ g.2
  obtain ⟨u, hu⟩ := hg
  refine ⟨u * u₁ * u⁻¹, Subgroup.Normal.conj_mem ‹_› u₁ hu₁ u, ?_⟩
  rw [map_mul, map_mul, map_inv, hu, hn1]
  rfl

theorem map_center_eq_inf_centralizer {ι : X →* A} (hι : Function.Injective ι) {V : Subgroup A}
    (hr : ι.range = V) : (center X).map ι = V ⊓ centralizer (V : Set A) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨hr ▸ ⟨u, rfl⟩, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : v ∈ ι.range := hr ▸ hv
    obtain ⟨w, rfl⟩ := hv'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu w]
  · rintro ⟨hx, hxc⟩
    have hx' : x ∈ ι.range := hr ▸ hx
    obtain ⟨u, rfl⟩ := hx'
    refine ⟨u, Subgroup.mem_center_iff.mpr fun w => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hxc _ (hr ▸ ⟨w, rfl⟩)

theorem le_of_comap_le {ι : X →* A} {E : Subgroup A} {U : Subgroup X} (hE : E ≤ ι.range)
    (h : E.comap ι ≤ U) : E ≤ U.map ι := by
  intro x hx
  obtain ⟨u, rfl⟩ := hE hx
  exact ⟨u, h hx, rfl⟩

end Transport

theorem le_U1_or_le_U2 {E : Subgroup ↥(unipAll F4)} (hsq : ∀ x ∈ E, x * x = 1) :
    E ≤ U1 ∨ E ≤ U2 := by
  have hE : E.map (unipAll F4).subtype ≤ unipAll F4 := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hsq' : ∀ g ∈ E.map (unipAll F4).subtype, g * g = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (hsq u hu)
  rcases le_unipOne_or_le_unipTwo _ hE hsq' with h | h
  · left
    intro u hu
    exact h ⟨u, hu, rfl⟩
  · right
    intro u hu
    exact h ⟨u, hu, rfl⟩

theorem radicals_of_chart {A : Type*} [Group A] [Finite A] {ι : ↥(unipAll F4) →* A}
    (hι : Function.Injective ι) {V : Subgroup A} (hr : ι.range = V) :
    U1.map ι ≤ V ∧ U2.map ι ≤ V ∧ ((U1.map ι).subgroupOf V).Normal ∧
      ((U2.map ι).subgroupOf V).Normal ∧ CFSG.Open.IsElemAbelian 2 (U1.map ι) ∧
      CFSG.Open.IsElemAbelian 2 (U2.map ι) ∧ Nat.card (U1.map ι) = 16 ∧
      Nat.card (U2.map ι) = 16 ∧ U1.map ι ⊓ U2.map ι = V ⊓ centralizer (V : Set A) ∧
      U1.map ι ⊔ U2.map ι = V ∧ Nat.card ↥(V ⊓ centralizer (V : Set A)) = 4 ∧
      (∀ E : Subgroup A, E ≤ V → CFSG.Open.IsElemAbelian 2 E → E ≤ U1.map ι ∨ E ≤ U2.map ι) ∧
      (∀ E : Subgroup A, E ≤ V → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
        E = U1.map ι ∨ E = U2.map ι) ∧
      (∀ x ∈ V, x ^ 2 = 1 → x ∈ U1.map ι ∨ x ∈ U2.map ι) := by
  have h2 : ∀ a : F4, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hinfc : U1.map ι ⊓ U2.map ι = V ⊓ centralizer (V : Set A) := by
    rw [← Subgroup.map_inf _ _ ι hι, U1_inf_U2]
    exact map_center_eq_inf_centralizer hι hr
  have hU1ab : CFSG.Open.IsElemAbelian 2 U1 := by
    refine isElemAbelian_of_forall ?_ ?_
    · intro x hx y hy
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
      obtain ⟨a', b', c', rfl⟩ := exists_ofCoords y
      rw [ofCoords_mem_U1] at hx hy
      subst hx hy
      rw [ofCoords_mul, ofCoords_mul, ofCoords_inj]
      refine ⟨by ring, by ring, by ring⟩
    · intro x hx
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
      rw [ofCoords_mem_U1] at hx
      subst hx
      rw [sq, ofCoords_mul, ← ofCoords_zero, ofCoords_inj]
      refine ⟨h2 a, by simp, ?_⟩
      rw [mul_zero, add_zero, h2 c]
  have hU2ab : CFSG.Open.IsElemAbelian 2 U2 := by
    refine isElemAbelian_of_forall ?_ ?_
    · intro x hx y hy
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
      obtain ⟨a', b', c', rfl⟩ := exists_ofCoords y
      rw [ofCoords_mem_U2] at hx hy
      subst hx hy
      rw [ofCoords_mul, ofCoords_mul, ofCoords_inj]
      refine ⟨by ring, by ring, by ring⟩
    · intro x hx
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
      rw [ofCoords_mem_U2] at hx
      subst hx
      rw [sq, ofCoords_mul, ← ofCoords_zero, ofCoords_inj]
      refine ⟨by simp, h2 b, ?_⟩
      rw [zero_mul, add_zero, h2 c]
  have hE : ∀ E : Subgroup A, E ≤ V → CFSG.Open.IsElemAbelian 2 E →
      E ≤ U1.map ι ∨ E ≤ U2.map ι := by
    intro E hEV hEab
    have hEr : E ≤ ι.range := hr ▸ hEV
    have hsq : ∀ x ∈ E.comap ι, x * x = 1 := by
      intro x hx
      apply hι
      rw [map_mul, map_one, ← sq]
      exact hEab.2 _ hx
    rcases le_U1_or_le_U2 hsq with h | h
    · exact Or.inl (le_of_comap_le hEr h)
    · exact Or.inr (le_of_comap_le hEr h)
  have hc1 : Nat.card (U1.map ι) = 16 := by rw [Subgroup.card_map_of_injective hι, card_U1]
  have hc2 : Nat.card (U2.map ι) = 16 := by rw [Subgroup.card_map_of_injective hι, card_U2]
  refine ⟨(Subgroup.map_le_range ι U1).trans hr.le, (Subgroup.map_le_range ι U2).trans hr.le,
    normal_map_subgroupOf hr U1, normal_map_subgroupOf hr U2, isElemAbelian_map ι hU1ab,
    isElemAbelian_map ι hU2ab, hc1, hc2, hinfc, ?_, ?_, hE, ?_, ?_⟩
  · rw [← Subgroup.map_sup, U1_sup_U2, ← MonoidHom.range_eq_map, hr]
  · rw [← hinfc, ← Subgroup.map_inf _ _ ι hι, Subgroup.card_map_of_injective hι, card_U1_inf_U2]
  · intro E hEV hEab hE16
    rcases hE E hEV hEab with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc1, hE16]))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc2, hE16]))
  · intro x hx hx2
    have hEab : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) := by
      refine isElemAbelian_of_forall ?_ ?_
      · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
        exact (Commute.zpow_zpow_self x m n).eq
      · rintro _ ⟨m, rfl⟩
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx2,
          _root_.one_zpow]
    rcases hE (Subgroup.zpowers x) ((Subgroup.zpowers_le).2 hx) hEab with h | h
    · exact Or.inl (h (Subgroup.mem_zpowers x))
    · exact Or.inr (h (Subgroup.mem_zpowers x))

theorem torus_of_chart {A : Type*} [Group A] [Finite A] {ι : ↥(unipAll F4) →* A}
    (hι : Function.Injective ι) {V : Subgroup A} (hr : ι.range = V) {h : A}
    (hodd : Odd (orderOf h))
    (hact : ∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
      ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c))) :
    h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      (∀ E : Subgroup A, E ≤ V → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
        h ∈ normalizer (E : Set A)) ∧
      ⁅V, Subgroup.zpowers h⁆ = V ∧
      (∀ u ∈ V ⊓ centralizer (V : Set A), u ≠ 1 → ∀ u' ∈ V ⊓ centralizer (V : Set A), u' ≠ 1 →
        ∃ y ∈ normalizer ((V ⊓ centralizer (V : Set A) : Subgroup A) : Set A),
          y * u * y⁻¹ = u') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := radicals_of_chart hι hr
  have hnormU : ∀ U : Subgroup ↥(unipAll F4),
      (∀ a b c : F4, ofCoords a b c ∈ U →
        ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c) ∈ U) →
      h ∈ normalizer (U.map ι : Set A) := by
    intro U hU
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨u, hu, rfl⟩ := hn
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
    rw [hact]
    exact ⟨_, hU a b c hu, rfl⟩
  have hnorm : h ∈ normalizer (V : Set A) := by
    have := hnormU ⊤ fun _ _ _ _ => trivial
    rwa [← MonoidHom.range_eq_map, hr] at this
  have hnorm1 : h ∈ normalizer (U1.map ι : Set A) := by
    refine hnormU _ fun a b c hu => ?_
    rw [ofCoords_mem_U1] at hu ⊢
    rw [hu, mul_zero]
  have hnorm2 : h ∈ normalizer (U2.map ι : Set A) := by
    refine hnormU _ fun a b c hu => ?_
    rw [ofCoords_mem_U2] at hu ⊢
    rw [hu, mul_zero]
  refine ⟨hnorm, hodd, ?_, ?_, ?_⟩
  · intro E hE hEab hE16
    rcases h13 E hE hEab hE16 with rfl | rfl
    · exact hnorm1
    · exact hnorm2
  ·
    set K := ⁅(V : Subgroup A), Subgroup.zpowers h⁆ with hK
    apply le_antisymm
    · rw [hK, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hg₂N : g₂ ∈ normalizer (V : Set A) := (Subgroup.zpowers_le.2 hnorm) hg₂
      have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ (V : Subgroup A) :=
        (mem_normalizer_iff.mp hg₂N g₁⁻¹).mp ((V : Subgroup A).inv_mem hg₁)
      have h2 : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact (V : Subgroup A).mul_mem hg₁ h1
    ·
      have key : ∀ a b c : F4, ι (ofCoords a b c) *
          (ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)))⁻¹ ∈ K := by
        intro a b c
        have hmem : ⁅ι (ofCoords a b c), h⁆ ∈ K :=
          Subgroup.commutator_mem_commutator
            (show ι (ofCoords a b c) ∈ V by rw [← hr]; exact ⟨_, rfl⟩) (Subgroup.mem_zpowers h)
        have heq : ⁅ι (ofCoords a b c), h⁆ = ι (ofCoords a b c) *
            (ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)))⁻¹ := by
          rw [← hact a b c, commutatorElement_def]
          group
        rwa [heq] at hmem
      have hne1 : (1 : F4) - F4.ω * F4.ω ≠ 0 := by decide
      have hne2 : (1 : F4) - F4.ω ≠ 0 := by decide
      have hdiv1 : ∀ y : F4, (1 - F4.ω * F4.ω) * (y / (1 - F4.ω * F4.ω)) = y := fun y => by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne1]
      have hdiv2 : ∀ y : F4, (1 - F4.ω) * (y / (1 - F4.ω)) = y := fun y => by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne2]
      have hone : ∀ x : F4, ι (ofCoords x 0 0) ∈ K := by
        intro x
        have := key (x / (1 - F4.ω * F4.ω)) 0 0
        rw [← map_inv, ← map_mul, ofCoords_inv, ofCoords_mul] at this
        convert this using 2
        rw [ofCoords_inj]
        refine ⟨?_, by ring, by ring⟩
        linear_combination (-1 : F4) * hdiv1 x
      have htwo : ∀ x : F4, ι (ofCoords 0 x 0) ∈ K := by
        intro x
        have := key 0 (x / (1 - F4.ω * F4.ω)) 0
        rw [← map_inv, ← map_mul, ofCoords_inv, ofCoords_mul] at this
        convert this using 2
        rw [ofCoords_inj]
        refine ⟨by ring, ?_, by ring⟩
        linear_combination (-1 : F4) * hdiv1 x
      have hthree : ∀ x : F4, ι (ofCoords 0 0 x) ∈ K := by
        intro x
        have := key 0 0 (x / (1 - F4.ω))
        rw [← map_inv, ← map_mul, ofCoords_inv, ofCoords_mul] at this
        convert this using 2
        rw [ofCoords_inj]
        refine ⟨by ring, by ring, ?_⟩
        linear_combination (-1 : F4) * hdiv2 x
      intro x hx
      have hx' : x ∈ ι.range := hr ▸ hx
      obtain ⟨u, rfl⟩ := hx'
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
      have hfac : ofCoords a b c = ofCoords a 0 0 * ofCoords 0 b 0 *
          ofCoords 0 0 (c - a * b) := by
        rw [ofCoords_mul, ofCoords_mul, ofCoords_inj]
        refine ⟨by ring, by ring, by ring⟩
      rw [hfac, map_mul, map_mul]
      exact K.mul_mem (K.mul_mem (hone a) (htwo b)) (hthree _)
  ·
    have hZeq : (V : Subgroup A) ⊓ centralizer (V : Set A) = (center ↥(unipAll F4)).map ι :=
      (map_center_eq_inf_centralizer hι hr).symm
    have hmemZ : ∀ c : F4, ι (ofCoords 0 0 c) ∈ (V : Subgroup A) ⊓ centralizer (V : Set A) := by
      intro c
      rw [hZeq]
      exact ⟨_, (mem_center_iff_ofCoords).2 ⟨rfl, rfl⟩, rfl⟩
    have hZcoord : ∀ u ∈ (V : Subgroup A) ⊓ centralizer (V : Set A),
        ∃ c : F4, u = ι (ofCoords 0 0 c) := by
      intro u hu
      rw [hZeq] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      obtain ⟨a, b, c, rfl⟩ := exists_ofCoords w
      obtain ⟨rfl, rfl⟩ := (mem_center_iff_ofCoords).1 hw
      exact ⟨c, rfl⟩
    have hnormZ : h ∈ normalizer (((V : Subgroup A) ⊓ centralizer (V : Set A) : Subgroup A) :
        Set A) := by
      rw [hZeq]
      refine hnormU _ fun a b c hu => ?_
      rw [mem_center_iff_ofCoords] at hu ⊢
      rw [hu.1, hu.2, mul_zero]
      exact ⟨rfl, rfl⟩
    have hact0 : ∀ c : F4, h * ι (ofCoords 0 0 c) * h⁻¹ = ι (ofCoords 0 0 (F4.ω * c)) := by
      intro c
      rw [hact, mul_zero]
    intro u hu hu1 u' hu' hu'1
    obtain ⟨c, rfl⟩ := hZcoord u hu
    obtain ⟨c', rfl⟩ := hZcoord u' hu'
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu1 (by rw [ofCoords_zero, map_one])
    have hc' : c' ≠ 0 := by
      rintro rfl
      exact hu'1 (by rw [ofCoords_zero, map_one])
    have hratio : c' / c ≠ 0 := div_ne_zero hc' hc
    have hc'eq : c' = (c' / c) * c := by field_simp
    rcases omega_cases (c' / c) with h0 | h1 | hω | hω2
    · exact absurd h0 hratio
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [h1, one_mul] at hc'eq
      rw [hc'eq]
      simp
    · refine ⟨h, hnormZ, ?_⟩
      rw [hω] at hc'eq
      rw [hact0, hc'eq]
    · refine ⟨h * h, (normalizer _).mul_mem hnormZ hnormZ, ?_⟩
      have : h * h * ι (ofCoords 0 0 c) * (h * h)⁻¹ =
          h * (h * ι (ofCoords 0 0 c) * h⁻¹) * h⁻¹ := by group
      rw [hω2] at hc'eq
      rw [this, hact0, hact0, hc'eq, mul_assoc]


end CFSG.OddStandard.Seitz77.L34

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification
  CFSG.ComponentClassification.PSL3Four CFSG.ABGLocalTools
open scoped commutatorElement

variable {A : Type*} [Group A] [Finite A]

theorem exists_equiv_unip (hZ : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* PSL3Four.S) (V : Sylow 2 A) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      Nonempty (↥V ≃* ↥(unipAll k)) := by
  obtain ⟨ι, -, hι, hr, -⟩ := L34.exists_chart hZ e V
  exact ⟨PSL3Four.F4, inferInstance, inferInstance, PSL3Four.natCard_F4,
    ⟨(MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hι).symm⟩⟩


open CFSG.Open

theorem exists_parabolic_radicals
    (hZ : Odd (Nat.card (center A))) (e : A ⧸ center A ≃* PSL3Four.S) (V : Sylow 2 A) :
    ∃ V₁ V₂ : Subgroup A, V₁ ≤ (V : Subgroup A) ∧ V₂ ≤ (V : Subgroup A) ∧
      (V₁.subgroupOf (V : Subgroup A)).Normal ∧ (V₂.subgroupOf (V : Subgroup A)).Normal ∧
      IsElemAbelian 2 V₁ ∧ IsElemAbelian 2 V₂ ∧ Nat.card V₁ = 16 ∧ Nat.card V₂ = 16 ∧
      V₁ ⊓ V₂ = (V : Subgroup A) ⊓ centralizer (V : Set A) ∧ V₁ ⊔ V₂ = (V : Subgroup A) ∧
      Nat.card ↥((V : Subgroup A) ⊓ centralizer (V : Set A)) = 4 ∧
      (∀ E : Subgroup A, E ≤ (V : Subgroup A) → IsElemAbelian 2 E → E ≤ V₁ ∨ E ≤ V₂) ∧
      (∀ E : Subgroup A, E ≤ (V : Subgroup A) → IsElemAbelian 2 E → Nat.card E = 16 →
        E = V₁ ∨ E = V₂) ∧
      (∀ x ∈ (V : Subgroup A), x ^ 2 = 1 → x ∈ V₁ ∨ x ∈ V₂) := by
  obtain ⟨ι, -, hι, hr, -⟩ := L34.exists_chart hZ e V
  exact ⟨_, _, L34.radicals_of_chart hι hr⟩


theorem exists_torus
    (hZ : Odd (Nat.card (center A))) (e : A ⧸ center A ≃* PSL3Four.S) (V : Sylow 2 A) :
    ∃ h ∈ normalizer (V : Set A), Odd (orderOf h) ∧
      (∀ E : Subgroup A, E ≤ (V : Subgroup A) → IsElemAbelian 2 E → Nat.card E = 16 →
        h ∈ normalizer (E : Set A)) ∧
      ⁅(V : Subgroup A), Subgroup.zpowers h⁆ = (V : Subgroup A) ∧
      (∀ u ∈ (V : Subgroup A) ⊓ centralizer (V : Set A), u ≠ 1 →
        ∀ u' ∈ (V : Subgroup A) ⊓ centralizer (V : Set A), u' ≠ 1 →
          ∃ y ∈ normalizer (((V : Subgroup A) ⊓ centralizer (V : Set A) : Subgroup A) : Set A),
            y * u * y⁻¹ = u') := by
  obtain ⟨ι, h, hι, hr, hnorm, hodd, hact⟩ := L34.exists_chart hZ e V
  exact ⟨h, hnorm, (L34.torus_of_chart hι hr hodd hact).2⟩


section Ambient

variable {G : Type*} [Group G] [Finite G] {A V : Subgroup G}

theorem exists_equiv_unip_of_isSylowOf
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    (hV : IsSylowOf 2 V A) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      Nonempty (↥V ≃* ↥(unipAll k)) := by
  obtain ⟨ι, -, hι, hr, -⟩ := L34.exists_chart_of_isSylowOf hZ e hV
  exact ⟨PSL3Four.F4, inferInstance, inferInstance, PSL3Four.natCard_F4,
    ⟨(MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hι).symm⟩⟩

theorem exists_parabolic_radicals_of_isSylowOf
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    (hV : IsSylowOf 2 V A) :
    ∃ V₁ V₂ : Subgroup G, V₁ ≤ V ∧ V₂ ≤ V ∧ (V₁.subgroupOf V).Normal ∧ (V₂.subgroupOf V).Normal ∧
      IsElemAbelian 2 V₁ ∧ IsElemAbelian 2 V₂ ∧ Nat.card V₁ = 16 ∧ Nat.card V₂ = 16 ∧
      V₁ ⊓ V₂ = V ⊓ centralizer (V : Set G) ∧ V₁ ⊔ V₂ = V ∧
      Nat.card ↥(V ⊓ centralizer (V : Set G)) = 4 ∧
      (∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → E ≤ V₁ ∨ E ≤ V₂) ∧
      (∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E = 16 → E = V₁ ∨ E = V₂) ∧
      (∀ x ∈ V, x ^ 2 = 1 → x ∈ V₁ ∨ x ∈ V₂) := by
  obtain ⟨ι, -, hι, hr, -⟩ := L34.exists_chart_of_isSylowOf hZ e hV
  exact ⟨_, _, L34.radicals_of_chart hι hr⟩

theorem exists_torus_of_isSylowOf
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    (hV : IsSylowOf 2 V A) :
    ∃ h ∈ A, h ∈ normalizer (V : Set G) ∧ Odd (orderOf h) ∧
      (∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E = 16 →
        h ∈ normalizer (E : Set G)) ∧ ⁅V, Subgroup.zpowers h⁆ = V ∧
      (∀ u ∈ V ⊓ centralizer (V : Set G), u ≠ 1 → ∀ u' ∈ V ⊓ centralizer (V : Set G), u' ≠ 1 →
        ∃ y ∈ normalizer ((V ⊓ centralizer (V : Set G) : Subgroup G) : Set G),
          y * u * y⁻¹ = u') := by
  obtain ⟨ι, h, hι, hr, hhA, hodd, hact⟩ := L34.exists_chart_of_isSylowOf hZ e hV
  exact ⟨h, hhA, L34.torus_of_chart hι hr hodd hact⟩

end Ambient

end CFSG.OddStandard.Seitz77
