module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Conj4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped commutatorElement

theorem eq_one_or_eq_neg_one_of_mul_self {E : Type*} [Field E] (h2 : (2 : E) ≠ 0)
    (u : Matrix (Fin 2) (Fin 2) E) (hdet : u.det = 1) (hu : u * u = 1) : u = 1 ∨ u = -1 := by
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  have e10 := congrFun (congrFun hu 1) 0
  have e11 := congrFun (congrFun hu 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have htr : u 0 0 + u 1 1 ≠ 0 := by
    intro h0
    have hd : u 1 1 = -u 0 0 := by linear_combination h0
    rw [hd] at hdet
    apply h2
    linear_combination -e00 - hdet
  have hb : u 0 1 = 0 := by
    have : u 0 1 * (u 0 0 + u 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right htr
  have hc : u 1 0 = 0 := by
    have : u 1 0 * (u 0 0 + u 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right htr
  rw [hb, zero_mul, sub_zero] at hdet
  rw [hb, zero_mul, add_zero] at e00
  have ha : u 0 0 = 1 ∨ u 0 0 = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; linear_combination e00)
  rcases ha with ha | ha
  · left
    have hd : u 1 1 = 1 := by rw [ha, one_mul] at hdet; exact hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · right
    have hd : u 1 1 = -1 := by rw [ha] at hdet; linear_combination -hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem commutator_comm_of_comm_mod {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) {k X Y : G} (hX : X * k * X⁻¹ * k⁻¹ ∈ Z)
    (hY : Y * k * Y⁻¹ * k⁻¹ ∈ Z) : ⁅X, Y⁆ * k = k * ⁅X, Y⁆ := by
  set a := X * k * X⁻¹ * k⁻¹ with ha
  set b := Y * k * Y⁻¹ * k⁻¹ with hb
  have hac : ∀ g, g * a = a * g := fun g => Subgroup.mem_center_iff.mp (hZ hX) g
  have hbc : ∀ g, g * b = b * g := fun g => Subgroup.mem_center_iff.mp (hZ hY) g
  have hXk : X * k = a * k * X := by rw [ha]; group
  have hYk : Y * k = b * k * Y := by rw [hb]; group
  have hXk' : X⁻¹ * k = a⁻¹ * k * X⁻¹ := by
    have h1 : X⁻¹ * (X * k) * X⁻¹ = X⁻¹ * (a * k * X) * X⁻¹ := by rw [hXk]
    have h2 : k * X⁻¹ = X⁻¹ * a * k := by
      calc k * X⁻¹ = X⁻¹ * (X * k) * X⁻¹ := by group
        _ = X⁻¹ * (a * k * X) * X⁻¹ := h1
        _ = X⁻¹ * a * k := by group
    calc X⁻¹ * k = a⁻¹ * (a * X⁻¹) * k := by group
      _ = a⁻¹ * (X⁻¹ * a) * k := by rw [hac X⁻¹]
      _ = a⁻¹ * (X⁻¹ * a * k) := by group
      _ = a⁻¹ * (k * X⁻¹) := by rw [h2]
      _ = a⁻¹ * k * X⁻¹ := by group
  have hYk' : Y⁻¹ * k = b⁻¹ * k * Y⁻¹ := by
    have h2 : k * Y⁻¹ = Y⁻¹ * b * k := by
      calc k * Y⁻¹ = Y⁻¹ * (Y * k) * Y⁻¹ := by group
        _ = Y⁻¹ * (b * k * Y) * Y⁻¹ := by rw [hYk]
        _ = Y⁻¹ * b * k := by group
    calc Y⁻¹ * k = b⁻¹ * (b * Y⁻¹) * k := by group
      _ = b⁻¹ * (Y⁻¹ * b) * k := by rw [hbc Y⁻¹]
      _ = b⁻¹ * (Y⁻¹ * b * k) := by group
      _ = b⁻¹ * (k * Y⁻¹) := by rw [h2]
      _ = b⁻¹ * k * Y⁻¹ := by group
  have hac' : ∀ g, g * a⁻¹ = a⁻¹ * g := fun g => by
    have := hac g⁻¹
    calc g * a⁻¹ = (a * g⁻¹)⁻¹ := by group
      _ = (g⁻¹ * a)⁻¹ := by rw [this]
      _ = a⁻¹ * g := by group
  have hbc' : ∀ g, g * b⁻¹ = b⁻¹ * g := fun g => by
    have := hbc g⁻¹
    calc g * b⁻¹ = (b * g⁻¹)⁻¹ := by group
      _ = (g⁻¹ * b)⁻¹ := by rw [this]
      _ = b⁻¹ * g := by group
  rw [commutatorElement_def]
  calc X * Y * X⁻¹ * Y⁻¹ * k = X * Y * X⁻¹ * (Y⁻¹ * k) := by group
    _ = X * Y * X⁻¹ * (b⁻¹ * k * Y⁻¹) := by rw [hYk']
    _ = (X * Y * X⁻¹ * b⁻¹) * k * Y⁻¹ := by group
    _ = (b⁻¹ * (X * Y * X⁻¹)) * k * Y⁻¹ := by rw [hbc']
    _ = b⁻¹ * X * Y * (X⁻¹ * k) * Y⁻¹ := by group
    _ = b⁻¹ * X * Y * (a⁻¹ * k * X⁻¹) * Y⁻¹ := by rw [hXk']
    _ = b⁻¹ * X * (Y * a⁻¹) * k * X⁻¹ * Y⁻¹ := by group
    _ = b⁻¹ * X * (a⁻¹ * Y) * k * X⁻¹ * Y⁻¹ := by rw [hac']
    _ = b⁻¹ * (X * a⁻¹) * (Y * k) * X⁻¹ * Y⁻¹ := by group
    _ = b⁻¹ * (a⁻¹ * X) * (b * k * Y) * X⁻¹ * Y⁻¹ := by rw [hac', hYk]
    _ = b⁻¹ * a⁻¹ * (X * b) * k * Y * X⁻¹ * Y⁻¹ := by group
    _ = b⁻¹ * a⁻¹ * (b * X) * k * Y * X⁻¹ * Y⁻¹ := by rw [hbc]
    _ = b⁻¹ * (a⁻¹ * b) * (X * k) * Y * X⁻¹ * Y⁻¹ := by group
    _ = b⁻¹ * (b * a⁻¹) * (a * k * X) * Y * X⁻¹ * Y⁻¹ := by rw [← hac' b, hXk]
    _ = k * (X * Y * X⁻¹ * Y⁻¹) := by group

theorem exists_centralizer_embedding {F : Type} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (k : GL (Fin 4) F) (l : Fˣ) (hsq : k ^ 2 = GeneralLinearGroup.scalar (Fin 4) l)
    (hns : ¬ IsSquare (l : F)) :
    ∃ (E : Type) (_ : Field E) (ρ : Subgroup.centralizer {k} →* GL (Fin 2) E),
      (2 : E) ≠ 0 ∧ Function.Injective ρ ∧ ρ (ordinaryCentralizerScalar k (-1)) = -1 := by
  classical
  have hstr := nonsquare_projective_centralizer_structure 4 (by norm_num) k l hsq hns
  let : Fact (¬ IsSquare l.val) := ⟨hns⟩
  let := matrixModule k l hsq
  dsimp only at hstr
  obtain ⟨-, hfinE, hm, -, -, -, -, -, -, -, -, e', -, -, -, -, -, -, he'scal, -⟩ := hstr
  have hm2 : Module.finrank (extension l.val) (Fin 4 → F) = 2 := by omega
  set τ : GL (Fin (Module.finrank (extension l.val) (Fin 4 → F))) (extension l.val) ≃*
      GL (Fin 2) (extension l.val) :=
    Units.mapEquiv (Matrix.reindexRingEquiv (extension l.val) (finCongr hm2)).toMulEquiv with hτ
  set ρ : Subgroup.centralizer {k} →* GL (Fin 2) (extension l.val) :=
    τ.toMonoidHom.comp e'.toMonoidHom with hρ
  have hρinj : Function.Injective ρ := τ.injective.comp e'.injective
  refine ⟨extension l.val, inferInstance, ρ, ?_, hρinj, ?_⟩
  · intro h0
    apply h2
    have : algebraMap F (extension l.val) 2 = 0 := by rw [map_ofNat]; exact h0
    exact (map_eq_zero_iff _ (algebraMap F (extension l.val)).injective).1 this
  · rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      he'scal (-1)]
    apply Units.ext
    have h1 : ((GeneralLinearGroup.scalar (Fin (Module.finrank (extension l.val) (Fin 4 → F))))
        (Units.map (algebraMap F (extension l.val)).toMonoidHom (-1)) :
        Matrix (Fin (Module.finrank (extension l.val) (Fin 4 → F)))
          (Fin (Module.finrank (extension l.val) (Fin 4 → F))) (extension l.val)) = -1 := by
      rw [GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [hτ, Units.coe_mapEquiv, Units.val_neg, Units.val_one]
    change Matrix.reindex _ _ _ = _
    rw [h1]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.reindex_apply]
    · have hij' : (finCongr hm2).symm i ≠ (finCongr hm2).symm j := fun h => hij (by
        simpa using congrArg (finCongr hm2) h)
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.neg_apply,
        Matrix.one_apply_ne hij, Matrix.one_apply_ne hij']

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem scalar_neg_one_eq (n : ℕ) :
    (GeneralLinearGroup.scalar (Fin n) (-1 : Fˣ) : GL (Fin n) F) = -1 := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem sq_eq_neg_one_of_comm_orderOf (hq : Odd (Fintype.card F))
    {u v : StatedProj (StatedSL 4 F)} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1) (hv : orderOf v = s) (huv : u * v = v * u)
    (X : StatedSL 4 F) (hX : QuotientGroup.mk X = u) :
    ((X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X : GL (Fin 4) F) = -1 := by
  have := Fact.mk hs
  have hA : ProjGenLinGroup.mk (X : GL (Fin 4) F) = projToPGL 4 F u := by
    rw [← hX, projToPGL_mk]
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (projToPGL 4 F v)
  have hinj := projToPGL_injective (F := F) 4
  obtain ⟨l, hl, hns⟩ := not_isSquare_of_comm_odd_order (n := 4) (e := 1) (by norm_num) hq hs
    hs2 (by simpa using hsq) (by norm_num) (X : GL (Fin 4) F)
    (by rw [hA]; exact fun h1 => hu1 (hinj (by rw [h1, map_one])))
    (by rw [hA, ← map_pow, hu2, map_one]) g
    (by
      rw [hg]
      intro h1
      have : v = 1 := hinj (by rw [h1, map_one])
      rw [this, orderOf_one] at hv
      exact hs.one_lt.ne' hv.symm)
    (by rw [hg, ← map_pow, ← hv, pow_orderOf_eq_one, map_one])
    (by rw [hg, hA, ← map_mul, ← map_mul, huv])
  obtain ⟨hl1, -⟩ := sq_eq_neg_one_of_det_eq_one (X : GL (Fin 4) F) l hl hns
    (det_eq_one_of_mem_statedSL X.2)
  have hl' : l = -1 := Units.ext (by rw [hl1, Units.val_neg, Units.val_one])
  rw [hl', scalar_neg_one_eq] at hl
  have := congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F)) hl
  simpa [sq] using this

theorem exists_lift_sq_eq_neg_one_of_perfect (hF : Fintype.card F % 4 = 3) (k : StatedSL 4 F)
    (hk : ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (k : GL (Fin 4) F) = -1)
    {J' : Subgroup (StatedProj (StatedSL 4 F))}
    (hJ' : J' ≤ Subgroup.centralizer {(QuotientGroup.mk k : StatedProj (StatedSL 4 F))})
    (hJp : ⁅J', J'⁆ = J') {z : StatedProj (StatedSL 4 F)} (hz : z ∈ J') (hz2 : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ X : StatedSL 4 F, QuotientGroup.mk X = z ∧
      ((X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X : GL (Fin 4) F) = -1 := by
  classical
  have h2F : (2 : F) ≠ 0 := by
    intro h0
    have hc : ringChar F = 2 := by
      have := (ringChar.spec F 2).1 (by exact_mod_cast h0)
      exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 this
    have := FiniteField.even_card_iff_char_two.1 hc
    omega
  have hns1 : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  set Z := (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) with hZ
  set π : StatedSL 4 F →* StatedProj (StatedSL 4 F) := QuotientGroup.mk' Z with hπ
  set kG : GL (Fin 4) F := (k : GL (Fin 4) F) with hkG
  have hk2 : kG ^ 2 = GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) := by
    rw [scalar_neg_one_eq]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, hk, Units.val_neg, Units.val_one]
  obtain ⟨E, _, ρ, h2E, hρinj, hρneg⟩ := exists_centralizer_embedding h2F kG (-1)
    hk2 (by simpa using hns1)
  set C' : Subgroup (StatedSL 4 F) := (Subgroup.centralizer {kG}).comap (StatedSL 4 F).subtype
    with hC'
  have hcen : ∀ X : StatedSL 4 F, π X ∈ Subgroup.centralizer {π k} →
      (X : GL (Fin 4) F) * kG * (X : GL (Fin 4) F)⁻¹ * kG⁻¹ ∈ StatedScalars (Fin 4) F := by
    intro X hX
    rw [Subgroup.mem_centralizer_singleton_iff] at hX
    have h1 : π (X * k * X⁻¹ * k⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hX]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hscal : StatedScalars (Fin 4) F ≤ Subgroup.center (GL (Fin 4) F) := by
    rw [StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar]
  set φ : C' →* StatedProj (StatedSL 4 F) := π.comp C'.subtype with hφ
  have hcomm_le : ⁅Subgroup.centralizer {π k}, Subgroup.centralizer {π k}⁆ ≤
      (⊤ : Subgroup C').map φ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨X, rfl⟩ := QuotientGroup.mk'_surjective Z u
    obtain ⟨Y, rfl⟩ := QuotientGroup.mk'_surjective Z v
    have hXY : ⁅X, Y⁆ ∈ C' := by
      rw [hC', Subgroup.mem_comap, map_commutatorElement, Subgroup.mem_centralizer_singleton_iff]
      exact commutator_comm_of_comm_mod hscal (hcen X hu) (hcen Y hv)
    refine ⟨⟨⁅X, Y⁆, hXY⟩, Subgroup.mem_top _, ?_⟩
    rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    change π ⁅X, Y⁆ = _
    rw [map_commutatorElement]
  have hJ'C : J' ≤ (⁅(⊤ : Subgroup C'), (⊤ : Subgroup C')⁆).map φ := by
    have h1 : J' ≤ (⊤ : Subgroup C').map φ := by
      rw [← hJp]
      exact (Subgroup.commutator_mono hJ' hJ').trans hcomm_le
    rw [Subgroup.map_commutator, ← hJp]
    exact Subgroup.commutator_mono h1 h1
  obtain ⟨x', hx', rfl⟩ := hJ'C hz
  set ι : C' →* Subgroup.centralizer {kG} :=
    { toFun := fun x => ⟨((x : StatedSL 4 F) : GL (Fin 4) F), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  set ρ' := ρ.comp ι with hρ'
  have hρ'inj : Function.Injective ρ' := hρinj.comp fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact this
  have hdet : GeneralLinearGroup.det (ρ' x') = 1 := by
    have hle : ⁅(⊤ : Subgroup C'), (⊤ : Subgroup C')⁆ ≤ (GeneralLinearGroup.det.comp ρ').ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact hle hx'
  set X : StatedSL 4 F := (x' : StatedSL 4 F) with hXdef
  have hX2 : X ^ 2 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change (φ x') ^ 2 = 1
    rw [sq, hz2]
  rw [hZ, Subgroup.mem_subgroupOf] at hX2
  obtain ⟨c, hc⟩ := hX2
  have hc4 : (c : F) ^ 4 = 1 := by
    have h1 : GeneralLinearGroup.det ((X ^ 2 : StatedSL 4 F) : GL (Fin 4) F) = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply, Units.val_one]
                    exact det_eq_one_of_mem_statedSL (X ^ 2).2)
    rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hneg1 : (-1 : GL (Fin 4) F) ∈ StatedSL 4 F := by
    apply Subgroup.subset_closure
    change ((-1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1
    rw [Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num
  have hnegC : (⟨-1, hneg1⟩ : StatedSL 4 F) ∈ C' := by
    rw [hC', Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    change (-1 : GL (Fin 4) F) * kG = kG * -1
    rw [neg_one_mul, mul_neg_one]
  have hρ'neg : ρ' ⟨⟨-1, hneg1⟩, hnegC⟩ = -1 := by
    rw [hρ', MonoidHom.comp_apply, ← hρneg]
    congr 1
    apply Subtype.ext
    change (-1 : GL (Fin 4) F) = _
    rw [ordinaryCentralizerScalar_apply, scalar_neg_one_eq]
  rcases eq_one_or_eq_neg_one_of_pow_four hF hc4 with h1 | h1
  ·
    exfalso
    have hc1 : c = 1 := Units.ext h1
    have hx'2 : x' ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change ((X : GL (Fin 4) F)) ^ 2 = 1
      rw [← Subgroup.coe_pow, ← hc, hc1, map_one]
    have hu2 : ((ρ' x' : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *
        (ρ' x' : GL (Fin 2) E) = 1 := by
      rw [← Units.val_mul, ← sq, ← map_pow, hx'2, map_one, Units.val_one]
    have hud : ((ρ' x' : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det = 1 := by
      have := congrArg Units.val hdet
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    rcases eq_one_or_eq_neg_one_of_mul_self h2E _ hud hu2 with h3 | h3
    · have : x' = 1 := hρ'inj (by rw [map_one]; exact Units.ext (by rw [h3, Units.val_one]))
      apply hz1
      rw [this, map_one]
    · have : x' = ⟨⟨-1, hneg1⟩, hnegC⟩ := hρ'inj (by
        rw [hρ'neg]; exact Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
      apply hz1
      rw [this, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨-1, scalar_neg_one_eq 4⟩
  · refine ⟨X, rfl, ?_⟩
    have hc1 : c = -1 := Units.ext (by rw [h1, Units.val_neg, Units.val_one])
    have h3 : ((X : GL (Fin 4) F)) ^ 2 = -1 := by
      rw [← Subgroup.coe_pow, ← hc, hc1, scalar_neg_one_eq]
    have := congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F)) h3
    simpa [sq] using this

theorem exists_conj_of_sq_eq_neg_one' (hF : Fintype.card F % 4 = 3) (X Y : StatedSL 4 F)
    (hX : ((X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X : GL (Fin 4) F) = -1)
    (hY : ((Y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Y : GL (Fin 4) F) = -1) :
    ∃ w : StatedProj (StatedSL 4 F), w * QuotientGroup.mk X * w⁻¹ = QuotientGroup.mk Y := by
  classical
  have hns1 : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  obtain ⟨M, hMd, hMX⟩ := exists_conj_of_sq_eq_neg_one (by omega) hns1 hX hY
  have hMu : IsUnit M.det := by rw [hMd]; exact isUnit_one
  let g : GL (Fin 4) F := ⟨M, M⁻¹, Matrix.mul_nonsing_inv _ hMu, Matrix.nonsing_inv_mul _ hMu⟩
  have hg : g ∈ StatedSL 4 F := Subgroup.subset_closure hMd
  refine ⟨QuotientGroup.mk ⟨g, hg⟩, ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  change M * _ * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
  rw [hMX, Matrix.mul_assoc]
  change _ * (M * M⁻¹) = _
  rw [Matrix.mul_nonsing_inv _ hMu, Matrix.mul_one]

end CFSG.ComponentClassification.CatFactsL4U4
