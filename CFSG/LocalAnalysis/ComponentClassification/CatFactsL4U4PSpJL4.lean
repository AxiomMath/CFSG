module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4JHat
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace PSpL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks StabL
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB Subgroup
open scoped commutatorElement

variable {F : Type} [Field F] [Fintype F]

theorem pow_conj_eq {G : Type*} [Group G] {X k z : G} (hz : z ∈ center G)
    (h : X * k * X⁻¹ = z * k) (n : ℕ) : X ^ n * k * (X ^ n)⁻¹ = z ^ n * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc X ^ (n + 1) * k * (X ^ (n + 1))⁻¹ = X * (X ^ n * k * (X ^ n)⁻¹) * X⁻¹ := by group
      _ = X * (z ^ n * k) * X⁻¹ := by rw [ih]
      _ = z ^ n * (X * k * X⁻¹) := by
          rw [← mul_assoc X, mem_center_iff.mp (pow_mem hz n) X]
          group
      _ = z ^ (n + 1) * k := by rw [h, pow_succ, mul_assoc]

theorem mem_J₀_of_odd (hF3 : Fintype.card F = 3)
    (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (J₀ F))
    {X : SpecialLinearGroup (Fin 4) F} (hX : proj 4 F X ∈ centralizer {proj 4 F k₀})
    (hodd : Odd (orderOf (proj 4 F X))) : proj 4 F X ∈ J₀ F := by
  classical
  have hF : Fintype.card F % 4 = 3 := by rw [hF3]
  have hcen : scalars 4 F ≤ center (SpecialLinearGroup (Fin 4) F) := scalars_le_center 4 F
  set m := orderOf (proj 4 F X) with hm
  have hsq : ∀ s ∈ scalars 4 F, s ^ 2 = 1 := by
    intro s hs
    obtain ⟨c, -, hc⟩ := mem_scalars.1 hs
    have hc2 : c ^ 2 = 1 := by
      have := pow_card_eq_one (x := c)
      rw [Fintype.card_units, hF3] at this
      exact this
    rw [sq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, ← map_mul, ← Units.val_mul, ← sq, hc2,
      Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  set z := X * k₀ * X⁻¹ * k₀⁻¹ with hz
  have hzs : z ∈ scalars 4 F := by
    rw [hz, ← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
      mem_centralizer_singleton_iff.mp hX]
    group
  have hXk : X * k₀ * X⁻¹ = z * k₀ := by rw [hz]; group
  have hXm : X ^ m ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_pow, hm, pow_orderOf_eq_one]
  have hzm : z ^ m = 1 := by
    have e1 := pow_conj_eq (hcen hzs) hXk m
    rw [← mem_center_iff.mp (hcen hXm) k₀, mul_inv_cancel_right] at e1
    have e2 := congrArg (· * k₀⁻¹) e1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at e2
    exact e2.symm
  have hz1 : z = 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, pow_succ, pow_mul, hsq z hzs, one_pow, one_mul] at hzm
    exact hzm
  have hXC : X ∈ C₀ F := by
    rw [C₀, mem_centralizer_singleton_iff]
    rw [hz1, one_mul] at hXk
    calc X * k₀ = X * k₀ * X⁻¹ * X := by group
      _ = k₀ * X := by rw [hXk]
  set s := X ^ m with hs
  set X' := X * s with hX'
  have hX'C : X' ∈ C₀ F := mul_mem hXC (by
    rw [C₀, mem_centralizer_singleton_iff]
    exact (mem_center_iff.mp (hcen hXm) k₀).symm)
  have hX'm : X' ^ m = 1 := by
    obtain ⟨t, ht⟩ := hodd
    have hsX : Commute X s := (Commute.self_pow X m)
    rw [hX', hsX.mul_pow, ← hs, ← pow_succ', ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring,
      pow_mul, hsq s hXm, one_pow]
  have hpX' : proj 4 F X' = proj 4 F X := by
    rw [hX', map_mul, (proj_eq_one_iff).2 hXm, mul_one]
  have hns : ¬ IsSquare ((-1 : Fˣ) : F) := by
    rw [Units.val_neg, Units.val_one, FiniteField.isSquare_neg_one_iff]
    omega
  set k := SpecialLinearGroup.toGL (k₀ : SpecialLinearGroup (Fin 4) F) with hk
  obtain ⟨E, _, _, ρ, hE, hρ⟩ := exists_centralizer_embedding_card k (-1) toGL_k₀_sq hns
  let ι : C₀ F →* centralizer {k} :=
    (SpecialLinearGroup.toGL.comp (C₀ F).subtype).codRestrict _ fun x => by
      rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, coe_subtype, hk,
        ← map_mul, ← map_mul]
      congr 1
      exact mem_centralizer_singleton_iff.mp x.2
  have hι : Function.Injective ι := fun a b hab => by
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val hab
  set ψ : C₀ F →* Eˣ := GeneralLinearGroup.det.comp (ρ.comp ι) with hψ
  have hE8 : Nat.card Eˣ = 8 := by
    let := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hE,
      Nat.card_eq_fintype_card, hF3]
    norm_num
  have hψX' : ψ ⟨X', hX'C⟩ = 1 := by
    have h1 : ψ ⟨X', hX'C⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨X', hX'C⟩ : C₀ F) ^ m = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hX'm]; rfl)
      rw [this, map_one]
    have h8 : ψ ⟨X', hX'C⟩ ^ 8 = 1 := by
      rw [← hE8]
      exact pow_card_eq_one'
    have hg : Nat.gcd m 8 = 1 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd))
    have := pow_gcd_eq_one.2 ⟨h1, h8⟩
    rwa [hg, pow_one] at this
  set K' := ψ.ker.map (C₀ F).subtype with hK'
  have hSC : S₀ F ≤ C₀ F := commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hSK : S₀ F ≤ K' := by
    rw [S₀, commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : C₀ F), (⟨b, hb⟩ : C₀ F)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hcardK : Nat.card K' ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by
    let g : K' → SpecialLinearGroup (Fin 2) E := fun x =>
      ⟨(ρ (ι ⟨x, by obtain ⟨y, -, hy⟩ := x.2; rw [← hy]; exact y.2⟩) :
        Matrix (Fin 2) (Fin 2) E), by
        obtain ⟨y, hy, hyx⟩ := x.2
        have hy' : y = ⟨x, by rw [← hyx]; exact y.2⟩ := Subtype.ext hyx
        rw [← hy']
        have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
        rwa [hψ, MonoidHom.comp_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 := Units.ext (congrArg Subtype.val hxy)
      have h2 := hι (hρ h1)
      exact Subtype.ext (congrArg (fun w : C₀ F => (w : SpecialLinearGroup (Fin 4) F)) h2)
    calc Nat.card K' ≤ Nat.card (SpecialLinearGroup (Fin 2) E) := Nat.card_le_card_of_injective g hg
      _ = Nat.card E * (Nat.card E ^ 2 - 1) := by
          let := Fintype.ofFinite E
          have hq : 1 < Fintype.card E := Fintype.one_lt_card
          rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
            pow_one, Nat.card_eq_fintype_card, show Fintype.card E ^ 2 - Fintype.card E =
              Fintype.card E * (Fintype.card E - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
            Nat.mul_div_cancel _ (by omega), mul_comm]
      _ = Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by rw [hE]
  set φ : K' →* projectiveSL 4 F := (proj 4 F).comp K'.subtype with hφ
  have hrange : φ.range = K'.map (proj 4 F) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  have hneg : (⟨-1, hSK neg_one_mem_S₀⟩ : K') ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, coe_subtype, proj_eq_one_iff, mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Units.val_neg,
      Units.val_one, map_neg, map_one]
  have h2F := two_ne_zero_of_card_mod_four hF
  have hne : (⟨-1, hSK neg_one_mem_S₀⟩ : K') ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun y : K' =>
      ((y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2F
    linear_combination -this
  have hker : 2 ≤ Nat.card φ.ker := by
    have : 1 < Nat.card φ.ker := by
      rw [one_lt_card_iff_ne_bot]
      intro hbot
      rw [hbot, mem_bot] at hneg
      exact hne hneg
    omega
  have hmul := card_ker_mul_card_range φ
  rw [hrange] at hmul
  have hJK : J₀ F ≤ K'.map (proj 4 F) := map_mono hSK
  have hJeq : K'.map (proj 4 F) = J₀ F := by
    refine (eq_of_le_of_card_ge hJK ?_).symm
    have : 2 * Nat.card (K'.map (proj 4 F)) ≤ Nat.card K' := by
      calc 2 * Nat.card (K'.map (proj 4 F)) ≤ Nat.card φ.ker * Nat.card (K'.map (proj 4 F)) :=
            Nat.mul_le_mul_right _ hker
        _ = Nat.card K' := hmul
    omega
  rw [← hJeq, ← hpX']
  exact ⟨X', ⟨⟨X', hX'C⟩, hψX', rfl⟩, rfl⟩

theorem conj_mem_closure {Y : Type*} [Group Y] {S : Set Y} {g : Y}
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) {x : Y} (hx : x ∈ closure S) : g * x * g⁻¹ ∈ closure S := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem le_closure_odd {Y : Type*} [Group Y] {S : Subgroup Y} [IsSimpleGroup ↥S]
    (hodd0 : ∃ y ∈ S, y ≠ 1 ∧ Odd (orderOf y)) :
    S ≤ closure {y : Y | y ∈ S ∧ Odd (orderOf y)} := by
  set T := closure {y : Y | y ∈ S ∧ Odd (orderOf y)} with hT
  have hn : (T.subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    refine conj_mem_closure ?_ hn
    rintro y ⟨hy1, hy2⟩
    have : orderOf ((g : Y) * y * (g : Y)⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ⟨mul_mem (mul_mem g.2 hy1) (inv_mem g.2), by rw [this]; exact hy2⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨y, hy, hy1, hyo⟩ := hodd0
    have : (⟨y, hy⟩ : S) ∈ T.subgroupOf S := by
      rw [mem_subgroupOf]
      exact subset_closure ⟨hy, hyo⟩
    rw [hb, mem_bot] at this
    exact hy1 (congrArg Subtype.val this)
  · rwa [subgroupOf_eq_top] at ht

omit [Fintype F] in
theorem J₀_le_centralizer : J₀ F ≤ centralizer {proj 4 F k₀} := by
  have hSC : S₀ F ≤ C₀ F := commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.mp (hSC hu)]

theorem centralizerCore516_k₀ [IsSimpleGroup ↥(J₀ F)]
    (hJ₀p : ⁅J₀ F, J₀ F⁆ = J₀ F)
    (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (J₀ F))
    (hodd0 : ∃ y ∈ J₀ F, y ≠ 1 ∧ Odd (orderOf y)) :
    centralizerCore516 (Fintype.card F) (proj 4 F k₀) = J₀ F := by
  have hJC := J₀_le_centralizer (F := F)
  unfold centralizerCore516
  split_ifs with hq3
  · apply le_antisymm
    · rw [closure_le]
      rintro y ⟨hy, hyo⟩
      obtain ⟨X, rfl⟩ := proj_surjective 4 F y
      exact mem_J₀_of_odd hq3 hcard hy hyo
    · exact (le_closure_odd hodd0).trans (closure_mono fun y hy => ⟨hJC hy.1, hy.2⟩)
  · exact le_antisymm (le_J₀ (Quasithin.perfectCore_le _) (Quasithin.perfectCore_perfect _))
      (Quasithin.le_perfectCore_of_perfect hJC hJ₀p)

theorem innerPSpAt_k₀ (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) [IsSimpleGroup ↥(J₀ F)] (hJ₀p : ⁅J₀ F, J₀ F⁆ = J₀ F)
    (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (J₀ F))
    (hodd0 : ∃ y ∈ J₀ F, y ≠ 1 ∧ Odd (orderOf y)) (hZ : center (projectiveSL 4 F) = ⊥) :
    InnerPSpAt (p ^ f) p f (proj 4 F k₀) := by
  classical
  have hq : p ^ f = Fintype.card F := by rw [← hK, Nat.card_eq_fintype_card]
  rw [hq]
  have hN := centralizerCore516_k₀ hJ₀p hcard hodd0
  have hJC := J₀_le_centralizer (F := F)
  have heven : Even (Nat.card (J₀ F)) := by
    have h1 := two_mul_card_J₀_le hF
    have hodd : Odd (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.odd_iff.2 (by omega)
    have h2 := le_antisymm h1 hcard
    rw [show (Nat.card F ^ 2) ^ 2 = Nat.card F ^ 4 by ring] at h2
    exact even_of_two_mul_eq hodd h2
  refine ⟨pPrimeCore_centralizerCore516_eq_bot hJC hN.le
    (eq_bot_of_le_simple heven), fun ε hε2 hε1 hεℓ _ hεN => ?_⟩
  have hfix : ∀ x ∈ J₀ F, ε x = x := fun x hx => hεN x (by rw [hN]; exact hx)
  rcases inner_or_alternating hF hp hK ε (m := 0) (by simpa using hε2) (hasUnipotents_J₀ hF)
      hfix with ⟨z, rfl⟩ | ⟨A, hA, rfl⟩
  · exfalso
    have hzC : z ∈ centralizer (J₀ F : Set (projectiveSL 4 F)) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := hfix x hx
      rw [MulAut.conj_apply] at this
      calc x * z = z * x * z⁻¹ * z := by rw [this]
        _ = z * x := by group
    have hz2 : z ^ 2 = 1 := by
      have h1 : MulAut.conj (z ^ 2) = 1 := by rw [map_pow, hε2]
      rw [conj_eq_one_iff_mem_center, hZ, mem_bot] at h1
      exact h1
    have hkC : proj 4 F k₀ ∈ centralizer (J₀ F : Set (projectiveSL 4 F)) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hJC hx)
    have hk2 : proj 4 F k₀ ^ 2 = 1 := by
      rw [sq, ← map_mul, proj_eq_one_iff, mem_scalars]
      refine ⟨-1, by norm_num, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change stdJ * stdJ = _
      rw [stdJ_mul_stdJ, Units.val_neg, Units.val_one, map_neg, map_one]
    have hk1 : proj 4 F k₀ ≠ 1 := by
      rw [Ne, proj_eq_one_iff, mem_scalars]
      rintro ⟨c, -, hc⟩
      have e00 := congrFun (congrFun hc 0) 0
      change stdJ 0 0 = _ at e00
      simp [stdJ, Matrix.scalar_apply] at e00
      exact Units.ne_zero c e00.symm
    have := isCyclic_centralizer hF (hasUnipotents_J₀ hF)
    by_cases hz1 : z = 1
    · exact hε1 (by rw [hz1, map_one])
    · apply hεℓ
      have := eq_of_sq_eq_one_of_isCyclic (a := (⟨z, hzC⟩ : centralizer (J₀ F : Set _)))
        (b := ⟨proj 4 F k₀, hkC⟩) (Subtype.ext (by simpa using hz2))
        (Subtype.ext (by simpa using hk2)) (fun h => hz1 (congrArg Subtype.val h))
        (fun h => hk1 (congrArg Subtype.val h))
      rw [show z = proj 4 F k₀ from congrArg Subtype.val this]
  · exact exists_psp_of_alt_L4 hF hp hK A hA

end PSpL

end CFSG.ComponentClassification.CatFactsL4U4
