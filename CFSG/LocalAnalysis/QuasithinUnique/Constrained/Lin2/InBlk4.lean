module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section BlockData

variable {G : Type} [Group G]

@[expose] def BlockData (L R : Subgroup G) (f : G) (n : ℕ) : Prop :=
  ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
    (α : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, F))
    (β : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → F)),
    n = m + m ∧ Fintype.card F = 2 ^ m ∧ (2 : F) = 0 ∧ Function.Surjective α ∧
      (∀ c, α c = 1 ↔ (c : G) ∈ blockU L) ∧ Function.Surjective β ∧
      (∀ v, β v = 1 ↔ (v : G) ∈ blockZ L) ∧
      (∀ (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)))
        (u v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))),
        (v : G) = c * u * c⁻¹ →
          Multiplicative.toAdd (β v) =
            (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) ∧
      ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)), (c : G) ∈ R ↔ ∃ s : F, α c = slUpper s

end BlockData

section Norm

variable {G : Type} [Group G] {L R : Subgroup G} {n : ℕ} {K : Type} [Field K] [Fintype K] {f : G}

omit [Fintype K] in
theorem slFix_slUpper (σ : K ≃+* K) (s : fixedField σ) :
    slFix σ (slUpper s) = slUpper (s : K) := by
  apply Subtype.ext
  ext i j
  rw [slFix_apply, slUpper_val, slUpper_val]
  fin_cases i <;> fin_cases j <;> simp

theorem NormData.exists_data (N : NormData L R n K f) (hK2 : (2 : K) = 0)
    (hOL : pCoreOf 2 L = blockU L)
    (hTrU : ∀ x ∈ blockU L, (f * x) * (f * x) = 1 → ∃ m ∈ blockU L, m⁻¹ * f * m = f * x)
    (hTrZ : ∀ x ∈ blockZ L, (f * x) * (f * x) = 1 → ∃ m ∈ blockZ L, m⁻¹ * f * m = f * x)
    (hσ : N.σ ≠ 1) : BlockData L R f n := by
  unfold BlockData
  obtain ⟨-, m, hnm, hfixcard⟩ := exists_half_of_twisted hK2 N.A.card_eq N.σ N.hσσ hσ
  have hcardF : Fintype.card (fixedField N.σ) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, ← hfixcard 1 (by simp)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp [mem_fixedField])
  have h2F : (2 : fixedField N.σ) = 0 := by
    apply Subtype.ext
    push_cast
    exact hK2
  obtain ⟨α', hα'1, hα's, hα'k⟩ := N.exists_alphaC hOL hTrU
  obtain ⟨β', hβ'1, hβ's, hβ'k⟩ := N.exists_betaV hTrZ
  have hRα : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
      (c : G) ∈ R ↔ ∃ s : fixedField N.σ, α' c = slUpper s := by
    intro c
    have hP := N.A.mem_P ⟨c, c.2.1⟩
    constructor
    · intro h
      obtain ⟨s, hs⟩ := mem_slUni.1 (hP.1 h)
      have hs0 : N.σ s = s := by
        have h1 : ((slFix N.σ (α' c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 =
            ((N.A.α ⟨c, c.2.1⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
          rw [hα'1 c]
        rw [hs, slUpper_val] at h1
        have h2 : (((α' c : Matrix (Fin 2) (Fin 2) (fixedField N.σ)) 0 1 : fixedField N.σ) : K) =
            s := h1
        rw [← h2]
        exact mem_fixedField.1 ((α' c : Matrix (Fin 2) (Fin 2) (fixedField N.σ)) 0 1).2
      refine ⟨⟨s, mem_fixedField.2 hs0⟩, slFix_injective N.σ ?_⟩
      rw [hα'1 c, slFix_slUpper]
      exact hs
    · rintro ⟨s, hs⟩
      apply hP.2
      rw [← hα'1 c, hs, slFix_slUpper]
      exact slUpper_mem_slUni _
  refine ⟨m, fixedField N.σ, inferInstance, inferInstance, α', β', hnm, hcardF, h2F, hα's, hα'k,
    hβ's, hβ'k, ?_, hRα⟩
  intro c u v hv
  have hβ'v : ∀ (w : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))) (i : Fin 2),
      ((Multiplicative.toAdd (β' w) i : fixedField N.σ) : K) =
        Multiplicative.toAdd (N.A.β ⟨w, w.2.1⟩) i := fun w i => by
    rw [← hβ'1 w]
    rfl
  funext i
  apply Subtype.ext
  have h1 := N.A.β_equiv ⟨c, c.2.1⟩ ⟨u, u.2.1⟩ ⟨v, v.2.1⟩ hv
  have h3 := slFix_mulVec N.σ (α' c) (Multiplicative.toAdd (β' u)) i
  rw [hα'1 c] at h3
  have hvec : Multiplicative.toAdd (N.A.β ⟨u, u.2.1⟩) =
      fun j => ((Multiplicative.toAdd (β' u) j : fixedField N.σ) : K) :=
    funext fun j => (hβ'v u j).symm
  rw [hβ'v v i, h1, hvec, h3]

end Norm

section Group

variable {G : Type} [Group G] {C V : Subgroup G} {F : Type} [Field F]

theorem eq_bot_of_normal_isPGroup_sl2_charTwo [Fintype F] (hF2 : (2 : F) = 0)
    (N : Subgroup SL(2, F)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have hcardF : Even (Nat.card (Fin 2 → F)) := by
    have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast hF2)
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk, ← pow_mul]
    exact (Nat.even_pow' (by have := k.pos; omega)).2 even_two
  have hmod := hN.card_modEq_card_fixedPoints (Fin 2 → F)
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥N (Fin 2 → F)) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, fun n => smul_zero _⟩⟩, inferInstance⟩
  have h2 : Nat.card (Fin 2 → F) % 2 = Nat.card (MulAction.fixedPoints ↥N (Fin 2 → F)) % 2 := hmod
  have h0 : Nat.card (Fin 2 → F) % 2 = 0 := Nat.even_iff.1 hcardF
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w : Fin 2 → F, w ∈ MulAction.fixedPoints ↥N (Fin 2 → F) ∧ w ≠ 0 := by
    by_contra hcon
    have hsub : Subsingleton (MulAction.fixedPoints ↥N (Fin 2 → F)) := ⟨fun x y => by
      apply Subtype.ext
      have hx : (x : Fin 2 → F) = 0 := by
        by_contra h
        exact hcon ⟨x, x.2, h⟩
      have hy : (y : Fin 2 → F) = 0 := by
        by_contra h
        exact hcon ⟨y, y.2, h⟩
      exact hx.trans hy.symm⟩
    have h1 : Nat.card (MulAction.fixedPoints ↥N (Fin 2 → F)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 hsub
    omega
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hfixall : ∀ w : Fin 2 → F, (g : SL(2, F)) • w = w := by
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    obtain ⟨h, hh⟩ := exists_sl2_mulVec_eq hw₀0 hw
    have hconj : h⁻¹ * g * h ∈ N := by
      have := (inferInstance : N.Normal).conj_mem g hg h⁻¹
      simpa [mul_assoc] using this
    have hfix : (h⁻¹ * g * h) • w₀ = w₀ := hw₀ ⟨h⁻¹ * g * h, hconj⟩
    have hhw : h • w₀ = w := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact hh
    calc g • w = g • (h • w₀) := by rw [hhw]
      _ = h • ((h⁻¹ * g * h) • w₀) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      _ = h • w₀ := by rw [hfix]
      _ = w := hhw
  apply sl2_eq_one_of_fix
  intro w
  have := hfixall w
  rwa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at this

theorem pCoreOf_eq_of_data [Fintype F] (hF2 : (2 : F) = 0) (hVC : V ≤ C)
    (hVel : IsElemAbelian 2 V) (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (α : ↥C →* SL(2, F)) (hα : Function.Surjective α) (hαk : ∀ c : ↥C, α c = 1 ↔ (c : G) ∈ V) :
    pCoreOf 2 C = V := by
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hVel.2 x x.2)⟩
  have hCN : C ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_conj_mem hVn
  have hVP : V ≤ pCoreOf 2 C := le_pCoreOf_of_normalizes hVC hCN hV2
  have hPV : pCoreOf 2 C ≤ V := by
    have hPC : pCoreOf 2 C ≤ C := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 C
    have hCP : C ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 C
    have hPn : ((pCoreOf 2 C).subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).2 hCP
    have hP2 : IsPGroup 2 ((pCoreOf 2 C).subgroupOf C) :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 C).of_equiv
        (Subgroup.subgroupOfEquivOfLe hPC).symm
    have : (((pCoreOf 2 C).subgroupOf C).map α).Normal := Subgroup.Normal.map hPn α hα
    have hbot := eq_bot_of_normal_isPGroup_sl2_charTwo hF2 _ (hP2.map α)
    intro x hx
    have hxC : x ∈ C := hPC hx
    have : α ⟨x, hxC⟩ ∈ ((pCoreOf 2 C).subgroupOf C).map α := ⟨⟨x, hxC⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (hαk ⟨x, hxC⟩).1 this
  exact le_antisymm hPV hVP

theorem exists_mem_commutator_of_beta (hF : ∃ a : F, a ≠ 0 ∧ a ≠ 1)
    (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (α : ↥C →* SL(2, F)) (hα : Function.Surjective α)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    ∀ y : Multiplicative (Fin 2 → F), ∃ v : ↥V, (v : G) ∈ ⁅V, C⁆ ∧ β v = y := by
  obtain ⟨a, ha0, ha1⟩ := hF
  have ha1' : a⁻¹ ≠ 1 := fun h => ha1 (inv_eq_one.1 h)
  let g : SL(2, F) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha0]⟩
  have hg : ∀ w : Fin 2 → F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec w = ![a * w 0, a⁻¹ * w 1] := by
    intro w
    ext i
    fin_cases i <;> simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨c, hc⟩ := hα g
  let S : Subgroup (Multiplicative (Fin 2 → F)) := ((⁅V, C⁆).subgroupOf V).map β
  have hSmem : ∀ w : Fin 2 → F,
      Multiplicative.ofAdd (w - ![a * w 0, a⁻¹ * w 1]) ∈ S := by
    intro w
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have hcuV : (c : G) * u * (c : G)⁻¹ ∈ V := hVn c c.2 u u.2
    refine ⟨u * ⟨(c : G) * u * (c : G)⁻¹, hcuV⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · show (u : G) * ((c : G) * u * (c : G)⁻¹)⁻¹ ∈ ⁅V, C⁆
      have := Subgroup.commutator_mem_commutator u.2 c.2
      convert this using 1
      simp [commutatorElement_def, mul_assoc]
    · have h1 := hβe c u ⟨(c : G) * u * (c : G)⁻¹, hcuV⟩ rfl
      have hw : Multiplicative.toAdd (β u) = w := by rw [hu]; rfl
      rw [hc, hg, hw] at h1
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, hw, sub_eq_add_neg]
      rfl
  have hS : ∀ z : Fin 2 → F, Multiplicative.ofAdd z ∈ S := by
    intro z
    have hne0 : (1 - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha1)
    have hne1 : (1 - a⁻¹) ≠ 0 := sub_ne_zero.2 (Ne.symm ha1')
    have h0 : Multiplicative.ofAdd (Pi.single 0 (z 0) : Fin 2 → F) ∈ S := by
      have := hSmem (Pi.single 0 ((1 - a)⁻¹ * z 0))
      convert this using 2
      ext i
      fin_cases i
      · simp
        have h' : (1 - a) * (1 - a)⁻¹ = 1 := mul_inv_cancel₀ hne0
        linear_combination (-(z 0)) * h'
      · simp
    have h1 : Multiplicative.ofAdd (Pi.single 1 (z 1) : Fin 2 → F) ∈ S := by
      have := hSmem (Pi.single 1 ((1 - a⁻¹)⁻¹ * z 1))
      convert this using 2
      ext i
      fin_cases i
      · simp
      · simp
        have h' : (1 - a⁻¹) * (1 - a⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hne1
        linear_combination (-(z 1)) * h'
    have hz : Multiplicative.ofAdd z =
        Multiplicative.ofAdd (Pi.single 0 (z 0) : Fin 2 → F) *
          Multiplicative.ofAdd (Pi.single 1 (z 1) : Fin 2 → F) := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i <;> simp
    rw [hz]
    exact S.mul_mem h0 h1
  intro y
  obtain ⟨v, hv, hvy⟩ := hS (Multiplicative.toAdd y)
  exact ⟨v, Subgroup.mem_subgroupOf.1 hv, by rw [hvy]; rfl⟩

theorem exists_pow_three_sl2 (hF2 : (2 : F) = 0) : ∃ M : SL(2, F), M ^ 3 = 1 ∧ M ≠ 1 := by
  let M : SL(2, F) := ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * hF2⟩
  have hMc : (M : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl
  refine ⟨M, ?_, ?_⟩
  · have hM3 : M * M * M = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hMc,
        Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hF2
    simpa [pow_succ] using hM3
  · intro e
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) e
    simp [M] at this

theorem six_dvd_card_sl2 [Fintype F] (hF2 : (2 : F) = 0) : 6 ∣ Nat.card SL(2, F) := by
  have h2 : 2 ∣ Nat.card SL(2, F) := by
    have h := orderOf_dvd_natCard (slUpper (1 : F))
    have ho : orderOf (slUpper (1 : F)) = 2 := by
      apply orderOf_eq_prime
      · rw [sq, ← slUpper_add, show (1 : F) + 1 = 0 by rw [one_add_one_eq_two]; exact hF2,
          slUpper_zero]
      · intro h1
        exact one_ne_zero (slUpper_injective (h1.trans slUpper_zero.symm))
    rwa [ho] at h
  have h3 : 3 ∣ Nat.card SL(2, F) := by
    obtain ⟨M, hM3, hM1⟩ := exists_pow_three_sl2 hF2
    have h := orderOf_dvd_natCard M
    rwa [orderOf_eq_prime hM3 hM1] at h
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3

theorem perm_four_of_data [Finite G] [Fintype F] (hcardF : Fintype.card F = 2)
    (hF2 : (2 : F) = 0) (hVC : V ≤ C) (hVel : IsElemAbelian 2 V)
    (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (α : ↥C →* SL(2, F)) (hα : Function.Surjective α) (hαk : ∀ c : ↥C, α c = 1 ↔ (c : G) ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβi : ∀ v : ↥V, β v = 1 → v = 1)
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    Nonempty (↥C ≃* Equiv.Perm (Fin 4)) := by
  classical
  have hCN : C ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_conj_mem hVn
  have hVnorm : (V.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).2 hCN
  have hβbij : Function.Bijective β := ⟨(injective_iff_map_eq_one β).2 hβi, hβ⟩
  have hVcard : Nat.card (V.subgroupOf C) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv,
      Nat.card_congr (Equiv.ofBijective β hβbij), Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, hcardF]
    norm_num
  refine CFSG.QuasithinUnique.Unc25Small.perm_four_of_klein (V.subgroupOf C) hVcard ?_ ?_ ?_
  · intro x hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← sq]
    exact hVel.2 _ hx
  · intro g hg
    have hfix : ∀ w : Fin 2 → F, (α g : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
      intro w
      obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd w)
      have hw : Multiplicative.toAdd (β v) = w := by rw [hv]; rfl
      have hcomm : g * (⟨v, hVC v.2⟩ : ↥C) = ⟨v, hVC v.2⟩ * g :=
        hg ⟨v, hVC v.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact v.2)
      have hcomm' : (g : G) * v = v * g := congrArg Subtype.val hcomm
      have := hβe g v v (by
        show (v : G) = (g : G) * v * (g : G)⁻¹
        rw [hcomm']
        group)
      rw [hw] at this
      exact this.symm
    exact Subgroup.mem_subgroupOf.2 ((hαk g).1 (sl2_eq_one_of_fix hfix))
  · have hker : α.ker = V.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    have hrange : α.range = ⊤ := MonoidHom.range_eq_top.2 hα
    have hcard := Subgroup.card_ker_mul_card_range α
    rw [hker, hrange, Subgroup.card_top, hVcard] at hcard
    obtain ⟨k, hk⟩ := six_dvd_card_sl2 hF2
    rw [← hcard, hk]
    exact ⟨k, by ring⟩

end Group

end CFSG.QuasithinUnique.Lin2
