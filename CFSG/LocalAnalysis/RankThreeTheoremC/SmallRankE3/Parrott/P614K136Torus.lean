module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Parab
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open Matrix Subgroup
open scoped MatrixGroups

theorem not_three_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hpos : 0 < 4 ^ k := by positivity
  rw [h1]
  omega

theorem eq_one_of_pow_three {n : ℕ} (hn : Odd n) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {a : F} (ha : a ^ 3 = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  set u : Fˣ := Units.mk0 a ha0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [hu, ha])
  have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have h2 : orderOf u ∣ 2 ^ n - 1 := by
    rw [← hF, ← Nat.card_units]
    exact orderOf_dvd_natCard u
  have hcop : Nat.Coprime 3 (2 ^ n - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_three_dvd_two_pow_sub_one hn)
  have hou : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at hou
  have := congrArg Units.val hou
  simpa [hu] using this

variable {F : Type*} [Field F]

theorem center_SL3_eq_bot (hF3 : ∀ a : F, a ^ 3 = 1 → a = 1) :
    Subgroup.center SL(3, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  rw [hF3 r hr, map_one] at hA'
  exact Subtype.ext hA'.symm

@[expose] noncomputable def pslEquivSL (hF3 : ∀ a : F, a ^ 3 = 1 → a = 1) :
    PSL(3, F) ≃* SL(3, F) :=
  (QuotientGroup.quotientMulEquivOfEq (center_SL3_eq_bot hF3)).trans QuotientGroup.quotientBot

@[expose] noncomputable def slFieldEquiv {L : Type*} [Field L] (e : F ≃+* L) :
    SL(3, F) ≃* SL(3, L) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext g i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext g i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem bijective_toGL_three_two :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL : SL(3, ZMod 2) →* GL (Fin 3) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    obtain ⟨u, hu⟩ := g.isUnit.map Matrix.detMonoidHom
    have hu' : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = u := hu.symm
    rw [hu', Subsingleton.elim u 1, Units.val_one]
  exact ⟨mkSL (ZMod 2) (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) hdet, Units.ext rfl⟩

@[expose] noncomputable def pslThreeTwoEquivGL32 :
    PSL(3, GaloisField 2 1) ≃* GL (Fin 3) (ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF3 : ∀ a : GaloisField 2 1, a ^ 3 = 1 → a = 1 := fun a ha =>
    eq_one_of_pow_three (by decide : Odd 1) (by rw [GaloisField.card 2 1 one_ne_zero, pow_one]) ha
  exact (pslEquivSL hF3).trans ((slFieldEquiv (GaloisField.equivZmodP 2).toRingEquiv).trans
    (MulEquiv.ofBijective _ bijective_toGL_three_two))

@[expose] noncomputable def torusDiag : Fˣ × Fˣ →* SL(3, F) where
  toFun st := mkSL F (Matrix.diagonal ![(st.1 : F), (st.2 : F), (((st.1 * st.2)⁻¹ : Fˣ) : F)])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons]
      rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  map_one' := by
    apply Subtype.ext
    rw [coe_mkSL, coe_SL_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  map_mul' a b := by
    apply Subtype.ext
    rw [coe_SL_mul, coe_mkSL, coe_mkSL, coe_mkSL, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem torusDiag_injective : Function.Injective (torusDiag (F := F)) := by
  intro a b h
  have h0 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp only [torusDiag, MonoidHom.coe_mk, OneHom.coe_mk, coe_mkSL, Matrix.diagonal_apply_eq,
    cons_val_zero, cons_val_one, head_cons] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem two_le_pRank [Finite F] {K : Type*} [Group K] [Finite K] (σ : K ≃* SL(3, F)) {f : ℕ}
    (hf : f.Prime) (hfd : f ∣ Nat.card F - 1) : 2 ≤ CFSG.Open.pRank f (⊤ : Subgroup K) := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) f (by rwa [Nat.card_units])
  set Z : Subgroup Fˣ := zpowers ζ with hZ
  let θ : Z × Z →* K :=
    σ.symm.toMonoidHom.comp (torusDiag.comp (MonoidHom.prodMap Z.subtype Z.subtype))
  have hθ : Function.Injective θ := by
    intro a b h
    have h1 := torusDiag_injective (σ.symm.injective h)
    simp only [MonoidHom.prodMap, MonoidHom.coe_prodMap, Prod.map, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype] at h1
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  have hZcard : Nat.card Z = f := by rw [hZ, Nat.card_zpowers, hζ]
  have hpow : ∀ a : Z × Z, a ^ f = 1 := fun a => by
    have h1 : a.1 ^ f = 1 := by rw [← hZcard]; exact pow_card_eq_one'
    have h2 : a.2 ^ f = 1 := by rw [← hZcard]; exact pow_card_eq_one'
    exact Prod.ext h1 h2
  have hcardA : Nat.card (Z × Z) = f ^ 2 := by rw [Nat.card_prod, hZcard, pow_two]
  exact CFSG.SectionRank.le_pRank_of_injective hf.one_lt (fun a b => mul_comm a b) hpow hcardA θ hθ
    le_top

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136
