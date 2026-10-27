module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam
public import CFSG.ClassicalInvolution.Q3.TL4MF163Res
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace MF163

open CFSG CFSG.Open CFSG.Blueprint CFSG.GorensteinWalter

theorem psl2_of_lieModel {Y : Type} [Group Y] {p f : ℕ} (h : LieModel Y .PSL 2 p f) :
    p.Prime ∧ 4 ≤ p ^ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rcases h with ⟨-, ⟨hp, hf, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨hp, ?_, F, inferInstance, inferInstance, hF,
      ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    by_contra hlt
    interval_cases hpf : p ^ f
    · exact h22 rfl
    · exact h23 rfl
  all_goals exact absurd h0 (by norm_num)

variable {X : Type} [Group X] [Finite X]

theorem eq_one_or_conj_of_quat_psl2 [IsSimpleGroup (genFittingFStar X)] {p f : ℕ}
    (hp2 : p ≠ 2) (hl : LieModel (TL4.FStarQuot X) .PSL 2 p f) (ι : QuaternionGroup 2 →* X)
    (hι : Function.Injective ι) (β : MulAut X) (hβ2 : β * β = 1) (hβι : ∀ g, β (ι g) = ι g) :
    β = 1 ∨ β = MulAut.conj (ι (QuaternionGroup.a 2)) := by
  obtain ⟨hp, h4, F, _, _, hFcard, ⟨e⟩⟩ := psl2_of_lieModel hl
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h4
    · exact h
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hFcard⟩
  have hcard : 3 < Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFcard])
    intro h0
    have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p 2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  set N := genFittingFStar X with hN
  have hNn : N.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal X
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ :=
      ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
        (by omega) (by omega)
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
    refine ⟨a, b, fun hab => hxy ?_⟩
    have := congrArg (fun g => e (QuotientGroup.mk g : TL4.FStarQuot X)) hab
    simp only [QuotientGroup.mk_mul, map_mul] at this
    rwa [ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have hZ : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hC : Subgroup.centralizer (N : Set X) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  let ψ : ↥N ≃* PSL2 F :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let θ : PGammaL2 F ≃* MulAut (PSL2 F) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 F hK hcard) ⟨pGammaL2ToMulAutPSL2_injective F hK hcard,
      pGammaL2ToMulAutPSL2_surjective F hFcard hK hcard⟩
  let Φ : X →* MulAut (PSL2 F) := (MulAut.congr ψ).toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hΦ : ∀ (x : X) (n : N), Φ x (ψ n) = ψ (MulAut.conjNormal x n) := by
    intro x n
    simp [Φ, MulAut.congr_apply]
  have hΦi : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hΦ x ⟨n, hn⟩
    rw [hx, MulAut.one_apply] at h1
    have h3 := congrArg Subtype.val (ψ.injective h1)
    rw [MulAut.conjNormal_apply] at h3
    calc n * x = (x * n * x⁻¹) * x := by rw [← h3]
      _ = x * n := by group
  have hmap := map_eq_of_centralizer_eq_bot hC β
  let βN : MulAut N := restrictAut β hmap
  let βt : MulAut (PSL2 F) := MulAut.congr ψ βN
  have hβt : ∀ n : N, βt (ψ n) = ψ (βN n) := fun n => by simp [βt, MulAut.congr_apply]
  have hrel : ∀ x : X, βt * Φ x = Φ (β x) * βt := by
    intro x
    ext w
    obtain ⟨n, rfl⟩ := ψ.surjective w
    rw [MulAut.mul_apply, MulAut.mul_apply, hΦ, hβt, hβt, hΦ]
    congr 1
    apply Subtype.ext
    rw [coe_restrictAut, MulAut.conjNormal_apply, MulAut.conjNormal_apply, coe_restrictAut,
      map_mul, map_mul, map_inv]
  let ρ : QuaternionGroup 2 →* PGammaL2 F := θ.symm.toMonoidHom.comp (Φ.comp ι)
  have hρ : ρ (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have h1 : Φ (ι (QuaternionGroup.a 2)) = 1 := by
      have := congrArg θ h
      simpa [ρ] using this
    have h3 : ι (QuaternionGroup.a 2) = 1 := hΦi (by rw [h1, map_one])
    exact absurd (hι (h3.trans (map_one ι).symm)) (by decide)
  have hb : θ.symm βt * θ.symm βt = 1 := by
    have h1 : βN * βN = 1 := by
      ext n
      rw [MulAut.mul_apply, coe_restrictAut, coe_restrictAut, ← MulAut.mul_apply, hβ2,
        MulAut.one_apply, MulAut.one_apply]
    have h3 : βt * βt = 1 := by
      simp only [βt]
      rw [← map_mul, h1, map_one]
    rw [← map_mul, h3, map_one]
  have hbρ : ∀ g, θ.symm βt * ρ g = ρ g * θ.symm βt := by
    intro g
    have h1 := hrel (ι g)
    rw [hβι g] at h1
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h1]
  rcases pgammaL2_eq_of_quat_hom hK h2 ρ hρ hb hbρ with h | h
  · left
    have hβt1 : βt = 1 := by
      have := congrArg θ h
      simpa using this
    have hβN : βN = 1 := (MulAut.congr ψ).injective (hβt1.trans (map_one _).symm)
    refine eq_of_eqOn hC (map_eq_of_centralizer_eq_bot hC 1) fun n hn => ?_
    have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : X)) hβN
    simpa [βN, coe_restrictAut] using this
  · right
    have hβt1 : βt = Φ (ι (QuaternionGroup.a 2)) := by
      have := congrArg θ h
      simpa [ρ] using this
    refine eq_of_eqOn hC (map_eq_of_centralizer_eq_bot hC _) fun n hn => ?_
    have h1 := congrArg (fun φ : MulAut (PSL2 F) => φ (ψ ⟨n, hn⟩)) hβt1
    simp only [hβt, hΦ] at h1
    have h3 := congrArg Subtype.val (ψ.injective h1)
    rw [coe_restrictAut, MulAut.conjNormal_apply] at h3
    rw [h3, MulAut.conj_apply]

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
