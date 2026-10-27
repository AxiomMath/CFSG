module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KU48RRs

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8 (Xs Rs act dotB mem_Rs dotB_eq_zero_of_mem_Rs Rs_ne_bot)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem vnorm_smul (μ : KF) (w : Fin 4 → KF) :
    vnorm hKF (μ • w) = (μ * hKF.bar μ) * vnorm hKF w := by
  simp only [vnorm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem isoVec_of_tot {R : Submodule KF (Fin 4 → KF)} (hR : ∀ x ∈ R, ∀ y ∈ R, dotB hKF x y = 0)
    {x : Fin 4 → KF} (hx : x ∈ R) (hx0 : x ≠ 0) : IsIsoVec hKF x :=
  ⟨hx0, by rw [vnorm_eq_dotB]; exact hR x hx x hx⟩

open Classical in
@[expose] def rootAny (w : Fin 4 → KF) : Subgroup SU4 :=
  if h : vnorm hKF w = 0 then rootSU w h else ⊥

theorem rootAny_of {w : Fin 4 → KF} (h : vnorm hKF w = 0) : rootAny w = rootSU w h := by
  unfold rootAny
  rw [dif_pos h]

theorem rootAny_smul {w : Fin 4 → KF} (hw : IsIsoVec hKF w) {μ : KF} (hμ : μ ≠ 0) :
    rootAny (μ • w) = rootAny w := by
  have h' : vnorm hKF (μ • w) = 0 := by
    rw [vnorm_smul, hw.2, mul_zero]
  rw [rootAny_of h', rootAny_of hw.2, rootSU_smul hw.2 hμ h']

theorem exists_smul_of_rootAny_eq {a b : Fin 4 → KF} (ha : IsIsoVec hKF a) (hb : IsIsoVec hKF b)
    (h : rootAny a = rootAny b) : ∃ μ : KF, μ ≠ 0 ∧ a = μ • b := by
  haveI : CharP KF 2 := hKF.charP
  rw [rootAny_of ha.2, rootAny_of hb.2] at h
  have h1 : tvSU a ha.2 1 (map_one _) ∈ rootSU a ha.2 := tvSU_mem a ha.2 1 (map_one _)
  rw [h] at h1
  obtain ⟨d, hd, hmat⟩ := mem_rootSU.1 h1
  rw [coe_tvSU] at hmat
  have hW : wMat hKF a = d • wMat hKF b := by
    have h2 : (1 : Matrix (Fin 4) (Fin 4) KF) + wMat hKF a = 1 + d • wMat hKF b := by
      simpa [tvMat] using hmat
    exact add_left_cancel h2
  have hent : ∀ i j, a i * hKF.bar (a j) = d * (b i * hKF.bar (b j)) := fun i j => by
    have := congrFun (congrFun hW i) j
    simpa [wMat] using this
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha.1 (funext hc)
  have hbar_ak : hKF.bar (a k) ≠ 0 := by
    rw [bar_pow]
    exact pow_ne_zero _ hk
  have hkk := hent k k
  have hLHS : a k * hKF.bar (a k) ≠ 0 := mul_ne_zero hk hbar_ak
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkk
    exact hLHS hkk
  have hbk : b k ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero, mul_zero] at hkk
    exact hLHS hkk
  have hbar_bk : hKF.bar (b k) ≠ 0 := by
    rw [bar_pow]
    exact pow_ne_zero _ hbk
  refine ⟨d * hKF.bar (b k) / hKF.bar (a k), ?_, funext fun i => ?_⟩
  · exact div_ne_zero (mul_ne_zero hd0 hbar_bk) hbar_ak
  · simp only [Pi.smul_apply, smul_eq_mul]
    have hi := hent i k
    field_simp
    linear_combination hi

@[expose] def Om (R : Submodule KF (Fin 4 → KF)) : Set (Subgroup SU4) :=
  rootAny '' {w | w ∈ R ∧ w ≠ 0}

theorem Om_finite (R : Submodule KF (Fin 4 → KF)) : (Om R).Finite :=
  Set.Finite.image _ (Set.toFinite _)

theorem rootAny_mem_Om {R : Submodule KF (Fin 4 → KF)} {w : Fin 4 → KF} (hw : w ∈ R) (hw0 : w ≠ 0) :
    rootAny w ∈ Om R :=
  Set.mem_image_of_mem rootAny ⟨hw, hw0⟩

theorem card_KF : Nat.card KF = 64 := by
  rw [hKF.card]
  norm_num

theorem card_Om_mod (R : Submodule KF (Fin 4 → KF)) (hR : ∀ x ∈ R, ∀ y ∈ R, dotB hKF x y = 0)
    (hne : R ≠ ⊥) : Nat.card (Om R) = 1 ∨ Nat.card (Om R) = 65 := by
  classical
  have hle := finrank_le_two_of_isotropic R hR
  have hpos : Module.finrank KF R ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  let F : {v : R // v ≠ 0} → ↥(Om R) := fun v =>
    ⟨rootAny (v.1 : Fin 4 → KF), rootAny_mem_Om v.1.2 (fun h => v.2 (Subtype.ext h))⟩
  have hF : ∀ (a b : {v : R // v ≠ 0}) (t : KF), a = t • (b : R) → F a = F b := by
    intro a b t hab
    have ht : t ≠ 0 := by
      rintro rfl
      apply a.2
      rw [hab, zero_smul]
    have hval : (a : Fin 4 → KF) = t • (b : Fin 4 → KF) := by
      rw [hab]
      rfl
    apply Subtype.ext
    show rootAny (a : Fin 4 → KF) = rootAny (b : Fin 4 → KF)
    rw [hval, rootAny_smul (isoVec_of_tot hR b.1.2 (fun h => b.2 (Subtype.ext h))) ht]
  let Ψ : Projectivization KF R → ↥(Om R) := Projectivization.lift F hF
  have hΨinj : Function.Injective Ψ := by
    intro p q
    induction p using Projectivization.ind with
    | h a ha =>
      induction q using Projectivization.ind with
      | h b hb =>
        intro hab
        have h1 : rootAny (a : Fin 4 → KF) = rootAny (b : Fin 4 → KF) := congrArg Subtype.val hab
        obtain ⟨μ, hμ, hμab⟩ :=
          exists_smul_of_rootAny_eq (isoVec_of_tot hR a.2 (fun h => ha (Subtype.ext h)))
            (isoVec_of_tot hR b.2 (fun h => hb (Subtype.ext h))) h1
        rw [Projectivization.mk_eq_mk_iff]
        refine ⟨Units.mk0 μ hμ, ?_⟩
        rw [Units.smul_def, Units.val_mk0]
        apply Subtype.ext
        rw [Submodule.coe_smul]
        exact hμab.symm
  have hΨsurj : Function.Surjective Ψ := by
    rintro ⟨X, hX⟩
    obtain ⟨w, ⟨hwR, hw0⟩, rfl⟩ := hX
    have hv : (⟨w, hwR⟩ : R) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
    exact ⟨Projectivization.mk KF (⟨w, hwR⟩ : R) hv, rfl⟩
  have hcardEq : Nat.card (Projectivization KF R) = Nat.card (Om R) :=
    Nat.card_congr (Equiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩)
  have hdim : Module.finrank KF R = 1 ∨ Module.finrank KF R = 2 := by omega
  rcases hdim with h1 | h1
  · have h2 := Projectivization.card_of_finrank KF R h1
    simp only [Finset.sum_range_one, pow_zero] at h2
    left
    rw [← hcardEq, h2]
  · have h2 := Projectivization.card_of_finrank KF R h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, card_KF] at h2
    right
    rw [← hcardEq, h2]
    norm_num

theorem exists_fixed_of_card {P : Type} [Group P] {X : Type} [MulAction P X] [Finite X]
    (hP : IsPGroup 3 P) (hcard : Nat.card X % 3 ≠ 0) : ∃ x : X, ∀ g : P, g • x = x := by
  have hmod := hP.card_modEq_card_fixedPoints X
  have hne : (MulAction.fixedPoints P X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hem
    have h0 : Nat.card (MulAction.fixedPoints P X) = 0 := by
      rw [hem]
      simp
    rw [h0] at hmod
    exact hcard (by simpa [Nat.ModEq] using hmod)
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, fun g => MulAction.mem_fixedPoints.1 hx g⟩

theorem Rs_totIso (W : Subgroup (GL (Fin 4) KF))
    (hWu : ∀ w ∈ W, ((w : Matrix (Fin 4) (Fin 4) KF).map hKF.bar)ᵀ * (w : Matrix (Fin 4) (Fin 4) KF) = 1) :
    ∀ x ∈ Rs W, ∀ y ∈ Rs W, dotB hKF x y = 0 :=
  fun x hx y hy => dotB_eq_zero_of_mem_Rs hKF hWu hx ((mem_Rs.1 hy).1)

theorem Om_map_mem (W : Subgroup (GL (Fin 4) KF))
    (hWu : ∀ w ∈ W, ((w : Matrix (Fin 4) (Fin 4) KF).map hKF.bar)ᵀ * (w : Matrix (Fin 4) (Fin 4) KF) = 1)
    (α : MulAut SU4) (g : SU4) (φ : KF ≃+* KF)
    (hα : ∀ x : SU4, ((α x : SU4) : GL (Fin 4) KF) =
      (g : GL (Fin 4) KF) * glAut φ (x : GL (Fin 4) KF) * (g : GL (Fin 4) KF)⁻¹)
    (hW1 : ∀ t ∈ W, ∃ t' ∈ W, (g : GL (Fin 4) KF) * glAut φ t' * (g : GL (Fin 4) KF)⁻¹ = t)
    (hW2 : ∀ t ∈ W, (g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹ ∈ W)
    {X : Subgroup SU4} (hX : X ∈ Om (Rs W)) : X.map α.toMonoidHom ∈ Om (Rs W) := by
  obtain ⟨w, ⟨hwR, hw0⟩, rfl⟩ := hX
  have hwiso : IsIsoVec hKF w := isoVec_of_tot (Rs_totIso W hWu) hwR hw0
  have hsFmem : sF g φ w ∈ Rs W := sF_mem_Rs g φ W hW1 hW2 hwR
  have hsF0 : sF g φ w ≠ 0 := sF_ne_zero g φ hw0
  have hmap := rootSU_map α g φ hα hwiso
  rw [rootAny_of hwiso.2, hmap, ← rootAny_of (isIsoVec_sF g φ hwiso).2]
  exact rootAny_mem_Om hsFmem hsF0

end CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R
