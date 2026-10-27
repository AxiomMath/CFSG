module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGResCls
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinMod
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearAut
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinN
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinS
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (perfectInLayer_of_congr perfectInLayer_projectiveSL)

private theorem linAsm_conj_inj {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro a ha
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have h := congrArg (fun α : MulAut R => α g) (MonoidHom.mem_ker.1 ha)
  simp only [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private theorem linAsm_noTorsion {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (h3 : ¬ 3 ∣ n ∨ ¬ 3 ∣ Nat.card F - 1) : ∀ z ∈ (proj n F).ker, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  rw [ker_proj] at hz
  obtain ⟨c, hcn, hzc⟩ := mem_scalars.1 hz
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hc3 : c ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← Matrix.scalar_inj (n := Fin n), map_pow, ← hzc,
      ← Matrix.SpecialLinearGroup.coe_pow, hz3, Matrix.SpecialLinearGroup.coe_one, map_one])
  obtain ⟨m, hm, hcm⟩ : ∃ m, Nat.Coprime 3 m ∧ c ^ m = 1 := by
    rcases h3 with h3 | h3
    · exact ⟨n, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, hcn⟩
    · refine ⟨Nat.card Fˣ, ?_, pow_card_eq_one'⟩
      rw [Nat.card_units]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hc1 := pow_gcd_eq_one.2 ⟨hc3, hcm⟩
  rw [Nat.Coprime.gcd_eq_one hm, pow_one] at hc1
  exact Subtype.ext (by rw [hzc, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one])

theorem SG.exists_fix_of_linCore {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] (Θ : G ≃* projectiveSL n F) {X : Subgroup (MulAut G)}
    (hXA : ∀ ε ∈ X, MulAut.congr Θ ε ∈ Set.range (conjAut n F)) (hX : IsElemAbelian 3 X)
    (h3 : ¬ 3 ∣ n ∨ ¬ 3 ∣ Nat.card F - 1) {δ : MulAut G} (hδ : δ ∈ X)
    (hcore : ∀ Bt : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), (∀ y ∈ Bt, y ^ 3 = 1) →
      (∀ y ∈ Bt, ∀ z ∈ Bt, y * z = z * y) → Nat.card Bt = Nat.card X → ∀ d ∈ Bt,
      ∃ A Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), IsSimpleGroup A ∧
        (∃ u w : A, u * w ≠ w * u) ∧ 3 ∣ Nat.card A ∧ Y ≤ Bt ∧ d ∈ Y ∧ Y.relIndex Bt ≤ 3 ∧
        ∀ y ∈ Y, ∀ z ∈ A, y * z = z * y) :
    ∃ A : Subgroup G, A ≤ fixSubgroup δ ∧ IsSimpleGroup A ∧ (∃ u w : A, u * w ≠ w * u) ∧
      3 ∣ Nat.card A ∧ ∃ Y : Subgroup (MulAut G), Y.relIndex X ≤ 3 ∧
        ∀ ε ∈ Y, A ≤ fixSubgroup ε := by
  obtain ⟨g, hg⟩ : ∃ g : projectiveSL n F →* MulAut G,
      g = (MulAut.congr Θ.symm).toMonoidHom.comp MulAut.conj := ⟨_, rfl⟩
  have hgi : Function.Injective g := by
    rw [hg]
    exact (MulAut.congr Θ.symm).injective.comp
      (linAsm_conj_inj (CFSG.EvenSmallLie.UnitarySix.YamadaInputs.center_projectiveSL_eq_bot hn))
  have hfix : ∀ s z : Matrix.SpecialLinearGroup (Fin n) F, s * z = z * s →
      Θ.symm (proj n F z) ∈ fixSubgroup (g (proj n F s)) := fun s z hsz => by
    rw [mem_fixSubgroup, hg]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hsz, mul_inv_cancel_right]
  have hXg : X ≤ g.range := fun ε hε => by
    obtain ⟨A, hA⟩ := hXA ε hε
    obtain ⟨s, hs⟩ := SG.conjAut_inner_of_cube hn h3 (A := A)
      (by rw [hA, ← map_pow, hX.2 ε hε, map_one])
    refine MonoidHom.mem_range.2 ⟨proj n F s, ?_⟩
    rw [hg, MonoidHom.comp_apply, ← hs, hA]
    ext y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  have hXe : IsElemAbelian 3 (X.comap g) := by
    have := hX.1
    refine ⟨⟨⟨fun a b => Subtype.ext (hgi ?_)⟩⟩, fun y hy => hgi (by
      rw [map_pow, hX.2 (g y) hy, map_one])⟩
    simpa using congrArg Subtype.val (mul_comm' (⟨g a, a.2⟩ : X) ⟨g b, b.2⟩)
  obtain ⟨Bt, hBm, -, hBe, hBc⟩ := CFSG.StandardType.TableBUE.exists_lift_of_noTorsion (proj n F)
    (proj_surjective n F) Nat.prime_three (linAsm_noTorsion hn h3) hXe
  have hBX : Bt.map (g.comp (proj n F)) = X := by
    rw [← Subgroup.map_map, hBm, Subgroup.map_comap_eq_self hXg]
  obtain ⟨p, rfl⟩ := hXg hδ
  obtain ⟨d, hdB, rfl⟩ : p ∈ Bt.map (proj n F) := by rw [hBm]; exact hδ
  have := hBe.1
  obtain ⟨A', Y', hs, ⟨u, w, huw⟩, h3A, -, hdY, hYi, hYA⟩ := hcore Bt (fun y hy => hBe.2 y hy)
    (fun y hy z hz => by simpa using congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Bt) ⟨z, hz⟩))
    (by rw [hBc, ← Subgroup.card_map_of_injective hgi, Subgroup.map_comap_eq_self hXg]) d hdB
  haveI := hs
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A' →* G, ψ = (Θ.symm.toMonoidHom.comp (proj n F)).comp A'.subtype :=
    ⟨_, rfl⟩
  have hψA : ∀ z : A', ψ z = Θ.symm (proj n F z) := fun z => by rw [hψ]; rfl
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.Normal.eq_bot_or_eq_top ψ.ker).resolve_right fun htop => huw (Subtype.ext ?_)
    have hu : Θ.symm (proj n F u) = 1 :=
      (hψA u).symm.trans (MonoidHom.mem_ker.1 (by rw [htop]; exact Subgroup.mem_top u))
    exact (Subgroup.mem_center_iff.1 (scalars_le_center n F
      (proj_eq_one_iff.1 ((MulEquiv.map_eq_one_iff _).1 hu))) (w : _)).symm
  let eA := MonoidHom.ofInjective hψi
  refine ⟨ψ.range, ?_, eA.symm.isSimpleGroup, ⟨eA u, eA w, fun h => huw (eA.injective (by
    rw [map_mul, map_mul]; exact h))⟩, (Nat.card_congr eA.toEquiv) ▸ h3A,
    Y'.map (g.comp (proj n F)), ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [hψA]
    exact hfix d z (hYA d hdY z z.2)
  · rw [← hBX, ← Subgroup.relIndex_comap]
    refine (Subgroup.relIndex_le_of_le_left (Subgroup.le_comap_map _ Y') ?_).trans hYi
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, rfl⟩
    rw [hψA]
    exact hfix y z (hYA y hy z z.2)

theorem qsF3ResLin_holds : QSF3ResLin := by
  intro Ω _ _ S B T x D K lab h hcat hB hlab _ h3 hcl
  have hcase := SG.resLin_rank h3 hcl
  obtain ⟨n, F, _, _, Θ, hF, hnA, hnD, hΘ⟩ := SG.linModel_of_innLabel h hlab
    (hcase.elim (fun h' => .inl h'.1) fun h' => h'.elim (fun h' => .inl h'.1) fun h' =>
      .inr ⟨h'.1, h'.2.2⟩)
  haveI : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hc := h.cfg
  obtain ⟨hDB, -⟩ := hc.std
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  obtain ⟨d, hdD, hdx⟩ := SG.exists_mem_D_not_zpowers h
  obtain ⟨hXe, hXc⟩ := SG.card_map_chevAut h hB
  set X := (B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)
  have hXA : ∀ ε ∈ X, MulAut.congr Θ ε ∈ Set.range (conjAut n F) := by
    rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
    exact hΘ b (Subgroup.mem_subgroupOf.1 hb) hbN
  obtain ⟨hn3, h3n, hcore⟩ : 3 ≤ n ∧ (¬ 3 ∣ n ∨ ¬ 3 ∣ Nat.card F - 1) ∧
      ∀ Bt : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), (∀ y ∈ Bt, y ^ 3 = 1) →
        (∀ y ∈ Bt, ∀ z ∈ Bt, y * z = z * y) → Nat.card Bt = Nat.card X → ∀ e ∈ Bt,
        ∃ A Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), IsSimpleGroup A ∧
          (∃ u w : A, u * w ≠ w * u) ∧ 3 ∣ Nat.card A ∧ Y ≤ Bt ∧ e ∈ Y ∧ Y.relIndex Bt ≤ 3 ∧
          ∀ y ∈ Y, ∀ z ∈ A, y * z = z * y := by
    rcases hcase with ⟨ht, hm, hr3, -⟩ | ⟨ht, hp, hr5, -⟩ | ⟨ht, hm, -⟩
    · have hn := hnA ht
      exact ⟨by omega, .inl (by omega), fun Bt hB3 hBc _ e he =>
        SG.exists_sl2_split (by omega) (by rw [hF]; exact hm) hB3 hBc he⟩
    · have hn := hnA ht
      exact ⟨by omega, .inr (by rw [hF]; omega), fun Bt hB3 hBc hBX e he =>
        SG.exists_sl2_nonsplit (by rw [hF]; exact hp) hB3 hBc (by rw [hBX, hXc]; norm_num) he⟩
    · have hn := hnD ht
      exact ⟨by omega, .inl (by omega), fun Bt hB3 hBc _ e he =>
        SG.exists_sl2_split (by omega) (by rw [hF]; exact hm) hB3 hBc he⟩
  have hdX : chevAut 3 S ⟨d, hSN d⟩ ∈ X :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hDB hdD))
  obtain ⟨A, hAd, hA, hnc, h3A, Y, hY, hYA⟩ :=
    SG.exists_fix_of_linCore hn3 Θ hXA hXe h3n hdX hcore
  have hd3 := chevAut_pow_eq_one 3 S (hSN d) (hc.elem.2 d (hDB hdD))
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hpl : PerfectInLayer (chevAut 3 S ⟨d, hSN d⟩) :=
    perfectInLayer_of_congr Θ _ (perfectInLayer_projectiveSL hn3 Nat.prime_three (by norm_num)
      (by rw [Nat.cast_ofNat, show (3 : F) = 2 + 1 by norm_num, h2, zero_add]; exact one_ne_zero)
      _ (by rw [← map_pow, hd3, map_one]))
  haveI := hA
  exact SG.false_of_simple_fix_relIndex h hcat hB (hSN d)
    (SG.glaLayer_fixSubgroup_chevAut h hdD hdx (hSN d)) hpl hAd hnc h3A hY hYA

end CFSG.LocalAnalysis.GLTheoremA.S265

end
