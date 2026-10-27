module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6POmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_exists_signChange_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (g : OGroup Q)
    (hdiag : ∀ o, ∃ s : ZMod 3, s * s = 1 ∧
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b o) = s • fr.b o) :
    ∃ J : Finset ι, g = fr.signChange J := by
  choose s hs hgs using hdiag
  have hs' : ∀ o, s o = 1 ∨ s o = -1 := fun o => by
    have h := hs o
    revert h
    generalize s o = x
    revert x
    decide
  have h13 : (1 : ZMod 3) ≠ -1 := by decide
  refine ⟨Finset.univ.filter (fun o => s o = -1), ?_⟩
  apply Subtype.ext
  apply fr.b.ext'
  intro o
  rw [fr.signChange_basis, hgs o]
  rcases hs' o with h | h
  · have hn : o ∉ Finset.univ.filter (fun o => s o = -1) := by simp [h, h13]
    rw [if_neg hn, h, one_smul]
  · have hm : o ∈ Finset.univ.filter (fun o => s o = -1) := by simp [h]
    rw [if_pos hm, h, neg_one_smul]

theorem fg_eq_ffB0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (B : Subgroup (OGroup Q)) (hΩ : B ≤ omegaGroup hQ) (hcard : Nat.card B = 16)
    (hdiag : ∀ g ∈ B, ∀ o, ∃ s : ZMod 3, s * s = 1 ∧
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b o) = s • fr.b o) : B = ffB0p fr := by
  have hle : B ≤ ffB0p fr := by
    intro g hg
    obtain ⟨J, hJ⟩ := fg_exists_signChange_eq fr g (hdiag g hg)
    have hmem : fr.pOrth 1 * fr.signChange J ∈ omegaGroup hQ := by
      rw [fr.pOrth_one, one_mul, ← hJ]
      exact hΩ hg
    rw [ff6p_mem_omega_iff hQ fr 1 J] at hmem
    have hnone : none ∉ J := fun h => by
      have h1 := hmem.1.mp h
      rw [Equiv.Perm.sign_one] at h1
      exact absurd h1 (by decide)
    refine ⟨J, hnone, ?_, hJ⟩
    have h2 := hmem.2
    rwa [Finset.erase_eq_of_notMem hnone] at h2
  haveI : Finite ↥(ffB0p fr) := Nat.finite_of_card_ne_zero (by rw [ffB0p_card]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [ffB0p_card, hcard])

theorem fg_polar_sim {ρ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ} (hρ : IsSimilitude Q ρ c) (x y : V) :
    QuadraticMap.polar Q (ρ x) (ρ y) = (c : ZMod 3) * QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]
  rw [← map_add, hρ, hρ, hρ, mul_sub, mul_sub]

theorem fg_exists_similitude (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {a : ZMod 3} (ha : a ≠ 0) :
    ∃ ρ : V ≃ₗ[ZMod 3] V, ∀ v, Q (ρ v) = a * Q v := by
  have h : a = 1 ∨ a = -1 := by
    revert ha
    generalize a = x
    revert x
    decide
  rcases h with rfl | rfl
  · exact ⟨1, fun v => by simp⟩
  · obtain ⟨ρ, hρ⟩ := (exists_isSimilitude_neg_one_iff hQ).mpr (by rw [hdim]; decide)
    exact ⟨ρ, fun v => by simpa using hρ v⟩

theorem fg_conj_E16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (B : Subgroup (OGroup Q)) (hΩ : B ≤ omegaGroup hQ) (hcard : Nat.card B = 16)
    (b : Module.Basis (Option (Fin 5)) (ZMod 3) V) {a : ZMod 3} (ha : a ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (hnone : Q (b none) = -a) (hsome : ∀ i : Fin 5, Q (b (some i)) = a)
    (hdiag : ∀ g ∈ B, ∀ o, ∃ s : ZMod 3, s * s = 1 ∧
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (b o) = s • b o) :
    ∃ (γ : simGroup Q) (fr : PFrame Q (Option (Fin 5)) ffC),
      B = (ffB0p fr).map (simAct Q γ).toMonoidHom := by
  have haa : a * a = 1 := by
    revert ha
    generalize a = x
    revert x
    decide
  obtain ⟨ρ, hρ⟩ := fg_exists_similitude hQ hdim ha
  have hsim : IsSimilitude Q ρ (Units.mk0 a ha) := hρ
  obtain ⟨fr, hfr⟩ : ∃ fr : PFrame Q (Option (Fin 5)) ffC, ∀ o, fr.b o = ρ (b o) :=
    ⟨{ b := b.map ρ
       norm := fun o => by
         rw [Module.Basis.map_apply, hρ]
         cases o with
         | none => rw [hnone, mul_neg, haa]; rfl
         | some i => rw [hsome i, haa]; rfl
       orth := fun i j hij => by
         rw [Module.Basis.map_apply, Module.Basis.map_apply, fg_polar_sim hsim, horth i j hij,
           mul_zero] }, fun o => Module.Basis.map_apply b ρ o⟩
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  let γ0 : simGroup Q := ⟨ρ, Units.mk0 a ha, hsim⟩
  have hB'Ω : B.map (simAct Q γ0).toMonoidHom ≤ omegaGroup hQ := by
    rintro _ ⟨t, ht, rfl⟩
    exact ff_simAct_mem_omegaGroup hQ h2 γ0 (hΩ ht)
  have hB'card : Nat.card ↥(B.map (simAct Q γ0).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (simAct Q γ0).injective, hcard]
  have hB'diag : ∀ g ∈ B.map (simAct Q γ0).toMonoidHom, ∀ o, ∃ s : ZMod 3, s * s = 1 ∧
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b o) = s • fr.b o := by
    rintro _ ⟨t, ht, rfl⟩ o
    obtain ⟨s, hs, hts⟩ := hdiag t ht o
    refine ⟨s, hs, ?_⟩
    rw [hfr o]
    show ρ (((t : OGroup Q) : V ≃ₗ[ZMod 3] V) (ρ.symm (ρ (b o)))) = s • ρ (b o)
    rw [LinearEquiv.symm_apply_apply, hts, map_smul]
  have hBeq : B.map (simAct Q γ0).toMonoidHom = ffB0p fr :=
    fg_eq_ffB0p hQ fr _ hB'Ω hB'card hB'diag
  refine ⟨γ0⁻¹, fr, ?_⟩
  rw [← hBeq, Subgroup.map_map]
  have hcomp : (simAct Q γ0⁻¹).toMonoidHom.comp (simAct Q γ0).toMonoidHom =
      MonoidHom.id (OGroup Q) := by
    apply MonoidHom.ext
    intro t
    show simAct Q γ0⁻¹ (simAct Q γ0 t) = t
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  rw [hcomp, Subgroup.map_id]

end CFSG.OddStandard.SmallF3.Omega
