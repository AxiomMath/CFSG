module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std

theorem isElemAbelian_map_gen {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {K : Subgroup G} (hK : IsElemAbelian p K) : IsElemAbelian p (K.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hK.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, hK.2 x hx, map_one]

abbrev VecAut (N : ℕ) : Type := (Fin N → ZMod 2) ≃ₗ[ZMod 2] (Fin N → ZMod 2)

theorem pRank_map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] {p : ℕ}
    (Φ : G ≃* H) (F : Subgroup G) :
    CFSG.Open.pRank p (F.map (Φ : G →* H)) = CFSG.Open.pRank p F := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E', hE'le, hE', hcard⟩
    refine ⟨E'.map (Φ.symm : H →* G), ?_, isElemAbelian_map_gen _ hE', ?_⟩
    · have h := Subgroup.map_mono (f := (Φ.symm : H →* G)) hE'le
      rw [Subgroup.map_map] at h
      convert h using 1
      ext x
      simp
    · rw [Subgroup.card_map_of_injective (Φ.symm.injective), hcard]
  · rintro ⟨E', hE'le, hE', hcard⟩
    refine ⟨E'.map (Φ : G →* H), ?_, isElemAbelian_map_gen _ hE', ?_⟩
    · exact Subgroup.map_mono hE'le
    · rw [Subgroup.card_map_of_injective (Φ.injective), hcard]

theorem map_symm_map_mulEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (E : Subgroup G) :
    (E.map (Φ : G →* H)).map (Φ.symm : H →* G) = E := by
  ext x
  simp

theorem card_map_mulEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (F : Subgroup G) :
    Nat.card (F.map (Φ : G →* H)) = Nat.card F :=
  Subgroup.card_map_of_injective Φ.injective

theorem centralizer_map_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H) (F : Subgroup G) :
    (Subgroup.centralizer (F : Set G)).map (e : G →* H) =
      Subgroup.centralizer ((F.map (e : G →* H) : Subgroup H) : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := hx z hz
    simp only [← map_mul, this]
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hy (e z) ⟨z, hz, rfl⟩
    apply e.injective
    simp only [map_mul]
    simpa using h1

theorem card_quotient_center_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup A) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (↥(K.map (e : A →* B)) ⧸ Subgroup.center ↥(K.map (e : A →* B))) := by
  have hc := Subgroup.map_center_eq (MulEquiv.subgroupMap e K)
  exact Nat.card_congr (QuotientGroup.congr _ _ (MulEquiv.subgroupMap e K) hc).toEquiv

theorem exists_ringEquiv_zmod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (K ≃+* ZMod 2) := by
  classical
  haveI := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  have hcard' : p ^ (n : ℕ) = 2 := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := by
      rw [← hcard']
      exact dvd_pow_self p (PNat.ne_zero n)
    exact (Nat.dvd_prime Nat.prime_two).1 hdvd |>.resolve_left hp.one_lt.ne' |> fun h => h
  subst hp2
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hinj : Function.Injective f := f.injective
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [ZMod.card, Nat.card_eq_fintype_card] at *
    omega
  exact ⟨(RingEquiv.ofBijective f hbij).symm⟩

theorem zero_or_one_of_ringEquiv {K : Type} [Field K] (σ : K ≃+* ZMod 2) (x : K) :
    x = 0 ∨ x = 1 := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (σ x) with h0 | h1
  · left
    apply σ.injective
    rw [h0, map_zero]
  · right
    apply σ.injective
    rw [h1, map_one]

theorem scalars_eq_bot_of_two {K : Type} [Field K] (N : ℕ) (σ : K ≃+* ZMod 2) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars N K = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, _, hAc⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars).1 hA
  have hc : (c : K) = 1 := by
    rcases zero_or_one_of_ringEquiv σ (c : K) with h0 | h1
    · exact absurd h0 c.ne_zero
    · exact h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hAc, hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

noncomputable def slEquivGL {K : Type} [Field K] (N : ℕ) (σ : K ≃+* ZMod 2) :
    Matrix.SpecialLinearGroup (Fin N) K ≃* GL (Fin N) K :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin N) K →* _)
    ⟨fun A B h => by
      apply Subtype.ext
      exact congrArg Units.val h, fun u => by
      have hdet : (u : Matrix (Fin N) (Fin N) K).det = 1 := by
        have h1 : (u : Matrix (Fin N) (Fin N) K).det * ((u⁻¹ : GL (Fin N) K) :
            Matrix (Fin N) (Fin N) K).det = 1 := by
          rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
        have hne : (u : Matrix (Fin N) (Fin N) K).det ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at h1
          exact zero_ne_one h1
        exact (zero_or_one_of_ringEquiv σ _).resolve_left hne
      exact ⟨⟨(u : Matrix (Fin N) (Fin N) K), hdet⟩, Units.ext rfl⟩⟩

noncomputable def glKZ2 {K : Type} [Field K] (N : ℕ) (σ : K ≃+* ZMod 2) :
    GL (Fin N) K ≃* GL (Fin N) (ZMod 2) :=
  Units.mapEquiv (RingEquiv.mapMatrix σ).toMulEquiv

noncomputable def projEquiv {K : Type} [Field K] (N : ℕ) (σ : K ≃+* ZMod 2) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K ≃*
      ((Fin N → ZMod 2) ≃ₗ[ZMod 2] (Fin N → ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_bot_of_two N σ)).trans
    (QuotientGroup.quotientBot.trans
      ((slEquivGL N σ).trans
        ((glKZ2 N σ).trans
          (Matrix.GeneralLinearGroup.toLin.trans
            (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin N → ZMod 2))))))

theorem KD264X1LinCore_holds : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD264X1LinCore := by
  intro N hN K _ _ hK E hE hmax
  obtain ⟨σ⟩ := exists_ringEquiv_zmod2 K hK
  let Φ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K ≃* VecAut N :=
    projEquiv (K := K) N σ
  have hmax' : ∀ E'' : Subgroup (VecAut N), IsElemAbelian 3 E'' → CFSG.Open.pRank 3 E'' ≤
      CFSG.Open.pRank 3 (E.map (Φ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K →*
        VecAut N)) := by
    intro E'' hE''
    rw [pRank_map_mulEquiv Φ E]
    rw [← pRank_map_mulEquiv Φ.symm E'']
    exact hmax _ (isElemAbelian_map_gen _ hE'')
  obtain ⟨F', hF'E, hF'ab, hF'card, L', hL'sub, hL'q, hL'div⟩ :=
    core_V (V := Fin N → ZMod 2) (N := N) (Module.finrank_fin_fun _) hN
      (E.map (Φ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K →* VecAut N))
      (isElemAbelian_map_gen _ hE) hmax'
  refine ⟨F'.map (Φ.symm : VecAut N →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K), ?_,
    isElemAbelian_map_gen _ hF'ab, ?_,
    L'.map (Φ.symm : VecAut N →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K), ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono (f := (Φ.symm : VecAut N →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K)) hF'E).trans
      (le_of_eq (map_symm_map_mulEquiv Φ E))
  · exact (card_map_mulEquiv Φ E).symm.trans (hF'card.trans
      (congrArg (fun n : ℕ => 3 * n) (card_map_mulEquiv Φ.symm F').symm))
  · have h := CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map Φ.symm hL'sub
    rw [centralizer_map_mulEquiv'] at h
    exact h
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap Φ.symm L') hL'q
  · exact (congrArg (fun n : ℕ => 3 ∣ n)
      (card_quotient_center_mulEquiv' Φ.symm L')).mp hL'div

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

end
