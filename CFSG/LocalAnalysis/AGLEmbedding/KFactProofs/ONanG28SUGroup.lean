module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUField
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28.SU

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

noncomputable section

theorem card_su_F64 : Nat.card (StatedSU 3 8 F64) = 16547328 := by
  have h : Nat.card F64 = (2 ^ 3) ^ 2 := by rw [card_F64]; norm_num
  have := CFSG.SectionRank.OddCover.card_statedSU_three (K := F64) (p := 2) (f := 3) h
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
  rw [this]
  norm_num

@[expose] def betaGL :
    Matrix.GeneralLinearGroup (Fin 3) F64 →* Matrix.GeneralLinearGroup (Fin 6) GF8 :=
  Units.map (blockMat : Matrix (Fin 3) (Fin 3) F64 →+* Matrix (Fin 6) (Fin 6) GF8).toMonoidHom

theorem coe_betaGL (u : Matrix.GeneralLinearGroup (Fin 3) F64) :
    ((betaGL u : Matrix.GeneralLinearGroup (Fin 6) GF8) : Matrix (Fin 6) (Fin 6) GF8) =
      blockMat (u : Matrix (Fin 3) (Fin 3) F64) := rfl

theorem betaGL_injective : Function.Injective betaGL := by
  intro u v h
  apply Units.ext
  apply blockMat_injective
  have := congrArg (fun w : Matrix.GeneralLinearGroup (Fin 6) GF8 =>
    (w : Matrix (Fin 6) (Fin 6) GF8)) h
  exact this

theorem exists_equiv_statedSU
    {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Matrix (Fin 6) (Fin 6) GF8)
    (hρ : Function.Injective ρ) (P Pi : Matrix (Fin 6) (Fin 6) GF8) (hP : P * Pi = 1)
    (hPi : Pi * P = 1) (S : Set Γ) (hcard : Nat.card (Subgroup.closure S) = 16547328)
    (hS : ∀ s ∈ S, ∃ G : Matrix (Fin 3) (Fin 3) F64, blockMat G = Pi * ρ s * P ∧ G.det = 1 ∧
      (blockMat G)ᵀ * jbM * blockMat G = jbM) :
    ∃ Θ : Subgroup.closure S ≃* StatedSU 3 8 F64,
      ∀ g : Subgroup.closure S,
        blockMat (((Θ g : StatedSU 3 8 F64) : Matrix.GeneralLinearGroup (Fin 3) F64) :
          Matrix (Fin 3) (Fin 3) F64) = Pi * ρ g * P := by
  classical
  let Pu : Matrix.GeneralLinearGroup (Fin 6) GF8 := ⟨P, Pi, hP, hPi⟩
  let γ : Γ →* Matrix.GeneralLinearGroup (Fin 6) GF8 :=
    (MulAut.conj Pu⁻¹).toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hγ : ∀ g, ((γ g : Matrix.GeneralLinearGroup (Fin 6) GF8) : Matrix (Fin 6) (Fin 6) GF8) =
      Pi * ρ g * P := by
    intro g
    simp [γ, Pu, MulAut.conj_apply]
  set SU := StatedSU 3 8 F64 with hSU
  set SUβ : Subgroup (Matrix.GeneralLinearGroup (Fin 6) GF8) := SU.map betaGL with hSUβ
  have hgen : ∀ s ∈ S, γ s ∈ SUβ := by
    intro s hs
    obtain ⟨G, hG, hdet, hsymp⟩ := hS s hs
    let u : Matrix.GeneralLinearGroup (Fin 3) F64 :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero G (by rw [hdet]; exact one_ne_zero)
    have hu : (u : Matrix (Fin 3) (Fin 3) F64) = G := rfl
    have huSU : u ∈ SU := by
      apply Subgroup.subset_closure
      refine ⟨by rw [hu]; exact hdet, ?_⟩
      rw [hu]
      exact unitary_of_symp hsymp
    refine ⟨u, huSU, ?_⟩
    apply Units.ext
    rw [coe_betaGL, hu, hG, hγ]
  have hV : ∀ g ∈ Subgroup.closure S, γ g ∈ SUβ := by
    intro g hg
    have : Subgroup.closure S ≤ SUβ.comap γ := by
      rw [Subgroup.closure_le]
      intro s hs
      exact hgen s hs
    exact this hg
  let Θ0 : Subgroup.closure S →* SUβ :=
    (γ.comp (Subgroup.closure S).subtype).codRestrict SUβ (fun g => hV g.1 g.2)
  let eβ : SU ≃* SUβ := Subgroup.equivMapOfInjective SU betaGL betaGL_injective
  let Θ1 : Subgroup.closure S →* SU := eβ.symm.toMonoidHom.comp Θ0
  have hΘ1 : ∀ g : Subgroup.closure S,
      betaGL ((Θ1 g : SU) : Matrix.GeneralLinearGroup (Fin 3) F64) = γ g := by
    intro g
    have : eβ (Θ1 g) = Θ0 g := by simp [Θ1]
    have h2 := congrArg (fun x : SUβ => (x : Matrix.GeneralLinearGroup (Fin 6) GF8)) this
    exact h2
  have hinj : Function.Injective Θ1 := by
    intro g h hgh
    have e1 : γ g = γ h := by rw [← hΘ1 g, ← hΘ1 h, hgh]
    have e2 := congrArg (fun w : Matrix.GeneralLinearGroup (Fin 6) GF8 =>
      (w : Matrix (Fin 6) (Fin 6) GF8)) e1
    simp only [hγ] at e2
    have e3 : ρ g = ρ h := by
      calc ρ g = (P * Pi) * ρ g * (P * Pi) := by rw [hP]; simp
        _ = P * (Pi * ρ g * P) * Pi := by simp only [mul_assoc]
        _ = P * (Pi * ρ h * P) * Pi := by rw [e2]
        _ = (P * Pi) * ρ h * (P * Pi) := by simp only [mul_assoc]
        _ = ρ h := by rw [hP]; simp
    exact Subtype.ext (hρ e3)
  have hbij : Function.Bijective Θ1 :=
    Function.Injective.bijective_of_nat_card_le hinj (by rw [hcard, hSU, card_su_F64])
  refine ⟨MulEquiv.ofBijective Θ1 hbij, fun g => ?_⟩
  have := congrArg (fun w : Matrix.GeneralLinearGroup (Fin 6) GF8 =>
    (w : Matrix (Fin 6) (Fin 6) GF8)) (hΘ1 g)
  simp only [coe_betaGL, hγ] at this
  exact this

theorem card_F64_sq : Nat.card F64 = (2 ^ 3) ^ 2 := by
  rw [card_F64]
  norm_num

theorem su_quasi : CFSG.IsQuasisimple (StatedSU 3 8 F64) ∧
    Subgroup.center (StatedSU 3 8 F64) =
      (StatedScalars (Fin 3) F64).subgroupOf (StatedSU 3 8 F64) :=
  CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := F64) (p := 2) (f := 3) (n := 3) card_F64_sq (le_refl 3) (by simp)

theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center Q))) with
    h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by
        rw [hMZ]
        rfl
      rw [e]
      have hn : (M ⊔ Subgroup.center Q).Normal := by
        rw [hMZ]
        infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

theorem det_of_mem_su {A : Matrix.GeneralLinearGroup (Fin 3) F64} (hA : A ∈ StatedSU 3 8 F64) :
    Matrix.GeneralLinearGroup.det A = 1 := by
  have h : StatedSU 3 8 F64 ≤
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) F64 →* F64ˣ).ker := by
    rw [StatedSU, Subgroup.closure_le]
    intro B hB
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    simpa using hB.1
  exact MonoidHom.mem_ker.1 (h hA)

@[expose] def omegaU : F64ˣ :=
  ⟨AdjoinRoot.root pF, AdjoinRoot.root pF ^ 2, by rw [← pow_succ']; exact omega_pow_three,
    by rw [← pow_succ]; exact omega_pow_three⟩

theorem coe_omegaU : (omegaU : F64) = AdjoinRoot.root pF := rfl

theorem coe_scalar_omegaU : ((Matrix.GeneralLinearGroup.scalar (Fin 3) omegaU :
    Matrix.GeneralLinearGroup (Fin 3) F64) : Matrix (Fin 3) (Fin 3) F64) = omegaMat := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  rfl

theorem units_cube_cases (c : F64ˣ) (h : c ^ 3 = 1) : ∃ k : ℕ, k < 3 ∧ c = omegaU ^ k := by
  have h3 : (c : F64) ^ 3 = 1 := by
    have := congrArg (fun u : F64ˣ => (u : F64)) h
    simpa using this
  have hq : AdjoinRoot.root pF * AdjoinRoot.root pF + AdjoinRoot.root pF + 1 = 0 := omega_quad
  have hw3 : AdjoinRoot.root pF ^ 3 = 1 := omega_pow_three
  have key : ((c : F64) - 1) * ((c : F64) - AdjoinRoot.root pF) *
      ((c : F64) - AdjoinRoot.root pF ^ 2) = 0 := by
    linear_combination (-((c : F64) ^ 2) + AdjoinRoot.root pF * (c : F64)) * hq +
      (-1) * hw3 + h3
  rcases mul_eq_zero.1 key with h12 | h4
  · rcases mul_eq_zero.1 h12 with h1 | h2
    · refine ⟨0, by norm_num, Units.ext ?_⟩
      simpa [sub_eq_zero] using h1
    · refine ⟨1, by norm_num, Units.ext ?_⟩
      simpa [sub_eq_zero, coe_omegaU] using h2
  · refine ⟨2, by norm_num, Units.ext ?_⟩
    simpa [sub_eq_zero, coe_omegaU] using h4

theorem center_le_zpowers {V : Type} [Group V] (Θ : V ≃* StatedSU 3 8 F64) (zv : V)
    (hz : (((Θ zv : StatedSU 3 8 F64) : Matrix.GeneralLinearGroup (Fin 3) F64) :
      Matrix (Fin 3) (Fin 3) F64) = omegaMat) :
    Subgroup.center V ≤ Subgroup.zpowers zv := by
  intro c hc
  have h1 : Θ c ∈ Subgroup.center (StatedSU 3 8 F64) := by
    rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv Θ]
    exact ⟨c, hc, rfl⟩
  rw [su_quasi.2, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨s, hs⟩ := h1
  have hdet := det_of_mem_su (Θ c).2
  rw [← hs, Matrix.GeneralLinearGroup.det_scalar] at hdet
  have hs3 : s ^ 3 = 1 := by simpa using hdet
  obtain ⟨k, -, hk⟩ := units_cube_cases s hs3
  have hzU : ((Θ zv : StatedSU 3 8 F64) : Matrix.GeneralLinearGroup (Fin 3) F64) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) omegaU := by
    apply Units.ext
    rw [hz, coe_scalar_omegaU]
  have hck : Θ c = Θ (zv ^ k) := by
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, ← hs, hk, map_pow, hzU]
  have : c = zv ^ k := Θ.injective hck
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers zv) k

theorem valid_twistedA_two_eight :
    (TauCeti.LieTypeIndex.twistedA 2 ⟨2, 3, Nat.prime_two, by norm_num⟩).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [TauCeti.PrimePower.card_def]
  norm_num

def projSUCongr (a b : ℕ) [Fact a.Prime] (ha : a = 2) (hb : b = 3) :
    StatedProj (StatedSU 3 8 (GaloisField 2 6)) ≃*
      StatedProj (StatedSU (2 + 1) (a ^ b) (GaloisField a (2 * b))) := by
  subst ha hb
  exact MulEquiv.refl _

theorem exists_surj {V : Type} [Group V] (Θ : V ≃* StatedSU 3 8 F64) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* (TauCeti.CFSGIndex.lie d).Group),
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 2 q) ∧
        Function.Surjective ψ := by
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA 2 q, valid_twistedA_two_eight⟩
  have : Fintype F64 := Fintype.ofFinite F64
  have : Fintype (GaloisField 2 6) := Fintype.ofFinite _
  have hc : Fintype.card F64 = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_F64,
      GaloisField.card 2 6 (by norm_num)]
    norm_num
  let e : F64 ≃+* GaloisField 2 6 := FiniteField.ringEquivOfCardEq hc
  have h1 : TauCeti.ValidLieTypeIndex.characteristic d = 2 := by
    show (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 2
    simp [q]
  have h2 : TauCeti.ValidLieTypeIndex.fieldExponent d = 3 := by
    show (TauCeti.LieTypeIndex.twistedA 2 q).fieldExponent = 3
    simp [q]
  have : Fact (TauCeti.ValidLieTypeIndex.characteristic d).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime d⟩
  let f2 := CFSG.Fischer.Classification.Recognition.statedProjSUEquiv e 3 8
  let f3 := (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q
    valid_twistedA_two_eight).symm
  let f4 := projSUCongr (TauCeti.ValidLieTypeIndex.characteristic d)
    (TauCeti.ValidLieTypeIndex.fieldExponent d) h1 h2
  refine ⟨d, f3.toMonoidHom.comp (f4.toMonoidHom.comp (f2.toMonoidHom.comp
    ((QuotientGroup.mk' _).comp Θ.toMonoidHom))), ⟨q, rfl, rfl, rfl⟩, ?_⟩
  exact f3.surjective.comp (f4.surjective.comp (f2.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp Θ.surjective)))

end

end CFSG.AGLEmbedding.KFactProofs.G28.SU
