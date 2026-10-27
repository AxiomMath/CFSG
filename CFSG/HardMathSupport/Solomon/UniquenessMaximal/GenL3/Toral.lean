module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.DiagCount
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.FixSub
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Equivariance
public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Fixed
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.ToralCore
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

section Card

variable {K : Type} [Field K] [Finite K]

theorem card_le_three_mul_inf (h3 : 3 ∣ Nat.card K - 1)
    (A : Subgroup (MulAut (projectiveSL 3 K))) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) := by
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) := inferInstance
  set F := l3FrameLinear h3 with hF
  have hle : A ≤ F.E := by
    intro x hx
    have h3x : x ^ 3 = 1 := hA.2 x hx
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3x
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · have : x = 1 := orderOf_eq_one_iff.1 h1
      rw [this]; exact F.E.one_mem
    · exact F.mem_E.2 (F.three_mem x 1 (by rw [h1]; norm_num))
  set ρ : ↥A →* (K ≃+* K) := F.rho.comp (Subgroup.inclusion hle) with hρ
  have hker : ∀ x : ↥A, ρ x = 1 ↔ (x : MulAut (projectiveSL 3 K)) ∈ F.D := fun x =>
    F.rho_eq_one_iff ⟨x, hle x.2⟩
  have hcube : ∀ c ∈ ρ.range, c ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : (x : ↥A) ^ 3 = 1 := Subtype.ext (hA.2 x x.2)
    rw [this, map_one]
  have hrcard : Nat.card ρ.range ≤ 3 :=
    card_le_three_of_pow (fun c => Subtype.ext (by simpa using hcube c c.2))
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hkercard : Nat.card ρ.ker ≤ Nat.card (A ⊓ linearAutGroup 3 K :
      Subgroup (MulAut (projectiveSL 3 K))) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥ρ.ker => (⟨(x.1 : MulAut (projectiveSL 3 K)), x.1.2, (hker x.1).1 x.2⟩ :
        ↥(A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))))) ?_
    intro x y hxy
    have h := congrArg (fun z : ↥(A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) =>
      (z : MulAut (projectiveSL 3 K))) hxy
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card A = Nat.card ρ.ker * Nat.card ρ.range := hmul.symm
    _ ≤ Nat.card (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) * 3 :=
        Nat.mul_le_mul hkercard hrcard
    _ = 3 * Nat.card (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) := by ring

theorem card_inf_linear_eq_nine (h3 : 3 ∣ Nat.card K - 1)
    (A : Subgroup (MulAut (projectiveSL 3 K))) (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) :
    Nat.card (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) = 9 := by
  have h1 := card_le_three_mul_inf h3 A hA
  have hE0A : IsElemAbelian 3 (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hA.2 x hx.1⟩
    exact Subtype.ext (by
      have := hA.1.is_comm.comm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
      simpa using congrArg Subtype.val this)
  have h2 : Nat.card (A ⊓ linearAutGroup 3 K : Subgroup (MulAut (projectiveSL 3 K))) ≤ 9 :=
    hD9_L h3 _ inf_le_right hE0A
  omega

end Card

section Toral

variable {F : Type} [Field F] [Finite F]

open CFSG.SectionRank.OddCover in
@[expose] def LiftsCommute (A : Subgroup (MulAut (projectiveSL 3 F))) : Prop :=
  ∀ g h : GL (Fin 3) F, conjAut 3 F g ∈ A → conjAut 3 F h ∈ A → g * h = h * g

theorem conjAut_eq_one_iff_scalar (B : GL (Fin 3) F) :
    conjAut 3 F B = 1 ↔ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = B := by
  constructor
  · intro h
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B 1
      (by rw [map_one, mul_one]; exact h)).2
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

theorem iota_eq_scalar (σ : F ≃+* F) {g : GL (Fin 3) (fixSub σ)} {c : Fˣ}
    (h : iotaGL σ g = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    g ∈ Subgroup.center (GL (Fin 3) (fixSub σ)) := by
  have hij : ∀ i j : Fin 3, (((g : Matrix (Fin 3) (Fin 3) (fixSub σ)) i j : fixSub σ) : F) =
      if i = j then (c : F) else 0 := by
    intro i j
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) i j) h
    simp only [coe_iotaGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at this
    exact this
  have hc : (c : F) ∈ fixSub σ := by
    have := hij 0 0
    simp only [ite_true] at this
    rw [← this]
    exact ((g : Matrix (Fin 3) (Fin 3) (fixSub σ)) 0 0).2
  set c₀ : fixSub σ := ⟨(c : F), hc⟩ with hc₀
  have hc₀ne : c₀ ≠ 0 := fun h0 => c.ne_zero (congrArg Subtype.val h0)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 c₀ hc₀ne, ?_⟩
  apply Units.ext
  ext i j
  rw [hij i j]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hc₀]
  split_ifs <;> rfl

theorem iotaGL_diagHom (σ : F ≃+* F) (d : Fin 3 → (fixSub σ)ˣ) :
    iotaGL σ (CFSG.SectionRank.OddCover.diagHom 3 d) =
      diagGL (fun i => Units.map (fixSub σ).subtype.toMonoidHom (d i)) := by
  apply Units.ext
  ext i j
  rw [coe_iotaGL, CFSG.SectionRank.OddCover.coe_diagHom, coe_diagGL]
  simp only [Matrix.diagonal_apply]
  split_ifs <;> rfl

theorem gen_toral_of_field (h3 : 3 ∣ Nat.card F - 1) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (A : Subgroup (MulAut (projectiveSL 3 F))) (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hf : fieldAut 3 F σ ∈ A) (hL : LiftsCommute A) : GenP A := by
  classical
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_unity h3
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hωσ : σ ω = ω := ringEquiv_fix_cube_root hσ3 hω3 hω1
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω3
  set w : Fˣ := Units.mk0 ω hω0 with hw
  set ψ0 : GL (Fin 3) (fixSub σ) →* MulAut (projectiveSL 3 F) :=
    (conjAut 3 F).comp (iotaGL σ) with hψ0
  set U : Subgroup (GL (Fin 3) (fixSub σ)) := A.comap ψ0 with hU
  have hψ0app : ∀ g, ψ0 g = conjAut 3 F (iotaGL σ g) := fun g => rfl
  set Z := Subgroup.center (GL (Fin 3) (fixSub σ)) with hZdef
  have hZU : Z ≤ U := by
    intro z hz
    rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨x, rfl⟩ := hz
    show ψ0 _ ∈ A
    rw [hψ0app, iotaGL_scalar, conjAut_scalar]
    exact A.one_mem
  have hexp : ∀ g ∈ U, g ^ 3 ∈ Z := by
    intro g hg
    have h1 : (conjAut 3 F (iotaGL σ g)) ^ 3 = 1 := hAel.2 _ hg
    have h2 : conjAut 3 F (iotaGL σ (g ^ 3)) = 1 := by rw [map_pow, map_pow]; exact h1
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar _).1 h2
    exact iota_eq_scalar σ hc.symm
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    apply iotaGL_injective σ
    rw [map_mul, map_mul]
    exact hL _ _ ha hb
  have hcard : Nat.card U = 9 * Nat.card Z := by
    set φ : U →* MulAut (projectiveSL 3 F) := ψ0.comp U.subtype with hφ
    have hrange : φ.range = A ⊓ linearAutGroup 3 F := by
      ext x
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩
        exact ⟨hg, conjAut_mem_linearAutGroup _⟩
      · rintro ⟨hxA, hxD⟩
        obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 hxD
        have hcm : conjAut 3 F B * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F B := by
          rw [hB]
          have := hAel.1.is_comm.comm ⟨x, hxA⟩ ⟨fieldAut 3 F σ, hf⟩
          simpa using congrArg Subtype.val this
        obtain ⟨μ, hμ0, hμ⟩ := exists_scalar_fixed hσ B hcm
        set B' : GL (Fin 3) F :=
          B * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) with hB'
        have hB'fix : ∀ i j, σ ((B' : Matrix (Fin 3) (Fin 3) F) i j) =
            (B' : Matrix (Fin 3) (Fin 3) F) i j := by
          intro i j
          rw [hB', bgll_coe_mul_scalar]
          simpa using hμ i j
        obtain ⟨g₀, hg₀⟩ := exists_iota_of_fixed σ B' hB'fix
        have hconj : conjAut 3 F B' = x := by
          rw [hB', map_mul, conjAut_scalar, mul_one, hB]
        refine ⟨⟨g₀, ?_⟩, ?_⟩
        · show conjAut 3 F (iotaGL σ g₀) ∈ A
          rw [hg₀, hconj]; exact hxA
        · show conjAut 3 F (iotaGL σ g₀) = x
          rw [hg₀, hconj]
    have hkerZ : ∀ g : φ.ker, (g : U).1 ∈ Z := by
      intro g
      have h1 : conjAut 3 F (iotaGL σ (g : U).1) = 1 := g.2
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar _).1 h1
      exact iota_eq_scalar σ hc.symm
    have hker : Nat.card φ.ker = Nat.card Z := by
      refine Nat.card_congr (Equiv.ofBijective (fun g : φ.ker => (⟨(g : U).1, hkerZ g⟩ : Z))
        ⟨?_, ?_⟩)
      · intro a b h
        exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
      · rintro ⟨z, hz⟩
        refine ⟨⟨⟨z, hZU hz⟩, ?_⟩, rfl⟩
        rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
        obtain ⟨x, rfl⟩ := hz
        show conjAut 3 F (iotaGL σ (Matrix.GeneralLinearGroup.scalar (Fin 3) x)) = 1
        rw [iotaGL_scalar, conjAut_scalar]
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hker, hrange, card_inf_linear_eq_nine h3 A hAel hA27] at hmul
    linarith
  have hωfix : ω ∈ fixSub σ := hωσ
  set w₀ : (fixSub σ)ˣ := Units.mk0 ⟨ω, hωfix⟩ (fun h0 => hω0 (congrArg Subtype.val h0)) with hw₀
  have hw03 : w₀ ^ 3 = 1 := by
    apply Units.ext
    apply Subtype.ext
    simpa [hw₀] using hω3
  have hw01 : w₀ ≠ 1 := by
    intro h
    apply hω1
    have := congrArg (fun u : (fixSub σ)ˣ => ((u : fixSub σ) : F)) h
    simpa [hw₀] using this
  obtain ⟨m, hm⟩ := exists_conj_diag w₀ hw03 hw01 U hZU hcomm hexp hcard
  set τ : MulAut (projectiveSL 3 F) := conjAut 3 F (iotaGL σ m) with hτ
  have hτf : τ * fieldAut 3 F σ = fieldAut 3 F σ * τ := fieldAut_comm_conjAut_iota σ m
  set A₂ : Subgroup (MulAut (projectiveSL 3 F)) := A.map (MulAut.conj τ).toMonoidHom with hA₂
  have hf₂ : fieldAut 3 F σ ∈ A₂ := by
    refine ⟨fieldAut 3 F σ, hf, ?_⟩
    show τ * fieldAut 3 F σ * τ⁻¹ = fieldAut 3 F σ
    rw [hτf, mul_assoc, mul_inv_cancel, mul_one]
  have hv₂ : ∀ c, vC w c ∈ A₂ := by
    intro c
    have h1 := hm c
    have h2 : conjAut 3 F (iotaGL σ (m⁻¹ * CFSG.SectionRank.OddCover.diagHom 3
        (fun k : Fin 3 => if k = c then w₀ else 1) * m)) ∈ A := h1
    simp only [map_mul, map_inv, iotaGL_diagHom] at h2
    rw [← hτ] at h2
    have hvc : vC w c = conjAut 3 F (diagGL (fun k : Fin 3 => if k = c then w else 1)) := rfl
    have hdd : (fun i : Fin 3 => Units.map (fixSub σ).subtype.toMonoidHom
        ((fun k : Fin 3 => if k = c then w₀ else 1) i)) = fun k : Fin 3 => if k = c then w else 1 := by
      funext k
      by_cases hk : k = c
      · simp only [hk, ite_true]
        apply Units.ext
        simp [hw₀, hw]
      · simp [hk]
    rw [hdd] at h2
    refine ⟨τ⁻¹ * vC w c * τ, ?_, ?_⟩
    · rw [SetLike.mem_coe, hvc]
      exact h2
    · show τ * (τ⁻¹ * vC w c * τ) * τ⁻¹ = vC w c
      group
  have hel₂ : IsElemAbelian 3 A₂ := isElemAbelian_map _ hAel
  have hcard₂ : Nat.card A₂ = 27 := by
    rw [hA₂, Subgroup.card_map_of_injective (MulAut.conj τ).injective, hA27]
  have hw₁ : ((w : Fˣ) : F) ^ 3 = 1 := hω3
  have := toral_core hσ h3 (w := w) hω3 hω1 hωσ A₂ hel₂ hcard₂ hv₂ hf₂
  exact GenP_of_conj τ A this

theorem gen_toral (h3 : 3 ∣ Nat.card F - 1)
    (A : Subgroup (MulAut (projectiveSL 3 F))) (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hb : ∃ b ∈ A, b ∉ linearAutGroup 3 F) (hL : LiftsCommute A) : GenP A := by
  classical
  obtain ⟨b, hbA, hbD⟩ := hb
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbD (h ▸ (linearAutGroup 3 F).one_mem)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf b = 3 ^ 1 := by rw [pow_one]; exact orderOf_eq_prime hb3 hb1
  set Fr := l3FrameLinear h3 with hFr
  have hbE : ∃ d ∈ Fr.D, ∃ c : F ≃+* F, b = d * Fr.fld c := Fr.three_mem b 1 hord
  obtain ⟨h, hh, c, hc3, hbh⟩ := Fr.lang b hb3 hbE hbD
  obtain ⟨H, hH⟩ := mem_linearAutGroup_iff.1 hh
  set τ : MulAut (projectiveSL 3 F) := h⁻¹ with hτ
  set A' : Subgroup (MulAut (projectiveSL 3 F)) := A.map (MulAut.conj τ).toMonoidHom with hA'
  have hf' : fieldAut 3 F c ∈ A' := by
    refine ⟨b, hbA, ?_⟩
    show τ * b * τ⁻¹ = fieldAut 3 F c
    rw [hbh, hτ]
    show h⁻¹ * (h * fieldAut 3 F c * h⁻¹) * h⁻¹⁻¹ = fieldAut 3 F c
    group
  have hL' : LiftsCommute A' := by
    intro g g' hg hg'
    have key : ∀ x : GL (Fin 3) F, conjAut 3 F x ∈ A' → conjAut 3 F (H * x * H⁻¹) ∈ A := by
      intro x hx
      obtain ⟨a, haA, ha⟩ := hx
      have : conjAut 3 F (H * x * H⁻¹) = a := by
        have h1 : τ * a * τ⁻¹ = conjAut 3 F x := ha
        rw [map_mul, map_mul, map_inv, hH]
        rw [hτ] at h1
        have h2 : a = h * conjAut 3 F x * h⁻¹ := by
          rw [← h1]; group
        rw [h2]
      rw [this]; exact haA
    have := hL _ _ (key g hg) (key g' hg')
    have h2 : H * (g * g') * H⁻¹ = H * (g' * g) * H⁻¹ := by
      calc H * (g * g') * H⁻¹ = (H * g * H⁻¹) * (H * g' * H⁻¹) := by group
        _ = (H * g' * H⁻¹) * (H * g * H⁻¹) := this
        _ = H * (g' * g) * H⁻¹ := by group
    simpa using h2
  have hel' : IsElemAbelian 3 A' := isElemAbelian_map _ hAel
  have hcard' : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj τ).injective, hA27]
  have hσ : orderOf c = 3 := hc3
  exact GenP_of_conj τ A (gen_toral_of_field h3 hσ A' hel' hcard' hf' hL')

end Toral

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
