module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneVad
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenHat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc.E6Three

theorem four_le_card_of_card_eq_sq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    (hK : Nat.card K = (ℓ ^ f) ^ 2) : 4 ≤ Nat.card K := by
  have h2 : 2 ≤ ℓ ^ f :=
    hℓ.two_le.trans (by simpa using Nat.pow_le_pow_right hℓ.pos hf)
  rw [hK]
  nlinarith

private theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (h3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h : q ^ 2 % 3 = 1 := by
    rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h | h <;> rw [Nat.pow_mod, h]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega


@[expose] noncomputable def twInndiagHom (K : Type) [Field K] (σ : K ≃+* K) :
    ↥(twistedE6InndiagGL K σ) →* MulAut ↥(adjointGroup Tag.E6 K) :=
  (e6InndiagConj K).comp (Subgroup.inclusion (twistedE6InndiagGL_le_e6InndiagGL K σ))

@[expose] noncomputable def twInndiagLift (K : Type) [Field K] (σ : K ≃+* K)
    (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :
    Subgroup (MulAut ↥(adjointGroup Tag.E6 K)) :=
  (S.comap (twistedE6InndiagConj K σ)).map (twInndiagHom K σ)

theorem twInndiagHom_injective {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (σ : K ≃+* K) : Function.Injective (twInndiagHom K σ) :=
  (e6InndiagConj_injective K hK).comp (Subgroup.inclusion_injective _)

theorem range_twInndiagHom_le (K : Type) [Field K] (σ : K ≃+* K) :
    (twInndiagHom K σ).range ≤ (hatAut .E6 K).range := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.cen_range_hatAut,
    ← range_e6InndiagConj]
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

theorem twInndiagLift_le_hatAut_range (K : Type) [Field K] (σ : K ≃+* K)
    (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :
    twInndiagLift K σ S ≤ (hatAut .E6 K).range :=
  (Subgroup.map_le_range _ _).trans (range_twInndiagHom_le K σ)

theorem isElemAbelian_comap_twistedE6InndiagConj {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (h : IsElemAbelian p S) : IsElemAbelian p (S.comap (twistedE6InndiagConj K σ)) := by
  have hφ := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  refine ⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun x hx => hφ ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (h.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  · rw [map_pow, h.2 _ hx, map_one]

theorem isElemAbelian_twInndiagLift {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (h : IsElemAbelian p S) :
    IsElemAbelian p (twInndiagLift K σ S) :=
  CFSG.StandardType.TableB.isElemAbelian_map
    (isElemAbelian_comap_twistedE6InndiagConj hℓ hf hK σ hσ h) _

theorem card_twInndiagLift {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hS : S ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Nat.card (twInndiagLift K σ S) = Nat.card S := by
  have hφ := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hSr : S ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hS
  rw [twInndiagLift,
    Subgroup.card_map_of_injective (twInndiagHom_injective (four_le_card_of_card_eq_sq hℓ hf hK) σ),
    ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hSr]

theorem card_le_of_le_twInndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : ¬ 3 ∣ ℓ ^ f) {X : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hX : IsElemAbelian 3 X) (hXI : X ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Nat.card X ≤ 3 ^ 6 := by
  rw [← card_twInndiagLift hℓ hf hK σ hσ hXI]
  exact E6One.card_le_of_le_hatAut (by rw [hK]; exact three_dvd_sq_sub_one_of_not_dvd h3)
    (isElemAbelian_twInndiagLift hℓ hf hK σ hσ hX) (twInndiagLift_le_hatAut_range K σ X)

theorem exists_conj_eq_of_le_twInndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : ¬ 3 ∣ ℓ ^ f)
    {X Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hXI : X ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hYI : Y ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hX : IsElemAbelian 3 X)
    (hY : IsElemAbelian 3 Y) (hXc : Nat.card X = 3 ^ 6) (hYc : Nat.card Y = 3 ^ 6) :
    ∃ γ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ, Y.map (MulAut.conj γ).toMonoidHom = X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6InndiagGL K σ) := Subtype.finite
  set φ := twistedE6InndiagConj K σ with hφdef
  set ψ := twInndiagHom K σ with hψdef
  have hφ : Function.Injective φ := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hψ : Function.Injective ψ :=
    twInndiagHom_injective (four_le_card_of_card_eq_sq hℓ hf hK) σ
  have hrange : φ.range = twistedE6Inn K σ ⊔ twistedE6Diag K σ := range_twistedE6InndiagConj K σ
  have hXr : X ≤ φ.range := hrange ▸ hXI
  have hYr : Y ≤ φ.range := hrange ▸ hYI
  set X' := X.comap φ with hX'
  set Y' := Y.comap φ with hY'
  have hX'map : X'.map φ = X := Subgroup.map_comap_eq_self hXr
  have hY'map : Y'.map φ = Y := Subgroup.map_comap_eq_self hYr
  have hX'c : Nat.card X' = 3 ^ 6 := by
    rw [← Subgroup.card_map_of_injective hφ, hX'map, hXc]
  have hY'c : Nat.card Y' = 3 ^ 6 := by
    rw [← Subgroup.card_map_of_injective hφ, hY'map, hYc]
  have hX'e : IsElemAbelian 3 X' := isElemAbelian_comap_twistedE6InndiagConj hℓ hf hK σ hσ hX
  have hY'e : IsElemAbelian 3 Y' := isElemAbelian_comap_twistedE6InndiagConj hℓ hf hK σ hσ hY
  obtain ⟨P, hXP⟩ := (IsPGroup.of_card hX'c).exists_le_sylow
  obtain ⟨P', hYP'⟩ := (IsPGroup.of_card hY'c).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(twistedE6InndiagGL K σ) P' P
  set c : ↥(twistedE6InndiagGL K σ) →* ↥(twistedE6InndiagGL K σ) :=
    (MulAut.conj g).toMonoidHom with hc
  have hYP : Y'.map c ≤ (P : Subgroup ↥(twistedE6InndiagGL K σ)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hYP' hy)
  have hcc : Nat.card (Y'.map c) = 3 ^ 6 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hY'c]
  have hce : IsElemAbelian 3 (Y'.map c) := CFSG.StandardType.TableB.isElemAbelian_map hY'e c
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact three_dvd_sq_sub_one_of_not_dvd h3
  have heq : X'.map ψ = (Y'.map c).map ψ :=
    E6One.eq_of_le_of_isPGroup hK3 (P.isPGroup'.map ψ)
      ((Subgroup.map_le_range _ _).trans (range_twInndiagHom_le K σ))
      ((Subgroup.map_le_range _ _).trans (range_twInndiagHom_le K σ))
      (Subgroup.map_mono hXP) (Subgroup.map_mono hYP)
      (CFSG.StandardType.TableB.isElemAbelian_map hX'e ψ)
      (CFSG.StandardType.TableB.isElemAbelian_map hce ψ)
      (by rw [Subgroup.card_map_of_injective hψ, hX'c])
      (by rw [Subgroup.card_map_of_injective hψ, hcc])
  have hXY : X' = Y'.map c := Subgroup.map_injective hψ heq
  refine ⟨φ g, hrange ▸ ⟨g, rfl⟩, ?_⟩
  have hcomm : (MulAut.conj (φ g)).toMonoidHom.comp φ = φ.comp c := by
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hc, map_mul, map_inv]
  rw [← hY'map, Subgroup.map_map, hcomm, ← Subgroup.map_map, ← hXY, hX'map]

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
