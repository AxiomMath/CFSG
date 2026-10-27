module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.E6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.MinE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.OfCentralCover
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

section Iso

variable {k : Type} [Field k] [Finite k]

theorem sigma_canonMin (θ : k →+* k) {w : WeylGroup Tag.E6}
    (hw : weylTwist TwistTag.E6 w = w) :
    TwistedE6.sigma k θ (canonMin k w) = canonMin k w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hwp : (coxeterSystem Tag.E6).wordProd (ω.map TwistedE6.rhoPerm) =
      (coxeterSystem Tag.E6).wordProd ω :=
    (weylTwist_wordProd TwistTag.E6 ω).symm.trans hw
  have hred : (coxeterSystem Tag.E6).IsReduced (ω.map TwistedE6.rhoPerm) := by
    rw [CoxeterSystem.IsReduced, hwp, hω.eq, List.length_map]
  have h1 : TwistedE6.sigma k θ (canonMin k ((coxeterSystem Tag.E6).wordProd ω)) =
      canonMin k ((coxeterSystem Tag.E6).wordProd (ω.map TwistedE6.rhoPerm)) := by
    rw [canonMin_wordProd hω, canonMin_wordProd hred, map_list_prod, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun a _ => TwistedE6.sigma_nm θ a
  rw [h1, hwp]

end Iso

section Cover

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hK hσ in
theorem sigma_sigma_eq (c : K) : σ (σ c) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

include hf hK in
theorem four_le_card_K : 4 ≤ Nat.card K := by
  rw [hK]
  have h1 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  nlinarith

include hf hK hσ in
theorem derived_eq : ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ =
    graphFixedRootGroup TwistTag.E6 K σ :=
  (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ hσ).2.2.1

include hf hK hσ in
@[expose] noncomputable def coverHom :
    ↥(TwistedE6.fixedGroup K σ) →* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  (MulEquiv.subgroupCongr (derived_eq hf hK σ hσ)).toMonoidHom.comp
    (CFSG.LieType.Simplicity.twistedIsogeny σ (sigma_sigma_eq hK σ hσ) (four_le_card_K hf hK))

include hf hK hσ in
theorem coe_coverHom (x : ↥(TwistedE6.fixedGroup K σ)) :
    ((coverHom hf hK σ hσ x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) =
      ((Isogeny.e6IsogenyT K (x : ↥(e6Data_valid.minGroup K)) :
        ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) :=
  rfl

include hf hK hσ in
theorem ker_coverHom :
    (coverHom hf hK σ hσ).ker = Subgroup.center ↥(TwistedE6.fixedGroup K σ) := by
  rw [← CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center (sigma_sigma_eq hK σ hσ)
    (four_le_card_K hf hK)]
  ext x
  simp only [MonoidHom.mem_ker, coverHom, MonoidHom.coe_comp, Function.comp_apply]
  exact MulEquiv.map_eq_one_iff _

include hf hK hσ in
theorem isCentralCover_coverHom : IsCentralCover (coverHom hf hK σ hσ) 2 where
  surj y := by
    have hy : (y : ModGL TwistTag.E6.tag K) ∈ ⁅twistedFixedGroup TwistTag.E6 K σ,
        twistedFixedGroup TwistTag.E6 K σ⁆ := by
      rw [derived_eq hf hK σ hσ]
      exact y.2
    rw [← Isogeny.range_e6IsogenyFixed σ (sigma_sigma_eq hK σ hσ) (four_le_card_K hf hK)] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  ker_le := (ker_coverHom hf hK σ hσ).le
  coprime := by
    have h1 : Nat.card (coverHom hf hK σ hσ).ker =
        Nat.gcd 3 (2 ^ f + 1) := by
      rw [ker_coverHom hf hK σ hσ]
      exact (CentralExt.TwistedE6Closed.card_center_fixedGroup hK hσ).1
    rw [h1]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 3 (2 ^ f + 1)) (by norm_num)

variable [CharP K 2]

theorem finite_fixedGroup : Finite ↥(TwistedE6.fixedGroup K σ) := by
  have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
  have : Finite ↥(e6Data_valid.minGroup K) := inferInstance
  infer_instance

include hf hK hσ in
theorem hcomm_cover :
    ∀ a ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ),
      ∀ b ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), a * b = b * a := by
  intro a ha b hb
  have hT : ∀ a ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ),
      ((Isogeny.e6IsogenyT K (a : ↥(e6Data_valid.minGroup K)) :
        ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) ∈
        torusGroup TwistTag.E6.tag K := fun a ha =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1
      (show ((coverHom hf hK σ hσ a : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ from ha)).1).1
  exact Subtype.ext (mul_comm_of_isogeny_mem_torusGroup (hT a ha) (hT b hb))

include hf hK hσ in
@[expose] noncomputable def twistedE6CoverData :
    CentralCoverData (twistedE6Datum hf hK σ hσ) (coverHom hf hK σ hσ) 2 where
  cover := isCentralCover_coverHom hf hK σ hσ
  nhatW w := ⟨canonMin K (w : WeylGroup TwistTag.E6.tag),
    (TwistedE6.mem_fixedGroup σ).2 (sigma_canonMin σ ((mem_relWeylTwist TwistTag.E6).1 w.2))⟩
  map_nhatW w := Subtype.ext (e6Isogeny_canonMin (w : WeylGroup TwistTag.E6.tag))
  nhatW_one := Subtype.ext (canonMin_one K)
  nhatW_simple_mul w a h := by
    refine Subtype.ext ?_
    have hl := length_orbitReflection_mul_of_relCs a w h
    have hsimp : (((relCs TwistTag.E6).simple a * w : ↥(relWeylTwist TwistTag.E6)) :
        WeylGroup TwistTag.E6.tag) = TwistTag.E6.orbitReflection a * (w : WeylGroup _) := by
      rw [relCs_simple]
      rfl
    have hsimp1 : (((relCs TwistTag.E6).simple a : ↥(relWeylTwist TwistTag.E6)) :
        WeylGroup TwistTag.E6.tag) = TwistTag.E6.orbitReflection a := by
      rw [relCs_simple]
    show canonMin K (((relCs TwistTag.E6).simple a * w : ↥(relWeylTwist TwistTag.E6)) :
        WeylGroup TwistTag.E6.tag) = canonMin K (((relCs TwistTag.E6).simple a :
          ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) *
        canonMin K (w : WeylGroup TwistTag.E6.tag)
    rw [hsimp, hsimp1]
    have hr : (coxeterSystem TwistTag.E6.tag).length (TwistTag.E6.orbitReflection a) =
        (TwistTag.E6.orbit a).card := length_orbitReflection a
    exact canonMin_mul_of_length_eq' (by rw [hl, hr, add_comm])
  hcomm := hcomm_cover hf hK σ hσ

end Cover

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
