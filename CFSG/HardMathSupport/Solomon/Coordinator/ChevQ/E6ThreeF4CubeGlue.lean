module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeD4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Generic

variable {G H : Type*} [Group G] [Group H]

theorem normalizesRGroup_map_of_injective {φ : G →* H} (hφ : Function.Injective φ) {r : ℕ}
    {E : Subgroup G} (h : NormalizesRGroup r E) : NormalizesRGroup r (E.map φ) := by
  obtain ⟨U, hU0, hUp, hUn⟩ := h
  refine ⟨U.map φ, fun hbot => hU0 ((Subgroup.map_eq_bot_iff_of_injective U hφ).1 hbot),
    hUp.map φ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomp : (MulAut.conj (φ x)).toMonoidHom.comp φ = φ.comp (MulAut.conj x).toMonoidHom :=
    MonoidHom.ext fun z => by simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hUn x hx]

private theorem cube_map_conj (g : G) {r : ℕ} {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) (hN : ¬ NormalizesRGroup r E) :
    IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj g).toMonoidHom) = 3 ^ 3 ∧
      ¬ NormalizesRGroup r (E.map (MulAut.conj g).toMonoidHom) :=
  ⟨hE.map _, by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc],
    fun h => hN (SeitzExcOpenRest2.normalizesRGroup_of_map_mulEquiv (MulAut.conj g) h)⟩

theorem cube_comap_of_le_range {φ : G →* H} (hφ : Function.Injective φ) {r : ℕ}
    {E : Subgroup H} (hle : E ≤ φ.range) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    (hN : ¬ NormalizesRGroup r E) :
    (E.comap φ).map φ = E ∧ IsElemAbelian 3 (E.comap φ) ∧ Nat.card (E.comap φ) = 3 ^ 3 ∧
      ¬ NormalizesRGroup r (E.comap φ) := by
  have hmap : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self hle
  refine ⟨hmap, hE.comap hφ, ?_, fun h => hN ?_⟩
  · rw [← Subgroup.card_map_of_injective hφ, hmap, hc]
  · rw [← hmap]
    exact normalizesRGroup_map_of_injective hφ h

private theorem exists_relIndex_three_of_card {E : Subgroup G} (hc : Nat.card E = 3 ^ 3) :
    ∃ F ≤ E, F.relIndex E = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 2 ∣ Nat.card E by rw [hc]; norm_num)
  refine ⟨F.map E.subtype, Subgroup.map_subtype_le F, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := F.map E.subtype) (K := E)
  rw [inf_of_le_left (Subgroup.map_subtype_le F),
    Subgroup.card_map_of_injective E.subtype_injective, hF, hc] at h1
  norm_num at h1
  omega

private theorem exists_fixed_subfield_of_sq (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq2 : 2 ≤ q) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k K), Nat.card k = q ∧
      ringChar k = ringChar K ∧ ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hKcard⟩ := FiniteField.card K (ringChar K)
  have hpr' : Fact (ringChar K).Prime := ⟨hpr⟩
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hKcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨i, -, hqi⟩ := (Nat.dvd_prime_pow hpr).1 hdvd
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hqi
    omega
  have hkcard : Nat.card (GaloisField (ringChar K) i) = q := by
    rw [GaloisField.card (ringChar K) i hi, hqi]
  obtain ⟨ιk⟩ := nonempty_ringHom_of_card_sq (ℓ := ringChar K) (f := i) (hkcard.trans hqi)
    (by rw [hqi] at hK; exact hK)
  letI : Algebra (GaloisField (ringChar K) i) K := ιk.toAlgebra
  refine ⟨GaloisField (ringChar K) i, inferInstance, inferInstance, inferInstance, hkcard, ?_, ?_⟩
  · exact ringChar.eq _ _
  · intro c
    rw [hσ]
    have hc : c ^ q = c := by
      rw [← hkcard]
      haveI : Fintype (GaloisField (ringChar K) i) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [← map_pow, hc]

end Generic

section Sylow


theorem range_embE6F4_eq (K : Type) [Field K] : (embE6F4 K).range = fixE6 K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (isoE6F4 K y).2
  · intro hx
    exact ⟨(isoE6F4 K).symm ⟨x, hx⟩, by simp [embE6F4]⟩

theorem embE6F4_inj (K : Type) [Field K] : Function.Injective (embE6F4 K) :=
  Subtype.val_injective.comp (isoE6F4 K).injective

private theorem card_fixE6_eq (K : Type) [Field K] [Finite K] :
    Nat.card (fixE6 K) = CFSG.Open.ordF4 (Nat.card K) := by
  rw [Nat.card_congr (isoE6F4 K).symm.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]

private theorem conj_le_fixE6_of_mod_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {E₀ : Subgroup (adjointGroup .E6 K)}
    (hexp : ∀ x ∈ E₀, x ^ 3 = 1) :
    ∃ g : adjointGroup .E6 K, E₀.map (MulAut.conj g).toMonoidHom ≤ fixE6 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E₀ := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    simpa using hexp x x.2⟩
  have hcard := Subgroup.card_mul_index (fixE6 K)
  rw [card_fixE6_eq, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
    ordE6_eq_ordF4_mul_of_mod_two hK] at hcard
  have hpos : 0 < CFSG.Open.ordF4 (Nat.card K) := by
    rw [← card_fixE6_eq]
    exact Nat.card_pos
  have hind := Nat.eq_of_mul_eq_mul_left hpos hcard
  obtain ⟨c, hc⟩ := ExcHighThree.exists_conj_le_of_not_dvd_index (fixE6 K)
    (by rw [hind]; exact not_dvd_three_mod_two hK) hP
  refine ⟨c⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa [MulAut.conj_apply, inv_inv] using hc x hx

end Sylow

section Two


theorem e6InnerCubeGenAt_two_of_d4
    (hF4 : SeitzExcOpenRest4.ThreeNonToralCubeRest .F4 LieTypeIndex.F4)
    (hD : E6F4CubeD4Two) : E6ThreeInner.E6InnerCubeGenAt 2 := by
  intro K _ _ hK hs E₀ hE₀ hc hN
  obtain ⟨g, hg⟩ := conj_le_fixE6_of_mod_two K hK hE₀.2
  refine SeitzExcOpenCubes.hyperGen_of_mulEquiv (MulAut.conj g) ?_
  obtain ⟨hE₁, hc₁, hN₁⟩ := cube_map_conj g hE₀ hc hN
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hle : E₁ ≤ (embE6F4 K).range := by
    rw [range_embE6F4_eq K]
    exact hg
  obtain ⟨hmap, hE₃, hc₃, hN₃⟩ := cube_comap_of_le_range (embE6F4_inj K) hle hE₁ hc₁ hN₁
  set E₃ := E₁.comap (embE6F4 K) with hE₃def
  have hs₃ := threeScope_F4_of_E6 hs
  have hK4 : 4 ≤ Nat.card K := by
    have := five_le_card_of_threeScope_E6 hK hs
    omega
  have hclose : HyperGen 3 ⊤ E₃ → fixE6 K ≤ hyperClosure 3 ⊤ E₁ := by
    intro hgen x hx
    rw [← range_embE6F4_eq K] at hx
    obtain ⟨y, rfl⟩ := hx
    have h0 : embE6F4 K y ∈ (hyperClosure 3 ⊤ E₃).map (embE6F4 K) :=
      ⟨y, hyperGen_iff_le.1 hgen (Subgroup.mem_top y), rfl⟩
    have h1 := CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.map_hyperClosure_le_of_injective
      (embE6F4_inj K) E₃ h0
    rwa [hmap] at h1
  rcases isEmpty_or_nonempty (LangPlaneData .F4 K E₃) with hemp | hne
  · exact e6_hyperGen_of_anti K hK4 E₁
      (hclose (hF4 K (by omega) hs₃ E₃ hE₃ hc₃ hN₃ hemp)) (hD K hK hs E₁ hg hE₁ hc₁ hN₁ hemp)
  obtain ⟨D⟩ := hne
  by_cases hkill : ∃ α, IsRoot Tag.F4 α ∧ D.Kills α
  · obtain ⟨α, hα, hkα⟩ := hkill
    obtain ⟨u, hu1, hur, hcomm⟩ := langPlaneKillsRoot_F4 K E₃ D α hα hkα
    exact absurd (SeitzExcOpenRest4.normalizesRGroup_of_commute hu1 hur hcomm) hN₃
  have hreg : ∀ α, IsRoot Tag.F4 α → ¬ D.Kills α := fun α hα hkα => hkill ⟨α, hα, hkα⟩
  have hw1 := (SeitzExcOpenRest5.f4_regular_datum_w hE₃ hc₃ D hreg).2 hK
  have hw : ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u := fun u => by
    rw [hw1]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul u
  obtain ⟨k, hk⟩ := SeitzExcOpenRest5.f4_exists_conj_le_frame_of_neg hE₃.2 D hw
  obtain ⟨F, hFE, hFi⟩ := exists_relIndex_three_of_card hc₁
  refine e6_hyperGen_of_anti K hK4 E₁
    (hclose (SeitzExcOpenRest5.hyperGen_F4_of_neg_datum hK hs₃ hE₃ hc₃ D hw))
    ⟨F, hFE, hFi, embE6F4 K k, (isoE6F4 K k).2, fun f hf u => ?_⟩
  have hf1 : f ∈ E₃.map (embE6F4 K) := by
    rw [hmap]
    exact hFE hf
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf1
  have hxF : k * x * k⁻¹ ∈ f4FrameGroup K := by
    have h1 := hk ⟨x, hx, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have h2 := commute_anti_of_mem_f4FrameGroup K hxF u
  rwa [map_mul, map_mul, map_inv] at h2

end Two

section One


theorem twE6InnerCubeGenAt_one_of_d4
    (hF4 : SeitzExcOpenRest4.ThreeNonToralCubeRest .F4 LieTypeIndex.F4)
    (hD : TwE6F4CubeD4One) : E6ThreeInner.TwE6InnerCubeGenAt 1 := by
  intro K _ _ σ q hK hσ hq hs E₀ hE₀ hc hN
  have hq7 : 7 ≤ q := seven_le_of_twThreeScope hK hq hs
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ :=
    exists_fixed_subfield_of_sq q K σ hK hσ (by omega)
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
  have hK' : Nat.card K = Nat.card k ^ 2 := by rw [hkq]; exact hK
  have hq' : Nat.card k % 3 = 1 := by rw [hkq]; exact hq
  have hk5 : 5 ≤ Nat.card k := by rw [hkq]; omega
  obtain ⟨g, hg⟩ := threeSubgroup_conj_into_F4 σ hσk hK' hfix hq' (by omega) E₀ hE₀.2
  refine SeitzExcOpenCubes.hyperGen_of_mulEquiv (MulAut.conj g) ?_
  obtain ⟨hE₁, hc₁, hN₁⟩ := cube_map_conj g hE₀ hc hN
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  have hle : E₁ ≤ (phiG σ hfix).range := by
    intro x hx
    obtain ⟨y, hy⟩ := hg hx
    exact ⟨(e6FixedF4EquivAll k).symm y, hy⟩
  obtain ⟨hmap, hE₃, hc₃, hN₃⟩ := cube_comap_of_le_range hι hg hE₁ hc₁ hN₁
  set E₃ := E₁.comap ι with hE₃def
  rw [← hkchar] at hN₃
  have hs₃ := threeScope_F4_of_twThreeScope hK' hs
  rcases isEmpty_or_nonempty (LangPlaneData .F4 k E₃) with hemp | hne
  · have hgen := hF4 k (by omega) hs₃ E₃ hE₃ hc₃ hN₃ hemp
    have hcl : (phiG σ hfix).range ≤ hyperClosure 3 ⊤ E₁ := by
      rintro _ ⟨z, rfl⟩
      have h0 : phiG σ hfix z ∈ (hyperClosure 3 ⊤ E₃).map ι :=
        ⟨e6FixedF4EquivAll k z, hyperGen_iff_le.1 hgen (Subgroup.mem_top _), by simp [hιdef]⟩
      have h1 := CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.map_hyperClosure_le_of_injective
        hι E₃ h0
      rwa [hmap] at h1
    exact twE6_hyperGen_of_anti σ hσk hfix hK' hk5 E₁ hcl
      (hD k K σ hσk hfix hK' hq' hs E₁ hle hE₁ hc₁ hN₁ hemp)
  obtain ⟨D⟩ := hne
  by_cases hkill : ∃ α, IsRoot Tag.F4 α ∧ D.Kills α
  · obtain ⟨α, hα, hkα⟩ := hkill
    obtain ⟨u, hu1, hur, hcomm⟩ := langPlaneKillsRoot_F4 k E₃ D α hα hkα
    exact absurd (SeitzExcOpenRest4.normalizesRGroup_of_commute hu1 hur hcomm) hN₃
  exact (SeitzExcOpenRest5.threeToralCubeRest_F4_one k hq' E₃ hE₃ hc₃ hN₃ D
    fun α hα hkα => hkill ⟨α, hα, hkα⟩).elim

end One

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
