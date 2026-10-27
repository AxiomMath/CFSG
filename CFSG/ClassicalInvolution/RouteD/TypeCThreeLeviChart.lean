module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviModel
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLayers

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock longInv suppGroup coords
  IsAdaptedShortIn shortBlock shortGroupNeg planeWeyl weylMat mem_coords mat_longInv)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups

theorem longInv_zero_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    longInv F 2 0 ≠ longInv F 2 1 := by
  intro h
  have h1 := congrArg (mat 2 F) h
  rw [mat_longInv, mat_longInv] at h1
  have h3 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
  simp [mem_coords] at h3
  exact h2 (by linear_combination -h3)

theorem commute_longInv_of_centralizes_node {F : Type} [Field F] [Finite F]
    (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F) {G : Type} [Group G]
    (ψ : StatedSp 2 F →* G) (hψ : Function.Injective ψ) {g : G}
    (hg : ∀ x, g * ψ x * g⁻¹ ∈ ψ.range) (hg' : ∀ x, g⁻¹ * ψ x * g ∈ ψ.range)
    (hT : ∀ B : SL(2, F), g * ψ (shortBlock F fin_two_zero_ne_one B) =
      ψ (shortBlock F fin_two_zero_ne_one B) * g)
    (hc : g * ψ (longInv F 2 0 * longInv F 2 1) = ψ (longInv F 2 0 * longInv F 2 1) * g)
    (hog : Odd (orderOf g)) :
    g * ψ (longInv F 2 0) = ψ (longInv F 2 0) * g := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  obtain ⟨A, σ, hA⟩ := exists_semilinear_lift' hodd h4 ψ hker (MulAut.conj g)
    (fun x => by simpa [MulAut.conj_apply] using hg x)
    (fun x => by simpa [MulAut.conj_symm_apply] using hg' x)
  have hfix : ∀ B : SL(2, F), conjSp 2 F A (fieldSp 2 F σ (shortBlock F fin_two_zero_ne_one B)) =
      shortBlock F fin_two_zero_ne_one B := by
    intro B
    apply hψ
    rw [← hA, MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hT B)
  obtain ⟨hσ, hcase⟩ := conj_longInv_of_centralizes_shortBlock h2 A σ hfix
  subst hσ
  have hz0 : g * ψ (longInv F 2 0) * g⁻¹ = ψ (conjSp 2 F A (longInv F 2 0)) := by
    have := hA (longInv F 2 0)
    simpa [MulAut.conj_apply] using this
  rcases hcase with h | h
  · rw [h] at hz0
    exact mul_inv_eq_iff_eq_mul.mp hz0
  · exfalso
    rw [h] at hz0
    set u₀ := ψ (longInv F 2 0) with hu₀
    set u₁ := ψ (longInv F 2 1) with hu₁
    have hcomm : u₀ * u₁ = u₁ * u₀ := by
      rw [hu₀, hu₁, ← map_mul, ← map_mul]
      exact congrArg ψ (Models.SymplecticPairs.commute_longBlock_longBlock
        fin_two_zero_ne_one (-1) (-1)).eq
    have hc' : g * (u₀ * u₁) * g⁻¹ = u₀ * u₁ := by
      rw [map_mul] at hc
      exact mul_inv_eq_iff_eq_mul.mpr hc
    have h1 : g * u₁ * g⁻¹ = u₀ := by
      have e : g * (u₀ * u₁) * g⁻¹ = (g * u₀ * g⁻¹) * (g * u₁ * g⁻¹) := by group
      rw [e, hz0, hcomm] at hc'
      have := mul_left_cancel hc'
      exact this
    have hsq : g * g * u₀ * (g * g)⁻¹ = u₀ := by
      calc g * g * u₀ * (g * g)⁻¹ = g * (g * u₀ * g⁻¹) * g⁻¹ := by group
        _ = u₀ := by rw [hz0, h1]
    obtain ⟨k, hk⟩ := hog
    have hpow : g ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one g
    have hg_eq : g = (g * g) ^ (k + 1) := by
      calc g = g ^ (2 * k + 1) * g := by rw [hpow, one_mul]
        _ = (g * g) ^ (k + 1) := by rw [← pow_two, ← pow_mul, ← pow_succ]; ring_nf
    have hconj : ∀ n : ℕ, (g * g) ^ n * u₀ * ((g * g) ^ n)⁻¹ = u₀ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (g * g) ^ (n + 1) * u₀ * ((g * g) ^ (n + 1))⁻¹
            = (g * g) ^ n * (g * g * u₀ * (g * g)⁻¹) * ((g * g) ^ n)⁻¹ := by
              rw [pow_succ, mul_inv_rev, mul_assoc, mul_assoc, mul_assoc]
              group
          _ = u₀ := by rw [hsq]; exact ih
    have := hconj (k + 1)
    rw [← hg_eq, hz0] at this
    exact longInv_zero_ne_one h2 (hψ this.symm)

theorem nonempty_equiv_node {F : Type} [Field F] {G : Type} [Group G] (ψ : StatedSp 2 F →* G)
    (hψ : Function.Injective ψ) :
    Nonempty (SL(2, F) ≃* ↥((shortBlock F fin_two_zero_ne_one).range.map ψ)) :=
  ⟨(MonoidHom.ofInjective
    (Models.SymplecticPairs.shortBlock_injective (K := F) fin_two_zero_ne_one)).trans
    (Subgroup.equivMapOfInjective _ ψ hψ)⟩

section Charts

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {Fr : Frame p f 2 Ω K z} {l : Fin 3}

open CFSG.ClassicalInvolution.Models.SymplecticPairs (suppGroup_coords_zero_union_one)

noncomputable def toSupp2 (F : Type) [Field F] : StatedSp 2 F →*
    ↥(suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) : Subgroup (StatedSp 2 F)) where
  toFun x := ⟨x, by rw [suppGroup_coords_zero_union_one]; exact Subgroup.mem_top x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toSupp2_injective (F : Type) [Field F] : Function.Injective (toSupp2 F) :=
  fun _ _ h => congrArg Subtype.val h

theorem toSupp2_surjective (F : Type) [Field F] : Function.Surjective (toSupp2 F) :=
  fun y => ⟨y.1, Subtype.ext rfl⟩

theorem map_toSupp2 (F : Type) [Field F] (X : Subgroup (StatedSp 2 F)) :
    X.map (toSupp2 F) = X.subgroupOf (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2))) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨y.1, hy, Subtype.ext rfl⟩⟩

@[expose] noncomputable def LocalFrameI.layerSp (S : CSetupW p f 2 Ω K z)
    (LF : LocalFrameI Fr l) : StatedSp 2 (GaloisField p f) →* G :=
  (LF.layerHom S fin_two_zero_ne_one).comp (toSupp2 (GaloisField p f))

theorem LocalFrameI.layerSp_injective (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l) :
    Function.Injective (LF.layerSp S) :=
  (LF.layerHom_injective S fin_two_zero_ne_one).comp (toSupp2_injective _)

theorem LocalFrameI.layerSp_range (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l) :
    (LF.layerSp S).range = Mf Fr (l.succAbove 0) (l.succAbove 1) := by
  rw [← LF.layerHom_range S fin_two_zero_ne_one, MonoidHom.range_eq_map, MonoidHom.range_eq_map,
    LocalFrameI.layerSp, ← Subgroup.map_map, Subgroup.map_top_of_surjective _
      (toSupp2_surjective _)]

theorem LocalFrameI.layerSp_longInv (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    (a : Fin 2) :
    LF.layerSp S (longInv (GaloisField p f) 2 a) = Fr.zf (l.succAbove a) := by
  have hmem : longInv (GaloisField p f) 2 a ∈
      suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) := by
    rw [suppGroup_coords_zero_union_one]
    exact Subgroup.mem_top _
  have hzM : Fr.zf (l.succAbove a) ∈ Mf Fr (l.succAbove 0) (l.succAbove 1) :=
    zf_mem_MfW Fr S _ (by fin_cases a <;> simp)
  have key : LF.layerEquiv S fin_two_zero_ne_one ⟨longInv (GaloisField p f) 2 a, hmem⟩ =
      ⟨Fr.zf (l.succAbove a), hzM⟩ := by
    apply LF.injective_locHom_Mf S fin_two_zero_ne_one
    rw [LF.locHom_layerEquiv S fin_two_zero_ne_one]
    exact (LF.mk_zfW S a).symm
  exact congrArg Subtype.val key

theorem LocalFrameI.exists_chart (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    {T : Subgroup G} (hT : T ≤ Mf Fr (l.succAbove 0) (l.succAbove 1))
    (hA : IsAdaptedShortIn (Mf Fr (l.succAbove 0) (l.succAbove 1)) (Fr.Tf (l.succAbove 0))
      (Fr.Tf (l.succAbove 1)) (Fr.zf (l.succAbove 0)) T) :
    ∃ ψ : StatedSp 2 (GaloisField p f) →* G, Function.Injective ψ ∧
      ψ.range = Mf Fr (l.succAbove 0) (l.succAbove 1) ∧
      (∀ a : Fin 2, ψ (longInv (GaloisField p f) 2 a) = Fr.zf (l.succAbove a)) ∧
      T = (shortBlock (GaloisField p f) fin_two_zero_ne_one).range.map ψ := by
  obtain ⟨s, hs, hTs⟩ := (LF.isAdaptedShortIn_iff S fin_two_zero_ne_one hT).mp hA
  have hlay : ∀ X : Subgroup (StatedSp 2 (GaloisField p f)),
      (X.subgroupOf (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)))).map
        (LF.layerHom S fin_two_zero_ne_one) = X.map (LF.layerSp S) := by
    intro X
    rw [← map_toSupp2, Subgroup.map_map]
    rfl
  rcases hs with rfl | rfl
  · exact ⟨LF.layerSp S, LF.layerSp_injective S, LF.layerSp_range S, LF.layerSp_longInv S,
      by rw [hTs, hlay]⟩
  · set w := planeWeyl (GaloisField p f) 2 1 with hw
    have hc0 : Commute w (longInv (GaloisField p f) 2 0) :=
      Models.SymplecticPairs.commute_planeWeyl_longInv fin_two_zero_ne_one
    have hc1 : Commute w (longInv (GaloisField p f) 2 1) := by
      have hcen := (CFSG.ClassicalInvolution.mem_center_sl2_iff (-1 : SL(2, GaloisField p f))).mpr
        (Or.inr rfl)
      have h := Subgroup.mem_center_iff.mp hcen (weylMat (GaloisField p f))
      exact Commute.map (show Commute (weylMat (GaloisField p f)) (-1) from h)
        (longBlock (GaloisField p f) 2 1)
    have hfix : ∀ a : Fin 2, w * longInv (GaloisField p f) 2 a * w⁻¹ =
        longInv (GaloisField p f) 2 a := by
      intro a
      fin_cases a
      · exact mul_inv_eq_iff_eq_mul.mpr hc0.eq
      · exact mul_inv_eq_iff_eq_mul.mpr hc1.eq
    refine ⟨(LF.layerSp S).comp (MulAut.conj w).toMonoidHom,
      (LF.layerSp_injective S).comp (MulAut.conj w).injective, ?_, ?_, ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj w).surjective,
        ← MonoidHom.range_eq_map, LF.layerSp_range S]
    · intro a
      change LF.layerSp S (w * longInv (GaloisField p f) 2 a * w⁻¹) = _
      rw [hfix a, LF.layerSp_longInv S a]
    · rw [hTs, hlay, shortGroupNeg, Subgroup.map_map]

end Charts

end CFSG.ClassicalInvolution.RouteD
