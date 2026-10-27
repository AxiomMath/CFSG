module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015E6Y
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2DiagEmbed
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.EvenSmallLie.TwoE6 Subgroup
open CFSG.Timmesfeld.LieEmbed (e6n)
open CFSG.RankThree.CentralCover (sl2Upper)
open scoped MatrixGroups

namespace I1015


section Central

variable {k : Type} [Field k]

theorem hm_prod_mem_center_gen {u : kˣ} (hu : u ^ 3 = 1) :
    e6Data_valid.hm k (e6n 0) u * e6Data_valid.hm k (e6n 2) (u ^ 2) *
        (e6Data_valid.hm k (e6n 5) (u ^ 2) * e6Data_valid.hm k (e6n 4) u) ∈
      center (e6Data_valid.minGroup k) := by
  set z := e6Data_valid.hm k (e6n 0) u * e6Data_valid.hm k (e6n 2) (u ^ 2) *
    (e6Data_valid.hm k (e6n 5) (u ^ 2) * e6Data_valid.hm k (e6n 4) u) with hz
  have key : ∀ γ, IsRoot .E6 γ → ∀ c,
      z * e6Data_valid.xm k γ c * z⁻¹ = e6Data_valid.xm k γ c := by
    intro γ hγ c
    obtain ⟨m, hm⟩ := e6_center_weight_check γ (mem_rootFinset.2 hγ)
    have e : z * e6Data_valid.xm k γ c * z⁻¹ =
        e6Data_valid.hm k (e6n 0) u * (e6Data_valid.hm k (e6n 2) (u ^ 2) *
          (e6Data_valid.hm k (e6n 5) (u ^ 2) * (e6Data_valid.hm k (e6n 4) u *
            e6Data_valid.xm k γ c * (e6Data_valid.hm k (e6n 4) u)⁻¹) *
              (e6Data_valid.hm k (e6n 5) (u ^ 2))⁻¹) *
                (e6Data_valid.hm k (e6n 2) (u ^ 2))⁻¹) * (e6Data_valid.hm k (e6n 0) u)⁻¹ := by
      rw [hz]; group
    rw [e, MinData.Valid.hm_conj_xm _ _ hγ, MinData.Valid.hm_conj_xm _ _ hγ,
      MinData.Valid.hm_conj_xm _ _ hγ, MinData.Valid.hm_conj_xm _ _ hγ, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, ← zpow_add]
    have hexp : MinData.toWeight γ (e6n 0) + (2 : ℕ) * MinData.toWeight γ (e6n 2) +
        (2 : ℕ) * MinData.toWeight γ (e6n 5) + MinData.toWeight γ (e6n 4) = 3 * m := by
      push_cast; linarith
    rw [hexp, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hu, one_zpow,
      Units.val_one, one_mul]
  have hle : (⊤ : Subgroup (e6Data_valid.minGroup k)) ≤ centralizer {z} := by
    rw [← e6Data_valid.iSup_rootGroup]
    refine iSup₂_le fun γ hγ x hx => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    rw [mem_centralizer_singleton_iff]
    have := key γ hγ c
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  exact mem_center_iff.2 fun g => mem_centralizer_singleton_iff.1 (hle (mem_top g))

end Central

section ZElt

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] def zElt (u : kˣ) : fixedGroup k θ :=
  ⟨hPairE θ (nd 0) (nd 5) u * hPairE θ (nd 2) (nd 4) (u ^ 2),
    mul_mem (hHatE_le_fixedGroup θ hθ (nf 3) (by
      change _ ∈ (hPairE θ (nd 0) (nd 5)).range
      exact ⟨u, rfl⟩)) (hHatE_le_fixedGroup θ hθ (nf 2) (by
      change _ ∈ (hPairE θ (nd 2) (nd 4)).range
      exact ⟨u ^ 2, rfl⟩))⟩

theorem zElt_val (u : kˣ) : (zElt θ hθ u : e6Data_valid.minGroup k) =
    hPairE θ (nd 0) (nd 5) u * hPairE θ (nd 2) (nd 4) (u ^ 2) := rfl

theorem zElt_val_eq {u : kˣ} (hu : u ^ 3 = 1) (hθu : Units.map (θ : k →* k) u = u ^ 2) :
    (zElt θ hθ u : e6Data_valid.minGroup k) =
      e6Data_valid.hm k (e6n 0) u * e6Data_valid.hm k (e6n 5) (u ^ 2) *
        (e6Data_valid.hm k (e6n 2) (u ^ 2) * e6Data_valid.hm k (e6n 4) u) := by
  have h4 : Units.map (θ : k →* k) (u ^ 2) = u := by
    rw [map_pow, hθu, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hu, one_mul]
  rw [zElt_val]
  change e6Data_valid.hm k (nd 0) u * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) u) *
    (e6Data_valid.hm k (nd 2) (u ^ 2) * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) (u ^ 2))) = _
  rw [hθu, h4]
  rfl

theorem zElt_mem_center {u : kˣ} (hu : u ^ 3 = 1) (hθu : Units.map (θ : k →* k) u = u ^ 2) :
    zElt θ hθ u ∈ Subgroup.center (fixedGroup k θ) := by
  have hc := hm_prod_mem_center_gen (k := k) hu
  have hcomm : e6Data_valid.hm k (e6n 5) (u ^ 2) * e6Data_valid.hm k (e6n 2) (u ^ 2) =
      e6Data_valid.hm k (e6n 2) (u ^ 2) * e6Data_valid.hm k (e6n 5) (u ^ 2) :=
    (hm_commute (e6n 5) (e6n 2) _ _).eq
  have hz : (zElt θ hθ u : e6Data_valid.minGroup k) =
      e6Data_valid.hm k (e6n 0) u * e6Data_valid.hm k (e6n 2) (u ^ 2) *
        (e6Data_valid.hm k (e6n 5) (u ^ 2) * e6Data_valid.hm k (e6n 4) u) := by
    rw [zElt_val_eq θ hθ hu hθu, mul_assoc (e6Data_valid.hm k (e6n 0) u),
      mul_assoc (e6Data_valid.hm k (e6n 0) u), ← mul_assoc (e6Data_valid.hm k (e6n 5) (u ^ 2)),
      hcomm, mul_assoc]
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have := Subgroup.mem_center_iff.1 hc (g : e6Data_valid.minGroup k)
  rw [← hz] at this
  exact this

theorem zElt_pow_three {u : kˣ} (hu : u ^ 3 = 1) : zElt θ hθ u ^ 3 = 1 := by
  apply Subtype.ext
  have hab : Commute (hPairE θ (nd 0) (nd 5) u) (hPairE θ (nd 2) (nd 4) (u ^ 2)) := by
    change Commute (e6Data_valid.hm k (nd 0) u * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) u))
      (e6Data_valid.hm k (nd 2) (u ^ 2) *
        e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) (u ^ 2)))
    exact (((hm_commute _ _ _ _).mul_right (hm_commute _ _ _ _)).mul_left
      ((hm_commute _ _ _ _).mul_right (hm_commute _ _ _ _)))
  have hu2 : (u ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
  rw [SubgroupClass.coe_pow, zElt_val, hab.mul_pow, ← map_pow, ← map_pow, hu, hu2, map_one,
    map_one, mul_one]
  rfl

theorem zElt_ne_one {u : kˣ} (hu : u ^ 3 = 1) (hθu : Units.map (θ : k →* k) u = u ^ 2) (hu1 : u ≠ 1) :
    zElt θ hθ u ≠ 1 := by
  intro h
  have h1 : (zElt θ hθ u : e6Data_valid.minGroup k) = 1 := congrArg Subtype.val h
  rw [zElt_val_eq θ hθ hu hθu] at h1
  have h2 := congrArg (fun g => e6Data_valid.endo k g (Finsupp.single e6TopWeight (1 : k))) h1
  obtain ⟨w0, w2, w4, w5⟩ := wt_e6TopWeight
  simp only [MinData.Valid.endo_mul, MinData.Valid.endo_hm, Module.End.mul_apply,
    MinData.hDiag_single, w0, w2, w4, w5, zpow_zero, zpow_one, Units.val_one, one_smul,
    MinData.Valid.endo_one, Module.End.one_apply] at h2
  have h3 := congrArg (fun v : Fin e6Data.d →₀ k => v e6TopWeight) h2
  simp at h3
  exact hu1 h3

end ZElt

section Main

variable {k : Type} [Field k] [Finite k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

include hθ in
theorem e6_exists_Y [CharP k 2] {t : kˣ} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hθt : Units.map (θ : k →* k) t = t ^ 2) :
    ∃ (Y : Subgroup (fixedGroup k θ)) (u z : fixedGroup k θ), IsElemAbelian 3 Y ∧
      3 ^ 4 ≤ Nat.card Y ∧ u * u = 1 ∧ u ∉ Subgroup.center (fixedGroup k θ) ∧
      (∀ y ∈ Y, y * u = u * y) ∧ z ∈ Subgroup.center (fixedGroup k θ) ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      z ∉ Y := by
  haveI : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  haveI : Finite (e6Data_valid.minGroup k) := inferInstance
  haveI : Finite (fixedGroup k θ) := inferInstance
  have hF : ringChar (ZMod 2) = 2 := ZMod.ringChar_zmod_n 2
  let j : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k
  have hj : ∀ x, θ (j x) = j x := fun x => by
    have := RingHom.ext_zmod (θ.comp j) j
    exact congrArg (fun f => f x) this
  set φ := te6SL2 θ j hj with hφ
  have htt : t * Units.map (θ : k →* k) t = 1 := by rw [hθt, ← pow_succ']; exact ht3
  have ht2 : ((t : k)) ^ 2 ≠ 1 := by
    intro h
    apply ht1
    have h' : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h', inv_one, one_mul]
  let e : Fin 3 → fixedGroup k θ := fun i => φ i.castSucc (sl2Three (ZMod 2))
  let y : Fin 3 → fixedGroup k θ := fun i => φ i.castSucc (sl2Upper 1)
  let u : fixedGroup k θ := φ 3 (sl2Upper 1)
  let s : fixedGroup k θ := te6Torus θ hθ t
  have hcomm : ∀ i i', i ≠ i' → ∀ A B : SL(2, ZMod 2), φ i A * φ i' B = φ i' B * φ i A :=
    fun i i' hii A B => te6SL2_commute θ j hj hii A B
  have hsφ : ∀ i A, Commute (φ i A) s := fun i A =>
    (te6Torus_commute θ j hj hθ htt i A).symm
  have hne : ∀ i : Fin 3, i.castSucc ≠ 3 := fun i h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hee : ∀ i i', Commute (e i) (e i') := fun i i' => by
    by_cases h : i = i'
    · subst h
      exact Commute.refl _
    · exact hcomm _ _ (fun h' => h (Fin.castSucc_injective _ h')) _ _
  have hs3 : s ^ 3 = 1 := by rw [te6Torus_pow, ht3, te6Torus_one]
  have hsc : s ∉ Subgroup.center (fixedGroup k θ) := te6Torus_not_mem_center θ hθ ht2
  have hY := exists_Y_of_witness e s y hee (fun i => hsφ _ _)
    (fun i => by rw [← map_pow, sl2Three_pow_three, map_one]) hs3
    (fun h => hsc (h ▸ Subgroup.one_mem _))
    (fun i i' h => hcomm _ _ (fun h' => h (Fin.castSucc_injective _ h')) _ _)
    (fun i => hsφ _ _)
    (fun i h => sl2Three_not_commute _ (te6SL2_injective θ j hj _
      (by rw [map_mul, map_mul]; exact h.eq.symm)))
  obtain ⟨Y, hYdef, hYe, hYc⟩ := hY
  have hu2 : u * u = 1 := by
    have h2 : sl2Upper (1 : ZMod 2) * sl2Upper 1 = 1 := by
      have := orderOf_sl2Upper_one hF
      have h3 : sl2Upper (1 : ZMod 2) ^ orderOf (sl2Upper (1 : ZMod 2)) = 1 :=
        pow_orderOf_eq_one _
      rw [this, pow_two] at h3
      exact h3
    show φ 3 (sl2Upper 1) * φ 3 (sl2Upper 1) = 1
    rw [← map_mul, h2, map_one]
  have hu1 : sl2Upper (1 : ZMod 2) ≠ 1 := by
    intro h
    have := orderOf_sl2Upper_one hF
    rw [h, orderOf_one] at this
    omega
  have huc : u ∉ Subgroup.center (fixedGroup k θ) := fun h => hu1 (te6SL2_central θ j hj 3 h)
  have hYu : ∀ x ∈ Y, x * u = u * x := by
    have hle : Y ≤ Subgroup.centralizer ({u} : Set (fixedGroup k θ)) := by
      rw [hYdef]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨o, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases o with _ | i
      · exact (hsφ 3 (sl2Upper 1)).symm.eq
      · exact (hcomm i.castSucc 3 (hne i) (sl2Three (ZMod 2)) (sl2Upper 1))
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hz := zElt_mem_center θ hθ ht3 hθt
  refine ⟨Y, u, zElt θ hθ t, hYe, ?_, hu2, huc, hYu, hz, zElt_pow_three θ hθ ht3,
    zElt_ne_one θ hθ ht3 hθt ht1, fun hzY => ?_⟩
  · simpa using hYc
  · refine zElt_ne_one θ hθ ht3 hθt ht1 (eq_one_of_mem_Y e s y hee (fun i => hsφ _ _)
      (fun i => by rw [← map_pow, sl2Three_pow_three, map_one]) hs3
      (fun i i' h => hcomm _ _ (fun h' => h (Fin.castSucc_injective _ h')) _ _)
      (fun i => hsφ _ _)
      (fun i h => sl2Three_not_commute _ (te6SL2_injective θ j hj _
        (by rw [map_mul, map_mul]; exact h.eq.symm)))
      ?_ (fun g => (Subgroup.mem_center_iff.1 hz g)) (hYdef ▸ hzY))
    by_contra hall
    push Not at hall
    exact hsc (Subgroup.mem_center_iff.2 fun g => (hall g).eq)

end Main

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
