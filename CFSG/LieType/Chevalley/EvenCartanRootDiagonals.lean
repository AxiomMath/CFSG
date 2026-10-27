module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem exists_det_transpose_cartan_eq_two_pow
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ n : ℕ, τ.cartan.transpose.det = 2 ^ n := by
  rw [Matrix.det_transpose]
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by rw [det_cartan_G2]; norm_num⟩
  · exact ⟨0, by rw [det_cartan_F4]; norm_num⟩
  · exact ⟨2, by rw [det_cartan_D4]; norm_num⟩
  · exact ⟨1, by rw [det_cartan_E7]; norm_num⟩
  · exact ⟨0, by rw [det_cartan_E8]; norm_num⟩

theorem existsUnique_zpow_two_pow_eq {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0)
    (n : ℕ) (a : Fˣ) : ∃! u : Fˣ, u ^ ((2 : ℤ) ^ n) = a := by
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have e : ∀ u : Fˣ, u ^ ((2 : ℤ) ^ n) = u ^ (2 ^ n) := fun u => by
    rw [← zpow_natCast]
    push_cast
    rfl
  have hinj : Function.Injective fun u : Fˣ => u ^ (2 ^ n) := fun u v h => by
    have h' : (u : F) ^ 2 ^ n = (v : F) ^ 2 ^ n := by
      have := congrArg Units.val h
      simpa only [Units.val_pow_eq_pow_val] using this
    refine Units.ext ((iterateFrobenius F 2 n).injective ?_)
    rwa [iterateFrobenius_def, iterateFrobenius_def]
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.1 hinj) a
  have hu' : u ^ 2 ^ n = a := hu
  refine ⟨u, (e u).trans hu', fun v hv => hinj ?_⟩
  have hv' : v ^ 2 ^ n = a := (e v).symm.trans hv
  change v ^ 2 ^ n = u ^ 2 ^ n
  rw [hv', hu']

theorem cartanChar_prod_zpow_adjugate {K : Type} [Field K] (u : Fin τ.rank → Kˣ) :
    cartanChar (fun j => ∏ i, u i ^ τ.cartan.transpose.adjugate j i) =
      fun l => u l ^ τ.cartan.transpose.det := by
  funext l
  set B := τ.cartan.transpose.adjugate
  calc ∏ j, (∏ i, u i ^ B j i) ^ τ.cartan j l
      = ∏ j, ∏ i, u i ^ (B j i * τ.cartan j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
    _ = ∏ i, ∏ j, u i ^ (B j i * τ.cartan j l) := Finset.prod_comm
    _ = ∏ i, u i ^ ((τ.cartan.transpose * B) l i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.transpose_apply, mul_comm]
    _ = u l ^ τ.cartan.transpose.det := by
        rw [Matrix.mul_adjugate, Finset.prod_eq_single l
          (fun i _ hi => by simp [Ne.symm hi]) (fun h => absurd (Finset.mem_univ l) h)]
        simp

theorem rootDiagUnit_eq_list_prod_torusElt_adjugate
    {K : Type} [Field K]
    {a u : Fin τ.rank → Kˣ} (hu : ∀ i, u i ^ τ.cartan.transpose.det = a i) :
    rootDiagUnit τ a = ((List.finRange τ.rank).map fun j =>
      torusElt τ K j (∏ i, u i ^ τ.cartan.transpose.adjugate j i)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_prod_zpow_adjugate]
  congr 1
  funext l
  exact (hu l).symm

theorem list_prod_torusElt_mem_torusGroup
    {K : Type} [Field K] (t : Fin τ.rank → Kˣ) :
    ((List.finRange τ.rank).map fun j => torusElt τ K j (t j)).prod ∈ torusGroup τ K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_torusGroup j _

theorem fixed_torusGroup_eq_map
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) (σ : K ≃+* K) :
    torusGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
      (torusGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := k.subtype
  obtain ⟨n, hn⟩ := exists_det_transpose_cartan_eq_two_pow hτ
  have h2k : (2 : k) = 0 := ι.injective (by rw [map_ofNat, map_zero]; exact h2)
  refine le_antisymm ?_ ?_
  · rintro h ⟨hh, hfix⟩
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    have hσa : ∀ i, σ (a i : K) = a i := by
      have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hfix
      have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
          rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom a)
      have h1 := rootDiagUnit_injective (h0.symm.trans hF)
      intro i
      exact congrArg Units.val (congrFun h1 i)
    set a' : Fin τ.rank → kˣ := fun i =>
      Units.mk0 ⟨a i, hσa i⟩ fun h => (a i).ne_zero (congrArg Subtype.val h)
    have ha' : ∀ i, Units.map ι.toMonoidHom (a' i) = a i := fun i => Units.ext rfl
    choose u hu _ using fun i => existsUnique_zpow_two_pow_eq h2k n (a' i)
    refine ⟨((List.finRange τ.rank).map fun j =>
      torusElt τ k j (∏ i, u i ^ τ.cartan.transpose.adjugate j i)).prod,
      list_prod_torusElt_mem_torusGroup _, ?_⟩
    rw [map_list_prod, List.map_map]
    rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := fun i => Units.map ι.toMonoidHom (u i))
      fun i => by rw [← map_zpow, hn, hu, ha']]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    rw [Function.comp_apply, baseChangeGL_torusElt, map_prod]
    simp only [map_zpow]
  · have hle : torusGroup τ k ≤ (torusGroup τ K).comap (baseChangeGL ι) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, s⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨hle hg, ?_⟩
    change baseChangeGL σ.toRingHom (baseChangeGL ι g) = baseChangeGL ι g
    rw [baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp ι = ι from RingHom.ext fun c => (mem_fixSubfield σ).1 c.2]

theorem even_power_two_Cartan_root_diagonals_inner
    (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K]
    (hK : ringChar K = 2) :
    (∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K) ∧
    (∀ (a : Fin τ.rank → Kˣ) (i : Fin τ.rank), ∃! u : Kˣ, u ^ τ.cartan.transpose.det = a i) ∧
    (∀ a u : Fin τ.rank → Kˣ, (∀ i, u i ^ τ.cartan.transpose.det = a i) →
      rootDiagUnit τ a = ((List.finRange τ.rank).map fun j =>
        torusElt τ K j (∏ i, u i ^ τ.cartan.transpose.adjugate j i)).prod) ∧
    ∀ σ : K ≃+* K,
      torusGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
        (torusGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_ringChar hK
  obtain ⟨n, hn⟩ := exists_det_transpose_cartan_eq_two_pow hτ
  have hroot : ∀ (a : Fin τ.rank → Kˣ) (i : Fin τ.rank),
      ∃! u : Kˣ, u ^ τ.cartan.transpose.det = a i := fun a i => by
    rw [hn]
    exact existsUnique_zpow_two_pow_eq h2 n (a i)
  refine ⟨fun a => ?_, hroot, fun a u hu => rootDiagUnit_eq_list_prod_torusElt_adjugate hu,
    fixed_torusGroup_eq_map hτ h2⟩
  choose u hu _ using hroot a
  rw [rootDiagUnit_eq_list_prod_torusElt_adjugate hu]
  exact list_prod_torusElt_mem_torusGroup _

end CFSG.LieType.Chevalley
