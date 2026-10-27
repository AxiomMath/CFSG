module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUnique
public import CFSG.Monster.B.Classical.PlaneAut
public meta import CFSG.Monster.B.Classical.PlaneData
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2036

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open CFSG.Fischer CFSG.Monster.B.Classical.Plane Module

abbrev Vec3 : Type := Fin 3 → F4

abbrev PG24Point : Type := {W : Submodule F4 Vec3 // finrank F4 W = 1}

abbrev PG24Plane : Type := {W : Submodule F4 Vec3 // finrank F4 W = 2}

instance : Finite (Submodule F4 Vec3) :=
  Finite.of_injective (fun W : Submodule F4 Vec3 => (W : Set Vec3)) SetLike.coe_injective

instance : Fintype PG24Point := Fintype.ofFinite _

instance : Fintype PG24Plane := Fintype.ofFinite _

instance : DecidableEq PG24Point := Classical.decEq _

instance (W : Submodule F4 Vec3) : DecidablePred fun p : PG24Point => (p : Submodule F4 Vec3) ≤ W :=
  Classical.decPred _

@[expose] def PG24Lines : Finset (Finset PG24Point) :=
  Finset.univ.image fun W : PG24Plane =>
    Finset.univ.filter fun p : PG24Point => (p : Submodule F4 Vec3) ≤ W

@[expose] def ptEquiv : Fin 21 ≃ PG24Point :=
  Ωproj.trans (Projectivization.equivSubmodule F4 Vec3)

theorem coe_ptEquiv (i : Fin 21) :
    (ptEquiv i : Submodule F4 Vec3) = Submodule.span F4 {Ω i} := rfl

theorem ptEquiv_le_iff (i : Fin 21) (W : Submodule F4 Vec3) :
    (ptEquiv i : Submodule F4 Vec3) ≤ W ↔ Ω i ∈ W := by
  rw [coe_ptEquiv, Submodule.span_singleton_le_iff_mem]

@[expose] def dotForm (c : Vec3) : Vec3 →ₗ[F4] F4 :=
  ∑ k : Fin 3, c k • LinearMap.proj k

theorem dotForm_apply (c v : Vec3) : dotForm c v = ∑ k, c k * v k := by
  simp [dotForm]

theorem dotForm_surjective {c : Vec3} (hc : c ≠ 0) : Function.Surjective (dotForm c) := by
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  intro t
  refine ⟨Pi.single k ((c k)⁻¹ * t), ?_⟩
  rw [dotForm_apply, Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp [hk]

theorem finrank_ker_dotForm {c : Vec3} (hc : c ≠ 0) :
    finrank F4 (LinearMap.ker (dotForm c)) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotForm c)
  rw [LinearMap.range_eq_top.2 (dotForm_surjective hc), finrank_top, finrank_self,
    finrank_fin_fun] at h
  omega

@[expose] def planeOf (a : Fin 21) : PG24Plane :=
  ⟨LinearMap.ker (dotForm (Ω a)), finrank_ker_dotForm (Ω_ne_zero a)⟩

theorem Ω_mem_planeOf (a i : Fin 21) :
    Ω i ∈ (planeOf a : Submodule F4 Vec3) ↔ i ∈ projLine a := by
  simp [planeOf, dotForm_apply, projLine]

theorem exists_planeOf_eq (W : PG24Plane) : ∃ a, planeOf a = W := by
  have hlt : (W : Submodule F4 Vec3) < ⊤ := by
    refine lt_of_le_of_ne le_top fun e => ?_
    have := W.2
    rw [e, finrank_top, finrank_fin_fun] at this
    omega
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Vec3 := fun k => f (fun j => if k = j then 1 else 0)
  have hfc : f = dotForm c := by
    refine LinearMap.ext fun v => ?_
    conv_lhs => rw [pi_eq_sum_univ v]
    rw [map_sum, dotForm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hc : c ≠ 0 := fun h => hf0 (by rw [hfc, h]; ext; simp [dotForm_apply])
  obtain ⟨t, ht, hct⟩ := exists_smul_Ω_normIdx c hc
  refine ⟨normIdx c, Subtype.ext ?_⟩
  have hker : LinearMap.ker (dotForm (Ω (normIdx c))) = LinearMap.ker f := by
    ext v
    simp only [LinearMap.mem_ker, hfc, dotForm_apply]
    conv_rhs => rw [hct]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.1 h).resolve_left ht⟩
  change LinearMap.ker (dotForm (Ω (normIdx c))) = W
  rw [hker]
  refine (Submodule.eq_of_le_of_finrank_eq hfW ?_).symm
  rw [W.2]
  have hf : f ≠ 0 := hf0
  rw [hfc] at hf ⊢
  exact (finrank_ker_dotForm hc).symm

theorem map_ptEquiv_projLine (a : Fin 21) :
    (projLine a).map ptEquiv.toEmbedding =
      Finset.univ.filter fun p : PG24Point => (p : Submodule F4 Vec3) ≤ planeOf a := by
  ext p
  rw [Finset.mem_map_equiv, Finset.mem_filter, ← Ω_mem_planeOf, ← ptEquiv_le_iff,
    Equiv.apply_symm_apply]
  simp

theorem image_ptEquiv_lines :
    (Finset.univ.image projLine).image (fun L => L.map ptEquiv.toEmbedding) = PG24Lines := by
  ext L
  simp only [Finset.image_image, PG24Lines, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨planeOf a, (map_ptEquiv_projLine a).symm⟩
  · rintro ⟨W, rfl⟩
    obtain ⟨a, rfl⟩ := exists_planeOf_eq W
    exact ⟨a, map_ptEquiv_projLine a⟩

theorem isSteinerPlane_projLine : IsSteinerPlane (Finset.univ.image projLine) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro L hL
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hL
    revert a
    exact Certificates.certificate2036.1
  · intro T hT
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hT
    have key : ∀ x y : Fin 21, x ≠ y → ∃ a : Fin 21, (x ∈ projLine a ∧ y ∈ projLine a) ∧
        ∀ b : Fin 21, x ∈ projLine b ∧ y ∈ projLine b → b = a :=
      Certificates.certificate2036.2
    obtain ⟨a, ha, hu⟩ := key x y hxy
    refine ⟨projLine a, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ a), ?_⟩, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha.1
      · exact ha.2
    · rintro L ⟨hL, hT⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hL
      rw [hu b ⟨hT (by simp), hT (by simp)⟩]

theorem IsSteinerPlane.map {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    {𝓛 : Finset (Finset P)} (h : IsSteinerPlane 𝓛) (e : P ≃ Q) :
    IsSteinerPlane (𝓛.image fun L => L.map e.toEmbedding) := by
  refine ⟨by rw [← h.card_points, Fintype.card_congr e], ?_, ?_⟩
  · intro L hL
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hL
    rw [Finset.card_map, h.card_line hM]
  · intro T hT
    obtain ⟨L, ⟨hL, hTL⟩, hu⟩ := h.2.2 (T.map e.symm.toEmbedding) (by rw [Finset.card_map, hT])
    refine ⟨L.map e.toEmbedding, ⟨Finset.mem_image_of_mem _ hL, ?_⟩, ?_⟩
    · intro q hq
      rw [Finset.mem_map_equiv]
      exact hTL (Finset.mem_map_equiv.2 (by simpa using hq))
    · rintro L' ⟨hL', hTL'⟩
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hL'
      rw [hu M ⟨hM, fun p hp => ?_⟩]
      rw [Finset.mem_map_equiv] at hp
      have := hTL' hp
      rwa [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply] at this

theorem isSteinerPlane_PG24 : IsSteinerPlane PG24Lines := by
  rw [← image_ptEquiv_lines]
  exact isSteinerPlane_projLine.map ptEquiv

theorem iso_PG24 {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}
    (h : IsSteinerPlane 𝓛) :
    ∃ e : P ≃ PG24Point, ∀ L : Finset P, L ∈ 𝓛 ↔ L.map e.toEmbedding ∈ PG24Lines := by
  obtain ⟨ι, hι⟩ := steinerPlane_iso_projLine h
  refine ⟨ι.trans ptEquiv, fun L => ?_⟩
  rw [← image_ptEquiv_lines, ← hι, Finset.image_image]
  constructor
  · intro hL
    refine Finset.mem_image.2 ⟨L, hL, ?_⟩
    simp only [Function.comp, Finset.map_map]
    rfl
  · intro hL
    obtain ⟨M, hM, e⟩ := Finset.mem_image.1 hL
    have : M = L := by
      have e' : M.map (ι.trans ptEquiv).toEmbedding = L.map (ι.trans ptEquiv).toEmbedding := by
        rw [← e]
        simp only [Function.comp, Finset.map_map]
        rfl
      exact Finset.map_injective _ e'
    exact this ▸ hM

end CFSG.ComponentClassification.WittDesign
