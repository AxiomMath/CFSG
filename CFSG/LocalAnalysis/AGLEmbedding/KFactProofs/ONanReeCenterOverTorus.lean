module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public section

namespace CFSG.AGLEmbedding.ReeCenterOver

open Equiv CFSG.AGLEmbedding.ReeModel CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Torus

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))

@[expose] noncomputable def hElt (s : Kˣ) : ↥(ReeTag.G2.reeGamma K a) :=
  ⟨smallReeTorusElt a K s, ReeTag.reeFixedBorel_le_reeGamma
    (ReeTag.reeFixedTorus_le_reeFixedBorel (smallReeTorusElt_mem hK s))⟩

theorem hElt_mem_stdB (s : Kˣ) : hElt (a := a) hK s ∈ stdB a K :=
  Subgroup.mem_subgroupOf.2 (ReeTag.reeFixedTorus_le_reeFixedBorel (smallReeTorusElt_mem hK s))

theorem hElt_conj_zHom (s : Kˣ) (c : K) :
    hElt (a := a) hK s * zHom hK (Multiplicative.ofAdd c) * (hElt (a := a) hK s)⁻¹ =
      zHom hK (Multiplicative.ofAdd (((s : K) ^ 3 ^ a) * c)) := by
  apply Subtype.ext
  have h := smallReeTorusElt_conj_smallReeCoord hK s 0 0 c
  rw [mul_zero, mul_zero] at h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zHom, coe_zHom]
  exact h

variable {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

@[expose] noncomputable def nElt : ↥(ReeTag.G2.reeGamma K a) :=
  ⟨canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀, ReeTag.canonicalRep_longest_mem_reeGamma hw₀⟩

include hw₀ in
theorem nElt_mul_hElt (s : Kˣ) :
    nElt (a := a) (K := K) hw₀ * hElt (a := a) hK s * (nElt (a := a) (K := K) hw₀)⁻¹ =
      (hElt (a := a) hK s)⁻¹ := by
  apply Subtype.ext
  have hh : smallReeTorusElt a K s ∈ torusGroup ReeTag.G2.tag K :=
    (Subgroup.mem_inf.1 (smallReeTorusElt_mem hK s)).1
  have := ReeTag.canonicalRep_longest_conj_torus hw₀ hh
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  exact this

include hw₀ in
theorem exists_u_mul_nElt {g : ↥(ReeTag.G2.reeGamma K a)} (hg : g ∉ stdB a K) :
    ∃ u ∈ stdU a K, (u * nElt (a := a) (K := K) hw₀)⁻¹ * g ∈ stdB a K := by
  have hgB : (g : ModGL ReeTag.G2.tag K) ∉ ReeTag.G2.reeFixedBorel K a := fun h =>
    hg (Subgroup.mem_subgroupOf.2 h)
  obtain ⟨u, hu, hub⟩ := ReeTag.exists_reeFixedPosUnipotent_mul_canonicalRep (a := a) (K := K) hw₀
    g.2 hgB
  refine ⟨⟨u, ReeTag.reeFixedPosUnipotent_le_reeGamma hu⟩, Subgroup.mem_subgroupOf.2 hu, ?_⟩
  exact Subgroup.mem_subgroupOf.2 hub

include hK in
theorem exists_coord {x : ↥(ReeTag.G2.reeGamma K a)} (hx : x ∈ stdU a K) :
    ∃ t b c : K, (x : ModGL ReeTag.G2.tag K) = smallReeCoord a K t b c := by
  have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
    Subgroup.mem_subgroupOf.1 hx
  obtain ⟨t, b, c, h⟩ := exists_smallReeCoordU_eq hK
    (⟨(x : ModGL ReeTag.G2.tag K), hx'⟩ : ↥(ReeTag.G2.reeFixedPosUnipotent K a))
  exact ⟨t, b, c, (congrArg Subtype.val h).symm⟩


omit [CharP K ReeTag.G2.prime] in
include hK in
theorem exists_unit_pow (μ : Kˣ) : ∃ s : Kˣ, s ^ (2 * 3 ^ a - 1) = μ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  exact hbij.2 μ

include hK in
theorem eq_stdU_of_invariant (ha : 1 ≤ a) (S₀ : Subgroup ↥(ReeTag.G2.reeGamma K a))
    (hS₀U : S₀ ≤ stdU a K)
    (hinv : ∀ (s : Kˣ), ∀ x ∈ S₀, hElt (a := a) hK s * x * (hElt (a := a) hK s)⁻¹ ∈ S₀)
    {x₀ : ↥(ReeTag.G2.reeGamma K a)} (hx₀ : x₀ ∈ S₀) (hx₀3 : x₀ ^ 3 ≠ 1) :
    stdU a K ≤ S₀ := by
  obtain ⟨t₀, b₀, c₀, hx₀e⟩ := exists_coord hK (hS₀U hx₀)
  have ht₀ : t₀ ≠ 0 := by
    rintro rfl
    apply hx₀3
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx₀e]
    exact smallReeCoord_zero_pow_three b₀ c₀
  set U' : Subgroup (ModGL ReeTag.G2.tag K) := ReeTag.G2.reeFixedPosUnipotent K a with hU'
  let φ : ↥U' →* ↥(ReeTag.G2.reeGamma K a) :=
    Subgroup.inclusion ReeTag.reeFixedPosUnipotent_le_reeGamma
  set S' : Subgroup ↥U' := S₀.comap φ with hS'
  have hfr : frattini ↥U' = (smallReeU1 a K).subgroupOf U' :=
    ReeTag.frattini_reeFixedPosUnipotent hK ha
  have hker := ReeTag.ker_smallReePi hK
  have hsup : S' ⊔ frattini ↥U' = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨t, b, c, rfl⟩ := exists_smallReeCoordU_eq hK u
    by_cases ht : t = 0
    · subst ht
      exact Subgroup.mem_sup_right (by rw [hfr]; exact Subgroup.mem_subgroupOf.2 ⟨b, c, rfl⟩)
    · obtain ⟨s, hs⟩ := exists_unit_pow hK (Units.mk0 (t / t₀) (div_ne_zero ht ht₀))
      have hsv : (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K)) = t / t₀ := by
        rw [hs]; rfl
      have hx₁S : hElt (a := a) hK s * x₀ * (hElt (a := a) hK s)⁻¹ ∈ S₀ := hinv s x₀ hx₀
      have hx₁e : ((hElt (a := a) hK s * x₀ * (hElt (a := a) hK s)⁻¹ :
          ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
          smallReeCoord a K t (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b₀) ((s : K) ^ 3 ^ a * c₀) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx₀e]
        have h := smallReeTorusElt_conj_smallReeCoord hK s t₀ b₀ c₀
        have : (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K)) * t₀ = t := by rw [hsv]; field_simp
        rw [this] at h
        exact h
      set s' : ↥U' := smallReeCoordU hK t (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b₀)
        ((s : K) ^ 3 ^ a * c₀) with hs'
      have hs'S : s' ∈ S' := by
        change φ s' ∈ S₀
        have : φ s' = hElt (a := a) hK s * x₀ * (hElt (a := a) hK s)⁻¹ :=
          Subtype.ext hx₁e.symm
        rw [this]
        exact hx₁S
      have hπ : s'⁻¹ * smallReeCoordU hK t b c ∈ frattini ↥U' := by
        rw [hfr, ← hker, MonoidHom.mem_ker, map_mul, map_inv, hs', smallReePi_apply,
          smallReePi_apply]
        group
      have : smallReeCoordU hK t b c = s' * (s'⁻¹ * smallReeCoordU hK t b c) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hs'S hπ
  have htop : S' = ⊤ := frattini_nongenerating hsup
  intro x hx
  have hx' : (⟨(x : ModGL ReeTag.G2.tag K), Subgroup.mem_subgroupOf.1 hx⟩ : ↥U') ∈ S' := by
    rw [htop]; exact Subgroup.mem_top _
  exact hx'


theorem hElt_inv (s : Kˣ) : (hElt (a := a) hK s)⁻¹ = hElt (a := a) hK s⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change smallReeTorusElt a K s * smallReeTorusElt a K s⁻¹ = 1
  rw [← smallReeTorusElt_mul, mul_inv_cancel, smallReeTorusElt_one]

include hK in
theorem hElt_conj_mem_center {s : Kˣ} {z : ↥(ReeTag.G2.reeGamma K a)}
    (hz : z ∈ stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))) :
    hElt (a := a) hK s * z * (hElt (a := a) hK s)⁻¹ ∈ stdU a K ⊓ Subgroup.centralizer
      ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) := by
  rw [← zHom_range hK] at hz ⊢
  obtain ⟨c, rfl⟩ := hz
  have := hElt_conj_zHom hK s (Multiplicative.toAdd c)
  rw [ofAdd_toAdd] at this
  rw [this]
  exact ⟨_, rfl⟩

end Torus

end CFSG.AGLEmbedding.ReeCenterOver
