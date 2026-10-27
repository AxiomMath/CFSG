module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47PGLCent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement Pointwise

namespace P47PGL

section Syl

variable {A : Type} [Group A] [Finite A]

theorem exists_conj_le_sylow {K₁ Q V : Subgroup A} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K₁)
    (hV : IsPGroup 2 V) (hVK : V ≤ K₁) : ∃ c ∈ K₁, ∀ v ∈ V, c⁻¹ * v * c ∈ Q := by
  obtain ⟨S, hS⟩ := hQ
  have hV' : IsPGroup 2 ↥(V.subgroupOf K₁) := hV.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hV'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥K₁) P S
  refine ⟨((c⁻¹ : ↥K₁) : A), (c⁻¹).2, fun v hv => ?_⟩
  have h1 : (⟨v, hVK hv⟩ : ↥K₁) ∈ (P : Subgroup ↥K₁) := hP (Subgroup.mem_subgroupOf.2 hv)
  have e2 : ((c • P : Sylow 2 ↥K₁) : Subgroup ↥K₁) = MulAut.conj c • (P : Subgroup ↥K₁) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
  have hc' : (c • P : Sylow 2 ↥K₁) = S := hc
  have h2 : c * (⟨v, hVK hv⟩ : ↥K₁) * c⁻¹ ∈ (S : Subgroup ↥K₁) := by
    rw [← hc', e2, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨⟨v, hVK hv⟩, h1, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [← hS]
  refine Subgroup.mem_map.2 ⟨c * ⟨v, hVK hv⟩ * c⁻¹, h2, ?_⟩
  simp

end Syl

section Embed

variable {A : Type} [Group A] {F : Type} [Field F] {K : Subgroup A}

@[expose] def embedPGL (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F) :
    Matrix.ProjGenLinGroup (Fin 3) F →* A :=
  K.subtype.comp e.symm.toMonoidHom

theorem embedPGL_apply (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F)
    (y : Matrix.ProjGenLinGroup (Fin 3) F) : embedPGL e y = ((e.symm y : ↥K) : A) :=
  rfl

theorem embedPGL_injective (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F) :
    Function.Injective (embedPGL e) :=
  K.subtype_injective.comp e.symm.injective

theorem map_top_embedPGL (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F) :
    (⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)).map (embedPGL e) = K := by
  ext x
  rw [Subgroup.mem_map]
  refine ⟨?_, fun hx => ⟨e ⟨x, hx⟩, Subgroup.mem_top _, by simp [embedPGL_apply]⟩⟩
  rintro ⟨y, -, rfl⟩
  exact (e.symm y).2

theorem map_commutator_embedPGL (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F) :
    (⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)),
      (⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F))⁆).map (embedPGL e) = ⁅K, K⁆ := by
  rw [Subgroup.map_commutator, map_top_embedPGL]

end Embed

theorem commutator_ne_self_of_isPGL3Four {A : Type} [Group A] {K : Subgroup A}
    (h : IsPGL3Four ↥K) : ⁅K, K⁆ ≠ K := by
  obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := h
  intro hKK
  apply commutator_pgl_ne_top hF4
  apply Subgroup.map_injective (embedPGL_injective e)
  rw [map_commutator_embedPGL, map_top_embedPGL, hKK]

theorem inf_commutator_eq_bot_of_C43d1 {A : Type} [Group A] [Finite A] {k : Kind} {z : A}
    {X : Subgroup A} (hX : C43d1 k z X) : X ⊓ ⁅ncl X, ncl X⁆ = ⊥ := by
  obtain ⟨-, h3, hP, -⟩ := hX
  have : (ncl X).Normal := by unfold ncl; infer_instance
  have : (⁅ncl X, ncl X⁆).Normal := Subgroup.commutator_normal _ _
  by_contra hne
  have hdvd : Nat.card ↥(X ⊓ ⁅ncl X, ncl X⁆) ∣ Nat.card ↥X := Subgroup.card_dvd_of_le inf_le_left
  rw [h3] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact hne (Subgroup.card_eq_one.1 h)
  · have hXle : X ≤ ⁅ncl X, ncl X⁆ := by
      have : X ⊓ ⁅ncl X, ncl X⁆ = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h3])
      exact inf_eq_left.1 this
    have hKle : ncl X ≤ ⁅ncl X, ncl X⁆ := Subgroup.normalClosure_le_normal hXle
    exact commutator_ne_self_of_isPGL3Four hP
      (le_antisymm (Subgroup.commutator_le_left _ _) hKle)

end P47PGL

open P47PGL

theorem not_le_centralizer_sylow2_C43d1 {A : Type} [Group A] [Finite A] {k : Kind} {z : A}
    {X : Subgroup A} (hX : C43d1 k z X) {Q : Subgroup A}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q ⁅ncl X, ncl X⁆) : ¬ X ≤ centralizer (Q : Set A) := by
  intro hc
  obtain ⟨-, h3, ⟨F, _, _, hF4, ⟨e⟩⟩, -⟩ := hX
  have : (ncl X).Normal := by unfold ncl; infer_instance
  have h2 := char_two_of_card_four hF4
  have hcube := cube_eq_one_of_card_four hF4
  have hV : (vSub F).map (embedPGL e) ≤ ⁅ncl X, ncl X⁆ := by
    rw [← map_commutator_embedPGL e]
    exact Subgroup.map_mono (vSub_le_commutator hF4)
  obtain ⟨c, hcK1, hcQ⟩ :=
    exists_conj_le_sylow hQ ((vSub_isPGroup hF4).map (embedPGL e)) hV
  have hcK : c ∈ ncl X := Subgroup.commutator_le_left (ncl X) (ncl X) hcK1
  have hXbot : X ≠ ⊥ := fun h => by
    have := Subgroup.card_eq_one.2 h
    omega
  obtain ⟨⟨g, hgX⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hXbot
  have hgK : g ∈ ncl X := Subgroup.subset_normalClosure hgX
  have hg3 : g ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥X) (x := ⟨g, hgX⟩)
    rw [h3] at h
    simpa using congrArg Subtype.val h
  have key : ∀ v ∈ (vSub F).map (embedPGL e), (c * g * c⁻¹) * v = v * (c * g * c⁻¹) := by
    intro v hv
    have h := (Subgroup.mem_centralizer_iff.1 (hc hgX)) _ (hcQ v hv)
    calc c * g * c⁻¹ * v = c * (g * (c⁻¹ * v * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * v * c) * g) * c⁻¹ := by rw [h]
      _ = v * (c * g * c⁻¹) := by group
  have hgh : c * g * c⁻¹ ∈ ncl X := (ncl X).mul_mem ((ncl X).mul_mem hcK hgK) ((ncl X).inv_mem hcK)
  have hcomm : ∀ m ∈ vSub F, e ⟨c * g * c⁻¹, hgh⟩ * m = m * e ⟨c * g * c⁻¹, hgh⟩ := by
    intro m hm
    have h := key (embedPGL e m) (Subgroup.mem_map_of_mem _ hm)
    have h' : (⟨c * g * c⁻¹, hgh⟩ : ↥(ncl X)) * e.symm m = e.symm m * ⟨c * g * c⁻¹, hgh⟩ :=
      Subtype.ext h
    simpa using congrArg e h'
  have hsq := sq_eq_one_of_comm h2 hcube (hcomm _ mk_x12_mem_vSub) (hcomm _ mk_x23_mem_vSub)
  have hgh2 : (⟨c * g * c⁻¹, hgh⟩ : ↥(ncl X)) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hsq, map_one]
  have hg2 : g ^ 2 = 1 := by
    have h0 : (c * g * c⁻¹) ^ 2 = 1 := by simpa using congrArg Subtype.val hgh2
    rw [conj_pow] at h0
    exact mul_eq_left.1 (mul_inv_eq_one.1 h0)
  have hg : g = 1 := by
    have h : g ^ 3 = g ^ 2 * g := pow_succ g 2
    rw [hg3, hg2, one_mul] at h
    exact h.symm
  exact hg1 (Subtype.ext hg)

theorem false_of_C43d1_sylow_normalizes {A : Type} [Group A] [Finite A] {k : Kind} {z : A}
    {X : Subgroup A} (hX : C43d1 k z X) {Q : Subgroup A}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q ⁅ncl X, ncl X⁆)
    (hn : Q ≤ normalizer (X : Set A)) : False := by
  refine not_le_centralizer_sylow2_C43d1 hX hQ ?_
  have : (ncl X).Normal := by unfold ncl; infer_instance
  have hK1 : (⁅ncl X, ncl X⁆).Normal := Subgroup.commutator_normal _ _
  have hbot := inf_commutator_eq_bot_of_C43d1 hX
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqK1 : q ∈ ⁅ncl X, ncl X⁆ := hQ.le hq
  have hqx : q * x * q⁻¹ ∈ X := (Subgroup.mem_set_normalizer_iff.1 (hn hq) x).1 hx
  have hmemX : q * x * q⁻¹ * x⁻¹ ∈ X := X.mul_mem hqx (X.inv_mem hx)
  have hmemK : q * x * q⁻¹ * x⁻¹ ∈ ⁅ncl X, ncl X⁆ := by
    have h1 : x * q⁻¹ * x⁻¹ ∈ ⁅ncl X, ncl X⁆ := hK1.conj_mem q⁻¹ (inv_mem hqK1) x
    simpa [mul_assoc] using mul_mem hqK1 h1
  have hone : q * x * q⁻¹ * x⁻¹ = 1 := by
    have hmem : q * x * q⁻¹ * x⁻¹ ∈ X ⊓ ⁅ncl X, ncl X⁆ := ⟨hmemX, hmemK⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hone)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
