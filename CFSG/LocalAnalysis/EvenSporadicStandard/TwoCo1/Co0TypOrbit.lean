module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypForm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypEighth

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Open

theorem hammingNorm_ΩC_add_dod₂ : hammingNorm (((ΩC + dod₂ : C)) : Fin 24 → ZMod 2) = 12 := by
  have h : ((ΩC + dod₂ : C) : Fin 24 → ZMod 2) = permWord sigEl (dod₂ : Fin 24 → ZMod 2) := by
    rw [permWord_sigEl_dod₂, add_comm]
    rfl
  rw [h]
  exact (hammingNorm_comp_perm _ _).trans hammingNorm_dod₂

theorem exists_permC_wt12 (hcls : Co0ClassData) {d a : C}
    (hd : hammingNorm (d : Fin 24 → ZMod 2) = 12) (ha : hammingNorm (a : Fin 24 → ZMod 2) = 12) :
    ∃ p : AutPerm, permC p d = a := by
  obtain ⟨p₁, h₁⟩ := exists_permC_dod₂ hcls hd
  obtain ⟨p₂, h₂⟩ := exists_permC_dod₂ hcls ha
  refine ⟨p₂ * p₁⁻¹, ?_⟩
  rw [permC_mul, ← h₁, ← permC_mul p₁⁻¹ p₁, inv_mul_cancel, permC_one, h₂]

theorem invType_conj_gO
    (hcls : Co0ClassData)
    (c : latticeO) {a : C} (ha : hammingNorm (a : Fin 24 → ZMod 2) = 12) :
    InvType (⊤ : Subgroup latticeO) negOneO co0C3 (c * gO a * c⁻¹) := by
  have hsq : (c * gO a * c⁻¹) ^ 2 = 1 := by
    rw [conj_pow, pow_two, gO_mul_self]
    group
  have hne1 : c * gO a * c⁻¹ ≠ 1 := by
    intro h
    have h1 : gO a = 1 := by
      calc gO a = c⁻¹ * (c * gO a * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    have h2 : a = 0 := gO_injective (h1.trans gO_zero.symm)
    rw [h2] at ha
    simp at ha
  refine ⟨trivial, orderOf_eq_prime hsq hne1, ?_, ?_, ?_⟩
  · intro h
    have htr := congrArg (fun x => (mat x).trace) h
    simp only [trace_mat_conj, trace_mat_gO, ha, trace_mat_negOneO] at htr
    norm_num at htr
  · rintro ⟨v, -, hv⟩
    refine no_eighth_root_wt12 ha (c⁻¹ * v * c) ?_
    rw [show c⁻¹ * v * c = c⁻¹ * v * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hv]
    group
  · obtain ⟨p, hp⟩ := exists_permC_dod₂ hcls ha
    have hconj : c * gO a * c⁻¹ = (c * (PO p)⁻¹) * gO dod₂ * (c * (PO p)⁻¹)⁻¹ := by
      rw [← hp, ← PO_inv_mul_gO_mul_PO]
      group
    rw [centIn, top_inf_eq, hconj, card_centralizer_conj_singleton, hcls.card_cent_dod]

theorem wt12_of_invType (hcls : Co0ClassData) (c : latticeO)
    {a : C} (h : InvType (⊤ : Subgroup latticeO) negOneO co0C3 (c * gO a * c⁻¹)) :
    hammingNorm (a : Fin 24 → ZMod 2) = 12 := by
  obtain ⟨c', d₁, hd₁, hyc⟩ := typeC_form hcls h
  have h1 := congrArg (fun x => (mat x).trace) hyc
  simp only [trace_mat_conj, trace_mat_gO] at h1
  have hwt : hammingNorm (d₁ : Fin 24 → ZMod 2) = 12 := by
    rcases hd₁ with rfl | rfl
    · exact hammingNorm_dod₂
    · exact hammingNorm_ΩC_add_dod₂
  rw [hwt] at h1
  have : (hammingNorm (a : Fin 24 → ZMod 2) : ℚ) = 12 := by
    push_cast at h1
    linarith
  exact_mod_cast this

theorem invType_conj_gO_iff
    (hcls : Co0ClassData)
    (c : latticeO) (a : C) :
    InvType (⊤ : Subgroup latticeO) negOneO co0C3 (c * gO a * c⁻¹) ↔
      hammingNorm (a : Fin 24 → ZMod 2) = 12 :=
  ⟨wt12_of_invType hcls c, invType_conj_gO hcls c⟩

theorem hammingNorm_of_mem_conj_form {d₁ : C} (hd₁ : d₁ = dod₂ ∨ d₁ = ΩC + dod₂) :
    hammingNorm (d₁ : Fin 24 → ZMod 2) = 12 := by
  rcases hd₁ with rfl | rfl
  · exact hammingNorm_dod₂
  · exact hammingNorm_ΩC_add_dod₂

theorem lat_orbit_typeC
    (hcls : Co0ClassData) :
    ∀ y, InvType (⊤ : Subgroup latticeO) negOneO co0C3 y →
      Nat.card {t : latticeO | t ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) ∧
        InvType (⊤ : Subgroup latticeO) negOneO co0C3 t} = 2576 ∧
      ∀ t, t ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) →
        InvType (⊤ : Subgroup latticeO) negOneO co0C3 t →
          ∃ n ∈ (⊤ : Subgroup latticeO) ⊓ Subgroup.normalizer
            ((pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) : Subgroup latticeO) : Set latticeO),
            n * y * n⁻¹ = t := by
  intro y hy
  obtain ⟨c, d₁, hd₁, hyc⟩ := typeC_form hcls hy
  have hd₁wt := hammingNorm_of_mem_conj_form hd₁
  rw [pCoreOf_centIn_eq hcls hd₁ hyc]
  have hmem : ∀ a : C, c * gO a * c⁻¹ ∈ signSub.map (MulAut.conj c).toMonoidHom := fun a =>
    ⟨gO a, mem_signSub.2 ⟨a, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hform : ∀ t ∈ signSub.map (MulAut.conj c).toMonoidHom, ∃ a : C, t = c * gO a * c⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := mem_signSub.1 hx
    exact ⟨a, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  refine ⟨?_, ?_⟩
  · rw [← ncard_wt12, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
      (fun a : wt12 => (⟨c * gO a.1 * c⁻¹, hmem a.1, invType_conj_gO hcls c a.2⟩ :
        {t : latticeO | t ∈ signSub.map (MulAut.conj c).toMonoidHom ∧
          InvType (⊤ : Subgroup latticeO) negOneO co0C3 t})) ⟨?_, ?_⟩))
    · intro a a' h
      have h1 := congrArg Subtype.val h
      have h2 : gO a.1 = gO a'.1 := by
        simpa using h1
      exact Subtype.ext (gO_injective h2)
    · rintro ⟨t, ht, hinv⟩
      obtain ⟨a, rfl⟩ := hform t ht
      exact ⟨⟨a, (invType_conj_gO_iff hcls c a).1 hinv⟩, rfl⟩
  · intro t ht hinv
    obtain ⟨a, rfl⟩ := hform t ht
    have ha := (invType_conj_gO_iff hcls c a).1 hinv
    obtain ⟨p, hp⟩ := exists_permC_wt12 hcls hd₁wt ha
    refine ⟨c * (PO p)⁻¹ * c⁻¹, ⟨trivial, ?_⟩, ?_⟩
    · have hPO : (PO p)⁻¹ ∈ Subgroup.normalizer (signSub : Set latticeO) :=
        le_normalizer_signSub (H := monoSub ⊤) le_rfl
          ((monoSub ⊤).inv_mem (PO_mem_monoSub (Subgroup.mem_top p)))
      rw [← Subgroup.map_equiv_normalizer_eq (signSub : Subgroup latticeO) (MulAut.conj c)]
      exact ⟨(PO p)⁻¹, hPO, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [hyc]
      calc c * (PO p)⁻¹ * c⁻¹ * (c * gO d₁ * c⁻¹) * (c * (PO p)⁻¹ * c⁻¹)⁻¹
          = c * ((PO p)⁻¹ * gO d₁ * PO p) * c⁻¹ := by group
        _ = c * gO a * c⁻¹ := by rw [PO_inv_mul_gO_mul_PO, hp]

end CFSG.EvenSporadicStandard.TwoCo1
