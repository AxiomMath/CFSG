module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gSyl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gSylModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped commutatorElement

section Model

open CFSG.ComponentClassification.PSL3Four


theorem fixSub_conjIso (i : Fin 4) :
    fixSub (Cls3.conjIso (rrR i)) = (CC i).subgroupOf S := by
  ext y
  rw [mem_fixSub, Subgroup.mem_subgroupOf, mem_CC]
  have h1 : (((Cls3.conjIso (rrR i)) y : ↥S) : Equiv.Perm (Fin 42)) =
      rr i * (y : Equiv.Perm (Fin 42)) * (rr i)⁻¹ := by
    have := conjAutS_apply (rrR i) y
    rw [coe_rrR] at this
    exact this
  constructor
  · intro h
    refine ⟨?_, y.2⟩
    have h2 := congrArg Subtype.val h
    rw [h1] at h2
    have h3 : rr i * (y : Equiv.Perm (Fin 42)) * (rr i)⁻¹ * rr i = (y : Equiv.Perm (Fin 42)) * rr i := by
      rw [h2]
    simpa [mul_assoc] using h3
  · rintro ⟨h, -⟩
    apply Subtype.ext
    rw [h1, h]
    simp [mul_assoc]

theorem card_fixSub_conjIso (i : Fin 4) :
    Nat.card (fixSub (Cls3.conjIso (rrR i))) = Nat.card (CC i) := by
  rw [fixSub_conjIso]
  have hle : CC i ≤ S := fun d hd => (mem_CC.mp hd).2
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem sylCfg_model :
    ∃ P E F : Subgroup ↥S, SylCfg (fun s => Cls3.conjIso r₃R s) P E F := by
  obtain ⟨P, E, F, hPS, hEP, hFP, hEF, hP, hE, hF, hexp, hr, hEsq, hEcen, hEcenter, hEr, hEcomm, hFcomm,
    hFsq, hfus⟩ := exists_sylCfg_model
  have hcard : ∀ {X : Subgroup (Equiv.Perm (Fin 42))}, X ≤ S → Nat.card (X.subgroupOf S) = Nat.card X :=
    fun {X} hX => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hmem : ∀ {X : Subgroup (Equiv.Perm (Fin 42))} {y : ↥S}, y ∈ X.subgroupOf S ↔ (y : Equiv.Perm (Fin 42)) ∈ X :=
    fun {X y} => Subgroup.mem_subgroupOf
  have hconj : ∀ s : ↥S, (((Cls3.conjIso r₃R) s : ↥S) : Equiv.Perm (Fin 42)) =
      r₃ * (s : Equiv.Perm (Fin 42)) * r₃⁻¹ := fun s => conjAutS_apply r₃R s
  refine ⟨P.subgroupOf S, E.subgroupOf S, F.subgroupOf S, ?_⟩
  exact
    { card_P := by rw [hcard hPS]; exact hP
      exp_P := fun x hx => Subtype.ext (by simpa using hexp x (hmem.mp hx))
      alpha_P := fun x hx => hmem.mpr (by rw [hconj]; exact hr x (hmem.mp hx))
      E_le := fun y hy => hmem.mpr (hEP (hmem.mp hy))
      F_le := fun y hy => hmem.mpr (hFP (hmem.mp hy))
      E_le_F := fun y hy => hmem.mpr (hEF (hmem.mp hy))
      card_E := by rw [hcard (hEP.trans hPS)]; exact hE
      card_F := by rw [hcard (hFP.trans hPS)]; exact hF
      E_sq := fun e he => Subtype.ext (by simpa using hEsq e (hmem.mp he))
      E_cen := fun e he x hx => Subtype.ext (by simpa using hEcen e (hmem.mp he) x (hmem.mp hx))
      E_center := fun x hx hc => hmem.mpr (hEcenter x (hmem.mp hx) (fun y hy =>
        congrArg Subtype.val (hc ⟨y, hPS hy⟩ (hmem.mpr hy))))
      E_alpha := fun e he => Subtype.ext (by
        rw [hconj]
        have := hEr e (hmem.mp he)
        rw [this]; simp [mul_assoc])
      E_comm := fun e he => by
        obtain ⟨a, ha, b, hb, hab⟩ := hEcomm e (hmem.mp he)
        exact ⟨⟨a, hPS ha⟩, hmem.mpr ha, ⟨b, hPS hb⟩, hmem.mpr hb, Subtype.ext (by simpa using hab)⟩
      F_comm := fun f hf g hg => Subtype.ext (by simpa using hFcomm f (hmem.mp hf) g (hmem.mp hg))
      F_sq := fun f hf => Subtype.ext (by simpa using hFsq f (hmem.mp hf))
      fusion := fun e he hne e' he' hne' => by
        have hne1 : (e : Equiv.Perm (Fin 42)) ≠ 1 := fun h1 => hne (Subtype.ext h1)
        have hne1' : (e' : Equiv.Perm (Fin 42)) ≠ 1 := fun h1 => hne' (Subtype.ext h1)
        obtain ⟨n, hnS, hnN, hnee⟩ := hfus e (hmem.mp he) hne1 e' (hmem.mp he') hne1'
        refine ⟨⟨n, hnS⟩, ?_, Subtype.ext (by simpa using hnee)⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have := Subgroup.mem_normalizer_iff.mp hnN (y : Equiv.Perm (Fin 42))
        rw [hmem, hmem]
        simpa using this }

theorem exists_sylCfg_of_graph {Y : Type} [Group Y] [Finite Y]
    (ψ : Y ≃* ↥S) (α : MulAut Y) (h2 : α * α = 1) (h60 : Nat.card (fixSub α) = 60) :
    ∃ P E F : Subgroup Y, SylCfg (fun y => α y) P E F := by
  set α' : MulAut ↥S := MulAut.congr ψ α with hα'
  have h2' : α' * α' = 1 := by rw [hα', ← map_mul, h2, map_one]
  have h60' : Nat.card (fixSub α') = 60 := by rw [hα', card_fixSub_congr]; exact h60
  have h1' : α' ≠ 1 := by
    intro h
    rw [h, fixSub_one, Subgroup.card_top, card_S] at h60'
    omega
  obtain ⟨i, β, hβ⟩ := exists_class_rep h2' h1'
  have hi : i = 2 := by
    have hc : Nat.card (CC i) = 60 := by
      rw [← card_fixSub_conjIso, ← hβ, card_fixSub_congr]
      exact h60'
    rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with rfl | rfl | rfl | rfl
    · rw [CC_zero, card_C₁] at hc; omega
    · rw [CC_one, card_C₂] at hc; omega
    · rfl
    · rw [CC_three, card_C₄] at hc; omega
  subst hi
  obtain ⟨P, E, F, hcfg⟩ := sylCfg_model
  have hrr : rrR 2 = r₃R := rfl
  rw [hrr] at hβ
  have hcfg' := hcfg.map β.symm.toMonoidHom β.symm.injective (α' := fun y => α' y)
    (fun y => by
      have h1 : Cls3.conjIso r₃R y = β (α' (β.symm y)) := by
        rw [← hβ]; rfl
      rw [h1]
      simp)
  have hcfg'' := hcfg'.map ψ.symm.toMonoidHom ψ.symm.injective (α' := fun y => α y)
    (fun s => by
      have h1 : α' s = ψ (α (ψ.symm s)) := rfl
      simp [h1])
  exact ⟨_, _, _, hcfg''⟩

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
