module

public import CFSG.GH74.GLS.C3.Layer2.L5C14
public import CFSG.GH74.GLS.C3.Layer2.L5C6
public import CFSG.GH74.GLS.C3.Layer2.L5C7
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5055

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Generic

@[expose] def conjAutOfNormalizer {P : Subgroup G} {b : G} (hb : b ∈ normalizer (P : Set G)) :
    ↥P ≃* ↥P where
  toFun p := ⟨b * p * b⁻¹, (mem_normalizer_iff.1 hb p).1 p.2⟩
  invFun p := ⟨b⁻¹ * p * b⁻¹⁻¹, (mem_normalizer_iff.1 (inv_mem hb) p).1 p.2⟩
  left_inv p := Subtype.ext (by simp [mul_assoc])
  right_inv p := Subtype.ext (by simp [mul_assoc])
  map_mul' p q := Subtype.ext (by simp [mul_assoc])

theorem mem_normalizer_of_conj_le {R : Subgroup G} {s : G} (hs : ∀ r ∈ R, s * r * s⁻¹ ∈ R) :
    s ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨hs g, fun hg => ?_⟩
  let f : ↥R → ↥R := fun r => ⟨s * r * s⁻¹, hs r r.2⟩
  have hinj : Function.Injective f := by
    intro r r' hrr
    have h2 : s * (r : G) * s⁻¹ = s * (r' : G) * s⁻¹ := congrArg Subtype.val hrr
    exact Subtype.ext (by simpa using h2)
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨s * g * s⁻¹, hg⟩
  have h2 : s * (r : G) * s⁻¹ = s * g * s⁻¹ := congrArg Subtype.val hr
  have : (r : G) = g := by simpa using h2
  rw [← this]
  exact r.2

theorem mem_of_sylow_normalizes {P N B : Subgroup G} (hP : IsSylow2In P N) (hB : IsPGroup 2 ↥B)
    (hPB : P ≤ B) {s : G} (hsB : s ∈ B) (hsN : s ∈ N) : s ∈ P := by
  have hle : P ⊔ zpowers s ≤ B := sup_le hPB (zpowers_le.2 hsB)
  have hle2 : P ⊔ zpowers s ≤ N := sup_le hP.1 (zpowers_le.2 hsN)
  have heq := sylow2_eq_of_le hP (hB.to_le hle) le_sup_left hle2
  have : s ∈ P ⊔ zpowers s := Subgroup.mem_sup_right (mem_zpowers s)
  rw [heq] at this
  exact this

end Generic

namespace Glue

theorem S0subP1_le_Sh1 : S0subP1 ≤ Sh1 := fun p hp => by
  have h := S0subP1_le_Sh1_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem R1subP_le_Sh0 : R1subP ≤ Sh0 := fun p hp => by
  have h := R1subP_le_Sh0_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem tr1_inj_chk :
    (List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    imp (decide (tr1 i = tr1 j)) (decide (i = j))) = true :=
  Certificates.certificate5055.2.1

theorem tr1_injective : Function.Injective tr1 := fun i j hij => by
  have h := tr1_inj_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq, List.mem_finRange, true_implies]
    at h
  exact h i j hij

theorem R1L_comm_chk :
    R1L.all (fun a => R1L.all fun b => decide (a * b = b * a)) = true :=
  Certificates.certificate5055.2.2.1

theorem R1L_ne_one_chk :
    R1L.any (fun r => decide (r ≠ 1)) = true :=
  Certificates.certificate5055.2.2.2.1

theorem R1L_sq_chk :
    R1L.all (fun r => decide (r * r = 1)) = true :=
  Certificates.certificate5055.2.2.2.2

theorem emb48_el16
    (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16)) (i : Fin 16) :
    emb48 Tr yy (el16 i) = Tr i := by
  have h1 : el16 i ∈ Rml := mem_Rm.1 (el16_mem i)
  simp [emb48, h1, idx16_el16]

theorem rhoF_eq {Tr : Fin 16 → Perm (Fin 16)} (hTr : Function.Injective Tr)
    {s : Perm (Fin 16)} {i j : Fin 16} (h : s * Tr i * s⁻¹ = Tr j) : rhoF Tr s i = j := by
  unfold rhoF
  have hex : ((List.finRange 16).find? (fun j' => decide (s * Tr i * s⁻¹ = Tr j'))).isSome := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_finRange j, by simp [h]⟩
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.1 hex
  have hp := List.find?_some hj'
  have h2 : s * Tr i * s⁻¹ = Tr j' := by simpa using hp
  have h3 : j' = j := hTr (h2.symm.trans h)
  rw [hj']
  simp [h3]

end Glue

section Model

variable {h : IsAConfig 5 x K T Q S a}

@[expose] noncomputable def Coord5.rhoS1
    (c : Coord5 h) {S₁ : Subgroup G} (hN : S₁ ≤ c.N) :
    ↥S₁ →* Perm (Fin 16) :=
  c.rhoG.comp (Subgroup.inclusion hN)

@[expose] noncomputable def Coord5.iotaS1 (c : Coord5 h) {S₁ : Subgroup G} (hT : T ≤ S₁) :
    ↥T5 →* ↥S₁ where
  toFun t := ⟨c.iotaT t, hT (c.iotaT_mem_T t)⟩
  map_one' := Subtype.ext (map_one c.iotaT)
  map_mul' s t := Subtype.ext (map_mul c.iotaT s t)

theorem Coord5.iotaS1_injective (c : Coord5 h) {S₁ : Subgroup G} (hT : T ≤ S₁) :
    Function.Injective (c.iotaS1 hT) := fun s t hst => by
  have h2 := congrArg Subtype.val hst
  exact c.iotaT_injective h2

structure Coord5.ModelIso
    (c : Coord5 h) {S₁ : Subgroup G} (hS : c.S1Data S₁)
    (M : Subgroup (Perm (Fin 16))) (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16)) where
  ψ : ↥S₁ ≃* ↥M
  spec : ∀ t, ((ψ (c.iotaS1 hS.hT t) : ↥M) : Perm (Fin 16)) = emb48 Tr yy t

variable
  {c : Coord5 h} {S₁ : Subgroup G} {hS : c.S1Data S₁}
  {M : Subgroup (Perm (Fin 16))} {Tr : Fin 16 → Perm (Fin 16)} {yy : Perm (Fin 16)}

theorem Coord5.ModelIso.liftEl
    (Ψ : c.ModelIso hS M Tr yy) (i : Fin 16) :
    ((Ψ.ψ ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ : ↥M) : Perm (Fin 16)) = Tr i := by
  have h1 := Ψ.spec (elT i)
  have h2 : c.iotaS1 hS.hT (elT i) = ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ :=
    Subtype.ext (c.iotaT_elT i)
  rw [h2] at h1
  rw [h1]
  exact Glue.emb48_el16 Tr yy i

theorem Coord5.ModelIso.conj
    (Ψ : c.ModelIso hS M Tr yy) {s : G} (hs : s ∈ S₁) (i : Fin 16) :
    ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) * Tr i * ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16))⁻¹ =
      Tr (c.rhoG ⟨s, hS.hN hs⟩ i) := by
  have e1 : (⟨s, hs⟩ : ↥S₁) * ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ *
      (⟨s, hs⟩ : ↥S₁)⁻¹ =
      ⟨c.liftEl (c.rhoG ⟨s, hS.hN hs⟩ i), Coord5.R_le_S1 hS (c.liftEl_mem _)⟩ :=
    Subtype.ext (by simp [Coord5.rhoG_spec])
  have h2 := congrArg (fun y : ↥S₁ => ((Ψ.ψ y : ↥M) : Perm (Fin 16))) e1
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [Ψ.liftEl, Ψ.liftEl] at h2
  exact h2

theorem Coord5.ModelIso.mem_R
    (Ψ : c.ModelIso hS M Tr yy) {s : G} (hs : s ∈ S₁) :
    s ∈ c.lift Rm ↔ ∃ i, ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) = Tr i := by
  constructor
  · intro hR
    refine ⟨idx16 (c.rco s), ?_⟩
    have h3 : (⟨s, hs⟩ : ↥S₁) = ⟨c.liftEl (idx16 (c.rco s)),
        Coord5.R_le_S1 hS (c.liftEl_mem _)⟩ := Subtype.ext (Coord5.exists_liftEl c hR)
    rw [h3]
    exact Ψ.liftEl _
  · rintro ⟨i, hi⟩
    have h4 : Ψ.ψ ⟨s, hs⟩ = Ψ.ψ ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ :=
      Subtype.ext (by rw [hi, Ψ.liftEl])
    have h5 : s = c.liftEl i := congrArg Subtype.val (Ψ.ψ.injective h4)
    rw [h5]
    exact c.liftEl_mem i

theorem Coord5.ModelIso.rhoF_eq
    (Ψ : c.ModelIso hS M Tr yy) (hTr : Function.Injective Tr)
    {s : G} (hs : s ∈ S₁) (i : Fin 16) :
    rhoF Tr ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) i = c.rhoG ⟨s, hS.hN hs⟩ i :=
  Glue.rhoF_eq hTr (Ψ.conj hs i)

end Model

end CFSG.GH74.GLS.C3.Layer2.L5
