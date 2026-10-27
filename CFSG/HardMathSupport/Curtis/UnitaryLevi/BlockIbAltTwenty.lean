module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbAltVoid
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PermThreeCentralizer

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}

theorem exists_mul_of_mem_sup_of_commute {X : Type*} [Group X] {P C : Subgroup X}
    (hcomm : ∀ p ∈ P, ∀ c ∈ C, p * c = c * p) {y : X} (hy : y ∈ P ⊔ C) :
    ∃ p ∈ P, ∃ c ∈ C, p * c = y := by
  let Q : Subgroup X :=
    { carrier := {y | ∃ p ∈ P, ∃ c ∈ C, p * c = y}
      one_mem' := ⟨1, P.one_mem, 1, C.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, c, hc, rfl⟩ ⟨p', hp', c', hc', rfl⟩
        refine ⟨p * p', P.mul_mem hp hp', c * c', C.mul_mem hc hc', ?_⟩
        calc p * p' * (c * c') = p * (p' * c) * c' := by group
          _ = p * (c * p') * c' := by rw [hcomm p' hp' c hc]
          _ = p * c * (p' * c') := by group
      inv_mem' := by
        rintro _ ⟨p, hp, c, hc, rfl⟩
        refine ⟨p⁻¹, P.inv_mem hp, c⁻¹, C.inv_mem hc, ?_⟩
        have h := hcomm p hp c hc
        calc p⁻¹ * c⁻¹ = (c * p)⁻¹ := by group
          _ = (p * c)⁻¹ := by rw [h] }
  have : P ⊔ C ≤ Q :=
    sup_le (fun p hp => ⟨p, hp, 1, C.one_mem, mul_one p⟩) (fun c hc => ⟨1, P.one_mem, c, hc, one_mul c⟩)
  exact this hy

theorem eq_one_of_central_alt (n : ℕ) (hn : 4 ≤ n) (z : alternatingGroup (Fin n))
    (hz : ∀ g, g * z = z * g) : z = 1 := by
  have h := alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn)
  have : z ∈ Subgroup.center (alternatingGroup (Fin n)) := Subgroup.mem_center_iff.mpr hz
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem le_alternatingGroup_of_perfect {n : ℕ} {W : Subgroup (Equiv.Perm (Fin n))}
    (hW : ⁅W, W⁆ = W) : W ≤ alternatingGroup (Fin n) := by
  rw [← hW]
  exact (Subgroup.commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le

theorem false_of_blockThreeIbHyp_of_mulEquiv_alt20 (h : BlockThreeIbHyp M S L D x)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin 20)) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hDle, -, -, hxD, hx3, hxC, free⟩ := id h
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  obtain ⟨p, hp, c, hc, hpc⟩ := exists_mul_of_mem_sup_of_commute (fun p hp c hc =>
    Subgroup.mem_centralizer_iff.mp hc p (hPL hp)) (hDle hxD)
  have hpL : p ∈ barM M L := hPL hp
  have hcL : ∀ l ∈ barM M L, l * c = c * l := fun l hl => Subgroup.mem_centralizer_iff.mp hc l hl
  have hcomm : Commute p c := hcL p hpL
  have hp3 : p ^ 3 = 1 := by
    have h1 : p ^ 3 * c ^ 3 = 1 := by rw [← hcomm.mul_pow, hpc]; exact hx3
    have hc3 : c ^ 3 ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.pow_mem _ hc 3
    have hcen : ∀ l ∈ barM M L, l * p ^ 3 = p ^ 3 * l := by
      intro l hl
      have : p ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      have := Subgroup.mem_centralizer_iff.mp hc3 l hl
      calc l * (c ^ 3)⁻¹ = (c ^ 3)⁻¹ * (c ^ 3 * l) * (c ^ 3)⁻¹ := by group
        _ = (c ^ 3)⁻¹ * (l * c ^ 3) * (c ^ 3)⁻¹ := by rw [this]
        _ = (c ^ 3)⁻¹ * l := by group
    have hz : e ⟨p ^ 3, Subgroup.pow_mem _ hpL 3⟩ = 1 := by
      apply eq_one_of_central_alt 20 (by norm_num)
      intro g
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hcen g g.2))
    have := e.injective (hz.trans (map_one e).symm)
    exact congrArg Subtype.val this
  set p' : ↥(barM M L) := ⟨p, hpL⟩ with hp'
  have hp1 : p' ≠ 1 := by
    intro h1
    have : p = 1 := congrArg Subtype.val h1
    apply hxC
    rw [← hpc, this, one_mul]
    exact hc
  set π : Equiv.Perm (Fin 20) := (e p' : Equiv.Perm (Fin 20)) with hπ
  have hπ3 : π ^ 3 = 1 := by
    have : e p' ^ 3 = 1 := by
      rw [← map_pow, ← map_one e]
      exact congrArg e (Subtype.ext hp3)
    exact congrArg Subtype.val this
  have hπ1 : π ≠ 1 := by
    intro h1
    apply hp1
    apply e.injective
    exact Subtype.ext (by simpa [hπ] using h1)
  obtain ⟨W, hWp, hW0, hWc⟩ := exists_perfect_le_centralizer_of_pow_three π hπ3 hπ1
  have hWA := le_alternatingGroup_of_perfect hWp
  set W₁ : Subgroup (alternatingGroup (Fin 20)) := W.subgroupOf (alternatingGroup (Fin 20)) with hW₁
  have hW₁p : ⁅W₁, W₁⁆ = W₁ := by
    apply Subgroup.map_injective (alternatingGroup (Fin 20)).subtype_injective
    rw [Subgroup.map_commutator, hW₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWA, hWp]
  have hW₁0 : W₁ ≠ ⊥ := by
    intro hb
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have : (⟨w, hWA hw⟩ : alternatingGroup (Fin 20)) ∈ W₁ := hw
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  set W₂ : Subgroup ↥(barM M L) := W₁.map e.symm.toMonoidHom with hW₂
  set W₃ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := W₂.map (barM M L).subtype with hW₃
  have hW₂p : ⁅W₂, W₂⁆ = W₂ := by rw [hW₂, ← Subgroup.map_commutator, hW₁p]
  have hW₃p : ⁅W₃, W₃⁆ = W₃ := by rw [hW₃, ← Subgroup.map_commutator, hW₂p]
  have hW₃L : W₃ ≤ barM M L := Subgroup.map_subtype_le _
  have hW₃x : W₃ ≤ Subgroup.centralizer ({x} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨_, ⟨w₁, hw₁, rfl⟩, rfl⟩
    set wL : ↥(barM M L) := e.symm w₁ with hwL
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpw : p * (wL : _) = (wL : _) * p := by
      have hcm : Commute (w₁ : Equiv.Perm (Fin 20)) π := hWc _ hw₁
      have : e (p' * wL) = e (wL * p') := by
        rw [map_mul, map_mul, hwL, MulEquiv.apply_symm_apply]
        exact Subtype.ext hcm.symm.eq
      exact congrArg Subtype.val (e.injective this)
    show (wL : _) * x = x * (wL : _)
    rw [← hpc]
    calc (wL : _) * (p * c) = ((wL : _) * p) * c := by group
      _ = (p * (wL : _)) * c := by rw [← hpw]
      _ = p * ((wL : _) * c) := by group
      _ = p * (c * (wL : _)) := by rw [hcL wL wL.2]
      _ = p * c * (wL : _) := by group
  have hW₃0 : W₃ ≠ ⊥ := by
    intro hb
    apply hW₁0
    have h2 : W₂ = ⊥ := by
      rw [hW₃, Subgroup.map_eq_bot_iff_of_injective _ (barM M L).subtype_injective] at hb
      exact hb
    rw [hW₂, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h2
    exact h2
  exact hW₃0 (free W₃ hW₃L hW₃p hW₃x)

theorem false_of_nineThreeSeven (h : BlockThreeIbHyp M S L D x) (h7 : NineThreeSeven M S L) :
    False :=
  (nineThreeSeven_five h h7).1.elim fun e => false_of_blockThreeIbHyp_of_mulEquiv_alt20 h e

end CFSG.HardMathSupport.Curtis.UnitaryLevi
