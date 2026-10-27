module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4Rot
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley.RootWalk CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT
open scoped commutatorElement MatrixGroups

section Roots

abbrev g2Long : Fin Tag.G2.rank := ⟨0, by decide⟩

abbrev g2Short : Fin Tag.G2.rank := ⟨1, by decide⟩

@[expose] def g2Hex : Fin 6 → Fin Tag.G2.rank → ℤ :=
  ![![1, 0], ![2, 3], ![1, 3], ![-1, 0], ![-2, -3], ![-1, -3]]

theorem isRoot_G2_iff_lt {v : Fin Tag.G2.rank → ℤ} :
    IsRoot .G2 v ↔ ∃ k < 12, Tag.G2.rootCertificate.root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2),
    show Tag.G2.rootCertificate.roots.length = 12 by decide]

theorem isRoot_g2Hex (k : Fin 6) : IsRoot .G2 (g2Hex k) := by
  rw [isRoot_G2_iff_lt]
  revert k
  decide +kernel

theorem g2Hex_rot (k : Fin 6) :
    reflect .G2 g2Long (reflect .G2 g2Short (g2Hex k)) = g2Hex (k + 1) := by
  revert k
  decide +kernel

theorem g2Hex_neg_zero : -g2Hex 0 = g2Hex 3 := by decide +kernel

theorem g2Hex_neg_two : -g2Hex 2 = g2Hex 5 := by decide +kernel

theorem g2Hex_zero : g2Hex 0 = Pi.single g2Long 1 := by decide +kernel

theorem g2Hex_two : g2Hex 2 = reflect .G2 g2Short (Pi.single g2Long 1) := by decide +kernel

theorem g2Hex_reflect_zero : reflect .G2 g2Short (g2Hex 0) = g2Hex 2 := by decide +kernel

end Roots

section Commutators

theorem g2_comm_two : ∃ N : ℤ, (N = 1 ∨ N = -1) ∧ ∀ (R : Type) [CommRing R] (c d : R),
    pinnedX .G2 R (g2Hex 0) c * pinnedX .G2 R (g2Hex 2) d * pinnedX .G2 R (g2Hex 0) (-c) *
      pinnedX .G2 R (g2Hex 2) (-d) = pinnedX .G2 R (g2Hex 1) ((N : R) * c * d) := by
  have hr : ((0 : ℕ), (3 : ℕ), [((1 : ℕ), (1 : ℕ), (7 : ℕ), (1 : ℤ))]) ∈ repsOf .G2 := by
    decide +kernel
  have h0 : Tag.G2.rootCertificate.root 0 = g2Hex 0 := by decide +kernel
  have h3 : Tag.G2.rootCertificate.root 3 = g2Hex 2 := by decide +kernel
  obtain ⟨-, -, hkeys, -, -⟩ := repShape_spec (τ := .G2) hr
  have hcp : commPairs .G2 (g2Hex 0) (g2Hex 2) = [(1, 1)] := by
    rw [← h0, ← h3]
    exact hkeys.symm
  have hsum : (1 : ℕ) • g2Hex 0 + (1 : ℕ) • g2Hex 2 = g2Hex 1 := by decide +kernel
  refine ⟨(rootOperatorFamily .G2).pinnedFamilySign (g2Hex 1) *
      (rootOperatorFamily .G2).pinnedFamilySign (g2Hex 0) *
      (rootOperatorFamily .G2).pinnedFamilySign (g2Hex 2) * 1, ?_, fun R _ c d => ?_⟩
  · rcases (rootOperatorFamily .G2).pinnedFamilySign_eq (g2Hex 1) with h1 | h1 <;>
      rcases (rootOperatorFamily .G2).pinnedFamilySign_eq (g2Hex 0) with h2 | h2 <;>
        rcases (rootOperatorFamily .G2).pinnedFamilySign_eq (g2Hex 2) with h3 | h3 <;>
          simp [h1, h2, h3]
  · have h := pinnedX_commFormula_of_commFormula (τ := .G2)
      (isRoot_rootCertificate_root (lt_length_of_mem_repsOf hr).1)
      (isRoot_rootCertificate_root (lt_length_of_mem_repsOf hr).2) (commFormula_rep hr) R c d
    dsimp only at h
    rw [h0, h3, hcp] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
      hsum] at h
    rw [h]
    congr 1

theorem g2_comm_one (R : Type) [CommRing R] (c d : R) :
    pinnedX .G2 R (g2Hex 0) c * pinnedX .G2 R (g2Hex 1) d * pinnedX .G2 R (g2Hex 0) (-c) *
      pinnedX .G2 R (g2Hex 1) (-d) = 1 := by
  have hr : ((0 : ℕ), (7 : ℕ), ([] : List Factor)) ∈ repsOf .G2 := by decide +kernel
  have h0 : Tag.G2.rootCertificate.root 0 = g2Hex 0 := by decide +kernel
  have h7 : Tag.G2.rootCertificate.root 7 = g2Hex 1 := by decide +kernel
  obtain ⟨-, -, hkeys, -, -⟩ := repShape_spec (τ := .G2) hr
  have hcp : commPairs .G2 (g2Hex 0) (g2Hex 1) = [] := by
    rw [← h0, ← h7]
    exact hkeys.symm
  have h := pinnedX_commFormula_of_commFormula (τ := .G2)
    (isRoot_rootCertificate_root (lt_length_of_mem_repsOf hr).1)
    (isRoot_rootCertificate_root (lt_length_of_mem_repsOf hr).2) (commFormula_rep hr) R c d
  dsimp only at h
  rw [h0, h7, hcp] at h
  simpa using h

end Commutators

section Elements

variable (F : Type) [Field F]

@[expose] noncomputable def g2HexX (k : Fin 6) (c : F) : ↥(adjointGroup .G2 F) :=
  ⟨pinnedX .G2 F (g2Hex k) c, pinnedX_mem_adjointGroup _ c⟩

@[expose] noncomputable def g2Rot : ↥(adjointGroup .G2 F) :=
  weylElement .G2 F g2Long * weylElement .G2 F g2Short

@[expose] def g2κ (k : Fin 6) : F :=
  ((allRootWeylSign .G2 g2Long (reflect .G2 g2Short (g2Hex k)) : ℤ) : F) *
    ((allRootWeylSign .G2 g2Short (g2Hex k) : ℤ) : F)

variable {F}

theorem g2HexX_add (k : Fin 6) (s t : F) : g2HexX F k (s + t) = g2HexX F k s * g2HexX F k t :=
  Subtype.ext (pinnedX_add .G2 F (g2Hex k) s t)

theorem g2HexX_injective (k : Fin 6) : Function.Injective (g2HexX F k) := fun _ _ h =>
  pinnedX_injective .G2 F (g2Hex k) (congrArg Subtype.val h)

theorem g2HexX_zero (k : Fin 6) : g2HexX F k 0 = 1 := Subtype.ext (pinnedX_zero .G2 F (g2Hex k))

theorem g2κ_sq (k : Fin 6) : g2κ F k * g2κ F k = 1 := by
  have h := (all_root_weyl_infinitesimal.{0} .G2).2.2.2.1
  have h1 := h g2Long (reflect .G2 g2Short (g2Hex k)) (IsRoot.reflect g2Short (isRoot_g2Hex k))
  have h2 := h g2Short (g2Hex k) (isRoot_g2Hex k)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [g2κ, h1, h2]

theorem g2HexX_rot (k : Fin 6) (u : F) :
    g2Rot F * g2HexX F k u * (g2Rot F)⁻¹ = g2HexX F (k + 1) (g2κ F k * u) := by
  apply Subtype.ext
  have h1 := weylElt_one_mul_pinnedX_mul_inv F g2Short (isRoot_g2Hex k) u
  have h2 := weylElt_one_mul_pinnedX_mul_inv F g2Long (IsRoot.reflect g2Short (isRoot_g2Hex k))
    (((allRootWeylSign .G2 g2Short (g2Hex k) : ℤ) : F) * u)
  change (weylElt .G2 F g2Long 1 * weylElt .G2 F g2Short 1) * pinnedX .G2 F (g2Hex k) u *
      (weylElt .G2 F g2Long 1 * weylElt .G2 F g2Short 1)⁻¹ =
        pinnedX .G2 F (g2Hex (k + 1)) (g2κ F k * u)
  have e : ∀ a b x : ModGL .G2 F, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  rw [e, h1, h2, g2Hex_rot k]
  congr 1
  simp only [g2κ]
  ring

theorem g2HexX_commutator_coe (j k : Fin 6) (s t : F) :
    ((⁅g2HexX F j s, g2HexX F k t⁆ : ↥(adjointGroup .G2 F)) : ModGL .G2 F) =
      pinnedX .G2 F (g2Hex j) s * pinnedX .G2 F (g2Hex k) t * pinnedX .G2 F (g2Hex j) (-s) *
        pinnedX .G2 F (g2Hex k) (-t) := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, g2HexX, pinnedX_neg]

theorem g2HexX_comm_one (s t : F) : ⁅g2HexX F 0 s, g2HexX F 1 t⁆ = 1 :=
  Subtype.ext (by rw [g2HexX_commutator_coe]; exact g2_comm_one F s t)

theorem g2HexX_comm_two {N : ℤ}
    (hform : ∀ (R : Type) [CommRing R] (c d : R),
      pinnedX .G2 R (g2Hex 0) c * pinnedX .G2 R (g2Hex 2) d * pinnedX .G2 R (g2Hex 0) (-c) *
        pinnedX .G2 R (g2Hex 2) (-d) = pinnedX .G2 R (g2Hex 1) ((N : R) * c * d)) (s t : F) :
    ⁅g2HexX F 0 s, g2HexX F 2 t⁆ = g2HexX F 1 ((N : F) * s * t) :=
  Subtype.ext (by rw [g2HexX_commutator_coe]; exact hform F s t)

theorem g2_exists_sl3 [Finite F] :
    ∃ (ρ : SL(3, F) →* ↥(adjointGroup .G2 F)) (l : Fin 6 → F), (∀ k, l k * l k = 1) ∧ ∀ c,
      ρ (tv 0 1 c) = g2HexX F 0 (l 0 * c) ∧ ρ (tv 1 2 c) = g2HexX F 2 (l 2 * c) ∧
      ρ (tv 0 2 c) = g2HexX F 1 (l 1 * c) ∧ ρ (tv 1 0 c) = g2HexX F 3 (l 3 * c) ∧
      ρ (tv 2 1 c) = g2HexX F 5 (l 5 * c) ∧ ρ (tv 2 0 c) = g2HexX F 4 (l 4 * c) := by
  obtain ⟨N, hN, hform⟩ := g2_comm_two
  have hNN : (N : F) * N = 1 := by rcases hN with rfl | rfl <;> simp
  exact exists_sl3_of_rotation (x := g2HexX F) (g := g2Rot F) (κ := g2κ F)
    (fun k s t => g2HexX_add k s t) (g2HexX_injective 1) g2κ_sq g2HexX_rot hNN g2HexX_comm_one
    (g2HexX_comm_two hform)

theorem mem_rootGroup_g2_iff {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ)
    {x : ↥(adjointGroup .G2 F)} :
    x ∈ rootGroup (rootOperatorFamily .G2) F γ ↔
      ∃ c : F, x = ⟨pinnedX .G2 F γ c, pinnedX_mem_adjointGroup γ c⟩ := by
  rw [rootGroup_of_isRoot hγ, ← (rootOperatorFamily .G2).subgroupOf_rootSubgroup_eq F ⟨γ, hγ⟩,
    Subgroup.mem_subgroupOf, mem_rootSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]⟩⟩

theorem g2Datum_rootGroup_hex_eq_range (k : Fin 6) {u : F} (hu : u * u = 1) :
    ((g2Datum F).rootGroup (g2Hex k) : Set ↥(adjointGroup .G2 F)) =
      Set.range fun c => g2HexX F k (u * c) := by
  have hu0 : u ≠ 0 := fun h => by
    rw [h, mul_zero] at hu
    exact zero_ne_one hu
  ext x
  rw [SetLike.mem_coe]
  change x ∈ rootGroup (rootOperatorFamily .G2) F (g2Hex k) ↔ _
  rw [mem_rootGroup_g2_iff (isRoot_g2Hex k)]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨u⁻¹ * c, by simp [g2HexX, mul_inv_cancel_left₀ hu0]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨u * c, rfl⟩

theorem g2_standardPair_base [Finite F] :
    ∃ W, LinearBlockStandardPair F W
      ((g2Datum F).rootGroup (g2Hex 0) ⊔ (g2Datum F).rootGroup (-g2Hex 0))
      ((g2Datum F).rootGroup (g2Hex 2) ⊔ (g2Datum F).rootGroup (-g2Hex 2)) := by
  obtain ⟨ρ, l, hl, hρ⟩ := g2_exists_sl3 (F := F)
  have hl0 : l 0 ≠ 0 := fun h => by
    have := hl 0
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hnt : ∃ g, ρ g ≠ 1 := ⟨tv 0 1 1, fun h => by
    rw [(hρ 1).1] at h
    have h2 := g2HexX_injective 0 (h.trans (g2HexX_zero 0).symm)
    exact hl0 (by simpa using h2)⟩
  have hker : ρ.ker ≤ Subgroup.center SL(3, F) :=
    ker_le_center_of_isQuasisimple (SpecialLinear.isQuasisimple 2 F le_rfl) hnt
  rw [g2Hex_neg_zero, g2Hex_neg_two]
  exact ⟨_, ModelFacts.linearBlockStandardPair_sup (K := ↥(adjointGroup .G2 F))
    (g2Datum_rootGroup_hex_eq_range 0 (hl 0)) (g2Datum_rootGroup_hex_eq_range 3 (hl 3))
    (g2Datum_rootGroup_hex_eq_range 2 (hl 2)) (g2Datum_rootGroup_hex_eq_range 5 (hl 5))
    ρ hker fun c => ⟨(hρ c).1, (hρ c).2.2.2.1, (hρ c).2.1, (hρ c).2.2.2.2.1⟩⟩

end Elements

end CFSG.ClassicalInvolution.Balance
