module

public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Chevalley.BorelStructure

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule


section Canon

variable (k : Type) [Field k]

@[expose] noncomputable def canonMin : WeylGroup Tag.E6 → ↥(e6Data_valid.minGroup k) :=
  (TauCeti.existsUnique_reducedWordLift (coxeterSystem Tag.E6) (e6Data_valid.nm k)
    (fun i j => e6Data_valid.nm_braidWord isFiniteType_cartan_E6 k i j)).exists.choose

variable {k}

theorem canonMin_wordProd {ω : List (Fin Tag.E6.rank)}
    (hω : (coxeterSystem Tag.E6).IsReduced ω) :
    canonMin k ((coxeterSystem Tag.E6).wordProd ω) = (ω.map (e6Data_valid.nm k)).prod :=
  (TauCeti.existsUnique_reducedWordLift (coxeterSystem Tag.E6) (e6Data_valid.nm k)
    (fun i j => e6Data_valid.nm_braidWord isFiniteType_cartan_E6 k i j)).exists.choose_spec ω hω

variable (k) in
theorem canonMin_one : canonMin k 1 = 1 := by
  have := canonMin_wordProd (k := k) (ω := []) (by simp [CoxeterSystem.IsReduced])
  rwa [CoxeterSystem.wordProd_nil, List.map_nil, List.prod_nil] at this

theorem canonMin_mul_of_length_eq {v v' : WeylGroup Tag.E6}
    (h : (coxeterSystem Tag.E6).length (v * v') =
      (coxeterSystem Tag.E6).length v + (coxeterSystem Tag.E6).length v') :
    canonMin k (v * v') = canonMin k v * canonMin k v' := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  obtain ⟨ω', hω', rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced v'
  have hred : (coxeterSystem Tag.E6).IsReduced (ω ++ ω') := by
    rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_append, h, hω.eq, hω'.eq,
      List.length_append]
  rw [← CoxeterSystem.wordProd_append, canonMin_wordProd hred, canonMin_wordProd hω,
    canonMin_wordProd hω', List.map_append, List.prod_append]

theorem canonMin_mul_of_length_eq' {v v' : WeylGroup TwistTag.E6.tag}
    (h : (coxeterSystem TwistTag.E6.tag).length (v * v') =
      (coxeterSystem TwistTag.E6.tag).length v + (coxeterSystem TwistTag.E6.tag).length v') :
    canonMin k (v * v') = canonMin k v * canonMin k v' :=
  canonMin_mul_of_length_eq h

end Canon

section Iso

variable {k : Type} [Field k] [Finite k]

theorem e6Isogeny_nt (a : Fin (Tag.rank .E6)) (s : kˣ) :
    ((Isogeny.e6Isogeny k (e6Data_valid.nt k a s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      weylElt .E6 k a s := by
  rw [weylElt_eq_xUnit_mul]
  change ((Isogeny.e6Isogeny k (e6Data_valid.xm k (Pi.single a 1) s *
    e6Data_valid.xm k (-Pi.single a 1) (-((s⁻¹ : kˣ) : k)) *
      e6Data_valid.xm k (Pi.single a 1) s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) = _
  rw [map_mul, map_mul, Isogeny.e6Isogeny_xm_single, Isogeny.e6Isogeny_xm_neg_single,
    Isogeny.eltElement_simpleRoot_E6, Isogeny.eltElement_neg_simpleRoot_E6]
  rfl

theorem e6Isogeny_canonMin (w : WeylGroup Tag.E6) :
    ((Isogeny.e6Isogeny k (canonMin k w) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonMin_wordProd hω, canonicalRep_wordProd hω, map_list_prod, Subgroup.val_list_prod,
    List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun a _ => e6Isogeny_nt a 1

end Iso

section Torus

variable {k : Type} [Field k] [Finite k]

theorem commute_of_mem_iSup_torus {x y : ↥(e6Data_valid.minGroup k)}
    (hx : x ∈ ⨆ i, e6Data_valid.torus k i) (hy : y ∈ ⨆ i, e6Data_valid.torus k i) :
    x * y = y * x := by
  obtain ⟨μ, hμ⟩ := e6Data_valid.exists_diagOp_of_mem_iSup_torus k hx
  obtain ⟨ν, hν⟩ := e6Data_valid.exists_diagOp_of_mem_iSup_torus k hy
  exact e6Data_valid.endo_injective k (by
    rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, hμ, hν, diagOp_comm])

theorem e6Isogeny_hm' (a : Fin (Tag.rank .E6)) (s : kˣ) :
    ((Isogeny.e6Isogeny k (e6Data_valid.hm k a s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      torusElt .E6 k a s := by
  change ((Isogeny.e6Isogeny k (e6Data_valid.nt k a s * (e6Data_valid.nt k a 1)⁻¹) :
    ↥(adjointGroup .E6 k)) : ModGL .E6 k) = _
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e6Isogeny_nt, e6Isogeny_nt,
    weylElt_inv]
  rfl

theorem exists_lift_torusGroup {g : ModGL .E6 k} (hg : g ∈ torusGroup .E6 k) :
    ∃ t ∈ ⨆ i, e6Data_valid.torus k i,
      ((Isogeny.e6Isogeny k t : ↥(adjointGroup .E6 k)) : ModGL .E6 k) = g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, s⟩, rfl⟩ := hx
    exact ⟨e6Data_valid.hm k a s, Subgroup.mem_iSup_of_mem a (e6Data_valid.hm_mem_torus k a s),
      e6Isogeny_hm' a s⟩
  | one => exact ⟨1, one_mem _, by rw [map_one]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, ht, e⟩ := hx
    obtain ⟨t', ht', e'⟩ := hy
    exact ⟨t * t', mul_mem ht ht', by rw [map_mul, Subgroup.coe_mul, e, e']⟩
  | inv x _ hx =>
    obtain ⟨t, ht, e⟩ := hx
    exact ⟨t⁻¹, inv_mem ht, by rw [map_inv, Subgroup.coe_inv, e]⟩

theorem mul_comm_of_isogeny_mem_torusGroup {a b : ↥(e6Data_valid.minGroup k)}
    (ha : ((Isogeny.e6IsogenyT k a : ↥(adjointGroup TwistTag.E6.tag k)) :
      ModGL TwistTag.E6.tag k) ∈ torusGroup TwistTag.E6.tag k)
    (hb : ((Isogeny.e6IsogenyT k b : ↥(adjointGroup TwistTag.E6.tag k)) :
      ModGL TwistTag.E6.tag k) ∈ torusGroup TwistTag.E6.tag k) : a * b = b * a := by
  have key : ∀ a : ↥(e6Data_valid.minGroup k), ((Isogeny.e6IsogenyT k a :
      ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k) ∈
        torusGroup TwistTag.E6.tag k →
      ∃ t ∈ ⨆ i, e6Data_valid.torus k i, ∃ z ∈ Subgroup.center ↥(e6Data_valid.minGroup k),
        a = t * z := by
    intro a hT
    obtain ⟨t, ht, e⟩ := exists_lift_torusGroup hT
    refine ⟨t, ht, t⁻¹ * a, ?_, by group⟩
    refine Isogeny.ker_e6IsogenyT_le_center k ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact inv_mul_eq_one.2 (Subtype.ext e)
  obtain ⟨t, ht, z, hz, hat⟩ := key a ha
  obtain ⟨t', ht', z', hz', hbt⟩ := key b hb
  rw [hat, hbt]
  have c1 := Subgroup.mem_center_iff.1 hz t'
  have c2 := Subgroup.mem_center_iff.1 hz' t
  have c3 := Subgroup.mem_center_iff.1 hz z'
  calc t * z * (t' * z') = t * (z * t') * z' := by group
    _ = t * (t' * z) * z' := by rw [← c1]
    _ = (t * t') * (z * z') := by group
    _ = (t' * t) * (z' * z) := by rw [commute_of_mem_iSup_torus ht ht', c3]
    _ = t' * (t * z') * z := by group
    _ = t' * (z' * t) * z := by rw [← c2]
    _ = t' * z' * (t * z) := by group

end Torus

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
