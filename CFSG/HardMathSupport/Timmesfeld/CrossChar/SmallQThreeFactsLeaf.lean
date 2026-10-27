module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public import CFSG.HardMathSupport.Timmesfeld.Balance.Faithful

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k]

@[expose] noncomputable def dV (ω : kˣ) (x : Fin τ.rank → ZMod 3) : ModGL τ k :=
  rootDiagUnit τ (torV ω x)

theorem pow_val_add {ω : kˣ} (hω : ω ^ 3 = 1) (a b : ZMod 3) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  have key : ∀ m : ℕ, ω ^ m = ω ^ (m % 3) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 3]
    rw [pow_add, pow_mul, hω, one_pow, mul_one]
  rw [← pow_add, ZMod.val_add, ← key]

theorem torV_add {ω : kˣ} (hω : ω ^ 3 = 1) (x y : Fin τ.rank → ZMod 3) :
    torV ω (x + y) = torV ω x * torV ω y := by
  funext i
  simp only [torV, Pi.add_apply, Pi.mul_apply, pow_val_add hω]

theorem torV_zero (ω : kˣ) : torV ω (0 : Fin τ.rank → ZMod 3) = 1 := by
  funext i
  simp [torV]

theorem dV_add {ω : kˣ} (hω : ω ^ 3 = 1) (x y : Fin τ.rank → ZMod 3) :
    dV ω (x + y) = dV ω x * dV ω y := by
  rw [dV, dV, dV, torV_add hω]
  exact Units.ext (rootDiag_mul_rootDiag _ _).symm

theorem dV_zero (ω : kˣ) : dV ω (0 : Fin τ.rank → ZMod 3) = 1 := by
  rw [dV, torV_zero]
  exact Units.ext rootDiag_one

theorem dV_injective {ω : kˣ} (hω : orderOf ω = 3) :
    Function.Injective (dV (τ := τ) ω) := by
  intro x y h
  have h1 := rootDiagUnit_injective (τ := τ) (K := k) h
  funext i
  have h2 := congrFun h1 i
  simp only [torV] at h2
  rw [pow_eq_pow_iff_modEq, hω] at h2
  have hx := ZMod.val_lt (x i)
  have hy := ZMod.val_lt (y i)
  have : (x i).val = (y i).val := by
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact ZMod.val_injective _ this

@[expose] noncomputable def dVHom {ω : kˣ} (hω : ω ^ 3 = 1) :
    Multiplicative (Fin τ.rank → ZMod 3) →* ModGL τ k where
  toFun x := dV ω x.toAdd
  map_one' := dV_zero ω
  map_mul' x y := dV_add hω x.toAdd y.toAdd

theorem dVHom_ofAdd {ω : kˣ} (hω : ω ^ 3 = 1) (x : Fin τ.rank → ZMod 3) :
    dVHom (τ := τ) hω (Multiplicative.ofAdd x) = dV ω x := rfl

section Reflection

theorem canonicalRep_conj_simple_mem_sup {S : Set (Fin τ.rank → ℤ)} {w : WeylGroup τ}
    {i : Fin τ.rank} (hS : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S)
    (hS' : -(w • (Pi.single i 1 : Fin τ.rank → ℤ)) ∈ S) :
    canonicalRep (coxeterSystem τ) k (w * simple τ i * w⁻¹) ∈ torusGroup τ k ⊔ rootSpan τ k S := by
  set n := canonicalRep (coxeterSystem τ) k w
  set α : Fin τ.rank → ℤ := w • (Pi.single i 1 : Fin τ.rank → ℤ)
  have hmapx := (canonical_weyl_root_transport τ k).2.1 w _ (isRoot_single τ i)
  have hmapy := (canonical_weyl_root_transport τ k).2.1 w _ (IsRoot.neg (isRoot_single τ i))
  rw [smul_neg] at hmapy
  have hU : ∀ β ∈ S, rootSubgroup τ k β ≤ torusGroup τ k ⊔ rootSpan τ k S := fun β hβ =>
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => rootSubgroup τ k γ) β hβ le_rfl).trans le_sup_right
  have hx : ∀ c : k, n * xUnit τ k i c * n⁻¹ ∈ torusGroup τ k ⊔ rootSpan τ k S := fun c => by
    refine hU α hS ?_
    rw [← hmapx]
    exact ⟨_, xUnit_mem_rootSubgroup i c, rfl⟩
  have hy : ∀ c : k, n * yUnit τ k i c * n⁻¹ ∈ torusGroup τ k ⊔ rootSpan τ k S := fun c => by
    refine hU (-α) hS' ?_
    rw [← hmapy]
    exact ⟨_, yUnit_mem_rootSubgroup i c, rfl⟩
  have hm : n * weylElt τ k i 1 * n⁻¹ ∈ torusGroup τ k ⊔ rootSpan τ k S := by
    rw [weylElt_eq_xUnit_mul]
    have e : n * (xUnit τ k i ((1 : kˣ) : k) * yUnit τ k i (-(((1 : kˣ)⁻¹ : kˣ) : k)) *
        xUnit τ k i ((1 : kˣ) : k)) * n⁻¹ = (n * xUnit τ k i ((1 : kˣ) : k) * n⁻¹) *
          (n * yUnit τ k i (-(((1 : kˣ)⁻¹ : kˣ) : k)) * n⁻¹) *
            (n * xUnit τ k i ((1 : kˣ) : k) * n⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have hN : (canonicalRep (coxeterSystem τ) k (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ k i 1 * n⁻¹) ∈ monomialSubgroup τ k :=
    mul_mem (inv_mem (canonicalRep_mem_monomialSubgroup k _))
      (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup k w) (weylElt_mem_monomialSubgroup i))
        (inv_mem (canonicalRep_mem_monomialSubgroup k w)))
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem τ) k (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ k i 1 * n⁻¹)) 1 := by
    have := (mapsRootLines_canonicalRep (R := k) (w * simple τ i * w⁻¹)).inv.mul
      (((mapsRootLines_canonicalRep (R := k) w).mul (mapsRootLines_weylElt i)).mul
        (mapsRootLines_canonicalRep (R := k) w).inv)
    rwa [inv_mul_cancel] at this
  have hT := mem_torusGroup_of_mapsRootLines_one hN hmaps
  have e : canonicalRep (coxeterSystem τ) k (w * simple τ i * w⁻¹) =
      (n * weylElt τ k i 1 * n⁻¹) *
        ((canonicalRep (coxeterSystem τ) k (w * simple τ i * w⁻¹))⁻¹ *
          (n * weylElt τ k i 1 * n⁻¹))⁻¹ := by group
  rw [e]
  exact mul_mem hm (inv_mem (le_sup_left (a := torusGroup τ k) hT))

theorem canonicalRep_rootReflection_mem {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    canonicalRep (coxeterSystem τ) k (rootReflection α) ∈
      torusGroup τ k ⊔ rootSpan τ k {α, -α} := by
  obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [rootReflection_eq_conj hwi]
  refine canonicalRep_conj_simple_mem_sup ?_ ?_
  · rw [hwi]
    exact Set.mem_insert _ _
  · rw [hwi]
    exact Set.mem_insert_of_mem _ rfl

end Reflection

theorem mem_of_pow_three_mem {M : Type*} [Group M] {x : M} (hx : Nat.Coprime 3 (orderOf x))
    {P : Subgroup M} (h : x ^ 3 ∈ P) : x ∈ P := by
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0] at hx
    norm_num at hx
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.1 h1]
    exact one_mem _
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hx (by omega)
  have e : x = (x ^ 3) ^ m := by
    rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
  rw [e]
  exact pow_mem h m

section Leaf

variable {G : Subgroup (ModGL τ k)} [Finite G] {ω : kˣ}

@[expose] noncomputable def dG (hG : ∀ x, dV (τ := τ) ω x ∈ G) (x : Fin τ.rank → ZMod 3) : G :=
  ⟨dV ω x, hG x⟩

@[expose] noncomputable def famCent (hG : ∀ x, dV (τ := τ) ω x ∈ G) (kb : List (List ℕ)) :
    Subgroup G :=
  ⨅ j : Fin kb.length, Subgroup.centralizer {dG hG (listVec τ.rank (kb.get j))}

theorem mem_familyCentralizer_of_mem_famCent (hGC : G ≤ adjointGroup τ k)
    (hG : ∀ x, dV (τ := τ) ω x ∈ G) {kb : List (List ℕ)} {g : G} (hg : g ∈ famCent hG kb) :
    (g : ModGL τ k) ∈ familyCentralizer τ k (famV (τ := τ) ω kb) := by
  rw [mem_familyCentralizer]
  refine ⟨hGC g.2, fun j => ?_⟩
  have hj := Subgroup.mem_iInf.1 hg j
  rw [Subgroup.mem_centralizer_singleton_iff] at hj
  have h1 : (dG hG (listVec τ.rank (kb.get j)) : ModGL τ k) * g =
      g * (dG hG (listVec τ.rank (kb.get j)) : ModGL τ k) := by
    have := congrArg Subtype.val hj
    simpa using this.symm
  change dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ = g
  change (dG hG (listVec τ.rank (kb.get j)) : ModGL τ k) * g *
    ((dG hG (listVec τ.rank (kb.get j)) : ModGL τ k))⁻¹ = g
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem gLAPPrimeCoreOf_leaf (hGC : G ≤ adjointGroup τ k) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    {kb : List (List ℕ)} (hX3 : ∀ g ∈ G, g ∈ torusGroup τ k → g ^ 3 = 1)
    (hcase : (familyKernel (famV (τ := τ) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        (∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α) ∧
        (∀ g ∈ G, g ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} → g ^ 3 ∈ rootSpan τ k {α, -α}) ∧
        ∀ N : Subgroup G, (∀ n ∈ N, (n : ModGL τ k) ∈ rootSpan τ k {α, -α}) →
          (∀ g : G, (g : ModGL τ k) ∈ rootSpan τ k {α, -α} → ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          Nat.Coprime 3 (Nat.card N) → N = ⊥) :
    GLAPPrimeCoreOf 3 (famCent hG kb) = ⊥ := by
  set C := famCent hG kb
  set O := GLAPPrimeCoreOf 3 C
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_gLAPPrimeCoreOf' Nat.prime_three C
  have hord : ∀ o ∈ O, Nat.Coprime 3 (orderOf (o : ModGL τ k)) := by
    intro o ho
    have h1 : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    have h2 : orderOf (o : ModGL τ k) = orderOf (⟨o, ho⟩ : O) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [h2]
    exact hcop.coprime_dvd_right h1
  have hfac := fun {o : G} (ho : o ∈ O) => familyCentralizer_le_mul τ k (famV (τ := τ) ω kb)
    (mem_familyCentralizer_of_mem_famCent hGC hG (gLAPPrimeCoreOf_le_self' C ho))
  rcases hcase with ⟨hK, hW⟩ | ⟨α, hα, hK, hW, hX4, hX5⟩
  · refine eq_bot_iff.2 fun o ho => ?_
    obtain ⟨w, hw, m, hm, he⟩ := hfac ho
    rw [hW w hw, canonicalRep_one, mul_one] at he
    have hmT : m ∈ torusGroup τ k := by
      have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
      rw [hK] at hm'
      have hbot : rootSpan τ k (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by
        simp [rootSpan]
      rwa [hbot, sup_bot_eq] at hm'
    have h3 : (o : ModGL τ k) ^ 3 = 1 := hX3 _ o.2 (he ▸ hmT)
    have h1 := mem_of_pow_three_mem (hord o ho) (P := ⊥) (by rw [h3]; exact one_mem _)
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  · set L := rootSpan τ k {α, -α}
    have hOL : ∀ o ∈ O, (o : ModGL τ k) ∈ L := by
      intro o ho
      obtain ⟨w, hw, m, hm, he⟩ := hfac ho
      have hmM : m ∈ torusGroup τ k ⊔ L := by
        have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
        rwa [hK] at hm'
      have hoM : (o : ModGL τ k) ∈ torusGroup τ k ⊔ L := by
        rw [he]
        rcases hW w hw with rfl | rfl
        · rwa [canonicalRep_one, mul_one]
        · exact mul_mem hmM (canonicalRep_rootReflection_mem hα)
      exact mem_of_pow_three_mem (hord o ho) (hX4 _ o.2 hoM)
    have hLC : ∀ g : G, (g : ModGL τ k) ∈ L → g ∈ C := by
      intro g hg
      have hgF : (g : ModGL τ k) ∈ familyCentralizer τ k (famV (τ := τ) ω kb) := by
        refine familyGroup_le_familyCentralizer (K := k) _ ?_
        change (g : ModGL τ k) ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb))
        rw [hK]
        exact le_sup_right (a := torusGroup τ k) hg
      refine Subgroup.mem_iInf.2 fun j => Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 := (mem_familyCentralizer.1 hgF).2 j
      apply Subtype.ext
      change (g : ModGL τ k) * dV ω (listVec τ.rank (kb.get j)) =
        dV ω (listVec τ.rank (kb.get j)) * g
      have h2 : dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ =
        (g : ModGL τ k) := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    exact hX5 O hOL (fun g hg n hn => gLAPPrimeCoreOf_conj_mem' g (hLC g hg) n hn) hcop

end Leaf

section Assembly

variable {G : Subgroup (ModGL τ k)} [Finite G] {ω : kˣ}

@[expose] noncomputable def dGHom (hω : ω ^ 3 = 1) (hG : ∀ x, dV (τ := τ) ω x ∈ G) :
    Multiplicative (Fin τ.rank → ZMod 3) →* G where
  toFun x := dG hG x.toAdd
  map_one' := Subtype.ext (dV_zero ω)
  map_mul' x y := Subtype.ext (dV_add hω x.toAdd y.toAdd)

theorem dGHom_ofAdd (hω : ω ^ 3 = 1) (hG : ∀ x, dV (τ := τ) ω x ∈ G) (x : Fin τ.rank → ZMod 3) :
    dGHom hω hG (Multiplicative.ofAdd x) = dG hG x := rfl

@[expose] noncomputable def genG (hG : ∀ x, dV (τ := τ) ω x ∈ G) (i : Fin τ.rank) : G :=
  dG hG (Pi.single i 1)

theorem genG_comm (hω : ω ^ 3 = 1) (hG : ∀ x, dV (τ := τ) ω x ∈ G) (i j : Fin τ.rank) :
    Commute (genG hG i) (genG hG j) := by
  change Commute (dGHom hω hG (Multiplicative.ofAdd _)) (dGHom hω hG (Multiplicative.ofAdd _))
  exact (Commute.all _ _).map _

theorem genG_pow (hω : ω ^ 3 = 1) (hG : ∀ x, dV (τ := τ) ω x ∈ G) (i : Fin τ.rank) :
    genG hG i ^ 3 = 1 := by
  show dGHom hω hG (Multiplicative.ofAdd (Pi.single i 1)) ^ 3 = 1
  rw [← map_pow, ← ofAdd_nsmul]
  have h : (3 • (Pi.single i 1 : Fin τ.rank → ZMod 3)) = 0 := by
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    have : (3 : ZMod 3) = 0 := rfl
    rw [Nat.cast_ofNat, this, zero_mul]
  rw [h, ofAdd_zero, map_one]

theorem vecProd_genG (hω : ω ^ 3 = 1) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    (a : Fin τ.rank → ZMod 3) : vecProd (genG hG) a = dG hG a := by
  rw [← dGHom_ofAdd hω hG, ofAdd_eq_prod a, ← List.prod_ofFn, map_list_prod, List.map_ofFn,
    vecProd, ← List.ofFn_eq_map]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  simp only [Function.comp_apply, map_pow]
  rfl

theorem length_stdBasis (r : ℕ) : (Native.stdBasis r).length = r := by
  simp [Native.stdBasis]

theorem get_stdBasis (j : Fin (Native.stdBasis τ.rank).length) :
    (Native.stdBasis τ.rank).get j =
      (List.range τ.rank).map fun l => if l = j.val then 1 else 0 := by
  rw [List.get_eq_getElem]
  simp [Native.stdBasis]

theorem listVec_stdBasis (j : Fin (Native.stdBasis τ.rank).length) :
    listVec τ.rank ((Native.stdBasis τ.rank).get j) =
      Pi.single (⟨j.val, by simpa [length_stdBasis] using j.2⟩ : Fin τ.rank) 1 := by
  funext i
  rw [get_stdBasis, listVec, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> simp

theorem le_sup_zpowers_of_relIndex {M : Type*} [Group M] {A B : Subgroup M} (hBA : B ≤ A)
    (hidx : B.relIndex A = 3) {t : M} (htA : t ∈ A) (htB : t ∉ B) :
    A ≤ B ⊔ Subgroup.zpowers t := by
  have h1 : (B ⊔ Subgroup.zpowers t).relIndex A ∣ 3 := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact Subgroup.relIndex_eq_one.1 h
  · exfalso
    have hle1 : B ≤ (B ⊔ Subgroup.zpowers t) ⊓ A := le_inf le_sup_left hBA
    have h2 := Subgroup.relIndex_mul_relIndex B ((B ⊔ Subgroup.zpowers t) ⊓ A) A hle1 inf_le_right
    rw [Subgroup.inf_relIndex_right, h, hidx] at h2
    have h3 : B.relIndex ((B ⊔ Subgroup.zpowers t) ⊓ A) = 1 := by omega
    have h4 := Subgroup.relIndex_eq_one.1 h3
    exact htB (h4 ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers t), htA⟩)

theorem gLAPPrimeCoreOf_centralizer_dG (hω3 : orderOf ω = 3) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    (hleaf : ∀ fl ∈ normVecs 3 τ.rank, GLAPPrimeCoreOf 3 (famCent hG (kerBasis 3 fl)) = ⊥)
    (hstd : GLAPPrimeCoreOf 3 (famCent hG (Native.stdBasis τ.rank)) = ⊥)
    {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG hG x}) = ⊥ := by
  have hω : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  set φ := vecProdHom (genG hG) (genG_comm hω hG) (genG_pow hω hG) with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dG hG a := fun a => vecProd_genG hω hG a
  have hinj : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have := dV_injective (τ := τ) hω3 (congrArg Subtype.val h)
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, this]
  set A := φ.range with hAdef
  have hmemA : ∀ a, dG hG a ∈ A := fun a => ⟨Multiplicative.ofAdd a, hφ a⟩
  have hAcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hA : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun y z => Subtype.ext (hAcomm y y.2 z z.2)⟩⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
      have h3 : (3 • Multiplicative.toAdd a) = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have : (3 : ZMod 3) = 0 := rfl
        rw [Nat.cast_ofNat, this, zero_mul]
      rw [h3, ofAdd_zero]
    rw [this, map_one]
  have hAC : A ≤ Subgroup.centralizer {dG hG x} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm y hy _ (hmemA x)
  have hA1 : A ≠ ⊥ := by
    intro h
    have h1 : dG hG x ∈ (⊥ : Subgroup G) := h ▸ hmemA x
    rw [Subgroup.mem_bot] at h1
    have h2 : dG hG x = dG hG 0 := h1.trans (Subtype.ext (dV_zero ω).symm)
    exact hx (dV_injective (τ := τ) hω3 (congrArg Subtype.val h2))
  have hcentB : ∀ (kb : List (List ℕ)), Subgroup.centralizer
      (Subgroup.closure {y | ∃ b ∈ kb, y = vecProd (genG hG) (listVec τ.rank b)} : Set G) =
        famCent hG kb := by
    intro kb
    rw [Subgroup.centralizer_closure]
    ext y
    rw [Subgroup.mem_centralizer_iff, famCent, Subgroup.mem_iInf]
    constructor
    · intro h j
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h _ ⟨kb.get j, List.get_mem kb j, (vecProd_genG hω hG _).symm⟩).symm
    · rintro h _ ⟨b, hb, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem hb
      rw [vecProd_genG hω hG]
      exact ((Subgroup.mem_centralizer_singleton_iff.1 (h j))).symm
  have hcentA : ∀ y : G, (∀ z ∈ A, z * y = y * z) ↔ y ∈ famCent hG (Native.stdBasis τ.rank) := by
    intro y
    rw [famCent, Subgroup.mem_iInf]
    constructor
    · intro h j
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h _ (hmemA _)).symm
    · intro h z hz
      obtain ⟨a, rfl⟩ := hz
      have hgen : ∀ i, genG hG i ∈ Subgroup.centralizer {y} := by
        intro i
        have := Subgroup.mem_centralizer_singleton_iff.1
          (h ⟨i.val, by simp [length_stdBasis]⟩)
        rw [listVec_stdBasis] at this
        exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
      have hz : φ a ∈ Subgroup.centralizer {y} := by
        rw [← ofAdd_toAdd a, hφdef, vecProdHom_apply, vecProd]
        refine Subgroup.list_prod_mem (K := Subgroup.centralizer {y}) fun g hg => ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        exact pow_mem (hgen i) _
      exact Subgroup.mem_centralizer_singleton_iff.1 hz
  refine gLAPPrimeCoreOf_eq_bot_of_hyperplanes Nat.prime_three hA hAC hA1 fun B hBA hidx => ?_
  obtain ⟨fl, hfl, hBeq⟩ := exists_normVec_eq_closure (genG_comm hω hG) (genG_pow hω hG) hinj hBA
    hidx
  by_cases hxB : dG hG x ∈ B
  · have hle : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer {dG hG x} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxB)
    rw [inf_eq_right.2 hle, hBeq, hcentB]
    exact hleaf fl hfl
  · have heq : Subgroup.centralizer {dG hG x} ⊓ Subgroup.centralizer (B : Set G) =
        famCent hG (Native.stdBasis τ.rank) := by
      ext y
      rw [Subgroup.mem_inf, ← hcentA]
      constructor
      · rintro ⟨h1, h2⟩ z hz
        have hz' := le_sup_zpowers_of_relIndex hBA hidx (hmemA x) hxB hz
        have hle : B ⊔ Subgroup.zpowers (dG hG x) ≤ Subgroup.centralizer {y} := by
          refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 h2 b hb)) ?_
          rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 h1).symm
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz')
      · intro h
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (h _ (hmemA x)).symm,
          Subgroup.mem_centralizer_iff.2 fun z hz => h z (hBA hz)⟩
    rw [heq]
    exact hstd

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
