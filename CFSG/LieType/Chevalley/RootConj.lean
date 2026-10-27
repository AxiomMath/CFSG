module

public import CFSG.LieType.Chevalley.Native
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag} {K : Type} [Field K]

theorem eltElement_simpleRoot (i : Fin τ.rank) (c : K) :
    (rootOperatorFamily τ).eltElement (simpleRoot τ i) c = xElement i c :=
  Subtype.ext ((rootOperatorFamily τ).eltUnit_simple i c)

theorem xElement_add (i : Fin τ.rank) (a b : K) :
    xElement i (a + b) = xElement (K := K) i a * xElement i b := by
  rw [← eltElement_simpleRoot, ← eltElement_simpleRoot, ← eltElement_simpleRoot,
    RootOperatorFamily.eltElement_add]

theorem xElement_zero (i : Fin τ.rank) : xElement (K := K) i 0 = 1 := by
  rw [← eltElement_simpleRoot, RootOperatorFamily.eltElement_zero]

theorem xElement_inv (i : Fin τ.rank) (c : K) : (xElement (K := K) i c)⁻¹ = xElement i (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← xElement_add, add_neg_cancel, xElement_zero]

theorem exists_conj_prod_weylElement (ω : List (Fin τ.rank)) (α : Root τ) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      (ω.map (weylElement τ K)).prod * (rootOperatorFamily τ).eltElement α c *
          ((ω.map (weylElement τ K)).prod)⁻¹ =
        (rootOperatorFamily τ).eltElement ((ω.map (simple τ)).prod • α) (ε * c) := by
  induction ω with
  | nil => exact ⟨1, Or.inl rfl, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    set β := (ω.map (simple τ)).prod • α
    refine ⟨((rootOperatorFamily τ).sign i β : K) * ε, ?_, fun c => ?_⟩
    · rcases (rootOperatorFamily τ).sign_eq i β with h1 | h1 <;> rcases hε with h2 | h2 <;>
        simp [h1, h2]
    · simp only [List.map_cons, List.prod_cons, mul_inv_rev]
      have e : weylElement τ K i * (ω.map (weylElement τ K)).prod *
          (rootOperatorFamily τ).eltElement α c *
          (((ω.map (weylElement τ K)).prod)⁻¹ * (weylElement τ K i)⁻¹) =
          weylElement τ K i * ((ω.map (weylElement τ K)).prod *
            (rootOperatorFamily τ).eltElement α c * ((ω.map (weylElement τ K)).prod)⁻¹) *
            (weylElement τ K i)⁻¹ := by group
      rw [e, h c, RootOperatorFamily.weylElement_mul_eltElement_mul_inv, mul_smul, mul_assoc]

theorem exists_conj_nrep (w : WeylGroup τ) (α : Root τ) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      nrep τ K w * (rootOperatorFamily τ).eltElement α c * (nrep τ K w)⁻¹ =
        (rootOperatorFamily τ).eltElement (w • α) (ε * c) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [nrep_eq_prod τ K hω]
  exact exists_conj_prod_weylElement ω α

theorem torusElement_conj_xElement (i k : Fin τ.rank) (t : Kˣ) (c : K) :
    torusElement τ K i t * xElement k c * (torusElement τ K i t)⁻¹ =
      xElement k (((t ^ τ.cartan i k : Kˣ) : K) * c) := by
  rw [← eltElement_simpleRoot, RootOperatorFamily.torusElement_mul_eltElement_mul_inv,
    ← eltElement_simpleRoot]
  congr 3
  simp [simpleRoot, Pi.single_apply]

theorem torusElement_commute (i j : Fin τ.rank) (t u : Kˣ) :
    Commute (torusElement τ K i t) (torusElement τ K j u) := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun x => Finsupp.ext fun a => ?_))
  change (torusElt τ K i t : Module.End K (RootModule τ K))
      ((torusElt τ K j u : Module.End K (RootModule τ K)) x) a =
    (torusElt τ K j u : Module.End K (RootModule τ K))
      ((torusElt τ K i t : Module.End K (RootModule τ K)) x) a
  rw [torusElt_apply, torusElt_apply, torusElt_apply, torusElt_apply, mul_left_comm]

theorem commutator_eltElement_of_repCheck (hv : allValid τ = true) {a b g : ℕ} {C : ℤ}
    (h : repCheck τ a b [(1, 1, g, C)] = true) (hg : g < τ.rootCertificate.roots.length)
    {α β : Root τ} (ha : rootPos α = a) (hb : rootPos β = b) (s t : K) :
    (rootOperatorFamily τ).eltElement α s * (rootOperatorFamily τ).eltElement β t *
        ((rootOperatorFamily τ).eltElement α s)⁻¹ * ((rootOperatorFamily τ).eltElement β t)⁻¹ =
      (rootOperatorFamily τ).eltElement (rootAt τ g hg) ((C : K) * s * t) := by
  set F := rootOperatorFamily τ
  have hop := elt_mul_elt_of_repCheck (R := K) hv h α β ha hb s t
  have hmul : F.eltElement α s * F.eltElement β t =
      factorsElement K [(1, 1, g, C)] s t * F.eltElement β t * F.eltElement α s := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, RootOperatorFamily.coe_eltElement,
      RootOperatorFamily.coe_eltUnit, coe_factorsElement]
    exact hop
  have hf : factorsElement K [(1, 1, g, C)] s t =
      F.eltElement (rootAt τ g hg) ((C : K) * s * t) := by
    simp [factorsElement, hg, F]
  rw [hmul, hf]
  group

end CFSG.LieType.Chevalley
