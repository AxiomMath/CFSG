module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise commutatorElement

theorem mem_of_pow_eq_self_of_le_card {L : Type*} [Field L] {N : ℕ} (hN : 1 < N)
    {S : Finset L} (hS : ∀ x ∈ S, x ^ N = x) (hcard : N ≤ S.card) {c : L} (hc : c ^ N = c) :
    c ∈ S := by
  classical
  have hP0 : (Polynomial.X ^ N - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hN
  have hroot : ∀ x : L, x ^ N = x →
      x ∈ (Polynomial.X ^ N - Polynomial.X : Polynomial L).roots.toFinset := fun x hx => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  have hsub : S ⊆ (Polynomial.X ^ N - Polynomial.X : Polynomial L).roots.toFinset :=
    fun x hx => hroot x (hS x hx)
  have hle : (Polynomial.X ^ N - Polynomial.X : Polynomial L).roots.toFinset.card ≤ S.card :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      ((FiniteField.X_pow_card_sub_X_natDegree_eq L hN).le.trans hcard))
  rw [Finset.eq_of_subset_of_card_le hsub hle]
  exact hroot c hc

section BaseChange

variable {t : TwistTag} {K L : Type} [Field K] [Field L] {σ : K →+* K} {Fr : L →+* L}
  (ι : K →+* L)

theorem baseChangeGL_canonicalRep
    {τ : Tag} (w : WeylGroup τ) :
    baseChangeGL ι (canonicalRep (coxeterSystem τ) K w) = canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_weylElt_one ι i)

variable {ι}

theorem ringHom_pow_apply_comm (h : ∀ c, Fr (ι c) = ι (σ c)) (n : ℕ) (c : K) :
    (Fr ^ n) (ι c) = ι ((σ ^ n) c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, h, pow_succ',
      RingHom.coe_mul, Function.comp_apply]

theorem map_mem_orbitField_of_comm (h : ∀ c, Fr (ι c) = ι (σ c)) {a : Fin t.foldedTag.rank} {c : K}
    (hc : c ∈ orbitField t K σ a) : ι c ∈ orbitField t L Fr a := by
  rw [mem_orbitField] at hc ⊢
  rw [ringHom_pow_apply_comm h, hc]

theorem baseChangeGL_orbitX
    (h : ∀ c, Fr (ι c) = ι (σ c)) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ a) :
    baseChangeGL ι (orbitX t K σ a c : ModGL t.tag K) =
      orbitX t L Fr a ⟨ι c, map_mem_orbitField_of_comm h c.2⟩ := by
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, baseChangeGL_xUnit, ← ringHom_pow_apply_comm h]

theorem map_baseChangeGL_graphFixedRootGroup_le
    (hσ : Function.Surjective σ)
    (h : ∀ c, Fr (ι c) = ι (σ c)) :
    (graphFixedRootGroup t K σ).map (baseChangeGL ι) ≤ graphFixedRootGroup t L Fr := by
  rw [graphFixedRootGroup_eq_closure σ hσ, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨w, hw, a, c, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, map_mul, map_mul, map_inv, baseChangeGL_canonicalRep,
    baseChangeGL_orbitX h]
  have hn := canonicalRep_mem_graphFixedRootGroup (K := L) (σ := Fr) hw
  exact mul_mem (mul_mem hn (graphFixedPosUnipotent_le_graphFixedRootGroup t L Fr
    (orbitX_mem_graphFixedPosUnipotent t Fr a _))) (inv_mem hn)

theorem graphFixedRootGroup_le_map_baseChangeGL
    (hFr : Function.Surjective Fr)
    (h : ∀ c, Fr (ι c) = ι (σ c))
    (hpar : ∀ a, ∀ c ∈ orbitField t L Fr a, ∃ c₀ ∈ orbitField t K σ a, ι c₀ = c) :
    graphFixedRootGroup t L Fr ≤ (graphFixedRootGroup t K σ).map (baseChangeGL ι) := by
  rw [graphFixedRootGroup_eq_closure Fr hFr, Subgroup.closure_le]
  rintro _ ⟨w, hw, a, ⟨c, hc⟩, rfl⟩
  obtain ⟨c₀, hc₀, rfl⟩ := hpar a c hc
  have hn := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ) hw
  refine ⟨canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a ⟨c₀, hc₀⟩ *
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹, mul_mem (mul_mem hn
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
        (orbitX_mem_graphFixedPosUnipotent t σ a _))) (inv_mem hn), ?_⟩
  rw [map_mul, map_mul, map_inv, baseChangeGL_canonicalRep, baseChangeGL_orbitX h]

end BaseChange

theorem odd_diagram_Frobenius_fixed_derived_root_group
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    (∃ e : adjointGroup t.tag L ≃* adjointGroup t.tag L, ∀ g : adjointGroup t.tag L,
      (e g : ModGL t.tag L) = twistHom t L Fr g) ∧
    Finite (twistedFixedGroup t L Fr) ∧
    (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) ≤
      twistedFixedGroup t L Fr ∧
    (((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
      (twistedFixedGroup t L Fr)).Normal ∧
    (twistedFixedGroup t L Fr : Set (ModGL t.tag L)) =
      (graphFixedTorus t L Fr : Set (ModGL t.tag L)) *
        ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :
          Set (ModGL t.tag L)) ∧
    (∀ [(((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
        (twistedFixedGroup t L Fr)).Normal],
      ∀ a b : ↥(twistedFixedGroup t L Fr) ⧸
        ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
          (twistedFixedGroup t L Fr), a * b = b * a) ∧
    ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ =
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) := by
  classical
  set q := p ^ f
  set ι := algebraMap K L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < q := lt_of_lt_of_le hp.one_lt (Nat.le_self_pow (by omega) p)
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by omega : 0 < q)
    exact ⟨z, by rw [hFr, hz]⟩
  set σL : L ≃+* L := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hσL : σL.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hcomm : ∀ c, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have hpar : ∀ a, ∀ c ∈ orbitField t L Fr a, ∃ c₀ ∈ orbitField t K σ a, ι c₀ = c := by
    intro a c hc
    have : Fintype (orbitField t K σ a) := Fintype.ofFinite _
    have hN : 1 < q ^ (t.orbit a).card :=
      Nat.one_lt_pow (Finset.card_ne_zero.2 (t.orbit_nonempty a)) hq1
    have hS : ∀ x ∈ Finset.univ.image (fun c₀ : orbitField t K σ a => ι c₀),
        x ^ q ^ (t.orbit a).card = x := fun x hx => by
      obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, ← pow_apply_eq_pow hσ, (mem_orbitField (t := t)).1 c₀.2]
    have hSc : q ^ (t.orbit a).card ≤
        (Finset.univ.image (fun c₀ : orbitField t K σ a => ι c₀)).card := by
      rw [Finset.card_image_of_injective (f := fun c₀ : orbitField t K σ a => ι c₀) _
          (ι.injective.comp Subtype.val_injective),
        Finset.card_univ, ← Nat.card_eq_fintype_card, ← hσσ', hcard]
    have hc' : c ^ q ^ (t.orbit a).card = c := by
      rw [← pow_apply_eq_pow hFr]
      exact (mem_orbitField (t := t)).1 hc
    obtain ⟨c₀, -, hc₀⟩ := Finset.mem_image.1 (mem_of_pow_eq_self_of_le_card hN hS hSc hc')
    exact ⟨c₀, c₀.2, hc₀⟩
  have hH : (graphFixedRootGroup t K σ).map (baseChangeGL ι) = graphFixedRootGroup t L Fr :=
    le_antisymm (map_baseChangeGL_graphFixedRootGroup_le hσsurj hcomm)
      (graphFixedRootGroup_le_map_baseChangeGL hFrsurj hcomm hpar)
  have hL2 : ringChar L ≠ 2 := by
    have hK2 : ringChar K ≠ 2 := by
      intro h2
      have h := (FiniteField.even_card_iff_char_two (F := K)).1 h2
      have hodd' : Odd (Fintype.card K) := by
        rw [← Nat.card_eq_fintype_card, hK]
        exact hodd.pow
      rw [Nat.odd_iff] at hodd'
      omega
    refine ringChar_ne_two_of_two_ne_zero fun h => Ring.two_ne_zero hK2 (ι.injective ?_)
    rw [map_ofNat, map_zero]
    exact h
  obtain ⟨hnormal, hmul, -, -, -⟩ := fixed_root_generated_normal_subgroup t L σL
  obtain ⟨-, -, hder⟩ := odd_diagram_fixed_root_group_perfect t L hL2 σL
  rw [hσL] at hnormal hmul hder
  rw [hH]
  have hfin : Finite (twistedFixedGroup t L Fr) := by
    have hentry : ∀ (g : twistedFixedGroup t L Fr) (a b : Label t.tag), ∃ x : K,
        ι x = ((g : ModGL t.tag L) : Module.End L (RootModule t.tag L)) (Finsupp.single b 1) a := by
      intro g a b
      have hit : (twistHom t L Fr)^[t.order] g = g := Function.iterate_fixed g.2.2 _
      rw [twistHom_iterate_order] at hit
      have hcoord := congrArg (fun A : ModGL t.tag L =>
        (A : Module.End L (RootModule t.tag L)) (Finsupp.single b 1) a) hit
      simp only [Units.coe_map] at hcoord
      change entrywise (Fr ^ t.order) _ (Finsupp.single b 1) a = _ at hcoord
      rw [entrywise_single, Finsupp.mapRange_apply, pow_apply_eq_pow hFr, ← hK] at hcoord
      exact mem_range_algebraMap_of_pow_card_eq hcoord
    choose φ hφ using hentry
    refine Finite.of_injective φ fun g g' hgg' => Subtype.ext (Units.ext ?_)
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [← hφ, ← hφ, hgg']
  refine ⟨⟨twistEquiv t L Fr hFrsurj, fun _ => rfl⟩, hfin, graphFixedRootGroup_le t L Fr,
    hnormal, hmul, fun a b => ?_, hder⟩
  induction a using QuotientGroup.induction_on with | H r => ?_
  induction b using QuotientGroup.induction_on with | H s => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rw [← hder]
  have e : (((r * s)⁻¹ * (s * r) : twistedFixedGroup t L Fr) : ModGL t.tag L) =
      ⁅((s : ModGL t.tag L))⁻¹, ((r : ModGL t.tag L))⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
    simp [mul_assoc]
  rw [e]
  exact Subgroup.commutator_mem_commutator (inv_mem s.2) (inv_mem r.2)

end CFSG.LieType.Chevalley
