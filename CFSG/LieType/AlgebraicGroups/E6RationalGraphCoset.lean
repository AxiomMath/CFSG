module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRational
public import CFSG.LieType.Chevalley.E6GeometricGraphInvolution
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Twist

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem frobTwistGL_diagramMap_pow_diagramMap (e ε : ℕ) :
    frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε) (diagramMap TwistTag.E6 k) =
      diagramMap TwistTag.E6 k := by
  have hFrP : entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) =
      diagramMap TwistTag.E6 k := by
    simpa using entrywiseFrobGL_diagramMap_zpow TwistTag.E6 p e 1
  rw [frobTwistGL_apply, hFrP, ((Commute.refl (diagramMap TwistTag.E6 k)).pow_left ε).eq,
    mul_inv_cancel_right]

theorem frobTwistGL_diagramMap_pow_twice
    (e ε : ℕ) (g : ModGL TwistTag.E6.tag k) :
    frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε) g) =
      entrywiseFrobGL TwistTag.E6.tag k p (e + e) g := by
  have hFrP : entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε) =
      diagramMap TwistTag.E6 k ^ ε := by
    simpa using entrywiseFrobGL_diagramMap_zpow TwistTag.E6 p e (ε : ℤ)
  have hP2 : diagramMap TwistTag.E6 k ^ ε * diagramMap TwistTag.E6 k ^ ε = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    have h := diagramMap_pow_order TwistTag.E6 k
    rw [show TwistTag.E6.order = 2 from rfl] at h
    rw [h, one_pow]
  have hFF : entrywiseFrobGL TwistTag.E6.tag k p e (entrywiseFrobGL TwistTag.E6.tag k p e g) =
      entrywiseFrobGL TwistTag.E6.tag k p (e + e) g := by
    refine Units.ext ?_
    simp only [Units.coe_map]
    change entrywise (iterateFrobenius k p e) (entrywise (iterateFrobenius k p e) _) =
      entrywise (iterateFrobenius k p (e + e)) _
    rw [entrywise_entrywise, iterateFrobenius_add]
  rw [frobTwistGL_apply, frobTwistGL_apply, map_mul, map_mul, map_inv, hFrP, hFF]
  calc diagramMap TwistTag.E6 k ^ ε * (diagramMap TwistTag.E6 k ^ ε *
        entrywiseFrobGL TwistTag.E6.tag k p (e + e) g * (diagramMap TwistTag.E6 k ^ ε)⁻¹) *
        (diagramMap TwistTag.E6 k ^ ε)⁻¹ =
      (diagramMap TwistTag.E6 k ^ ε * diagramMap TwistTag.E6 k ^ ε) *
        entrywiseFrobGL TwistTag.E6.tag k p (e + e) g *
          (diagramMap TwistTag.E6 k ^ ε * diagramMap TwistTag.E6 k ^ ε)⁻¹ := by group
    _ = _ := by rw [hP2, one_mul, inv_one, mul_one]

variable [IsAlgClosed k]

theorem frobTwistGL_diagramMap_pow_mem_adjointGroup
    (e ε : ℕ) {g : ModGL TwistTag.E6.tag k}
    (hg : g ∈ adjointGroup TwistTag.E6.tag k) :
    frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε) g ∈
      adjointGroup TwistTag.E6.tag k := by
  have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k (ε : ℤ))
  rw [zpow_natCast] at hQ
  exact hQ _ (entrywiseFrobGL_mem p e hg)

end Twist

section Representatives

open E6SignedGraph

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem commute_diagramMap_and_frob_of_graphRep
    {A : ModGL TwistTag.E6.tag k}
    (hA : A = diagramMap TwistTag.E6 k ∨
      A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) (e : ℕ) :
    Commute (diagramMap TwistTag.E6 k) A ∧ entrywiseFrobGL TwistTag.E6.tag k p e A = A := by
  have hFrP : entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) =
      diagramMap TwistTag.E6 k := by
    simpa using entrywiseFrobGL_diagramMap_zpow TwistTag.E6 p e 1
  rcases hA with rfl | rfl
  · exact ⟨Commute.refl _, hFrP⟩
  · refine ⟨?_, ?_⟩
    · change _ * _ = _ * _
      rw [← mul_assoc, diagramMap_mul_rootDiagUnit, signTuple_perm_symm, mul_assoc]
    · rw [map_mul, entrywiseFrobGL_rootDiagUnit p e (signTuple_eq_one_or k), hFrP]

end Representatives

open E6SignedGraph in
theorem E6_rational_graph_coset_fixed_components
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (ε : ℕ)
    (hε : ε = 0 ∨ ε = 1) :
    Finite (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))) ∧
    (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))).map
        (MulAut.conj (diagramMap TwistTag.E6 k)).toMonoidHom =
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)) ∧
    ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))⁆.map
        (MulAut.conj (diagramMap TwistTag.E6 k)).toMonoidHom =
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))⁆ ∧
    ∀ x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
      (x * diagramMap TwistTag.E6 k) ^ 2 = 1 →
      (∃ y ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
        y * (x * diagramMap TwistTag.E6 k) * y⁻¹ = diagramMap TwistTag.E6 k ∨
          y * (x * diagramMap TwistTag.E6 k) * y⁻¹ =
            rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) ∧
      ∀ r : ℕ, r.Prime → ∀ L : Subgroup ↥(⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))⁆ ⊓
            Subgroup.centralizer {x * diagramMap TwistTag.E6 k}),
        CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
  classical
  set P := diagramMap TwistTag.E6 k with hPdef
  set F := frobTwistGL TwistTag.E6.tag k p e (P ^ ε) with hFdef
  set G := adjointGroup TwistTag.E6.tag k with hGdef
  set R := fixedPointsIn G F with hRdef
  have hFP : F P = P := frobTwistGL_diagramMap_pow_diagramMap e ε
  have hFG : ∀ g ∈ G, F g ∈ G := fun g hg => frobTwistGL_diagramMap_pow_mem_adjointGroup e ε hg
  have hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hfin : Finite R := by
    set σ := iterateFrobeniusEquiv k p (e + e) with hσ
    have : Finite (fixSubfield σ) := by
      have hq1 : 1 < p ^ (e + e) := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
      have hP0 : (Polynomial.X ^ (p ^ (e + e)) - Polynomial.X : Polynomial k) ≠ 0 :=
        FiniteField.X_pow_card_sub_X_ne_zero k hq1
      refine Set.Finite.to_subtype ((Polynomial.finite_setOfPred_isRoot hP0).subset fun c hc => ?_)
      rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      exact hc
    have := finite_rationalFixedGroup σ (1 : ModGL TwistTag.E6.tag (fixSubfield σ))
    have hle : R ≤ rationalFixedGroup σ (1 : ModGL TwistTag.E6.tag (fixSubfield σ)) := by
      intro g hg
      obtain ⟨hgG, hgF⟩ := Subgroup.mem_inf.1 hg
      have hgF' : F g = g := hgF
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgG, ?_⟩, ?_⟩
      · rw [map_one, Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
      · change Units.map (entrywiseHom σ.toRingHom) g = g
        rw [iterateFrobeniusEquiv_toRingHom]
        change entrywiseFrobGL TwistTag.E6.tag k p (e + e) g = g
        rw [← frobTwistGL_diagramMap_pow_twice e ε g]
        change F (F g) = g
        rw [hgF', hgF']
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hPR : ∀ g ∈ R, P * g * P⁻¹ ∈ R := by
    intro g hg
    obtain ⟨hgG, hgF⟩ := Subgroup.mem_inf.1 hg
    have hgF' : F g = g := hgF
    refine Subgroup.mem_inf.2 ⟨hPG g hgG, ?_⟩
    change F (P * g * P⁻¹) = P * g * P⁻¹
    rw [map_mul, map_mul, map_inv, hFP, hgF']
  have hRmap : R.map (MulAut.conj P).toMonoidHom = R := by
    refine le_antisymm ?_ fun g hg => ⟨P * g * P⁻¹, hPR g hg, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact hPR g hg
    · change P * (P * g * P⁻¹) * P⁻¹ = g
      calc P * (P * g * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
        _ = g := by rw [hP2, one_mul, inv_one, mul_one]
  have hHmap : ⁅R, R⁆.map (MulAut.conj P).toMonoidHom = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, hRmap]
  refine ⟨hfin, hRmap, hHmap, fun x hx hx2 => ?_⟩
  obtain ⟨hxG, hxF⟩ := Subgroup.mem_inf.1 hx
  have hxF' : F x = x := hxF
  obtain ⟨g, hgG, hgA⟩ := E6_geometric_graph_involution_two_representatives hp k halg hxG hx2
  obtain ⟨A, hAdef⟩ : ∃ A, g * (x * P) * g⁻¹ = A := ⟨_, rfl⟩
  have hAform : A = P ∨ A = rootDiagUnit TwistTag.E6.tag (signTuple k) * P := hAdef ▸ hgA
  obtain ⟨hPA, hFrA⟩ := commute_diagramMap_and_frob_of_graphRep (p := p) hAform e
  have hFA : F A = A := by
    rw [hFdef, frobTwistGL_apply, hFrA, ((hPA.pow_left ε).eq), mul_inv_cancel_right]
  have hFxP : F (x * P) = x * P := by rw [map_mul, hxF', hFP]
  have hFg : (F g)⁻¹ * A * F g = x * P := by
    have h := congrArg F hAdef
    rw [hFA, map_mul, map_mul, map_inv, hFxP] at h
    rw [← h]
    group
  obtain ⟨c, hcdef⟩ : ∃ c, g * (F g)⁻¹ = c := ⟨_, rfl⟩
  have hcZ : c ∈ graphCentralizer TwistTag.E6.tag k A := by
    refine Subgroup.mem_inf.2 ⟨hcdef ▸ mul_mem hgG (inv_mem (hFG g hgG)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * A = g * ((F g)⁻¹ * A * F g) * (F g)⁻¹ := by rw [← hcdef]; group
      _ = g * (x * P) * g⁻¹ * (g * (F g)⁻¹) := by rw [hFg]; group
      _ = A * c := by rw [hAdef, hcdef]
  obtain ⟨-, hLang⟩ := E6_geometric_graph_centralizers_connected_Lang p hp k A hAform
  obtain ⟨-, -, -, hsurj⟩ := hLang e he ε
  obtain ⟨z, hz, hzc⟩ := hsurj c hcZ
  have hzc' : z⁻¹ * F z = c := hzc
  obtain ⟨hzG, hzA⟩ := Subgroup.mem_inf.1 hz
  rw [Subgroup.mem_centralizer_singleton_iff] at hzA
  obtain ⟨y, hydef⟩ : ∃ y, z * g = y := ⟨_, rfl⟩
  have hyR : y ∈ R := by
    refine Subgroup.mem_inf.2 ⟨hydef ▸ mul_mem hzG hgG, ?_⟩
    change F y = y
    have hFz : F z = z * c := by rw [← hzc']; group
    rw [← hydef, map_mul, hFz, ← hcdef]
    group
  have hyA : y * (x * P) * y⁻¹ = A := by
    calc y * (x * P) * y⁻¹ = z * (g * (x * P) * g⁻¹) * z⁻¹ := by rw [← hydef]; group
      _ = A := by rw [hAdef, hzA]; group
  refine ⟨⟨y, hyR, hyA ▸ hAdef ▸ hgA⟩, fun r hr L hL => ?_⟩
  obtain ⟨hyG, hFy⟩ := Subgroup.mem_inf.1 hyR
  have hFy' : F y = y := hFy
  set B := R ⊓ Subgroup.centralizer {x * P} with hBdef
  set J := frobFixedCentralizer TwistTag.E6.tag p e A (P ^ ε) with hJdef
  have hHR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_self R
  have hBR : B ≤ R := inf_le_left
  have : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective hBR)
  have : (⁅R, R⁆.subgroupOf R).Normal := commutator_subgroupOf_normal R
  have : Group.IsSolvable (R ⧸ ⁅R, R⁆.subgroupOf R) := isSolvable_quotient_commutator_subgroupOf R
  have : ((⁅R, R⁆ ⊓ B).subgroupOf B).Normal := normal_inf_subgroupOf hBR
  have : Group.IsSolvable (B ⧸ (⁅R, R⁆ ⊓ B).subgroupOf B) := isSolvable_quotient_inf_subgroupOf hBR
  have hHB : ⁅R, R⁆ ⊓ B = ⁅R, R⁆ ⊓ Subgroup.centralizer {x * P} := by
    rw [hBdef, ← inf_assoc, inf_eq_left.2 hHR]
  have hBJ : B.map (MulAut.conj y).toMonoidHom = J := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨hbR, hbc⟩ := Subgroup.mem_inf.1 hb
      obtain ⟨hbG, hbF⟩ := Subgroup.mem_inf.1 hbR
      have hbF' : F b = b := hbF
      rw [Subgroup.mem_centralizer_singleton_iff] at hbc
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hyG hbG) (inv_mem hyG), ?_⟩,
        ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hyA]
        calc y * b * y⁻¹ * (y * (x * P) * y⁻¹) = y * (b * (x * P)) * y⁻¹ := by group
          _ = y * ((x * P) * b) * y⁻¹ := by rw [hbc]
          _ = y * (x * P) * y⁻¹ * (y * b * y⁻¹) := by group
      · change F (y * b * y⁻¹) = y * b * y⁻¹
        rw [map_mul, map_mul, map_inv, hFy', hbF']
    · intro hw
      obtain ⟨hwZ, hwF⟩ := Subgroup.mem_inf.1 hw
      obtain ⟨hwG, hwc⟩ := Subgroup.mem_inf.1 hwZ
      have hwF' : F w = w := hwF
      rw [Subgroup.mem_centralizer_singleton_iff] at hwc
      refine ⟨y⁻¹ * w * y, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
        ⟨mul_mem (mul_mem (inv_mem hyG) hwG) hyG, ?_⟩, ?_⟩, ?_⟩
      · change F (y⁻¹ * w * y) = y⁻¹ * w * y
        rw [map_mul, map_mul, map_inv, hFy', hwF']
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hxP : x * P = y⁻¹ * A * y := by rw [← hyA]; group
        rw [hxP]
        calc y⁻¹ * w * y * (y⁻¹ * A * y) = y⁻¹ * (w * A) * y := by group
          _ = y⁻¹ * (A * w) * y := by rw [hwc]
          _ = y⁻¹ * A * y * (y⁻¹ * w * y) := by group
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  set L' := L.map (⁅R, R⁆ ⊓ Subgroup.centralizer {x * P}).subtype with hL'def
  have hsub : L'.subgroupOf (⁅R, R⁆ ⊓ Subgroup.centralizer {x * P}) = L :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) L
  have h1 : L' ≤ ⁅R, R⁆ ⊓ B ∧ CFSG.IsPComponent r (L'.subgroupOf (⁅R, R⁆ ⊓ B)) := by
    rw [hHB, hsub]
    exact ⟨Subgroup.map_subtype_le L, hL⟩
  have h2 := (isPComponent_subgroupOf_iff_of_isSolvable inf_le_right r hr L').2 h1
  have h3 := (isPComponent_subgroupOf_map_conj_iff y hBJ r hr L').1 h2
  have hε' : ε ∈ ({0, 1} : Set ℕ) := by
    rcases hε with rfl | rfl <;> simp
  obtain ⟨AK, hAK⟩ : ∃ AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)),
      (A = diagramMap TwistTag.E6 k ∧ AK = diagramMap TwistTag.E6 _) ∨
      (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k ∧
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) := by
    rcases hAform with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨-, hcomp, -⟩ :=
    E6_canonical_graph_centralizer_rational_fixed_components p hp he k A AK hAK
  have hq := (hcomp ε hε').2 r hr _ h3.2
  let e₁ : L ≃* L' := Subgroup.equivMapOfInjective L _ Subtype.val_injective
  let e₂ : L' ≃* L'.map (MulAut.conj y).toMonoidHom :=
    Subgroup.equivMapOfInjective L' _ (MulAut.conj y).injective
  exact (isQuasisimple_congr (e₁.trans (e₂.trans (Subgroup.subgroupOfEquivOfLe h3.1).symm))).2 hq

end CFSG.LieType.AlgebraicGroups
