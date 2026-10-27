module

public import CFSG.CharacterTheory.Wreathed.QuaternionOvergroups

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open BenderSuzuki.External BenderSuzuki.PFchapter1section1
open QuaternionOvergroups
open scoped Classical Pointwise
universe u
variable {K : Type u} [Group K] [Finite K]

@[expose] def sylowEmbeddedSubgroup (P : Sylow 2 K) {m : ℕ}
    (i : P →* Wreath m) (A : Subgroup K) : Subgroup (Wreath m) :=
  (A.subgroupOf (P : Subgroup K)).map i

@[expose] def sylowEmbeddedSubgroupEquiv (P : Sylow 2 K) {m : ℕ}
    (i : P →* Wreath m) (hi : Function.Injective i)
    (A : Subgroup K) (hAP : A ≤ P) : A ≃* sylowEmbeddedSubgroup P i A :=
  (Subgroup.subgroupOfEquivOfLe hAP).symm.trans
    ((A.subgroupOf (P : Subgroup K)).equivMapOfInjective i hi)

omit [Finite K] in
theorem sylowEmbeddedSubgroupEquiv_coe (P : Sylow 2 K) {m : ℕ}
    (i : P →* Wreath m) (hi : Function.Injective i)
    (A : Subgroup K) (hAP : A ≤ P) (a : A) :
    (sylowEmbeddedSubgroupEquiv P i hi A hAP a : Wreath m) = i ⟨a, hAP a.property⟩ := rfl

omit [Finite K] in
theorem sylowEmbeddedSubgroup_centralizer (P : Sylow 2 K) {m : ℕ}
    (i : P →* Wreath m) (hi : Function.Injective i)
    (A : Subgroup K) (hAP : A ≤ P) :
    i.range ⊓ Subgroup.centralizer (sylowEmbeddedSubgroup P i A : Set (Wreath m)) =
      sylowEmbeddedSubgroup P i ((P : Subgroup K) ⊓ Subgroup.centralizer (A : Set K)) := by
  ext w
  constructor
  · rintro ⟨⟨a, rfl⟩, hc⟩
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    change (a : K) ∈ (P : Subgroup K) ⊓ Subgroup.centralizer (A : Set K)
    refine ⟨a.property, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    let bP : P := ⟨b, hAP hb⟩
    have hbI : i bP ∈ sylowEmbeddedSubgroup P i A :=
      Subgroup.mem_map.mpr ⟨bP, hb, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hc (i bP) hbI
    have hP : bP * a = a * bP := hi (by simpa only [map_mul] using h)
    exact congrArg Subtype.val hP
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro b ⟨bP, hb, rfl⟩
    have hc : (a : K) ∈ Subgroup.centralizer (A : Set K) := ha.2
    have h := Subgroup.mem_centralizer_iff.mp hc (bP : K) hb
    have hP : bP * a = a * bP := Subtype.ext h
    simpa only [map_mul] using congrArg i hP

omit [Finite K] in
theorem sylowEmbeddedSubgroup_center (P : Sylow 2 K) {m : ℕ}
    (i : P →* Wreath m) (hi : Function.Injective i)
    (A : Subgroup K) (hAP : A ≤ P) :
    sylowEmbeddedSubgroup P i ((Subgroup.center A).map A.subtype) =
      (Subgroup.center (sylowEmbeddedSubgroup P i A)).map
        (sylowEmbeddedSubgroup P i A).subtype := by
  let E := sylowEmbeddedSubgroupEquiv P i hi A hAP
  rw [← Subgroup.map_center_eq E, Subgroup.map_map]
  ext w
  constructor
  · rintro ⟨a, ⟨b, hb, hba⟩, rfl⟩
    refine ⟨b, hb, ?_⟩
    change (E b : Wreath m) = i a
    exact (sylowEmbeddedSubgroupEquiv_coe P i hi A hAP b).trans
      (congrArg i (Subtype.ext hba))
  · rintro ⟨b, hb, rfl⟩
    change (E b : Wreath m) ∈ _
    rw [show (E b : Wreath m) = i ⟨b, hAP b.property⟩ from
      sylowEmbeddedSubgroupEquiv_coe P i hi A hAP b]
    exact Subgroup.mem_map.mpr ⟨⟨b, hAP b.property⟩,
      Subgroup.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩

theorem proper_embedded_quaternion_centric_step
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (hY : Original.Y (2 ^ n) ≤ i.range) (hproper : i.range < ⊤)
    (x : P) (hx : i x = Original.x (2 ^ n))
    (A : Subgroup K) (hAP : A ≤ P)
    (hcent : subgroupCentralizerIn (P : Subgroup K) A ≤ A)
    (hext : HuppertExtremal P A) (g : K)
    (hg : g ∈ Subgroup.normalizer (A : Set K)) (hxA : (x : K) ∈ A) :
    g⁻¹ * (x : K) * g = x := by
  let AI := sylowEmbeddedSubgroup P i A
  let E := sylowEmbeddedSubgroupEquiv P i hi A hAP
  have hAI : AI ≤ i.range := Subgroup.map_le_range _ _
  have hcentEq : (P : Subgroup K) ⊓ Subgroup.centralizer (A : Set K) =
      (Subgroup.center A).map A.subtype := by
    ext a
    constructor
    · intro ha
      let aA : A := ⟨a, hcent ha⟩
      refine ⟨aA, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp ha.2 b b.property)
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hAP a.property, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro b hb
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha (⟨b, hb⟩ : A))
  have hcentI : i.range ⊓ Subgroup.centralizer (AI : Set (Wreath (2 ^ n))) =
      (Subgroup.center AI).map AI.subtype := by
    rw [sylowEmbeddedSubgroup_centralizer P i hi A hAP, hcentEq,
      sylowEmbeddedSubgroup_center P i hi A hAP]
  have hstr :=
    proper_overgroups_of_maximal_quaternion_have_no_odd_abelian_centric_automorphisms
      n hn
  by_cases hab : IsMulCommutative A
  · let : IsMulCommutative A := hab
    have habI : IsMulCommutative AI := by
      apply isMulCommutative_iff.mpr
      intro a b
      apply E.symm.injective
      simpa only [map_mul] using (isMulCommutative_iff.mp hab) (E.symm a) (E.symm b)
    have hcentAb : i.range ⊓ Subgroup.centralizer (AI : Set (Wreath (2 ^ n))) = AI := by
      rw [hcentI, Subgroup.center_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    have hAutI : IsPGroup 2 (MulAut AI) := (hstr.2 i.range hY hproper).2.2.1 AI hAI habI hcentAb
    have hAut : IsPGroup 2 (MulAut A) := hAutI.of_equiv (MulAut.congr E.symm)
    obtain ⟨p, hpP, _, hp⟩ := extremal_two_group_step_replacement P A hext hAut g hg
    let pP : P := ⟨p, hpP⟩
    have hfix : i (pP⁻¹ * x * pP) = i x := by
      simp only [map_mul, map_inv, hx]
      exact ((wreath_center_involution_and_quaternion_coordinates n hn).x_class _).mp
        (by exact isConj_iff.mpr ⟨(i pP)⁻¹, by group⟩)
    have hfixP := congrArg Subtype.val (hi hfix)
    exact (hp (x : K) hxA).symm.trans hfixP
  · have hnonab : ∃ a b : A, a * b ≠ b * a := by
      by_contra h
      apply hab
      apply isMulCommutative_iff.mpr
      intro a b
      exact not_not.mp (fun hn => h ⟨a, b, hn⟩)
    have hnonabI : ∃ a b : AI, a * b ≠ b * a :=
      by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨E a, E b, fun h => hab (E.injective (by simpa only [map_mul] using h))⟩
    obtain ⟨_, _, _, _, hxI, hfix⟩ :=
      (hstr.2 i.range hY hproper).2.2.2 AI hAI hnonabI hcentI
    let xA : A := ⟨x, hxA⟩
    have hxEA : E xA = (⟨Original.x (2 ^ n), hxI⟩ : AI) := by
      apply Subtype.ext
      exact (sylowEmbeddedSubgroupEquiv_coe P i hi A hAP xA).trans hx
    let phi : MulAut AI := E.symm.trans
      ((A.normalizerMonoidHom ⟨g, hg⟩).symm.trans E)
    have hf := hfix phi
    have hfA : (A.normalizerMonoidHom ⟨g, hg⟩).symm xA = xA := by
      apply E.injective
      have hf' : E ((A.normalizerMonoidHom ⟨g, hg⟩).symm
          (E.symm ⟨Original.x (2 ^ n), hxI⟩)) = ⟨Original.x (2 ^ n), hxI⟩ := hf
      rw [← hxEA, E.symm_apply_apply] at hf'
      exact hf'
    exact (Subgroup.normalizerMonoidHom_apply_symm_apply_coe A ⟨g, hg⟩ xA).symm.trans
      (congrArg Subtype.val hfA)


theorem proper_embedded_quaternion_centric_chain
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (hY : Original.Y (2 ^ n) ≤ i.range) (hproper : i.range < ⊤)
    (x : P) (hx : i x = Original.x (2 ^ n)) {g : K}
    (hchain : HuppertCentricConjugationDecomposition (P : Subgroup K)
      (HuppertExtremal P) (Subgroup.zpowers (x : K)) g) :
    g⁻¹ * (x : K) * g = x := by
  induction hchain with
  | one => group
  | @tail g h A hprev hext hAP hcur hh hc ih =>
    have hxA : (x : K) ∈ A := by
      have hmem : g⁻¹ * (x : K) * g ∈ rightConjugate (Subgroup.zpowers (x : K)) g :=
        Subgroup.mem_map.mpr ⟨x, Subgroup.mem_zpowers _, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      simpa only [ih] using hcur hmem
    have hfix : h⁻¹ * (x : K) * h = x := by
      rcases hc with hcent | hcentral
      · exact proper_embedded_quaternion_centric_step n hn P i hi hY hproper
          x hx A hAP hcent hext h hh hxA
      · have hcomm := Subgroup.mem_centralizer_iff.mp hcentral (x : K) hxA
        calc
          h⁻¹ * (x : K) * h = h⁻¹ * ((x : K) * h) := by group
          _ = h⁻¹ * (h * (x : K)) := by rw [hcomm]
          _ = x := by group
    calc
      (g * h)⁻¹ * (x : K) * (g * h) = h⁻¹ * (g⁻¹ * (x : K) * g) * h := by group
      _ = h⁻¹ * (x : K) * h := by rw [ih]
      _ = x := hfix

theorem proper_embedded_quaternion_singleton_fusion
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (hY : Original.Y (2 ^ n) ≤ i.range) (hproper : i.range < ⊤)
    (x : P) (hx : i x = Original.x (2 ^ n))
    (g : K) (hg : g⁻¹ * (x : K) * g ∈ (P : Subgroup K)) :
    g⁻¹ * (x : K) * g = x := by
  have hAP : Subgroup.zpowers (x : K) ≤ (P : Subgroup K) :=
    Subgroup.zpowers_le.mpr x.property
  have hcur : rightConjugate (Subgroup.zpowers (x : K)) g ≤ (P : Subgroup K) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  exact proper_embedded_quaternion_centric_chain n hn P i hi hY hproper x hx
    (HuppertExtremal.centric_conjugation_decomposition P hAP hcur)

omit [Finite K] in
theorem proper_embedded_quaternion_central_involution
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (x : P) (hx : i x = Original.x (2 ^ n)) :
    x ∈ Subgroup.center (P : Subgroup K) ∧ orderOf x = 2 := by
  have hcoord := wreath_center_involution_and_quaternion_coordinates n hn
  constructor
  · apply Subgroup.mem_center_iff.mpr
    intro y
    apply hi
    simp only [map_mul, hx]
    have hfix : (i y)⁻¹ * Original.x (2 ^ n) * i y = Original.x (2 ^ n) :=
      (hcoord.x_class _).mp (isConj_iff.mpr ⟨(i y)⁻¹, by group⟩)
    calc
      i y * Original.x (2 ^ n) = i y * ((i y)⁻¹ * Original.x (2 ^ n) * i y) :=
        congrArg (fun z => i y * z) hfix.symm
      _ = Original.x (2 ^ n) * i y := by group
  · rw [← orderOf_injective i hi x, hx]
    exact hcoord.involution_orders.1


theorem proper_quaternion_wreath_overgroup_Sylow_forces_centralizer_factorization
    {K : Type} [Group K] [Finite K]
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (hY : Original.Y (2 ^ n) ≤ i.range) (hproper : i.range < ⊤)
    (x : P) (hx : i x = Original.x (2 ^ n)) :
    (∀ g : K, g⁻¹ * (x : K) * g ∈ (P : Subgroup K) → g⁻¹ * (x : K) * g = x) ∧
      (∀ g : K, ∃ k ∈ oddCore K,
        ∃ c ∈ Subgroup.centralizer ({(x : K)} : Set K), g = k * c) ∧
      (QuotientGroup.mk (x : K) : K ⧸ oddCore K) ∈ Subgroup.center (K ⧸ oddCore K) := by
  have hfus := proper_embedded_quaternion_singleton_fusion n hn P i hi hY hproper x hx
  obtain ⟨hcent, hord⟩ := proper_embedded_quaternion_central_involution n hn P i hi x hx
  obtain ⟨hfac, hquot⟩ := CFSG.Adapters.glauberman_zStar P x hcent hord hfus
  refine ⟨hfus, ?_, hquot⟩
  intro g
  obtain ⟨c, hc, k, hk, hg⟩ := hfac g⁻¹
  refine ⟨k⁻¹, (oddCore K).inv_mem hk, c⁻¹,
    (Subgroup.centralizer ({(x : K)} : Set K)).inv_mem hc, ?_⟩
  rw [← mul_inv_rev, ← hg, inv_inv]


theorem proper_quaternion_wreath_overgroup_Sylow_odd_core_product
    {K : Type} [Group K] [Finite K]
    (n : ℕ) (hn : 2 ≤ n) (P : Sylow 2 K)
    (i : P →* Wreath (2 ^ n)) (hi : Function.Injective i)
    (hY : Original.Y (2 ^ n) ≤ i.range) (hproper : i.range < ⊤)
    (x : P) (hx : i x = Original.x (2 ^ n)) :
    (oddCore K : Set K) * (Subgroup.centralizer ({(x : K)} : Set K) : Set K) = Set.univ ∧
      (QuotientGroup.mk (x : K) : K ⧸ oddCore K) ∈ Subgroup.center (K ⧸ oddCore K) := by
  obtain ⟨_, hfac, hquot⟩ :=
    proper_quaternion_wreath_overgroup_Sylow_forces_centralizer_factorization
      n hn P i hi hY hproper x hx
  refine ⟨Set.eq_univ_iff_forall.mpr ?_, hquot⟩
  intro g
  obtain ⟨k, hk, c, hc, hg⟩ := hfac g
  exact Set.mem_mul.mpr ⟨k, hk, c, hc, hg.symm⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
