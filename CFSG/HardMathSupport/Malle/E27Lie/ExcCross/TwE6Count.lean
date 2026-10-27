module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Order
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TorsionTorus
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Sylow
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6OneBound
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 CoxeterSystem

set_option linter.unusedSectionVars false

section TwCount


variable {L : Type} [Field L]

local notation "ρ6" => TwistTag.E6.perm

theorem rootChar_zpow_exps {τ : Tag} (u : Lˣ) (e : Fin τ.rank → ℤ) (v : Fin τ.rank → ℤ) :
    rootChar (fun j => u ^ e j) v = u ^ ∑ j, e j * v j := by
  rw [rootChar, ← prodZpowSum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul]

theorem cartan_diag6 (i : Fin TwistTag.E6.tag.rank) : TwistTag.E6.tag.cartan i i = 2 := by
  revert i
  decide

theorem comm_weylElt_rootDiagUnit6 (i : Fin TwistTag.E6.tag.rank) (u : Lˣ) :
    weylElt TwistTag.E6.tag L i 1 * rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u) *
        (weylElt TwistTag.E6.tag L i 1)⁻¹ *
        (rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u))⁻¹ =
      torusElt TwistTag.E6.tag L i u⁻¹ := by
  let e1 : Fin TwistTag.E6.tag.rank → ℤ := fun j => (if j = i then (1 : ℤ) else 0) - TwistTag.E6.tag.cartan i j
  let a : Fin TwistTag.E6.tag.rank → Lˣ := fun j => u ^ e1 j
  let c : Fin TwistTag.E6.tag.rank → Lˣ := fun j => u ^ (-(TwistTag.E6.tag.cartan i j))
  have hb : (Pi.mulSingle i u : Fin TwistTag.E6.tag.rank → Lˣ) = fun j => u ^ (if j = i then (1 : ℤ) else 0) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hac : a = Pi.mulSingle i u * c := by
    funext j
    simp only [a, e1, c, Pi.mul_apply, hb, ← zpow_add]
    rw [sub_eq_add_neg]
  have hchar : ∀ v, rootChar a (reflect TwistTag.E6.tag i v) = rootChar (Pi.mulSingle i u) v := by
    intro v
    rw [hb, rootChar_zpow_exps, rootChar_zpow_exps]
    congr 1
    set S : ℤ := ∑ j, TwistTag.E6.tag.cartan i j * v j with hS
    have h1 : ∑ j, e1 j * reflect TwistTag.E6.tag i v j = ∑ j, e1 j * v j - S * e1 i := by
      simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp only [Pi.single_eq_same, mul_one]; ring
      · intro j _ hj; simp [Pi.single_apply, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1]
    have h2 : ∑ j, e1 j * v j = v i - S := by
      simp only [e1, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ i v]
      simp [hS]
    have h3 : e1 i = -1 := by
      simp only [e1, ↓reduceIte]
      rw [cartan_diag6 i]; norm_num
    have h4 : ∑ j, (if j = i then (1 : ℤ) else 0) * v j = v i := by
      simp
    rw [h2, h3, h4]
    ring
  have hconj : rootDiagUnit TwistTag.E6.tag a = weylElt TwistTag.E6.tag L i 1 * rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u) *
      (weylElt TwistTag.E6.tag L i 1)⁻¹ := by
    rw [← canonicalRep_simple (coxeterSystem TwistTag.E6.tag) L i]
    refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ _).2 fun v => ?_
    rw [simple_smul]
    exact hchar v
  have hcomm : rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u) *
      rootDiagUnit TwistTag.E6.tag c = rootDiagUnit TwistTag.E6.tag c *
      rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u) := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  rw [torusElt_eq_rootDiagUnit, ← hconj, hac, rootDiagUnit_mul, hcomm, mul_inv_cancel_right]
  congr 1
  funext j
  simp only [c, inv_zpow']


theorem weylElt_mem_X6 (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) (i : Fin TwistTag.E6.tag.rank) :
    weylElt TwistTag.E6.tag L i 1 ∈ X6 L Fr w0 :=
  tits6_le_X6 Fr w0 (weylElt_mem_tits6 i)

theorem rootDiagUnit_mulSingle_mem_X6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    (i : Fin TwistTag.E6.tag.rank) {u : Lˣ} (hu : u ^ (q + 1) = 1) :
    rootDiagUnit TwistTag.E6.tag (Pi.mulSingle i u) ∈ X6 L Fr w0 := by
  refine twistedTorus_le_X6 Fr w0 ?_
  rw [twistedTorus6_eq Fr hw0]
  refine ⟨Pi.mulSingle i u, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedCharTuples_neg_iff hFr]
  intro j
  by_cases h : j = i
  · subst h; simpa using hu
  · simp [Pi.mulSingle_eq_of_ne h]

theorem torusElt_mem_Y6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq3 : 3 ∣ q + 1) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    {Y : Subgroup (ModGL TwistTag.E6.tag L)}
    (hYc : ∀ x ∈ X6 L Fr w0, ∀ y ∈ X6 L Fr w0, x * y * x⁻¹ * y⁻¹ ∈ Y)
    (i : Fin TwistTag.E6.tag.rank) {t : Lˣ} (ht : t ^ 3 = 1) :
    torusElt TwistTag.E6.tag L i t ∈ Y := by
  have hu : t⁻¹ ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq3
    rw [hk, pow_mul, inv_pow, ht, inv_one, one_pow]
  have h := hYc _ (weylElt_mem_X6 Fr w0 i) _ (rootDiagUnit_mulSingle_mem_X6 hFr hw0 i hu)
  rw [comm_weylElt_rootDiagUnit6, inv_inv] at h
  exact h

theorem gz_mem_Y6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq3 : 3 ∣ q + 1) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    {Y : Subgroup (ModGL TwistTag.E6.tag L)}
    (hYc : ∀ x ∈ X6 L Fr w0, ∀ y ∈ X6 L Fr w0, x * y * x⁻¹ * y⁻¹ ∈ Y)
    {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) (z : Fin TwistTag.E6.tag.rank → ZMod 3) :
    gz ζ z ∈ Y := by
  rw [gz_eq_prod_torusElt hζ]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  refine torusElt_mem_Y6 hFr hq3 hw0 hYc j ?_
  rw [← pow_mul, mul_comm, pow_mul, (mem_rootsOfUnity 3 _).1 ζ.2, one_pow]


section YCount

variable {τ : Tag}

theorem card_fixed_le_mul_card_Tor3Y {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3)
    [Finite (Tor3 τ L)] {n : ℕ} (hn : (kerC τ).card ≤ n) (Y : Subgroup (ModGL τ L))
    (hY : ∀ z, gz ζ z ∈ Y) {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L) :
    (fixed3 τ.cartan (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩))).card ≤
      n * Nat.card ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
  classical
  have hfin : Finite ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans inf_le_left :
      Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L)) ≤ Tor3 τ L))
      (Subgroup.inclusion_injective _)
  set S := fixed3 τ.cartan (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩)) with hS
  have hfib : ∀ a ∈ S.image (gz (τ := τ) (L := L) ζ),
      (S.filter fun x => gz (τ := τ) (L := L) ζ x = a).card ≤ n := by
    intro a ha
    obtain ⟨z0, -, rfl⟩ := Finset.mem_image.1 ha
    refine le_trans (Finset.card_le_card_of_injOn (fun x => x - z0) (fun x hx => ?_)
      (fun x _ y _ hxy => sub_left_inj.1 hxy)) hn
    exact gz_eq_imp hζ (Finset.mem_filter.1 hx).2
  have h1 := Finset.card_le_mul_card_image S n hfib
  have h2 : (S.image (gz (τ := τ) (L := L) ζ)).card ≤
      Nat.card ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
    let ι : ↥(S.image (gz (τ := τ) (L := L) ζ)) →
        ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := fun a =>
      ⟨a.1, by
        obtain ⟨z, hzS, hz⟩ := Finset.mem_image.1 a.2
        rw [← hz]
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨gz_mem_Tor3 hζ z, hY z⟩,
          Subgroup.mem_centralizer_singleton_iff.2 (gz_commute hζ hs hzS).symm⟩⟩
    have hι : Function.Injective ι := by
      intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this
    have := Nat.card_le_card_of_injective ι hι
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  exact h1.trans (Nat.mul_le_mul_left n h2)

theorem card_Tor3Y_inf_centralizer_ge {m n : ℕ}
    (hW : ∀ p : WeylGroup τ, p ^ 3 = 1 → ∃ g : WeylGroup τ,
      m ≤ (fixed3 τ.cartan (weylMatrix (g⁻¹ * p * g))).card)
    {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) [Finite (Tor3 τ L)] (hn : (kerC τ).card ≤ n)
    (Y : Subgroup (ModGL τ L)) (hY : ∀ z, gz ζ z ∈ Y)
    (hYn : ∀ g : WeylGroup τ, ∀ y ∈ Y,
      canonicalRep (coxeterSystem τ) L g * y * (canonicalRep (coxeterSystem τ) L g)⁻¹ ∈ Y)
    {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L) (hs3 : s ^ 3 = 1) :
    m ≤ n * Nat.card ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
  have hp3 : weylQuotientHom τ L ⟨s, hs⟩ ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one (weylQuotientHom τ L)
    exact Subtype.ext hs3
  obtain ⟨g, hg⟩ := hW _ hp3
  set n₀ : ModGL τ L := canonicalRep (coxeterSystem τ) L g with hn₀
  have hnm : n₀ ∈ monomialSubgroup τ L :=
    Subgroup.mem_sup_right (canonicalRep_mem_closure _ L g)
  have hπ : weylQuotientHom τ L ⟨n₀, hnm⟩ = g := weylQuotientHom_eq (mapsRootLines_canonicalRep g)
  have hs'm : n₀⁻¹ * s * n₀ ∈ monomialSubgroup τ L := mul_mem (mul_mem (inv_mem hnm) hs) hnm
  have hs'π : weylQuotientHom τ L ⟨n₀⁻¹ * s * n₀, hs'm⟩ =
      g⁻¹ * weylQuotientHom τ L ⟨s, hs⟩ * g := by
    have : (⟨n₀⁻¹ * s * n₀, hs'm⟩ : monomialSubgroup τ L) =
        ⟨n₀, hnm⟩⁻¹ * ⟨s, hs⟩ * ⟨n₀, hnm⟩ := rfl
    rw [this, map_mul, map_mul, map_inv, hπ]
  have h1 := card_fixed_le_mul_card_Tor3Y hζ hn Y hY hs'm
  rw [hs'π] at h1
  refine (hg.trans h1).trans (Nat.mul_le_mul_left n ?_)
  have : Finite ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans inf_le_left :
      Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L)) ≤ Tor3 τ L))
      (Subgroup.inclusion_injective _)
  let φ : ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({n₀⁻¹ * s * n₀} : Set (ModGL τ L))) →
      ↥(Tor3 τ L ⊓ Y ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := fun x =>
    ⟨n₀ * x.1 * n₀⁻¹, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨
      canonicalRep_conj_Tor3_mem g (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 x.2).1).1,
      hYn g _ (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 x.2).1).2⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (by
        have hx := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
        calc n₀ * x.1 * n₀⁻¹ * s = n₀ * (x.1 * (n₀⁻¹ * s * n₀)) * n₀⁻¹ := by group
          _ = n₀ * ((n₀⁻¹ * s * n₀) * x.1) * n₀⁻¹ := by rw [hx]
          _ = s * (n₀ * x.1 * n₀⁻¹) := by group)⟩⟩
  have hφ : Function.Injective φ := by
    intro x y h
    have := congrArg Subtype.val h
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  exact Nat.card_le_card_of_injective φ hφ

end YCount


section X6Final

variable {τ : Tag}

theorem Tor3_le_E3 : Tor3 τ L ≤ E3 τ L := by
  intro x hx
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1
  have h3 : a ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := τ) (K := L)
    have := hx.2
    change rootDiagUnitHom τ L a ^ 3 = 1 at this
    rw [← map_pow] at this
    exact this.trans (map_one (rootDiagUnitHom τ L)).symm
  exact ⟨fun i => ⟨a i, (mem_rootsOfUnity 3 _).2 (congrFun h3 i)⟩, rfl⟩

theorem finite_Tor3_of_alg [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) : Finite (Tor3 τ L) := by
  have hc : Nat.card (rootsOfUnity 3 L) = 3 := card_rootsOfUnity_alg' h3
  have := finite_E3 (τ := τ) hc
  exact Finite.of_injective (fun x : Tor3 τ L => (⟨x.1, Tor3_le_E3 x.2⟩ : E3 τ L))
    (by
      intro x y h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this)

theorem exists_cube_root_alg [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) :
    ∃ ζ : rootsOfUnity 3 L, orderOf ζ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (rootsOfUnity 3 L) = 3 := card_rootsOfUnity_alg' h3
  exact exists_prime_orderOf_dvd_card' (G := rootsOfUnity 3 L) 3 (by rw [hc])


theorem E3_le_X6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq3 : 3 ∣ q + 1) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u) :
    E3 TwistTag.E6.tag L ≤ X6 L Fr w0 := by
  rintro _ ⟨f, rfl⟩
  refine twistedTorus_le_X6 Fr w0 ?_
  rw [twistedTorus6_eq Fr hw0]
  refine ⟨fun i => (f i : Lˣ), ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedCharTuples_neg_iff hFr]
  intro i
  obtain ⟨k, hk⟩ := hq3
  rw [hk, pow_mul, (mem_rootsOfUnity 3 _).1 (f i).2, one_pow]

theorem exists_three_subgroup_X6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq3 : 3 ∣ q + 1) (h3 : ((3 : ℕ) : L) ≠ 0)
    {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    (Y : Subgroup (ModGL TwistTag.E6.tag L))
    (hYc : ∀ x ∈ X6 L Fr w0, ∀ y ∈ X6 L Fr w0, x * y * x⁻¹ * y⁻¹ ∈ Y)
    (hYn : ∀ x ∈ X6 L Fr w0, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    {s : ModGL TwistTag.E6.tag L} (hsY : s ∈ Y) (hsX : s ∈ X6 L Fr w0) (hs3 : s ^ 3 = 1) :
    ∃ B : Subgroup (ModGL TwistTag.E6.tag L), B ≤ Y ⊓ X6 L Fr w0 ∧
      B ≤ Subgroup.centralizer ({s} : Set (ModGL TwistTag.E6.tag L)) ∧ Finite B ∧
      (∀ x ∈ B, x ^ 3 = 1) ∧ 81 ≤ Nat.card B := by
  have hfin : Finite (Tor3 TwistTag.E6.tag L) := finite_Tor3_of_alg h3
  have hfinY : Finite ↥(Tor3 TwistTag.E6.tag L ⊓ Y) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : Tor3 TwistTag.E6.tag L ⊓ Y ≤ _))
      (Subgroup.inclusion_injective _)
  obtain ⟨ζ, hζ⟩ := exists_cube_root_alg (L := L) h3
  have hY : ∀ z, gz ζ z ∈ Y := fun z => gz_mem_Y6 hFr hq3 hw0 hYc hζ z
  have hYnorm : ∀ g : WeylGroup TwistTag.E6.tag, ∀ y ∈ Y,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L g * y *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L g)⁻¹ ∈ Y := fun g y hy =>
    hYn _ (tits6_le_X6 Fr w0 (canonicalRep_mem_tits6 g)) y hy
  have hker : (kerC TwistTag.E6.tag).card ≤ 3 := kerC_E6_card
  have hW : ∀ p : WeylGroup TwistTag.E6.tag, p ^ 3 = 1 → ∃ g : WeylGroup TwistTag.E6.tag,
      81 ≤ (fixed3 TwistTag.E6.tag.cartan (weylMatrix (g⁻¹ * p * g))).card :=
    fun p hp => exists_conj_fixed3_E6 p hp
  have hsm : s ∈ monomialSubgroup TwistTag.E6.tag L := X6_le_monomial Fr w0 hsX
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := exists_three_subgroup_centralizer (Tor3 TwistTag.E6.tag L ⊓ Y)
    (fun a ha b hb => Tor3_comm ha.1 hb.1) (fun a ha => Tor3_cube ha.1) hs3
  refine ⟨B, ?_, hB2, hB3, hB4, ?_⟩
  · refine hB1.trans (sup_le ?_ ?_)
    · intro x hx
      exact ⟨hx.2, E3_le_X6 hFr hq3 hw0 (Tor3_le_E3 hx.1)⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hsY, hsX⟩
  · rcases hB5 with ⟨-, rfl⟩ | ⟨-, hcard⟩
    · have h1 := card_fixed_le_mul_card_Tor3Y hζ hker Y hY (one_mem (monomialSubgroup _ L))
      have hq : weylQuotientHom TwistTag.E6.tag L ⟨(1 : ModGL TwistTag.E6.tag L), one_mem _⟩ = 1 :=
        map_one _
      rw [hq, weylMatrix_one] at h1
      have hfix : fixed3 TwistTag.E6.tag.cartan
          (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) =
          Finset.univ := by
        refine Finset.eq_univ_of_forall fun z =>
          Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
        simp
      rw [hfix, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
      have h2 : Nat.card ↥(Tor3 TwistTag.E6.tag L ⊓ Y ⊓
          Subgroup.centralizer ({(1 : ModGL TwistTag.E6.tag L)} : Set _)) ≤
          Nat.card ↥(Tor3 TwistTag.E6.tag L ⊓ Y) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective inf_le_left)
      have h6 : 3 ^ TwistTag.E6.tag.rank = 729 := by decide
      omega
    · have := card_Tor3Y_inf_centralizer_ge hW hζ hker Y hY hYnorm hsm hs3
      omega

end X6Final

end TwCount

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
