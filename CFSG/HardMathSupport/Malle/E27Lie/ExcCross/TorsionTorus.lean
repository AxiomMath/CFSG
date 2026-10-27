module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TorsionFixed

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6

section TorTorus

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L]

theorem torusGroup_comm {x y : ModGL τ L} (hx : x ∈ torusGroup τ L) (hy : y ∈ torusGroup τ L) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

variable (τ L) in
@[expose] def Tor3 : Subgroup (ModGL τ L) where
  carrier := {x | x ∈ torusGroup τ L ∧ x ^ 3 = 1}
  mul_mem' := fun {x y} hx hy => by
    have hc : Commute x y := torusGroup_comm hx.1 hy.1
    exact ⟨mul_mem hx.1 hy.1, by rw [hc.mul_pow, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 3⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem Tor3_comm {x y : ModGL τ L} (hx : x ∈ Tor3 τ L) (hy : y ∈ Tor3 τ L) : x * y = y * x :=
  torusGroup_comm hx.1 hy.1

theorem Tor3_cube {x : ModGL τ L} (hx : x ∈ Tor3 τ L) : x ^ 3 = 1 := hx.2

theorem canonicalRep_conj_Tor3_mem (g : WeylGroup τ) {x : ModGL τ L} (hx : x ∈ Tor3 τ L) :
    canonicalRep (coxeterSystem τ) L g * x * (canonicalRep (coxeterSystem τ) L g)⁻¹ ∈
      Tor3 τ L := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer g) x).1 hx.1, ?_⟩
  have : (canonicalRep (coxeterSystem τ) L g * x * (canonicalRep (coxeterSystem τ) L g)⁻¹) ^ 3 =
      canonicalRep (coxeterSystem τ) L g * x ^ 3 * (canonicalRep (coxeterSystem τ) L g)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [this, hx.2]; group

variable (τ) in
@[expose] def cartanT (z : Fin τ.rank → ZMod 3) : Fin τ.rank → ZMod 3 :=
  fun j => ∑ i, z i * ((τ.cartan i j : ℤ) : ZMod 3)

theorem cartanT_sub (z z' : Fin τ.rank → ZMod 3) :
    cartanT τ (z - z') = cartanT τ z - cartanT τ z' := by
  funext j
  simp only [cartanT, Pi.sub_apply, sub_mul]
  exact Finset.sum_sub_distrib _ _

variable (τ) in
@[expose] def kerC : Finset (Fin τ.rank → ZMod 3) :=
  Finset.univ.filter fun z => cartanT τ z = 0

@[expose] def gz (ζ : rootsOfUnity 3 L) (z : Fin τ.rank → ZMod 3) : ModGL τ L :=
  psi3 τ L (fz τ ζ (cartanT τ z))

theorem pow_val_sum_eq_prod {ι : Type} [Fintype ι] {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (z : ι → ZMod 3) (c : ι → ℤ) :
    ζ ^ (∑ i, z i * (c i : ZMod 3)).val = ∏ i, (ζ ^ (z i).val) ^ c i := by
  have h1 : ∏ i, (ζ ^ (z i).val) ^ c i = ζ ^ ∑ i, (((z i).val : ℤ) * c i) := by
    rw [← prodZpowSum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  rw [h1, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hζ]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem gz_eq_prod_torusElt {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3)
    (z : Fin τ.rank → ZMod 3) :
    gz ζ z = ((List.finRange τ.rank).map fun j =>
      torusElt τ L j ((ζ : Lˣ) ^ (z j).val)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, gz, psi3_apply]
  congr 1
  funext j
  simp only [cartanChar, fz, Subgroup.coe_pow]
  exact pow_val_sum_eq_prod (by rw [← Subgroup.orderOf_coe ζ] at hζ; exact hζ) z
    (fun i => τ.cartan i j)

theorem gz_mem_torusGroup {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3)
    (z : Fin τ.rank → ZMod 3) : gz ζ z ∈ torusGroup τ L := by
  rw [gz_eq_prod_torusElt hζ]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup _ _

theorem gz_mem_Tor3 {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) (z : Fin τ.rank → ZMod 3) :
    gz ζ z ∈ Tor3 τ L := by
  have hmem : gz ζ z ∈ E3 τ L := ⟨_, rfl⟩
  exact ⟨gz_mem_torusGroup hζ z, E3_cube hmem⟩

theorem cartanT_mem_fixed3 {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L)
    {z : Fin τ.rank → ZMod 3}
    (hz : z ∈ fixed3 τ.cartan (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩))) :
    cartanT τ z ∈ fixed3 (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
      (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩)) := by
  set M := weylMatrix (weylQuotientHom τ L ⟨s, hs⟩) with hM
  have hz' := (Finset.mem_filter.1 hz).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
  have h := hz' j
  simp only [Matrix.one_mul]
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul] at h
  simp only [cartanT, Finset.sum_mul, Finset.mul_sum] at h ⊢
  rw [Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gz_commute {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) {s : ModGL τ L}
    (hs : s ∈ monomialSubgroup τ L) {z : Fin τ.rank → ZMod 3}
    (hz : z ∈ fixed3 τ.cartan (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩))) :
    s * gz ζ z = gz ζ z * s :=
  psi3_fz_commute hζ hs (cartanT_mem_fixed3 hs hz)

theorem gz_eq_imp {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) {z z' : Fin τ.rank → ZMod 3}
    (h : gz ζ z = gz ζ z') : z - z' ∈ kerC τ := by
  have h1 := fz_injective hζ (psi3_injective h)
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  rw [cartanT_sub, h1, sub_self]


theorem card_fixed_le_mul_card_Tor3 {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3)
    [Finite (Tor3 τ L)] {n : ℕ} (hn : (kerC τ).card ≤ n) {s : ModGL τ L}
    (hs : s ∈ monomialSubgroup τ L) :
    (fixed3 τ.cartan (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩))).card ≤
      n * Nat.card ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
  classical
  have hfin : Finite ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : Tor3 τ L ⊓ _ ≤ Tor3 τ L))
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
      Nat.card ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
    let ι : ↥(S.image (gz (τ := τ) (L := L) ζ)) →
        ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := fun a =>
      ⟨a.1, by
        obtain ⟨z, hzS, hz⟩ := Finset.mem_image.1 a.2
        rw [← hz]
        exact Subgroup.mem_inf.2 ⟨gz_mem_Tor3 hζ z,
          Subgroup.mem_centralizer_singleton_iff.2 (gz_commute hζ hs hzS).symm⟩⟩
    have hι : Function.Injective ι := by
      intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this
    have := Nat.card_le_card_of_injective ι hι
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  exact h1.trans (Nat.mul_le_mul_left n h2)


theorem card_Tor3_inf_centralizer_ge {m n : ℕ}
    (hW : ∀ p : WeylGroup τ, p ^ 3 = 1 → ∃ g : WeylGroup τ,
      m ≤ (fixed3 τ.cartan (weylMatrix (g⁻¹ * p * g))).card)
    {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) [Finite (Tor3 τ L)] (hn : (kerC τ).card ≤ n)
    {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L) (hs3 : s ^ 3 = 1) :
    m ≤ n * Nat.card ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := by
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
  have h1 := card_fixed_le_mul_card_Tor3 hζ hn hs'm
  rw [hs'π] at h1
  refine (hg.trans h1).trans (Nat.mul_le_mul_left n ?_)
  have : Finite ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : Tor3 τ L ⊓ _ ≤ Tor3 τ L))
      (Subgroup.inclusion_injective _)
  let φ : ↥(Tor3 τ L ⊓ Subgroup.centralizer ({n₀⁻¹ * s * n₀} : Set (ModGL τ L))) →
      ↥(Tor3 τ L ⊓ Subgroup.centralizer ({s} : Set (ModGL τ L))) := fun x =>
    ⟨n₀ * x.1 * n₀⁻¹, Subgroup.mem_inf.2 ⟨
      canonicalRep_conj_Tor3_mem g (Subgroup.mem_inf.1 x.2).1,
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

theorem card_Tor3_ge {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) [Finite (Tor3 τ L)] {n : ℕ}
    (hn : (kerC τ).card ≤ n) : 3 ^ τ.rank ≤ n * Nat.card (Tor3 τ L) := by
  have h1 := card_fixed_le_mul_card_Tor3 hζ hn (one_mem (monomialSubgroup τ L))
  have hq : weylQuotientHom τ L ⟨(1 : ModGL τ L), one_mem _⟩ = 1 := map_one _
  rw [hq, weylMatrix_one] at h1
  have hfix : fixed3 τ.cartan (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun z => Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
    simp
  rw [hfix, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
  refine h1.trans (Nat.mul_le_mul_left n ?_)
  exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective
    (inf_le_left : Tor3 τ L ⊓ Subgroup.centralizer ({(1 : ModGL τ L)} : Set (ModGL τ L)) ≤ Tor3 τ L))

theorem exists_three_subgroup_Tor3 (hker : (kerC τ).card ≤ 3) (hr : 5 ≤ τ.rank)
    (hW : ∀ p : WeylGroup τ, p ^ 3 = 1 → ∃ g : WeylGroup τ,
      81 ≤ (fixed3 τ.cartan (weylMatrix (g⁻¹ * p * g))).card)
    {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) [Finite (Tor3 τ L)]
    {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L) (hs3 : s ^ 3 = 1) :
    ∃ B : Subgroup (ModGL τ L), B ≤ Tor3 τ L ⊔ Subgroup.zpowers s ∧
      B ≤ Subgroup.centralizer ({s} : Set (ModGL τ L)) ∧ Finite B ∧ (∀ x ∈ B, x ^ 3 = 1) ∧
      81 ≤ Nat.card B := by
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := exists_three_subgroup_centralizer (Tor3 τ L)
    (fun a ha b hb => Tor3_comm ha hb) (fun a ha => Tor3_cube ha) hs3
  refine ⟨B, hB1, hB2, hB3, hB4, ?_⟩
  rcases hB5 with ⟨-, rfl⟩ | ⟨-, hcard⟩
  · have h := card_Tor3_ge hζ hker
    have h5 : 3 ^ 5 ≤ 3 ^ τ.rank := Nat.pow_le_pow_right (by norm_num) hr
    omega
  · have := card_Tor3_inf_centralizer_ge hW hζ hker hs hs3
    omega

end TorTorus

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
