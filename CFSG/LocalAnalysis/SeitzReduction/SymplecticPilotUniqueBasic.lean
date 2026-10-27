module

public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangian
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotEndField
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spMat displacement mem_displacement
  spMat_mul_mulVec spMat_inv_mulVec_mulVec pairedSympForm_spMat isTotallyIsotropic_displacement
  displacement_eq_zero_of_mem_orthogonal)
open CFSG.RankThree.Classical (siegelRadicalSp siegelSpHom mem_siegelRadicalSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Siegel

variable {r : ℕ} {F : Type} [Field F]

theorem isoFlag_le_isoFlag_rank (d : ℕ) : isoFlag r F d ≤ isoFlag r F r := by
  intro v hv
  obtain ⟨h1, -⟩ := mem_isoFlag.mp hv
  exact mem_isoFlag.mpr ⟨h1, fun j hj => absurd j.2 (not_lt.mpr hj)⟩

theorem commute_of_mem_siegelRadicalSp {x y : StatedSp r F} (hx : x ∈ siegelRadicalSp r F)
    (hy : y ∈ siegelRadicalSp r F) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem exists_inv_mul_mul_mem_siegelRadicalSp [CharP F 2] {s : StatedSp r F} (hs : s * s = 1) :
    ∃ g : StatedSp r F, g⁻¹ * s * g ∈ siegelRadicalSp r F := by
  set W := displacement s with hWdef
  have hW : IsTotallyIsotropic (pairedSympForm F r) W := isTotallyIsotropic_displacement hs
  have hd : Module.finrank F W ≤ r := finrank_le_of_isTotallyIsotropic
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    SymplecticFlag.finrank_standard hW
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq
    (SymplecticHigher.isTotallyIsotropic_isoFlag (K := F) (r := r) (Module.finrank F W)) hW
    (SymplecticHigher.finrank_isoFlag hd)
  refine ⟨g, ?_⟩
  set s₁ := g⁻¹ * s * g with hs₁
  have hfix : ∀ x ∈ isoFlag r F r, spMat s₁ *ᵥ x = x := by
    intro x hx
    have hgx : spMat g *ᵥ x ∈ (pairedSympForm F r).orthogonal W := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [← hg] at hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      change pairedSympForm F r (spMat g *ᵥ y) (spMat g *ᵥ x) = 0
      rw [pairedSympForm_spMat]
      exact SymplecticHigher.isTotallyIsotropic_isoFlag r y (isoFlag_le_isoFlag_rank _ hy) x hx
    have h0 := displacement_eq_zero_of_mem_orthogonal hs hgx
    rw [hs₁, spMat_mul_mulVec, spMat_mul_mulVec, sub_eq_zero.mp h0, spMat_inv_mulVec_mulVec]
  have hdisp : ∀ v, spMat s₁ *ᵥ v - v ∈ isoFlag r F r := by
    intro v
    have h1 : spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v ∈ W :=
      mem_displacement.mpr ⟨_, rfl⟩
    rw [← hg] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp h1
    have hwe' : w = spMat s₁ *ᵥ v - v := by
      have h2 := congrArg (spMat g⁻¹ *ᵥ ·) hwe
      simp only [Matrix.mulVecLin_apply, spMat_inv_mulVec_mulVec] at h2
      rw [h2, hs₁, Matrix.mulVec_sub, spMat_mul_mulVec, spMat_mul_mulVec,
        spMat_inv_mulVec_mulVec]
    rw [← hwe']
    exact isoFlag_le_isoFlag_rank _ hw
  set S := (spMat s₁).toBlocks₁₂ with hSdef
  have hblock : spMat s₁ = fromBlocks 1 S 0 1 := by
    have hcol : ∀ j k, spMat s₁ k j = (spMat s₁ *ᵥ Pi.single j 1) k := fun j k => by
      rw [mulVec_single_one]
      rfl
    have hsingle : ∀ j : Fin r, (Pi.single (Sum.inl j) 1 : Fin r ⊕ Fin r → F) ∈ isoFlag r F r :=
      fun j => mem_isoFlag.mpr ⟨fun i => by simp, fun i hi => absurd i.2 (not_lt.mpr hi)⟩
    ext (i | i) (j | j)
    · rw [hcol, hfix _ (hsingle j)]
      simp [Matrix.one_apply, Pi.single_apply]
    · rfl
    · rw [hcol, hfix _ (hsingle j)]
      simp
    · have h := (mem_isoFlag.mp (hdisp (Pi.single (Sum.inr j) 1))).1 i
      rw [Pi.sub_apply, ← hcol, sub_eq_zero] at h
      rw [h]
      simp [Matrix.one_apply, Pi.single_apply]
  have hS : Sᵀ = S := by
    have h := SymplecticTorusWeyl.mem_statedSp_iff.mp s₁.2
    change (spMat s₁)ᵀ * fromBlocks 0 1 (-1) 0 * spMat s₁ = fromBlocks 0 1 (-1) 0 at h
    rw [hblock] at h
    exact SymplecticLagrangian.transpose_eq_of_fromBlocks_mem h
  exact mem_siegelRadicalSp.2 ⟨S, hS, hblock⟩

theorem exists_map_conj_siegelRadicalSp_le_centralizer [CharP F 2] {s : StatedSp r F}
    (hs : s * s = 1) : ∃ g : StatedSp r F,
      (siegelRadicalSp r F).map (MulAut.conj g).toMonoidHom ≤
        centralizer ({s} : Set (StatedSp r F)) := by
  obtain ⟨g, hg⟩ := exists_inv_mul_mul_mem_siegelRadicalSp hs
  refine ⟨g, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hc := commute_of_mem_siegelRadicalSp hu hg
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * u * g⁻¹ * s = g * (u * (g⁻¹ * s * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * s * g) * u) * g⁻¹ := by rw [hc]
    _ = s * (g * u * g⁻¹) := by group

theorem pow_dvd_card_centralizer_statedSp [Finite F] [CharP F 2] {s : StatedSp r F}
    (hs : s * s = 1) :
    Nat.card F ^ (r * (r + 1) / 2) ∣ Nat.card (centralizer ({s} : Set (StatedSp r F))) := by
  obtain ⟨g, hg⟩ := exists_map_conj_siegelRadicalSp_le_centralizer hs
  have := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hR := (CFSG.RankThree.Classical.siegel_radical_sp Nat.prime_two hF r).2
  rw [← hF] at hR
  rw [← hR, ← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  exact Subgroup.card_dvd_of_le hg

end Siegel

section TwoParts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem gcd_two_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Nat.gcd 2 (2 ^ f - 1) = 1 := by
  refine Nat.coprime_two_left.2 ?_
  obtain ⟨r, rfl⟩ : ∃ r, f = r + 1 := ⟨f - 1, by omega⟩
  refine ⟨2 ^ r - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem factorization_card_statedSp {n f : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    (Nat.card (StatedSp n K)).factorization 2 = f * n ^ 2 := by
  obtain ⟨m, hm, hSp⟩ :=
    CFSG.ComponentClassification.SymmetricLocal.card_statedSp_eq_two_pow_mul_odd hK hf hn
  rw [hSp, Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)), add_zero]

theorem factorization_card_le_of_le_centralizer_sp (hL : CFSG.Open.standardComponentIsStandard L)
    {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) :
    (Nat.card X).factorization 2 ≤ f * n ^ 2 + 1 + f.factorization 2 := by
  have : NeZero n := ⟨by omega⟩
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have h1 := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer hL
    (e.trans (F4Pilot.spProjEquiv n K)) ht hKt hXt
  have h2 := E6Pilot.card_mulAut_dvd_card_mul_card_outer (StatedProj (StatedSp n K))
  have h3 := (SymplecticHigher.outer_card_dvd Nat.prime_two hf hK (by omega)).2 hn
  rw [gcd_two_two_pow_sub_one hf, mul_one] at h3
  have hP : Nat.card (StatedProj (StatedSp n K)) = Nat.card (StatedSp n K) :=
    (Nat.card_congr (F4Pilot.spProjEquiv n K).toEquiv).symm
  have h4 : Nat.card X ∣ 2 * (Nat.card (StatedProj (StatedSp n K)) * f) :=
    h1.trans (Nat.mul_dvd_mul_left 2 (h2.trans (Nat.mul_dvd_mul_left _ h3)))
  have hP0 : Nat.card (StatedProj (StatedSp n K)) ≠ 0 := by
    rw [hP]
    exact Nat.card_pos.ne'
  have hf0 : f ≠ 0 := by omega
  have hN0 : Nat.card (StatedProj (StatedSp n K)) * f ≠ 0 := mul_ne_zero hP0 hf0
  have h5 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (mul_ne_zero two_ne_zero hN0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hN0, Finsupp.add_apply, Nat.factorization_mul hP0 hf0,
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, hP,
    factorization_card_statedSp (by omega) hK hf] at h5
  omega

end TwoParts

section Outer

theorem isPerfect_statedSp_of_charTwo {k : Type} [Field k] [Finite k] [CharP k 2] {r : ℕ}
    (hr : 3 ≤ r) : Group.IsPerfect (StatedSp r k) := by
  obtain ⟨g, hg, hk⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have h : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
      (Nat.card k = 2 ∧ 3 ≤ r) := by
    rcases Nat.lt_or_ge g 2 with h | h
    · right
      right
      refine ⟨?_, hr⟩
      rw [hk, show g = 1 by omega]
      norm_num
    · left
      right
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) h
  have : Group.IsPerfect (TauCeti.GLSymplecticFin r k) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin k r h
  let e : TauCeti.GLSymplecticFin r k ≃* StatedSp r k :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic r k).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := r) (K := k)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

variable {r : ℕ} {K : Type} [Field K]

theorem conj_mul_fieldSp_sq (s : StatedSp r K) (ρ : K ≃+* K) :
    MulAut.conj s * SymplecticHigher.fieldSp r K ρ *
        (MulAut.conj s * SymplecticHigher.fieldSp r K ρ) =
      MulAut.conj (s * SymplecticHigher.fieldSp r K ρ s) *
        SymplecticHigher.fieldSp r K (ρ * ρ) := by
  rw [map_mul (SymplecticHigher.fieldSp r K) ρ ρ]
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]

theorem exists_eq_conj_fieldSp_of_not_inner [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {β : MulAut (StatedSp r K)} (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range) :
    ∃ σ : K ≃+* K, orderOf σ = 2 ∧ ∃ h : StatedSp r K,
      β = MulAut.conj h * SymplecticHigher.fieldSp r K σ * (MulAut.conj h)⁻¹ := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨s, ρ, rfl⟩ := exists_eq_conj_mul_fieldSp hr β
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact hβi ⟨s, by rw [map_one, mul_one]⟩
  have hρ2 : ρ * ρ = 1 := by
    rw [conj_mul_fieldSp_sq] at hβ
    have h2 : SymplecticHigher.fieldSp r K (ρ * ρ) =
        MulAut.conj (s * SymplecticHigher.fieldSp r K ρ s)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hβ
    exact F4Pilot.eq_one_of_fieldSp_eq_one
      (fieldSp_eq_one_of_mem_range_conj (by omega) ⟨_, h2.symm⟩)
  have hσ : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq, hρ2]) hρ1
  exact ⟨ρ, hσ, F4Pilot.exists_eq_conj_mul_fieldSp_mul_conj_inv hr hσ hβ hβi⟩

end Outer

section OuterFixed

variable {r : ℕ} {K : Type} [Field K]

theorem fixedSubgroup_conj_eq_map {X : Type*} [Group X] (c β : MulAut X) :
    fixedSubgroup (c * β * c⁻¹) = (fixedSubgroup β).map c.toMonoidHom := by
  ext x
  rw [mem_map_equiv]
  change (c * β * c⁻¹) x = x ↔ β (c.symm x) = c.symm x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
  constructor
  · intro h
    have h1 := congrArg c.symm h
    rwa [MulEquiv.symm_apply_apply] at h1
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem exists_subfield_of_not_inner [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {β : MulAut (StatedSp r K)} (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range) :
    ∃ k : Subfield K, Nat.card k ^ 2 = Nat.card K ∧
      Nat.card (fixedSubgroup β) = Nat.card (StatedSp r k) ∧
      ⁅fixedSubgroup β, fixedSubgroup β⁆ = fixedSubgroup β := by
  obtain ⟨σ, hσ, h, rfl⟩ := exists_eq_conj_fieldSp_of_not_inner hr hβ hβi
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  obtain ⟨hfe, -, hk⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringEquiv_involution_facts hf hK
      hσσ hσ1
  set k := CFSG.ComponentClassification.UnbalancedCatalog.descentField σ with hkdef
  have : CharP k 2 := (k.subtype).charP k.subtype_injective 2
  have hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range (k.subtype) := fun x => by
    rw [← CFSG.ComponentClassification.UnbalancedCatalog.mem_descentField]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hfixσ : fixedSubgroup (SymplecticHigher.fieldSp r K σ) =
      (F4Pilot.statedSpMap k.subtype r).range :=
    F4Pilot.eqLocus_fieldSp_eq_range k.subtype hfix
  have hmap : fixedSubgroup (MulAut.conj h * SymplecticHigher.fieldSp r K σ * (MulAut.conj h)⁻¹) =
      ((F4Pilot.statedSpMap k.subtype r).range).map (MulAut.conj h).toMonoidHom := by
    rw [fixedSubgroup_conj_eq_map, hfixσ]
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hk, hK, ← pow_mul]
    congr 1
    obtain ⟨m, hm⟩ := hfe
    omega
  · rw [hmap, Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (F4Pilot.statedSpMap_injective _ r), Subgroup.card_top]
  · have : Group.IsPerfect (StatedSp r k) := isPerfect_statedSp_of_charTwo hr
    rw [hmap, ← map_commutator, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]

end OuterFixed

theorem not_sq_card_statedSp_dvd {k K : Type} [Field k] [Field K] [Finite k] [Finite K] {r e : ℕ}
    (hr : 1 ≤ r) (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = Nat.card k ^ 2) :
    ¬ Nat.card (StatedSp r k) ^ 2 ∣ Nat.card (StatedSp r K) := by
  intro hdvd
  rw [SymplecticFlag.card_statedSp, SymplecticFlag.card_statedSp, hK] at hdvd
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  generalize Nat.card k = x at hdvd hk hk2
  have hx1 : 1 ≤ x := by omega
  have hpow1 : ∀ j, 1 ≤ x ^ j := fun j => Nat.one_le_pow _ _ hx1
  have hfac : ∀ j, (x ^ 2) ^ (2 * j) - 1 = (x ^ (2 * j) - 1) * (x ^ (2 * j) + 1) := by
    intro j
    have h1 := hpow1 (2 * j)
    zify [h1, Nat.one_le_pow (2 * j) (x ^ 2) (hpow1 2)]
    ring
  set D := ∏ j ∈ Finset.Icc 1 r, (x ^ (2 * j) - 1) with hD
  set E := ∏ j ∈ Finset.Icc 1 r, (x ^ (2 * j) + 1) with hE
  have hSpK : (x ^ 2) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((x ^ 2) ^ (2 * j) - 1) =
      (x ^ (r ^ 2) * D) * (x ^ (r ^ 2) * E) := by
    rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_mul_distrib, ← hD, ← hE]
    ring
  rw [hSpK, sq] at hdvd
  have hD0 : 0 < D := Finset.prod_pos fun j hj => by
    have h2 : 2 ≤ x ^ (2 * j) :=
      calc 2 ≤ x := hk2
        _ = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ (2 * j) := Nat.pow_le_pow_right (by omega) (by simp at hj; omega)
    omega
  have hpos : 0 < x ^ (r ^ 2) * D := Nat.mul_pos (by positivity) hD0
  obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  have hx3 : ((x : ℕ) : ZMod 3) ^ 2 = 1 := by
    rw [hk, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul]
    have : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide
    rw [this, one_pow]
  have hD3 : ((D : ℕ) : ZMod 3) = 0 := by
    rw [hD, Nat.cast_prod]
    refine Finset.prod_eq_zero (i := 1) (by simp [hr]) ?_
    rw [Nat.cast_sub (hpow1 _), Nat.cast_pow, Nat.cast_one, pow_mul, hx3, one_pow, sub_self]
  have hE3 : ((x ^ (r ^ 2) * E : ℕ) : ZMod 3) ^ 2 = 1 := by
    rw [Nat.cast_mul, Nat.cast_pow, hE, Nat.cast_prod, mul_pow, ← pow_mul, mul_comm (r ^ 2) 2,
      pow_mul, hx3, one_pow, one_mul, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, pow_mul, hx3, one_pow]
    decide
  rw [hc, Nat.cast_mul, Nat.cast_mul, hD3, mul_zero, zero_mul] at hE3
  exact absurd hE3 (by decide)

end CFSG.SeitzReduction.SymplecticPilot
