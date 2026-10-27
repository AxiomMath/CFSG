module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import CFSG.Sporadic.Schreier.M11
public import Certificates.Certificate110
public import Certificates.Certificate2191
public import Certificates.Certificate3120
public import Certificates.Certificate4154
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.QuasithinUnique.Unc25M11

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.QuasithinUnique.Unc25Small
  CFSG.Sporadic.Schreier

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

abbrev MG : Type := ↥𝓜

theorem sa_mem : sa ∈ 𝓜 := pw_mem [0, 1, 1, 0, 1, 0, 1, 1]

theorem sb_mem : sb ∈ 𝓜 := pw_mem [0]

@[expose] def ga : MG := ⟨sa, sa_mem⟩

@[expose] def gb : MG := ⟨sb, sb_mem⟩

@[expose] def P0 : Subgroup MG where
  carrier := {x | (x : Equiv.Perm (Fin 11)) ∈ P0L}
  one_mem' := show ((1 : MG) : Equiv.Perm (Fin 11)) ∈ P0L from one_mem_P0L
  mul_mem' := fun {x y} (hx : (x : Equiv.Perm (Fin 11)) ∈ P0L) (hy : (y : Equiv.Perm (Fin 11)) ∈ P0L) =>
    show ((x * y : MG) : Equiv.Perm (Fin 11)) ∈ P0L from mul_mem_P0L _ hx _ hy
  inv_mem' := fun {x} (hx : (x : Equiv.Perm (Fin 11)) ∈ P0L) =>
    show ((x⁻¹ : MG) : Equiv.Perm (Fin 11)) ∈ P0L from inv_mem_P0L _ hx

theorem mem_P0 {x : MG} : x ∈ P0 ↔ (x : Equiv.Perm (Fin 11)) ∈ P0L := Iff.rfl

theorem card_P0 : Nat.card P0 = 16 := by
  have h := card_eq_length (fun x : MG => x ∈ P0) (fun x => (x : Equiv.Perm (Fin 11)))
    Subtype.val_injective P0L P0L_nodup ?_
  · rw [P0L_length] at h
    exact h
  · intro b
    constructor
    · intro hb
      obtain ⟨i, -, j, -, rfl⟩ := mem_P0L_iff.mp hb
      exact ⟨⟨sa ^ i * sb ^ j, Subgroup.mul_mem _ (Subgroup.pow_mem _ sa_mem i)
        (Subgroup.pow_mem _ sb_mem j)⟩,
        mem_P0.mpr hb, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact mem_P0.mp hx

theorem isSylowTwoOf_P0 : IsSylowTwoOf P0 ⊤ := by
  have hcard : Nat.card MG = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold IsSylowTwoOf
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card_P0]; norm_num), ?_⟩
  have hmul := Subgroup.card_mul_index P0
  rw [card_P0, hcard] at hmul
  have h495 : P0.index = 495 := by omega
  have hrel : (P0.subgroupOf ⊤).index = P0.index := Subgroup.relIndex_top_right P0
  rw [hrel, h495]
  decide

@[expose] def a0 : ↥P0 := ⟨ga, mem_P0.mpr sa_mem_P0L⟩

@[expose] def b0 : ↥P0 := ⟨gb, mem_P0.mpr sb_mem_P0L⟩

theorem coe_a0 : (((a0 : ↥P0) : MG) : Equiv.Perm (Fin 11)) = sa := rfl

theorem coe_b0 : (((b0 : ↥P0) : MG) : Equiv.Perm (Fin 11)) = sb := rfl

theorem coe_coe_pow (x : ↥P0) (n : ℕ) :
    ((((x ^ n : ↥P0)) : MG) : Equiv.Perm (Fin 11)) = (((x : MG)) : Equiv.Perm (Fin 11)) ^ n := by
  simp

theorem a0_pow : a0 ^ 8 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_coe_pow, coe_a0]
  exact sa_pow

theorem b0_sq : b0 ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_coe_pow, coe_b0, pow_two]
  exact sb_sq

theorem b0_conj : b0 * a0 * b0⁻¹ = a0 ^ 3 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_coe_pow, coe_a0]
  exact sb_conj

theorem shape_P0 : Nonempty (↥P0 ≃* SemidihedralGroup 4) := by
  have hab : b0 * a0 * b0⁻¹ = a0 ^ (2 ^ (4 - 2) - 1) := by
    rw [show (2 ^ (4 - 2) - 1 : ℕ) = 3 by norm_num]
    exact b0_conj
  have hrels : ∀ r ∈ semidihedralRels 4, FreeGroup.lift ![a0, b0] r = 1 := by
    rintro r (rfl | rfl | rfl)
    · simpa using a0_pow
    · simpa using b0_sq
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hab, mul_inv_cancel]
  let φ : SemidihedralGroup 4 →* ↥P0 := PresentedGroup.toGroup hrels
  have hφ0 : φ (PresentedGroup.of 0) = a0 := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hφ1 : φ (PresentedGroup.of 1) = b0 := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨i, -, j, -, hx⟩ := mem_P0L_iff.mp (mem_P0.mp x.2)
    refine ⟨PresentedGroup.of 0 ^ i * PresentedGroup.of 1 ^ j, ?_⟩
    rw [map_mul, map_pow, map_pow, hφ0, hφ1]
    apply Subtype.ext
    apply Subtype.ext
    show ((((a0 ^ i : ↥P0)) : MG) : Equiv.Perm (Fin 11)) *
      ((((b0 ^ j : ↥P0)) : MG) : Equiv.Perm (Fin 11)) = ((x : MG) : Equiv.Perm (Fin 11))
    rw [coe_coe_pow, coe_coe_pow, coe_a0, coe_b0]
    exact hx.symm
  have : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hle : Nat.card (SemidihedralGroup 4) ≤ Nat.card ↥P0 := by
    simp [CFSG.Semidihedral.card 4 (by norm_num), card_P0]
  exact ⟨(MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hle)).symm⟩

theorem normProp_all :
    ∀ y ∈ 𝓜, NormProp y := fun y hy =>
  of_decide_eq_true (List.all_eq_true.mp normProp_check y ((mem_m11Elements y).mpr hy))

theorem centB_all :
    ∀ y ∈ 𝓜, centB y = true := fun y hy =>
  List.all_eq_true.mp centB_check y ((mem_m11Elements y).mpr hy)

theorem normalizer_le_P0
    : Subgroup.normalizer (P0 : Set MG) ≤ P0 := by
  intro g hg
  have h1 : g * ga * g⁻¹ ∈ P0 :=
    (Subgroup.mem_normalizer_iff.mp hg ga).mp (mem_P0.mpr sa_mem_P0L)
  have h2 : g * gb * g⁻¹ ∈ P0 :=
    (Subgroup.mem_normalizer_iff.mp hg gb).mp (mem_P0.mpr sb_mem_P0L)
  exact mem_P0.mpr (normProp_all g.1 g.2 (mem_P0.mp h1) (mem_P0.mp h2))

theorem mem_normalizer_of_conj_le {X : Type} [Group X] [Finite X] {F : Subgroup X} {w : X}
    (h : ∀ f ∈ F, w * f * w⁻¹ ∈ F) : w ∈ Subgroup.normalizer (F : Set X) := by
  have hle : F.map (MulAut.conj w).toMonoidHom ≤ F := by
    rintro _ ⟨f, hf, rfl⟩
    exact h f hf
  have hcard : Nat.card (F.map (MulAut.conj w).toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  have heq : F.map (MulAut.conj w).toMonoidHom = F :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨h f, fun hf => ?_⟩
  have hf' : w * f * w⁻¹ ∈ F.map (MulAut.conj w).toMonoidHom := by
    rw [heq]
    exact hf
  obtain ⟨f', hf'F, hf'f⟩ := hf'
  have : f' = f := (MulAut.conj w).injective hf'f
  rwa [← this]

theorem four_P0 :
    ∀ F : Subgroup MG, F ≤ P0 → IsFourSubgroup F →
    Subgroup.centralizer (F : Set MG) = F ∧
      ∃ w ∈ Subgroup.normalizer (F : Set MG), orderOf w = 3 := by
  intro F hFP hF
  obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, rfl⟩ := exists_kleinFour_gens hF
  have hmem := Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht hs hc
  have htF : t ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem t).mpr (Or.inr (Or.inl rfl))
  have hsF : s ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have htP : (t : Equiv.Perm (Fin 11)) ∈ P0L := mem_P0.mp (hFP htF)
  have hsP : (s : Equiv.Perm (Fin 11)) ∈ P0L := mem_P0.mp (hFP hsF)
  have hinv : ∀ x : MG, x ≠ 1 → x * x = 1 → (x : Equiv.Perm (Fin 11)) ∈ P0L →
      (x : Equiv.Perm (Fin 11)) ∈ invsP0 := by
    intro x hx1 hx2 hxP
    unfold invsP0
    rw [List.mem_filter]
    refine ⟨hxP, ?_⟩
    rw [decide_eq_true_iff]
    exact ⟨fun h => hx1 (Subtype.ext h), congrArg Subtype.val hx2⟩
  have htI := hinv t ht1 ht htP
  have hsI := hinv s hs1 hs hsP
  have hne : (t : Equiv.Perm (Fin 11)) ≠ s := fun h => hts (Subtype.ext h)
  have hcomm : (t : Equiv.Perm (Fin 11)) * s = s * t := congrArg Subtype.val hc.eq
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro g hg
      have hgt : g * t = t * g := (Subgroup.mem_centralizer_iff.mp hg t htF).symm
      have hgs : g * s = s * g := (Subgroup.mem_centralizer_iff.mp hg s hsF).symm
      have key := centProp_of_centB (centB_all g.1 g.2) _ htI _ hsI (congrArg Subtype.val hgt)
        (congrArg Subtype.val hgs) hne hcomm
      rw [hmem]
      rcases key with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
      · exact Or.inl (Subtype.ext h)
    · intro f hf
      have := hF.1.1
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact setLike_mul_comm hg hf
  · obtain ⟨w, hwW, hw3, hw1, hwt, hws⟩ := W3_check _ htI _ hsI hne hcomm
    obtain ⟨W, hWval⟩ : ∃ W : MG, (W : Equiv.Perm (Fin 11)) = w := ⟨⟨w, W3_mem w hwW⟩, rfl⟩
    rw [← hWval] at hw3 hw1 hwt hws
    have hlist : ∀ x : MG, (x : Equiv.Perm (Fin 11)) ∈
        [1, (t : Equiv.Perm (Fin 11)), (s : Equiv.Perm (Fin 11)),
          (t : Equiv.Perm (Fin 11)) * (s : Equiv.Perm (Fin 11))] →
        x ∈ kleinFourOfCommutingInvolutions t s ht hs hc := by
      intro x hx
      rw [hmem]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
      · exact Or.inl (Subtype.ext h)
    have hWt : W * t * W⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc := hlist _ hwt
    have hWs : W * s * W⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc := hlist _ hws
    have hnorm : W ∈ Subgroup.normalizer
        ((kleinFourOfCommutingInvolutions t s ht hs hc : Subgroup MG) : Set MG) := by
      refine mem_normalizer_of_conj_le fun f hf => ?_
      rw [hmem] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · have : W * (t * s) * W⁻¹ = (W * t * W⁻¹) * (W * s * W⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hWt hWs
      · exact hWt
      · exact hWs
      · rw [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
    have hW3 : W ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    have hW1 : W ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨W, hnorm, orderOf_eq_prime hW3 hW1⟩

theorem sylowFourData_P0 :
    SylowFourData P0 :=
  { sylow := isSylowTwoOf_P0
    shape := Or.inr shape_P0
    normalizer_le := normalizer_le_P0
    four := four_P0 }

theorem mem_innerAut_of_forall {X : Type} [Group X] (φ : MulAut X) (g : X)
    (h : ∀ x, φ x = g * x * g⁻¹) : φ ∈ innerAut X :=
  ⟨g, MulEquiv.ext fun x => by rw [MulAut.conj_apply, h x]⟩

theorem m11G_smallListFacts
    : SmallListFacts MG :=
  { simple := (CFSG.Sporadic.Mathieu.fam_m11_simplicity).2.2
    out_two := fun φ => by
      obtain ⟨g, hg⟩ := Unc25G2.aut_inner φ
      exact ⟨0, by rw [pow_zero, pow_one]; exact mem_innerAut_of_forall φ g hg⟩
    sylow_shape := sylowFourData_P0.sylow_shape
    sylow_normalizer := sylowFourData_P0.sylow_normalizer
    four_normalizer := fun _ hF => sylowFourData_P0.four_normalizer hF
    four_fixes := by
      intro P _ F hFP hF φ hφ y
      obtain ⟨g, hg⟩ := Unc25G2.aut_inner φ
      have hgC : g ∈ Subgroup.centralizer (F : Set MG) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        have h1 := hφ f hf
        rw [hg f] at h1
        calc f * g = (g * f * g⁻¹) * g := by rw [h1]
          _ = g * f := by group
      rw [sylowFourData_P0.centralizer_four hF] at hgC
      have hgP : g ∈ P := hFP hgC
      rw [hg y]
      constructor
      · intro h
        have := P.mul_mem (P.mul_mem (P.inv_mem hgP) h) hgP
        simpa [mul_assoc] using this
      · intro h
        exact P.mul_mem (P.mul_mem hgP h) (P.inv_mem hgP) }

theorem m11G_fixPointwiseInner : FixPointwiseInner MG := by
  intro _ _ α _
  obtain ⟨g, hg⟩ := Unc25G2.aut_inner α
  exact mem_innerAut_of_forall α g hg

theorem m11_facts
    (X : Type) [Group X] [Finite X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) :
    SmallListFacts X ∧ FixPointwiseInner X := by
  obtain ⟨e⟩ := h
  exact ⟨SmallListFacts.of_mulEquiv e m11G_smallListFacts,
    FixPointwiseInner.of_mulEquiv e m11G_fixPointwiseInner⟩

end CFSG.QuasithinUnique.Unc25M11
