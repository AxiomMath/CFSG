module

public import CFSG.LieType.Chevalley.Assembly
public import CFSG.LieType.Chevalley.NativeRoots
public import CFSG.LieType.Chevalley.NativeTorus
public import CFSG.LieType.Chevalley.WeylSpace
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits RootSpace
open scoped RealInnerProductSpace

variable (τ : Tag) (K : Type) [Field K]

structure RootSubgroups where
  X : Root τ → Subgroup (adjointGroup τ K)
  mem_simple : ∀ i (g : adjointGroup τ K), g ∈ X (simpleRoot τ i) ↔
    ∃ c : K, (g : ModGL τ K) = xUnit τ K i c
  mem_neg_simple : ∀ i (g : adjointGroup τ K), g ∈ X (-simpleRoot τ i) ↔
    ∃ c : K, (g : ModGL τ K) = yUnit τ K i c
  weight_shift : ∀ α, ∀ g ∈ X α, ∀ a b : Label τ,
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
        (Finsupp.single b 1 : RootModule τ K) a ≠ 0 →
      ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • α.1
  conj_weyl : ∀ i α,
    (X α).map (MulAut.conj (weylElement τ K i)).toMonoidHom = X (simple τ i • α)
  conj_torus : ∀ i (t : Kˣ) α,
    (X α).map (MulAut.conj (torusElement τ K i t)).toMonoidHom = X α
  comm : ∀ (i : Fin τ.rank) (β : Root τ), 0 < height β.1 → β ≠ simpleRoot τ i →
    ∀ x ∈ X (simpleRoot τ i), ∀ y ∈ X β, x * y * x⁻¹ * y⁻¹ ∈
      ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • (simpleRoot τ i).1 + b • β.1),
        X γ

variable {τ K}

theorem map_conj_map_conj {G : Type*} [Group G] (g h : G) (S : Subgroup G) :
    (S.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      S.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one {G : Type*} [Group G] (S : Subgroup G) :
    S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  ext y
  simp

theorem RootSubgroups.map_conj [Finite K] (F : RootSubgroups τ K) (m : monomialGroup τ K)
    (α : Root τ) :
    (F.X α).map (MulAut.conj (m : adjointGroup τ K)).toMonoidHom =
      F.X (weylHom τ K m • α) := by
  obtain ⟨m, hm⟩ := m
  induction hm using Subgroup.closure_induction generalizing α with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨⟨i, t⟩, rfl⟩
    · rw [F.conj_weyl, weylHom_weylElement]
    · rw [F.conj_torus, weylHom_torusElement, one_smul]
  | one =>
    have h1 : weylHom τ K ⟨1, one_mem _⟩ = 1 := map_one _
    rw [h1, one_smul, map_conj_one]
  | mul x y hx hy ihx ihy =>
    have hxy : weylHom τ K ⟨x * y, mul_mem (show x ∈ monomialGroup τ K from hx)
        (show y ∈ monomialGroup τ K from hy)⟩ =
        weylHom τ K ⟨x, hx⟩ * weylHom τ K ⟨y, hy⟩ := by
      rw [← map_mul]
      rfl
    rw [hxy, mul_smul, ← ihx, ← ihy, map_conj_map_conj]
  | inv x hx ihx =>
    have hx' : x ∈ monomialGroup τ K := hx
    have hinv : weylHom τ K ⟨x⁻¹, inv_mem hx'⟩ = (weylHom τ K ⟨x, hx'⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [hinv]
    have h := ihx ((weylHom τ K ⟨x, hx'⟩)⁻¹ • α)
    rw [smul_inv_smul] at h
    rw [← h, map_conj_map_conj, inv_mul_cancel, map_conj_one]

@[expose] noncomputable def RootSubgroups.toRootGroupData [Finite K] (F : RootSubgroups τ K) :
    RootGroupData (rootCombinatorics τ) (adjointGroup τ K) where
  X := F.X
  N := monomialGroup τ K
  φ := weylHom τ K
  n i := ⟨weylElement τ K i, weylElement_mem_monomialGroup i⟩
  φ_n i := weylHom_weylElement i
  map_conj m α := F.map_conj m α

theorem RootSubgroups.pow_card_sub_one_eq_one [Finite K] (F : RootSubgroups τ K)
    {h : adjointGroup τ K} (hh : h ∈ F.toRootGroupData.H) : h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := F.toRootGroupData)).mp hh
  have hmono := isMonomial_weylHom k
  change weylHom τ K k = 1 at hk
  rw [hk] at hmono
  have hpres : PreservesWeights
      (((k : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K)) := by
    intro a b hab
    have := hmono a b (by simpa using hab)
    rwa [one_smul] at this
  have hdiag : ∀ b : Label τ, ∃ μ : K,
      (((k : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single b 1) = μ • Finsupp.single b 1 := by
    rintro (i | ⟨α, hα⟩)
    · have hmap := F.map_conj k (simpleRoot τ i)
      change (F.X (simpleRoot τ i)).map _ = F.X (weylHom τ K k • simpleRoot τ i) at hmap
      rw [hk, one_smul] at hmap
      obtain ⟨x, hx⟩ : ∃ x : adjointGroup τ K, (x : ModGL τ K) = xUnit τ K i 1 :=
        ⟨⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩, rfl⟩
      have hxX : x ∈ F.X (simpleRoot τ i) := (F.mem_simple i x).mpr ⟨1, hx⟩
      have hconj : (k : adjointGroup τ K) * x * (k : adjointGroup τ K)⁻¹ ∈
          F.X (simpleRoot τ i) := by
        rw [← hmap]
        exact ⟨x, hxX, rfl⟩
      obtain ⟨c, hc⟩ := (F.mem_simple i _).mp hconj
      have hc' := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hx, coe_xUnit] at hc'
      have hcomm : (((k : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K)) *
          xOp τ K i 1 = xOp τ K i c *
            (((k : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K)) := by
        rw [← hc', mul_assoc _ (((((k : adjointGroup τ K) : ModGL τ K))⁻¹ : ModGL τ K) :
          Module.End K (RootModule τ K)), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one]
      exact exists_apply_hVec_eq_smul hpres i hcomm
    · have := hpres.apply_rootVec (K := K) hα
      rw [rootVec_eq_single hα] at this
      exact ⟨_, this⟩
  have hpow := pow_card_sub_one_eq_one_of_diagonal
    ((k : adjointGroup τ K) : ModGL τ K) hdiag
  exact Subtype.ext (by simpa using hpow)

theorem RootSubgroups.coprime_card_H [Finite K] (F : RootSubgroups τ K) (p : ℕ) [Fact p.Prime]
    [CharP K p] : Nat.Coprime (Nat.card F.toRootGroupData.H) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow := F.pow_card_sub_one_eq_one h.2
  have hdvd' : p ∣ Nat.card K - 1 := by
    rw [← hh, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hpow
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  have hpK : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  have := Nat.dvd_sub hpK hdvd'
  rw [Nat.sub_sub_self hK1, Nat.dvd_one] at this
  exact (Fact.out : p.Prime).one_lt.ne' this

theorem labelWeight_eq_ofLattice (a : Label τ) : labelWeight a = ofLattice (labelWt τ a) := by
  rcases a with i | α
  · change (0 : RootSpace τ) = ofLattice 0
    rw [ofLattice_zero]
  · rfl

@[expose] noncomputable def xElement (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

@[expose] noncomputable def yElement (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

theorem torusElement_mem_H [Finite K] (F : RootSubgroups τ K) (i : Fin τ.rank) (t : Kˣ) :
    torusElement τ K i t ∈ F.toRootGroupData.H :=
  (RootGroupData.mem_H_iff (D := F.toRootGroupData)).mpr
    ⟨⟨_, torusElement_mem_monomialGroup i t⟩, weylHom_torusElement i t, rfl⟩

theorem xElement_mem_B [Finite K] (F : RootSubgroups τ K) (i : Fin τ.rank) (c : K) :
    xElement i c ∈ F.toRootGroupData.B :=
  F.toRootGroupData.U_le_B (F.toRootGroupData.simple_le_U i
    ((F.mem_simple i _).mpr ⟨c, rfl⟩))

theorem RootSubgroups.rankOne [Finite K] (F : RootSubgroups τ K) (i : Fin τ.rank) :
    F.toRootGroupData.RankOne i := by
  intro y hy
  obtain ⟨c, hc⟩ := (F.mem_neg_simple i y).mp hy
  rcases eq_or_ne c 0 with rfl | hc0
  · left
    have : y = 1 := Subtype.ext (hc.trans (Units.ext (yOp_zero i)))
    rw [this]
    exact one_mem _
  · right
    set u : Kˣ := Units.mk0 c hc0
    refine ⟨xElement i ↑u⁻¹ * torusElement τ K i (-u⁻¹),
      mul_mem (xElement_mem_B F i _) (F.toRootGroupData.H_le_B (torusElement_mem_H F i _)),
      xElement i ↑u⁻¹, xElement_mem_B F i _, ?_⟩
    apply Subtype.ext
    rw [hc]
    have := yUnit_eq_mul_weylElt (τ := τ) (K := K) i u
    rw [Units.val_mk0] at this
    rw [this]
    rfl

theorem RootSubgroups.closure_B_union_n [Finite K] (F : RootSubgroups τ K) :
    Subgroup.closure ((F.toRootGroupData.B : Set (adjointGroup τ K)) ∪
      Set.range fun i => (F.toRootGroupData.n i : adjointGroup τ K)) = ⊤ := by
  set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · refine Subgroup.subset_closure (.inl ?_)
    have : g = xElement i c := Subtype.ext (Units.ext hg)
    rw [this]
    exact xElement_mem_B F i c
  · have hgX : g ∈ F.X (-simpleRoot τ i) :=
      (F.mem_neg_simple i g).mpr ⟨c, Units.ext hg⟩
    rcases F.rankOne i g hgX with hB | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    · exact Subgroup.subset_closure (.inl hB)
    · refine mul_mem (mul_mem (Subgroup.subset_closure (.inl hb₁))
        (Subgroup.subset_closure (.inr ⟨i, rfl⟩))) (Subgroup.subset_closure (.inl hb₂))

theorem RootSubgroups.simple_le_normalizer_Ui [Finite K] (F : RootSubgroups τ K)
    (i : Fin τ.rank) :
    F.toRootGroupData.X ((rootCombinatorics τ).simple i) ≤
      Subgroup.normalizer (F.toRootGroupData.Ui i : Set (adjointGroup τ K)) := by
  refine F.toRootGroupData.simple_le_normalizer_Ui i fun β hβ hne x hx y hy => ?_
  have hβ' : 0 < height β.1 := hβ
  have h := F.comm i β hβ' hne x hx y hy
  refine (iSup₂_le (f := fun (γ : Root τ)
    (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • (simpleRoot τ i).1 + b • β.1) => F.X γ)
    (a := F.toRootGroupData.Ui i) fun γ hγ => ?_) h
  obtain ⟨a, b, ha, hb, hγeq⟩ := hγ
  have hβnn := (IsRoot.height_pos_iff β.2).1 hβ'
  have hcoord : ∀ k, γ.1 k = a * (Pi.single i 1 : Fin τ.rank → ℤ) k + b * β.1 k := fun k => by
    rw [hγeq]
    simp [nsmul_eq_mul, simpleRoot]
  have hγpos : 0 < height γ.1 := by
    have hsum : height γ.1 = a * height (Pi.single i 1 : Fin τ.rank → ℤ) + b * height β.1 := by
      simp only [height, hcoord, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum, height_single]
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have ha' : (0 : ℤ) ≤ a := by positivity
    nlinarith
  have hγne : γ ≠ simpleRoot τ i := by
    intro h
    have hval : ∀ k, γ.1 k = (Pi.single i 1 : Fin τ.rank → ℤ) k := fun k => by rw [h]; rfl
    by_cases hall : ∀ j, j ≠ i → β.1 j = 0
    ·
      have hβi : β.1 = (β.1 i) • Pi.single i 1 := by
        ext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hall k hk, hk]
      have hroot : IsRoot τ ((β.1 i) • Pi.single i 1) := hβi ▸ β.2
      rcases (isRoot_smul_single_iff i (β.1 i)).1 hroot with h1 | h1
      · exact hne (Subtype.ext (by rw [hβi, h1, one_smul]; rfl))
      · have := hβnn i
        omega
    · push Not at hall
      obtain ⟨j, hji, hj0⟩ := hall
      have hjpos : 0 < β.1 j := lt_of_le_of_ne (hβnn j) (Ne.symm hj0)
      have h1 := hval j
      rw [hcoord, Pi.single_apply, ite_eq_right_iff.mpr (fun h => absurd h hji), mul_zero,
        zero_add] at h1
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
  exact F.toRootGroupData.X_le_Ui hγpos hγne

theorem weylHom_surjective [Finite K] : Function.Surjective (weylHom τ K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_simple, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, weylHom_weylElement i⟩

theorem RootSubgroups.X_ne_bot [Finite K] (F : RootSubgroups τ K) (α : Root τ) :
    F.X α ≠ ⊥ := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.mp α.2
  obtain ⟨m, rfl⟩ := weylHom_surjective (τ := τ) (K := K) w
  have hα : α = weylHom τ K m • simpleRoot τ j := Subtype.ext hwj.symm
  rw [hα, ← F.map_conj m]
  intro hbot
  have hx : xElement (K := K) j 1 ∈ F.X (simpleRoot τ j) := (F.mem_simple j _).mpr ⟨1, rfl⟩
  have hmem : (MulAut.conj (m : adjointGroup τ K)).toMonoidHom (xElement j 1) ∈
      (F.X (simpleRoot τ j)).map (MulAut.conj (m : adjointGroup τ K)).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot] at hmem
  replace hmem : xElement (K := K) j 1 = 1 := by simpa using hmem
  have h1 : xOp τ K j 1 = xOp τ K j 0 := by
    rw [xOp_zero]
    exact congrArg (fun g : adjointGroup τ K =>
      ((g : ModGL τ K) : Module.End K (RootModule τ K))) hmem
  exact one_ne_zero (xOp_injective j h1)

theorem holds_adjointGroup [Finite K] (F : RootSubgroups τ K) (p : ℕ) [Fact p.Prime] [CharP K p] :
    Holds (adjointGroup τ K) p := by
  classical
  set D := F.toRootGroupData
  refine holds_of_rootGroupData D Finsupp.basisSingleOne (glRep (adjointGroup τ K)) p
    (glRep_injective _) (weylAct τ) labelWeight (fun α => ofLattice α.1) (dominantCone τ)
    (heightVector τ) F.simple_le_normalizer_Ui F.rankOne F.closure_B_union_n
    closure_range_simple ?_ (fun v hv => eq_zero_of_forall_weylAct_eq hv)
    exists_weylAct_mem_dominantCone ?_ ?_
    (fun α => ofLattice_neg α.1)
    (fun α hα v hv => IsRoot.inner_nonneg_of_mem_dominantCone α.2 hα hv)
    (fun α hα => IsRoot.inner_heightVector_pos hα) F.X_ne_bot
    (fun w hw => rootCombinatorics_eq_one hw) (F.coprime_card_H p)
  ·
    refine eq_top_iff.2 ((span_ofLattice_isRoot (τ := τ)).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨α, rfl⟩
    exact ⟨.inr α, rfl⟩
  ·
    intro m a b hab
    have h := isMonomial_weylHom m a b (by simpa using hab)
    rw [labelWeight_eq_ofLattice, labelWeight_eq_ofLattice, h, weylAct_ofLattice]
    rfl
  ·
    intro α x hx a b hab
    obtain ⟨k, hk, hw⟩ := F.weight_shift α x hx a b (by simpa using hab)
    refine ⟨k, hk, ?_⟩
    rw [labelWeight_eq_ofLattice, labelWeight_eq_ofLattice, hw, ofLattice_add]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℤ, ofLattice_smul]
    norm_cast

end CFSG.LieType.Chevalley
