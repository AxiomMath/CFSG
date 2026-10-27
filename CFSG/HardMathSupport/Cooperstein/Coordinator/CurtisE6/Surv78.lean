module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv27
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv78Model
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjDisp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min TensorProduct


theorem isSimpleRep_comp {G H : Type*} [Group G] [Group H] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] {ρ : Representation k H V} (hρ : IsSimpleRep ρ) {π : G →* H}
    (hπ : Function.Surjective π) : IsSimpleRep (ρ.comp π) :=
  ⟨hρ.1, fun W hW => hρ.2 W fun g w hw => by
    obtain ⟨g', rfl⟩ := hπ g
    exact hW g' w hw⟩

theorem heckeT_cover_comp {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Finite G] [Fact p.Prime]
    {D : CurtisDatum G cs p} {π : Ĝ →* G} (C : CentralCoverData D π p) {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (s : B) (v : V) :
    C.datum.heckeT (ρ.comp π) s v = D.heckeT ρ s v := by
  have i0 : Fintype ↥(D.X s) := Fintype.ofFinite _
  letI i2 : Fintype ↥(C.lX s) := Fintype.ofFinite _
  letI i1 : Fintype ↥(C.datum.X s) := i2
  rw [C.datum.heckeT_apply, D.heckeT_apply]
  refine Fintype.sum_equiv (C.lXEquiv s) (fun x : ↥(C.lX s) => (ρ.comp π) ((x : Ĝ) * C.nhat s) v)
    (fun y : ↥(D.X s) => ρ ((y : G) * D.n s) v) fun x => ?_
  show ρ (π ((x : Ĝ) * C.nhat s)) v = ρ (π (x : Ĝ) * D.n s) v
  rw [map_mul, C.hn]

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [Algebra K k]
  [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]

theorem e6IsogenyT_hm' (i : Fin TwistTag.E6.tag.rank) (u : Kˣ) :
    Isogeny.e6IsogenyT K (e6Data_valid.hm K i u) = dC TwistTag.E6.tag K i u :=
  Subtype.ext (coe_e6IsogenyT_hm i u)

theorem e6_isCoverType_comp {ρ : Representation k ↥(adjointGroup TwistTag.E6.tag K) V} {y : V}
    {χ : ↥(adjointGroup TwistTag.E6.tag K) → k} {J : Finset (Fin TwistTag.E6.tag.rank)}
    (ht : IsChevTypeLD TwistTag.E6 K 2 e6LongestData ρ y χ J) :
    IsCoverType (e6CoverRankOne K) (ρ.comp (Isogeny.e6IsogenyT K)) y
      (fun g => χ (Isogeny.e6IsogenyT K g)) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨?_, h2, fun h hh => h3 _ (Subgroup.mem_comap.1 hh), fun s => ?_⟩
  · refine ((e6CoverData K).datum.mem_fixU _).2 fun u hu => ?_
    exact ((chevDatumLD TwistTag.E6 K 2 e6LongestData).mem_fixU _).1 h1 _ hu.1
  · rw [h4 s, heckeT_cover_comp (e6CoverData K)]
    refine and_congr (forall_congr' fun u => ?_) Iff.rfl
    show χ (dC TwistTag.E6.tag K s u) = 1 ↔ χ (Isogeny.e6IsogenyT K (e6Data_valid.hm K s u)) = 1
    rw [e6IsogenyT_hm']

theorem isSimpleRep_bc_adj78' : IsSimpleRep (Survivors.bcRep k (adj78 K)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Survivors.isSimpleRep_bc (adjDatum78 (K := K)) (adj78 K) (rootVec TwistTag.E6.tag K e6Theta)
    rootVec_theta_ne_zero (fun _ hx => fixU_le_line78 hx)
    (orbitSpan_adjRep adjTop_E6.root (words := fun j => e6ThetaWords.getD j []) e6_words_check)

theorem adj78_bc_isChevTypeLD' :
    IsChevTypeLD TwistTag.E6 K 2 e6LongestData (Survivors.bcRep k (adj78 K))
      (Survivors.bcVec k (rootVec TwistTag.E6.tag K e6Theta))
      (fun g => algebraMap K k (adjChi78 K g)) (Finset.univ.erase e6node2) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Survivors.IsTypeGen.baseChange (chevDatumLD TwistTag.E6 K 2 e6LongestData)
    (show Survivors.IsTypeGen (chevDatumLD TwistTag.E6 K 2 e6LongestData) (adj78 K)
      (rootVec TwistTag.E6.tag K e6Theta) (adjChi78 K) (Finset.univ.erase e6node2)
      _ (fun s => Kˣ) (fun i t => dC TwistTag.E6.tag K i t) from adj78_isChevTypeLD)

theorem e6_78_iso_bc {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ (Finset.univ.erase e6node2))
    (hχ : ∀ i u, χ (e6Data_valid.hm K i u) =
      algebraMap K k (adjChi78 K (dC TwistTag.E6.tag K i u))) :
    ∃ β : (k ⊗[K] RootModule TwistTag.E6.tag K) ≃ₗ[k] V, ∀ (g : ↥(e6Data_valid.minGroup K))
      (v : k ⊗[K] RootModule TwistTag.E6.tag K),
        β (((Survivors.bcRep k (adj78 K)).comp (Isogeny.e6IsogenyT K)) g v) = ρ g (β v) := by
  have hρ₂ := isSimpleRep_comp (isSimpleRep_bc_adj78' (K := K) (k := k))
    (Isogeny.e6IsogenyT_surjective (k := K))
  have ht₂ := e6_isCoverType_comp (adj78_bc_isChevTypeLD' (K := K) (k := k))
  have hH := e6_chi_eq_on_H hρ hρ₂ ht ht₂ (fun i u => by
    rw [hχ i u]
    exact congrArg (fun x => algebraMap K k (adjChi78 K x)) (e6IsogenyT_hm' (K := K) i u).symm)
  exact e6_iso_of_isCoverType hρ₂ hρ ht₂ (CurtisTw.IsCoverType.congr_H ht hH)

end Model

section Card

open FFExc CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour

theorem card_le_of_conj_abelian' {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : List (List ℤ)}
    (hPD : PosData τ R) (hc0 : 0 < τ.cartan.det) {k : Type*} [Field k] [Finite k]
    (U : Subgroup (hV.minGroup k)) (hU : U = posUnip hV k)
    (hconj : ∀ A : Subgroup (hV.minGroup k), (∀ a ∈ A, a ^ 2 = 1) →
      ∃ g : hV.minGroup k, A.map (MulAut.conj g).toMonoidHom ≤ U) (N : ℕ)
    (hab : ∀ X : Finset (Fin τ.rank → ℤ), (∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ) →
      (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot τ (γ + δ)) → X.card ≤ N)
    (A : Subgroup (hV.minGroup k)) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ Nat.card k ^ N := by
  obtain ⟨g, hg⟩ := hconj A hel
  have hel' : ∀ b ∈ A.map (MulAut.conj g).toMonoidHom, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have hAU : A.map (MulAut.conj g).toMonoidHom ≤ lvlU hV k (fWt τ.rank) 1 := by
    rw [lvlU_one_eq hV hPD k, ← hU]; exact hg
  obtain ⟨X, Y, hXr, hXX, -, hcard, -, -⟩ := exists_leading_data (hV := hV) (k := k) hc0
    (fun γ δ hγ hδ h => hPD.inj γ δ hγ hδ h) hAU (comm_of_exp_two hel')
  have hXP : ∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ := fun γ hγ =>
    ⟨(hXr γ hγ).1, (hPD.pos γ (hXr γ hγ).1).1 (hXr γ hγ).2⟩
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  rw [← natCard_map_conj' hV k A g]
  exact hcard.trans (Nat.pow_le_pow_right hq (hab X hXP hXX))

theorem e6_abelian_card_bound' (K : Type) [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (e6Data_valid.minGroup K)) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ Nat.card K ^ 16 := by
  have := finite_minGroup6 K
  exact card_le_of_conj_abelian' e6Data_valid posData_E6
    (MinData.det_cartan_pos posDef_cartan_E6) (posU6 K) (posU6_eq K)
    (fun B hB => e6_conj_into_posU6 K B (isPGroup_of_sq B hB)) 16
    (fun X hXP hXX => e6_abelian_card_le X hXP hXX) A hel

end Card

section Bound

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem adj78_fix_bound (A : Subgroup ↥(e6Data_valid.minGroup K)) (hA : ∀ a ∈ A, a ^ 2 = 1)
    (hne : A ≠ ⊥) :
    22 + Module.finrank K ↥(fixSub (adj78 K) (A.map (Isogeny.e6IsogenyT K))) ≤ 78 := by
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hπ1 : Isogeny.e6IsogenyT K (a : ↥(e6Data_valid.minGroup K)) ≠ 1 := fun h =>
    ha1 (Subtype.ext (FFExc.two_group_inf_ker K A (FFExc.isPGroup_of_sq A hA) a.2 h))
  have hp : IsPGroup 2 (A.map (Isogeny.e6IsogenyT K)) := FFExc.isPGroup_of_sq _ (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA x hx, map_one])
  obtain ⟨g, hg⟩ : ∃ g : ↥(adjointGroup TwistTag.E6.tag K),
      (A.map (Isogeny.e6IsogenyT K)).map (MulAut.conj g).toMonoidHom ≤
        (posUnipotent TwistTag.E6.tag K).subgroupOf (adjointGroup TwistTag.E6.tag K) :=
    FFExc.adjoint_conj_into_U K Tag.E6 (A.map (Isogeny.e6IsogenyT K)) hp
  obtain ⟨b, hb⟩ : ∃ b : ↥(adjointGroup TwistTag.E6.tag K),
      b = Isogeny.e6IsogenyT K (a : ↥(e6Data_valid.minGroup K)) := ⟨_, rfl⟩
  have hbA : b ∈ A.map (Isogeny.e6IsogenyT K) := ⟨a, a.2, hb.symm⟩
  have hc := hg ⟨b, hbA, rfl⟩
  have hu : (((MulAut.conj g) b : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) ∈
      posUnipotent TwistTag.E6.tag K := Subgroup.mem_subgroupOf.1 hc
  have hu1 : (((MulAut.conj g) b : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) ≠
      1 := by
    intro h
    have h' : (MulAut.conj g) b = 1 := Subtype.ext h
    exact hπ1 (hb ▸ (MulAut.conj g).map_eq_one_iff.1 h')
  have h22 := FFExc.displacement_E6 K hu hu1
  set E : Module.End K (RootModule TwistTag.E6.tag K) := ((b : ModGL TwistTag.E6.tag K) :
    Module.End K (RootModule TwistTag.E6.tag K)) - 1 with hE
  have hconj : ((((MulAut.conj g) b : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1 =
      (1 : K) • (((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) * E *
        (((g : ModGL TwistTag.E6.tag K)⁻¹ : ModGL TwistTag.E6.tag K) :
          Module.End K (RootModule TwistTag.E6.tag K))) := by
    have h1 : ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) *
        (((g : ModGL TwistTag.E6.tag K)⁻¹ : ModGL TwistTag.E6.tag K) :
          Module.End K (RootModule TwistTag.E6.tag K)) = 1 := Units.mul_inv _
    rw [one_smul, hE, mul_sub, sub_mul, mul_one, h1]
    simp [MulAut.conj_apply, mul_assoc]
  have hrank : 22 ≤ Module.finrank K ↥(LinearMap.range E) := by
    have h2 := FFExc.finrank_range_conj
      ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))
      (((g : ModGL TwistTag.E6.tag K)⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) E (Units.mul_inv _) (Units.inv_mul _) 1
      one_ne_zero
    rw [← h2, ← hconj]
    exact h22
  have hle : fixSub (adj78 K) (A.map (Isogeny.e6IsogenyT K)) ≤ LinearMap.ker E := by
    intro v hv
    have := hv b hbA
    rw [LinearMap.mem_ker, hE]
    show ((b : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) v - v = 0
    exact sub_eq_zero.2 this
  have h3 := LinearMap.finrank_range_add_finrank_ker E
  have h4 := Submodule.finrank_mono hle
  rw [finrank_adj78] at h3
  omega

end Bound

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6Surv78_core {k : Type} [Field k] [CharP k 2] [inst₀ : Algebra K k] {V : Type*}
    [AddCommGroup V] [Module k V] {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6} {b : ℕ}
    (hρ : IsSimpleRep ρ) (ht : IsCoverType (e6CoverRankOne K) ρ y χ J)
    (hJ : J = Finset.univ.erase (⟨1, by decide⟩ : N6))
    (hχ : ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
      if i = (⟨1, by decide⟩ : N6) then (@algebraMap K k _ _ inst₀ (u : K)) ^ (2 ^ b) else 1) :
    Module.finrank k V = 78 ∧ ∀ A : Subgroup ↥(e6Data_valid.minGroup K), (∀ a ∈ A, a ^ 2 = 1) →
      A ≠ ⊥ → 22 + Module.finrank k ↥(fixSub ρ A) ≤ 78 ∧ Nat.card A ≤ Nat.card K ^ 16 := by
  letI alg : Algebra K k := ((algebraMap K k).comp (frobEquiv K b).toRingHom).toAlgebra
  have key : ∀ u : K, algebraMap K k u = (@algebraMap K k _ _ inst₀ u) ^ (2 ^ b) := fun u => by
    show @algebraMap K k _ _ inst₀ (frobEquiv K b u) = _
    rw [frobEquiv_apply, map_pow]
  have key2 : ∀ (i : Fin TwistTag.E6.tag.rank) (u : Kˣ),
      (if i = e6node2 then (@algebraMap K k _ _ inst₀ (u : K)) ^ (2 ^ b) else 1) =
        algebraMap K k (adjChi78 K (dC TwistTag.E6.tag K i u)) := by
    intro i u
    rw [adjChi78_dC, key]
    by_cases h : i = e6node2
    · rw [if_pos h, if_pos h, zpow_one]
    · rw [if_neg h, if_neg h, zpow_zero]
      simp
  subst hJ
  have hχ' : ∀ i u, χ (e6Data_valid.hm K i u) =
      algebraMap K k (adjChi78 K (dC TwistTag.E6.tag K i u)) := fun i u => (hχ i u).trans (key2 i u)
  obtain ⟨β, hβ⟩ := e6_78_iso_bc hρ ht hχ'
  refine ⟨?_, fun A hA hne => ?_⟩
  · rw [← β.finrank_eq, Module.finrank_baseChange, finrank_adj78]
  · have h1 := finrank_fixSub_of_iso β hβ A
    have e : fixSub ((Survivors.bcRep k (adj78 K)).comp (Isogeny.e6IsogenyT K)) A =
        fixSub (Survivors.bcRep k (adj78 K)) (A.map (Isogeny.e6IsogenyT K)) := by
      ext v
      constructor
      · intro hv h hh
        obtain ⟨g, hg, rfl⟩ := hh
        exact hv g hg
      · intro hv g hg
        exact hv _ ⟨g, hg, rfl⟩
    have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (adj78 K) (A.map (Isogeny.e6IsogenyT K))
    have h3 := adj78_fix_bound A hA hne
    refine ⟨?_, e6_abelian_card_bound' K A hA⟩
    rw [h1, e]
    omega

end Core

theorem e6Surv78_holds : E6Surv78 := by
  intro K _ _ _ n hn hK k _ _ _ _ m ρ y χ J b hρ ht hb hJ hχ
  obtain ⟨h1, h2⟩ := e6Surv78_core hρ ht hJ hχ
  exact ⟨by simpa using h1, h2⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
