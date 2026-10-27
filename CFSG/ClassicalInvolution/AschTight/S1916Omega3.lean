module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega2
public import CFSG.ClassicalInvolution.Asc77.AscSix69
public import CFSG.ClassicalInvolution.AschTight.S1916Omega

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

structure YPrimeData (K : Subgroup G) (z : G) (Y' Q : Subgroup G) : Prop where
  normal : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Y' : Set G)
  le : Y' ≤ Subgroup.centralizer ({z} : Set G)
  sylow : IsSylow2In Q Y'
  inv : IsUniqueInvolution Q z
  noncomm : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  card : ∀ R : Subgroup G, IsSylow2In R K → Nat.card R = Nat.card Q
  gen : Subgroup.closure {x : G | x ∈ Y' ∧ IsPGroup 2 (Subgroup.zpowers x)} = Y'
  cent : ∀ y ∈ Y', ∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K

variable {Y' Q : Subgroup G}

omit [Finite G] in
theorem mem_omegaPrime_iff {M : Subgroup G} :
    M ∈ omegaPrime K Y' ↔ ∃ g : G, M = conjSub g K ∨ M = conjSub g Y' := by
  constructor
  · rintro (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact ⟨g, Or.inl rfl⟩
    · exact ⟨g, Or.inr rfl⟩
  · rintro ⟨g, rfl | rfl⟩
    · exact Or.inl ⟨g, rfl⟩
    · exact Or.inr ⟨g, rfl⟩

theorem centralizer_le_normalizer_of_tightD (ht : S19R.TightStd p f K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  (normalizer_eq_centralizer_of_tight ht.toTightBranch).ge

theorem exists_data_of_mem_omegaPrime (ht : S19R.TightStd p f K z) (hY : YPrimeData K z Y' Q)
    {M : Subgroup G} (hM : M ∈ omegaPrime K Y') :
    ∃ g : G, (M = conjSub g K ∨ M = conjSub g Y') ∧ IsUniqueInvolution M (g * z * g⁻¹) ∧
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  obtain ⟨g, rfl | rfl⟩ := mem_omegaPrime_iff.mp hM
  · exact ⟨g, Or.inl rfl, hzK.conj g,
      centralizer_le_normalizer_conjSub (centralizer_le_normalizer_of_tightD ht) g⟩
  · exact ⟨g, Or.inr rfl, hzY.conj g, centralizer_le_normalizer_conjSub hY.normal g⟩

theorem natCard_eq_of_isSylow2In_omegaPrime (hY : YPrimeData K z Y' Q) {M P : Subgroup G}
    (hM : M ∈ omegaPrime K Y') (hP : IsSylow2In P M) : Nat.card P = Nat.card Q := by
  obtain ⟨g, rfl | rfl⟩ := mem_omegaPrime_iff.mp hM
  · have h1 := hP.conj g⁻¹
    rw [conjSub_inv_conjSub] at h1
    rw [← hY.card _ h1]
    exact (natCard_conjSub P g⁻¹).symm
  · have h1 := hP.conj g⁻¹
    rw [conjSub_inv_conjSub] at h1
    rw [← h1.natCard_eq hY.sylow]
    exact (natCard_conjSub P g⁻¹).symm

omit [Finite G] in
theorem not_isMulCommutative_conjSub {P : Subgroup G} (h : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x)
    (g : G) : ¬ IsMulCommutative ↥(conjSub g P) := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  have h1 := hc.is_comm.comm (⟨g * x * g⁻¹, conj_mem_conjSub hx⟩ : ↥(conjSub g P))
    ⟨g * y * g⁻¹, conj_mem_conjSub hy⟩
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul] at h2
  apply hxy
  have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h2
      _ = g * (y * x) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

omit [Finite G] in
theorem closure_twoElements_conjSub {M : Subgroup G}
    (hgen : Subgroup.closure {x : G | x ∈ M ∧ IsPGroup 2 (Subgroup.zpowers x)} = M) (g : G) :
    Subgroup.closure {x : G | x ∈ conjSub g M ∧ IsPGroup 2 (Subgroup.zpowers x)} =
      conjSub g M := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  conv_lhs => rw [← hgen]
  rw [conjSub, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxM, hx2⟩, rfl⟩
  refine ⟨⟨x, hxM, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

omit [Finite G] in
theorem omega4_conjSub {M N : Subgroup G} (g : G)
    (h : padicValNat 2 (Nat.card ↥(M ⊓ N)) ≤ 1 ∧ ⁅M, N⁆ ≤ oddCoreOf M ⊓ oddCoreOf N) :
    padicValNat 2 (Nat.card ↥(conjSub g M ⊓ conjSub g N)) ≤ 1 ∧
      ⁅conjSub g M, conjSub g N⁆ ≤ oddCoreOf (conjSub g M) ⊓ oddCoreOf (conjSub g N) := by
  refine ⟨?_, ?_⟩
  · rw [← conjSub_inf, natCard_conjSub]
    exact h.1
  · rw [oddCoreOf_conjSub, oddCoreOf_conjSub, ← conjSub_inf, conjSub, conjSub, conjSub,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono h.2

theorem hypOmegaGen_omegaPrime [IsSimpleGroup G] (ht : S19R.TightStd p f K z)
    (hY : YPrimeData K z Y' Q) :
    HypOmegaGen (omegaPrime K Y') where
  conjInvariant := conjInvariant_omegaPrime K Y'
  omega1 := by
    intro M hM
    obtain ⟨g, hMg, hzM, -⟩ := exists_data_of_mem_omegaPrime ht hY hM
    refine ⟨⟨_, hzM⟩, ?_⟩
    rcases hMg with rfl | rfl
    · obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
      have hR := isSylow2In_map_sylow K Q₀
      have hRmem : (Q₀ : Subgroup ↥K).map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
        ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
      exact ⟨_, hR.conj g, not_isMulCommutative_conjSub (exists_ne_comm_of_mem_rSet
        ht.branch.odd ht.branch.five ht.branch.member hRmem).1 g⟩
    · exact ⟨_, hY.sylow.conj g, not_isMulCommutative_conjSub hY.noncomm g⟩
  omega2 := by
    intro M hM
    left
    obtain ⟨g, rfl | rfl⟩ := mem_omegaPrime_iff.mp hM
    · obtain ⟨z', hz'⟩ := classical_of_tight ht.toTightBranch (conjSub g K) ⟨g, rfl⟩
      refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
      refine le_of_forall_isSylow2In_of_isPerfect hz'.perfect fun V hV x hx => ?_
      exact Subgroup.subset_closure ⟨hV.1 hx, hV.2.1.to_le (Subgroup.zpowers_le.mpr hx)⟩
    · exact closure_twoElements_conjSub hY.gen g
  omega3 := fun M hM J hJ P P' hP hP' => by
    rw [natCard_eq_of_isSylow2In_omegaPrime hY hM hP, natCard_eq_of_isSylow2In_omegaPrime hY hJ hP']
  omega4 := by
    intro M hM J hJ hne
    obtain ⟨g, hMg, hzM, -⟩ := exists_data_of_mem_omegaPrime ht hY hM
    obtain ⟨h, hJh, hzJ, -⟩ := exists_data_of_mem_omegaPrime ht hY hJ
    by_cases h2 : 2 ∣ Nat.card ↥(M ⊓ J)
    · obtain ⟨y, hy, hy2, hy1⟩ := exists_involution_of_two_dvd h2
      have e1 : y = g * z * g⁻¹ := (hzM.unique y hy.1 hy2).resolve_left hy1
      have e2 : y = h * z * h⁻¹ := (hzJ.unique y hy.2 hy2).resolve_left hy1
      have egh : g * z * g⁻¹ = h * z * h⁻¹ := e1.symm.trans e2
      have hbase := omega4_base ht hY.normal hY.le hY.cent
      rcases hMg with rfl | rfl <;> rcases hJh with rfl | rfl
      · exact (hypOmegaMod_of_tightD ht).omega4 _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ hne
      · have e : conjSub h Y' = conjSub g Y' := conjSub_eq_of_conj_eq hY.normal egh.symm
        rw [e]
        have := omega4_conjSub g hbase
        exact ⟨this.1, fun _ => this.2⟩
      · have e : conjSub g Y' = conjSub h Y' := conjSub_eq_of_conj_eq hY.normal egh
        rw [e, inf_comm, Subgroup.commutator_comm, inf_comm (oddCoreOf (conjSub h Y'))]
        have := omega4_conjSub h hbase
        exact ⟨this.1, fun _ => this.2⟩
      · exact absurd (conjSub_eq_of_conj_eq hY.normal egh) hne
    · have h0 : padicValNat 2 (Nat.card ↥(M ⊓ J)) = 0 := padicValNat.eq_zero_of_not_dvd h2
      exact ⟨by omega, fun h1 => by omega⟩
  omega5 := by
    intro M hM J _ _ z' hz' v _ _ _ hvz
    obtain ⟨g, -, hzM, hNM⟩ := exists_data_of_mem_omegaPrime ht hY hM
    have e : z' = g * z * g⁻¹ := hz'.eq hzM
    subst e
    exact hNM (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem twinSet_omegaPrime (ht : S19R.TightStd p f K z) (hY : YPrimeData K z Y' Q) :
    twinSet (omegaPrime K Y') K = {K, Y'} := by
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  ext J
  constructor
  · rintro ⟨hJ, z', hz'K, hz'J⟩
    have e1 : z' = z := hz'K.eq hzK
    subst e1
    obtain ⟨g, hJg, hzJ, -⟩ := exists_data_of_mem_omegaPrime ht hY hJ
    have egz : g * z' * g⁻¹ = 1 * z' * 1⁻¹ := by rw [hzJ.eq hz'J]; group
    rcases hJg with rfl | rfl
    · left
      rw [conjSub_eq_of_conj_eq (centralizer_le_normalizer_of_tightD ht) egz, conjSub_one]
    · right
      rw [conjSub_eq_of_conj_eq hY.normal egz, conjSub_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inl (CoreAssembly.mem_conjClass_self J), z, hzK, hzK⟩
    · exact ⟨Or.inr (CoreAssembly.mem_conjClass_self J), z, hzK, hzY⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
