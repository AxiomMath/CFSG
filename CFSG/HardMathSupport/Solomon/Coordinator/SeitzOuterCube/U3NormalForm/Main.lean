module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Classify
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.QuotientCard
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.AssemblyU
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalForm
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitaryStd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF SplitDataU fieldCubeU_standardForm)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three (liftGL ιU liftGL_diagGL
  liftGL_diagGL_foote
  liftGL_monomGL heisCubeU map_conj_sup_zpowers exists_pow_mul_of_mem_sup)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
  (sc monomGL diagGL mem_of_zpow_mem_of_pow_three card_sup_of_commute_disjoint)

theorem u3Three_cube_normal_form {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    (hq2 : 2 < ℓ ^ f) (hq3 : 3 ∣ ℓ ^ f + 1)
    {B : Subgroup (MulAut (unitaryPSU h 3))} (hB : IsElemAbelian 3 B) (hc : Nat.card B = 3 ^ 3) :
    ∃ (α : MulAut (unitaryPSU h 3)) (σ : F ≃+* F), orderOf σ = 3 ∧
      ((∃ A : Subgroup (MulAut (unitaryPSU h 3)),
          SplitDataU h σ A (B.map (MulAut.conj α).toMonoidHom)) ∨
       (∃ (lam ω : Fˣ) (D X : unitaryIsom3 h), σ lam = lam ∧ IsPrimitiveRoot (ω : F) 3 ∧
          (D : GL (Fin 3) F) = diagGL F 1 ω (ω ^ 2) ∧ (X : GL (Fin 3) F) = monomGL F lam ∧
          B.map (MulAut.conj α).toMonoidHom = heisCubeU h σ D X)) := by
  classical
  have hfin : Finite F := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : 3 ∣ Nat.card F - 1 :=
    CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU.three_dvd_card_sub_one h hq3
  have hout : ¬ B ≤ (psuConj h).range := by
    intro hle
    have := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range hK3 B
      hle (fun x hx y hy => congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hB.2
    rw [hc] at this
    norm_num at this
  obtain ⟨g, σ, hσ, hB'eq, hcent⟩ := fieldCubeU_standardForm hq2 B hB hout
  set c : MulAut (unitaryPSU h 3) := psuConj h g with hcdef
  set B' : Subgroup (MulAut (unitaryPSU h 3)) := B.map (MulAut.conj c).toMonoidHom with hB'
  have hB'e : IsElemAbelian 3 B' := CFSG.SectionRank.isElemAbelian_map hB _
  have hB'c : Nat.card B' = 3 ^ 3 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj c).injective, hc]
  set A : Subgroup (MulAut (unitaryPSU h 3)) := B' ⊓ (psuConj h).range with hA
  set fσ : MulAut (unitaryPSU h 3) := psuField h σ with hfσ
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hf3 : fσ ^ 3 = 1 := by rw [hfσ, ← map_pow, hσ3, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hfnl : fσ ∉ (psuConj h).range :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.psuField_not_mem_psuConj_range hσ1
  have hf1 : fσ ≠ 1 := fun h1 => hfnl (h1 ▸ one_mem _)
  have hfA : ∀ a ∈ A, Commute a fσ := by
    intro a ha
    have := (Subgroup.mem_centralizer_iff.1 (hcent ha)) fσ (Set.mem_singleton fσ)
    exact this.symm
  have hof : orderOf fσ = 3 := orderOf_eq_prime hf3 hf1
  have hAc : Nat.card A = 9 := by
    have hdisj : Disjoint (Subgroup.zpowers fσ) A := by
      rw [Subgroup.disjoint_def]
      intro x hxf hxA
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxf
      by_cases h3k : (3 : ℤ) ∣ k
      · exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hof]; exact_mod_cast h3k)
      · exact absurd (mem_of_zpow_mem_of_pow_three hf3 h3k hxA.2) hfnl
    have hcomm : ∀ h ∈ Subgroup.zpowers fσ, ∀ k ∈ A, Commute h k := by
      intro h hh k hk
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact ((hfA k hk).symm).zpow_left i
    have := card_sup_of_commute_disjoint _ _ hcomm hdisj
    rw [← hB'eq, hB'c, Nat.card_zpowers, hof] at this
    omega
  obtain ⟨h₀, hbar⟩ := exists_fixData h hσ
  have h3₀ : 3 ∣ ℓ ^ (f / 3) + 1 := three_dvd_sub_data h hσ hq3
  have hAt_ker := phi_eq_one_iff h h₀ hbar
  set φ : unitaryIsom3 h₀ →* MulAut (unitaryPSU h 3) := phi h h₀ hbar with hφ
  have hφcomm : ∀ M, Commute (φ M) fσ := fun M => (phi_commute h h₀ hbar M).symm
  set Ã : Subgroup (unitaryIsom3 h₀) := A.comap φ with hÃ
  have hAsurj : ∀ a ∈ A, ∃ M : unitaryIsom3 h₀, φ M = a := by
    intro a ha
    exact exists_phi_eq_of_commute h h₀ hbar hσ ha.2 (hfA a ha).symm.eq
  have hAmap : Ã.map φ = A := by
    ext a
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact hM
    · intro ha
      obtain ⟨M, hM⟩ := hAsurj a ha
      exact ⟨M, by show φ M ∈ A; rw [hM]; exact ha, hM⟩
  set At' : Subgroup (GL (Fin 3) (fixF σ)) := Ã.map (unitaryIsom3 h₀).subtype with hAt'
  have hAt'U : At' ≤ unitaryIsom3 h₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAt'S : sc (fixF σ) ⊓ unitaryIsom3 h₀ ≤ At' := by
    rintro x ⟨hxs, hxU⟩
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    show φ ⟨x, hxU⟩ ∈ A
    rw [(hAt_ker ⟨x, hxU⟩).2 hxs]
    exact A.one_mem
  have hAt'cube : ∀ x ∈ At', x ^ 3 ∈ sc (fixF σ) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : φ (y ^ 3) = 1 := by
      rw [map_pow]
      exact hB'e.2 _ (hy : φ y ∈ A).1
    exact (hAt_ker (y ^ 3)).1 h1
  have hAt'comm : ∀ x ∈ At', ∀ y ∈ At', x * y * x⁻¹ * y⁻¹ ∈ sc (fixF σ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 : φ (x * y * x⁻¹ * y⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      have := congrArg Subtype.val
        (hB'e.1.is_comm.comm ⟨φ x, (hx : φ x ∈ A).1⟩ ⟨φ y, (hy : φ y ∈ A).1⟩)
      have h' : φ x * φ y = φ y * φ x := this
      rw [h']
      group
    exact (hAt_ker (x * y * x⁻¹ * y⁻¹)).1 h1
  have hAt'rank : Nat.card (At' ⧸ (sc (fixF σ)).subgroupOf At') = 9 := by
    rw [hAt', hÃ, card_quotient_map_comap (unitaryIsom3 h₀) φ A hAsurj (sc (fixF σ))
      (fun u => hAt_ker u), hAc]
  have conj_key : ∀ g₁ : unitaryIsom3 h₀,
      B.map (MulAut.conj (φ g₁ * c)).toMonoidHom =
        Subgroup.zpowers fσ ⊔ A.map (MulAut.conj (φ g₁)).toMonoidHom := by
    intro g₁
    have e1 : B.map (MulAut.conj (φ g₁ * c)).toMonoidHom =
        B'.map (MulAut.conj (φ g₁)).toMonoidHom := by
      rw [hB', Subgroup.map_map]
      congr 1
    rw [e1, hB'eq]
    exact map_conj_sup_zpowers fσ A _ (hφcomm g₁)
  have hΘQ : ∀ g₁ : unitaryIsom3 h₀,
      A.map (MulAut.conj (φ g₁)).toMonoidHom = (Ã.map (MulAut.conj g₁).toMonoidHom).map φ := by
    intro g₁
    rw [← hAmap, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hΘcomm : ∀ g₁ : unitaryIsom3 h₀, ∀ a ∈ A.map (MulAut.conj (φ g₁)).toMonoidHom,
      Commute a fσ := by
    intro g₁ a ha
    rw [hΘQ] at ha
    obtain ⟨z, -, rfl⟩ := ha
    exact hφcomm z
  have hQmem : ∀ g₁ : unitaryIsom3 h₀, ∀ z : unitaryIsom3 h₀,
      z ∈ Ã.map (MulAut.conj g₁).toMonoidHom ↔
        (z : GL (Fin 3) (fixF σ)) ∈
          At'.map (MulAut.conj (g₁ : GL (Fin 3) (fixF σ))).toMonoidHom := by
    intro g₁ z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : GL (Fin 3) (fixF σ)), ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨x, hx, rfl⟩, hp⟩
      refine ⟨x, hx, Subtype.ext ?_⟩
      exact hp
  rcases pgu3_rank_two_classify_any h₀ h3₀ At' hAt'U hAt'S hAt'cube hAt'comm hAt'rank with
    ⟨g₀, hg₀, hT⟩ | ⟨g₀, hg₀, lam, ω, hω, hD, hX, hH⟩
  ·
    set g₁ : unitaryIsom3 h₀ := ⟨g₀, hg₀⟩ with hg₁
    refine ⟨φ g₁ * c, σ, hσ, Or.inl ⟨A.map (MulAut.conj (φ g₁)).toMonoidHom, ?_⟩⟩
    rw [conj_key g₁]
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB'e.2 a ha.1, map_one]
    · intro a ha
      rw [hΘQ] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨a₁, b₁, c₁, -, -, hdiag⟩ := hT (by
        have := (hQmem g₁ z).1 hz
        exact this)
      have hlift : liftGL σ (z : GL (Fin 3) (fixF σ)) =
          CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL ![ιU σ a₁, ιU σ b₁, ιU σ c₁] := by
        rw [hdiag, liftGL_diagGL_foote]
      have hd : (CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL
          ![ιU σ a₁, ιU σ b₁, ιU σ c₁] : GL (Fin 3) F) ∈ unitaryIsom3 h := by
        rw [← hlift]
        exact (liftU h h₀ hbar z).2
      refine ⟨![ιU σ a₁, ιU σ b₁, ιU σ c₁], hd, ?_⟩
      rw [hφ, phi_apply]
      congr 1
      exact Subtype.ext hlift
    · intro b hb
      exact exists_pow_mul_of_mem_sup hf3 (A := A.map (MulAut.conj (φ g₁)).toMonoidHom)
        (hΘcomm g₁) b hb
  ·
    set g₁ : unitaryIsom3 h₀ := ⟨g₀, hg₀⟩ with hg₁
    set Dk : unitaryIsom3 h₀ := ⟨diagGL (fixF σ) 1 ω (ω ^ 2), hD⟩ with hDk
    set Xk : unitaryIsom3 h₀ := ⟨monomGL (fixF σ) lam, hX⟩ with hXk
    set D : unitaryIsom3 h := liftU h h₀ hbar Dk with hDdef
    set X : unitaryIsom3 h := liftU h h₀ hbar Xk with hXdef
    have hDeq : (D : GL (Fin 3) F) = diagGL F 1 (ιU σ ω) (ιU σ ω ^ 2) := by
      rw [hDdef, coe_liftU]
      change liftGL σ (diagGL (fixF σ) 1 ω (ω ^ 2)) = _
      rw [liftGL_diagGL, map_one, map_pow]
    have hXeq : (X : GL (Fin 3) F) = monomGL F (ιU σ lam) := by
      rw [hXdef, coe_liftU]
      change liftGL σ (monomGL (fixF σ) lam) = _
      rw [liftGL_monomGL]
    refine ⟨φ g₁ * c, σ, hσ, Or.inr ⟨ιU σ lam, ιU σ ω, D, X, ?_, ?_, hDeq, hXeq, ?_⟩⟩
    · exact mem_fixF.1 (lam : fixF σ).2
    · simpa [ιU] using hω.map_of_injective (f := (fixF σ).subtype) Subtype.val_injective
    · rw [conj_key g₁, hΘQ g₁, heisCubeU]
      have hφD : φ Dk = psuConj h D := rfl
      have hφX : φ Xk = psuConj h X := rfl
      rw [← hφD, ← hφX]
      congr 1
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        have hzmem := (hQmem g₁ z).1 hz
        rw [hH] at hzmem
        have key : ∀ w ∈ Subgroup.closure ({monomGL (fixF σ) lam, diagGL (fixF σ) 1 ω (ω ^ 2)} ∪
            ↑(sc (fixF σ) ⊓ unitaryIsom3 h₀)),
            ∃ hw : w ∈ unitaryIsom3 h₀, φ ⟨w, hw⟩ ∈
              Subgroup.zpowers (φ Dk) ⊔ Subgroup.zpowers (φ Xk) := by
          intro w hw
          induction hw using Subgroup.closure_induction with
          | mem w hw =>
            rcases hw with hw | ⟨hws, hwU⟩
            · rcases hw with rfl | rfl
              · exact ⟨hX, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
              · exact ⟨hD, Subgroup.mem_sup_left (Subgroup.mem_zpowers _)⟩
            · refine ⟨hwU, ?_⟩
              rw [(hAt_ker ⟨w, hwU⟩).2 hws]
              exact one_mem _
          | one => exact ⟨one_mem _, by
              have : (⟨1, one_mem _⟩ : unitaryIsom3 h₀) = 1 := rfl
              rw [this, map_one]; exact one_mem _⟩
          | mul a b _ _ ha hb =>
            obtain ⟨haU, ha'⟩ := ha
            obtain ⟨hbU, hb'⟩ := hb
            refine ⟨mul_mem haU hbU, ?_⟩
            have : (⟨a * b, mul_mem haU hbU⟩ : unitaryIsom3 h₀) = ⟨a, haU⟩ * ⟨b, hbU⟩ := rfl
            rw [this, map_mul]
            exact mul_mem ha' hb'
          | inv a _ ha =>
            obtain ⟨haU, ha'⟩ := ha
            refine ⟨inv_mem haU, ?_⟩
            have : (⟨a⁻¹, inv_mem haU⟩ : unitaryIsom3 h₀) = (⟨a, haU⟩ : unitaryIsom3 h₀)⁻¹ := rfl
            rw [this, map_inv]
            exact inv_mem ha'
        obtain ⟨hzU, hzφ⟩ := key _ hzmem
        exact hzφ
      · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · refine ⟨Dk, (hQmem g₁ Dk).2 ?_, rfl⟩
          rw [hH]
          exact Subgroup.subset_closure (Or.inl (Or.inr rfl))
        · refine ⟨Xk, (hQmem g₁ Xk).2 ?_, rfl⟩
          rw [hH]
          exact Subgroup.subset_closure (Or.inl (Or.inl rfl))

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF
