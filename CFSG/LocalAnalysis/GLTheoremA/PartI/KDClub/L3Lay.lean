module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerLay

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.GLTheoremB

section Dichot

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {Y : Type} [Group Y]

theorem dichot_proj_field (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {β : MulAut Y} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    (∃ σ : K ≃+* K, orderOf σ = 3) ∨ InnerAutAt π p f K β := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  set ε : Y ≃* pkg.M := e.trans pkg.η with hε
  have hβ3' : MulAut.congr ε β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  rcases pkg.dich _ hβ3' with hin | ⟨σ, hσ, κ, hκ, hβ'⟩
  · obtain ⟨x, hx, hxs⟩ := pkg.conj_of_inndiag _ hin
    have hxs' : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (e.symm (QuotientGroup.mk s)) = e.symm (QuotientGroup.mk t) := by
      intro s t ht
      have h1 := hxs s t ht
      rw [hε, congr_trans', congr_symm_congr, MulAut.congr_apply] at h1
      rw [← h1]
      simp
    let ν : ↥(slPi π 3 (p ^ f) K) →* Y :=
      e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    have hνker : ∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K := by
      intro s hs
      have h1 : (QuotientGroup.mk s : ↥(slPi π 3 (p ^ f) K) ⧸
          Subgroup.center ↥(slPi π 3 (p ^ f) K)) = 1 :=
        e.symm.injective (by simpa [ν] using hs)
      have h2 : s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := (QuotientGroup.eq_one_iff s).1 h1
      rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hνsurj : Function.Surjective ν := by
      intro y
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e y)
      exact ⟨s, by simp [ν, hs]⟩
    have hνβ : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
        β (ν s) = ν t := fun s t ht => hxs' s t ht
    have hxZ : x ∉ zPi π 3 (p ^ f) K := by
      intro hz
      apply hβ1
      rw [zPi_eq hπ hq' (exists_tau hK hq).choose_spec.1 (exists_tau hK hq).choose_spec.2] at hz
      have hz' := (Subgroup.mem_inf.1 hz).2
      ext y
      obtain ⟨s, rfl⟩ := hνsurj y
      have := commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)
      have h1 := hνβ s s (by
        calc (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * x * x⁻¹ := (mul_inv_cancel_right _ _).symm
          _ = x * s * x⁻¹ := by rw [this])
      simpa using h1
    have hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K := by
      obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
      rw [zPi_eq hπ hq' hτ hτ1]
      refine Subgroup.mem_inf.2 ⟨pow_mem hx 3, ?_⟩
      refine mem_statedScalars_of_comm_mod hK hq hq2 fun s hs => ?_
      let s0 : ↥(slPi π 3 (p ^ f) K) := ⟨s, hs⟩
      let t1 : ↥(slPi π 3 (p ^ f) K) := ⟨x * s0 * x⁻¹, conj_mem_slPi hπ hx s0.2⟩
      let t2 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t1 * x⁻¹, conj_mem_slPi hπ hx t1.2⟩
      let t3 : ↥(slPi π 3 (p ^ f) K) := ⟨x * t2 * x⁻¹, conj_mem_slPi hπ hx t2.2⟩
      have h1 : β (ν s0) = ν t1 := hνβ s0 t1 rfl
      have h2 : β (ν t1) = ν t2 := hνβ t1 t2 rfl
      have h3 : β (ν t2) = ν t3 := hνβ t2 t3 rfl
      have hβν : (β ^ 3) (ν s0) = ν s0 := by rw [hβ3]; rfl
      have h4 : ν s0 = ν t3 := by
        rw [← hβν]
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
        rw [h1, h2, h3]
      exact mem_centMod_of_nu_eq hνker t3 (by
        change x * (x * (x * (s0 : GL (Fin 3) K) * x⁻¹) * x⁻¹) * x⁻¹ = _
        rw [pow_three']
        group) h4
    exact Or.inr ⟨ν, hνsurj, hνker, x, hx, hxZ, hx3, hνβ⟩
  · exact Or.inl ⟨σ, hσ⟩


end Dichot

section Lay

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {Y : Type} [Group Y] [Finite Y]

theorem inner_lay_iso (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {β : MulAut Y} (h : InnerAutAt π p f K β) :
    (∀ J : Subgroup Y, ¬ CFSG.Open.GLAPComponent 3 (fixSub β) J) ∨
      ∃ Φ : ↥(slPi π 2 (p ^ f) K) →* Y, Function.Injective Φ ∧
        ∀ J : Subgroup Y, CFSG.Open.GLAPComponent 3 (fixSub β) J → J = Φ.range := by
  obtain ⟨ν, hνs, hνker, x, hx, hxZ, hx3, hνβ⟩ := h
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨y, ⟨z, hz, hyz⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hx hxZ hx3
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact (Subgroup.mem_inf.1 hz).2
  have hcm : ∀ s : ↥(slPi π 3 (p ^ f) K), ν s ∈ fixSub β →
      ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) y := by
    intro s hs
    rw [hyz, centMod_mul_scalar hzS]
    exact mem_centMod_of_nu_eq hνker ⟨x * s * x⁻¹, conj_mem_slPi hπ hx s.2⟩ rfl
      ((mem_fixSub.1 hs).symm.trans (hνβ s _ rfl))
  have hnone : Group.IsSolvable ↥(centMod (slPi π 3 (p ^ f) K) y) →
      ∀ J : Subgroup Y, ¬ CFSG.Open.GLAPComponent 3 (fixSub β) J := by
    intro hM J hJ
    have hQ := isQuasisimple_quotient_of_glaPComponent hJ
    exact false_of_isSolvable_quotient hQ (isSolvable_of_centMod_solvable J
      (fun j _ => hνs j) (fun s hs => hcm s (hJ.1 hs)) hM)
  rcases hcases with ⟨-, ⟨e⟩, -⟩ | ⟨⟨g, hg, e, he, hge⟩, ⟨e'⟩, hcen⟩ | ⟨-, -, -, hcyc, -, -⟩
  · exact Or.inl (hnone (isSolvable_centMod _ _
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)))
  · right
    have hτ2 : τ ^ 2 ≠ 1 := by
      intro h
      apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, h, div_one]
    have he1 : e ≠ 1 := by
      intro h1
      have h1' : (e : K) = 1 := by rw [h1]; rfl
      rcases he with h | h
      · exact hτ1 (h.symm.trans h1')
      · exact hτ2 (h.symm.trans h1')
    have hyg : y = g * diagE e * g⁻¹ := by
      have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rwa [hge] at this
    let ψ : ↥(glPi π 2 (p ^ f) K) →* ↥(slPi π 3 (p ^ f) K) :=
      { toFun := fun B => ⟨g * blockHom (B : GL (Fin 2) K) * g⁻¹,
          conj_mem_slPi hπ hg (blockHom_mem_slPi hK B.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul, map_mul]; group) }
    have hψy : ∀ B : ↥(glPi π 2 (p ^ f) K),
        ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) * x =
          x * ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) := by
      intro B
      have h1 : ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) * y =
          y * ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) := by
        change g * blockHom (B : GL (Fin 2) K) * g⁻¹ * y =
          y * (g * blockHom (B : GL (Fin 2) K) * g⁻¹)
        rw [hyg]
        calc g * blockHom (B : GL (Fin 2) K) * g⁻¹ * (g * diagE e * g⁻¹)
            = g * (blockHom (B : GL (Fin 2) K) * diagE e) * g⁻¹ := by group
          _ = g * (diagE e * blockHom (B : GL (Fin 2) K)) * g⁻¹ := by
            rw [blockHom_commute e (B : GL (Fin 2) K)]
          _ = g * diagE e * g⁻¹ * (g * blockHom (B : GL (Fin 2) K) * g⁻¹) := by group
      set s := ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) with hs
      have hc := commute_of_mem_statedScalars hzS s
      rw [hyz] at h1
      have h2 : s * x * z = x * s * z := by
        calc s * x * z = s * (x * z) := by rw [mul_assoc]
          _ = x * z * s := h1
          _ = x * (z * s) := by rw [mul_assoc]
          _ = x * (s * z) := by rw [hc]
          _ = x * s * z := by rw [mul_assoc]
      exact mul_right_cancel h2
    let Φ : ↥(glPi π 2 (p ^ f) K) →* Y := ν.comp ψ
    have hFrange : fixSub β = Φ.range := by
      apply le_antisymm
      · intro j hj
        obtain ⟨s, hs⟩ := hνs j
        have hsC := hcm s (by rw [hs]; exact hj)
        rw [hcen] at hsC
        obtain ⟨hsL, hsy⟩ := Subgroup.mem_inf.1 hsC
        have hsy' := Subgroup.mem_centralizer_iff.1 hsy y rfl
        have hsl : g⁻¹ * (s : GL (Fin 3) K) * g ∈ slPi π 3 (p ^ f) K := by
          have := conj_mem_slPi hπ (inv_mem hg) hsL
          simpa using this
        have hce : g⁻¹ * (s : GL (Fin 3) K) * g ∈ Subgroup.centralizer ({diagE e} :
            Set (GL (Fin 3) K)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw, ← hge]
          calc g⁻¹ * y * g * (g⁻¹ * (s : GL (Fin 3) K) * g) = g⁻¹ * (y * s) * g := by group
            _ = g⁻¹ * (s * y) * g := by rw [hsy']
            _ = g⁻¹ * s * g * (g⁻¹ * y * g) := by group
        have hmem : g⁻¹ * (s : GL (Fin 3) K) * g ∈ (glPi π 2 (p ^ f) K).map blockHom := by
          rw [← centralizer_diagE_eq hK he1]
          exact Subgroup.mem_inf.2 ⟨hsl, hce⟩
        obtain ⟨B, hB, hBeq⟩ := hmem
        refine ⟨⟨B, hB⟩, ?_⟩
        show ν (ψ ⟨B, hB⟩) = j
        rw [← hs]
        congr 1
        apply Subtype.ext
        show g * blockHom B * g⁻¹ = s
        rw [hBeq]
        group
      · rintro _ ⟨B, rfl⟩
        show β (ν (ψ B)) = ν (ψ B)
        refine hνβ (ψ B) (ψ B) ?_
        calc ((ψ B : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K)
            = (ψ B : GL (Fin 3) K) * x * x⁻¹ := (mul_inv_cancel_right _ _).symm
          _ = x * (ψ B : GL (Fin 3) K) * x⁻¹ := by rw [hψy B]
    have hFF : ⁅fixSub β, fixSub β⁆ = (commutator ↥(glPi π 2 (p ^ f) K)).map Φ := by
      rw [hFrange]
      change _ = (⁅(⊤ : Subgroup ↥(glPi π 2 (p ^ f) K)), (⊤ : Subgroup ↥(glPi π 2 (p ^ f) K))⁆ :
        Subgroup ↥(glPi π 2 (p ^ f) K)).map Φ
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    have hS2 := isQuasisimple_slPi_two hK hq hq2
    let ι : ↥(slPi π 2 (p ^ f) K) →* ↥(glPi π 2 (p ^ f) K) :=
      Subgroup.inclusion (slPi_le_glPi hπ)
    let Φ2 : ↥(slPi π 2 (p ^ f) K) →* Y := Φ.comp ι
    have hcommle : ∀ a ∈ commutator ↥(glPi π 2 (p ^ f) K), a ∈ ι.range := by
      intro a ha
      have hle : commutator ↥(glPi π 2 (p ^ f) K) ≤
          ((Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).comp
            (glPi π 2 (p ^ f) K).subtype).ker := by
        change (⁅(⊤ : Subgroup ↥(glPi π 2 (p ^ f) K)), (⊤ : Subgroup ↥(glPi π 2 (p ^ f) K))⁆ :
          Subgroup ↥(glPi π 2 (p ^ f) K)) ≤ _
        rw [Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
      have hdet : Matrix.GeneralLinearGroup.det ((a : ↥(glPi π 2 (p ^ f) K)) : GL (Fin 2) K) = 1 :=
        MonoidHom.mem_ker.1 (hle ha)
      have hdet' : (((a : ↥(glPi π 2 (p ^ f) K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = 1 := by
        have := congrArg Units.val hdet
        simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
      exact ⟨⟨(a : GL (Fin 2) K), (mem_slPi_iff hπ).2 ⟨a.2, hdet'⟩⟩, Subtype.ext rfl⟩
    have hΦ2le : Φ2.range ≤ fixSub β := by
      rw [hFrange, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    have hS0 : ⁅fixSub β, fixSub β⁆ = Φ2.range := by
      apply le_antisymm
      · rw [hFF]
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, rfl⟩ := hcommle a ha
        exact ⟨b, rfl⟩
      · have hperf : commutator ↥(slPi π 2 (p ^ f) K) = ⊤ := (Group.isPerfect_def).1 hS2.1
        have h1 : Φ2.range = ⁅Φ2.range, Φ2.range⁆ := by
          calc Φ2.range = (⊤ : Subgroup ↥(slPi π 2 (p ^ f) K)).map Φ2 := MonoidHom.range_eq_map _
            _ = (commutator ↥(slPi π 2 (p ^ f) K)).map Φ2 := by rw [hperf]
            _ = ⁅Φ2.range, Φ2.range⁆ := by
              change (⁅(⊤ : Subgroup ↥(slPi π 2 (p ^ f) K)), (⊤ : Subgroup ↥(slPi π 2 (p ^ f) K))⁆ :
                Subgroup ↥(slPi π 2 (p ^ f) K)).map Φ2 = _
              rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
        rw [h1]
        exact Subgroup.commutator_mono hΦ2le hΦ2le
    have hS2' := hS2
    obtain ⟨-, -, a, b, hab⟩ := hS2
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
    have hA1 : A ≠ 1 := by
      rintro rfl
      apply hab
      simp
    have hΦker : ∀ A : ↥(slPi π 2 (p ^ f) K), Φ2 A = 1 → A = 1 := by
      intro A h1
      have h2 : ψ (ι A) ∈ ν.ker := h1
      obtain ⟨ω, hω⟩ := hνker _ h2
      have hAdet : (((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = 1 := ((mem_slPi_iff hπ).1 A.2).2
      have hdU : Matrix.GeneralLinearGroup.det ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) = 1 :=
        Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hAdet)
      have h3 : g * blockHom ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) * g⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ω := hω.symm
      have hcs := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ω g⁻¹).eq
      have hbl : blockHom ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ω := by
        calc blockHom ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K)
            = g⁻¹ * (g * blockHom ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) * g⁻¹) * g := by
              group
          _ = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) ω * g := by rw [h3]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * g⁻¹ * g := by rw [hcs]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ω := by group
      have h00 := congrArg (fun m : GL (Fin 3) K => (m : Matrix (Fin 3) (Fin 3) K) 0 0) hbl
      simp only [coe_blockHom, blockMat, hdU] at h00
      rw [coe_scalar_eq_smul] at h00
      have hω1 : ω = 1 := Units.ext (by simpa using h00.symm)
      have h4 : blockHom ((A : ↥(slPi π 2 (p ^ f) K)) : GL (Fin 2) K) = 1 := by
        rw [hbl, hω1, map_one]
      exact Subtype.ext (blockHom_injective (h4.trans (map_one blockHom).symm))
    have hΦA : Φ2 A ≠ 1 := fun h1 => hA1 (hΦker A h1)
    have hΦinj : Function.Injective Φ2 := (injective_iff_map_eq_one Φ2).2 hΦker
    have hq0 : CFSG.IsQuasisimple ↥Φ2.range :=
      CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hS2'
        (MonoidHom.rangeRestrict_surjective Φ2)
        ⟨A, fun h => hΦA (by simpa using congrArg Subtype.val h)⟩
    have hqS : CFSG.Open.IsQuasisimple ↥(⁅fixSub β, fixSub β⁆) := by
      rw [hS0]
      exact isQuasisimple_open hq0
    refine ⟨Φ2, hΦinj, fun J hJ => ?_⟩
    have hperf := glaPComponent_perfect hJ
    have hJF : J ≤ fixSub β := hJ.1
    have hJS : J ≤ ⁅fixSub β, fixSub β⁆ := by
      calc J = ⁅J, J⁆ := hperf.symm
        _ ≤ ⁅fixSub β, fixSub β⁆ := Subgroup.commutator_mono hJF hJF
    have hSF : ⁅fixSub β, fixSub β⁆ ≤ fixSub β := by
      rw [hS0]
      exact hΦ2le
    have hsn := isSubnormal_of_le_of_le hJ.2.1 hJS hSF
    rw [← hS0]
    exact eq_of_isSubnormal_of_quasisimple hqS hsn hperf (glaPComponent_ne_bot hJ)
  · exact Or.inl (hnone (isSolvable_centMod _ _ (by have := hcyc; exact inferInstance)))


end Lay

end CFSG.HardMathSupport.Solomon.Coordinator
