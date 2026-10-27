module

public import CFSG.ClassicalInvolution.Asc77.WP3SCSModel

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY
open scoped commutatorElement

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

namespace TwinVertex

variable (V : TwinVertex p f Ω z)

theorem a_sq : V.a * V.a = 1 :=
  mul_self_eq_one_of_orderOf_eq_two V.hMa.orderOf_eq_two

theorem a_ne_one : V.a ≠ 1 := ne_one_of_orderOf_eq_two V.hMa.orderOf_eq_two

theorem u_sq : (V.x * V.y) * (V.x * V.y) = 1 := by
  calc (V.x * V.y) * (V.x * V.y) = V.x * (V.y * V.x) * V.y := by group
    _ = V.x * (V.x * V.y) * V.y := by rw [← V.hxy]
    _ = (V.x * V.x) * (V.y * V.y) := by group
    _ = 1 := by rw [V.hxx, V.hyy, V.a_sq]

theorem comm_au : V.a * (V.x * V.y) = (V.x * V.y) * V.a := by
  have h1 : V.a * V.x = V.x * V.a := by
    rw [← V.hxx]
    group
  have h2 : V.a * V.y = V.y * V.a := by
    rw [← V.hyy]
    group
  calc V.a * (V.x * V.y) = (V.a * V.x) * V.y := by group
    _ = (V.x * V.a) * V.y := by rw [h1]
    _ = V.x * (V.a * V.y) := by group
    _ = V.x * (V.y * V.a) := by rw [h2]
    _ = (V.x * V.y) * V.a := by group

end TwinVertex

theorem XCtx.generation_of_vertex (C : XCtx p f Ω z) (a₁ : Fin C.D.card)
    (hD4 : C.D.tag a₁ ≠ .trialityD4)
    (hothers : ∀ j, j ≠ a₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (hzA1 : ∀ j, (C.D.tag j = .PSL ∧ C.D.rank j = 2) →
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range)
    (V : TwinVertex p f Ω z)
    (hMF : TwinMFGeneration p (C.D.exp a₁) (C.D.tag a₁) (C.D.rank a₁))
    (hu1 : V.x * V.y ≠ 1) (huz : V.x * V.y ≠ z) (hua : V.x * V.y ≠ V.a)
    (hauz : V.a * (V.x * V.y) ≠ z) :
    CentralizerGenerationStar Ω (Subgroup.closure ({V.a, V.x * V.y, z} : Set G)) z := by
  classical
  set B : Subgroup G := Subgroup.closure ({V.a, V.x * V.y, z} : Set G) with hB
  have hz1 : z ≠ 1 := C.hKz.ne_one
  have hz2 : z * z = 1 := C.hKz.sq
  have hzC := XCtx.hzC z
  have hcg : ∀ s ∈ ({V.a, V.x * V.y, z} : Set G), ∀ s' ∈ ({V.a, V.x * V.y, z} : Set G),
      s * s' = s' * s := by
    have haz : V.a * z = z * V.a := Subgroup.mem_centralizer_singleton_iff.mp V.a_mem
    have huz' : (V.x * V.y) * z = z * (V.x * V.y) :=
      Subgroup.mem_centralizer_singleton_iff.mp V.u_mem
    intro s hs s' hs'
    rcases hs with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
    · rfl
    · exact V.comm_au
    · exact haz
    · exact V.comm_au.symm
    · rfl
    · exact huz'
    · exact haz.symm
    · exact huz'.symm
    · rfl
  have hsq : ∀ s ∈ ({V.a, V.x * V.y, z} : Set G), s * s = 1 := by
    intro s hs
    rcases hs with rfl | rfl | rfl
    · exact V.a_sq
    · exact V.u_sq
    · exact hz2
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := ChainFrame.commutes_closure hcg
  have hB2 : ∀ x ∈ B, x * x = 1 := ChainFrame.sq_closure hsq hcg
  have haB : V.a ∈ B := Subgroup.subset_closure (by simp)
  have huB : V.x * V.y ∈ B := Subgroup.subset_closure (by simp)
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have hBz : B ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hB, Subgroup.closure_le]
    rintro s (rfl | rfl | rfl)
    · exact V.a_mem
    · exact V.u_mem
    · exact hzC
  have hxY : V.x ∈ exactLayer Ω z := exactCore_le_exactLayer V.hM V.hx
  have hyY : V.y ∈ exactLayer Ω z := exactCore_le_exactLayer V.hM' V.hy
  have hBY : B ≤ exactLayer Ω z := by
    rw [hB, Subgroup.closure_le]
    rintro s (rfl | rfl | rfl)
    · rw [← V.hxx]
      exact mul_mem hxY hxY
    · exact mul_mem hxY hyY
    · exact C.z_mem_exactLayer
  set H : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 B,
    (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) with hH
  have hlift : ∀ {e : G} (heB : e ∈ B) (he1 : e ≠ 1) (hez : e ≠ z) (heC : e ∈ Subgroup.centralizer
      ({z} : Set G)) {q : OddQuot z}, q ∈ memberJoin (exactFamily Ω z) z →
      q * oddQuotMk z ⟨e, heC⟩ = oddQuotMk z ⟨e, heC⟩ * q → q ∈ modOdd z H := by
    intro e heB he1 hez heC q hq hc
    exact mem_modOdd_of_commutes_frame hBc hB2 hzB hz1 hBz hBY heB he1 hez hq fun he =>
      hc.symm
  have hua1 : V.a * (V.x * V.y) ≠ 1 := by
    intro h
    apply hua
    have h2 := congrArg (fun w => V.a * w) h
    simp only [mul_one] at h2
    calc V.x * V.y = V.a * (V.a * (V.x * V.y)) := by
          rw [← mul_assoc, V.a_sq, one_mul]
      _ = V.a := by rw [h, mul_one]
  have hauB : V.a * (V.x * V.y) ∈ B := mul_mem haB huB
  have hauC : V.a * (V.x * V.y) ∈ Subgroup.centralizer ({z} : Set G) := mul_mem V.a_mem V.u_mem
  refine centralizerGenerationStar_of_images C.hs.normalizes (B := B) ?_
  intro N hN y hy hyC
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hN
  have hymem : oddQuotMk z ⟨y, hyC⟩ ∈ R.map (C.psi j) := hmod ▸ oddQuotMk_mem_modOdd hy hyC
  by_cases hj : j = a₁
  · subst hj
    obtain ⟨R₀, R₀', x, x', ã, ã', hdat, hã, hã', hsq1, hsq2, hxψ, -, hũψ⟩ :=
      C.exists_modelDatum j hD4 hothers hzA1 V
    have hgen := hMF R₀ R₀' x x' hdat ã hã ã' hã' hsq1 hsq2 R hR
    obtain ⟨r, hrR, hr⟩ := hymem
    rw [← hr]
    have hcent : ∀ (w : (compModel C.D j).K) (e : G) (heB : e ∈ B) (he1 : e ≠ 1) (hez : e ≠ z)
        (heC : e ∈ Subgroup.centralizer ({z} : Set G)),
        C.psi j w = oddQuotMk z ⟨e, heC⟩ →
        ∀ c ∈ Subgroup.centralizer ({w} : Set (compModel C.D j).K), C.psi j c ∈ modOdd z H := by
      intro w e heB he1 hez heC hw c hc
      refine hlift heB he1 hez heC (C.psi_mem_memberJoin j c) ?_
      rw [← hw, ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    have h1 : (Subgroup.centralizer ({x} : Set (compModel C.D j).K)).map (C.psi j) ≤
        modOdd z H := by
      rintro _ ⟨c, hc, rfl⟩
      exact hcent x V.a haB V.a_ne_one V.haz V.a_mem hxψ c hc
    have h2 : (Subgroup.centralizer ({ã * ã'} : Set (compModel C.D j).K)).map (C.psi j) ≤
        modOdd z H := by
      rintro _ ⟨c, hc, rfl⟩
      exact hcent (ã * ã') (V.x * V.y) huB hu1 huz V.u_mem hũψ c hc
    have h3 : (Subgroup.centralizer ({x * (ã * ã')} : Set (compModel C.D j).K)).map
        (C.psi j) ≤ modOdd z H := by
      rintro _ ⟨c, hc, rfl⟩
      refine hcent (x * (ã * ã')) (V.a * (V.x * V.y)) hauB hua1 hauz hauC ?_ c hc
      rw [map_mul, hxψ, hũψ, ← map_mul]
      rfl
    have hsup : (Subgroup.centralizer ({x} : Set (compModel C.D j).K) ⊔
        Subgroup.centralizer ({ã * ã'} : Set (compModel C.D j).K) ⊔
        Subgroup.centralizer ({x * (ã * ã')} : Set (compModel C.D j).K)).map (C.psi j) ≤
        modOdd z H := by
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le h1 h2) h3
    exact hsup (Subgroup.mem_map_of_mem _ (hgen hrR))
  · have hA := hothers j hj
    have hRtop : R = ⊤ := C.fund_eq_top j hA hR
    rw [hRtop, Subgroup.map_top] at hymem
    obtain ⟨R₀, R₀', x, x', ã, ã', hdat, hã, hã', hsq1, hsq2, hxψ, -, hũψ⟩ :=
      C.exists_modelDatum a₁ hD4 hothers hzA1 V
    obtain ⟨r, hr⟩ := hymem
    rw [← hr]
    refine hlift haB V.a_ne_one V.haz V.a_mem (C.psi_mem_memberJoin j r) ?_
    rw [← hxψ]
    exact C.psi_commute hj r x

end Gen

end CFSG.ClassicalInvolution.Asc77
