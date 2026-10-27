module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Slot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitE4
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] def E4Sp6FrameModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M], CFSG.Blueprint.LieModel M .PSp 3 2 1 →
    ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∀ K' ∈ CoreAssembly.conjClass K, K' ≠ K → K' ≤ Subgroup.normalizer (K : Set M) →
        ∀ u₁ ∈ K, ∀ u₂ ∈ K', u₁ * u₁ = s → u₂ * u₂ = s → ∀ g : M, g * s * g⁻¹ ≠ u₁ * u₂

section TwinE4

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem false_of_twinFrame_twinE4 (hO8 : E4O8TwinModel) (hSp : E4Sp6FrameModel)
    (hS : Q8Section X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z) (hTO : TwinOnlyNbr Φ)
    (hE : TwinE4 X) {A A' B : Subgroup X} {z u₁ u₂ τ ε : X}
    (F : TwinFrame Φ A A' B z u₁ u₂ τ ε) (hnbr : A' ∈ omegaNbr Φ A) : False := by
  have hΩ := hS.hyp
  have hgen := hS.gen
  have hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2) := fun J hJ =>
    hS.q8 J hJ J (TL4.Vtx.isSylow2In_self (h2 J hJ))
  obtain ⟨Q, hQ, f, hfs, hker2, hM⟩ := hE
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := fun J hJ u hu huN =>
    hno J hJ u hu ⟨f.ker, inferInstance, hker2, huN⟩
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot h2 hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ h2 hgen hker2 hmeet
  have hc : CentQuotGen Φ f.ker := centQuotGen hΩ h2 hNc hmeet
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : ExLie (X ⧸ f.ker) :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  obtain ⟨hq8A, hinvA, htwA⟩ := twinDatum_quot hΩ h2 hq8 hNc hmeet F.hA F.hzA
  have hΦ : Φ = CoreAssembly.conjClass A := by
    ext J
    constructor
    · intro hJ
      exact htrans A F.hA J hJ
    · rintro ⟨g, rfl⟩
      exact hΩ.conjInvariant g A F.hA
  have hnbr_iff : ∀ J, J ∈ omegaNbr Φ A ↔
      J ∈ Φ ∧ J ≠ A ∧ J ≤ Subgroup.normalizer (A : Set X) := by
    intro J
    have := TL4.Vtx.mem_omegaNbr_conjClass_iff (K₀ := A) (K := A) (J := J) (h2 A F.hA)
    rw [← hΦ] at this
    exact this
  have hmapC : ∀ y : X, (conjSub y A).map (QuotientGroup.mk' f.ker) =
      conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) :=
    fun y => AscQuot.map_conjSub _ _ _
  obtain ⟨hA'Φ, hA'A, hA'N⟩ := (hnbr_iff A').mp hnbr
  rcases hMq with hSpM | hO8M
  ·
    have hZ : Subgroup.center (X ⧸ f.ker) = ⊥ := by
      have : IsSimpleGroup (X ⧸ f.ker) := TL4.Vtx.isSimpleGroup_of_exLie (Or.inl hSpM)
      exact center_eq_bot_of_quat hq8A
    have hA'conj : A'.map (QuotientGroup.mk' f.ker) ∈
        CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)) := by
      obtain ⟨g, rfl⟩ := htrans A F.hA A' hA'Φ
      exact ⟨QuotientGroup.mk' f.ker g, (hmapC g).symm⟩
    have hA'ne : A'.map (QuotientGroup.mk' f.ker) ≠ A.map (QuotientGroup.mk' f.ker) :=
      fun h => hA'A (hc.eq_of_map A' hA'Φ A F.hA h)
    have hA'le : A'.map (QuotientGroup.mk' f.ker) ≤
        Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := by
      rintro _ ⟨b, hb, rfl⟩
      rw [mem_normalizer_iff_conjSub_eq, ← hmapC b, mem_normalizer_iff_conjSub_eq.mp (hA'N hb)]
    have hε1 : QuotientGroup.mk' f.ker ε = 1 := by
      have hmem : QuotientGroup.mk' f.ker ε ∈ Subgroup.center (X ⧸ f.ker) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective f.ker y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp F.he x]
      rw [hZ] at hmem
      exact hmem
    obtain ⟨g, hg⟩ := htrans A F.hA B F.hB
    have hτ : g * z * g⁻¹ = τ := by
      have h1 := F.hzA.conj g
      rw [hg] at h1
      exact F.htB.eq h1 |>.symm
    refine hSp (X ⧸ f.ker) hSpM (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z)
      hq8A hinvA htwA _ hA'conj hA'ne hA'le (QuotientGroup.mk' f.ker u₁)
      (Subgroup.mem_map_of_mem _ F.h₁) (QuotientGroup.mk' f.ker u₂)
      (Subgroup.mem_map_of_mem _ F.h₂) ?_ ?_ (QuotientGroup.mk' f.ker g) ?_
    · rw [← map_mul, F.o₁]
    · rw [← map_mul, F.o₂]
    · rw [← map_inv, ← map_mul, ← map_mul, hτ, F.hrel, map_mul, hε1, mul_one, map_mul]
  ·
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁A, hJ₂A, hJ₁₂, hn₁, hn₂⟩ :=
      hO8 (X ⧸ f.ker) hO8M (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) hq8A
        hinvA htwA
    have lift : ∀ J ∈ CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)),
        J ≠ A.map (QuotientGroup.mk' f.ker) →
        J ≤ Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) →
          ∃ B' ∈ omegaNbr Φ A, B'.map (QuotientGroup.mk' f.ker) = J := by
      rintro J ⟨h, rfl⟩ hne hle
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
      have hne' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≠
          A.map (QuotientGroup.mk' f.ker) := hne
      have hle' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≤
          Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := hle
      refine ⟨conjSub y A, (hnbr_iff _).mpr ⟨hΩ.conjInvariant y A F.hA, ?_, ?_⟩, hmapC y⟩
      · intro hyA
        apply hne'
        rw [← hmapC, hyA]
      · intro b hb
        refine hc.normalizer_of_map A F.hA b (hle' ?_)
        rw [← hmapC]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨B₁, hB₁, hB₁J⟩ := lift J₁ hJ₁ hJ₁A hn₁
    obtain ⟨B₂, hB₂, hB₂J⟩ := lift J₂ hJ₂ hJ₂A hn₂
    exact hJ₁₂ (by rw [← hB₁J, ← hB₂J, hTO A F.hA B₁ hB₁ B₂ hB₂])

end TwinE4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M
