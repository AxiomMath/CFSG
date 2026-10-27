module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Invol

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.Blueprint

structure Model28 (K : Type*) [Group K] where
  e : K ≃* ↥QP.originalSubgroup
  Φ : MulAut K ≃* ↥QA.originalSubgroup
  spec : ∀ (φ : MulAut K) (x : K),
    ((e (φ x) : ↥QP.originalSubgroup) : Pm) =
      (Φ φ : Pm) * (e x : Pm) * (Φ φ : Pm)⁻¹

theorem exists_model28
    {K : Type} [Group K] (h : LieModel K .PSU 3 3 1) :
    Nonempty (Model28 K) := by
  obtain ⟨e0⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.U33.autModel e0
  exact ⟨{ e := M.e.trans (MulEquiv.subgroupCongr hP)
           Φ := M.Φ.trans (MulEquiv.subgroupCongr hA)
           spec := by
             intro φ x
             simpa [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply] using M.spec φ x }⟩

theorem centA_trivial :
    ∀ σ ∈ QA.originalSubgroup, (∀ x ∈ QP.originalSubgroup, σ * x = x * σ) → σ = 1 := by
  intro σ hσ hc
  obtain ⟨-, -, -, ⟨hu, hv, -, -⟩, -, -, -, -, -, -, -, -, -, -, hcent, -⟩ :=
    Certificates.certificate5133
  rw [QA_closure] at hσ
  rw [QP_closure] at hc
  exact hcent σ hσ (hc pu hu) (hc pv hv)

section Model

variable {K : Type*} [Group K] (m : Model28 K)

@[expose] def Model28.ε : K →* Pm := QP.originalSubgroup.subtype.comp m.e.toMonoidHom

@[expose] def Model28.ι : MulAut K →* Pm := QA.originalSubgroup.subtype.comp m.Φ.toMonoidHom

include m

theorem Model28.ε_injective : Function.Injective m.ε := by
  intro a b h
  exact m.e.injective (Subtype.val_injective (by simpa [Model28.ε] using h))

theorem Model28.ι_injective : Function.Injective m.ι := by
  intro a b h
  exact m.Φ.injective (Subtype.val_injective (by simpa [Model28.ι] using h))

theorem Model28.ε_mem (k : K) : m.ε k ∈ QP.originalSubgroup := by
  exact (m.e k).2

theorem Model28.ι_mem (φ : MulAut K) : m.ι φ ∈ QA.originalSubgroup := by
  exact (m.Φ φ).2

theorem Model28.exists_ε {p : Pm} (hp : p ∈ QP.originalSubgroup) : ∃ k : K, m.ε k = p := by
  exact ⟨m.e.symm ⟨p, hp⟩, by simp [Model28.ε]⟩

theorem Model28.ε_apply (φ : MulAut K) (x : K) :
    m.ε (φ x) = m.ι φ * m.ε x * (m.ι φ)⁻¹ := by
  simpa [Model28.ε, Model28.ι] using m.spec φ x

theorem Model28.ι_conj (k : K) : m.ι (MulAut.conj k) = m.ε k := by
  have hσA : m.ι (MulAut.conj k) ∈ QA.originalSubgroup := m.ι_mem _
  have hkA : m.ε k ∈ QA.originalSubgroup := P_le_A (m.ε_mem k)
  have hcA : (m.ε k)⁻¹ * m.ι (MulAut.conj k) ∈ QA.originalSubgroup :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkA) hσA
  have hcomm : ∀ x ∈ QP.originalSubgroup,
      (m.ε k)⁻¹ * m.ι (MulAut.conj k) * x
        = x * ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := m.exists_ε hx
    have hspec := m.ε_apply (MulAut.conj k) y
    rw [MulAut.conj_apply] at hspec
    rw [map_mul, map_mul, map_inv] at hspec
    have hkey : m.ε k * m.ε y * (m.ε k)⁻¹
        = m.ι (MulAut.conj k) * m.ε y * (m.ι (MulAut.conj k))⁻¹ := hspec
    have h1 : ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) * m.ε y
        * ((m.ε k)⁻¹ * m.ι (MulAut.conj k))⁻¹ = m.ε y := by
      calc ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) * m.ε y
            * ((m.ε k)⁻¹ * m.ι (MulAut.conj k))⁻¹
          = (m.ε k)⁻¹ * (m.ι (MulAut.conj k) * m.ε y
              * (m.ι (MulAut.conj k))⁻¹) * (m.ε k) := by group
        _ = (m.ε k)⁻¹ * (m.ε k * m.ε y * (m.ε k)⁻¹) * (m.ε k) := by rw [← hkey]
        _ = m.ε y := by group
    calc ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) * m.ε y
          = (((m.ε k)⁻¹ * m.ι (MulAut.conj k)) * m.ε y
              * ((m.ε k)⁻¹ * m.ι (MulAut.conj k))⁻¹)
            * ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) := by group
        _ = m.ε y * ((m.ε k)⁻¹ * m.ι (MulAut.conj k)) := by rw [h1]
  have hc1 : (m.ε k)⁻¹ * m.ι (MulAut.conj k) = 1 := centA_trivial _ hcA hcomm
  have h2 : m.ι (MulAut.conj k) = m.ε k := by
    have := congrArg (fun z => m.ε k * z) hc1
    simpa [mul_assoc] using this
  exact h2

theorem Model28.card_K : Nat.card K = 6048 := by
  rw [Nat.card_congr m.e.toEquiv, card_P]

theorem Model28.card_aut : Nat.card (MulAut K) = 12096 := by
  rw [Nat.card_congr m.Φ.toEquiv, card_A]

end Model

end CFSG.OddStandard.SmallF3.HarrisU33.K28
