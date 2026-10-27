module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i141f_g2_inner {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {L A : Subgroup Γ} {n : ℕ}
    (hcat : catalogIs (PSimple p L) (S10.isG2n n)) (hInn : S10.InnDiagOn p A L) {a : Γ}
    (ha : a ∈ A) :
    ∃ s : PSimple p L, chevAut p L ⟨a, hInn.1 ha⟩ = MulAut.conj s := by
  obtain ⟨hA, hM⟩ := hInn
  obtain ⟨hn2, hD⟩ := HG2Inn.g2Datum_of_marking hcat hM
  have hlab : GLAInLambda2 (⟨.G2, 0, n⟩ : GLALabel) :=
    show 1 ≤ n ∧ (0 = 0 ∧ 2 ≤ n) from ⟨by omega, rfl, hn2⟩
  have hX := rk2_inndiag_subset_inn_of_notDerived hlab (by simp) (by simp) (by simp) (by simp) _ hD
  obtain ⟨R', _, I', F', hQ'⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hX
  obtain ⟨⟨-, -, θ', hP'⟩, hI'⟩ := hQ'
  obtain ⟨φ, hφI, hφ⟩ := hP' a⁻¹ (inv_mem ha)
  obtain ⟨r, rfl⟩ := hI' hφI
  refine ⟨θ'.symm r, ?_⟩
  ext s
  have h := i141f_induces_chevAut θ' (hA (inv_mem ha)) hφ s
  have e : (⟨a⁻¹⁻¹, inv_mem (hA (inv_mem ha))⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
      ⟨a, hA ha⟩ := Subtype.ext (inv_inv a)
  rw [e] at h
  apply θ'.injective
  rw [← h]
  simp [MulAut.conj_apply]

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
