module

public import CFSG.ClassicalInvolution.Asc77.AscCX9W
public import CFSG.ClassicalInvolution.Asc77.AscC5OM30

public section

namespace CFSG.ClassicalInvolution.Asc77.C5P

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

variable {p : ℕ}

theorem diagTriv_iff_of_conj {H : Type} [Group H] {α β : H ≃* H} (h : H)
    (hβ : ∀ b, β b = h * α b * h⁻¹) : CX.DiagTriv p β ↔ CX.DiagTriv p α := by
  constructor
  · intro hb u hu
    obtain ⟨g, hg⟩ := hb u hu
    refine ⟨h⁻¹ * g, ?_⟩
    have e : α u = h⁻¹ * β u * h := by rw [hβ u]; group
    rw [e, hg]
    group
  · intro ha u hu
    obtain ⟨g, hg⟩ := ha u hu
    refine ⟨h * g, ?_⟩
    rw [hβ u, hg]
    group

theorem diagTriv_transport_iff {K S : Type} [Group K] [Group S] (φ : K ≃* S) (R : K ≃* K) :
    CX.DiagTriv p R ↔ CX.DiagTriv p (φ.symm.trans (R.trans φ)) := by
  have hR : φ.trans ((φ.symm.trans (R.trans φ)).trans φ.symm) = R := by
    ext k
    simp
  conv_lhs => rw [← hR]
  exact CX.diagTriv_conj_iff φ _

theorem transport_apply_eq {X K S : Type} [Group X] [Group K] [Group S] {B : Subgroup X}
    (ι : K ≃* B) (e : S ≃* B) (s : X ≃* X) (R : K ≃* K)
    (hR : ∀ k, (ι (R k) : X) = s (ι k)) (f : S → S) (hf : ∀ b, s (e b : X) = (e (f b) : X))
    (b : S) : ((ι.trans e.symm).symm.trans (R.trans (ι.trans e.symm))) b = f b := by
  apply e.injective
  apply Subtype.ext
  rw [← hf b]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]
  rw [hR, MulEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Asc77.C5P

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem om5StabDiag_proved : Om5StabDiag p f := by
  intro K₀ K₀' _ _ L hL s hA hA'
  obtain ⟨Φ, z', a₀, b₀, hD⟩ := hL
  obtain ⟨fr⟩ := C5O.M.exists_frame hD
  have h2 : (2 : GaloisField p f) ≠ 0 := C5O.M.two_ne_zero_gf f hD.odd
  have h5 := C5O.M.five_le_card_gf (p := p) (f := f) hD.five
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  obtain ⟨M, σ, hs⟩ := fr.exists_lift_aut h2 s
  have hi := C5O.M.Frame.lift_longInv h2 h4 fr fr s M σ hs hA.le
  obtain ⟨g, hg, hdet⟩ := C5O.M.exists_gl_blocks M (C5O.M.isBD_gm_of_conjSp_longInv h2 M σ hi)
  have hsk : ∀ (k : Fin 2) (b : SL(2, GaloisField p f)),
      s (fr.ψ (longBlock (GaloisField p f) 2 k b)) =
        fr.ψ (longBlock (GaloisField p f) 2 k (C5O.M.slSemi (g k) σ b)) := by
    intro k b
    rw [hs, C5O.M.conjSp_fieldSp_longBlock_gl M hg σ k b]
  have key : ∀ (k : Fin 2) (B : Subgroup L.X), B = (longRootSp2 (GaloisField p f) 2 k).map fr.ψ →
      ∃ e : SL(2, GaloisField p f) ≃* B,
        ∀ b, (e b : L.X) = fr.ψ (longBlock (GaloisField p f) 2 k b) := by
    intro k B hB
    have hinj : Function.Injective (fr.ψ.comp (longBlock (GaloisField p f) 2 k)) := by
      intro x y hxy
      apply longBlock_injective k
      exact fr.injOn_L h2 k ⟨x, rfl⟩ ⟨y, rfl⟩ hxy
    have hrange : (fr.ψ.comp (longBlock (GaloisField p f) 2 k)).range = B := by
      rw [hB, MonoidHom.range_comp]
      rfl
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun b => rfl⟩
  obtain ⟨e₀, he₀⟩ := key 0 L.A fr.hA
  obtain ⟨e₁, he₁⟩ := key 1 L.A' fr.hA'
  have hα₀ := C5P.transport_apply_eq L.ι e₀ s (TwinGroup.restr s hA) (TwinGroup.restr_apply s hA)
    (C5O.M.slSemi (g 0) σ) (fun b => by rw [he₀, he₀, hsk])
  have hα₁ := C5P.transport_apply_eq L.ι' e₁ s (TwinGroup.restr' s hA')
    (TwinGroup.restr'_apply s hA') (C5O.M.slSemi (g 1) σ) (fun b => by rw [he₁, he₁, hsk])
  have hdet1 : ((g 1 * (g 0)⁻¹ : GL (Fin 2) (GaloisField p f)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p f)).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdet 1, ← hdet 0, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]
  let h' : SL(2, GaloisField p f) := ⟨_, hdet1⟩
  have hh' : Matrix.SpecialLinearGroup.toGL h' = g 1 * (g 0)⁻¹ := Units.ext rfl
  rw [C5P.diagTriv_transport_iff (L.ι.trans e₀.symm) (TwinGroup.restr s hA),
    C5P.diagTriv_transport_iff (L.ι'.trans e₁.symm) (TwinGroup.restr' s hA')]
  refine (C5P.diagTriv_iff_of_conj h' fun b => ?_).symm
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [hα₁, map_mul, map_mul, map_inv, hα₀, hh', C5O.M.slg_slSemi, C5O.M.slg_slSemi]
  group

end CFSG.ClassicalInvolution.Asc77.CX
