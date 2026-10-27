module

public import CFSG.GH74.Generic.BProg.B3.S3Rk2Basic
public import CFSG.GH74.Generic.BProg.B3.S3Rk2Conj
public import CFSG.GH74.Generic.BProg.B3.S3L3Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

namespace S3Rk2Lemma316

variable {G : Type} [Group G] [Finite G]

theorem lemma316_of_N {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y)
    (hN : ∀ g ∈ normalizer (A : Set G), g * x = x * g) {g : G} (hgx : g * x * g⁻¹ = x * y) :
    ¬ A.map (MulAut.conj g).toMonoidHom ≤ K ⊔ CxK x K := by
  classical
  intro hle
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ h.circ
  have hx2 : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ h.circ
  have d : S3Rk2Basic.KCData x K := ⟨hK, hx2, h.shape, h.rank1⟩
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hxK⟩ := S3Rk1Basic.exists_E h.circ h.src h.shape
  obtain ⟨-, hAel, hA8, -⟩ := h.src
  have hBel : CFSG.IsElementaryAbelian 2 ↥(A.map (MulAut.conj g).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map (p := 2) (A := A) (MulAut.conj g).toMonoidHom
  have hB8 : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA8]
  obtain ⟨hxB, hFel, hF4, hBeq⟩ := S3Rk2Basic.KCData.elemAb_le_sup d hle hBel hB8
  obtain ⟨k, hkK, hkmap⟩ := S3Rk2Conj.exists_conj_four h.shape hEK
    (inf_le_right : A.map (MulAut.conj g).toMonoidHom ⊓ K ≤ K) hEel hE4 hFel hF4
  have hKx : ∀ k ∈ K, k * x = x * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
  have hkxk : k * x * k⁻¹ = x := by
    rw [hKx k hkK]; group
  have hmapA : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom = A := by
    have hkx' : (MulAut.conj k).toMonoidHom x = x := by simpa [MulAut.conj_apply] using hkxk
    rw [hBeq, Subgroup.map_sup, hkmap, hAE, MonoidHom.map_zpowers, hkx']
  have hnorm : k * g ∈ normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc A.map (MulAut.conj (k * g)).toMonoidHom
        = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
      _ = A := hmapA
  have hcomm := hN (k * g) hnorm
  have hgcomm : g * x = x * g := by
    have h1 : k * (g * x) = k * (x * g) := by
      calc k * (g * x) = k * g * x := by group
        _ = x * (k * g) := hcomm
        _ = (x * k) * g := by group
        _ = (k * x) * g := by rw [← hKx k hkK]
        _ = k * (x * g) := by group
    exact mul_left_cancel h1
  have hy : x * y = x := by
    calc x * y = g * x * g⁻¹ := hgx.symm
      _ = x := by rw [hgcomm]; group
  have hy1 : y = 1 := mul_eq_left.1 hy
  have hy2 := h.y_ord
  rw [hy1, orderOf_one] at hy2
  omega

end S3Rk2Lemma316

end CFSG.GH74.Generic.BProg.B3
