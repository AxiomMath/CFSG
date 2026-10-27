module

public import CFSG.ClassicalInvolution.Asc77.AscS24BHAlpha
public import CFSG.ClassicalInvolution.Asc77.AscS24Cent

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem le_centralizer_of_tq {M : Subgroup G} {c : G} (hc2 : c * c = 1)
    (hcM : c ∈ trivialOnQuot M)
    (hO : oddCoreIn M ≤ Subgroup.centralizer ({c} : Set G)) :
    M ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  have ho : ⁅c, x⁆ ∈ oddCoreIn M := hcM.2 x hx
  have hoc : ⁅c, x⁆ * c = c * ⁅c, x⁆ := Subgroup.mem_centralizer_singleton_iff.mp (hO ho)
  have hdef : c * x * c⁻¹ = ⁅c, x⁆ * x := by rw [commutatorElement_def]; group
  have hcoc : c * ⁅c, x⁆ * c⁻¹ = ⁅c, x⁆ := by rw [← hoc]; group
  have h2 : ⁅c, x⁆ * ⁅c, x⁆ * x = x := by
    calc ⁅c, x⁆ * ⁅c, x⁆ * x = ⁅c, x⁆ * (⁅c, x⁆ * x) := by group
      _ = (c * ⁅c, x⁆ * c⁻¹) * (c * x * c⁻¹) := by rw [hcoc, hdef]
      _ = c * (c * x * c⁻¹) * c⁻¹ := by rw [hdef]; group
      _ = (c * c) * x * (c * c)⁻¹ := by group
      _ = x := by rw [hc2]; group
  have hoo : ⁅c, x⁆ * ⁅c, x⁆ = 1 := mul_eq_right.mp h2
  have ho1 : ⁅c, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) ho (isPGroup_zpowers_of_sq_eq_one hoo)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h3 : c * x * c⁻¹ = x := by rw [hdef, ho1, one_mul]
  calc x * c = c * x * c⁻¹ * c := by rw [h3]
    _ = c * x := by group

omit [Finite G] in
theorem conjSub_le_centralizer {M : Subgroup G} {n c : G}
    (hM : M ≤ Subgroup.centralizer ({c} : Set G)) (hn : n * c = c * n) :
    conjSub n M ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : n⁻¹ * x * n * c = c * (n⁻¹ * x * n) := Subgroup.mem_centralizer_singleton_iff.mp (hM hx)
  have hn' : n⁻¹ * c = c * n⁻¹ := by
    calc n⁻¹ * c = n⁻¹ * (c * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * c) * n⁻¹ := by rw [hn]
      _ = c * n⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * c = n * (n⁻¹ * x * n) * (n⁻¹ * c) := by group
    _ = n * (n⁻¹ * x * n) * (c * n⁻¹) := by rw [hn']
    _ = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = (n * c) * (n⁻¹ * x * n) * n⁻¹ := by group
    _ = (c * n) * (n⁻¹ * x * n) * n⁻¹ := by rw [hn]
    _ = c * x := by group

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

theorem closure_za_le_B : Subgroup.closure ({z, H.a} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h <;> rw [h]
  exacts [H.z_mem_B, H.a_mem_B]

theorem closure_ja_le_B : Subgroup.closure ({H.C.D.F.j, H.a} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h <;> rw [h]
  exacts [H.j_mem_B, H.a_mem_B]

theorem closure_za : IsElemAbelian2 (Subgroup.closure ({z, H.a} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair H.C.hzK.sq H.ha2 H.C.hzK.ne_one H.ha1 H.a_ne_z.symm H.comm_z

theorem closure_ja : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, H.a} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair H.C.hjJ.sq H.ha2 H.C.hjJ.ne_one H.ha1 H.a_ne_j.symm H.comm_j

theorem a_mem_centralizer_Oz [IsSimpleGroup G] :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf
    (H.alphaOf_eq_bot _ H.closure_za_le_B H.closure_za) (Subgroup.subset_closure (by simp))
    H.C.hzK.ne_one (Subgroup.subset_closure (by simp))

theorem a_mem_centralizer_Oj [IsSimpleGroup G] :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({H.C.D.F.j} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf
    (H.alphaOf_eq_bot _ H.closure_ja_le_B H.closure_ja) (Subgroup.subset_closure (by simp))
    H.C.hjJ.ne_one (Subgroup.subset_closure (by simp))

theorem le_of_member [IsSimpleGroup G] {M : Subgroup G} (hM : M ∈ Ω) {b : G}
    (hb : IsUniqueInvolution M b) (hbzj : b = z ∨ b = H.C.D.F.j)
    (haM : H.a ∈ trivialOnQuot M) : M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  refine le_centralizer_of_tq H.ha2 haM fun x hx => ?_
  have hsub := T7A.isSubnormal_centralizer H.C.hs.stand.hyp hM hb
  have hxO := oddCoreIn_le_of_isSubnormal hsub hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hbzj with rfl | rfl
  · exact Subgroup.mem_centralizer_iff.mp H.a_mem_centralizer_Oz x hxO
  · exact Subgroup.mem_centralizer_iff.mp H.a_mem_centralizer_Oj x hxO

theorem K_le [IsSimpleGroup G] : K ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.C.hs.stand.mem H.C.hzK (Or.inl rfl) (H.K_tq H.a H.ha2 H.haR).2

theorem K'_le [IsSimpleGroup G] : K' ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.C.hs.hK'.1 H.C.hzK' (Or.inl rfl) (H.K'_tq H.a H.ha2 H.haR').2

theorem J_le [IsSimpleGroup G] : H.C.D.F.ρ₃.K ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.C.D.F.ρ₃.hK H.C.hjJ (Or.inr rfl) (H.J_tq H.a H.ha2 H.hTa).2

theorem Js_le [IsSimpleGroup G] : H.Js ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.Js_mem H.hjJs (Or.inr rfl) (H.Js_tq H.a H.ha2 H.Ts_le).2

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
