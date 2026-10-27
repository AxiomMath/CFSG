module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngH
public import CFSG.ClassicalInvolution.Asc77.AscS24BHCent

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

namespace Ctx8Frame

theorem mem_closure_of_mem_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w ∈ Subgroup.closure ({C.D.F.j, z} : Set G) := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.mul_nf] at h2
  obtain ⟨h1, h3⟩ := C.eq_one_of_nf _ _ h2
  have ha := C.four_dvd_of_x₁ h1
  have hb := C.four_dvd_of_x₃ h3
  obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
  have e1 : C.D.x₁ ^ (2 : ℤ) = z := by rw [zpow_two, ← sq, C.x₁_sq]
  have e3 : C.D.x₃ ^ (2 : ℤ) = C.D.F.j := by rw [zpow_two, ← sq, C.x₃_sq]
  rw [zpow_mul, zpow_mul, e1, e3]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem u_cases : u = C.D.F.j ∨ u = C.D.F.j * z := by
  obtain ⟨-, huW, hu2, hu1, huz⟩ := C.hd.hu
  rcases T7B.mem_closure_pair C.hjJ.sq C.hzK.sq C.hjJ.ne_one C.hzK.ne_one C.comm_jz
    (C.mem_closure_of_mem_W huW hu2) with h | h | h | h
  · exact absurd h hu1
  · exact Or.inl h
  · exact absurd h huz
  · exact Or.inr h

theorem r_conj_jz : C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹ = C.D.F.j := by
  have hrz : C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem C.hzK C.r_mem_K).symm]; group
  calc C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹
      = (C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹) := by group
    _ = C.D.F.j := by rw [C.r_conj_j, hrz, mul_assoc, C.hzK.sq, mul_one]


theorem r_mem_centralizer_z : C.D.F.ρ.r ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem C.hzK C.r_mem_K).symm

end Ctx8Frame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame


theorem T_card : Nat.card ↥H.T₃ = 2 * Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := by
  rw [IsSylow2In.natCard_eq H.hT H.C.D.F.ρ₃.hRK]
  have h := Q3CL.Thompson.D_card H.C.D.c.hΩ H.C.D.c.hW H.C.D.F.ρ₃.hR
  rw [← H.C.D.h₃] at h
  exact h


theorem exists_s : ∃ s ∈ H.T₃, s ∉ Subgroup.zpowers H.C.D.x₃ := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : H.T₃ ≤ Subgroup.zpowers H.C.D.x₃)
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := Nat.card_pos
  have := H.T_card
  omega

theorem s_not_comm_z {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s * z * s⁻¹ ≠ z := by
  intro h
  apply H.not_le_centralizer_z
  have hzs : z * s = s * z := by
    calc z * s = s * z * s⁻¹ * s := by rw [h]
      _ = s * z := by group
  have hzx : z * H.C.D.x₃ = H.C.D.x₃ * z :=
    Q3CL.Thompson.commutes_of_mem_WSet H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
      H.C.D.x₃_mem
  exact commute_of_index_two (Subgroup.zpowers_le.mpr H.x₃_mem_T) H.T_card hs hsU hzx hzs

theorem s_conj_z_cases {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s * z * s⁻¹ = H.C.D.F.j ∨ s * z * s⁻¹ = H.C.D.F.j * z := by
  have hsW : s * z * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (H.hTN hs) z).mp H.C.hd.hzW
  have h2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
    calc s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
      _ = 1 := by rw [H.C.hzK.sq]; group
  rcases T7B.mem_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one H.C.comm_jz
    (H.C.mem_closure_of_mem_W hsW h2) with h | h | h | h
  · exfalso
    apply H.C.hzK.ne_one
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact absurd h (H.s_not_comm_z hs hsU)
  · exact Or.inr h

theorem s_mem_normalizer_B {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s ∈ Subgroup.normalizer (H.B : Set G) := by
  have hsj : s * H.C.D.F.j * s⁻¹ = H.C.D.F.j := by
    rw [(e189_commute_of_mem H.C.hjJ (H.hT.1 hs)).symm]; group
  have hsa : s * H.a * s⁻¹ = H.a := by rw [H.comm_T hs]; group
  refine mem_normalizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  · have e : s * (H.C.D.F.j * H.a) * s⁻¹ = (s * H.C.D.F.j * s⁻¹) * (s * H.a * s⁻¹) := by group
    rw [e, hsj, hsa]
    exact H.ja_mem_B
  · rw [hsj]
    exact H.j_mem_B
  · rcases H.s_conj_z_cases hs hsU with h' | h' <;> rw [h']
    · exact H.j_mem_B
    · exact H.B.mul_mem H.j_mem_B H.z_mem_B


theorem closure_jz_le_B : Subgroup.closure ({H.C.D.F.j, z} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h <;> rw [h]
  exacts [H.j_mem_B, H.z_mem_B]


theorem closure_jz : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, z} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one
    H.C.z_ne_j.symm H.C.comm_jz

theorem alphaOf_eq_bot (hyp51 : Hyp51 H.B)
    (hCz0 : Subgroup.centralizer ({z} : Set G) ≤ gamma2 H.B (Subgroup.centralizer ({z} : Set G)))
    (h23 : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hbot : ∀ {A : Subgroup G}, Odd (Nat.card A) → Subgroup.normalizer (A : Set G) = ⊤ → A = ⊥) :
    ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥ := by
  obtain ⟨hodd, halpha⟩ := lemma54_odd_and_eq hyp51 H.closure_jz_le_B H.closure_jz
  set α₀ := alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) with hα₀
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) :=
    hCz0.trans (gamma2_le_normalizer_alphaOf halpha _)
  obtain ⟨s, hsT, hsU⟩ := H.exists_s
  have hsα : s ∈ Subgroup.normalizer (α₀ : Set G) :=
    normalizer_alpha halpha H.closure_jz_le_B H.closure_jz (H.s_mem_normalizer_B hsT hsU)
  have hrα : H.C.D.F.ρ.r ∈ Subgroup.normalizer (α₀ : Set G) := hCz H.C.r_mem_centralizer_z
  have hj : Subgroup.centralizer ({H.C.D.F.j} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) ∧
      Subgroup.centralizer ({H.C.D.F.j * z} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
    rcases H.s_conj_z_cases hsT hsU with h | h
    · have h1 := T7A.centralizer_conj_le hsα h.symm hCz
      exact ⟨h1, T7A.centralizer_conj_le hrα H.C.r_conj_j.symm h1⟩
    · have h2 := T7A.centralizer_conj_le hsα h.symm hCz
      exact ⟨T7A.centralizer_conj_le hrα H.C.r_conj_jz.symm h2, h2⟩
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
    intro c hc
    rcases H.C.u_cases with h | h
    · exact hj.1 (by rw [← h]; exact hc)
    · exact hj.2 (by rw [← h]; exact hc)
  have hN : Subgroup.normalizer (α₀ : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h23]
    exact sup_le hCu hCz
  have hα := hbot hodd hN
  intro A hAB hA
  rw [halpha A hAB hA, hα]

end HFrame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame

theorem comm_z : z * H.a = H.a * z := H.comm_W H.C.hd.hzW

theorem comm_j : H.C.D.F.j * H.a = H.a * H.C.D.F.j :=
  H.comm_W (H.C.x₃_sq ▸ W.pow_mem H.C.D.x₃_mem 2)


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

theorem a_mem_centralizer_Oz
    (hα : ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥) :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf
    (hα _ H.closure_za_le_B H.closure_za) (Subgroup.subset_closure (by simp))
    H.C.hzK.ne_one (Subgroup.subset_closure (by simp))

theorem a_mem_centralizer_Oj
    (hα : ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥) :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({H.C.D.F.j} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf
    (hα _ H.closure_ja_le_B H.closure_ja) (Subgroup.subset_closure (by simp))
    H.C.hjJ.ne_one (Subgroup.subset_closure (by simp))

theorem le_of_member
    (hsubn : ∀ M ∈ Ω, ∀ b : G, IsUniqueInvolution M b →
      IsSubnormal M (Subgroup.centralizer ({b} : Set G)))
    (hOz : H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G))
    (hOj : H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({H.C.D.F.j} : Set G)) : Subgroup G) : Set G))
    {M : Subgroup G} (hM : M ∈ Ω) {b : G}
    (hb : IsUniqueInvolution M b) (hbzj : b = z ∨ b = H.C.D.F.j)
    (haM : H.a ∈ trivialOnQuot M) : M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  refine le_centralizer_of_tq H.ha2 haM fun x hx => ?_
  have hsub := hsubn M hM b hb
  have hxO := oddCoreIn_le_of_isSubnormal hsub hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hbzj with rfl | rfl
  · exact Subgroup.mem_centralizer_iff.mp hOz x hxO
  · exact Subgroup.mem_centralizer_iff.mp hOj x hxO

end HFrame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame

include H in

theorem centralizer_z_le_sigma
    (hdstar : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → L ∈ dstarComp Ω K) :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K :=
    ⟨H.C.hyp.conjInvariant c K H.C.mem, z, H.C.hzK, hcz ▸ H.C.hzK.conj c⟩
  exact T7A.mem_sigmaStarNorm_of_conj H.C.hyp.conjInvariant H.C.mem
    (hdstar hL)

theorem J_mem_dstarComp (hWN : W ≤ Subgroup.normalizer (K : Set G)) :
    H.C.D.F.ρ₃.K ∈ dstarComp Ω K := by
  have hcard : Nat.card ↥H.C.D.F.ρ₃.R = 2 * Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := by
    have h := Q3CL.Thompson.D_card H.C.D.c.hΩ H.C.D.c.hW H.C.D.F.ρ₃.hR
    rw [← H.C.D.h₃] at h
    exact h
  have hU : Subgroup.zpowers H.C.D.x₃ ∈ USet Ω :=
    mem_USet_of_natCard H.C.D.F.ρ₃.hK H.C.D.F.ρ₃.hRK
      (Subgroup.zpowers_le.mpr H.C.x₃_mem_R₃) inferInstance hcard
  have hUN : Subgroup.zpowers H.C.D.x₃ ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (hWN H.C.D.x₃_mem)
  have hstar : H.C.D.F.ρ₃.K ∈ omegaStarNbr Ω K :=
    ⟨H.C.D.F.ρ₃.hK, H.C.J_ne_K, _, hU, Subgroup.zpowers_le.mpr H.C.x₃_mem_J, hUN⟩
  exact Relation.ReflTransGen.single ⟨H.C.D.F.ρ₃.hK, Or.inl hstar⟩

include H in

theorem centralizer_u_le_sigma
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K)
    (hJ : H.C.D.F.ρ₃.K ∈ dstarComp Ω K) :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  obtain ⟨y, hy⟩ := H.C.trans _ H.C.D.F.ρ₃.hK
  have hyN : y ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj H.C.hyp.conjInvariant H.C.mem (hy ▸ hJ)
  have hj : H.C.D.F.j = y * z * y⁻¹ := H.C.hjJ.eq (hy ▸ H.C.hzK.conj y)
  have hCj : Subgroup.centralizer ({H.C.D.F.j} : Set G) ≤ sigmaStarNorm Ω K :=
    T7A.centralizer_conj_le hyN hj hCz
  have hCjz : Subgroup.centralizer ({H.C.D.F.j * z} : Set G) ≤ sigmaStarNorm Ω K :=
    T7A.centralizer_conj_le (hCz H.C.r_mem_centralizer_z) H.C.r_conj_j.symm hCj
  intro c hc
  rcases H.C.u_cases with h | h
  · exact hCj (by rw [← h]; exact hc)
  · exact hCjz (by rw [← h]; exact hc)

end HFrame
end

end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
