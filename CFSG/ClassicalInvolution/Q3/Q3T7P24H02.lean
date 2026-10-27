module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01
public import CFSG.ClassicalInvolution.Asc77.AscS24BHCent
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngH2
public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A06

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

private def toHFrame : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame Ω K K' W S R R' z u where
  C := H.C.toFrame
  a := H.a
  T₃ := H.T₃
  ha2 := H.ha2
  ha1 := H.ha1
  haR := H.haR
  haR' := H.haR'
  hT := H.hT
  hTN := H.hTN
  hTa := H.hTa

theorem closure_jz_le_B : Subgroup.closure ({H.C.D.F.j, z} : Set G) ≤ H.B := by
  exact (toHFrame H).closure_jz_le_B

theorem closure_jz : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, z} : Set G)) 2 :=
  (toHFrame H).closure_jz

theorem centralizer_z_le_gamma2 :
    Subgroup.centralizer ({z} : Set G) ≤ gamma2 H.B (Subgroup.centralizer ({z} : Set G)) := by
  have hst := H.C.hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hB := H.B_isElemAbelian
  have hBC : H.B ≤ Subgroup.centralizer ({z} : Set G) := fun _ hb =>
    Lemma52Proof.le_centralizer_of_mem hB H.z_mem_B hb
  have hO := S24.oddCore_le_gamma2_of hB H.B_card hBC
  have hK := S24.le_gamma2_of_trivial hΩ H.z_mem_B H.a_mem_B H.ha2 H.ha1 H.a_ne_z.symm H.comm_z
    hO hst.mem H.C.hzK (H.K_tq H.a H.ha2 H.haR).2
  have hK' := S24.le_gamma2_of_trivial hΩ H.z_mem_B H.a_mem_B H.ha2 H.ha1 H.a_ne_z.symm H.comm_z
    hO H.C.hs.hK'.1 H.C.hzK' (H.K'_tq H.a H.ha2 H.haR').2
  intro c hc
  obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ := T7K.centralizer_eq_sup_mul H.C.hs H.C.j_mem_sup
    H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq hc
  refine Subgroup.mul_mem _ ((sup_le hK hK') hq) ?_
  have hcz : z * c₀ = c₀ * z := (Subgroup.mem_centralizer_singleton_iff.mp hc₀).symm
  exact T7K.le_gamma2 H.closure_jz_le_B H.closure_jz
    ⟨hc₀, T7B.mem_centralizer_closure_pair hcomm.symm hcz⟩

theorem alphaOf_eq_bot [h23 : Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] :
    ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥ := by
  exact (toHFrame H).alphaOf_eq_bot H.hyp51 H.centralizer_z_le_gamma2 (h23.out H.C.hs H.C.hd) (fun
    hodd hN => T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard H.C.hs.hz))
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

theorem a_mem_centralizer_Oz [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
  (toHFrame H).a_mem_centralizer_Oz H.alphaOf_eq_bot

theorem a_mem_centralizer_Oj [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({H.C.D.F.j} : Set G)) : Subgroup G) : Set G) :=
  (toHFrame H).a_mem_centralizer_Oj H.alphaOf_eq_bot

theorem le_of_member [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] {M : Subgroup G} (hM : M ∈ Ω) {b : G}
    (hb : IsUniqueInvolution M b) (hbzj : b = z ∨ b = H.C.D.F.j)
    (haM : H.a ∈ trivialOnQuot M) : M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  exact (toHFrame H).le_of_member (fun M hM b hb => T7A.isSubnormal_centralizer H.C.hs.stand.modU hM
    hb) H.a_mem_centralizer_Oz H.a_mem_centralizer_Oj hM hb hbzj haM

theorem K_le [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : K ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.C.hs.stand.mem H.C.hzK (Or.inl rfl) (H.K_tq H.a H.ha2 H.haR).2

theorem K'_le [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : K' ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.C.hs.hK'.1 H.C.hzK' (Or.inl rfl) (H.K'_tq H.a H.ha2 H.haR').2

theorem J_le [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : H.C.D.F.ρ₃.K ≤ Subgroup.centralizer ({H.a} :
    Set G) :=
  H.le_of_member H.C.D.F.ρ₃.hK H.C.hjJ (Or.inr rfl) (H.J_tq H.a H.ha2 H.hTa).2

theorem Js_le [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : H.Js ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member H.Js_mem H.hjJs (Or.inr rfl) (H.Js_tq H.a H.ha2 H.Ts_le).2
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

theorem kPerp_J : KPerp Ω H.C.D.F.ρ₃.K = {H.C.D.F.ρ₃.K, H.Js} := by
  have hst := H.C.hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  obtain ⟨g, hg⟩ := hst.trans _ H.C.D.F.ρ₃.hK
  have h1 := T7L.kPerp_conj_pair hΩ.conjInvariant H.C.hs.perp g
  rw [hg] at h1
  have hTR : H.Ts ∈ RSet Ω := mem_RSet_of_isSylow2In H.Js_mem H.Ts_syl
  have h8 := hΩ.eight_le_of_mem_RSet hTR
  have hTN := hΩ.le_normalizer_of_le_centralizer H.C.D.F.ρ₃.hK H.Js_mem
    H.Js_ne.symm H.C.hjJ H.Ts_syl.1 H.Ts_syl.2.1 (by omega)
    (H.Ts_syl.1.trans (le_centralizer_of_unique H.hjJs))
  have hnbr : H.Js ∈ omegaNbr Ω H.C.D.F.ρ₃.K := ⟨H.Js_mem, H.Js_ne, H.Ts, hTR, H.Ts_syl.1, hTN⟩
  have hmem : H.Js ∈ KPerp Ω H.C.D.F.ρ₃.K := Set.mem_insert_of_mem _ hnbr
  rw [h1] at hmem
  rcases hmem with h | h
  · exact absurd h H.Js_ne
  · rw [h1, h]

theorem exists_L [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] {u₁ : G} (hu : u₁ ∈ K ⊔ K') (hu1 : u₁ ≠ 1) (huz
    : u₁ ≠ z)
    (hu2 : u₁ * u₁ = 1) :
    ∃ L ∈ Ω, IsUniqueInvolution L u₁ ∧
      ∀ M ∈ KPerp Ω L, M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  have hΩ : HypOmegaModT Ω := H.C.hs.stand.modU
  obtain ⟨c, hc, hcu⟩ := T7K.exists_conj_of_involution H.C.hs H.C.j_mem_sup H.C.hjJ.ne_one
    H.C.z_ne_j.symm H.C.hjJ.sq hu hu1 huz hu2
  have hca : c * H.a = H.a * c :=
    Subgroup.mem_centralizer_singleton_iff.mp ((sup_le H.K_le H.K'_le) hc)
  refine ⟨conjSub c H.C.D.F.ρ₃.K, hΩ.conjInvariant c _ H.C.D.F.ρ₃.hK, ?_, ?_⟩
  · have h := H.C.hjJ.conj c
    rwa [hcu] at h
  · intro M hM
    rw [T7L.kPerp_conj_pair hΩ.conjInvariant H.kPerp_J c] at hM
    rcases hM with h | h <;> rw [h]
    · exact conjSub_le_centralizer H.J_le hca
    · exact conjSub_le_centralizer H.Js_le hca
include H in

theorem not_mem_K' {y : G} (hy : y ∈ K) (oy : orderOf y = 4) : y ∉ K' := by
  intro hy'
  have hΩ : HypOmegaModT Ω := H.C.hs.stand.modU
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers y) := T7A.isPGroup_zpowers_of_orderOf_four oy
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers y) := by rw [Nat.card_zpowers, oy]
  exact H.C.hs.hne (hΩ.eq_of_le_of_le H.C.hs.stand.mem H.C.hs.hK'.1 h2 h4
    (Subgroup.zpowers_le.mpr hy) (Subgroup.zpowers_le.mpr hy')).symm

theorem third_le [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] {W₁ : Subgroup G} (c : Q3CL.Thompson.Ctx Ω W₁)
    {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hFK : F.ρ.K = K) (hFK' : F.ρ'.K = K') (hFz : F.z = z)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    F.ρ₃.r ∈ Subgroup.centralizer ({H.a} : Set G) := by
  have hst := H.C.hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaModT Ω := hst.modU
  obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, -⟩ :=
    F.exists_structure c he hab hcomm hac
  have mx₁ : x₁ ∈ F.ρ.R ⊓ W₁ := h₁ ▸ Subgroup.mem_zpowers x₁
  have mx₂ : x₂ ∈ F.ρ'.R ⊓ W₁ := h₂ ▸ Subgroup.mem_zpowers x₂
  have ob : orderOf (x₁ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega) (by rw [o₁]; exact dvd_mul_left m 4)
    rwa [o₁, Nat.mul_div_cancel _ hm] at this
  have ob' : orderOf (x₂ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega) (by rw [o₂]; exact dvd_mul_left m 4)
    rwa [o₂, Nat.mul_div_cancel _ hm] at this
  have hbK : x₁ ^ m ∈ F.ρ.K ⊓ W₁ := ⟨F.ρ.hRK.1 (F.ρ.R.pow_mem mx₁.1 m), W₁.pow_mem mx₁.2 m⟩
  have hb'K : x₂ ^ m ∈ F.ρ'.K ⊓ W₁ := ⟨F.ρ'.hRK.1 (F.ρ'.R.pow_mem mx₂.1 m), W₁.pow_mem mx₂.2 m⟩
  obtain ⟨u₁, hu₁, hsu, -⟩ := T7D.frame_fixed c F.ρ F.ρ' F.ρ₃ F.hnbr F.hnbr' F.hne₁ F.hne₂ F.hn₁
    F.hn₂ F.hn₁' F.hn₂' F.hz F.hz' F.hj hbK hb'K ob ob'
  have hbKK : x₁ ^ m ∈ K := hFK ▸ hbK.1
  have hb'KK : x₂ ^ m ∈ K' := hFK' ▸ hb'K.1
  have hbb : x₁ ^ m * x₁ ^ m = z := hFz ▸ T7A.sq_eq_of_orderOf_four F.hz hbK.1 ob
  have hb'b' : x₂ ^ m * x₂ ^ m = z := hFz ▸ T7A.sq_eq_of_orderOf_four F.hz' hb'K.1 ob'
  have hcomm₁₂ : x₁ ^ m * x₂ ^ m = x₂ ^ m * x₁ ^ m := c.comm_W _ hbK.2 _ hb'K.2

  obtain ⟨y, hyK, hyW, hyy, hyc, rfl⟩ : ∃ y, y ∈ K ∧ y ∈ W₁ ∧ y * y = z ∧
      y * x₂ ^ m = x₂ ^ m * y ∧ u₁ = y * x₂ ^ m := by
    rcases hu₁ with h | h
    · exact ⟨x₁ ^ m, hbKK, hbK.2, hbb, hcomm₁₂, h⟩
    · refine ⟨(x₁ ^ m)⁻¹, K.inv_mem hbKK, W₁.inv_mem hbK.2, ?_, ?_, h⟩
      · rw [← mul_inv_rev, hbb]; exact inv_eq_of_mul_eq_one_right H.C.hzK.sq
      · exact (Commute.inv_left hcomm₁₂).eq
  have hu2 : y * x₂ ^ m * (y * x₂ ^ m) = 1 := by
    calc y * x₂ ^ m * (y * x₂ ^ m) = y * (x₂ ^ m * y) * x₂ ^ m := by group
      _ = y * (y * x₂ ^ m) * x₂ ^ m := by rw [hyc]
      _ = (y * y) * (x₂ ^ m * x₂ ^ m) := by group
      _ = 1 := by rw [hyy, hb'b', H.C.hzK.sq]
  have hnot : ∀ v ∈ K, y * x₂ ^ m ≠ v := by
    intro v hv h
    have e : x₂ ^ m = y⁻¹ * v := by rw [← h]; group
    have hK : x₂ ^ m ∈ K := by rw [e]; exact K.mul_mem (K.inv_mem hyK) hv
    exact H.not_mem_K' hK ob' hb'KK
  obtain ⟨L, hLΩ, hLu, hLperp⟩ := H.exists_L (Subgroup.mul_mem _ (Subgroup.mem_sup_left hyK)
    (Subgroup.mem_sup_right hb'KK)) (hnot 1 K.one_mem) (hnot z H.C.hzK.mem) hu2
  have hT : F.ρ₃.R ≤ Subgroup.centralizer ({y * x₂ ^ m} : Set G) := by
    have huW : y * x₂ ^ m ∈ W₁ := W₁.mul_mem hyW hb'K.2
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hxW : x ∈ W₁
    · exact c.comm_W x hxW _ huW
    · have h1 := Q3CL.Thompson.D_inv_mul_mem c.hΩ c.hW F.ρ₃.hR F.ρ₃.hr hx F.ρ₃.hrW hxW
      have h2 : F.ρ₃.r⁻¹ * x * (y * x₂ ^ m) = (y * x₂ ^ m) * (F.ρ₃.r⁻¹ * x) := c.comm_W _ h1 _ huW
      have hs : F.ρ₃.r * (y * x₂ ^ m) = (y * x₂ ^ m) * F.ρ₃.r := by
        calc F.ρ₃.r * (y * x₂ ^ m) = F.ρ₃.r * (y * x₂ ^ m) * F.ρ₃.r⁻¹ * F.ρ₃.r := by group
          _ = (y * x₂ ^ m) * F.ρ₃.r := by rw [hsu]
      calc x * (y * x₂ ^ m) = F.ρ₃.r * (F.ρ₃.r⁻¹ * x * (y * x₂ ^ m)) := by group
        _ = F.ρ₃.r * ((y * x₂ ^ m) * (F.ρ₃.r⁻¹ * x)) := by rw [h2]
        _ = (F.ρ₃.r * (y * x₂ ^ m)) * (F.ρ₃.r⁻¹ * x) := by group
        _ = ((y * x₂ ^ m) * F.ρ₃.r) * (F.ρ₃.r⁻¹ * x) := by rw [hs]
        _ = (y * x₂ ^ m) * x := by group
  have hJ₁ : F.ρ₃.K ∈ KPerp Ω L := by
    by_cases hJL : F.ρ₃.K = L
    · rw [hJL]; exact Set.mem_insert _ _
    · have h8 := hΩ.eight_le_of_mem_RSet F.ρ₃.hR.1
      have hN := hΩ.le_normalizer_of_le_centralizer hLΩ F.ρ₃.hK (Ne.symm hJL) hLu
        F.ρ₃.hRK.1 F.ρ₃.hRK.2.1 (by omega) hT
      exact Set.mem_insert_of_mem _ ⟨F.ρ₃.hK, hJL, F.ρ₃.R, F.ρ₃.hR.1, F.ρ₃.hRK.1, hN⟩
  exact hLperp _ hJ₁ (F.ρ₃.hRK.1 F.ρ₃.hr)

theorem exists_conj_K' [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = K' := by
  have hs : H.C.D.F.ρ₃.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    H.J_le (H.C.D.F.ρ₃.hRK.1 H.C.D.F.ρ₃.hr)
  have hr : H.C.D.F.ρ.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_r
  have ht : H.C.D.F.ρ'.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_t
  obtain ⟨h, hh, hK⟩ := exists_conj_of_frame H.C.D.c H.C.D.hφ H.C.D.F H.C.D.hab H.C.D.hcomm
    H.C.D.hac hr ht hs H.C.D.F.ρ'
  exact ⟨h, hh, (congrArg (conjSub h) H.C.hK).symm.trans (hK.trans H.C.hK')⟩

theorem key [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] (W₁ : Subgroup G) (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z
    ∈ W₁)
    (J' : Subgroup G) (hJ' : J' ∈ Ω) (hT : ∃ T ∈ DSet Ω W₁, IsSylow2In T J') :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
  obtain ⟨T, hTD, hTJ'⟩ := hT
  have hst := H.C.hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have c : Q3CL.Thompson.Ctx Ω W₁ := T7D.ctx_of_stand hst hW₁
  obtain ⟨S₁, ρ, ρ', -, hρK, hρ'K, -, -, hnbr, hnbr', hab, hcomm⟩ :=
    T7E.exists_twin_reps H.C.hs hW₁ hzW₁
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hΩ hW₁ hJ' hTJ' hTD
  rcases T7E.rep_dichotomy H.C.hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
  · rcases hall σ with h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [conjSub_one, ← hσK, h, hρK]⟩
    · obtain ⟨g, hg, hgK⟩ := H.exists_conj_K'
      exact ⟨g, hg, by rw [hgK, ← hσK, h, hρ'K]⟩
  · obtain ⟨F, hFρ, hFρ', hFρ₃, hFz⟩ :=
      T7E.frame4_of_twin_reps H.C.hs hW₁ hρK hρ'K hnbr hnbr' hac hbc
    subst hFρ hFρ' hFρ₃
    have hs₁ := H.third_le c he F hρK hρ'K hFz hab hcomm hac
    have hr₁ : F.ρ.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
      H.K_le (hρK ▸ F.ρ.hRK.1 F.ρ.hr)
    have hr₁' : F.ρ'.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
      H.K'_le (hρ'K ▸ F.ρ'.hRK.1 F.ρ'.hr)
    obtain ⟨h, hh, hK⟩ := exists_conj_of_frame c he F hab hcomm hac hr₁ hr₁' hs₁ σ
    exact ⟨h, hh, by rw [← hρK, hK, hσK]⟩

theorem trans [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J := by
  have hst := H.C.hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' →
      ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h
      have hzW₁ : z ∈ W₁ :=
        (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K H.C.hzK).2
      exact H.key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK H.C.hzK).2
      exact H.key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
  intro J hJ
  have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, Subgroup.one_mem _, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h | h⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)
include H in

theorem centralizer_z_le_sigma :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
  exact (toHFrame H).centralizer_z_le_sigma (fun hL =>
    CFSG.ClassicalInvolution.Q3.Q3T7P24.mem_dstarComp_of_twin H.C.hs.stand.modU H.C.hs.stand.mem hL)

theorem J_mem_dstarComp : H.C.D.F.ρ₃.K ∈ dstarComp Ω K := by
  exact (toHFrame H).J_mem_dstarComp (H.C.W_le_normalizer K H.C.hs.stand.mem ⟨H.C.x₁_mem_K,
    H.C.D.x₁_mem⟩ H.C.orderOf_x₁)
include H in

theorem centralizer_u_le_sigma :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  exact (toHFrame H).centralizer_u_le_sigma H.centralizer_z_le_sigma H.J_mem_dstarComp
include H in

theorem false_of [h23 : Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : False := by
  have hst := H.C.hs.stand
  have hN : sigmaStarNorm Ω K = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h23.out H.C.hs H.C.hd]
    exact sup_le H.centralizer_u_le_sigma H.centralizer_z_le_sigma
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({H.a} : Set G) := by
    intro M hM
    obtain ⟨g, hg⟩ := hst.trans M hM
    have hgN : g ∈ sigmaStarNorm Ω K := by rw [hN]; exact Subgroup.mem_top g
    have hMS : M ∈ dstarComp Ω K := by
      rw [← hg]
      exact (mem_sigmaStarNorm_iff.mp hgN K).mp Relation.ReflTransGen.refl
    obtain ⟨h, hh, hK⟩ := H.trans M hMS
    rw [← hK]
    exact conjSub_le_centralizer H.K_le (Subgroup.mem_centralizer_singleton_iff.mp hh)
  have htop : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({H.a} : Set G) := iSup₂_le hall
  rw [hst.gen] at htop
  apply H.ha1
  refine T7B.eq_one_of_central (T7C.exists_not_commute_of_stand hst) fun g => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
end HCtx

theorem h3_proved [Fact Q3T7P24.Sup23_2Three] [Fact Q3T7P24.Hyp51VertexThree] [Fact
    Q3T7P24.Hyp51TwinInnerThree] : H3 := by
  intro G _ _ _ Ω K K' W S R R' z u hs hd h8 D hK hK' hR hR' a ha2 haR haR' T₃ hT hTN hTa
  by_contra ha1
  have hz : D.F.z = z := (hs.hz.eq (hK ▸ D.F.hz)).symm
  exact (⟨⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩, a, T₃, ha2, ha1, haR, haR', hT, hTN, hTa⟩ :
    HCtx Ω K K' W S R R' z u).false_of
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
