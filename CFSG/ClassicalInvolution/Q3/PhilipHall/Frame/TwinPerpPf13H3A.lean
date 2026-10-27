module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf11H02
public import CFSG.ClassicalInvolution.Asc77.AscS24BHCent

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx

theorem mem_centralizer_closure_pair' {n x y : G} (hx : x * n = n * x) (hy : y * n = n * y) :
    n ∈ Subgroup.centralizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => g * n = n * g) ?_ ?_ ?_ ?_ hg
  · rintro g (rfl | rfl)
    · exact hx
    · exact hy
  · simp
  · intro a b _ _ ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  · intro a _ ha
    exact (Commute.inv_left (show Commute a n from ha)).eq

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

@[expose] def H0 : Subgroup G :=
  Subgroup.centralizer ((Subgroup.closure ({z, H.a} : Set G) : Subgroup G) : Set G) ⊔
    oddCoreOf (Subgroup.centralizer ({z} : Set G))

@[expose] def TransH0 : Prop :=
  ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∃ c ∈ H.H0, conjSub c W = W₁

theorem H0_le_centralizer_z : H.H0 ≤ Subgroup.centralizer ({z} : Set G) := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx z (Subgroup.subset_closure (by simp))
  · rintro x ⟨y, -, rfl⟩
    exact y.2

theorem cent_norm_le_normalizer_alpha
    (halpha : ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)))
    {n : G} (hnz : n ∈ Subgroup.centralizer ({z} : Set G))
    (hnW : n ∈ Subgroup.normalizer (W : Set G)) :
    n ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) := by
  have hjW : H.C.D.F.j ∈ W := H.C.x₃_sq ▸ W.pow_mem H.C.D.x₃_mem 2
  have hzn : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp hnz
  have hCjz : Subgroup.centralizer ((Subgroup.closure ({H.C.D.F.j, z} : Set G) : Subgroup G) :
      Set G) ≤ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) :=
    T7B.centralizer_le_normalizer_alphaOf _
  have hnj : n * H.C.D.F.j * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hnW _).mp hjW
  have h2 : n * H.C.D.F.j * n⁻¹ * (n * H.C.D.F.j * n⁻¹) = 1 := by
    calc n * H.C.D.F.j * n⁻¹ * (n * H.C.D.F.j * n⁻¹) = n * (H.C.D.F.j * H.C.D.F.j) * n⁻¹ := by
          group
      _ = 1 := by rw [H.C.hjJ.sq]; group
  rcases T7B.mem_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one H.C.comm_jz
    (H.C.mem_closure_of_mem_W hnj h2) with h | h | h | h
  · exfalso
    apply H.C.hjJ.ne_one
    calc H.C.D.F.j = n⁻¹ * (n * H.C.D.F.j * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · apply hCjz
    refine mem_centralizer_closure_pair' ?_ hzn.symm
    calc H.C.D.F.j * n = (n * H.C.D.F.j * n⁻¹) * n := by rw [h]
      _ = n * H.C.D.F.j := by group
  · exfalso
    apply H.C.z_ne_j
    calc z = n⁻¹ * (n * z) := by group
      _ = n⁻¹ * (z * n) := by rw [hzn]
      _ = n⁻¹ * z * n := by group
      _ = n⁻¹ * (n * H.C.D.F.j * n⁻¹) * n := by rw [h]
      _ = H.C.D.F.j := by group
  · have hrα : H.C.D.F.ρ.r ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) :=
      normalizer_alpha halpha H.closure_jz_le_B H.closure_jz H.r_mem_normalizer_B
    have hrz : H.C.D.F.ρ.r * z = z * H.C.D.F.ρ.r :=
      Subgroup.mem_centralizer_singleton_iff.mp H.C.r_mem_centralizer_z
    have hrn : H.C.D.F.ρ.r * n ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) := by
      apply hCjz
      refine mem_centralizer_closure_pair' ?_ ?_
      · have e : H.C.D.F.ρ.r * (n * H.C.D.F.j * n⁻¹) * H.C.D.F.ρ.r⁻¹ = H.C.D.F.j := by
          rw [h]; exact H.C.r_conj_jz
        calc H.C.D.F.j * (H.C.D.F.ρ.r * n) = (H.C.D.F.ρ.r * (n * H.C.D.F.j * n⁻¹) *
            H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * n) := by rw [e]
          _ = H.C.D.F.ρ.r * n * H.C.D.F.j := by group
      · calc z * (H.C.D.F.ρ.r * n) = (z * H.C.D.F.ρ.r) * n := by group
          _ = (H.C.D.F.ρ.r * z) * n := by rw [hrz]
          _ = H.C.D.F.ρ.r * (z * n) := by group
          _ = H.C.D.F.ρ.r * (n * z) := by rw [← hzn]
          _ = H.C.D.F.ρ.r * n * z := by group
    have e : n = H.C.D.F.ρ.r⁻¹ * (H.C.D.F.ρ.r * n) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hrα) hrn

theorem B_le_centralizer_z : H.B ≤ Subgroup.centralizer ({z} : Set G) := by
  unfold B
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hx with rfl | rfl | rfl
  · calc H.C.D.F.j * H.a * z = H.C.D.F.j * (H.a * z) := by group
      _ = H.C.D.F.j * (z * H.a) := by rw [H.comm_z]
      _ = (H.C.D.F.j * z) * H.a := by group
      _ = (z * H.C.D.F.j) * H.a := by rw [H.C.comm_jz]
      _ = z * (H.C.D.F.j * H.a) := by group
  · exact H.C.comm_jz
  · rfl

theorem alpha_facts [Fact P24.Hyp51VertexP] [Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) :=
  lemma54_odd_and_eq H.hyp51 H.closure_jz_le_B H.closure_jz

theorem H0_le_normalizer_alpha
    (halpha : ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G))) :
    H.H0 ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) := by
  refine sup_le ?_ ?_
  · have h1 := T7B.centralizer_le_normalizer_alphaOf
      (Subgroup.closure ({z, H.a} : Set G) : Subgroup G)
    rwa [halpha _ H.closure_za_le_B H.closure_za] at h1
  · have h1 := S24.oddCore_le_gamma2_of H.B_isElemAbelian H.B_card H.B_le_centralizer_z
    exact h1.trans (gamma2_le_normalizer_alphaOf halpha _)

theorem cent_z_le_normalizer_alpha (hT : H.TransH0)
    (halpha : ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G))) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) : Set G) := by
  intro c hc
  have hΩ : HypOmegaMod Ω := H.C.hs.stand.hyp
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hW1 : conjSub c W ∈ WSet Ω := WSet.conj hΩ.conjInvariant H.C.hd.hW c
  have hzW1 : z ∈ conjSub c W := by
    rw [mem_conjSub_iff]
    have : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
        _ = c⁻¹ * (c * z) := by rw [hcz]
        _ = z := by group
    rw [this]
    exact H.C.hd.hzW
  obtain ⟨c₀, hc₀, hc₀W⟩ := hT _ hW1 hzW1
  have hc₀z := H.H0_le_centralizer_z hc₀
  have hn : c₀⁻¹ * c ∈ Subgroup.normalizer (W : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hc₀W, conjSub_inv_conjSub]
  have hnz : c₀⁻¹ * c ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀z) hc
  have h1 := H.cent_norm_le_normalizer_alpha halpha hnz hn
  have h0 := H.H0_le_normalizer_alpha halpha hc₀
  have e : c = c₀ * (c₀⁻¹ * c) := by group
  rw [e]
  exact Subgroup.mul_mem _ h0 h1

theorem alphaOf_eq_bot₂ [h23 : Fact P24.Sup23_2P] [Fact P24.Hyp51VertexP] [Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] (hT : H.TransH0) :
    ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥ := by
  obtain ⟨hodd, halpha⟩ := H.alpha_facts
  set α₀ := alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) with hα₀
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) :=
    H.cent_z_le_normalizer_alpha hT halpha
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
    rw [← h23.out H.C.hyp]
    exact sup_le hCu hCz
  have hα := P24.eq_bot_of_normalizer_eq_top_core hodd hN
  intro A hAB hA
  rw [halpha A hAB hA, hα]

@[expose] def AlphaBot : Prop :=
  ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥

theorem a_mem_centralizer_Oz₂ (hα : H.AlphaBot) :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf (hα _ H.closure_za_le_B H.closure_za)
    (Subgroup.subset_closure (by simp)) H.C.hzK.ne_one (Subgroup.subset_closure (by simp))

theorem a_mem_centralizer_Oj₂ (hα : H.AlphaBot) :
    H.a ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({H.C.D.F.j} : Set G)) : Subgroup G) : Set G) :=
  S24.mem_centralizer_oddCoreOf_of_alphaOf (hα _ H.closure_ja_le_B H.closure_ja)
    (Subgroup.subset_closure (by simp)) H.C.hjJ.ne_one (Subgroup.subset_closure (by simp))

theorem le_of_member₂ (hα : H.AlphaBot) [CoreLike G] {M : Subgroup G} (hM : M ∈ Ω) {b : G}
    (hb : IsUniqueInvolution M b) (hbzj : b = z ∨ b = H.C.D.F.j)
    (haM : H.a ∈ trivialOnQuot M) : M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  refine le_centralizer_of_tq H.ha2 haM fun x hx => ?_
  have hsub := H.C.hs.stand.cls.isSubnormal_of_uniqueInvolution hM hb
  have hxO := oddCoreIn_le_of_isSubnormal hsub hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hbzj with rfl | rfl
  · exact Subgroup.mem_centralizer_iff.mp (H.a_mem_centralizer_Oz₂ hα) x hxO
  · exact Subgroup.mem_centralizer_iff.mp (H.a_mem_centralizer_Oj₂ hα) x hxO

theorem K_le₂ (hα : H.AlphaBot) [CoreLike G] : K ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member₂ hα H.C.hs.stand.mem H.C.hzK (Or.inl rfl) (H.K_tq H.a H.ha2 H.haR).2

theorem J_le₂ (hα : H.AlphaBot) [CoreLike G] :
    H.C.D.F.ρ₃.K ≤ Subgroup.centralizer ({H.a} : Set G) :=
  H.le_of_member₂ hα H.C.D.F.ρ₃.hK H.C.hjJ (Or.inr rfl) (H.J_tq H.a H.ha2 H.hTa).2

theorem H0_le_centralizer_a (hα : H.AlphaBot) [CoreLike G] :
    H.H0 ≤ Subgroup.centralizer ({H.a} : Set G) := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx H.a (Subgroup.subset_closure (by simp)) |>.symm
  · rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxO : (y : G) ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (H.a_mem_centralizer_Oz₂ hα) _ hxO

theorem exists_conj_of_rep (hα : H.AlphaBot) [CoreLike G] (σ : Thompson.Rep Ω W) :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = σ.K := by
  have hs : H.C.D.F.ρ₃.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    H.J_le₂ hα (H.C.D.F.ρ₃.hRK.1 H.C.D.F.ρ₃.hr)
  have hr : H.C.D.F.ρ.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_r
  have ht : H.C.D.F.ρ'.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_t
  obtain ⟨h, hh, hK⟩ := exists_conj_of_frame H.C.D.c H.C.D.hφ H.C.D.F H.C.D.hab H.C.D.hcomm
    H.C.D.hac hr ht hs σ
  exact ⟨h, hh, (congrArg (conjSub h) H.C.hK).symm.trans hK⟩

theorem key₂ (hα : H.AlphaBot) (hT : H.TransH0) [CoreLike G] (W₁ : Subgroup G) (hW₁ : W₁ ∈ WSet Ω)
    (hzW₁ : z ∈ W₁) (J' : Subgroup G) (hJ' : J' ∈ Ω) (hT' : ∃ T ∈ DSet Ω W₁, IsSylow2In T J') :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
  obtain ⟨T, hTD, hTJ'⟩ := hT'
  obtain ⟨c, hc, hcW⟩ := hT W₁ hW₁ hzW₁
  have hca : c ∈ Subgroup.centralizer ({H.a} : Set G) := H.H0_le_centralizer_a hα hc
  have hΩ : HypOmegaMod Ω := H.C.hs.stand.hyp
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer (W₁ : Set G) := fun t ht => hTD.2 ht
  have hTD' : conjSub c⁻¹ T ∈ DSet Ω W := by
    refine ⟨RSet.conj hΩ.conjInvariant hTD.1 c⁻¹, fun x hx => ?_⟩
    rw [mem_conjSub_iff] at hx
    rw [mem_normalizer_iff_conjSub_eq]
    simp only [inv_inv] at hx
    have hxt := hTN _ hx
    rw [mem_normalizer_iff_conjSub_eq] at hxt
    have hW : conjSub c⁻¹ W₁ = W := by rw [← hcW, conjSub_inv_conjSub]
    calc conjSub x W = conjSub x (conjSub c⁻¹ W₁) := by rw [hW]
      _ = conjSub (c⁻¹ * (c * x * c⁻¹)) W₁ := by rw [← conjSub_mul]; congr 1; group
      _ = conjSub c⁻¹ (conjSub (c * x * c⁻¹) W₁) := by rw [conjSub_mul]
      _ = W := by rw [hxt, hW]
  have hJ'' : conjSub c⁻¹ J' ∈ Ω := hΩ.conjInvariant c⁻¹ J' hJ'
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hΩ H.C.hd.hW hJ'' (hTJ'.conj c⁻¹) hTD'
  obtain ⟨h, hh, hK⟩ := H.exists_conj_of_rep hα σ
  refine ⟨c * h, Subgroup.mul_mem _ hca hh, ?_⟩
  rw [conjSub_mul, hK, hσK, conjSub_conjSub_inv]

theorem trans₂ (hα : H.AlphaBot) (hT : H.TransH0) [CoreLike G] :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J := by
  have hst := H.C.hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' →
      ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT', hR₁K, hTJ'⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h
      have hzW₁ : z ∈ W₁ :=
        (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K H.C.hzK).2
      exact H.key₂ hα hT W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT', hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT', hR₁J', hTK⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT' hTK H.C.hzK).2
      exact H.key₂ hα hT W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
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

include H in
theorem false_of_transH0 [h23 : Fact P24.Sup23_2P] [Fact P24.Hyp51VertexP] [Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] (hT : H.TransH0) : False := by
  have hα : H.AlphaBot := H.alphaOf_eq_bot₂ hT
  have hst := H.C.hs.stand
  have hN : sigmaStarNorm Ω K = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h23.out H.C.hyp]
    exact sup_le H.centralizer_u_le_sigma H.centralizer_z_le_sigma
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({H.a} : Set G) := by
    intro M hM
    obtain ⟨g, hg⟩ := hst.trans M hM
    have hgN : g ∈ sigmaStarNorm Ω K := by rw [hN]; exact Subgroup.mem_top g
    have hMS : M ∈ dstarComp Ω K := by
      rw [← hg]
      exact (mem_sigmaStarNorm_iff.mp hgN K).mp Relation.ReflTransGen.refl
    obtain ⟨h, hh, hK⟩ := H.trans₂ hα hT M hMS
    rw [← hK]
    exact conjSub_le_centralizer (H.K_le₂ hα) (Subgroup.mem_centralizer_singleton_iff.mp hh)
  have htop : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({H.a} : Set G) := iSup₂_le hall
  rw [hst.gen] at htop
  apply H.ha1
  refine P24.eq_one_of_central_core fun g => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))

end HCtx
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
