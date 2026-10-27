module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalN60Four
public import CFSG.LocalAnalysis.EvenBN.G2.ProductDefs
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

namespace ProductComplementFourAux

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (sylow_prod le_normalizer_of_commutator_mem)
open scoped commutatorElement Pointwise MatrixGroups

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem sup_inf_eq_of_sup_eq {N A M P : Subgroup G} (hMP : M ≤ P) (hPN : P ≤ N)
    (hAM : A ≤ normalizer (M : Set G)) (hsup : A ⊔ M = N) : M ⊔ (P ⊓ A) = P := by
  refine le_antisymm (sup_le hMP inf_le_left) fun p hp => ?_
  have hp' : p ∈ M ⊔ A := by
    rw [sup_comm, hsup]
    exact hPN hp
  obtain ⟨m, hm, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer hAM p hp'
  have ha' : a ∈ P := by
    have := mul_mem (inv_mem (hMP hm)) hp
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ⟨ha', ha⟩)

theorem le_sup_map_conj_of_sup_eq {N A M P : Subgroup G} {s : G}
    (hN : N = P ⊔ P.map (MulAut.conj s).toMonoidHom) (hMP : M ≤ P) (hPN : P ≤ N)
    (hNM : N ≤ normalizer (M : Set G)) (hsM : s ∈ normalizer (M : Set G)) (hAN : A ≤ N)
    (hsup : A ⊔ M = N) (hsA : s ∈ A) :
    A ≤ (P ⊓ A) ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom := by
  have hAM' : A ≤ normalizer (M : Set G) := hAN.trans hNM
  have hPeq : M ⊔ (P ⊓ A) = P := sup_inf_eq_of_sup_eq hMP hPN hAM' hsup
  have hMs : M.map (MulAut.conj s).toMonoidHom = M := Common.map_conj_eq_of_mem_normalizer hsM
  have hTA : (P ⊓ A) ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom ≤ A := by
    refine sup_le inf_le_right ?_
    calc (P ⊓ A).map (MulAut.conj s).toMonoidHom ≤ A.map (MulAut.conj s).toMonoidHom :=
          Subgroup.map_mono inf_le_right
      _ = A := Common.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsA)
  have hTn : (P ⊓ A) ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom ≤ normalizer (M : Set G) :=
    hTA.trans hAM'
  have hNle : N ≤ M ⊔ ((P ⊓ A) ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom) := by
    rw [hN]
    refine sup_le ?_ ?_
    · calc P = M ⊔ (P ⊓ A) := hPeq.symm
        _ ≤ _ := sup_le_sup_left le_sup_left _
    · calc P.map (MulAut.conj s).toMonoidHom
          = (M ⊔ (P ⊓ A)).map (MulAut.conj s).toMonoidHom := by rw [hPeq]
        _ = M.map (MulAut.conj s).toMonoidHom ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom :=
            Subgroup.map_sup _ _ _
        _ = M ⊔ (P ⊓ A).map (MulAut.conj s).toMonoidHom := by rw [hMs]
        _ ≤ _ := sup_le_sup_left le_sup_right _
  intro a ha
  obtain ⟨m, hm, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer hTn a (hNle (hAN ha))
  have hmA : m ∈ A := by
    have := mul_mem ha (inv_mem (hTA hτ))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hMP hm, hmA⟩) hτ

theorem mem_map_conj_iff' {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_conj {t : G} (ht : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext x
  rw [mem_map_conj_iff', mem_map_conj_iff']
  have : t⁻¹ * (t⁻¹ * x * t) * t = x := by
    rw [hti]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  rw [this]

theorem isSylowOf_inf_of_sup_eq {N A M P : Subgroup G} (hP : IsSylowOf 2 P N) (hMP : M ≤ P)
    (hNM : N ≤ normalizer (M : Set G)) (hAN : A ≤ N) (hsup : A ⊔ M = N) :
    IsSylowOf 2 (P ⊓ A) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ≤ N := hP.le
  have hAM : A ≤ normalizer (M : Set G) := hAN.trans hNM
  have h1 := Common.card_sup_mul_card_inf_eq (A := M) (B := A) hAM
  rw [sup_comm, hsup, inf_comm] at h1
  have hMA : M ⊔ (P ⊓ A) = P := sup_inf_eq_of_sup_eq hMP hPN hAM hsup
  have hPAM : (P ⊓ A) ≤ normalizer (M : Set G) := inf_le_right.trans hAM
  have h2 := Common.card_sup_mul_card_inf_eq (A := M) (B := P ⊓ A) hPAM
  rw [hMA, ← inf_assoc, inf_of_le_left hMP, inf_comm] at h2
  have hy : 0 < Nat.card ↥(A ⊓ M) := Nat.card_pos
  have h3 : Nat.card A * Nat.card P = Nat.card ↥(P ⊓ A) * Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_right hy
    calc Nat.card A * Nat.card P * Nat.card ↥(A ⊓ M)
        = Nat.card A * (Nat.card P * Nat.card ↥(A ⊓ M)) := by ring
      _ = Nat.card A * (Nat.card M * Nat.card ↥(P ⊓ A)) := by rw [h2]
      _ = Nat.card ↥(P ⊓ A) * (Nat.card M * Nat.card A) := by ring
      _ = Nat.card ↥(P ⊓ A) * (Nat.card N * Nat.card ↥(A ⊓ M)) := by rw [h1]
      _ = Nat.card ↥(P ⊓ A) * Nat.card N * Nat.card ↥(A ⊓ M) := by ring
  have hrA : (P ⊓ A).relIndex A * Nat.card ↥(P ⊓ A) = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := P ⊓ A) (K := A)
    rwa [inf_of_le_left inf_le_right] at this
  have hrN : P.relIndex N * Nat.card P = Nat.card N := by
    have := Subgroup.relIndex_mul_card (H := P) (K := N)
    rwa [inf_of_le_left hPN] at this
  have hp0 : 0 < Nat.card P := Nat.card_pos
  have hpa0 : 0 < Nat.card ↥(P ⊓ A) := Nat.card_pos
  have heq : (P ⊓ A).relIndex A = P.relIndex N := by
    apply Nat.eq_of_mul_eq_mul_right hp0
    apply Nat.eq_of_mul_eq_mul_right hpa0
    calc (P ⊓ A).relIndex A * Nat.card P * Nat.card ↥(P ⊓ A)
        = ((P ⊓ A).relIndex A * Nat.card ↥(P ⊓ A)) * Nat.card P := by ring
      _ = Nat.card A * Nat.card P := by rw [hrA]
      _ = Nat.card ↥(P ⊓ A) * Nat.card N := h3
      _ = Nat.card ↥(P ⊓ A) * (P.relIndex N * Nat.card P) := by rw [hrN]
      _ = P.relIndex N * Nat.card P * Nat.card ↥(P ⊓ A) := by ring
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  refine ⟨inf_le_right, hP.2.1.to_le inf_le_left, ?_⟩
  rw [heq]
  exact hP.2.2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

structure Config (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) (t s : G)
    (C Y U S E L : Subgroup G) (ρ : ↥C →* SL(2, K) × SL(2, K)) : Prop where
  hK : Nat.card K = 2 ^ m
  hm : 2 ≤ m
  ht : t * t = 1
  htC : t ∈ normalizer (C : Set G)
  hsC : s ∈ C
  hYC : Y ≤ C
  hρ : Function.Surjective ρ
  hker : ρ.ker = Y.subgroupOf C
  hswap : ∀ n n' : ↥C, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap
  hYsq : ∀ y ∈ Y, y * y = 1
  hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x
  hcY : Nat.card Y = (2 ^ m) ^ 4
  hcen : Y ⊓ centralizer (C : Set G) = ⊥
  hSC : IsSylowOf 2 S C
  hYS : Y ≤ S
  hgen : C ≤ S ⊔ S.map (MulAut.conj s).toMonoidHom
  hUY : U ≤ Y
  hUt : U.map (MulAut.conj t).toMonoidHom = U
  hcU : Nat.card U = (2 ^ m) ^ 2
  hUS : U ≤ centralizer (S : Set G)
  hUs : U ⊓ U.map (MulAut.conj s).toMonoidHom = ⊥
  hES : E ≤ S
  hE : CFSG.IsElementaryAbelian 2 E
  hYES : Y ⊔ E = S
  hLC : L ≤ C
  hLt : ∀ l ∈ L, t * l * t⁻¹ = l
  hL : Nonempty (SL(2, K) ≃* ↥L)

namespace Config

variable {m : ℕ} {t s : G} {C Y U S E L : Subgroup G} {ρ : ↥C →* SL(2, K) × SL(2, K)}
  (c : Config K m t s C Y U S E L ρ)

include c

theorem four_le : 4 ≤ Nat.card K := by
  rw [c.hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) c.hm

theorem t_mem_normalizer_Y : t ∈ normalizer (Y : Set G) :=
  Common.mem_normalizer_ker_of_swap c.htC c.hswap c.hYC c.hker

theorem C_le_normalizer_Y : C ≤ normalizer (Y : Set G) := Common.le_normalizer_of_ker c.hYC c.hker

theorem Y_le_prodFst : Y ≤ Common.prodFst ρ := Common.le_prodFst c.hYC c.hker

theorem prodFst_sup_conj :
    Common.prodFst ρ ⊔ (Common.prodFst ρ).map (MulAut.conj t).toMonoidHom = C :=
  Common.prodFst_sup_map_conj c.htC c.ht c.hswap c.hρ

theorem commutator_prodFst_conj_le :
    ⁅Common.prodFst ρ, (Common.prodFst ρ).map (MulAut.conj t).toMonoidHom⁆ ≤ Y :=
  Common.commutator_prodFst_map_conj_le c.htC c.ht c.hswap c.hker

theorem prodFst_inf_conj :
    Common.prodFst ρ ⊓ (Common.prodFst ρ).map (MulAut.conj t).toMonoidHom = Y := by
  refine le_antisymm (fun z hz => ?_) (le_inf c.Y_le_prodFst ?_)
  · obtain ⟨hzΛ, hzΛt⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hzC, h2⟩ := (Common.mem_prodFst_iff ρ).1 hzΛ
    obtain ⟨hzC', h1⟩ := (Common.mem_map_conj_prodFst_iff c.htC c.ht c.hswap).1 hzΛt
    have : (⟨z, hzC⟩ : ↥C) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact Prod.ext h1 h2
    rw [c.hker, Subgroup.mem_subgroupOf] at this
    exact this
  · rw [← Common.map_conj_eq_of_mem_normalizer c.t_mem_normalizer_Y]
    exact Subgroup.map_mono c.Y_le_prodFst

theorem C_le_normalizer_prodFst : C ≤ normalizer (Common.prodFst ρ : Set G) :=
  Common.le_normalizer_prodFst ρ

theorem C_le_normalizer_conj_prodFst :
    C ≤ normalizer (((Common.prodFst ρ).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
  Common.le_normalizer_map_conj_prodFst c.htC

theorem prodFst_le_sup_conj : Common.prodFst ρ ≤ (S ⊓ Common.prodFst ρ) ⊔
    (S ⊓ Common.prodFst ρ).map (MulAut.conj s).toMonoidHom := by
  set Λ := Common.prodFst ρ with hΛdef
  set Λt := Λ.map (MulAut.conj t).toMonoidHom with hΛtdef
  obtain ⟨-, -, hSsup, -, -⟩ :=
    sylow_prod c.hSC c.prodFst_sup_conj c.prodFst_inf_conj c.commutator_prodFst_conj_le c.hYS
  have hsΛ : s ∈ normalizer (Λ : Set G) := c.C_le_normalizer_prodFst c.hsC
  have hsΛt : s ∈ normalizer (Λt : Set G) := c.C_le_normalizer_conj_prodFst c.hsC
  have hΛs : Λ.map (MulAut.conj s).toMonoidHom = Λ := Common.map_conj_eq_of_mem_normalizer hsΛ
  have hΛts : Λt.map (MulAut.conj s).toMonoidHom = Λt :=
    Common.map_conj_eq_of_mem_normalizer hsΛt
  have hΛC : Λ ≤ C := Common.prodFst_le ρ
  have hΛtC : Λt ≤ C := le_sup_right.trans c.prodFst_sup_conj.le
  set V := S ⊓ Λ with hV
  set V' := S ⊓ Λt with hV'
  set H := V ⊔ V.map (MulAut.conj s).toMonoidHom with hH
  set H' := V' ⊔ V'.map (MulAut.conj s).toMonoidHom with hH'
  have hHΛ : H ≤ Λ := sup_le inf_le_right ((Subgroup.map_mono inf_le_right).trans hΛs.le)
  have hH'Λt : H' ≤ Λt := sup_le inf_le_right ((Subgroup.map_mono inf_le_right).trans hΛts.le)
  have hVH : V ≤ H := le_sup_left
  have hYH : Y ≤ H := (le_inf c.hYS c.Y_le_prodFst).trans hVH
  have hC : C ≤ H ⊔ H' := by
    refine c.hgen.trans ?_
    rw [hSsup, Subgroup.map_sup]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
  intro l hl
  have hl' : l ∈ H ⊔ H' := hC (hΛC hl)
  have hH'H : H' ≤ normalizer (H : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ ∈ ⁅Λt, Λ⁆ := Subgroup.commutator_mem_commutator (hH'Λt hx) (hHΛ hy)
    rw [Subgroup.commutator_comm] at h1
    have h2 := hYH (c.commutator_prodFst_conj_le h1)
    rwa [commutatorElement_def] at h2
  obtain ⟨h₀, hh₀, h', hh', rfl⟩ := Common.exists_mul_of_le_normalizer hH'H l hl'
  have hh'Λ : h' ∈ Λ := by
    have := mul_mem (inv_mem (hHΛ hh₀)) hl
    rwa [inv_mul_cancel_left] at this
  have : h' ∈ Λ ⊓ Λt := ⟨hh'Λ, hH'Λt hh'⟩
  rw [c.prodFst_inf_conj] at this
  exact mul_mem hh₀ (hYH this)

theorem inf_prodFst_le_normalizer : S ⊓ Common.prodFst ρ ≤ normalizer ((((S ⊓ Common.prodFst ρ).map
    (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  set Λ := Common.prodFst ρ with hΛdef
  set Λt := Λ.map (MulAut.conj t).toMonoidHom with hΛtdef
  set Z := ((S ⊓ Λ).map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom with hZ
  have hsΛt : s ∈ normalizer (Λt : Set G) := c.C_le_normalizer_conj_prodFst c.hsC
  have hsY : s ∈ normalizer (Y : Set G) := c.C_le_normalizer_Y c.hsC
  have hY1 : Y.map (MulAut.conj t).toMonoidHom = Y :=
    Common.map_conj_eq_of_mem_normalizer c.t_mem_normalizer_Y
  have hY2 : Y.map (MulAut.conj s).toMonoidHom = Y := Common.map_conj_eq_of_mem_normalizer hsY
  have hYZ : Y ≤ Z := by
    calc Y = (Y.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
          rw [hY1, hY2]
      _ ≤ Z := Subgroup.map_mono (Subgroup.map_mono (le_inf c.hYS c.Y_le_prodFst))
  have hZΛt : Z ≤ Λt := by
    calc Z ≤ Λt.map (MulAut.conj s).toMonoidHom :=
          Subgroup.map_mono (Subgroup.map_mono inf_le_right)
      _ = Λt := Common.map_conj_eq_of_mem_normalizer hsΛt
  intro v hv
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hc : ⁅v, y⁆ ∈ Y :=
    c.commutator_prodFst_conj_le
      (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.1 hv).2 (hZΛt hy))
  have e : v * y * v⁻¹ = ⁅v, y⁆ * y := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem (hYZ hc) hy

theorem exists_perfect :
    ∃ P : Subgroup G, P ≤ Common.prodFst ρ ∧ ⁅P, P⁆ = P ∧ P ⊔ Y = Common.prodFst ρ ∧
      ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      ∀ R : Subgroup G, R ≤ Common.prodFst ρ → ⁅R, R⁆ = R → R ≤ P := by
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K c.four_le
  set Λ := Common.prodFst ρ with hΛdef
  have hV : IsSylowOf 2 (S ⊓ Λ) Λ :=
    (sylow_prod c.hSC c.prodFst_sup_conj c.prodFst_inf_conj c.commutator_prodFst_conj_le
      c.hYS).1
  have hEle : E ≤ S := c.hES
  have hE' : CFSG.IsElementaryAbelian 2 ↥(E ⊓ Λ) :=
    Common.isElementaryAbelian_mono c.hE inf_le_left
  have hEX' : Y ⊔ E ⊓ Λ = S ⊓ Λ := by
    refine le_antisymm (sup_le (le_inf c.hYS c.Y_le_prodFst) (inf_le_inf_right _ hEle)) ?_
    intro x hx
    obtain ⟨hxS, hxΛ⟩ := Subgroup.mem_inf.1 hx
    have hx' : x ∈ ((E ⊔ Y : Subgroup G) : Set G) := by
      rw [sup_comm, c.hYES]
      exact hxS
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E Y
      (fun e he => c.C_le_normalizer_Y (c.hSC.le (hEle he)))] at hx'
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.1 hx'
    have heΛ : e ∈ Λ := by
      have := mul_mem hxΛ (inv_mem (c.Y_le_prodFst hy))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨he, heΛ⟩))
      (Subgroup.mem_sup_left hy)
  refine Common.exists_perfect_commuting_factor_of_ambient c.hK c.hm (E := E ⊓ Λ) c.Y_le_prodFst
    (Common.prodFst_le ρ) c.C_le_normalizer_prodFst c.C_le_normalizer_Y c.hYsq c.hYab c.htC
    c.t_mem_normalizer_Y c.prodFst_sup_conj c.commutator_prodFst_conj_le
    (Common.le_commutator_sup_of_perfect c.hρ c.hker) (Common.prodFstHom ρ)
    (Common.surjective_prodFstHom c.hρ) (Common.ker_prodFstHom c.hker) c.hYS hV
    (inf_le_inf_right _ hEle) hE' hEX' c.hsC c.prodFst_le_sup_conj c.inf_prodFst_le_normalizer
    c.hUY c.hUS c.hUt ?_ ?_ ?_ ?_
  · rw [c.hcen]; exact bot_le
  · rw [c.hUs]; exact bot_le
  · rw [c.hcen, Subgroup.card_bot, mul_one, c.hcY]
  · rw [c.hcen, Subgroup.card_bot, mul_one, c.hcU]

theorem exists_complement_of_perfect {P : Subgroup G} (hPΛ : P ≤ Common.prodFst ρ)
    (hPY : P ⊔ Y = Common.prodFst ρ)
    (hPcomm : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPn : ∀ g ∈ C, ∀ x ∈ P, g * x * g⁻¹ ∈ P) :
    ∃ A : Subgroup G, A ≤ C ∧ A ⊓ Y = ⊥ ∧ C = A ⊔ Y ∧
      A.map (MulAut.conj t).toMonoidHom = A ∧ L ≤ A := by
  set Λ := Common.prodFst ρ with hΛdef
  set Λt := Λ.map (MulAut.conj t).toMonoidHom with hΛtdef
  have hΛsup : Λ ⊔ Λt = C := c.prodFst_sup_conj
  have hΛinf : Λ ⊓ Λt = Y := c.prodFst_inf_conj
  have hYΛ : Y ≤ Λ := c.Y_le_prodFst
  have hΛC : Λ ≤ C := Common.prodFst_le ρ
  have hΛtC : Λt ≤ C := le_sup_right.trans hΛsup.le
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.ht
  have hPC : P ≤ C := hPΛ.trans hΛC
  have hYn : ∀ g ∈ C, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    (mem_normalizer_iff.1 (c.C_le_normalizer_Y hg) y).1 hy
  have hYt : Y.map (MulAut.conj t).toMonoidHom = Y :=
    Common.map_conj_eq_of_mem_normalizer c.t_mem_normalizer_Y
  set Pt := P.map (MulAut.conj t).toMonoidHom with hPt
  have hPtΛt : Pt ≤ Λt := Subgroup.map_mono hPΛ
  have hPtC : Pt ≤ C := hPtΛt.trans hΛtC
  have hCt : ∀ g ∈ C, t⁻¹ * g * t ∈ C := by
    intro g hg
    have := (mem_normalizer_iff.1 c.htC g).1 hg
    rw [hti] at this ⊢
    exact this
  have hPtn : ∀ g ∈ C, ∀ x ∈ Pt, g * x * g⁻¹ ∈ Pt := by
    intro g hg x hx
    rw [hPt, mem_map_conj_iff'] at hx ⊢
    have := hPn (t⁻¹ * g * t) (hCt g hg) (t⁻¹ * x * t) hx
    have e : t⁻¹ * (g * x * g⁻¹) * t = (t⁻¹ * g * t) * (t⁻¹ * x * t) * (t⁻¹ * g * t)⁻¹ := by
      group
    rw [e]
    exact this
  have hPPt_comm : ∀ x ∈ P, ∀ y ∈ Pt, x * y = y * x := by
    intro x hx y hy
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hPcomm hx
    exact (mem_centralizer_iff.1 this y hy).symm
  have hΛt' : Pt ⊔ Y = Λt := by
    rw [hΛtdef, ← hPY, Subgroup.map_sup, hYt]
  set W := P ⊓ Y with hW
  have hWt : W.map (MulAut.conj t).toMonoidHom = Pt ⊓ Y := by
    rw [hW, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hYt]
  have hcen' : ∀ z ∈ Y, (∀ g ∈ C, z * g = g * z) → z = 1 := by
    intro z hz hzc
    have : z ∈ Y ⊓ centralizer (C : Set G) :=
      ⟨hz, mem_centralizer_iff.2 fun g hg => (hzc g hg).symm⟩
    rw [c.hcen, Subgroup.mem_bot] at this
    exact this
  have hC_of : ∀ z : G, (∀ g ∈ Λ, z * g = g * z) → (∀ g ∈ Λt, z * g = g * z) →
      ∀ g ∈ C, z * g = g * z := by
    intro z h1 h2 g hg
    have hle : C ≤ centralizer ({z} : Set G) := by
      rw [← hΛsup]
      exact sup_le (fun x hx => mem_centralizer_singleton_iff.2 (h1 x hx).symm)
        (fun x hx => mem_centralizer_singleton_iff.2 (h2 x hx).symm)
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hQcomm : ∀ Q : Subgroup G, Q ≤ C → (∀ g ∈ C, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) → Q ⊓ Y = ⊥ →
      ∀ q ∈ Q, ∀ y ∈ Y, q * y = y * q := by
    intro Q hQC hQn hQY q hq y hy
    have h1 : q * y * q⁻¹ * y⁻¹ ∈ Q := by
      have := mul_mem hq (hQn y (c.hYC hy) q⁻¹ (inv_mem hq))
      simpa [mul_assoc] using this
    have h2 : q * y * q⁻¹ * y⁻¹ ∈ Y := mul_mem (hYn q (hQC hq) y hy) (inv_mem hy)
    have h3 : q * y * q⁻¹ * y⁻¹ ∈ Q ⊓ Y := ⟨h1, h2⟩
    rw [hQY, Subgroup.mem_bot] at h3
    calc q * y = (q * y * q⁻¹ * y⁻¹) * (y * q) := by group
      _ = y * q := by rw [h3, one_mul]
  have hWne : W ≠ ⊥ := by
    intro hW0
    have hWt0 : Pt ⊓ Y = ⊥ := by rw [← hWt, hW0, Subgroup.map_bot]
    have hP1 := hQcomm P hPC hPn hW0
    have hP2 := hQcomm Pt hPtC hPtn hWt0
    have hY1 : ∀ y ∈ Y, y = 1 := by
      intro y hy
      refine hcen' y hy (hC_of y ?_ ?_)
      · intro g hg
        rw [← hPY] at hg
        obtain ⟨p, hp, y', hy', rfl⟩ :=
          Common.exists_mul_of_le_normalizer' (hPC.trans c.C_le_normalizer_Y) g hg
        calc y * (p * y') = (y * p) * y' := by group
          _ = (p * y) * y' := by rw [(hP1 p hp y hy).symm]
          _ = p * (y * y') := by group
          _ = p * (y' * y) := by rw [c.hYab y hy y' hy']
          _ = p * y' * y := by group
      · intro g hg
        rw [← hΛt'] at hg
        obtain ⟨p, hp, y', hy', rfl⟩ :=
          Common.exists_mul_of_le_normalizer' (hPtC.trans c.C_le_normalizer_Y) g hg
        calc y * (p * y') = (y * p) * y' := by group
          _ = (p * y) * y' := by rw [(hP2 p hp y hy).symm]
          _ = p * (y * y') := by group
          _ = p * (y' * y) := by rw [c.hYab y hy y' hy']
          _ = p * y' * y := by group
    have hYbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 hY1
    have hc := c.hcY
    rw [hYbot, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by have := c.hm; omega)
    have h2 : 1 < (2 ^ m) ^ 4 := Nat.one_lt_pow (by norm_num) h1
    omega
  have hΛtW : Λt ≤ centralizer (W : Set G) := by
    rw [← hΛt']
    refine sup_le (fun y hy => mem_centralizer_iff.2 fun w hw => ?_)
      (fun y hy => mem_centralizer_iff.2 fun w hw => ?_)
    · exact hPPt_comm w hw.1 y hy
    · exact c.hYab w hw.2 y hy
  have hΛW : ¬ Λ ≤ centralizer (W : Set G) := by
    intro h
    apply hWne
    have hCW : C ≤ centralizer (W : Set G) := by
      rw [← hΛsup]
      exact sup_le h hΛtW
    refine (Subgroup.eq_bot_iff_forall W).2 fun w hw => hcen' w hw.2 fun g hg => ?_
    exact mem_centralizer_iff.1 (hCW hg) w hw
  have hWnorm : ∀ g ∈ C, g ∈ normalizer (W : Set G) := fun g hg =>
    Common.mem_normalizer_inf (Subgroup.mem_normalizer_fintype fun x hx => hPn g hg x hx)
      (c.C_le_normalizer_Y hg)
  have hWcard : Nat.card K ^ 2 ≤ Nat.card W := by
    have hWΛ : Λ ≤ normalizer (W : Set G) := fun g hg => hWnorm g (hΛC hg)
    let ψ : ↥Λ →* MulAut ↥W := CFSG.SL2MinimalFaithful.conjAction hWΛ
    let θ : ↥Λ →* SL(2, K) := Common.prodFstHom ρ
    have hθ : Function.Surjective θ := Common.surjective_prodFstHom c.hρ
    have hker : θ.ker ≤ ψ.ker := by
      intro l hl
      have hl' : (l : G) ∈ Y := by
        have := hl
        rw [MonoidHom.mem_ker] at this
        have h2 : l ∈ θ.ker := hl
        rw [Common.ker_prodFstHom c.hker, Subgroup.mem_subgroupOf] at h2
        exact h2
      rw [MonoidHom.mem_ker]
      ext w
      rw [CFSG.SL2MinimalFaithful.conjAction_apply]
      change (l : G) * w * (l : G)⁻¹ = w
      rw [c.hYab l hl' w w.2.2]
      group
    let ψ' : SL(2, K) →* MulAut ↥W :=
      θ.liftOfRightInverse (Function.surjInv hθ) (Function.rightInverse_surjInv hθ) ⟨ψ, hker⟩
    have hψ' : ∀ l : ↥Λ, ψ' (θ l) = ψ l := fun l =>
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
    refine Common.sl2_card_sq_le_of_ne_one (MulEquiv.refl SL(2, K)) c.hK c.hm ψ'
      ((Common.isPGroup_two_of_mul_self c.hYsq).to_le inf_le_right) ?_
    intro h1
    apply hΛW
    intro l hl
    rw [mem_centralizer_iff]
    intro w hw
    have h2 := hψ' ⟨l, hl⟩
    rw [h1, MonoidHom.one_apply] at h2
    have h3 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h2
    simp only [CFSG.SL2MinimalFaithful.conjAction_apply, MulAut.one_apply] at h3
    change w = l * w * l⁻¹ at h3
    calc w * l = (l * w * l⁻¹) * l := by rw [← h3]
      _ = l * w := by group
  have hWtcard : Nat.card ↥(Pt ⊓ Y) = Nat.card W := by
    rw [← hWt]
    exact Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hWWt : W ⊓ (Pt ⊓ Y) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    obtain ⟨⟨hzP, hzY⟩, hzPt, -⟩ := hz
    refine hcen' z hzY (hC_of z ?_ ?_)
    · intro g hg
      rw [← hPY] at hg
      obtain ⟨p, hp, y', hy', rfl⟩ :=
        Common.exists_mul_of_le_normalizer' (hPC.trans c.C_le_normalizer_Y) g hg
      calc z * (p * y') = (z * p) * y' := by group
        _ = (p * z) * y' := by rw [(hPPt_comm p hp z hzPt).symm]
        _ = p * (z * y') := by group
        _ = p * (y' * z) := by rw [c.hYab z hzY y' hy']
        _ = p * y' * z := by group
    · intro g hg
      rw [← hΛt'] at hg
      obtain ⟨p, hp, y', hy', rfl⟩ :=
        Common.exists_mul_of_le_normalizer' (hPtC.trans c.C_le_normalizer_Y) g hg
      calc z * (p * y') = (z * p) * y' := by group
        _ = (p * z) * y' := by rw [hPPt_comm z hzP p hp]
        _ = p * (z * y') := by group
        _ = p * (y' * z) := by rw [c.hYab z hzY y' hy']
        _ = p * y' * z := by group
  have hWtn : W ≤ normalizer ((Pt ⊓ Y : Subgroup G) : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun y hy => c.hYab y hy.2 w hw.2)
  have hYeq : W ⊔ (Pt ⊓ Y) = Y := by
    have hWtN' : (Pt ⊓ Y) ≤ normalizer (W : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun w hw => c.hYab w hw.2 y hy.2)
    have h1 := Common.card_sup_mul_card_inf_eq hWtN'
    rw [hWWt, Subgroup.card_bot, mul_one, hWtcard] at h1
    have hle : W ⊔ (Pt ⊓ Y) ≤ Y := sup_le inf_le_right inf_le_right
    have h2 : (2 ^ m) ^ 4 ≤ Nat.card ↥(W ⊔ (Pt ⊓ Y)) := by
      rw [h1]
      calc (2 ^ m) ^ 4 = (Nat.card K ^ 2) * (Nat.card K ^ 2) := by rw [c.hK]; ring
        _ ≤ Nat.card W * Nat.card W := Nat.mul_le_mul hWcard hWcard
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [c.hcY]; exact h2)
  have hPsup : P ⊔ Pt = C := by
    refine le_antisymm (sup_le hPC hPtC) ?_
    have hYle : Y ≤ P ⊔ Pt := by
      rw [← hYeq]
      exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    rw [← hΛsup]
    refine sup_le ?_ ?_
    · rw [← hPY]
      exact sup_le le_sup_left hYle
    · rw [← hΛt']
      exact sup_le le_sup_right hYle
  have hPinf : P ⊓ Pt = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hzY : z ∈ Y := by
      have : z ∈ Λ ⊓ Λt := ⟨hPΛ hz.1, hPtΛt hz.2⟩
      rwa [hΛinf] at this
    have : z ∈ W ⊓ (Pt ⊓ Y) := ⟨⟨hz.1, hzY⟩, hz.2, hzY⟩
    rw [hWWt, Subgroup.mem_bot] at this
    exact this
  have hPPt_norm : P ≤ normalizer (Pt : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun y hy => (hPPt_comm x hx y hy).symm)
  have hmemPt : ∀ x ∈ P, t * x * t⁻¹ ∈ Pt := fun x hx => ⟨x, hx, rfl⟩
  have hLrep : ∀ b ∈ L, ∃ x ∈ P, b = x * (t * x * t⁻¹) := by
    intro b hb
    have hbC : b ∈ P ⊔ Pt := by
      rw [hPsup]
      exact c.hLC hb
    obtain ⟨x, hx, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hPPt_norm b hbC
    obtain ⟨y₀, hy₀, hyy₀⟩ : ∃ y₀ ∈ P, y = t * y₀ * t⁻¹ :=
      ⟨t⁻¹ * y * t, mem_map_conj_iff'.1 hy, by group⟩
    have hb' := c.hLt _ hb
    have e1 : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * y₀ := by
      rw [hyy₀, hti]
      calc t * (x * (t * y₀ * t)) * t = (t * x * t) * y₀ * (t * t) := by group
        _ = (t * x * t) * y₀ := by rw [c.ht, mul_one]
    have hxy : x * y = y₀ * (t * x * t⁻¹) := by
      rw [← hb', e1]
      exact (hPPt_comm y₀ hy₀ _ (hmemPt x hx)).symm
    have hdiv : y₀⁻¹ * x = (t * x * t⁻¹) * y⁻¹ := by
      calc y₀⁻¹ * x = y₀⁻¹ * (x * y) * y⁻¹ := by group
        _ = y₀⁻¹ * (y₀ * (t * x * t⁻¹)) * y⁻¹ := by rw [hxy]
        _ = (t * x * t⁻¹) * y⁻¹ := by group
    have h1 : y₀⁻¹ * x ∈ P ⊓ Pt := Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hy₀) hx, by rw [hdiv]; exact mul_mem (hmemPt x hx) (inv_mem hy)⟩
    rw [hPinf, Subgroup.mem_bot] at h1
    have hxy₀ : y₀ = x := inv_mul_eq_one.1 h1
    refine ⟨x, hx, ?_⟩
    rw [hyy₀, hxy₀]
  have hLY : L ⊓ Y = ⊥ := by
    haveI : IsSimpleGroup SL(2, K) := Common.sl2_isSimpleGroup_of_charTwo c.four_le
    obtain ⟨e⟩ := c.hL
    haveI : IsSimpleGroup ↥L := e.symm.isSimpleGroup
    have hnorm : ((L ⊓ Y).subgroupOf L).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g.2 hx.1) (inv_mem g.2),
        hYn g (c.hLC g.2) x hx.2⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ Y).subgroupOf L) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ Y).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_exists_mul_ne (K := K)
      apply hab
      have hLY' : ∀ x : ↥L, (x : G) ∈ Y := fun x => by
        have : x ∈ (L ⊓ Y).subgroupOf L := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.1 this).2
      have hcomm := c.hYab (e a : G) (hLY' _) (e b) (hLY' _)
      have : e (a * b) = e (b * a) := Subtype.ext (by simpa using hcomm)
      exact e.injective this
  let B₁ : Subgroup G :=
    { carrier := {x | x ∈ P ∧ x * (t * x * t⁻¹) ∈ L}
      mul_mem' := by
        rintro a b ⟨haP, haL⟩ ⟨hbP, hbL⟩
        refine ⟨mul_mem haP hbP, ?_⟩
        have hc := hPPt_comm b hbP _ (hmemPt a haP)
        have e : a * b * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
          calc a * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
            _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
            _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group
        rw [e]
        exact mul_mem haL hbL
      one_mem' := by
        refine ⟨one_mem P, ?_⟩
        simp
      inv_mem' := by
        rintro x ⟨hxP, hxL⟩
        refine ⟨inv_mem hxP, ?_⟩
        have hc := hPPt_comm x⁻¹ (inv_mem hxP) _ (inv_mem (hmemPt x hxP))
        have e : x⁻¹ * (t * x⁻¹ * t⁻¹) = (x * (t * x * t⁻¹))⁻¹ := by
          calc x⁻¹ * (t * x⁻¹ * t⁻¹) = x⁻¹ * (t * x * t⁻¹)⁻¹ := by group
            _ = (t * x * t⁻¹)⁻¹ * x⁻¹ := hc
            _ = (x * (t * x * t⁻¹))⁻¹ := by group
        rw [e]
        exact inv_mem hxL }
  have hB₁mem : ∀ x, x ∈ B₁ ↔ x ∈ P ∧ x * (t * x * t⁻¹) ∈ L := fun x => Iff.rfl
  have hB₁P : B₁ ≤ P := fun x hx => ((hB₁mem x).1 hx).1
  have hB₁W : B₁ ⊓ W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨hxB, hxP', hxY⟩ := hx
    have hxL := ((hB₁mem x).1 hxB).2
    have hxt : t * x * t⁻¹ ∈ Y := (mem_normalizer_iff.1 c.t_mem_normalizer_Y x).1 hxY
    have hb : x * (t * x * t⁻¹) ∈ L ⊓ Y := ⟨hxL, mul_mem hxY hxt⟩
    rw [hLY, Subgroup.mem_bot] at hb
    have hxPt : x ∈ Pt := by
      have : x = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hb
      rw [this]
      exact inv_mem (hmemPt x hxP')
    have : x ∈ P ⊓ Pt := ⟨hxP', hxPt⟩
    rw [hPinf, Subgroup.mem_bot] at this
    exact this
  have hLcard : Nat.card B₁ = Nat.card SL(2, K) := by
    have hbij : Function.Bijective
        (fun x : B₁ => (⟨(x : G) * (t * x * t⁻¹), ((hB₁mem x).1 x.2).2⟩ : ↥L)) := by
      refine ⟨fun x y hxy => ?_, fun b => ?_⟩
      · obtain ⟨a, ha⟩ := x
        obtain ⟨b, hb⟩ := y
        have hxy' : a * (t * a * t⁻¹) = b * (t * b * t⁻¹) := congrArg Subtype.val hxy
        have haP : a ∈ P := ((hB₁mem a).1 ha).1
        have hbP : b ∈ P := ((hB₁mem b).1 hb).1
        have : b⁻¹ * a = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by
          calc b⁻¹ * a = b⁻¹ * (a * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
            _ = b⁻¹ * (b * (t * b * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [hxy']
            _ = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
        have h1 : b⁻¹ * a ∈ P ⊓ Pt := Subgroup.mem_inf.2
          ⟨mul_mem (inv_mem hbP) haP, by
            rw [this]; exact mul_mem (hmemPt b hbP) (inv_mem (hmemPt a haP))⟩
        rw [hPinf, Subgroup.mem_bot] at h1
        exact Subtype.ext (inv_mul_eq_one.1 h1).symm
      · obtain ⟨x, hx, hbx⟩ := hLrep b b.2
        exact ⟨⟨x, (hB₁mem x).2 ⟨hx, hbx ▸ b.2⟩⟩, Subtype.ext hbx.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).trans
      (Nat.card_congr c.hL.some.toEquiv).symm
  have hPcard : Nat.card P = Nat.card W * Nat.card SL(2, K) := by
    let θP : ↥P →* SL(2, K) := (Common.prodFstHom ρ).comp (Subgroup.inclusion hPΛ)
    have hθP : Function.Surjective θP := by
      intro g
      obtain ⟨l, rfl⟩ := Common.surjective_prodFstHom c.hρ g
      have hl : (l : G) ∈ P ⊔ Y := by rw [hPY]; exact l.2
      obtain ⟨p, hp, y, hy, hpy⟩ :=
        Common.exists_mul_of_le_normalizer' (hPC.trans c.C_le_normalizer_Y) _ hl
      refine ⟨⟨p, hp⟩, ?_⟩
      have hy' : (⟨y, c.Y_le_prodFst hy⟩ : ↥Λ) ∈ (Common.prodFstHom ρ).ker := by
        rw [Common.ker_prodFstHom c.hker, Subgroup.mem_subgroupOf]
        exact hy
      have hl' : l = Subgroup.inclusion hPΛ ⟨p, hp⟩ * ⟨y, c.Y_le_prodFst hy⟩ := Subtype.ext hpy
      show (Common.prodFstHom ρ) (Subgroup.inclusion hPΛ ⟨p, hp⟩) = (Common.prodFstHom ρ) l
      rw [hl', map_mul, MonoidHom.mem_ker.1 hy', mul_one]
    have hkerP : θP.ker = W.subgroupOf P := by
      ext p
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (Common.prodFstHom ρ) (Subgroup.inclusion hPΛ p) = 1 ↔ _
      rw [← MonoidHom.mem_ker, Common.ker_prodFstHom c.hker, Subgroup.mem_subgroupOf]
      exact ⟨fun h => Subgroup.mem_inf.2 ⟨p.2, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩
    have := Subgroup.card_ker_mul_card_of_surjective hθP
    rw [hkerP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ P)).toEquiv]
      at this
    exact this.symm
  have hPeq : B₁ ⊔ W = P := by
    have hBWn : B₁ ≤ normalizer (W : Set G) := fun x hx => hWnorm x (hPC (hB₁P hx))
    have h1 := Common.card_sup_mul_card_inf_eq (A := W) (B := B₁) hBWn
    rw [inf_comm, hB₁W, Subgroup.card_bot, mul_one, hLcard] at h1
    have hle : W ⊔ B₁ ≤ P := sup_le inf_le_left hB₁P
    rw [sup_comm]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hPcard])
  have hB₁t : B₁ ≤ normalizer ((B₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun y hy =>
        (hPPt_comm x (hB₁P hx) y (Subgroup.map_mono hB₁P hy)).symm)
  have hAC : B₁ ⊔ B₁.map (MulAut.conj t).toMonoidHom ≤ C :=
    sup_le (hB₁P.trans hPC) ((Subgroup.map_mono hB₁P).trans hPtC)
  refine ⟨B₁ ⊔ B₁.map (MulAut.conj t).toMonoidHom, hAC, ?_, ?_, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    obtain ⟨hzA, hzY⟩ := hz
    obtain ⟨x, hx, y', hy', rfl⟩ := Common.exists_mul_of_le_normalizer' hB₁t z hzA
    rw [← hYeq] at hzY
    obtain ⟨w, hw, w', hw', hzw⟩ := Common.exists_mul_of_le_normalizer' hWtn _ hzY
    have h1 : w⁻¹ * x = w' * y'⁻¹ := by
      calc w⁻¹ * x = w⁻¹ * (x * y') * y'⁻¹ := by group
        _ = w⁻¹ * (w * w') * y'⁻¹ := by rw [hzw]
        _ = w' * y'⁻¹ := by group
    have h2 : w⁻¹ * x ∈ P ⊓ Pt := Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hw.1) (hB₁P hx), by
        rw [h1]; exact mul_mem hw'.1 (inv_mem (Subgroup.map_mono hB₁P hy'))⟩
    rw [hPinf, Subgroup.mem_bot] at h2
    have hxw : x = w := (inv_mul_eq_one.1 h2).symm
    have hy'w' : y' = w' := by
      have : w' * y'⁻¹ = 1 := by rw [← h1, h2]
      exact (mul_inv_eq_one.1 this).symm
    have hx1 : x = 1 := by
      have : x ∈ B₁ ⊓ W := ⟨hx, hxw ▸ hw⟩
      rw [hB₁W, Subgroup.mem_bot] at this
      exact this
    have hy1 : y' = 1 := by
      have : y' ∈ B₁.map (MulAut.conj t).toMonoidHom ⊓ (Pt ⊓ Y) := ⟨hy', hy'w' ▸ hw'⟩
      rw [← hWt, ← Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hB₁W, Subgroup.map_bot,
        Subgroup.mem_bot] at this
      exact this
    rw [hx1, hy1, one_mul]
  · refine le_antisymm ?_ (sup_le hAC c.hYC)
    rw [← hPsup]
    refine sup_le ?_ ?_
    · rw [← hPeq]
      exact sup_le (le_sup_left.trans le_sup_left) (inf_le_right.trans le_sup_right)
    · have : Pt = (B₁ ⊔ W).map (MulAut.conj t).toMonoidHom := by rw [hPeq]
      rw [this, Subgroup.map_sup]
      refine sup_le (le_sup_right.trans le_sup_left) ?_
      rw [hWt]
      exact inf_le_right.trans le_sup_right
  · rw [Subgroup.map_sup, map_conj_conj c.ht, sup_comm]
  · intro b hb
    obtain ⟨x, hx, hbx⟩ := hLrep b hb
    have hxB : x ∈ B₁ := (hB₁mem x).2 ⟨hx, hbx ▸ hb⟩
    rw [hbx]
    exact mul_mem (Subgroup.mem_sup_left hxB)
      (Subgroup.mem_sup_right ⟨x, hxB, rfl⟩)

theorem exists_complement : ∃ A : Subgroup G, A ≤ C ∧ A ⊓ Y = ⊥ ∧ C = A ⊔ Y ∧
    A.map (MulAut.conj t).toMonoidHom = A ∧ L ≤ A := by
  obtain ⟨P, hPΛ, hPperf, hPY, hPcomm, hPmax⟩ := c.exists_perfect
  refine c.exists_complement_of_perfect hPΛ hPY hPcomm ?_
  intro g hg x hx
  have hgΛ : g ∈ normalizer (Common.prodFst ρ : Set G) := c.C_le_normalizer_prodFst hg
  have hR : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    refine hPmax _ ?_ ?_
    · rw [← Common.map_conj_eq_of_mem_normalizer hgΛ]
      exact Subgroup.map_mono hPΛ
    · rw [← Subgroup.map_commutator, hPperf]
  exact hR ⟨x, hx, rfl⟩

end Config

theorem exists_complement_of_data {m : ℕ} {t s : G} {N M P C Y U E L : Subgroup G}
    (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) (ht : t * t = 1)
    (htC : t ∈ normalizer (C : Set G))
    (hNM : N ≤ normalizer (M : Set G)) (hsM : s ∈ normalizer (M : Set G)) (hsC : s ∈ C)
    (hMP : M ≤ P) (hPN : P ≤ N) (hCN : C ≤ N) (hCM : C ⊓ M = Y) (hsup : C ⊔ M = N)
    (hNP : N = P ⊔ P.map (MulAut.conj s).toMonoidHom) (hPsyl : IsSylowOf 2 P N)
    (ρ : ↥N →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = M.subgroupOf N)
    (hswap : ∀ n n' : ↥N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap)
    (hYsq : ∀ y ∈ Y, y * y = 1) (hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hcY : Nat.card Y = (2 ^ m) ^ 4)
    (hMY : ∀ x ∈ M, ∀ y ∈ Y, x * y = y * x) (hZN : N ⊓ centralizer (N : Set G) = ⊥)
    (hUY : U ≤ Y) (hUt : U.map (MulAut.conj t).toMonoidHom = U)
    (hcU : Nat.card U = (2 ^ m) ^ 2) (hUP : U ≤ centralizer (P : Set G))
    (hUs : U ⊓ U.map (MulAut.conj s).toMonoidHom = ⊥)
    (hES : E ≤ P ⊓ C) (hE : CFSG.IsElementaryAbelian 2 E) (hYE : Y ⊔ E = P ⊓ C)
    (hLC : L ≤ C) (hLt : ∀ l ∈ L, t * l * t⁻¹ = l) (hL : Nonempty (SL(2, K) ≃* ↥L)) :
    ∃ A : Subgroup G, A ≤ C ∧ A ⊓ M = ⊥ ∧ N = A ⊔ M ∧
      A.map (MulAut.conj t).toMonoidHom = A ∧ L ≤ A := by
  have hYC : Y ≤ C := hCM ▸ inf_le_left
  have hYM : Y ≤ M := hCM ▸ inf_le_right
  have hCM' : C ≤ normalizer (M : Set G) := hCN.trans hNM
  have hMN : M ≤ N := hMP.trans hPN
  let ρ' : ↥C →* SL(2, K) × SL(2, K) := ρ.comp (Subgroup.inclusion hCN)
  have hker' : ρ'.ker = Y.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ρ (Subgroup.inclusion hCN c) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    constructor
    · intro hc
      rw [← hCM]
      exact ⟨c.2, hc⟩
    · intro hc
      rw [← hCM] at hc
      exact hc.2
  have hρ' : Function.Surjective ρ' := by
    intro g
    obtain ⟨n, rfl⟩ := hρ g
    have hn : (n : G) ∈ C ⊔ M := by rw [hsup]; exact n.2
    obtain ⟨c, hc, mm, hm', hcm⟩ := Common.exists_mul_of_le_normalizer' hCM' _ hn
    refine ⟨⟨c, hc⟩, ?_⟩
    have hmm : (⟨mm, hMN hm'⟩ : ↥N) ∈ ρ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hm'
    have hn' : n = Subgroup.inclusion hCN ⟨c, hc⟩ * ⟨mm, hMN hm'⟩ := Subtype.ext hcm
    show ρ (Subgroup.inclusion hCN ⟨c, hc⟩) = ρ n
    rw [hn', map_mul, MonoidHom.mem_ker.1 hmm, mul_one]
  have hcen : Y ⊓ centralizer (C : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    obtain ⟨hzY, hzC⟩ := hz
    have hle : N ≤ centralizer ({z} : Set G) := by
      rw [← hsup]
      refine sup_le (fun c hc => mem_centralizer_singleton_iff.2 ?_)
        (fun x hx => mem_centralizer_singleton_iff.2 ?_)
      · exact mem_centralizer_iff.1 hzC c hc
      · exact (hMY x hx z hzY)
    have : z ∈ N ⊓ centralizer (N : Set G) := by
      refine ⟨hCN (hYC hzY), mem_centralizer_iff.2 fun n hn => ?_⟩
      exact mem_centralizer_singleton_iff.1 (hle hn)
    rw [hZN, Subgroup.mem_bot] at this
    exact this
  have hSC : IsSylowOf 2 (P ⊓ C) C := by
    have := isSylowOf_inf_of_sup_eq hPsyl hMP hNM hCN hsup
    exact this
  have c : Config K m t s C Y U (P ⊓ C) E L ρ' :=
    { hK := hK, hm := hm, ht := ht, htC := htC, hsC := hsC, hYC := hYC, hρ := hρ'
      hker := hker'
      hswap := fun n n' hn => hswap ⟨n, hCN n.2⟩ ⟨n', hCN n'.2⟩ hn
      hYsq := hYsq, hYab := hYab, hcY := hcY, hcen := hcen, hSC := hSC
      hYS := le_inf (hYM.trans hMP) hYC
      hgen := le_sup_map_conj_of_sup_eq hNP hMP hPN hNM hsM hCN hsup hsC
      hUY := hUY, hUt := hUt, hcU := hcU
      hUS := hUP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))
      hUs := hUs, hES := hES, hE := hE, hYES := hYE, hLC := hLC, hLt := hLt, hL := hL }
  obtain ⟨A, hAC, hAY, hCA, hAt, hLA⟩ := c.exists_complement
  refine ⟨A, hAC, ?_, ?_, hAt, hLA⟩
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have : x ∈ A ⊓ Y := ⟨hx.1, hCM ▸ ⟨hAC hx.1, hx.2⟩⟩
    rw [hAY, Subgroup.mem_bot] at this
    exact this
  · rw [← hsup, hCA]
    refine le_antisymm (sup_le (sup_le le_sup_left (hYM.trans le_sup_right)) le_sup_right) ?_
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

end Abstract

end ProductComplementFourAux

namespace Setup

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (ProductAlternative)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Four

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_complement₂_four_core (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4)
    (hsyl₂ : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t))
    {α₂ : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex₂ : ExactClosure (yamadaBarK₂ d t) α₂ (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hprod : ProductAlternative (yamadaBarK₂ d t) α₂ (yamadaT₂ d t))
    (hc₂ : yamadaN₂ d t = (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊔ yamadaM₆ d t)
    (hLevi : d.leviB ≤ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) :
    ∃ A : Subgroup G, Complement₂ d t A := by
  have hD := hQ.doubling
  have ht2 : t * t = 1 := h.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨-, htN, htM⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    SeriesN2Aux.K₂_le_normalizer hW h d hK hQ
  have hNM : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    SeriesN2Aux.N₂_le_normalizer_M₆ hW h d hK hQ
  have hbar := barSub_yamadaN₂ d t hKN
  have hτ : orderOf (barMap (yamadaM₆ d t) ⟨t, htN⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (⟨t, htN⟩ * ⟨t, htN⟩ : normalizer (yamadaM₆ d t : Set G)) = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact htM
        ((CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff).1 h1)
  have hPA' : ProductAlternative (barSub (yamadaM₆ d t) (yamadaK₂ d)) α₂
      (barMap (yamadaM₆ d t) ⟨t, htN⟩) := by
    rw [← yamadaT₂_eq d htN]
    exact hprod
  obtain ⟨ρ, hρ, hker, hswap⟩ :=
    ProductDefsAux.exists_rho (X := yamadaM₆ d t) (CU := yamadaK₂ d) (NC := yamadaN₂ d t)
      hNM hbar htN hτ α₂ hPA'
  have hMP : yamadaM₆ d t ≤ yamadaP d t := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hPN : yamadaP d t ≤ yamadaN₂ d t := SeriesN2Aux.P_le_N₂ hW h d hK hQ hex₂
  have hCN : yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) ≤ yamadaN₂ d t := inf_le_left
  have hCM := h.yamada_5_60_3_four hW d hK hQ hK4
  have hNP := SeriesN2Aux.N₂_eq_P_sup hW h d hK hQ hex₂
  have hsM : d.wb ∈ normalizer (yamadaM₆ d t : Set G) := h.wb_mem_normalizer_yamadaM₆ d hK
  have hsC : d.wb ∈ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) := hLevi d.wb_mem_leviB
  have htN₂ : t ∈ normalizer (yamadaN₂ d t : Set G) :=
    SeriesCentersAux.t_mem_normalizer_N₂ hW h d hK hQ
  have htJ : t ∈ centralizer (d.J₄ : Set G) := by
    rw [← (d.yamada_3_9_4_four_G hK4).1]
    exact h.t_mem_centralizer_J₁ d
  have htC : t ∈ normalizer ((yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) : Subgroup G) : Set G) :=
    Common.mem_normalizer_inf htN₂
      (mem_normalizer_centralizer_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ htJ))
  have hYsq : ∀ y ∈ yamadaY₂ d t, y * y = 1 := fun y hy =>
    h.yamadaY₂_mul_self hW d hK hD hy
  have hYab : ∀ x ∈ yamadaY₂ d t, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    h.yamadaY₂_mul_comm d hK hD hx hy
  have hcY : Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 := by
    rw [h.card_yamadaY₂ d hK hD, hK]
  have hMY : ∀ x ∈ yamadaM₆ d t, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (Setup.Q44.M₆_le_centralizer_Y₂ hW h d hK hQ hx) y hy).symm
  have hZN := (h.yamadaN₂_centers hW d hK hQ hsyl₂ hex₂).2.2.2.2.2
  have hUt : (yamadaU₁ d t).map (MulAut.conj t).toMonoidHom = yamadaU₁ d t :=
    Common.map_conj_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaU₁ d hK hD).1
  have hcU : Nat.card (yamadaU₁ d t) = (2 ^ f) ^ 2 := by
    rw [hD.card_eq, hK]
  have hUP : yamadaU₁ d t ≤ centralizer (yamadaP d t : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun g hg => by
      have := ((SeriesN2Aux.mem_U₁_iff hW h d hK hQ).1 hx).2 g hg
      rw [← commutatorElement_def] at this
      exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  obtain ⟨E, hEC, -, hYE, hEel⟩ := h.yamada_5_60_3_complement_four hW d hK hQ hK4
  have hPC : yamadaP d t ⊓ (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) =
      yamadaP d t ⊓ centralizer (d.J₄ : Set G) := by
    rw [← inf_assoc, inf_of_le_left hPN]
  have hLt : ∀ l ∈ d.leviB, t * l * t⁻¹ = l := fun l hl => by
    have := mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hl))
    calc t * l * t⁻¹ = (l * t) * t⁻¹ := by rw [this]
      _ = l := by group
  obtain ⟨A, hAC, hAM, hAN, hAt, hLA⟩ := ProductComplementFourAux.exists_complement_of_data
    (K := K) (m := f) hK h.two_le ht2 htC hNM hsM hsC hMP hPN hCN hCM
    (hc₂.symm) hNP hsyl₂ ρ hρ hker hswap hYsq hYab hcY hMY hZN
    (Setup.yamadaU₁_le_yamadaY₂ d t) hUt hcU hUP
    (h.yamadaU₁_inf_map_wb d hK hD) (by rw [hPC]; exact hEC) hEel (by rw [hPC]; exact hYE)
    hLevi hLt (d.yamada_3_11_G.2.1)
  refine ⟨A, { le_cen := hAC, inf_eq := hAM, sup_eq := hAN, conj_eq := ?_, levi_le := hLA }⟩
  show A.map (MulAut.conj t⁻¹).toMonoidHom = A
  rw [hti]
  exact hAt

end Four

section Wrapper

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_complement₂_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4)
    (hsyl₂ : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t))
    {α₂ : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex₂ : ExactClosure (yamadaBarK₂ d t) α₂ (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hprod : ProductAlternative (yamadaBarK₂ d t) α₂ (yamadaT₂ d t)) :
    ∃ A : Subgroup G, Complement₂ d t A := by
  obtain ⟨hc₂, hLevi⟩ := h.yamada_5_60_2 hW d hK hQ
  exact h.exists_complement₂_four_core hW d hK hQ hK4 hsyl₂ hex₂ hprod hc₂ hLevi

end Wrapper

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
