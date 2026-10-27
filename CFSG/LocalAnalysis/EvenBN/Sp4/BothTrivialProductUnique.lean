module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductDiag
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.EvenBN.Common (prodFst prodFstHom)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (ProductAlternative FieldAlternative)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
open scoped MatrixGroups Matrix

namespace UniqueAux

section Abstract

variable {G : Type*} [Group G]

theorem uq_mem_map_conj_iff {M : Subgroup G} {y g : G} :
    g ∈ M.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * g * y ∈ M := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem uq_conj_mem {H : Subgroup G} {y g : G} (hy : y ∈ normalizer (H : Set G)) (hg : g ∈ H) :
    y * g * y⁻¹ ∈ H :=
  (mem_normalizer_iff.1 hy g).1 hg

theorem uq_conj_inv_mem {H : Subgroup G} {y g : G} (hy : y ∈ normalizer (H : Set G))
    (hg : g ∈ H) : y⁻¹ * g * y ∈ H := by
  simpa using (mem_normalizer_iff.1 (inv_mem hy) g).1 hg

structure IsMid (N X M : Subgroup G) : Prop where
  X_le : X ≤ M
  le_N : M ≤ N
  conj_mem : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M
  exists_not_X : ∃ g ∈ M, g ∉ X
  exists_not_M : ∃ g ∈ N, g ∉ M

theorem IsMid.map_conj {N X M : Subgroup G} (hM : IsMid N X M) {y : G}
    (hyN : y ∈ normalizer (N : Set G)) (hyX : y ∈ normalizer (X : Set G)) :
    IsMid N X (M.map (MulAut.conj y).toMonoidHom) where
  X_le x hx := by
    rw [uq_mem_map_conj_iff]
    exact hM.X_le (uq_conj_inv_mem hyX hx)
  le_N g hg := by
    obtain ⟨m, hm, rfl⟩ := hg
    exact uq_conj_mem hyN (hM.le_N hm)
  conj_mem n hn g hg := by
    rw [uq_mem_map_conj_iff] at hg ⊢
    have h1 := hM.conj_mem (y⁻¹ * n * y) (uq_conj_inv_mem hyN hn) _ hg
    have e : y⁻¹ * (n * g * n⁻¹) * y = (y⁻¹ * n * y) * (y⁻¹ * g * y) * (y⁻¹ * n * y)⁻¹ := by
      group
    rw [e]
    exact h1
  exists_not_X := by
    obtain ⟨g, hg, hgX⟩ := hM.exists_not_X
    refine ⟨y * g * y⁻¹, ⟨g, hg, rfl⟩, fun h => hgX ?_⟩
    have e : y⁻¹ * (y * g * y⁻¹) * y = g := by group
    rw [← e]
    exact uq_conj_inv_mem hyX h
  exists_not_M := by
    obtain ⟨g, hgN, hgM⟩ := hM.exists_not_M
    refine ⟨y * g * y⁻¹, uq_conj_mem hyN hgN, fun h => hgM ?_⟩
    rw [uq_mem_map_conj_iff] at h
    have e : y⁻¹ * (y * g * y⁻¹) * y = g := by group
    rw [e] at h
    exact h

theorem IsMid.eq_prodFst_or {K : Type*} [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {N X M : Subgroup G} {t : G} {ρ : N →* SL(2, K) × SL(2, K)}
    (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N)
    (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap) (hM : IsMid N X M) :
    M = prodFst ρ ∨ M = (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
  set H : Subgroup (SL(2, K) × SL(2, K)) := (M.subgroupOf N).map ρ with hH
  have hpre : ∀ n : N, ρ n ∈ H → (n : G) ∈ M := by
    rintro n ⟨m, hm, hmn⟩
    have hk : m⁻¹ * n ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmn, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at hk
    have h2 := mul_mem (mem_subgroupOf.1 hm) (hM.X_le hk)
    simpa using h2
  have hnorm : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hh
    obtain ⟨n, rfl⟩ := hρ g
    refine ⟨n * m * n⁻¹, mem_subgroupOf.2 ?_, by simp⟩
    exact hM.conj_mem n n.2 m (mem_subgroupOf.1 hm)
  rcases Common.normal_sl2_prod_eq h4 hnorm with h | h | h | h
  · exfalso
    obtain ⟨g, hg, hgX⟩ := hM.exists_not_X
    have hgN : g ∈ N := hM.le_N hg
    apply hgX
    have h1 : ρ ⟨g, hgN⟩ ∈ H := ⟨⟨g, hgN⟩, mem_subgroupOf.2 hg, rfl⟩
    rw [h, mem_bot] at h1
    have h2 : (⟨g, hgN⟩ : N) ∈ ρ.ker := h1
    rw [hker, mem_subgroupOf] at h2
    exact h2
  · left
    ext g
    constructor
    · intro hg
      have hgN : g ∈ N := hM.le_N hg
      have h1 : ρ ⟨g, hgN⟩ ∈ H := ⟨⟨g, hgN⟩, mem_subgroupOf.2 hg, rfl⟩
      rw [h, mem_prod] at h1
      exact (Common.mem_prodFst_iff ρ).2 ⟨hgN, mem_bot.1 h1.2⟩
    · intro hg
      obtain ⟨hgN, h2⟩ := (Common.mem_prodFst_iff ρ).1 hg
      refine hpre ⟨g, hgN⟩ ?_
      rw [h, mem_prod]
      exact ⟨mem_top _, mem_bot.2 h2⟩
  · right
    ext g
    constructor
    · intro hg
      have hgN : g ∈ N := hM.le_N hg
      have h1 : ρ ⟨g, hgN⟩ ∈ H := ⟨⟨g, hgN⟩, mem_subgroupOf.2 hg, rfl⟩
      rw [h, mem_prod] at h1
      exact (Common.mem_map_conj_prodFst_iff htN ht2 hswap).2 ⟨hgN, mem_bot.1 h1.1⟩
    · intro hg
      obtain ⟨hgN, h2⟩ := (Common.mem_map_conj_prodFst_iff htN ht2 hswap).1 hg
      refine hpre ⟨g, hgN⟩ ?_
      rw [h, mem_prod]
      exact ⟨mem_bot.2 h2, mem_top _⟩
  · exfalso
    obtain ⟨g, hgN, hgM⟩ := hM.exists_not_M
    exact hgM (hpre ⟨g, hgN⟩ (by rw [h]; exact mem_top _))

theorem mem_normalizer_prodFst_of_odd_aux {K : Type*} [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {N X : Subgroup G} {t : G} {ρ : N →* SL(2, K) × SL(2, K)}
    (hρ : Function.Surjective ρ) (hXN : X ≤ N) (hker : ρ.ker = X.subgroupOf N)
    (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    {y : G} (hyN : y ∈ normalizer (N : Set G)) (hyX : y ∈ normalizer (X : Set G))
    (hy : Odd (orderOf y)) : y ∈ normalizer ((prodFst ρ : Subgroup G) : Set G) := by
  have : Nontrivial SL(2, K) := (Common.sl2_isSimpleGroup_of_charTwo h4).toNontrivial
  obtain ⟨a, ha⟩ := exists_ne (1 : SL(2, K))
  have hmid : IsMid N X (prodFst ρ) := by
    refine ⟨Common.le_prodFst hXN hker, Common.prodFst_le ρ,
      fun n hn m hm => Common.conj_mem_prodFst ρ hn hm, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := hρ (a, 1)
      refine ⟨n, (Common.mem_prodFst_iff ρ).2 ⟨n.2, congrArg Prod.snd hn⟩, fun hnX => ?_⟩
      have h1 : n ∈ ρ.ker := by
        rw [hker, mem_subgroupOf]
        exact hnX
      rw [MonoidHom.mem_ker, hn] at h1
      exact ha (congrArg Prod.fst h1)
    · obtain ⟨n, hn⟩ := hρ (1, a)
      refine ⟨n, n.2, fun hnΛ => ?_⟩
      obtain ⟨_, h2⟩ := (Common.mem_prodFst_iff ρ).1 hnΛ
      exact ha ((congrArg Prod.snd hn).symm.trans h2)
  have hne : prodFst ρ ≠ (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    intro heq
    obtain ⟨n, hn⟩ := hρ (a, 1)
    have h1 : (n : G) ∈ prodFst ρ := (Common.mem_prodFst_iff ρ).2 ⟨n.2, congrArg Prod.snd hn⟩
    rw [heq] at h1
    obtain ⟨_, h2⟩ := (Common.mem_map_conj_prodFst_iff htN ht2 hswap).1 h1
    exact ha ((congrArg Prod.fst hn).symm.trans h2)
  have hmid1 := hmid.map_conj hyN hyX
  rcases hmid1.eq_prodFst_or h4 hρ hker htN ht2 hswap with h1 | h1
  · exact Common.mem_normalizer_of_map_conj_eq h1
  · have hmid2 := hmid1.map_conj hyN hyX
    rcases hmid2.eq_prodFst_or h4 hρ hker htN ht2 hswap with h2 | h2
    · have hall : ∀ w, w ∈ prodFst ρ ↔ y⁻¹ * (y⁻¹ * w * y) * y ∈ prodFst ρ := fun w => by
        have e : w ∈ ((prodFst ρ).map (MulAut.conj y).toMonoidHom).map
            (MulAut.conj y).toMonoidHom ↔ w ∈ prodFst ρ := by rw [h2]
        rw [← e, uq_mem_map_conj_iff, uq_mem_map_conj_iff]
      have hyy : y * y ∈ normalizer ((prodFst ρ : Subgroup G) : Set G) := by
        refine mem_normalizer_iff.2 fun z => ?_
        have h3 := hall ((y * y) * z * (y * y)⁻¹)
        rw [show y⁻¹ * (y⁻¹ * ((y * y) * z * (y * y)⁻¹) * y) * y = z by group] at h3
        exact h3.symm
      obtain ⟨k, hk⟩ := hy
      have h4' : y ^ (2 * k + 1) = 1 := by
        rw [← hk]
        exact pow_orderOf_eq_one y
      have h5 : (y * y) ^ (k + 1) = y := by
        rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h4',
          one_mul]
      rw [← h5]
      exact pow_mem hyy (k + 1)
    · exfalso
      apply hne
      have h3 : ((prodFst ρ).map (MulAut.conj y).toMonoidHom).map
          (MulAut.conj y).toMonoidHom = (prodFst ρ).map (MulAut.conj y).toMonoidHom :=
        h2.trans h1.symm
      have h4' : (prodFst ρ).map (MulAut.conj y).toMonoidHom = prodFst ρ :=
        Subgroup.map_injective (MulAut.conj y).injective h3
      exact h4'.symm.trans h1

end Abstract

section Core

variable {G : Type*} [Group G] {S : Type*} [Group S]

abbrev cB (X : Subgroup G) {N : Subgroup G} (ρ : N →* S × S) : Subgroup G :=
  X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G)

abbrev cBt (X : Subgroup G) (t : G) {N : Subgroup G} (ρ : N →* S × S) : Subgroup G :=
  X ⊓ centralizer (((prodFst ρ).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)

theorem uq_conj_mem_centralizer_map {t : G} {H : Subgroup G} {z : G}
    (hz : z ∈ centralizer (H : Set G)) :
    t * z * t⁻¹ ∈ centralizer ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  have h1 := mem_centralizer_iff.1 hz h hh
  show t * h * t⁻¹ * (t * z * t⁻¹) = t * z * t⁻¹ * (t * h * t⁻¹)
  calc t * h * t⁻¹ * (t * z * t⁻¹) = t * (h * z) * t⁻¹ := by group
    _ = t * (z * h) * t⁻¹ := by rw [h1]
    _ = t * z * t⁻¹ * (t * h * t⁻¹) := by group

theorem uq_map_conj_map_conj {t : G} (ht2 : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  ext g
  rw [uq_mem_map_conj_iff, uq_mem_map_conj_iff]
  have e : t⁻¹ * (t⁻¹ * g * t) * t = g := by
    rw [show t⁻¹ * (t⁻¹ * g * t) * t = (t * t)⁻¹ * g * (t * t) by group, ht2]
    group
  rw [e]

theorem uq_vec_eq_zero {K : Type*} [Field K] {v : Fin 2 → K}
    (h : ∀ M : SL(2, K), (M : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) : v = 0 := by
  have h₁ := congrFun (h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩) 0
  have h₂ := congrFun (h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩) 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₁ h₂
  funext i
  fin_cases i
  · simpa using h₂
  · simpa using h₁

section Decomposition

variable {N X P : Subgroup G} {t : G} {ρ : N →* S × S} (d : ProductDiagData N X P t ρ)
include d

theorem exists_mul_prodFst {n : G} (hn : n ∈ N) :
    ∃ l ∈ prodFst ρ, ∃ m ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom, n = l * m := by
  have h1 := Common.prodFst_sup_map_conj d.t_mem d.t_sq d.swap d.surj
  have hΛ : prodFst ρ ≤ normalizer (((prodFst ρ).map (MulAut.conj t).toMonoidHom : Subgroup G) :
      Set G) := (Common.prodFst_le ρ).trans (Common.le_normalizer_map_conj_prodFst d.t_mem)
  have hn' : n ∈ ((prodFst ρ ⊔ (prodFst ρ).map (MulAut.conj t).toMonoidHom : Subgroup G) :
      Set G) := by
    rw [h1]
    exact hn
  rw [coe_mul_of_left_le_normalizer_right _ _ hΛ] at hn'
  obtain ⟨l, hl, m, hm, rfl⟩ := hn'
  exact ⟨l, hl, m, hm, rfl⟩

theorem mem_prodFst_conj_decomp {m : G} (hm : m ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom) :
    ∃ a ∈ P.map (MulAut.conj t).toMonoidHom, ∃ b ∈ X, m = a * b := by
  have hl : t * m * t⁻¹ ∈ P ⊔ X := d.sup_X.ge ((diag_mem_map_conj_iff d.t_sq).1 hm)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P X
    (fun p hp => d.N_le_normalizer (d.P_le hp))] at hl
  obtain ⟨p, hp, u, hu, hpu⟩ := hl
  replace hpu : p * u = t * m * t⁻¹ := hpu
  refine ⟨t * p * t⁻¹, ⟨p, hp, rfl⟩, t * u * t⁻¹, d.conj_t_mem_X hu, ?_⟩
  calc m = t * (t * m * t⁻¹) * t⁻¹ := (diag_conj_conj d.t_sq m).symm
    _ = t * (p * u) * t⁻¹ := by rw [hpu]
    _ = (t * p * t⁻¹) * (t * u * t⁻¹) := by group

theorem comm_of_mem_inf_X {c m : G} (hc : c ∈ P ⊓ X)
    (hm : m ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom) : m * c = c * m := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prodFst_conj_decomp d hm
  have h1 : a * c = c * a := mem_centralizer_iff.1
    (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj (mem_inf.1 hc).1) a ha
  have h2 : b * c = c * b := d.X_comm b hb c (mem_inf.1 hc).2
  calc a * b * c = a * (b * c) := by group
    _ = a * (c * b) := by rw [h2]
    _ = (a * c) * b := by group
    _ = (c * a) * b := by rw [h1]
    _ = c * (a * b) := by group

theorem inf_X_le_cBt : P ⊓ X ≤ cBt X t ρ := fun c hc =>
  mem_inf.2 ⟨(mem_inf.1 hc).2, mem_centralizer_iff.2 fun m hm => comm_of_mem_inf_X d hc hm⟩

theorem comm_mem_cBt {l x : G} (hl : l ∈ prodFst ρ) (hx : x ∈ X) :
    l * x * l⁻¹ * x⁻¹ ∈ cBt X t ρ := by
  have hl' : l ∈ P ⊔ X := d.sup_X.ge hl
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P X
    (fun p hp => d.N_le_normalizer (d.P_le hp))] at hl'
  obtain ⟨p, hp, u, hu, rfl⟩ := hl'
  have hux : u * x = x * u := d.X_comm u hu x hx
  have e : p * u * x * (p * u)⁻¹ * x⁻¹ = p * x * p⁻¹ * x⁻¹ := by
    calc p * u * x * (p * u)⁻¹ * x⁻¹ = p * (u * x) * u⁻¹ * p⁻¹ * x⁻¹ := by group
      _ = p * (x * u) * u⁻¹ * p⁻¹ * x⁻¹ := by rw [hux]
      _ = p * x * p⁻¹ * x⁻¹ := by group
  rw [e]
  have hcP : p * x * p⁻¹ * x⁻¹ ∈ P := by
    have h1 : x * p * x⁻¹ ∈ P := d.conj_mem_P (d.X_le hx) hp
    have e2 : p * x * p⁻¹ * x⁻¹ = p * (x * p * x⁻¹)⁻¹ := by group
    rw [e2]
    exact mul_mem hp (inv_mem h1)
  have hcX : p * x * p⁻¹ * x⁻¹ ∈ X := mul_mem (d.conj_mem_X (d.P_le hp) hx) (inv_mem hx)
  exact inf_X_le_cBt d (mem_inf.2 ⟨hcP, hcX⟩)

theorem conj_cBt_mem_cB {z : G} (hz : z ∈ cBt X t ρ) : t * z * t⁻¹ ∈ cB X ρ := by
  refine mem_inf.2 ⟨d.conj_t_mem_X (mem_inf.1 hz).1, ?_⟩
  have h1 := uq_conj_mem_centralizer_map (t := t) (mem_inf.1 hz).2
  rwa [uq_map_conj_map_conj d.t_sq] at h1

theorem comm_mem_cB {m x : G} (hm : m ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom)
    (hx : x ∈ X) : m * x * m⁻¹ * x⁻¹ ∈ cB X ρ := by
  have hl : t * m * t⁻¹ ∈ prodFst ρ := (diag_mem_map_conj_iff d.t_sq).1 hm
  have h2 := conj_cBt_mem_cB d (comm_mem_cBt d hl (d.conj_t_mem_X hx))
  have e : t * ((t * m * t⁻¹) * (t * x * t⁻¹) * (t * m * t⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹) * t⁻¹ =
      (t * (t * m * t⁻¹) * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) * (t * (t * m * t⁻¹) * t⁻¹)⁻¹ *
        (t * (t * x * t⁻¹) * t⁻¹)⁻¹ := by group
  rw [e] at h2
  simpa only [diag_conj_conj d.t_sq] using h2

theorem comm_of_mem_cB_inf_cBt {z n : G} (hz : z ∈ cB X ρ) (hz' : z ∈ cBt X t ρ) (hn : n ∈ N) :
    n * z = z * n := by
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_prodFst d hn
  have h1 : l * z = z * l := mem_centralizer_iff.1 (mem_inf.1 hz).2 l hl
  have h2 : m * z = z * m := mem_centralizer_iff.1 (mem_inf.1 hz').2 m hm
  calc l * m * z = l * (m * z) := by group
    _ = l * (z * m) := by rw [h2]
    _ = (l * z) * m := by group
    _ = (z * l) * m := by rw [h1]
    _ = z * (l * m) := by group

end Decomposition

structure AxisCtx {K : Type} [Field K] (X N P Ai : Subgroup G) (t : G)
    (ρ : N →* SL(2, K) × SL(2, K)) (β : SL(2, K) ≃* SL(2, K)) (s : SL(2, K) → G)
    (psi : G → Fin 2 → K) : Prop where
  Ai_le : Ai ≤ X
  mem_Ai : ∀ x ∈ X, t * x = x * t → x ∈ Ai
  s_mem : ∀ M, s M ∈ N
  s_comm : ∀ M, t * s M = s M * t
  s_rho : ∀ (M : SL(2, K)) (hM : s M ∈ N), ρ ⟨s M, hM⟩ = (β M, β M)
  psi_mul : ∀ a ∈ Ai, ∀ b ∈ Ai, psi (a * b) = psi a + psi b
  psi_surj : ∀ v : Fin 2 → K, ∃ a ∈ Ai, psi a = v
  psi_conj : ∀ (M : SL(2, K)) (a : G), a ∈ Ai → s M * a * (s M)⁻¹ ∈ Ai ∧
    psi (s M * a * (s M)⁻¹) = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ psi a
  diag : ∀ a ∈ Ai, ∃ x ∈ P, x * (t * x * t⁻¹) = a

section Theta

variable {K : Type} [Field K] {N X P Ai : Subgroup G} {t : G} {ρ : N →* SL(2, K) × SL(2, K)}
  {β : SL(2, K) ≃* SL(2, K)} {s : SL(2, K) → G} {psi : G → Fin 2 → K}

namespace AxisCtx

variable (a : AxisCtx X N P Ai t ρ β s psi)
include a

theorem psi_one : psi 1 = 0 := by
  have h := a.psi_mul 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at h
  have h' : psi 1 + psi 1 = psi 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

end AxisCtx

section Delta

variable (d : ProductDiagData N X P t ρ)
include d

theorem delta_mem_X {x : G} (hx : x ∈ X) : x * (t * x * t⁻¹) ∈ X :=
  mul_mem hx (d.conj_t_mem_X hx)

theorem delta_comm_X {x : G} (hx : x ∈ X) :
    t * (x * (t * x * t⁻¹)) = (x * (t * x * t⁻¹)) * t := by
  have hq : t * x * t⁻¹ ∈ X := d.conj_t_mem_X hx
  have h1 : t * (x * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹) := by
    calc t * (x * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
      _ = (t * x * t⁻¹) * x := by rw [diag_conj_conj d.t_sq]
      _ = x * (t * x * t⁻¹) := d.X_comm _ hq _ hx
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem delta_mul_X {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    (x * y) * (t * (x * y) * t⁻¹) = (x * (t * x * t⁻¹)) * (y * (t * y * t⁻¹)) := by
  have hq : t * x * t⁻¹ ∈ X := d.conj_t_mem_X hx
  have hc : y * (t * x * t⁻¹) = (t * x * t⁻¹) * y := d.X_comm _ hy _ hq
  calc (x * y) * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
    _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [hc]
    _ = (x * (t * x * t⁻¹)) * (y * (t * y * t⁻¹)) := by group

variable (a : AxisCtx X N P Ai t ρ β s psi)
include a

theorem delta_mem_Ai {x : G} (hx : x ∈ X) : x * (t * x * t⁻¹) ∈ Ai :=
  a.mem_Ai _ (delta_mem_X d hx) (delta_comm_X d hx)

theorem mem_Ai_of_delta_eq_one {x : G} (hx : x ∈ X) (h : x * (t * x * t⁻¹) = 1) : x ∈ Ai := by
  have hq : t * x * t⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right h
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (d.X_sq x hx)
  refine a.mem_Ai x hx ?_
  have : t * x * t⁻¹ = x := by rw [hq, hxinv]
  exact mul_inv_eq_iff_eq_mul.1 this

theorem Theta_mul {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    psi ((x * y) * (t * (x * y) * t⁻¹)) =
      psi (x * (t * x * t⁻¹)) + psi (y * (t * y * t⁻¹)) := by
  rw [delta_mul_X d hx hy]
  exact a.psi_mul _ (delta_mem_Ai d a hx) _ (delta_mem_Ai d a hy)

theorem Theta_inv {x : G} (hx : x ∈ X) :
    psi (x⁻¹ * (t * x⁻¹ * t⁻¹)) = -psi (x * (t * x * t⁻¹)) := by
  have h := Theta_mul d a hx (inv_mem hx)
  rw [mul_inv_cancel] at h
  have h1 : (1 : G) * (t * 1 * t⁻¹) = 1 := by group
  rw [h1, a.psi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem Theta_one : psi (1 * (t * 1 * t⁻¹)) = 0 := by
  have h1 : (1 : G) * (t * 1 * t⁻¹) = 1 := by group
  rw [h1, a.psi_one]

theorem Theta_conj_s (M : SL(2, K)) {x : G} (hx : x ∈ X) :
    psi ((s M * x * (s M)⁻¹) * (t * (s M * x * (s M)⁻¹) * t⁻¹)) =
      (M : Matrix (Fin 2) (Fin 2) K) *ᵥ psi (x * (t * x * t⁻¹)) := by
  have hg : t * s M * t⁻¹ = s M := mul_inv_eq_iff_eq_mul.2 (a.s_comm M)
  have e : (s M * x * (s M)⁻¹) * (t * (s M * x * (s M)⁻¹) * t⁻¹) =
      s M * (x * (t * x * t⁻¹)) * (s M)⁻¹ := by
    calc (s M * x * (s M)⁻¹) * (t * (s M * x * (s M)⁻¹) * t⁻¹)
        = (s M * x * (s M)⁻¹) * ((t * s M * t⁻¹) * (t * x * t⁻¹) * (t * s M * t⁻¹)⁻¹) := by
          group
      _ = (s M * x * (s M)⁻¹) * (s M * (t * x * t⁻¹) * (s M)⁻¹) := by rw [hg]
      _ = s M * (x * (t * x * t⁻¹)) * (s M)⁻¹ := by group
  rw [e]
  exact (a.psi_conj M _ (delta_mem_Ai d a hx)).2

theorem Theta_eq_zero_of_central {z : G} (hz : z ∈ X) (hc : ∀ n ∈ N, n * z = z * n) :
    psi (z * (t * z * t⁻¹)) = 0 := by
  refine uq_vec_eq_zero fun M => ?_
  have hgN : s M ∈ N := a.s_mem M
  have h1 : s M * z = z * s M := hc _ hgN
  have hz' : s M * z * (s M)⁻¹ = z := mul_inv_eq_iff_eq_mul.2 h1
  have hgt : s M * t * (s M)⁻¹ = t := mul_inv_eq_iff_eq_mul.2 (a.s_comm M).symm
  have e : s M * (z * (t * z * t⁻¹)) * (s M)⁻¹ = z * (t * z * t⁻¹) := by
    calc s M * (z * (t * z * t⁻¹)) * (s M)⁻¹
        = (s M * z * (s M)⁻¹) * ((s M * t * (s M)⁻¹) * (s M * z * (s M)⁻¹) *
            (s M * t * (s M)⁻¹)⁻¹) := by group
      _ = z * (t * z * t⁻¹) := by rw [hz', hgt]
  have h2 := (a.psi_conj M _ (delta_mem_Ai d a hz)).2
  rw [e] at h2
  exact h2.symm

theorem exists_inf_X_delta {u : G} (hu : u ∈ Ai) : ∃ x ∈ P ⊓ X, x * (t * x * t⁻¹) = u := by
  obtain ⟨x, hxP, hxu⟩ := a.diag u hu
  refine ⟨x, mem_inf.2 ⟨hxP, ?_⟩, hxu⟩
  have hxN := d.P_le hxP
  obtain ⟨_, h2⟩ := (Common.mem_prodFst_iff ρ).1 (d.le_prodFst hxP)
  have htx : t * x * t⁻¹ ∈ N := d.conj_t_mem_N hxN
  have h1 : ρ ⟨t * x * t⁻¹, htx⟩ = (ρ ⟨x, hxN⟩).swap := d.swap _ _ rfl
  have hker : (⟨x, hxN⟩ * ⟨t * x * t⁻¹, htx⟩ : N) ∈ ρ.ker := by
    rw [d.ker, mem_subgroupOf]
    show x * (t * x * t⁻¹) ∈ X
    rw [hxu]
    exact a.Ai_le hu
  have h3 : ρ (⟨x, hxN⟩ * ⟨t * x * t⁻¹, htx⟩) = 1 := hker
  rw [map_mul, h1] at h3
  have h4 : (ρ ⟨x, hxN⟩).1 = 1 := by
    have := congrArg Prod.fst h3
    simpa [h2] using this
  have h5 : ρ ⟨x, hxN⟩ = 1 := Prod.ext h4 h2
  have h6 : (⟨x, hxN⟩ : N) ∈ ρ.ker := h5
  rw [d.ker, mem_subgroupOf] at h6
  exact h6

theorem exists_decomp_X {x : G} (hx : x ∈ X) :
    ∃ b ∈ cB X ρ, ∃ b' ∈ cBt X t ρ, x = b * b' := by
  obtain ⟨b₁, hb₁, hδ₁⟩ := exists_inf_X_delta d a (delta_mem_Ai d a hx)
  have hb₁X := (mem_inf.1 hb₁).2
  have ha₂X : x * b₁ ∈ X := mul_mem hx hb₁X
  have hδ₂ : (x * b₁) * (t * (x * b₁) * t⁻¹) = 1 := by
    rw [delta_mul_X d hx hb₁X, hδ₁]
    exact d.X_sq _ (delta_mem_X d hx)
  have ha₂ : x * b₁ ∈ Ai := mem_Ai_of_delta_eq_one d a ha₂X hδ₂
  obtain ⟨x₀, hx₀, hδ₀⟩ := exists_inf_X_delta d a ha₂
  have hx₀X := (mem_inf.1 hx₀).2
  refine ⟨t * x₀ * t⁻¹, conj_cBt_mem_cB d (inf_X_le_cBt d hx₀), x₀ * b₁,
    mul_mem (inf_X_le_cBt d hx₀) (inf_X_le_cBt d hb₁), ?_⟩
  have hc : x₀ * (t * x₀ * t⁻¹) = (t * x₀ * t⁻¹) * x₀ := d.X_comm _ hx₀X _ (d.conj_t_mem_X hx₀X)
  calc x = (x * b₁) * b₁ := by rw [mul_assoc, d.X_sq b₁ hb₁X, mul_one]
    _ = (x₀ * (t * x₀ * t⁻¹)) * b₁ := by rw [hδ₀]
    _ = ((t * x₀ * t⁻¹) * x₀) * b₁ := by rw [hc]
    _ = (t * x₀ * t⁻¹) * (x₀ * b₁) := by group

end Delta

def uqH1 {K : Type} [Field K] {N X P Ai : Subgroup G} {t : G} {ρ : N →* SL(2, K) × SL(2, K)}
    {β : SL(2, K) ≃* SL(2, K)} {s : SL(2, K) → G} {psi : G → Fin 2 → K}
    (d : ProductDiagData N X P t ρ) (a : AxisCtx X N P Ai t ρ β s psi) : Subgroup G where
  carrier := {x | ∃ b ∈ cB X ρ, ∃ b' ∈ cBt X t ρ, psi (b' * (t * b' * t⁻¹)) 1 = 0 ∧ x = b * b'}
  mul_mem' := by
    rintro _ _ ⟨b₁, hb₁, b₁', hb₁', h₁, rfl⟩ ⟨b₂, hb₂, b₂', hb₂', h₂, rfl⟩
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, b₁' * b₂', mul_mem hb₁' hb₂', ?_, ?_⟩
    · rw [Theta_mul d a (mem_inf.1 hb₁').1 (mem_inf.1 hb₂').1, Pi.add_apply, h₁, h₂, add_zero]
    · have hc := d.X_comm b₁' (mem_inf.1 hb₁').1 b₂ (mem_inf.1 hb₂).1
      calc b₁ * b₁' * (b₂ * b₂') = b₁ * (b₁' * b₂) * b₂' := by group
        _ = b₁ * (b₂ * b₁') * b₂' := by rw [hc]
        _ = (b₁ * b₂) * (b₁' * b₂') := by group
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [Theta_one d a]; rfl, (mul_one 1).symm⟩
  inv_mem' := by
    rintro _ ⟨b, hb, b', hb', h, rfl⟩
    refine ⟨b⁻¹, inv_mem hb, b'⁻¹, inv_mem hb', ?_, ?_⟩
    · rw [Theta_inv d a (mem_inf.1 hb').1, Pi.neg_apply, h, neg_zero]
    · rw [mul_inv_rev, d.X_comm b'⁻¹ (inv_mem (mem_inf.1 hb').1) b⁻¹ (inv_mem (mem_inf.1 hb).1)]

section Key

variable (d : ProductDiagData N X P t ρ) (a : AxisCtx X N P Ai t ρ β s psi)
include d a

theorem exists_mem_X_not_mem_uqH1 : ∃ x ∈ X, x ∉ uqH1 d a := by
  obtain ⟨u, hu, hpu⟩ := a.psi_surj (Pi.single 1 1)
  obtain ⟨x₀, hx₀, hδ₀⟩ := exists_inf_X_delta d a hu
  refine ⟨x₀, (mem_inf.1 hx₀).2, ?_⟩
  rintro ⟨b, hb, b', hb', h1, hx⟩
  have hb'X := (mem_inf.1 hb').1
  have hbX := (mem_inf.1 hb).1
  have hbBt : b ∈ cBt X t ρ := by
    have e : b = x₀ * b'⁻¹ := by rw [hx]; group
    rw [e]
    exact mul_mem (inf_X_le_cBt d hx₀) (inv_mem hb')
  have hΘb : psi (b * (t * b * t⁻¹)) = 0 :=
    Theta_eq_zero_of_central d a hbX fun n hn => comm_of_mem_cB_inf_cBt d hb hbBt hn
  have h2 := Theta_mul d a hbX hb'X
  rw [← hx, hδ₀, hpu, hΘb, zero_add] at h2
  have h3 := congrFun h2 1
  rw [h1] at h3
  simp at h3

theorem key {y : G} (hyN : y ∈ N) {c : K} (hc : c ≠ 0)
    (hy : (ρ ⟨y, hyN⟩).1 = β (upperSL c)) {x : G} (hx : x ∈ X) (hyx : y * x = x * y) :
    x ∈ uqH1 d a := by
  obtain ⟨b, hb, b', hb', rfl⟩ := exists_decomp_X d a hx
  have hbX := (mem_inf.1 hb).1
  have hb'X := (mem_inf.1 hb').1
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_prodFst d hyN
  have hlb : ∀ z ∈ cB X ρ, l * z = z * l := fun z hz => mem_centralizer_iff.1 (mem_inf.1 hz).2 l hl
  have hmb' : ∀ z ∈ cBt X t ρ, m * z = z * m := fun z hz =>
    mem_centralizer_iff.1 (mem_inf.1 hz).2 m hm
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = m * b * m⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hc₀B : c₀ ∈ cB X ρ := by
    rw [hc₀]
    exact comm_mem_cB d hm hbX
  have hyb : l * m * b * (l * m)⁻¹ = c₀ * b := by
    have e1 : m * b * m⁻¹ = c₀ * b := by rw [hc₀]; group
    have h1 := hlb c₀ hc₀B
    have h2 := hlb b hb
    calc l * m * b * (l * m)⁻¹ = l * (m * b * m⁻¹) * l⁻¹ := by group
      _ = l * (c₀ * b) * l⁻¹ := by rw [e1]
      _ = (l * c₀) * b * l⁻¹ := by group
      _ = (c₀ * l) * b * l⁻¹ := by rw [h1]
      _ = c₀ * (l * b) * l⁻¹ := by group
      _ = c₀ * (b * l) * l⁻¹ := by rw [h2]
      _ = c₀ * b := by group
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = l * b' * l⁻¹ * b'⁻¹ := ⟨_, rfl⟩
  have hd₀Bt : d₀ ∈ cBt X t ρ := by
    rw [hd₀]
    exact comm_mem_cBt d hl hb'X
  have hyb' : l * m * b' * (l * m)⁻¹ = d₀ * b' := by
    have h3 : m * b' * m⁻¹ = b' := mul_inv_eq_iff_eq_mul.2 (hmb' b' hb')
    calc l * m * b' * (l * m)⁻¹ = l * (m * b' * m⁻¹) * l⁻¹ := by group
      _ = l * b' * l⁻¹ := by rw [h3]
      _ = d₀ * b' := by rw [hd₀]; group
  have hconj : (l * m) * (b * b') * (l * m)⁻¹ = b * b' := mul_inv_eq_iff_eq_mul.2 hyx
  have hbd : b * d₀ = d₀ * b := d.X_comm b hbX d₀ (mem_inf.1 hd₀Bt).1
  have hsplit : (l * m) * (b * b') * (l * m)⁻¹ = (c₀ * d₀) * (b * b') := by
    calc (l * m) * (b * b') * (l * m)⁻¹
        = (l * m * b * (l * m)⁻¹) * (l * m * b' * (l * m)⁻¹) := by group
      _ = (c₀ * b) * (d₀ * b') := by rw [hyb, hyb']
      _ = c₀ * (b * d₀) * b' := by group
      _ = c₀ * (d₀ * b) * b' := by rw [hbd]
      _ = (c₀ * d₀) * (b * b') := by group
  have hcd : c₀ * d₀ = 1 := mul_right_cancel ((hsplit.symm.trans hconj).trans (one_mul _).symm)
  have hd₀B : d₀ ∈ cB X ρ := by
    have e : d₀ = c₀⁻¹ := eq_inv_of_mul_eq_one_right hcd
    rw [e]
    exact inv_mem hc₀B
  have hsN : s (upperSL c) ∈ N := a.s_mem _
  have hsρ := a.s_rho (upperSL c) hsN
  have hmem : (s (upperSL c))⁻¹ * (l * m) ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    refine (Common.mem_map_conj_prodFst_iff d.t_mem d.t_sq d.swap).2
      ⟨mul_mem (inv_mem hsN) hyN, ?_⟩
    have e : (⟨(s (upperSL c))⁻¹ * (l * m), mul_mem (inv_mem hsN) hyN⟩ : N) =
        (⟨s (upperSL c), hsN⟩ : N)⁻¹ * ⟨l * m, hyN⟩ := rfl
    rw [e, map_mul, map_inv, hsρ, Prod.fst_mul, Prod.fst_inv, hy]
    simp
  have hcomm := mem_centralizer_iff.1 (mem_inf.1 hb').2 _ hmem
  have hyb'' : l * m * b' * (l * m)⁻¹ = s (upperSL c) * b' * (s (upperSL c))⁻¹ := by
    calc l * m * b' * (l * m)⁻¹
        = s (upperSL c) * ((s (upperSL c))⁻¹ * (l * m) * b') * (l * m)⁻¹ := by group
      _ = s (upperSL c) * (b' * ((s (upperSL c))⁻¹ * (l * m))) * (l * m)⁻¹ := by rw [hcomm]
      _ = s (upperSL c) * b' * (s (upperSL c))⁻¹ := by group
  have hd₀eq : d₀ = (s (upperSL c) * b' * (s (upperSL c))⁻¹) * b'⁻¹ := by
    have h4 := hyb'.symm.trans hyb''
    calc d₀ = d₀ * b' * b'⁻¹ := by group
      _ = _ := by rw [h4]
  have hsb'X : s (upperSL c) * b' * (s (upperSL c))⁻¹ ∈ X := d.conj_mem_X hsN hb'X
  have hΘ := Theta_mul d a hsb'X (inv_mem hb'X)
  rw [← hd₀eq, Theta_eq_zero_of_central d a (mem_inf.1 hd₀B).1
    (fun n hn => comm_of_mem_cB_inf_cBt d hd₀B hd₀Bt hn), Theta_conj_s d a (upperSL c) hb'X,
    Theta_inv d a hb'X] at hΘ
  have h1 := congrFun hΘ 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, coe_upperSL] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hc
  · exact ⟨b, hb, b', hb', h1, rfl⟩

theorem uqH1_le : uqH1 d a ≤ X := by
  rintro _ ⟨b, hb, b', hb', -, rfl⟩
  exact mul_mem (mem_inf.1 hb).1 (mem_inf.1 hb').1

end Key

theorem uq_comm_of_sq {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y * (x * y) = 1) :
    x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [← h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

theorem uq_exists_mul_of_card [Finite G] {X X' E F S : Subgroup G} (hSXX' : X ⊔ X' = S)
    (hX'X : X' ≤ normalizer (X : Set G)) (hSX' : S ≤ normalizer (X' : Set G))
    (hFXX' : X ⊓ X' = F) (hEF : E ⊓ X' = F) (hES : E ≤ S)
    (hcard : Nat.card X' = Nat.card X) (hEcard : Nat.card E = Nat.card X) {x : G} (hx : x ∈ X) :
    ∃ e ∈ E, ∃ y ∈ X', x = e * y := by
  have hEN : E ≤ normalizer (X' : Set G) := hES.trans hSX'
  have h1 := FullCenter.card_sup_mul_card_inf X X' hX'X
  have h2 := FullCenter.card_sup_mul_card_inf X' E hEN
  rw [hSXX', hFXX'] at h1
  rw [inf_comm, hEF] at h2
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have h3 : Nat.card (X' ⊔ E : Subgroup G) = Nat.card S := by
    refine Nat.eq_of_mul_eq_mul_right hFpos ?_
    rw [h1, h2, hEcard, hcard]
  have h4 : X' ⊔ E = S :=
    Subgroup.eq_of_le_of_card_ge (sup_le (le_sup_right.trans hSXX'.le) hES) h3.ge
  have h5 : E ⊔ X' = S := by rw [sup_comm]; exact h4
  have hxS : x ∈ (E ⊔ X' : Subgroup G) := by
    rw [h5, ← hSXX']
    exact mem_sup_left hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right E X' hEN] at hxS
  obtain ⟨e, he, y, hy, rfl⟩ := hxS
  exact ⟨e, he, y, hy, rfl⟩

section Claim

variable (d : ProductDiagData N X P t ρ) (a : AxisCtx X N P Ai t ρ β s psi)
include d a

theorem claim1 [Finite G] {X' E F S : Subgroup G} (hSXX' : X ⊔ X' = S) (hSN : S ≤ N)
    (hX'X : X' ≤ normalizer (X : Set G)) (hSX' : S ≤ normalizer (X' : Set G))
    (hX'sq : ∀ y ∈ X', y * y = 1) (hFXX' : X ⊓ X' = F) (hFS : ∀ f ∈ F, ∀ n ∈ S, n * f = f * n)
    (hρS : (S.subgroupOf N).map ρ = ((upperSL2 K).map β.toMonoidHom).prod
      ((upperSL2 K).map β.toMonoidHom))
    (hcard : Nat.card X' = Nat.card X) (hES : E ≤ S) (hEsq : ∀ e ∈ E, e * e = 1)
    (hEcard : Nat.card E = Nat.card X) (hEF : E ⊓ X' = F) :
    E ≤ (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
  have hS1 : ∀ (n : G) (hn : n ∈ N), n ∈ S → ∃ c : K, (ρ ⟨n, hn⟩).1 = β (upperSL c) := by
    intro n hn hnS
    have h1 : ρ ⟨n, hn⟩ ∈ (S.subgroupOf N).map ρ := ⟨⟨n, hn⟩, mem_subgroupOf.2 hnS, rfl⟩
    rw [hρS, mem_prod] at h1
    obtain ⟨u, hu, hu'⟩ := h1.1
    obtain ⟨c, rfl⟩ := mem_upperSL2_iff.1 hu
    exact ⟨c, hu'.symm⟩
  have hy₀ : ∃ y₀ ∈ S, ∃ hy₀N : y₀ ∈ N, (ρ ⟨y₀, hy₀N⟩).1 = β (upperSL 1) := by
    have hmem : (β (upperSL (1 : K)), β (upperSL (1 : K))) ∈ (S.subgroupOf N).map ρ := by
      rw [hρS, mem_prod]
      exact ⟨⟨upperSL 1, upperSL_mem_upperSL2 1, rfl⟩, ⟨upperSL 1, upperSL_mem_upperSL2 1, rfl⟩⟩
    obtain ⟨n, hn, hnρ⟩ := hmem
    exact ⟨n, mem_subgroupOf.1 hn, n.2, congrArg Prod.fst hnρ⟩
  subst hSXX' hFXX'
  have hFH : X ⊓ X' ≤ uqH1 d a := by
    intro f hf
    obtain ⟨y₀, hy₀S, hy₀N, hρ₀⟩ := hy₀
    exact key d a hy₀N one_ne_zero hρ₀ (mem_inf.1 hf).1 (hFS f hf y₀ hy₀S)
  have hunion : ∀ e ∈ E, e ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom ∨
      e ∈ uqH1 d a ⊔ X' := by
    intro e he
    by_cases hΛt : e ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom
    · exact Or.inl hΛt
    · right
      have heS : e ∈ X ⊔ X' := hES he
      have heN : e ∈ N := hSN heS
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left X X' hX'X] at heS
      obtain ⟨x₀, hx₀, y₀, hy₀', rfl⟩ := heS
      have hxy : x₀ * y₀ = y₀ * x₀ := uq_comm_of_sq (d.X_sq x₀ hx₀) (hX'sq y₀ hy₀') (hEsq _ he)
      have hcomm : x₀ * y₀ * x₀ = x₀ * (x₀ * y₀) := by
        calc x₀ * y₀ * x₀ = x₀ * (y₀ * x₀) := by group
          _ = x₀ * (x₀ * y₀) := by rw [hxy]
      have hne : (ρ ⟨x₀ * y₀, heN⟩).1 ≠ 1 := fun h1 =>
        hΛt ((Common.mem_map_conj_prodFst_iff d.t_mem d.t_sq d.swap).2 ⟨heN, h1⟩)
      obtain ⟨c, hc⟩ := hS1 _ heN (hES he)
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [upperSL_zero, map_one] at hc
        exact hne hc
      have hx₀H := key d a heN hc0 hc hx₀ hcomm
      exact mul_mem_sup hx₀H hy₀'
  rcases subgroup_le_of_subset_union hunion with hle | hle
  · exact hle
  · exfalso
    obtain ⟨x, hxX, hxH⟩ := exists_mem_X_not_mem_uqH1 d a
    apply hxH
    obtain ⟨e, he, y, hy, rfl⟩ := uq_exists_mul_of_card rfl hX'X hSX' rfl hEF hES hcard hEcard hxX
    have heH : e ∈ uqH1 d a ⊔ X' := hle he
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (uqH1 d a) X'
      ((uqH1_le d a).trans (le_sup_left.trans hSX'))] at heH
    obtain ⟨h, hh, y'', hy'', hey⟩ := heH
    replace hey : h * y'' = e := hey
    have hhX : h ∈ X := uqH1_le d a hh
    have h1 : h⁻¹ * (e * y) = y'' * y := by rw [← hey]; group
    have h2 : h⁻¹ * (e * y) ∈ X ⊓ X' :=
      mem_inf.2 ⟨mul_mem (inv_mem hhX) hxX, by rw [h1]; exact mul_mem hy'' hy⟩
    have h3 : e * y = h * (h⁻¹ * (e * y)) := by group
    rw [h3]
    exact mul_mem hh (hFH h2)

theorem le_of_elementary [Finite G] {X' E F S : Subgroup G} (hSXX' : X ⊔ X' = S) (hSN : S ≤ N)
    (hX'X : X' ≤ normalizer (X : Set G)) (hSX' : S ≤ normalizer (X' : Set G))
    (hX'sq : ∀ y ∈ X', y * y = 1) (hFXX' : X ⊓ X' = F) (hFS : ∀ f ∈ F, ∀ n ∈ S, n * f = f * n)
    (hρS : (S.subgroupOf N).map ρ = ((upperSL2 K).map β.toMonoidHom).prod
      ((upperSL2 K).map β.toMonoidHom))
    (hcard : Nat.card X' = Nat.card X) (htX' : t ∈ normalizer (X' : Set G)) (hES : E ≤ S)
    (hEsq : ∀ e ∈ E, e * e = 1) (hEcard : Nat.card E = Nat.card X) (hEF : E ⊓ X' = F) :
    E ≤ X := by
  have h1 := claim1 d a hSXX' hSN hX'X hSX' hX'sq hFXX' hFS hρS hcard hES hEsq hEcard hEF
  subst hSXX' hFXX'
  have hcinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hXc : X.map (MulAut.conj t).toMonoidHom = X :=
    Common.map_conj_eq_of_mem_normalizer d.t_mem_X
  have hX'c : X'.map (MulAut.conj t).toMonoidHom = X' :=
    Common.map_conj_eq_of_mem_normalizer htX'
  have hSc : (X ⊔ X').map (MulAut.conj t).toMonoidHom = X ⊔ X' := by
    rw [Subgroup.map_sup, hXc, hX'c]
  have hFc : (X ⊓ X').map (MulAut.conj t).toMonoidHom = X ⊓ X' := by
    rw [Subgroup.map_inf_eq _ _ _ hcinj, hXc, hX'c]
  have hEt := claim1 d a (E := E.map (MulAut.conj t).toMonoidHom) rfl hSN hX'X hSX' hX'sq rfl hFS
    hρS hcard ((Subgroup.map_mono hES).trans hSc.le)
    (by
      rintro _ ⟨e₀, he₀, rfl⟩
      show t * e₀ * t⁻¹ * (t * e₀ * t⁻¹) = 1
      calc t * e₀ * t⁻¹ * (t * e₀ * t⁻¹) = t * (e₀ * e₀) * t⁻¹ := by group
        _ = 1 := by rw [hEsq e₀ he₀]; group)
    ((Subgroup.card_map_of_injective hcinj).trans hEcard)
    (by
      conv_lhs => rw [← hX'c]
      rw [← Subgroup.map_inf_eq _ _ _ hcinj, hEF, hFc])
  intro e he
  have heN : e ∈ N := hSN (hES he)
  obtain ⟨_, hf1⟩ := (Common.mem_map_conj_prodFst_iff d.t_mem d.t_sq d.swap).1 (h1 he)
  have hte : t * e * t⁻¹ ∈ E.map (MulAut.conj t).toMonoidHom := ⟨e, he, rfl⟩
  obtain ⟨hteN, hf2⟩ := (Common.mem_map_conj_prodFst_iff d.t_mem d.t_sq d.swap).1 (hEt hte)
  have h3 : ρ ⟨t * e * t⁻¹, hteN⟩ = (ρ ⟨e, heN⟩).swap := d.swap _ _ rfl
  rw [h3] at hf2
  have h5 : ρ ⟨e, heN⟩ = 1 := Prod.ext hf1 hf2
  have h6 : (⟨e, heN⟩ : N) ∈ ρ.ker := h5
  rw [d.ker, mem_subgroupOf] at h6
  exact h6

end Claim

end Theta

end Core

section Aux

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_X_aux {X X' F S : Subgroup G} {y : G} (hyS : y ∈ normalizer (S : Set G))
    (hyX' : y ∈ normalizer (X' : Set G)) (hXS : X ≤ S) (hXsq : ∀ x ∈ X, x * x = 1)
    (hFXX' : X ⊓ X' = F) (hc : (center S).map S.subtype = F)
    (key : ∀ A : Subgroup G, A ≤ S → (∀ x ∈ A, x * x = 1) → Nat.card A = Nat.card X →
      A ⊓ X' = F → A = X) : y ∈ normalizer (X : Set G) := by
  have hF : ∀ z, z ∈ F ↔ z ∈ S ∧ ∀ s ∈ S, s * z = z * s := fun z => by
    rw [← hc]
    exact mem_center_map_iff
  have hyF : y ∈ normalizer (F : Set G) := by
    refine mem_normalizer_of_conj_le fun f hf => ?_
    obtain ⟨hfS, hfc⟩ := (hF f).1 hf
    refine (hF _).2 ⟨uq_conj_mem hyS hfS, fun s hs => ?_⟩
    have h1 := hfc _ (uq_conj_inv_mem hyS hs)
    calc s * (y * f * y⁻¹) = y * ((y⁻¹ * s * y) * f) * y⁻¹ := by group
      _ = y * (f * (y⁻¹ * s * y)) * y⁻¹ := by rw [h1]
      _ = y * f * y⁻¹ * s := by group
  refine Common.mem_normalizer_of_map_conj_eq (key _ ?_ ?_ ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact uq_conj_mem hyS (hXS hx)
  · rintro _ ⟨x, hx, rfl⟩
    show y * x * y⁻¹ * (y * x * y⁻¹) = 1
    calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hXsq x hx]; group
  · exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  · have h1 : X'.map (MulAut.conj y).toMonoidHom = X' := Common.map_conj_eq_of_mem_normalizer hyX'
    have h2 : F.map (MulAut.conj y).toMonoidHom = F := Common.map_conj_eq_of_mem_normalizer hyF
    calc X.map (MulAut.conj y).toMonoidHom ⊓ X'
        = X.map (MulAut.conj y).toMonoidHom ⊓ X'.map (MulAut.conj y).toMonoidHom := by rw [h1]
      _ = (X ⊓ X').map (MulAut.conj y).toMonoidHom :=
          (Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective).symm
      _ = F := by rw [hFXX', h2]

end Aux

end UniqueAux

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem UniqueAux.rho_S_eq_prod (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K))
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i]) (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M)) :
    (𝐒.subgroupOf 𝐍𝐂[i]).map ρ = ((upperSL2 K).map β.toMonoidHom).prod
      ((upperSL2 K).map β.toMonoidHom) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hf := closureSetupFacts h hbt i
  have hPS := (BothTrivialSlice.S_inf_C h hbt).symm.le.trans inf_le_left
  have hScard := (card_barSub hf.X_le_S hf.S_le).symm
  rw [hf.card_S] at hScard
  have hK : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact h.setup.card_K
  refine Common.map_subgroupOf_eq_prod (m := n) (by have := h.setup.two_le; omega) hK ρ hker
    hf.S_le_NC hf.X_le_S (IsPGroup.of_card (n := 8 * n) (by rw [hScard, hf.card_X]; ring))
    hScard (B := (upperSL2 K).map β.toMonoidHom)
    (by rw [card_map_of_injective β.injective, card_upperSL2, h.setup.card_K]) ?_
  intro b hb
  obtain ⟨u, hu, rfl⟩ := hb
  have hsN := sup_le_NC (t := t) i (mem_sup_left (s_mem_CU h i u))
  exact ⟨⟨_, hsN⟩, hPS (symm_mem_pull.mpr (sHom_upper_le_antiUnipotent i ⟨u, hu, rfl⟩)),
    hβ u hsN⟩

theorem eq_X_of_elementary (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M))
    {P : Subgroup G} (hPΛ : P ≤ prodFst ρ) (hP : ⁅P, P⁆ = P) (hPX : P ⊔ 𝐗[i] = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P)
    {A : Subgroup G} (hAS : A ≤ 𝐒) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = Nat.card 𝐗[i]) (hAX : A ⊓ 𝐗[i.swap] = 𝐅) : A = 𝐗[i] := by
  have hsup := sup_le_NC (φ := φ) (t := t) i
  have d := ProductDiagData.mk hρ hker (le_sup_right.trans hsup)
    (fun x hx => X_mul_self h hbt i hx)
    (fun x hx y hy => comm_of_mul_self (fun _ hz => X_mul_self h hbt i hz) hx hy)
    (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i (t_mem_normalizer_X h i) hz)
    h.setup.t_mul_t hswap hPΛ hP hPX hPt hPmax
  have hdiag := diagonal_eq_CU h hbt i ρ hρ hker hswap β hβ hPΛ hP hPX hPt hPmax
  have a := UniqueAux.AxisCtx.mk (β := β) (s := fun M => ((φ.symm (sHom K i M) : L) : G))
    (psi := psiG φ i)
    ((X_inf_C h i).ge.trans inf_le_left)
    (fun x hx hxt => (X_inf_C h i).le ⟨hx, mem_centralizer_singleton_iff.2 hxt.symm⟩)
    (fun M => hsup (mem_sup_left (s_mem_CU h i M)))
    (fun M => h.twoCore.comm (φ.symm (sHom K i M)).2)
    hβ
    (fun u hu v hv => psiG_mul h.twoCore φ i hu hv)
    (fun v => exists_psiG_eq h.twoCore φ i v)
    (fun M u hu => psiG_conj_s h.twoCore φ i M hu)
    (fun u hu => hdiag.2.1 u (((X_inf_CU h i).ge hu).2))
  have hle := UniqueAux.le_of_elementary d a (X_sup_X_swap i) (S_le_NC h hbt i)
    ((X_le_S i.swap).trans (S_le_normalizer_X h hbt i)) (S_le_normalizer_X h hbt i.swap)
    (fun y hy => X_mul_self h hbt i.swap hy) (X_inf_X_swap h i)
    (fun f hf n hn => F_comm_S h hbt hf hn) (UniqueAux.rho_S_eq_prod h hbt i ρ hker β hβ)
    (by rw [card_X h i, card_X h i.swap]) (t_mem_normalizer_X h i.swap) hAS
    (fun e he => mul_self_of_elem hA he) hcard hAX
  exact eq_of_le_of_card_ge hle hcard.ge

theorem mem_normalizer_X_of_mem_normalizer_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M))
    {P : Subgroup G} (hPΛ : P ≤ prodFst ρ) (hP : ⁅P, P⁆ = P) (hPX : P ⊔ 𝐗[i] = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P)
    {y : G} (hyS : y ∈ normalizer (𝐒 : Set G)) (hyX : y ∈ normalizer (𝐗[i.swap] : Set G)) :
    y ∈ normalizer (𝐗[i] : Set G) :=
  UniqueAux.mem_normalizer_X_aux hyS hyX (X_le_S i) (fun x hx => X_mul_self h hbt i hx) (X_inf_X_swap h i)
    (center_S h hbt) fun A hAS hAsq hcard hAX =>
      eq_X_of_elementary h hbt i ρ hρ hker hswap β hβ hPΛ hP hPX hPt hPmax hAS
        (isElementaryAbelian_of_mul_self hAsq) hcard hAX

theorem mem_normalizer_prodFst_of_odd (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    {y : G} (hyX : y ∈ normalizer (𝐗[i] : Set G)) (hy : Odd (orderOf y)) :
    y ∈ normalizer ((prodFst ρ : Subgroup G) : Set G) :=
  UniqueAux.mem_normalizer_prodFst_of_odd_aux h.four_le_card hρ (le_sup_right.trans (sup_le_NC i)) hker
    (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i (t_mem_normalizer_X h i) hz)
    h.setup.t_mul_t hswap (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i hyX hz) hyX hy

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
