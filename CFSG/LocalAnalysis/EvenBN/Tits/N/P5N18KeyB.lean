module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Strong
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open
open scoped commutatorElement

structure KFacts {X : Type*} [Group X] [Finite X] (K U : Subgroup X) (x t : X) (rk : X → ℕ) : Prop where
  htt : t * t = 1
  htnU : t ∉ U
  htU : ∀ u ∈ U, t * u = u * t
  hU0ab : IsElemAbelian 2 (U ⊔ zpowers t)
  hU0card : Nat.card ↥(U ⊔ zpowers t) = 32
  hNK : ∀ g : X, g ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) ↔ g ∈ K
  hUK : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U
  hmax : ∀ E : Subgroup X, E ≤ K → IsElemAbelian 2 E →
    Nat.card E ≤ 32 ∧ (Nat.card E = 32 → E = U ⊔ zpowers t)
  hcomm : ∀ y ∈ K, y * y = 1 → y ∉ U ⊔ zpowers t →
    Nat.card ↥⁅U, zpowers y⁆ = 4 ∧ Nat.card ↥(U ⊓ centralizer ({y} : Set X)) = 4
  hklein : ∀ B : Subgroup X, B ≤ K → IsElemAbelian 2 B → 4 ≤ (B ⊓ (U ⊔ zpowers t)).relIndex B →
    ∃ y ∈ B, y ∉ U ⊔ zpowers t ∧ ∃ k ∈ K, (k * y * k⁻¹) * x * (k * y * k⁻¹)⁻¹ = x⁻¹
  htrans : ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b
  hrk_conj : ∀ g y : X, rk (g * y * g⁻¹) = rk y
  hrk3 : ∃ u ∈ U, u ≠ 1 ∧ rk u ≤ 8
  hrk4 : ∀ y g : X, y * y = 1 → y * (g * x * g⁻¹) * y⁻¹ = (g * x * g⁻¹)⁻¹ → 16 ≤ rk y

variable {X : Type*} [Group X] [Finite X]

theorem fusion_of_weakly_closed (S : Sylow 2 X) {A : Subgroup X} (hAS : A ≤ (S : Subgroup X))
    (hweak : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup X) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a b : X} (ha : a ∈ A) (hb : b ∈ A) {g : X}
    (hg : g * a * g⁻¹ = b) : ∃ n ∈ normalizer (A : Set X), n * a * n⁻¹ = b := by
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hAS
  have hAC : A ≤ centralizer ({b} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.2 (hab y hy b hb)
  have hgAC : A.map (MulAut.conj g).toMonoidHom ≤ centralizer ({b} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hg]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hab y hy a ha]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  obtain ⟨c, hc, R, hR, hAR, hgAR⟩ := Strong.exists_conj_le_isPGroup _ hA2 (hA2.map _) hAC hgAC
  obtain ⟨k, hk⟩ := Strong.exists_map_conj_le_sylow S hR
  have e1 : A.map (MulAut.conj k).toMonoidHom = A := hweak k ((map_mono hAR).trans hk)
  have e2 : A.map (MulAut.conj (k * (c * g))).toMonoidHom = A := by
    apply hweak
    rw [← Strong.map_conj_map_conj, ← Strong.map_conj_map_conj]
    exact (map_mono hgAR).trans hk
  have e3 : A.map (MulAut.conj (c * g)).toMonoidHom = A :=
    Subgroup.map_injective (MulAut.conj k).injective (by rw [Strong.map_conj_map_conj, e2, e1])
  refine ⟨c * g, Strong.mem_normalizer_of_map_conj_eq e3, ?_⟩
  have hcb : c * b = b * c := mem_centralizer_singleton_iff.1 hc
  calc c * g * a * (c * g)⁻¹ = c * (g * a * g⁻¹) * c⁻¹ := by group
    _ = b := by rw [hg, hcb, mul_inv_cancel_right]

private theorem keyB_sup_le_sylow {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk)
    (S : Sylow 2 X) (hSK : (S : Subgroup X) ≤ K) : U ⊔ zpowers t ≤ (S : Subgroup X) := by
  have hSN : (S : Subgroup X) ≤ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) :=
    fun s hs => (h.hNK s).2 (hSK hs)
  have hsup := h.hU0ab.isPGroup.to_sup_of_normal_left' S.isPGroup' hSN
  exact le_sup_left.trans (S.is_maximal' hsup le_sup_right).le

private theorem keyB_weak {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk)
    {S : Subgroup X} (hSK : S ≤ K) (g : X)
    (hg : (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom ≤ S) :
    (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom = U ⊔ zpowers t :=
  (h.hmax _ (hg.trans hSK) (h.hU0ab.map _)).2
    ((Subgroup.card_map_of_injective (MulAut.conj g).injective).trans h.hU0card)

private theorem keyB_inf_le {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk)
    (S : Sylow 2 X) (hSK : (S : Subgroup X) ≤ K) {B : Subgroup X}
    (hBU : ∀ b ∈ B, ∃ g : X, g * b * g⁻¹ ∈ U) : B ⊓ (U ⊔ zpowers t) ≤ U := by
  rintro b ⟨hbB, hbU₀⟩
  obtain ⟨g, hg⟩ := hBU b hbB
  obtain ⟨n, hn, hnb⟩ := fusion_of_weakly_closed S (keyB_sup_le_sylow h S hSK) (keyB_weak h hSK)
    (fun a ha c hc => h.hU0ab.comm ha hc) hbU₀ ((le_sup_left : U ≤ U ⊔ zpowers t) hg) (g := g) rfl
  convert h.hUK n⁻¹ (Subgroup.inv_mem _ ((h.hNK n).1 hn)) _ hg using 1
  rw [← hnb]
  group

private theorem keyB_relIndex_lt {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk)
    {B : Subgroup X} (hBK : B ≤ K) (hB : IsElemAbelian 2 B)
    (hBU : ∀ b ∈ B, ∃ g : X, g * b * g⁻¹ ∈ U) : (B ⊓ (U ⊔ zpowers t)).relIndex B < 4 := by
  by_contra hlt
  obtain ⟨y, hyB, hyU₀, k, -, hk⟩ := h.hklein B hBK hB (not_lt.1 hlt)
  have hy2 : y * y = 1 := hB.mul_self_eq_one hyB
  have h16 : 16 ≤ rk y := by
    rw [← h.hrk_conj k y]
    refine h.hrk4 _ 1 ?_ ?_
    · calc k * y * k⁻¹ * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
        _ = 1 := by rw [hy2, mul_one, mul_inv_cancel]
    · simp only [one_mul, inv_one, mul_one]
      exact hk
  obtain ⟨g, hg⟩ := hBU y hyB
  have hy1 : g * y * g⁻¹ ≠ 1 := fun h1 => hyU₀ (by
    rw [conj_eq_one_iff.1 h1]
    exact one_mem _)
  obtain ⟨u, huU, hu1, hu8⟩ := h.hrk3
  obtain ⟨k', -, hk'⟩ := h.htrans _ hg u huU hy1 hu1
  have hu : rk u = rk y := by rw [← hk', h.hrk_conj, h.hrk_conj]
  omega

theorem keyB {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk) (S : Sylow 2 X)
    (hSK : (S : Subgroup X) ≤ K) {B : Subgroup X} (hBK : B ≤ K) (hB : IsElemAbelian 2 B)
    (hBU : ∀ b ∈ B, ∃ g : X, g * b * g⁻¹ ∈ U) (hBnU : ¬ B ≤ U) :
    Nat.card B ≤ 8 ∧ U.relIndex B ≤ 2 := by
  have hinf := keyB_inf_le h S hSK hBU
  have hlt := keyB_relIndex_lt h hBK hB hBU
  rw [inf_relIndex_left] at hlt
  obtain ⟨nB, hnB⟩ := IsPGroup.iff_card.1 hB.isPGroup
  have hdvd : (U ⊔ zpowers t).relIndex B ∣ 2 ^ nB := by
    rw [← hnB]
    exact relIndex_dvd_card _ _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hBU₀ : ¬ B ≤ U ⊔ zpowers t := fun hle => hBnU fun b hb => hinf ⟨hb, hle hb⟩
  have h2 : (U ⊔ zpowers t).relIndex B = 2 := by
    have hne : (U ⊔ zpowers t).relIndex B ≠ 1 := fun h1 => hBU₀ (relIndex_eq_one.1 h1)
    rw [hm] at hlt hne ⊢
    rcases m with _ | _ | m
    · exact absurd (pow_zero 2) hne
    · rfl
    · rw [pow_succ, pow_succ] at hlt
      have := pow_pos (show 0 < 2 by norm_num) m
      omega
  obtain ⟨y, hyB, hyU₀⟩ := SetLike.not_le_iff_exists.1 hBU₀
  have hC4 := (h.hcomm y (hBK hyB) (hB.mul_self_eq_one hyB) hyU₀).2
  have hle : (U ⊔ zpowers t) ⊓ B ≤ U ⊓ centralizer ({y} : Set X) := fun b hb =>
    ⟨hinf ⟨hb.2, hb.1⟩, mem_centralizer_singleton_iff.2 (hB.comm hb.2 hyB)⟩
  have hcard := relIndex_mul_card (H := U ⊔ zpowers t) (K := B)
  rw [h2] at hcard
  have hUB : U ⊓ B = (U ⊔ zpowers t) ⊓ B :=
    le_antisymm (inf_le_inf_right B le_sup_left) fun b hb => ⟨hinf ⟨hb.2, hb.1⟩, hb.2⟩
  refine ⟨?_, ?_⟩
  · have := Subgroup.card_le_of_le hle
    omega
  · have hU2 : U.relIndex B = 2 := by
      rw [← inf_relIndex_right, hUB, inf_relIndex_right, h2]
    exact hU2.le

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
