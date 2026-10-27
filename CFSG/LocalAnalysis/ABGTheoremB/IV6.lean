module

public import CFSG.LocalAnalysis.ABGTheoremB.Statements
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  refine isSylowOf_of_card (fun y hy => ?_) ?_
  · rw [mem_map_conj_iff] at hy
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mp (hP.le hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem subset_normalizer_mul_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {P K X : Subgroup G} (hP : IsSylowOf p P K) (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    (X : Set G) ⊆ (Subgroup.normalizer (P : Set G) : Set G) * (K : Set G) := by
  intro x hx
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj (isSylowOf_map_conj hP (inv_mem (hXK hx)))
  refine ⟨x * k, ?_, k⁻¹, inv_mem hk, by group⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  have h := hconj (k * y * k⁻¹)
  rw [mem_map_conj_iff, inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h
  rw [show x * k * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ by group]
  exact h.symm

private theorem isSylowOf_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) : IsSylowOf p (P : Subgroup G) K :=
  isSylowOf_iff.mpr ⟨hPK, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPK))⟩

private theorem dvd_card_of_isSylowOf_of_dvd [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) (hdvd : p ∣ Nat.card K) : p ∣ Nat.card P := by
  rw [hP.card_eq]
  exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd).ne'

private theorem ne_bot_of_isSylowOf_of_dvd [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) (hdvd : p ∣ Nat.card K) : P ≠ ⊥ := by
  intro hbot
  have h := dvd_card_of_isSylowOf_of_dvd hP hdvd
  rw [hbot, Subgroup.card_bot] at h
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h)

private theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) : Odd (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

private theorem mem_of_sq_mem_of_odd_orderOf {K : Subgroup G} {y : G} (hy : Odd (orderOf y))
    (h : y ^ 2 ∈ K) : y ∈ K := by
  obtain ⟨m, hm⟩ := hy
  have e : (y ^ 2) ^ (m + 1) = y := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [← e]
  exact K.pow_mem h _

private theorem oddCore_le_solvableRadical (K : Type*) [Group K] [Finite K] :
    CFSG.oddCore K ≤ CFSG.solvableRadical K :=
  le_sSup ⟨inferInstance, CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ABGTheoremB.odd_card_oddCore K)⟩

private theorem exists_mem_inv_mul_mem_centralizer_of_odd {M : Subgroup G} (hM : Odd (Nat.card M))
    {x k : G} (hx : x * x = 1) (hk : k * x * k⁻¹ * x⁻¹ ∈ M) :
    ∃ m ∈ M, m⁻¹ * k ∈ Subgroup.centralizer ({x} : Set G) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcI : k * x * k⁻¹ * x⁻¹ ∈ OddInversion.invertedSet M x := by
    rw [OddInversion.mem_invertedSet]
    refine ⟨hk, ?_⟩
    rw [show x * (k * x * k⁻¹ * x⁻¹) * x⁻¹ = x * k * x * k⁻¹ * (x⁻¹ * x⁻¹) by group,
      show (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ by group, hxinv, hx, mul_one]
  obtain ⟨d, hd, hd2⟩ := OddInversion.exists_sq_eq_of_mem_invertedSet hM hcI
  rw [OddInversion.mem_invertedSet] at hd
  refine ⟨d, hd.1, ?_⟩
  have e1 : x * d⁻¹ * x⁻¹ = d := by
    rw [show x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ by group, hd.2, inv_inv]
  have key : d * x * d⁻¹ = k * x * k⁻¹ := by
    calc d * x * d⁻¹ = d * (x * d⁻¹ * x⁻¹) * x := by group
      _ = d ^ 2 * x := by rw [e1, pow_two]
      _ = k * x * k⁻¹ := by rw [hd2]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc d⁻¹ * k * x = d⁻¹ * (k * x * k⁻¹) * k := by group
    _ = d⁻¹ * (d * x * d⁻¹) * k := by rw [key]
    _ = x * (d⁻¹ * k) := by group

private theorem conj_mul_inv_mem_oddCoreIn_of_sup_eq {H : Subgroup G} {x : G}
    (hfac : oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer ({x} : Set G)) = H) (hxH : x ∈ H)
    {h : G} (hh : h ∈ H) : h * x * h⁻¹ * x⁻¹ ∈ oddCoreIn H := by
  have hnorm : H ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (oddCoreIn H : Set G) := inf_le_left.trans (le_normalizer_oddCoreIn H)
  rw [← hfac, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hh
  obtain ⟨n, hn, o, ho, rfl⟩ := hh
  have hnx : Commute n x := Subgroup.mem_centralizer_singleton_iff.mp hn.2
  have hxo : x * o⁻¹ * x⁻¹ ∈ oddCoreIn H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H hxH) o⁻¹).mp (inv_mem ho)
  have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H hn.1)
    (o * (x * o⁻¹ * x⁻¹))).mp (mul_mem ho hxo)
  have e : n * o * x * (n * o)⁻¹ * x⁻¹ = n * (o * (x * o⁻¹ * x⁻¹)) * n⁻¹ := by
    calc n * o * x * (n * o)⁻¹ * x⁻¹ = n * o * x * o⁻¹ * (n⁻¹ * x⁻¹) := by group
      _ = n * o * x * o⁻¹ * (x⁻¹ * n⁻¹) := by rw [hnx.inv_inv.eq]
      _ = n * (o * (x * o⁻¹ * x⁻¹)) * n⁻¹ := by group
  rw [e]
  exact h1

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem normalizer_mem_familyL (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hdiv : r ∣ Nat.card σ.ON) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ∈ σ.familyL r := by
  have : Fact r.Prime := ⟨hr⟩
  exact ⟨⟨R, ne_bot_of_isSylowOf_of_dvd hR hdiv, hR.isPGroup, rfl⟩,
    subset_normalizer_mul_of_isSylowOf hR (hσ.L₀_le_N.trans σ.N_le_normalizer_ON), hRD, R, hR,
    Subgroup.le_normalizer⟩

theorem isSylowOf_oddCoreIn_normalizer_of_mem_familyL (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    {H : Subgroup G} (hH : H ∈ σ.familyL r) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRH : R ≤ oddCoreIn H)
    (hsyl : IsSylowOf r R (oddCoreIn H)) :
    IsSylowOf r R (oddCoreIn (Subgroup.normalizer (R : Set G))) := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hfac := (σ.familyL_properties hσ hII hr hdiv hH).2.1
  obtain ⟨⟨X, -, hXp, hHX⟩, -, hDH, -⟩ := hH
  have hXO : X ≤ oddCoreIn H := by
    rw [hHX]
    exact le_oddCoreIn Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup hr hr2 hXp)
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hHX]
    exact hRH.trans (oddCoreIn_le H)
  have hXR : X ≤ R :=
    le_sup_left.trans (hsyl.eq_of_le le_sup_right (sup_le hXO hRH)
      (hXp.to_sup_of_normal_left' hR.isPGroup hRX)).le
  have hCH : Subgroup.centralizer (R : Set G) ≤ H := by
    rw [hHX]
    exact (Subgroup.centralizer_le fun y hy => hXR hy).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKL := σ.normalizer_mem_familyL hσ hr hdiv hR hRD
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hRK : R ≤ oddCoreIn (Subgroup.normalizer (R : Set G)) :=
    le_oddCoreIn Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup hr hr2 hR.isPGroup)
  obtain ⟨R', hR', hRR', hR'D⟩ := exists_isSylowOf_normalized_ge_of_odd hr hD2
    (hRD.trans (le_normalizer_oddCoreIn _)) (odd_card_oddCoreIn _) hRK hR.isPGroup hRD
  have hR'N : R' ⊓ σ.N = R := by
    refine hR.eq_of_le (le_inf hRR' (hR.le.trans σ.ON_le_N)) ?_
      (hR'.isPGroup.to_le inf_le_left)
    exact (inf_le_inf_right _ hR'.le).trans (σ.oddCoreIn_inf_N_le_ON_of_cover hσ hII hKL.2.1)
  have hxD : σ.x ∈ σ.D := σ.T_le_D hσ σ.x_mem_T
  have hR'odd : Odd (Nat.card R') := odd_card_of_isPGroup hr hr2 hR'.isPGroup
  have heq : R' ⊓ σ.N = R' := by
    by_contra hne
    obtain ⟨y, hyI, hy1, hyC⟩ := exists_inverted_centralizing_fixed hR'.isPGroup hR'odd
      hσ.x_order (hR'D hxD) (lt_of_le_of_ne inf_le_left hne)
    rw [OddInversion.mem_invertedSet] at hyI
    have hyR : y ∈ Subgroup.centralizer (R : Set G) := by
      rw [← hR'N]
      exact hyC
    have hcomm := conj_mul_inv_mem_oddCoreIn_of_sup_eq hfac (hDH hxD) (hCH hyR)
    rw [show y * σ.x * y⁻¹ * σ.x⁻¹ = y * (σ.x * y * σ.x⁻¹)⁻¹ by group, hyI.2, inv_inv,
      ← pow_two] at hcomm
    have hyodd : Odd (orderOf y) := hR'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard R' hyI.1)
    have hyO : y ∈ oddCoreIn H := mem_of_sq_mem_of_odd_orderOf hyodd hcomm
    have hsup := hsyl.eq_of_le (le_sup_left : R ≤ R ⊔ Subgroup.zpowers y)
      (sup_le hRH (Subgroup.zpowers_le.mpr hyO))
      (hR'.isPGroup.to_le (sup_le hRR' (Subgroup.zpowers_le.mpr hyI.1)))
    have hyRR : y ∈ R := by
      rw [← hsup]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hyN : y * σ.x = σ.x * y := (σ.mem_N_iff y).mp (σ.ON_le_N (hR.le hyRR))
    have hyy : y⁻¹ = y := by
      rw [← hyI.2, ← hyN, mul_inv_cancel_right]
    apply hy1
    refine Subgroup.mem_bot.mp (mem_of_sq_mem_of_odd_orderOf hyodd ?_)
    rw [pow_two]
    nth_rewrite 1 [← hyy]
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  rw [heq.symm.trans hR'N] at hR'
  exact hR'

theorem not_isSylowOf_oddCoreIn_of_not_stationary (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) (hns : ¬ σ.Stationary r)
    {H : Subgroup G} (hH : H ∈ σ.familyL r) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRH : R ≤ oddCoreIn H) :
    ¬ IsSylowOf r R (oddCoreIn H) := fun hsyl =>
  hns ⟨R, hR, σ.isSylowOf_oddCoreIn_normalizer_of_mem_familyL hσ hII hr hdiv hH hR hRD hRH hsyl⟩

theorem propIV61 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h32 : σ.LemmaIV32)
    (h33 : σ.LemmaIV33) : σ.PropIV61 := by
  intro r hr hdiv hexc H hH
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  obtain ⟨-, -, -, ⟨P₂, hP₂⟩, -, R, hR, hRD, hRH⟩ := σ.familyL_properties hσ hII hr hdiv hH
  have hDH : σ.D ≤ H := hH.2.2.1
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨Rs, hRs, hRRs, hRsD⟩ := exists_isSylowOf_normalized_ge_of_odd hr hD2
    (hDH.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H) hRH hR.isPGroup hRD
  rcases hRRs.lt_or_eq with hlt | hReq
  ·
    have h := h33 r hr hdiv H hH R Rs hR hRD hRH hRs hRsD hlt
    exact ⟨h.1.trans (oddCore_le_solvableRadical H), h.2⟩
  ·
    have hRO : IsSylowOf r R (oddCoreIn H) := by
      rw [hReq]
      exact hRs
    have hcore := σ.isSylowOf_oddCoreIn_normalizer_of_mem_familyL hσ hII hr hdiv hH hR hRD hRH hRO
    obtain ⟨hNL, hNc⟩ := h32 r hr hdiv hexc R hR hRD
    obtain ⟨S₁, hS₁⟩ := exists_sylow_le_inf_of_subset_mul P₂ (hP₂.trans inf_le_left)
      (oddCoreIn_le H) (le_normalizer_oddCoreIn H) (odd_card_oddCoreIn H).not_two_dvd_nat
      (subset_normalizer_mul_of_isSylowOf hRO (le_normalizer_oddCoreIn H))
    have hS₁N : (S₁ : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := hS₁.trans inf_le_left
    have hS₁H : (S₁ : Subgroup G) ≤ H := hS₁.trans inf_le_right
    have hZS₁ : CFSG.QuasiDihedralFusion.centerOf (S₁ : Subgroup G) ≤ S₁ := inf_le_left
    have hN := (hII.qgroup_constraint_criterion _ hNL.2.2.1
      (oddCoreIn_ne_bot_of_isPLocal hr hr2 hNL.1) hNL.2.1 S₁ (isSylowOf_of_sylow_le S₁ hS₁N) r
      hr hr2 R hcore hS₁N).1.mp hNc
    refine (hII.qgroup_constraint_criterion H hDH (oddCoreIn_ne_bot_of_isPLocal hr hr2 hH.1)
      hH.2.1 S₁ (isSylowOf_of_sylow_le S₁ hS₁H) r hr hr2 R hRO hS₁N).1.mpr ?_
    exact hN.of_le (inf_le_inf_right _ (hZS₁.trans hS₁H))
      (le_inf (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right)

theorem propIV62 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.PropIV62 := by
  intro r hr hdiv H hH R₁ hR₁ hR₁p _ hR₁D hcov hX
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hfac, -, -, ⟨hON, -⟩, RN, hRN, hRND, hRNH⟩ :=
    σ.familyL_properties hσ hII hr hdiv hH
  have hDH : σ.D ≤ H := hH.2.2.1
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hxD : σ.x ∈ σ.D := σ.T_le_D hσ σ.x_mem_T
  have hDO : σ.D ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hDH.trans (le_normalizer_oddCoreIn H)
  refine ⟨⟨R₁, hR₁, hR₁p, rfl⟩, ?_, hR₁D, ?_⟩
  ·
    intro l hl
    obtain ⟨h, hh, o₁, ho₁, rfl⟩ := hH.2.1 hl
    obtain ⟨k, hk, m, hm, rfl⟩ := hcov hh
    set K := H ⊓ Subgroup.normalizer (R₁ : Set G) with hK
    have hk : k ∈ K := hk
    have hm : m ∈ oddCoreIn H := hm
    have hxK : σ.x ∈ K := Subgroup.mem_inf.mpr ⟨hDH hxD, hR₁D hxD⟩
    have hModd : Odd (Nat.card (oddCoreIn H ⊓ K : Subgroup G)) :=
      (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hx2 : σ.x * σ.x = 1 := by
      have h1 := pow_orderOf_eq_one σ.x
      rwa [hσ.x_order, pow_two] at h1
    obtain ⟨m', hm', hn⟩ := exists_mem_inv_mul_mem_centralizer_of_odd hModd hx2
      (Subgroup.mem_inf.mpr ⟨conj_mul_inv_mem_oddCoreIn_of_sup_eq hfac (hDH hxD)
        (Subgroup.mem_inf.mp hk).1,
        K.mul_mem (K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)) (K.inv_mem hxK)⟩)
    obtain ⟨hm'O, hm'K⟩ := Subgroup.mem_inf.mp hm'
    have hkmN : k * m ∈ σ.N := by
      have h1 := σ.N.mul_mem (hσ.L₀_le_N hl) (σ.N.inv_mem (σ.ON_le_N ho₁))
      rwa [mul_inv_cancel_right] at h1
    have haO : (k * m)⁻¹ * (m'⁻¹ * k) ∈ oddCoreIn H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H
        (H.inv_mem (Subgroup.mem_inf.mp hk).1)) m'⁻¹).mp ((oddCoreIn H).inv_mem hm'O)
      rw [inv_inv] at h1
      rw [show (k * m)⁻¹ * (m'⁻¹ * k) = m⁻¹ * (k⁻¹ * m'⁻¹ * k) by group]
      exact (oddCoreIn H).mul_mem ((oddCoreIn H).inv_mem hm) h1
    have ha : (k * m)⁻¹ * (m'⁻¹ * k) ∈ σ.ON :=
      hON (Subgroup.mem_inf.mpr ⟨haO, σ.N.mul_mem (σ.N.inv_mem hkmN) hn⟩)
    exact ⟨m'⁻¹ * k, (Subgroup.mem_inf.mp (K.mul_mem (K.inv_mem hm'K) hk)).2,
      ((k * m)⁻¹ * (m'⁻¹ * k))⁻¹ * o₁, σ.ON.mul_mem (σ.ON.inv_mem ha) ho₁, by group⟩
  ·
    obtain ⟨X, hX, hXN⟩ := hX
    have hDY : σ.D ≤ Subgroup.normalizer
        ((oddCoreIn H ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) :=
      (le_inf hDO (hR₁D.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    obtain ⟨Rs, hRs, hRsD⟩ := exists_isSylowOf_normalized_of_odd hr hD2 hDY
      ((odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    have hRsO : IsSylowOf r Rs (oddCoreIn H) := by
      refine isSylowOf_of_card (hRs.le.trans inf_le_left) ?_
      rw [hRs.card_eq, ← (hX.of_le (le_inf hX.le hXN) inf_le_left).card_eq, hX.card_eq]
    obtain ⟨RH, hRH, hRNRH, hRHD⟩ := exists_isSylowOf_normalized_ge_of_odd hr hD2 hDO
      (odd_card_oddCoreIn H) hRNH hRN.isPGroup hRND
    obtain ⟨c, hc, hcRH⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr hD2 hDO
      (odd_card_oddCoreIn H) hRH hRsO hRHD hRsD
    have hcN : c ∈ Subgroup.normalizer (σ.ON : Set G) := by
      apply σ.N_le_normalizer_ON
      rw [σ.mem_N_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hc.2) σ.x hxD).symm
    refine ⟨RN.map (MulAut.conj c).toMonoidHom, isSylowOf_map_conj hRN hcN, ?_⟩
    calc RN.map (MulAut.conj c).toMonoidHom ≤ RH.map (MulAut.conj c).toMonoidHom :=
          Subgroup.map_mono hRNRH
      _ = Rs := hcRH
      _ ≤ Subgroup.normalizer (R₁ : Set G) := hRs.le.trans inf_le_right

theorem corIV61 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h61 : σ.PropIV61)
    (h62 : σ.PropIV62) : σ.CorIV61 := by
  intro r hr hdiv hexc H hH Rs hRs hRsD hnorm
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hDH : σ.D ≤ H := hH.2.2.1
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hOH : oddCoreIn H ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 hH.1
  set Z := CFSG.thompsonCenter Rs with hZ
  set M := pPrimeCoreIn r H with hM
  set O := oddCoreIn H with hO
  set C := CFSG.QuasiDihedralFusion.centerOf σ.D with hC
  have hZRs : Z ≤ Rs := CFSG.thompsonCenter_le Rs
  have hZp : IsPGroup r Z := hRs.isPGroup.to_le hZRs
  have hZH : Z ≤ H := hZRs.trans hRs.le
  have hMH : M ≤ H := pPrimeCoreIn_le r H
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn H
  have hMcop : Nat.Coprime r (Nat.card M) := by
    rw [hM, pPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hYH : M ⊔ Z ≤ H := sup_le hMH hZH
  have hYset : ((M ⊔ Z : Subgroup G) : Set G) = (Z : Set G) * (M : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hZH.trans hHM)
  have hCD : C ≤ σ.D := inf_le_left
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := hCD.trans (hDH.trans hHO)
  have hYS : M ⊔ Z ≤ O ⊔ C := by
    rw [hO, hC, ← hII.qgroup_solvRad H hDH hOH hH.2.1, solvRadIn,
      ← Subgroup.map_subgroupOf_eq_of_le hYH]
    apply Subgroup.map_mono
    refine le_trans ?_ (h61 r hr hdiv hexc H hH).1
    apply le_Op_p'p_of_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hnorm)
    intro y hy
    have hy' : (y : G) ∈ ((M ⊔ Z : Subgroup G) : Set G) := hy
    rw [hYset] at hy'
    obtain ⟨z, hz, m, hm, hzm⟩ := hy'
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
    have hk' : (⟨z, hZH hz⟩ : H) ^ r ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hyz : y = ⟨z, hZH hz⟩ * m₀ := Subtype.ext hzm.symm
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hyz, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff m₀).mpr hm₀, mul_one, ← QuotientGroup.mk_pow, hk',
      QuotientGroup.mk_one]
  have hZO : Z ≤ O := by
    have hle : Z ⊔ O ≤ C ⊔ O :=
      sup_le ((le_sup_right.trans hYS).trans (sup_comm O C).le) le_sup_right
    have h1 : O.relIndex Z ∣ O.relIndex C := by
      rw [← relIndex_sup_right_of_le_normalizer (hZH.trans hHO),
        ← relIndex_sup_right_of_le_normalizer hCO]
      exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex O (Z ⊔ O) (C ⊔ O) le_sup_right hle)
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hZp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hD2.to_le hCD)
    have hcop : Nat.Coprime (r ^ a) (2 ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
    refine Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop ?_ ?_)
    · rw [← ha]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card O Z)
    · rw [← hb]
      exact h1.trans (Dvd.intro _ (Subgroup.relIndex_mul_card O C))
  have hZeq : (M ⊔ Z) ⊓ (Rs ⊓ O) = Z := by
    refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right (le_inf hZRs hZO))
    have hyY : y ∈ ((M ⊔ Z : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hy).1
    have hyRs : y ∈ Rs := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).2).1
    rw [hYset] at hyY
    obtain ⟨z, hz, m, hm, rfl⟩ := hyY
    have hmRs : m ∈ Rs := by
      have h1 := Rs.mul_mem (Rs.inv_mem (hZRs hz)) hyRs
      rwa [inv_mul_cancel_left] at h1
    have hm1 : m = 1 := by
      obtain ⟨k, hk⟩ := hRs.isPGroup ⟨m, hmRs⟩
      have h1 : orderOf m ∣ r ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hMcop.pow_left k) h1
        (Subgroup.orderOf_dvd_natCard M hm))
    change z * m ∈ Z
    rw [hm1, mul_one]
    exact hz
  have hZD : σ.D ≤ Subgroup.normalizer (Z : Set G) := by
    rw [← hZeq]
    exact (le_inf (hDH.trans hnorm) hRsD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRsO : IsSylowOf r (Rs ⊓ O) O := hRs.inf_of_le_normalizer (oddCoreIn_le H) hHO
  have hRsNZ : Rs ⊓ O ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans (Subgroup.le_normalizer.trans
      (CFSG.normalizer_le_normalizer_thompsonCenter Rs))
  have hZY : IsSylowOf r Z (M ⊔ Z) := by
    refine isSylowOf_iff.mpr ⟨le_sup_right, hZp, ?_⟩
    rw [relIndex_sup_eq_relIndex_of_le_normalizer (hZH.trans hHM)]
    intro hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hMcop
      (hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_card Z M)))
  have hcov : (H : Set G) ⊆
      ((H ⊓ Subgroup.normalizer (Z : Set G) : Subgroup G) : Set G) * (O : Set G) := by
    intro h hh
    obtain ⟨n, hn, y, hy, rfl⟩ := subset_normalizer_mul_of_isSylowOf hZY hnorm hh
    have hy' : y ∈ ((C ⊔ O : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hYS hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCO] at hy'
    obtain ⟨d, hd, o, ho, rfl⟩ := hy'
    refine ⟨n * d, Subgroup.mem_inf.mpr ⟨?_, (Subgroup.normalizer (Z : Set G)).mul_mem hn
      (hZD (hCD hd))⟩, o, ho, by group⟩
    have h1 := H.mul_mem hh (H.inv_mem (oddCoreIn_le H ho))
    rwa [show n * (d * o) * o⁻¹ = n * d by group] at h1
  have hRsne : Rs ≠ ⊥ := by
    obtain ⟨R₀, hR₀, -, hR₀O⟩ := (σ.familyL_properties hσ hII hr hdiv hH).2.2.2.2.2
    exact ne_bot_of_isSylowOf_of_dvd hRs ((dvd_card_of_isSylowOf_of_dvd hR₀ hdiv).trans
      (Subgroup.card_dvd_of_le (hR₀O.trans (oddCoreIn_le H))))
  have hZne : Z ≠ ⊥ := CFSG.section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hRs.isPGroup hRsne
  exact h62 r hr hdiv H hH Z hZne hZp hZO hZD hcov ⟨Rs ⊓ O, hRsO, hRsNZ⟩

end Setting

end CFSG.ABGTheoremB
