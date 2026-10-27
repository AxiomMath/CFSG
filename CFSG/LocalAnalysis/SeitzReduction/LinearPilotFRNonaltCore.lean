module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

namespace Nonalt

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

variable (K) in
@[expose] def coreRadical (i : Fin n) : Subgroup (projectiveSL n K) :=
  perfectCore (autFixSubgroup (dualAut n K)) ⊓ radical i

theorem levi_le_perfectCore {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ}
    (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) (i : Fin n) :
    levi (K := K) i ≤ perfectCore (autFixSubgroup (dualAut n K)) :=
  le_perfectCore_of_perfect (levi_le i) (levi_spec hK hq hr hr1 i).2.1

variable [CharP K 2]

theorem le_radical_of_isPGroup {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ}
    (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) (i : Fin n) {T : Subgroup (projectiveSL n K)}
    (hT : IsPGroup 2 T) (hTΘ : T ≤ perfectCore (autFixSubgroup (dualAut n K)))
    (hN : perfectCore (autFixSubgroup (dualAut n K)) ≤ normalizer (T : Set (projectiveSL n K))) :
    T ≤ radical (K := K) i := by
  have hev : Even n := ⟨r + 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  set X := autFixSubgroup (dualAut n K) with hX
  set R := radical (K := K) i with hR
  set L := levi (K := K) i with hL
  have hLΘ := levi_le_perfectCore hK hq hr hr1 i
  obtain ⟨hsimple, hperf, -⟩ := levi_spec hK hq hr hr1 i
  have hXR := le_normalizer_radical (K := K) hev hn3 i
  have hTX : T ≤ X := hTΘ.trans (perfectCore_le X)
  have hTR2 : IsPGroup 2 (T ⊔ R : Subgroup (projectiveSL n K)) :=
    IsPGroup.to_sup_of_normal_right' hT (isPGroup_radical hev i) (hTX.trans hXR)
  set T' := (T ⊔ R) ⊓ L with hT'
  have hLN : L ≤ normalizer (T' : Set (projectiveSL n K)) := by
    have h1 : L ≤ normalizer ((T ⊔ R : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) :=
      (le_inf (hLΘ.trans hN) ((levi_le i).trans hXR)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    exact (le_inf h1 le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTn : (T'.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hLN
  have hT'bot : T' = ⊥ := by
    have := hTn
    rcases hsimple.eq_bot_or_eq_top_of_normal (T'.subgroupOf L) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact le_bot_iff.1 fun x hx => h.le_bot ⟨hx, (inf_le_right : T' ≤ L) hx⟩
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have hL2 : IsPGroup 2 L := hTR2.to_le (h.trans inf_le_left)
      have hLbot := eq_bot_of_commutator_eq_self_of_isPGroup (p := 2) L hL2 hperf
      have : Nontrivial L := hsimple.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne L
      apply hab
      have ha : (a : projectiveSL n K) = 1 := (Subgroup.eq_bot_iff_forall L).1 hLbot _ a.2
      have hb : (b : projectiveSL n K) = 1 := (Subgroup.eq_bot_iff_forall L).1 hLbot _ b.2
      exact Subtype.ext (ha.trans hb.symm)
  intro t ht
  obtain ⟨ρ, hρ, s, hs, hρs⟩ := exists_radical_mul_levi hev hn3 i (hTX ht)
  have hsT' : s ∈ T' := by
    refine ⟨?_, hs⟩
    have e : s = ρ⁻¹ * t := by rw [← hρs, inv_mul_cancel_left]
    rw [e]
    exact (T ⊔ R).mul_mem ((T ⊔ R).inv_mem (Subgroup.mem_sup_right hρ))
      (Subgroup.mem_sup_left ht)
  rw [hT'bot, mem_bot] at hsT'
  rw [← hρs, hsT', mul_one]
  exact hρ

theorem coreRadical_spec {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ}
    (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) (i : Fin n) :
    IsPGroup 2 (coreRadical K i) ∧
      coreRadical K i ≤ perfectCore (autFixSubgroup (dualAut n K)) ∧
      perfectCore (autFixSubgroup (dualAut n K)) ≤
        normalizer (coreRadical K i : Set (projectiveSL n K)) ∧
      (∀ T : Subgroup (projectiveSL n K), IsPGroup 2 T →
        T ≤ perfectCore (autFixSubgroup (dualAut n K)) →
        perfectCore (autFixSubgroup (dualAut n K)) ≤ normalizer (T : Set (projectiveSL n K)) →
          T ≤ coreRadical K i) ∧
      perfectCore (autFixSubgroup (dualAut n K)) = coreRadical K i ⊔ levi i ∧
      levi (K := K) i ≤ normalizer (coreRadical K i : Set (projectiveSL n K)) ∧
      Disjoint (coreRadical K i) (levi (K := K) i) := by
  have hev : Even n := ⟨r + 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  set Θ := perfectCore (autFixSubgroup (dualAut n K)) with hΘ
  have hLΘ := levi_le_perfectCore hK hq hr hr1 i
  have hXR := le_normalizer_radical (K := K) hev hn3 i
  have hΘN : Θ ≤ normalizer (coreRadical K i : Set (projectiveSL n K)) :=
    (le_inf le_normalizer ((perfectCore_le _).trans hXR)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨(isPGroup_radical hev i).to_le inf_le_right, inf_le_left, hΘN,
    fun T hT hTΘ hN => le_inf hTΘ (le_radical_of_isPGroup hK hq hr hr1 i hT hTΘ hN),
    le_antisymm ?_ (sup_le inf_le_left hLΘ), hLΘ.trans hΘN,
    (disjoint_radical_levi hev i).mono_left inf_le_right⟩
  intro x hx
  obtain ⟨ρ, hρ, s, hs, rfl⟩ := exists_radical_mul_levi hev hn3 i ((perfectCore_le _) hx)
  have hρΘ : ρ ∈ Θ := by
    have e : ρ = (ρ * s) * s⁻¹ := by group
    rw [e]
    exact Θ.mul_mem hx (Θ.inv_mem (hLΘ hs))
  exact Subgroup.mul_mem_sup ⟨hρΘ, hρ⟩ hs

omit [Finite K] in
theorem coreRadical_comm {i : Fin n} (hn : Even n) {x y : projectiveSL n K}
    (hx : x ∈ coreRadical K i) (hy : y ∈ coreRadical K i) : x * y = y * x :=
  radical_comm hn hx.2 hy.2

theorem card_coreRadical_le (hn : Even n) (i : Fin n) :
    Nat.card (coreRadical K i) ≤ Nat.card K ^ (n - 1) := by
  have h := Subgroup.card_le_of_le (inf_le_right : coreRadical K i ≤ radical (K := K) i)
  exact h.trans (card_radical_le hn i)

theorem map_coreRadical_eq {G : Type*} [Group G] {φ φ' : projectiveSL n K →* G}
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : n = 2 * r + 2)
    (hr1 : 1 ≤ r) (i : Fin n) (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hΘ : (perfectCore (autFixSubgroup (dualAut n K))).map φ =
      (perfectCore (autFixSubgroup (dualAut n K))).map φ') :
    (coreRadical K i).map φ' = (coreRadical K i).map φ := by
  obtain ⟨hQp, hQΘ, hΘN, hmax, -⟩ := coreRadical_spec hK hq hr hr1 i
  have heq : coreRadical K i = ((coreRadical K i).map φ).comap φ' := by
    apply le_antisymm
    · exact le_comap_map_of_forall hφ hΘ hmax hQp hQΘ hΘN
    · exact hmax _ (isPGroup_comap_map hφ' hQp) (comap_map_le hφ' hΘ hQΘ)
        (le_normalizer_comap_map hΘ hΘN)
  have h2 := map_comap_map_eq hΘ hQΘ
  rw [← heq] at h2
  exact h2

theorem map_coreRadical_eq_of_map_eq {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {r : ℕ} (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) (i : Fin n) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (autFixSubgroup (dualAut n K))).map β.toMonoidHom =
      perfectCore (autFixSubgroup (dualAut n K))) :
    (coreRadical K i).map β.toMonoidHom = coreRadical K i := by
  obtain ⟨hQp, hQΘ, hΘN, hmax, -⟩ := coreRadical_spec hK hq hr hr1 i
  have hle : (coreRadical K i).map β.toMonoidHom ≤ coreRadical K i := by
    refine hmax _ (hQp.map _) ?_ ?_
    · rw [← hβ]
      exact map_mono hQΘ
    · rw [← hβ]
      exact (map_mono hΘN).trans (le_normalizer_map _)
  exact eq_of_le_of_card_ge hle (card_map_of_injective β.injective).ge

end Nonalt

end CFSG.SeitzReduction.LinearPilot
