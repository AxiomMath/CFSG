module

public import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoQData
public import CFSG.ClassicalInvolution.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem exists_iterate_commutator_mem {G : Type*} [Group G] {U Λ : Subgroup G}
    (hUs : IsSubnormal U Λ) {t : G} (ht : t ∈ U) {g : G} (hg : g ∈ Λ) :
    ∃ n : ℕ, (fun x => x * t * x⁻¹ * t⁻¹)^[n] g ∈ U := by
  induction hUs generalizing g with
  | refl H => exact ⟨0, hg⟩
  | step hHM hn hMK ih =>
      rename_i H M K
      obtain ⟨n, hn'⟩ := ih (hHM ht) hg
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      have hmem : (⟨(fun x => x * t * x⁻¹ * t⁻¹)^[n] g, hn'⟩ : M) * ⟨t, hHM ht⟩ *
          (⟨(fun x => x * t * x⁻¹ * t⁻¹)^[n] g, hn'⟩ : M)⁻¹ * ⟨t, hHM ht⟩⁻¹ ∈
          H.subgroupOf M :=
        (H.subgroupOf M).mul_mem
          (hn.conj_mem ⟨t, hHM ht⟩ (mem_subgroupOf.mpr ht) ⟨_, hn'⟩)
          ((H.subgroupOf M).inv_mem (mem_subgroupOf.mpr ht))
      exact Subgroup.mem_subgroupOf.mp hmem

theorem iterate_commutator_of_conj_eq_inv {G : Type*} [Group G] {t a : G}
    (h : t * a * t⁻¹ = a⁻¹) (n : ℕ) :
    (fun x => x * t * x⁻¹ * t⁻¹)^[n] a = a ^ (2 ^ n) := by
  have hinv : t * a⁻¹ * t⁻¹ = a := by
    simpa [mul_assoc] using congrArg Inv.inv h
  have hc : ∀ m : ℕ, t * (a ^ m)⁻¹ * t⁻¹ = a ^ m := by
    intro m
    rw [← inv_pow, ← conj_pow, hinv]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      calc a ^ 2 ^ n * t * (a ^ 2 ^ n)⁻¹ * t⁻¹
          = a ^ 2 ^ n * (t * (a ^ 2 ^ n)⁻¹ * t⁻¹) := by group
        _ = a ^ 2 ^ n * a ^ 2 ^ n := by rw [hc]
        _ = a ^ 2 ^ (n + 1) := by rw [← pow_add, pow_succ, Nat.mul_two]

theorem exists_inv_noncomm_of_su {X : Type} [Group X] [Finite X]
    (hX : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU 3 2 K)))
    {t : X} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ c d : X, c ^ 3 = 1 ∧ d ^ 3 = 1 ∧ c * d ≠ d * c ∧ t * c * t⁻¹ = c⁻¹ ∧
      t * d * t⁻¹ = d⁻¹ := by
  classical
  obtain ⟨K, hKfield, hKfin, hK4, ⟨e⟩⟩ := hX
  have htop : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(⊤ : Subgroup X) ≃* ↥(CFSG.Open.StatedSU 3 2 K)) :=
    ⟨K, hKfield, hKfin, hK4, ⟨Subgroup.topEquiv.trans e⟩⟩
  obtain ⟨s, d, z, f, g, -, -, -, hf4, hfs, hfd, -, hHeis, hsO, hdO, hsd, -, hf2, hg2,
    hgf, hTcard⟩ := SUQ.exists_qdata_of_su (Y := X) (T := ⊤) htop
  have hs3 : s ^ 3 = 1 := hHeis.cube s hsO
  have hd3 : d ^ 3 = 1 := hHeis.cube d hdO
  let φ : QuaternionGroup 2 →* X := SUQ.quatHom hf4 hg2 hgf
  let Q : Subgroup X := φ.range
  have hφ : Function.Injective φ := SUQ.quatHom_injective hf4 hf2 hg2 hgf
  have hQcard : Nat.card Q = 8 := by
    show Nat.card φ.range = 8
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hXcard : Nat.card X = 216 := by
    rw [← Subgroup.card_top]
    exact hTcard
  have hQfac : Nat.card Q = 2 ^ (Nat.card X).factorization 2 := by
    rw [hQcard, hXcard]
    have h216 : (216 : ℕ) = 2 ^ 3 * 27 := by norm_num
    rw [h216, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 27)]
    norm_num
  let S : Sylow 2 X := Sylow.ofCard Q hQfac
  have hSQ : (S : Subgroup X) = Q := Sylow.coe_ofCard _ _
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨c, s', hsS, hsord, hcst⟩ :=
    CFSG.ClassicalInvolution.exists_conj_mem_sylow_of_orderOf_eq_two S htord
  have hsQ : s' ∈ Q := hSQ ▸ hsS
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hsQ
  have hs'1 : s' ≠ 1 := by
    intro h1
    rw [h1] at hsord
    simp at hsord
  have hs'2 : s' ^ 2 = 1 := by
    simpa [hsord] using pow_orderOf_eq_one s'
  have hq2 : q ^ 2 = 1 := by
    apply hφ
    rw [map_pow, hq, hs'2, map_one]
  have hq1 : q ≠ 1 := by
    intro h1
    exact hs'1 (by rw [← hq, h1, map_one])
  have hqa : q = QuaternionGroup.a 2 :=
    (CFSG.ClassicalInvolution.quaternionGroup_orderOf_eq_two_iff 2 q).mp
      (orderOf_eq_prime hq2 hq1)
  have hs'f2 : s' = f ^ 2 := by
    rw [← hq, hqa]
    have h := SUQ.quatHom_a hf4 hg2 hgf (2 : ZMod (2 * 2))
    rw [show φ (QuaternionGroup.a 2) = f ^ (ZMod.cast (2 : ZMod (2 * 2)) : ℤ) from h,
      ZMod.cast_eq_val,
      show (2 : ZMod (2 * 2)) = ((2 : ℕ) : ZMod (2 * 2)) from rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by norm_num), zpow_natCast]
  have ht_eq : t = c * f ^ 2 * c⁻¹ := by
    rw [← hcst, hs'f2]
  have hconj_s : t * (c * s * c⁻¹) * t⁻¹ = (c * s * c⁻¹)⁻¹ := by
    rw [ht_eq]
    calc c * f ^ 2 * c⁻¹ * (c * s * c⁻¹) * (c * f ^ 2 * c⁻¹)⁻¹
        = c * (f ^ 2 * s * (f ^ 2)⁻¹) * c⁻¹ := by group
      _ = c * s⁻¹ * c⁻¹ := by rw [hfs]
      _ = (c * s * c⁻¹)⁻¹ := by group
  have hconj_d : t * (c * d * c⁻¹) * t⁻¹ = (c * d * c⁻¹)⁻¹ := by
    rw [ht_eq]
    calc c * f ^ 2 * c⁻¹ * (c * d * c⁻¹) * (c * f ^ 2 * c⁻¹)⁻¹
        = c * (f ^ 2 * d * (f ^ 2)⁻¹) * c⁻¹ := by group
      _ = c * d⁻¹ * c⁻¹ := by rw [hfd]
      _ = (c * d * c⁻¹)⁻¹ := by group
  have hcs3 : (c * s * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hs3, mul_one, mul_inv_cancel]
  have hcd3 : (c * d * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hd3, mul_one, mul_inv_cancel]
  have hcsd : (c * s * c⁻¹) * (c * d * c⁻¹) ≠ (c * d * c⁻¹) * (c * s * c⁻¹) := by
    intro h1
    apply hsd
    have h2 := congrArg (fun x => c⁻¹ * x * c) h1
    simpa [mul_assoc] using h2
  exact ⟨c * s * c⁻¹, c * d * c⁻¹, hcs3, hcd3, hcsd, hconj_s, hconj_d⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
