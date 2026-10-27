module

public import CFSG.Open.Defs
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

variable {M : Type*} [Group M]

theorem eq_one_or_eq_of_natCard_eq_two {Z : Type*} [Group Z] (hZ : Nat.card Z = 2) {a : Z}
    (ha : a ≠ 1) (z : Z) : z = 1 ∨ z = a := by
  by_contra hne
  push Not at hne
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hinj : Function.Injective (![1, a, z] : Fin 3 → Z) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [hZ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem not_uniqueInvNormal_of_ambient_quasisimple (H : Subgroup M) (r : M) (hr : r ∈ H)
    (K : Subgroup M) (hK : centralizerIn H r = K) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 2) (u : M) (huK : u ∈ K) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hur : u ≠ r) (N : Subgroup H) : ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  intro h
  have hNK : ∀ n ∈ N, (n : M) ∈ K := fun n hn => by
    rw [← hK]
    exact mem_centralizerIn.mpr ⟨n.2, by
      simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp
        (h.le_centralizer hn))⟩
  have hrK : r ∈ K := by
    rw [← hK]
    exact mem_centralizerIn.mpr ⟨hr, rfl⟩
  have hrc : (⟨r, hrK⟩ : K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk : (k : M) ∈ centralizerIn H r := by rw [hK]; exact k.2
    exact (mem_centralizerIn.mp hk).2
  obtain ⟨s, hsN, hs4⟩ := h.exists_orderOf_eq_four
  have hr1 : (⟨r, hr⟩ : H) ≠ 1 := by
    intro hr1
    obtain ⟨s', hs'N, hst, hs'4⟩ := h.exists_sq_eq
    have : s' * s' = 1 := by rw [hst, hr1]
    have h2 : orderOf s' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hs'4] at h2
    omega
  have hr1' : (⟨r, hrK⟩ : K) ≠ 1 := fun h' => hr1 (Subtype.ext (by
    simpa using congrArg Subtype.val h'))
  let N' : Subgroup K := (N.map H.subtype).subgroupOf K
  have hmemN' : ∀ k : K, k ∈ N' ↔ ∃ n ∈ N, (n : M) = k := by
    intro k
    simp only [N', Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
  have hN'n : N'.Normal := by
    refine ⟨fun n' hn' k => ?_⟩
    obtain ⟨n, hn, hne⟩ := (hmemN' n').1 hn'
    have hk : (k : M) ∈ centralizerIn H r := by rw [hK]; exact k.2
    have hkc : (⟨(k : M), (mem_centralizerIn.mp hk).1⟩ : H) ∈
        Subgroup.centralizer ({(⟨r, hr⟩ : H)} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizerIn.mp hk).2
    exact (hmemN' _).2 ⟨_, h.conj_mem _ hkc n hn, by simp [← hne]⟩
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hNmap : (N'.map (QuotientGroup.mk' (Subgroup.center ↥K))).Normal :=
    Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hNmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N'.map (QuotientGroup.mk' (Subgroup.center ↥K))) with hbot | htop
  ·
    have hsK : (⟨(s : M), hNK s hsN⟩ : K) ∈ N' := (hmemN' _).2 ⟨s, hsN, rfl⟩
    have hsZ : (⟨(s : M), hNK s hsN⟩ : K) ∈ Subgroup.center ↥K := by
      have : QuotientGroup.mk' (Subgroup.center ↥K) ⟨(s : M), hNK s hsN⟩ ∈
          N'.map (QuotientGroup.mk' (Subgroup.center ↥K)) := ⟨_, hsK, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hsq : (⟨(s : M), hNK s hsN⟩ : K) ^ 2 = 1 := by
      rcases eq_one_or_eq_of_natCard_eq_two hZ (a := ⟨⟨r, hrK⟩, hrc⟩) (fun h' => hr1' (by
        simpa using congrArg Subtype.val h')) ⟨_, hsZ⟩ with h1 | h1
      · have := congrArg Subtype.val h1
        simp only [Subgroup.coe_one] at this
        rw [this]
        exact one_pow 2
      · have := congrArg Subtype.val h1
        simp only at this
        rw [this, pow_two]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        have h2 : orderOf (⟨r, hr⟩ : H) = 2 := by
          obtain ⟨s', -, hst, hs'4⟩ := h.exists_sq_eq
          have h3 : orderOf (s' ^ 2) = 2 := by
            rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs'4]; norm_num), hs'4]
          rwa [pow_two, hst] at h3
        have := pow_orderOf_eq_one (⟨r, hr⟩ : H)
        rw [h2, pow_two] at this
        simpa using congrArg Subtype.val this
    have h4 : orderOf (⟨(s : M), hNK s hsN⟩ : K) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h5 : orderOf (⟨(s : M), hNK s hsN⟩ : K) = 4 := by
      rw [Subgroup.orderOf_mk]
      rw [← Subgroup.orderOf_coe] at hs4
      exact hs4
    rw [h5] at h4
    omega
  ·
    have huK' : (⟨u, huK⟩ : K) ∈ N' := by
      have : QuotientGroup.mk' (Subgroup.center ↥K) ⟨u, huK⟩ ∈
          N'.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n', hn', hn'e⟩ := this
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hn'e
      have hz : n'⁻¹ * ⟨u, huK⟩ ∈ Subgroup.center ↥K := hn'e
      have htN' : (⟨r, hrK⟩ : K) ∈ N' := (hmemN' _).2 ⟨⟨r, hr⟩, h.mem, rfl⟩
      rcases eq_one_or_eq_of_natCard_eq_two hZ (a := ⟨⟨r, hrK⟩, hrc⟩) (fun h' => hr1' (by
        simpa using congrArg Subtype.val h')) ⟨_, hz⟩ with h1 | h1
      · have h2 : n'⁻¹ * ⟨u, huK⟩ = 1 := congrArg Subtype.val h1
        have : (⟨u, huK⟩ : K) = n' := by
          rw [inv_mul_eq_one] at h2
          exact h2.symm
        rw [this]
        exact hn'
      · have h2 : n'⁻¹ * ⟨u, huK⟩ = ⟨r, hrK⟩ := congrArg Subtype.val h1
        have : (⟨u, huK⟩ : K) = n' * ⟨r, hrK⟩ := by
          rw [← h2]
          group
        rw [this]
        exact N'.mul_mem hn' htN'
    obtain ⟨n, hn, hne0⟩ := (hmemN' _).1 huK'
    have hne : (n : M) = u := hne0
    have hn2 : orderOf n = 2 := by
      refine orderOf_eq_prime (by
        rw [pow_two]
        apply Subtype.ext
        simpa [hne] using hu2) ?_
      intro hn1
      apply hu1
      rw [← hne, hn1]
      rfl
    have := h.eq_of_orderOf_eq_two n hn hn2
    apply hur
    rw [← hne, this]

end CFSG.ClassicalInvolution.Nobq
