module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem odd_card_of_forall_odd_orderOf {G : Type} [Group G] [Finite G]
    (h : ∀ x : G, Odd (orderOf x)) : Odd (Nat.card G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.mp hev)
  have h1 := h z
  rw [hz] at h1
  exact absurd h1 (by decide)

theorem exists_isElemAbelian_lift {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) {Ab : Subgroup (H ⧸ N)} (hAb : IsElemAbelian 2 Ab) :
    ∃ E : Subgroup H, IsElemAbelian 2 E ∧ Nat.card E = Nat.card Ab := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set Et : Subgroup H := Ab.comap π with hEt
  set ρ : Et →* Ab := π.subgroupComap Ab with hρ
  have hρsurj : Function.Surjective ρ :=
    MonoidHom.subgroupComap_surjective π Ab (QuotientGroup.mk'_surjective N)
  have hAbp : IsPGroup 2 Ab := fun x => ⟨1, Subtype.ext (by simpa using hAb.2 (x : H ⧸ N) x.2)⟩
  have hker_mem : ∀ x : Et, ρ x = 1 → (x : H) ∈ N := by
    intro x hx
    have : π (x : H) = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff _).mp this
  have hker_odd : ∀ x : Et, ρ x = 1 → Odd (orderOf x) := by
    intro x hx
    have hxN := hker_mem x hx
    have h1 : orderOf (⟨(x : H), hxN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h2 : orderOf (⟨(x : H), hxN⟩ : N) = orderOf x := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [← h2]
    exact Odd.of_dvd_nat hN h1
  have hkerodd : Odd (Nat.card ρ.ker) := by
    refine odd_card_of_forall_odd_orderOf fun x => ?_
    have h := hker_odd (x : Et) x.2
    rwa [Subgroup.orderOf_coe] at h
  have hcard : Nat.card ρ.ker * Nat.card Ab = Nat.card Et := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rwa [MonoidHom.range_eq_top.mpr hρsurj, Subgroup.card_top] at h
  obtain ⟨S⟩ : Nonempty (Sylow 2 Et) := inferInstance
  obtain ⟨j, hj⟩ := hAbp.exists_card_eq
  have hScard : Nat.card S = Nat.card Ab := by
    rw [Sylow.card_eq_multiplicity, ← hcard, hj,
      Nat.factorization_mul hkerodd.pos.ne' (pow_pos (by norm_num) j).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hkerodd)
        (even_iff_two_dvd.mpr h)), Nat.Prime.factorization_pow Nat.prime_two]
    simp
  set φ : S →* Ab := ρ.comp (S : Subgroup Et).subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : ρ (x : Et) = 1 := hx
    obtain ⟨k, hk⟩ := S.isPGroup' x
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hodd : Odd (orderOf x) := by
      have := hker_odd (x : Et) hx1
      rwa [Subgroup.orderOf_coe] at this
    have hi0 : i = 0 := by
      by_contra hne
      rw [hi] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
    have hone : orderOf x = 1 := by rw [hi, hi0, pow_zero]
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  refine ⟨(S : Subgroup Et).map Et.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩
    apply Subtype.ext
    have hc : φ ⟨s, hs⟩ * φ ⟨t, ht⟩ = φ ⟨t, ht⟩ * φ ⟨s, hs⟩ :=
      Subtype.ext (congrArg Subtype.val (hAb.1.is_comm.comm (φ ⟨s, hs⟩) (φ ⟨t, ht⟩)))
    have h2 : (⟨s, hs⟩ : S) * ⟨t, ht⟩ = ⟨t, ht⟩ * ⟨s, hs⟩ :=
      hφinj (by rw [map_mul, map_mul]; exact hc)
    exact congrArg (fun z : S => ((z : Et) : H)) h2
  · rintro _ ⟨s, hs, rfl⟩
    have h2 : (⟨s, hs⟩ : S) ^ 2 = 1 := by
      apply hφinj
      rw [map_pow, map_one]
      exact Subtype.ext (hAb.2 _ (φ ⟨s, hs⟩).2)
    have h3 := congrArg (fun z : S => ((z : Et) : H)) h2
    simpa using h3
  · rw [Subgroup.card_map_of_injective Et.subtype_injective]
    exact hScard

end CFSG.QuasithinUnique.Lin2
