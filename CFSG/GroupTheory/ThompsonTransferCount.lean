module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.ThompsonTransferCount

open MulAction Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.ThompsonIndexTwo

section Orbits

variable {H α : Type*} [Group H] [MulAction H α] [Fintype α]

theorem card_filter_eq_sum_orbit [Fintype (orbitRel.Quotient H α)] (R : α → Prop)
    [DecidablePred R] (hR : ∀ (h : H) (a : α), R (h • a) ↔ R a) :
    (Finset.univ.filter R).card =
      ∑ ω : orbitRel.Quotient H α, if R ω.out then Nat.card (orbit H ω.out) else 0 := by
  classical
  rw [Finset.card_filter]
  calc ∑ a : α, (if R a then 1 else 0)
      = ∑ s : (ω : orbitRel.Quotient H α) × ↥(orbit H ω.out), if R s.2.1 then 1 else 0 := by
        rw [← Equiv.sum_comp (selfEquivSigmaOrbits H α) (fun s => if R s.2.1 then 1 else 0)]
        rfl
    _ = ∑ ω : orbitRel.Quotient H α, ∑ b : ↥(orbit H ω.out), if R b.1 then 1 else 0 :=
        Fintype.sum_sigma _
    _ = _ := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hb : ∀ b : ↥(orbit H ω.out), (R b.1 ↔ R ω.out) := by
          rintro ⟨b, g, rfl⟩
          exact hR g _
        by_cases hω : R ω.out
        · rw [if_pos hω, Finset.sum_congr rfl fun b _ => if_pos ((hb b).mpr hω), Finset.sum_const,
            Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]
        · rw [if_neg hω]
          exact Finset.sum_eq_zero fun b _ => if_neg fun h => hω ((hb b).mp h)

end Orbits

section Cosets

variable {G : Type*} [Group G] {T U : Subgroup G}

theorem smul_eq_iff (g : G) (y : G ⧸ T) : g • y = y ↔ y.out⁻¹ * g * y.out ∈ T := by
  have h := smul_mk_eq_iff T g y.out
  rwa [QuotientGroup.out_eq'] at h

theorem pow_smul_eq_iff_dvd (x : G) (y : G ⧸ T) (n : ℕ) :
    x ^ n • y = y ↔ Function.minimalPeriod (x • ·) y ∣ n := by
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt, Function.IsFixedPt,
    smul_iterate]

theorem minimalPeriod_eq_of_mem_of_not_mem (hUidx : U.relIndex T = 2) (x : G) {k : ℕ}
    (hk : 1 ≤ k) (y : G ⧸ T) (hT : y.out⁻¹ * x ^ 2 ^ k * y.out ∈ T)
    (hU : y.out⁻¹ * x ^ 2 ^ k * y.out ∉ U) : Function.minimalPeriod (x • ·) y = 2 ^ k := by
  have hd : Function.minimalPeriod (x • ·) y ∣ 2 ^ k :=
    (pow_smul_eq_iff_dvd x y _).mp ((smul_eq_iff _ y).mpr hT)
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rcases Nat.lt_or_ge j k with hlt | hge
  · exfalso
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hz : y.out⁻¹ * x ^ 2 ^ k' * y.out ∈ T := by
      rw [← smul_eq_iff, pow_smul_eq_iff_dvd, hj]
      exact pow_dvd_pow 2 (by omega)
    apply hU
    have h2 := Subgroup.mul_self_mem_of_index_two (H := U.subgroupOf T) hUidx ⟨_, hz⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h2
    rw [show y.out⁻¹ * x ^ 2 ^ (k' + 1) * y.out =
        y.out⁻¹ * x ^ 2 ^ k' * y.out * (y.out⁻¹ * x ^ 2 ^ k' * y.out) by
      rw [pow_succ, pow_mul, sq]; group]
    exact h2
  · rw [hj, le_antisymm hjk hge]

variable [(U.subgroupOf T).Normal] [IsMulCommutative (Qbar T U)]

open scoped Classical in
theorem mem_not_mem_iff_valF (u : G) (y : G ⧸ T) :
    (y.out⁻¹ * u * y.out ∈ T ∧ y.out⁻¹ * u * y.out ∉ U) ↔ valF T U u y ≠ 1 := by
  rw [valF_eq T U u y y.out (QuotientGroup.out_eq' y)]
  by_cases h : y.out⁻¹ * u * y.out ∈ T
  · simp only [h, ↓reduceDIte, true_and, Ne, phiQ_eq_one_iff]
  · simp only [h, ↓reduceDIte, false_and, ne_eq, not_true_eq_false]

theorem mem_not_mem_smul_iff (u d : G) (hd : d * u = u * d) (y : G ⧸ T) :
    ((d • y).out⁻¹ * u * (d • y).out ∈ T ∧ (d • y).out⁻¹ * u * (d • y).out ∉ U) ↔
      (y.out⁻¹ * u * y.out ∈ T ∧ y.out⁻¹ * u * y.out ∉ U) := by
  rw [mem_not_mem_iff_valF, mem_not_mem_iff_valF, valF_smul T U u d hd y]

end Cosets

section Main

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem two_pow_dvd_card_orbit {T : Subgroup G} (hT : IsPGroup 2 T) {u : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer {u})
    (hKsyl : ¬ 2 ∣ K.relIndex (Subgroup.centralizer {u})) {j : ℕ} (y : G ⧸ T)
    (hyT : y.out⁻¹ * u * y.out ∈ T)
    (hd : 2 ^ j * Nat.card ↥(T ⊓ Subgroup.centralizer {y.out⁻¹ * u * y.out}) ∣
      Nat.card ↥(Subgroup.centralizer {u})) :
    2 ^ j ∣ Nat.card (orbit K y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := y.out with ht
  set w := t⁻¹ * u * t with hw
  set Cw : Subgroup G := T ⊓ Subgroup.centralizer {w} with hCw
  set C : Subgroup G := Subgroup.centralizer {u} with hC
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp (hT.to_le (inf_le_left : Cw ≤ T)))
  have hK : 2 ^ j * Nat.card Cw ∣ Nat.card K := by
    have hrel := Subgroup.relIndex_mul_card K C
    rw [inf_of_le_left hKC] at hrel
    rw [← hrel] at hd
    rw [ha, ← pow_add] at hd ⊢
    exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hKsyl)).dvd_of_dvd_mul_left hd
  set Sy : Subgroup K := stabilizer K y with hSy
  have hSdvd : Nat.card Sy ∣ Nat.card Cw := by
    set φ : ↥K →* G := (MulAut.conj t⁻¹).toMonoidHom.comp K.subtype with hφ
    have hφinj : Function.Injective φ := (MulAut.conj t⁻¹).injective.comp K.subtype_injective
    have hle : Sy.map φ ≤ Cw := by
      rintro z ⟨s, hs, rfl⟩
      have hs' : (s : G) • y = y := hs
      have hsT := (smul_eq_iff (s : G) y).mp hs'
      have hsu : (s : G) * u = u * s :=
        (Subgroup.mem_centralizer_iff.mp (hKC s.2) u (Set.mem_singleton u)).symm
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simpa [hφ, MulAut.conj_apply] using hsT
      · rw [Subgroup.mem_centralizer_iff]
        rintro z rfl
        simp only [hφ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          Subgroup.coe_subtype, MulAut.conj_apply, inv_inv, hw]
        calc t⁻¹ * u * t * (t⁻¹ * s * t) = t⁻¹ * (u * s) * t := by group
          _ = t⁻¹ * (s * u) * t := by rw [hsu]
          _ = t⁻¹ * s * t * (t⁻¹ * u * t) := by group
    rw [← Subgroup.card_map_of_injective (K := Sy) hφinj]
    exact Subgroup.card_dvd_of_le hle
  have hos : Nat.card Sy * Nat.card (orbit K y) = Nat.card K := by
    rw [← Subgroup.card_mul_index Sy, hSy, index_stabilizer, Nat.card_coe_set_eq]
  have hS0 : Nat.card Sy ≠ 0 := Nat.card_pos.ne'
  have h1 : 2 ^ j * Nat.card Sy ∣ Nat.card Sy * Nat.card (orbit K y) :=
    hos ▸ (mul_dvd_mul_left _ hSdvd).trans hK
  rw [mul_comm (2 ^ j)] at h1
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hS0)).mp h1

theorem exists_normal_index_two_of_count {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U) (hconj : ∀ g : G, g⁻¹ * x * g ∉ U)
    (hpow : ∀ (g : G) (k : ℕ), 1 ≤ k → g⁻¹ * x ^ 2 ^ k * g ∈ T → g⁻¹ * x ^ 2 ^ k * g ∉ U →
      2 ^ (k + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer {g⁻¹ * x ^ 2 ^ k * g}) ∣
        Nat.card ↥(Subgroup.centralizer {x ^ 2 ^ k})) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQcard : Nat.card (Qbar T U) = 2 := hUidx
  haveI : IsCyclic (Qbar T U) := isCyclic_of_prime_card hQcard
  haveI : IsMulCommutative (Qbar T U) := inferInstance
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  obtain ⟨N₀, hN₀⟩ : ∃ n, orderOf x = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT ⟨x, hxT⟩
    exact ⟨n, by simpa using hn⟩
  set g₀ : Qbar T U := phiQ T U ⟨x, hxT⟩ with hg₀
  have hg₀1 : g₀ ≠ 1 := fun h => hxU ((phiQ_eq_one_iff T U _).mp h)
  have hg₀2 : g₀ ^ 2 = 1 := by rw [← hQcard]; exact pow_card_eq_one'
  have hval : ∀ z : ↥T, phiQ T U z = if (z : G) ∈ U then 1 else g₀ := by
    intro z
    split_ifs with hz
    · exact (phiQ_eq_one_iff T U z).mpr hz
    · have h1 : (((⟨x, hxT⟩ : ↥T)⁻¹ * z : ↥T) : G) ∈ U := by
        simpa using inv_mul_mem_of_not_mem hUidx hxT z.2 hxU hz
      have h2 := (phiQ_eq_one_iff T U _).mpr h1
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
  set mp : G ⧸ T → ℕ := fun y => Function.minimalPeriod (x • ·) y with hmp
  set bad : orbitRel.Quotient (zpowers x) (G ⧸ T) → Prop :=
    fun q => q.out.out⁻¹ * x ^ mp q.out * q.out.out ∉ U with hbad
  have hτ : MonoidHom.transfer (phiQ T U) x = g₀ ^ (Finset.univ.filter bad).card := by
    rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    simp only [hval]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hmpdvd : ∀ y : G ⧸ T, mp y ∣ 2 ^ N₀ := fun y => by
    rw [← hN₀]
    exact (pow_smul_eq_iff_dvd x y _).mp (by rw [pow_orderOf_eq_one, one_smul])
  have heven : ∀ k : ℕ, 1 ≤ k →
      2 ∣ (Finset.univ.filter (fun q => bad q ∧ mp q.out = 2 ^ k)).card := by
    intro k hk
    set n := 2 ^ k with hn
    set R : G ⧸ T → Prop :=
      fun y => y.out⁻¹ * x ^ n * y.out ∈ T ∧ y.out⁻¹ * x ^ n * y.out ∉ U with hR
    have hRiff : ∀ y, R y ↔ (mp y = n ∧ y.out⁻¹ * x ^ mp y * y.out ∉ U) := by
      intro y
      constructor
      · rintro ⟨h1, h2⟩
        have hm : mp y = n := minimalPeriod_eq_of_mem_of_not_mem hUidx x hk y h1 h2
        exact ⟨hm, by rw [hm]; exact h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by rwa [h1] at h2⟩
        rw [← smul_eq_iff, pow_smul_eq_iff_dvd]
        exact h1.symm ▸ dvd_refl _
    have hcomm : ∀ h : G, h ∈ zpowers x → h * x ^ n = x ^ n * h := by
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (((Commute.refl x).zpow_left j).pow_right n).eq
    have hd1 : (Finset.univ.filter R).card =
        n * (Finset.univ.filter (fun q => bad q ∧ mp q.out = n)).card := by
      rw [card_filter_eq_sum_orbit (H := zpowers x) R
        (fun h y => mem_not_mem_smul_iff (x ^ n) h (hcomm h h.2) y), Finset.card_filter,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : R q.out
      · have h' := (hRiff _).mp hq
        rw [if_pos hq, if_pos ⟨h'.2, h'.1⟩, mul_one, Nat.card_eq_fintype_card,
          ← MulAction.minimalPeriod_eq_card]
        exact h'.1
      · rw [if_neg hq, if_neg (fun h => hq ((hRiff _).mpr ⟨h.2, h.1⟩)), mul_zero]
    have hd2 : 2 * n ∣ (Finset.univ.filter R).card := by
      obtain ⟨j₀, hj₀⟩ : ∃ j, orderOf (x ^ n) = 2 ^ j := by
        have h1 := orderOf_pow_dvd (x := x) n
        rw [hN₀] at h1
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
        exact ⟨j, hj⟩
      obtain ⟨K, hKC, -, hKsyl, -⟩ := exists_sylow_centralizer (p := 2) ⟨j₀, hj₀⟩
      have h2n : 2 * n = 2 ^ (k + 1) := by rw [hn, pow_succ, mul_comm]
      rw [card_filter_eq_sum_orbit (H := K) R (fun h y => mem_not_mem_smul_iff (x ^ n) h
        (Subgroup.mem_centralizer_iff.mp (hKC h.2) _ (Set.mem_singleton _)).symm y)]
      refine Finset.dvd_sum fun q _ => ?_
      split_ifs with hq
      · rw [h2n]
        exact two_pow_dvd_card_orbit hT hKC hKsyl q.out hq.1 (hpow q.out.out k hk hq.1 hq.2)
      · exact dvd_zero _
    rw [hd1, mul_comm 2 n] at hd2
    exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < n)).mp hd2
  have hfix : Odd (Finset.univ.filter
      (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) => mp q.out = 1)).card := by
    have hzp : IsPGroup 2 (zpowers x) := hT.to_le (Subgroup.zpowers_le.mpr hxT)
    have hmod := hzp.card_modEq_card_fixedPoints (G ⧸ T)
    have hinvF : ∀ (h : zpowers x) (y : G ⧸ T),
        h • y ∈ fixedPoints (zpowers x) (G ⧸ T) ↔ y ∈ fixedPoints (zpowers x) (G ⧸ T) := by
      intro h y
      constructor
      · intro hy
        have h1 : h⁻¹ • (h • y) = h • y := mem_fixedPoints.mp hy h⁻¹
        rw [inv_smul_smul] at h1
        rw [h1]
        exact hy
      · intro hy
        rw [mem_fixedPoints.mp hy h]
        exact hy
    have hcount : Nat.card (fixedPoints (zpowers x) (G ⧸ T)) =
        (Finset.univ.filter
          (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) => mp q.out = 1)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
        card_filter_eq_sum_orbit (H := zpowers x) (fun y => y ∈ fixedPoints (zpowers x) (G ⧸ T))
          hinvF, Finset.card_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : q.out ∈ fixedPoints (zpowers x) (G ⧸ T) ↔ mp q.out = 1 := by
        rw [mem_fixedPoints_zpowers_iff, Function.minimalPeriod_eq_one_iff_isFixedPt]
        rfl
      by_cases hq : q.out ∈ fixedPoints (zpowers x) (G ⧸ T)
      · rw [if_pos hq, if_pos (hiff.mp hq), Nat.card_eq_fintype_card,
          (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mp hq]
      · rw [if_neg hq, if_neg (fun h => hq (hiff.mpr h))]
    rw [← hcount, Nat.odd_iff,
      show Nat.card (fixedPoints (zpowers x) (G ⧸ T)) % 2 = Nat.card (G ⧸ T) % 2 from hmod.symm]
    exact Nat.two_dvd_ne_zero.mp hTidx
  have hodd : Odd (Finset.univ.filter bad).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun q => mp q.out) (t := Nat.divisors (2 ^ N₀))
      (fun q _ => Nat.mem_divisors.mpr ⟨hmpdvd q.out, by positivity⟩),
      ← Finset.add_sum_erase _ _ (Nat.mem_divisors.mpr ⟨one_dvd _, by positivity⟩)]
    have h1 : (Finset.univ.filter bad).filter (fun q => mp q.out = 1) =
        Finset.univ.filter (fun q => mp q.out = 1) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      show q.out.out⁻¹ * x ^ mp q.out * q.out.out ∉ U
      rw [h, pow_one]
      exact hconj _
    rw [h1]
    refine hfix.add_even (even_iff_two_dvd.mpr (Finset.dvd_sum fun n hn => ?_))
    obtain ⟨hn1, hnd⟩ := Finset.mem_erase.mp hn
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.mem_divisors.mp hnd).1
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hn1 (pow_zero 2))
    rw [Finset.filter_filter]
    exact heven k hk
  have hτ1 : MonoidHom.transfer (phiQ T U) x ≠ 1 := by
    rw [hτ]
    obtain ⟨M, hM⟩ := hodd
    rw [hM, pow_succ, pow_mul, hg₀2, one_pow, one_mul]
    exact hg₀1
  set τ := MonoidHom.transfer (phiQ T U) with hτdef
  refine ⟨τ.ker, τ.normal_ker, ?_⟩
  rw [Subgroup.index_ker]
  have hdvd : Nat.card τ.range ∣ 2 := hQcard ▸ Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card τ.range ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro h
    have hx : τ x ∈ τ.range := ⟨x, rfl⟩
    rw [h, Subgroup.mem_bot] at hx
    exact hτ1 hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

end Main

end CFSG.ThompsonTransferCount
