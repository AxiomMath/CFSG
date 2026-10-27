module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

private theorem mem_of_pow_mem_of_coprime_index {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (x : G) {p : ℕ} (hcop : Nat.Coprime p K.index) (hxp : x ^ p ∈ K) : x ∈ K := by
  have h1 : (x : G ⧸ K) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hxp
  have h2 : (x : G ⧸ K) ^ K.index = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact K.pow_index_mem x
  have h3 : (x : G ⧸ K) ^ Nat.gcd p K.index = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  have hg : Nat.gcd p K.index = 1 := hcop
  rw [hg, pow_one] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

private theorem centralizer_le_normalizer {H : Type*} [Group H] (S : Subgroup H) :
    Subgroup.centralizer (S : Set H) ≤ (Subgroup.normalizer (S : Set H)) := by
  intro c hc
  have hc' : ∀ h ∈ S, h * c = c * h := fun h hh => Subgroup.mem_centralizer_iff.1 hc h hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hc' h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have h1 := hc' (c * h * c⁻¹) hh
    have e : c * h * c⁻¹ * c = c * h := by group
    rw [e] at h1
    rw [mul_left_cancel h1]
    exact hh

private theorem normal_centralizer_subgroupOf {H : Type*} [Group H] (S : Subgroup H) :
    ((Subgroup.centralizer (S : Set H)).subgroupOf (Subgroup.normalizer (S : Set H))).Normal := by
  refine ⟨fun k hk g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  have hc : ∀ s ∈ S, s * (k : H) = (k : H) * s := fun s hs =>
    Subgroup.mem_centralizer_iff.1 hk s hs
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hgs : (g : H)⁻¹ * s * (g : H) ∈ S := by
    have h1 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (S : Set H)).inv_mem g.2) s).1 hs
    rwa [inv_inv] at h1
  have hc' := hc _ hgs
  calc s * ((g : H) * (k : H) * (g : H)⁻¹)
      = (g : H) * (((g : H)⁻¹ * s * (g : H)) * (k : H)) * (g : H)⁻¹ := by group
    _ = (g : H) * ((k : H) * ((g : H)⁻¹ * s * (g : H))) * (g : H)⁻¹ := by rw [hc']
    _ = (g : H) * (k : H) * (g : H)⁻¹ * s := by group

private theorem normalizer_le_centralizer_of_pow {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (S : Subgroup H) (hSindex : ¬ p ∣ S.index) (hSC : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hpow : ∀ n ∈ (Subgroup.normalizer (S : Set H)), n ^ p ∈ Subgroup.centralizer (S : Set H)) :
    (Subgroup.normalizer (S : Set H)) ≤ Subgroup.centralizer (S : Set H) := by
  have hSC' : S ≤ Subgroup.centralizer (S : Set H) := fun s hs =>
    Subgroup.mem_centralizer_iff.2 fun t ht => hSC t ht s hs
  have h1 := Subgroup.relIndex_mul_relIndex S (Subgroup.centralizer (S : Set H)) (Subgroup.normalizer (S : Set H))
    hSC' (centralizer_le_normalizer S)
  have hSN : S ≤ (Subgroup.normalizer (S : Set H)) := Subgroup.le_normalizer
  have h2 := Subgroup.relIndex_mul_index hSN
  have hdvd : (Subgroup.centralizer (S : Set H)).relIndex (Subgroup.normalizer (S : Set H)) ∣ S.index :=
    dvd_trans (Dvd.intro_left _ h1) (Dvd.intro _ h2)
  have hcop : Nat.Coprime p ((Subgroup.centralizer (S : Set H)).subgroupOf (Subgroup.normalizer (S : Set H))).index :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hSindex (dvd_trans h hdvd)
  haveI := normal_centralizer_subgroupOf S
  intro n hn
  have hpn : (⟨n, hn⟩ : (Subgroup.normalizer (S : Set H))) ^ p ∈
      (Subgroup.centralizer (S : Set H)).subgroupOf (Subgroup.normalizer (S : Set H)) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hpow n hn
  exact Subgroup.mem_subgroupOf.1 (mem_of_pow_mem_of_coprime_index _ _ hcop hpn)

private theorem pow_mem_centralizer_of_normalizer {H : Type*} [Group H] (S : Subgroup H) {p : ℕ}
    (hp : 0 < p) (x : H) (hxS : x ∈ S) (hzp : Subgroup.zpowers x = S) (hordx : orderOf x = p ^ 2)
    (hSC : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hcomm : ∀ n ∈ (Subgroup.normalizer (S : Set H)), (n * x * n⁻¹ * x⁻¹) ^ p = 1) :
    ∀ n ∈ (Subgroup.normalizer (S : Set H)), n ^ p ∈ Subgroup.centralizer (S : Set H) := by
  intro n hn
  obtain ⟨z, hz⟩ : ∃ z : H, z = n * x * n⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hzS : z ∈ S := by
    rw [hz]
    exact S.mul_mem ((Subgroup.mem_normalizer_iff.1 hn x).1 hxS) (S.inv_mem hxS)
  have hzp' : z ^ p = 1 := by
    rw [hz]
    exact hcomm n hn
  have hzx : Commute z x := hSC z hzS x hxS
  have hnx : n * x * n⁻¹ = z * x := by
    rw [hz, inv_mul_cancel_right]
  have hzmem : z ∈ Subgroup.zpowers x := by
    rw [hzp]
    exact hzS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzmem
  have hkp : x ^ (k * (p : ℤ)) = 1 := by
    rw [zpow_mul, hk, zpow_natCast, hzp']
  have hpk : (p : ℤ) ∣ k := by
    have h1 : ((orderOf x : ℕ) : ℤ) ∣ k * (p : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 hkp
    rw [hordx] at h1
    have e : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) := by push_cast; ring
    rw [e] at h1
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne')).1 h1
  obtain ⟨j, hj⟩ := hpk
  have hzk : z ^ k = 1 := by
    rw [hj, zpow_mul, zpow_natCast, hzp', one_zpow]
  have hnz : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = n * x ^ k * n⁻¹ := by rw [hk]
      _ = (n * x * n⁻¹) ^ k := conj_zpow.symm
      _ = (z * x) ^ k := by rw [hnx]
      _ = z ^ k * x ^ k := hzx.mul_zpow k
      _ = z := by rw [hzk, hk, one_mul]
  have hnzc : n * z = z * n := by
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnz]
  have hφx : (MulAut.conj n) x = z * x := by
    rw [MulAut.conj_apply]
    exact hnx
  have hφz : (MulAut.conj n) z = z := by
    rw [MulAut.conj_apply]
    exact hnz
  have hind : ∀ m : ℕ, ((MulAut.conj n) ^ m) x = z ^ m * x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ' (MulAut.conj n) m, MulAut.mul_apply, ih, map_mul, map_pow, hφz, hφx,
        ← mul_assoc, ← pow_succ z m]
  have hcomm_p : Commute (n ^ p) x := by
    have h1 := hind p
    rw [hzp', one_mul] at h1
    rw [← map_pow (MulAut.conj : H →* MulAut H) n p, MulAut.conj_apply] at h1
    show n ^ p * x = x * n ^ p
    calc n ^ p * x = (n ^ p * x * (n ^ p)⁻¹) * n ^ p := by group
      _ = x * n ^ p := by rw [h1]
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : s ∈ Subgroup.zpowers x := by
    rw [hzp]
    exact hs
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs'
  exact ((hcomm_p.zpow_right m).eq).symm

private theorem exists_subgroup_card_eq_prime_le {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (I S : Subgroup H) [I.Normal] (hindex : I.index = p) (hScard : Nat.card S = p ^ 2)
    (x : H) (hxS : x ∈ S) (hxI : x ∉ I) :
    ∃ T : Subgroup H, T ≤ I ∧ T ≤ S ∧ Nat.card T = p := by
  let f : S →* H ⧸ I := (QuotientGroup.mk' I).comp S.subtype
  have hQ : Nat.card (H ⧸ I) = p := hindex
  have hidx : f.ker.index ∣ p := by
    rw [Subgroup.index_ker, ← hQ]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hne1 : f.ker.index ≠ 1 := by
    intro h1
    have htop : f.ker = ⊤ := Subgroup.index_eq_one.1 h1
    have hmem : (⟨x, hxS⟩ : S) ∈ f.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    have h2 : (x : H ⧸ I) = 1 := MonoidHom.mem_ker.1 hmem
    exact hxI ((QuotientGroup.eq_one_iff x).1 h2)
  have hkerp : f.ker.index = p := by
    rcases (Nat.dvd_prime hp).1 hidx with h | h
    · exact absurd h hne1
    · exact h
  have hkercard : Nat.card f.ker = p := by
    have h := Subgroup.card_mul_index (H := f.ker)
    rw [hkerp, hScard, sq] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  refine ⟨f.ker.map S.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    have h2 : ((s : H) : H ⧸ I) = 1 := MonoidHom.mem_ker.1 hs
    exact (QuotientGroup.eq_one_iff (s : H)).1 h2
  · rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hkercard

theorem false_of_prime_index_normal_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (I : Subgroup H) [I.Normal] (hI : I ≤ commutator H) (hindex : I.index = p)
    (hdvd : p ∣ Nat.card I) (hndvd : ¬ p ^ 2 ∣ Nat.card I)
    (hfix : ∀ S : Subgroup H, S ≤ I → Nat.card S = p → ∀ α : H, α ^ p = 1 →
      (∀ s ∈ S, α * s = s * α) → α ∈ I) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hHcard : Nat.card I * p = Nat.card H := by
    rw [← hindex]
    exact Subgroup.card_mul_index (H := I)
  have hdvd2 : p ^ 2 ∣ Nat.card H := by
    rw [← hHcard, sq]
    exact mul_dvd_mul_right hdvd p
  obtain ⟨S, hScard⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd2
  have hSindex : ¬ p ∣ S.index := by
    rintro ⟨c, hc⟩
    apply hndvd
    have h1 : Nat.card S * S.index = Nat.card H := Subgroup.card_mul_index (H := S)
    rw [hScard, hc, ← hHcard] at h1
    have h2 : Nat.card I * p = p ^ 2 * c * p := by
      rw [← h1]
      ring
    exact ⟨c, Nat.eq_of_mul_eq_mul_right hp.pos h2⟩
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hScard).is_comm.comm
        (⟨a, ha⟩ : S) ⟨b, hb⟩)
  obtain ⟨x, hxS, hxI⟩ : ∃ x ∈ S, x ∉ I := by
    by_contra hcon
    push_neg at hcon
    have h1 := Subgroup.card_dvd_of_le (show S ≤ I from fun y hy => hcon y hy)
    rw [hScard] at h1
    exact hndvd h1
  have hord_dvd : ∀ w ∈ S, orderOf w ∣ p ^ 2 := by
    intro w hw
    have h := orderOf_dvd_natCard (⟨w, hw⟩ : S)
    rw [hScard, Subgroup.orderOf_mk] at h
    exact h
  have hord_eq : ∀ w ∈ S, w ^ p ≠ 1 → orderOf w = p ^ 2 := by
    intro w hw hwp
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 (hord_dvd w hw)
    interval_cases i
    · exfalso
      apply hwp
      have h1 : w = 1 := orderOf_eq_one_iff.1 (by simpa using hi')
      rw [h1, one_pow]
    · exfalso
      apply hwp
      have h1 := pow_orderOf_eq_one w
      rw [hi', pow_one] at h1
      exact h1
    · exact hi'
  have hgen : ∀ w ∈ S, w ^ p ≠ 1 → Subgroup.zpowers w = S := by
    intro w hw hwp
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw) (le_of_eq ?_)
    rw [Nat.card_zpowers, hord_eq w hw hwp, hScard]
  have hL : ∀ w ∈ S, w ∈ I → w ^ p = 1 := by
    intro w hw hwI
    by_contra hne
    apply hxI
    have hxz : x ∈ Subgroup.zpowers w := by
      rw [hgen w hw hne]
      exact hxS
    exact Subgroup.zpowers_le.2 hwI hxz
  have hQcomm : ∀ a b : H ⧸ I, a * b = b * a := by
    have hQ : Nat.card (H ⧸ I) = p := hindex
    have hcyc : IsCyclic (H ⧸ I) := isCyclic_of_prime_card hQ
    have hcm : IsMulCommutative (H ⧸ I) := inferInstance
    exact fun a b => hcm.is_comm.comm a b
  have hcommN : ∀ n ∈ (Subgroup.normalizer (S : Set H)), (n * x * n⁻¹ * x⁻¹) ^ p = 1 := by
    intro n hn
    have hzS : n * x * n⁻¹ * x⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 hn x).1 hxS) (S.inv_mem hxS)
    have hzI : n * x * n⁻¹ * x⁻¹ ∈ I := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← commutatorElement_def]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hQcomm _ _)
    exact hL _ hzS hzI
  by_cases hxp : x ^ p = 1
  ·
    obtain ⟨T, hTI, hTS, hTcard⟩ :=
      exists_subgroup_card_eq_prime_le hp I S hindex hScard x hxS hxI
    exact hxI (hfix T hTI hTcard x hxp (fun s hs => hScomm x hxS s (hTS hs)))
  ·
    have hzp : Subgroup.zpowers x = S := hgen x hxS hxp
    have hordx : orderOf x = p ^ 2 := hord_eq x hxS hxp
    have hpow := pow_mem_centralizer_of_normalizer S hp.pos x hxS hzp hordx hScomm hcommN
    have hNC := normalizer_le_centralizer_of_pow hp S hSindex hScomm hpow
    let P : Sylow p H := (IsPGroup.of_card hScard).toSylow hSindex
    have hPS : (P : Subgroup H) = S := rfl
    have hNC' : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := hNC
    have hBurn := MonoidHom.not_dvd_card_ker_transferSylow P hNC'
    have hker : commutator H ≤ (MonoidHom.transferSylow P hNC').ker := by
      unfold commutator
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      apply Subtype.ext
      have ha : ((MonoidHom.transferSylow P hNC' g₁ : P) : H) ∈ S :=
        (MonoidHom.transferSylow P hNC' g₁).2
      have hb : ((MonoidHom.transferSylow P hNC' g₂ : P) : H) ∈ S :=
        (MonoidHom.transferSylow P hNC' g₂).2
      exact hScomm _ ha _ hb
    exact hBurn (hdvd.trans (Subgroup.card_dvd_of_le (hI.trans hker)))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
