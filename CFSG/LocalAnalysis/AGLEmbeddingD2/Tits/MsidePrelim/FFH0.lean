module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.Quasithin.Background.C1PackSolvP

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem sl2_unique_three (x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  revert x y hx3 hx1 hy3
  decide +revert

theorem sl2_comm_three (a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 := by
  revert a b ha3 ha1 hb2 hb1
  decide +revert

theorem sl2_exists_three : ∃ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ^ 3 = 1 ∧ a ≠ 1 := by
  decide

section NaturalL2

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem exists_three_of_actsAsNaturalL2 (h : ActsAsNaturalL2 L U) :
    ∃ ℓ ∈ L, ℓ ^ 3 = 1 ∧ ℓ ≠ 1 := by
  obtain ⟨e, -, -⟩ := h
  obtain ⟨a, ha3, ha1⟩ := sl2_exists_three
  refine ⟨(e.symm a : L), (e.symm a).2, ?_, ?_⟩
  · have h3 : (e.symm a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have := congrArg Subtype.val h3
    simpa using this
  · intro h1
    apply ha1
    have h2 : e.symm a = 1 := Subtype.ext h1
    have := congrArg e h2
    simpa using this

theorem mem_zpowers_of_actsAsNaturalL2 (h : ActsAsNaturalL2 L U) {x y : MulAut W}
    (hx : x ∈ L) (hy : y ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers x := by
  obtain ⟨e, -, -⟩ := h
  have ha3 : (e ⟨x, hx⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨x, hx⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hx3), map_one]
  have ha1 : e ⟨x, hx⟩ ≠ 1 := fun h1 => hx1 (by
    have := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val this)
  have hb3 : (e ⟨y, hy⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨y, hy⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hy3), map_one]
  rcases sl2_unique_three _ _ ha3 ha1 hb3 with h1 | h1 | h1
  · have := e.injective (h1.trans (map_one e).symm)
    have hy1 : y = 1 := by simpa using congrArg Subtype.val this
    rw [hy1]
    exact Subgroup.one_mem _
  · have := e.injective h1
    have hyx : y = x := by simpa using congrArg Subtype.val this
    rw [hyx]
    exact Subgroup.mem_zpowers x
  · have := e.injective (h1.trans (map_pow e _ 2).symm)
    have hyx : y = x ^ 2 := by simpa using congrArg Subtype.val this
    rw [hyx]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2

theorem comm_three_of_actsAsNaturalL2 (h : ActsAsNaturalL2 L U) {a b : MulAut W} (ha : a ∈ L)
    (hb : b ∈ L) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 := by
  obtain ⟨e, -, -⟩ := h
  have ha3' : (e ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨a, ha⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using ha3), map_one]
  have ha1' : e ⟨a, ha⟩ ≠ 1 := fun h1 => ha1 (by
    have := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val this)
  have hb2' : (e ⟨b, hb⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨b, hb⟩ : ↥L) ^ 2 = 1 from Subtype.ext (by simpa using hb2), map_one]
  have hb1' : e ⟨b, hb⟩ ≠ 1 := fun h1 => hb1 (by
    have := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val this)
  obtain ⟨hc3, hc1⟩ := sl2_comm_three _ _ ha3' ha1' hb2' hb1'
  set c : ↥L := ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹ with hc
  have hec : e c = e ⟨a, ha⟩ * e ⟨b, hb⟩ * (e ⟨a, ha⟩)⁻¹ * (e ⟨b, hb⟩)⁻¹ := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcv : (c : MulAut W) = a * b * a⁻¹ * b⁻¹ := by simp [hc]
  refine ⟨?_, ?_⟩
  · have h3 : c ^ 3 = 1 := e.injective (by rw [map_pow, hec, hc3, map_one])
    rw [← hcv]
    simpa using congrArg Subtype.val h3
  · intro h1
    apply hc1
    have h2 : c = 1 := Subtype.ext (by rw [hcv]; exact h1)
    rw [← hec, h2, map_one]

end NaturalL2

section IndexThree

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem eq_one_of_pow_three_of_isPGroup {A : Subgroup Ω} (hA : IsPGroup 2 A) {x : Ω} (hx : x ∈ A)
    (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  rw [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem relIndex_sup_eq_three {L A : Subgroup Ω} (hAN : A ≤ Subgroup.normalizer (L : Set Ω))
    (hA : IsPGroup 2 A) (hL : Nat.card L = 6) {τ : Ω} (hτL : τ ∈ L) (hτA : τ ∈ A) (hτ : τ ≠ 1) :
    A.relIndex (L ⊔ A) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := B6.relIndex_inf_eq_relIndex_sup hAN
  rw [sup_comm, ← h1]
  have h2 : IsPGroup 2 (A ⊓ L : Subgroup Ω) := hA.to_le inf_le_left
  have hdvd : Nat.card (A ⊓ L : Subgroup Ω) ∣ 6 := hL ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hne : Nat.card (A ⊓ L : Subgroup Ω) ≠ 1 := by
    intro h1'
    rw [Subgroup.card_eq_one] at h1'
    have hmem : τ ∈ (A ⊓ L : Subgroup Ω) := ⟨hτA, hτL⟩
    rw [h1'] at hmem
    exact hτ (Subgroup.mem_bot.mp hmem)
  have hcard : Nat.card (A ⊓ L : Subgroup Ω) = 2 := by
    rw [hn] at hdvd hne ⊢
    have hle : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hn3 : n < 3 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases n <;> simp_all
  have := Subgroup.relIndex_mul_card (A ⊓ L) L
  rw [inf_of_le_left inf_le_right, hcard, hL] at this
  omega

omit [Finite Ω] in
theorem eq_or_eq_of_relIndex_eq_three {A Z Y : Subgroup Ω} (h3 : A.relIndex Y = 3) (hAZ : A ≤ Z)
    (hZY : Z ≤ Y) : Z = A ∨ Z = Y := by
  have h := Subgroup.relIndex_mul_relIndex A Z Y hAZ hZY
  rw [h3] at h
  have hd : A.relIndex Z ∣ 3 := ⟨_, h.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hAZ)
  · rw [h1] at h
    have h2 : Z.relIndex Y = 1 := by omega
    exact Or.inr (le_antisymm hZY (Subgroup.relIndex_eq_one.1 h2))

omit [Finite Ω] in
theorem isSylowTwoOf_of_relIndex_eq_three {A Y : Subgroup Ω} (hAY : A ≤ Y) (hA : IsPGroup 2 A)
    (h3 : A.relIndex Y = 3) : IsSylowTwoOf A Y := by
  refine ⟨hAY, hA, ?_⟩
  show ¬ 2 ∣ A.relIndex Y
  rw [h3]
  norm_num

theorem eq_of_isPGroup_of_relIndex_eq_three {A Z Y : Subgroup Ω} (h3 : A.relIndex Y = 3)
    (hAZ : A ≤ Z) (hZY : Z ≤ Y) (hZ : IsPGroup 2 Z) : Z = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_eq_of_relIndex_eq_three h3 hAZ hZY with h | h
  · exact h
  · exfalso
    subst h
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    have := Subgroup.relIndex_mul_card A Z
    rw [inf_of_le_left hAZ, h3, hn] at this
    have h3d : 3 ∣ 2 ^ n := ⟨_, this.symm⟩
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)
    omega

omit [Finite Ω] in
theorem card_eq_two_of_dvd_six {P : Subgroup Ω} (hP : IsPGroup 2 P) (hdvd : Nat.card P ∣ 6)
    (hne : P ≠ ⊥) : Nat.card P = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := by
    refine Nat.finite_of_card_ne_zero ?_
    intro h0
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by norm_num)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hne1 : Nat.card P ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.1 h1)
  rw [hn] at hdvd hne1 ⊢
  have hle : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hn3 : n < 3 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    omega
  interval_cases n <;> simp_all

omit [Finite Ω] in
theorem mem_of_pow_mem_of_coprime {H : Subgroup Ω} {x : Ω} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ H) (hb : x ^ b = 1) : x ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have e : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← zpow_add, mul_comm (a : ℤ) u, mul_comm (b : ℤ) v, huv, zpow_one]
  rw [e, hb, one_zpow, mul_one]
  exact H.zpow_mem ha u

end IndexThree

section CyclicQuotient

variable {Ω : Type*} [Group Ω] {W P₀ : Subgroup Ω} [(P₀.subgroupOf W).Normal]

theorem isCyclic_quotient_of_eq {z : Ω} (hzW : z ∈ W)
    (hzP₀ : Subgroup.zpowers z ≤ Subgroup.normalizer (P₀ : Set Ω))
    (hW : W = Subgroup.zpowers z ⊔ P₀) : IsCyclic (↥W ⧸ P₀.subgroupOf W) := by
  refine ⟨QuotientGroup.mk ⟨z, hzW⟩, fun q => ?_⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : (w : Ω) ∈ ((Subgroup.zpowers z ⊔ P₀ : Subgroup Ω) : Set Ω) := by
    rw [← hW]
    exact w.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzP₀] at hw
  obtain ⟨x, hx, d, hd, hxd⟩ := hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : ((((⟨z, hzW⟩ : W) ^ n)⁻¹ * w : W) : Ω) = (z ^ n)⁻¹ * (w : Ω) := by simp
  rw [e, ← hxd]
  simpa using hd

theorem isCyclic_of_inf_eq_bot [IsCyclic (↥W ⧸ P₀.subgroupOf W)] {P : Subgroup Ω} (hPW : P ≤ W)
    (hPP₀ : P ⊓ P₀ = ⊥) : IsCyclic P := by
  let φ : ↥P →* ↥W ⧸ P₀.subgroupOf W := (QuotientGroup.mk' _).comp (Subgroup.inclusion hPW)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : Subgroup.inclusion hPW x ∈ P₀.subgroupOf W := (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at hx'
    have hmem : (x : Ω) ∈ P ⊓ P₀ := ⟨x.2, hx'⟩
    rw [hPP₀, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact (MulEquiv.isCyclic (MonoidHom.ofInjective hinj)).2 inferInstance

theorem mem_zpowers_sup_of_not_mem {z w : Ω} (hzW : z ∈ W) (hwW : w ∈ W)
    (hzP₀ : Subgroup.zpowers z ≤ Subgroup.normalizer (P₀ : Set Ω))
    (hW : W = Subgroup.zpowers z ⊔ P₀) {N₀ : Subgroup Ω} (hP₀N₀ : P₀ ≤ N₀) (hz3N : z ^ 3 ∈ N₀)
    {a : ℕ} (hz3a : z ^ 3 ^ a ∈ P₀) (hwN : w ∉ N₀) : z ∈ Subgroup.zpowers w ⊔ P₀ := by
  have hP₀W : P₀ ≤ W := hW ▸ le_sup_right
  have hw : w ∈ ((Subgroup.zpowers z ⊔ P₀ : Subgroup Ω) : Set Ω) := by
    rw [← hW]
    exact hwW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzP₀] at hw
  obtain ⟨x, hx, d, hd, hxd⟩ := hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hi : ¬ (3 : ℤ) ∣ i := by
    rintro ⟨m, rfl⟩
    apply hwN
    rw [← hxd]
    refine N₀.mul_mem ?_ (hP₀N₀ hd)
    rw [_root_.zpow_mul]
    exact N₀.zpow_mem (by exact_mod_cast hz3N) m
  obtain ⟨u, v, huv⟩ :=
    (((Prime.coprime_iff_not_dvd Int.prime_three).2 hi).symm.pow_right (n := a))
  set zq : ↥W ⧸ P₀.subgroupOf W := QuotientGroup.mk ⟨z, hzW⟩ with hzq
  set wq : ↥W ⧸ P₀.subgroupOf W := QuotientGroup.mk ⟨w, hwW⟩ with hwq
  have hd1 : (QuotientGroup.mk ⟨d, hP₀W hd⟩ : ↥W ⧸ P₀.subgroupOf W) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hd)
  have hwi : wq = zq ^ i := by
    rw [hwq, hzq, ← QuotientGroup.mk_zpow]
    have e : (⟨w, hwW⟩ : W) = (⟨z, hzW⟩ : W) ^ i * ⟨d, hP₀W hd⟩ := Subtype.ext (by simp [hxd])
    rw [e, QuotientGroup.mk_mul, hd1, mul_one]
  have hz1 : zq ^ ((3 : ℤ) ^ a) = 1 := by
    rw [hzq, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have e : ((((⟨z, hzW⟩ : W) ^ ((3 : ℤ) ^ a)) : W) : Ω) = z ^ 3 ^ a := by
      rw [Subgroup.coe_zpow]
      exact_mod_cast (zpow_natCast z (3 ^ a))
    rw [e]
    exact hz3a
  have hzw : zq = wq ^ u := by
    calc zq = zq ^ (u * i + v * (3 : ℤ) ^ a) := by rw [huv, zpow_one]
      _ = (zq ^ i) ^ u * (zq ^ ((3 : ℤ) ^ a)) ^ v := by
        rw [zpow_add, mul_comm u i, mul_comm v, _root_.zpow_mul, _root_.zpow_mul]
      _ = wq ^ u := by rw [hz1, one_zpow, mul_one, hwi]
  rw [hzq, hwq, ← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hzw
  have hzw' : z⁻¹ * w ^ u ∈ P₀ := by simpa using hzw
  have e : z = w ^ u * (z⁻¹ * w ^ u)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) u) (P₀.inv_mem hzw')

end CyclicQuotient

section Preimage

variable {G : Type} [Group G] {M V : Subgroup G} {hU : IsElemAbelian 2 V}
  (hMN : M ≤ Subgroup.normalizer (V : Set G))

theorem mem_preAutM_iff_convI {Λ : Subgroup (MulAut (IntMod V hU))} {g : G} (hg : g ∈ M) :
    g ∈ preAutM hU hMN Λ ↔ convI hU ⟨g, hMN hg⟩ ∈ Λ := by
  rw [mem_preAutM]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hg, h⟩⟩

theorem autI_preAutM_le (Λ : Subgroup (MulAut (IntMod V hU))) :
    autI hU (preAutM hU hMN Λ) ≤ Λ := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
  obtain ⟨_, hgΛ⟩ := (mem_preAutM hU hMN).1 hg
  exact hgΛ

theorem le_preAutM_of_autI_le {K : Subgroup G} (hKM : K ≤ M) {Λ : Subgroup (MulAut (IntMod V hU))}
    (hK : autI hU K ≤ Λ) : K ≤ preAutM hU hMN Λ := fun _ hg =>
  (mem_preAutM_iff_convI hMN (hKM hg)).2 (hK (convI_mem_autI hU hg (hMN (hKM hg))))

end Preimage

structure FFH0Hyp {G : Type} [Group G] [Finite G] (M T V : Subgroup G) (hU : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hU)))) (L : Subgroup (MulAut (IntMod V hU))) :
    Prop where
  charTwo : CharTwo M
  sylow : IsSylowTwoOf T M
  le_center : V ≤ pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G)
  fam : S3Family I
  card : ∀ L' ∈ I, Nat.card L' = 6
  thompsonJ_eq : autI hU (thompsonJ M) = ⨆ L' ∈ I, L'
  sylow_thompsonJ : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M))
  perm : ∀ g ∈ autI hU M, ∀ L' ∈ I, B1.conjAut g L' ∈ I
  mem : L ∈ I

namespace FFH0Hyp

variable {G : Type} [Group G] [Finite G] {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} {L : Subgroup (MulAut (IntMod V hU))}
  (h : FFH0Hyp M T V hU I L)
include h

theorem V_le : V ≤ T :=
  h.le_center.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow))

theorem V_le_pCoreOf : V ≤ pCoreOf 2 M := h.le_center.trans inf_le_left

theorem pCoreOf_le_centralizer : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) := fun q hq =>
  Subgroup.mem_centralizer_iff.2 fun _ hv =>
    (Subgroup.mem_centralizer_iff.1 (h.le_center hv).2 q hq).symm

theorem baum_le_M : baum T ≤ M := (inf_le_left : baum T ≤ T).trans h.sylow.1

theorem L_le : L ≤ autI hU (thompsonJ M) := by
  rw [h.thompsonJ_eq]
  exact le_iSup₂_of_le L h.mem le_rfl

theorem iSup_le_normalizer :
    (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases hLL : L' = L
  · subst hLL
    exact Subgroup.le_normalizer
  · exact E2.le_normalizer_of_commute fun a ha b hb => h.fam.comm L' hL' L h.mem hLL a ha b hb

theorem autI_baum_le (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    autI hU (baum T) ≤ autI hU (thompsonJ M) :=
  autI_baum_le_autI_thompsonJ hMN h.sylow h.V_le h.fam h.thompsonJ_eq
    (thompsonJ_le_thompsonJ_of_isSylowTwoOf h.sylow) h.perm

theorem autI_baum_le_normalizer (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    autI hU (baum T) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) :=
  ((h.autI_baum_le hMN).trans h.thompsonJ_eq.le).trans h.iSup_le_normalizer

theorem isPGroup_autI_baum : IsPGroup 2 (autI hU (baum T)) :=
  isPGroup_autI hU (h.sylow.2.1.to_le (inf_le_left : baum T ≤ T))

theorem sup_le_autI : L ⊔ autI hU (baum T) ≤ autI hU M :=
  sup_le (h.L_le.trans (autI_mono hU (thompsonJ_le_self M))) (autI_mono hU h.baum_le_M)

theorem exists_tau : ∃ τ ∈ L, τ ∈ autI hU (thompsonJ T) ∧ τ ^ 2 = 1 ∧ τ ≠ 1 := by
  have hLN : autI hU (thompsonJ M) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) :=
    h.thompsonJ_eq.le.trans h.iSup_le_normalizer
  have hP := B6.isSylowTwoOf_inf_normal h.sylow_thompsonJ h.L_le hLN
  set P := autI hU (thompsonJ T) ⊓ L with hPdef
  have hL6 := h.card L h.mem
  have hne : P ≠ ⊥ := by
    intro hbot
    apply hP.2.2
    show 2 ∣ P.relIndex L
    rw [hbot, Subgroup.relIndex_bot_left, hL6]
    norm_num
  have hcard : Nat.card P = 2 :=
    card_eq_two_of_dvd_six hP.2.1 (hL6 ▸ Subgroup.card_dvd_of_le inf_le_right) hne
  obtain ⟨⟨τ, hτP⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have h2 : τ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := P) (x := ⟨τ, hτP⟩)
    rw [hcard] at this
    simpa using congrArg Subtype.val this
  exact ⟨τ, hτP.2, hτP.1, h2, fun h1 => hτ1 (Subtype.ext h1)⟩

theorem relIndex_eq_three (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    (autI hU (baum T)).relIndex (L ⊔ autI hU (baum T)) = 3 := by
  obtain ⟨τ, hτL, hτJ, -, hτ1⟩ := h.exists_tau
  exact relIndex_sup_eq_three (h.autI_baum_le_normalizer hMN) h.isPGroup_autI_baum
    (h.card L h.mem) hτL (autI_mono hU (B6.thompsonJ_le_baum T) hτJ) hτ1

theorem isSylowTwoOf_autI_baum (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    IsSylowTwoOf (autI hU (baum T)) (L ⊔ autI hU (baum T)) :=
  isSylowTwoOf_of_relIndex_eq_three le_sup_right h.isPGroup_autI_baum (h.relIndex_eq_three hMN)

theorem exists_ell : ∃ ℓ ∈ L, ℓ ^ 3 = 1 ∧ ℓ ≠ 1 :=
  exists_three_of_actsAsNaturalL2 (h.fam.nat L h.mem)

variable (hMN : M ≤ Subgroup.normalizer (V : Set G))
include hMN

theorem baum_le_preAutM : baum T ≤ preAutM hU hMN (autI hU (baum T)) :=
  le_preAutM_of_autI_le hMN h.baum_le_M le_rfl

theorem baum_le_inf : baum T ≤ T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) :=
  le_inf inf_le_left (le_preAutM_of_autI_le hMN h.baum_le_M le_sup_right)

theorem autI_inf_eq :
    autI hU (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) = autI hU (baum T) :=
  eq_of_isPGroup_of_relIndex_eq_three (h.relIndex_eq_three hMN) (autI_mono hU (h.baum_le_inf hMN))
    ((autI_mono hU inf_le_right).trans (autI_preAutM_le hMN _))
    (isPGroup_autI hU (h.sylow.2.1.to_le inf_le_left))

theorem inf_le_preAutM :
    T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ preAutM hU hMN (autI hU (baum T)) :=
  le_preAutM_of_autI_le hMN (inf_le_left.trans h.sylow.1) (h.autI_inf_eq hMN).le

theorem isSylowTwoOf_inf :
    IsSylowTwoOf (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)))
      (preAutM hU hMN (L ⊔ autI hU (baum T))) := by
  set X := preAutM hU hMN (L ⊔ autI hU (baum T)) with hX
  have hXM : X ≤ M := preAutM_le hU hMN _
  have hCX : Subgroup.centralizer (V : Set G) ⊓ M ≤ X := centralizer_inf_le_preAutM hU hMN _
  refine B2F.isSylowTwoOf_of_isSylowTwoOf_autI hU (hXM.trans hMN) inf_le_right
    (h.sylow.2.1.to_le inf_le_left) ?_ ?_
  · have e1 : X ⊓ Subgroup.centralizer (V : Set G) = Subgroup.centralizer (V : Set G) ⊓ M := by
      apply le_antisymm
      · exact fun x hx => ⟨hx.2, hXM hx.1⟩
      · exact fun x hx => ⟨hCX hx, hx.1⟩
    have e2 : (T ⊓ X) ⊓ Subgroup.centralizer (V : Set G) =
        T ⊓ (Subgroup.centralizer (V : Set G) ⊓ M) := by
      apply le_antisymm
      · exact fun x hx => ⟨hx.1.1, hx.2, h.sylow.1 hx.1.1⟩
      · exact fun x hx => ⟨⟨hx.1, hCX hx.2⟩, hx.2.1⟩
    rw [e1, e2]
    exact B6.isSylowTwoOf_inf_normal h.sylow inf_le_right
      (B2F.le_normalizer_inf (B2F.le_normalizer_centralizer hMN) Subgroup.le_normalizer)
  · rw [h.autI_inf_eq hMN]
    exact B6.isSylowTwoOf_mono (h.isSylowTwoOf_autI_baum hMN)
      (autI_mono hU ((h.baum_le_inf hMN).trans inf_le_right)) (autI_preAutM_le hMN _)

theorem pCoreOf_le_inf : pCoreOf 2 M ≤ T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) :=
  le_inf (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow) fun _ hq =>
    centralizer_inf_le_preAutM hU hMN _
      ⟨h.pCoreOf_le_centralizer hq, CFSG.LieType.BorelTits.pCoreOf_le 2 M hq⟩

theorem baum_inf : baum (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) = baum T :=
  (baum_eq_of_le (h.baum_le_inf hMN) inf_le_left).symm

theorem not_preAutM_le :
    ¬ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ preAutM hU hMN (autI hU (baum T)) := by
  intro hle
  obtain ⟨ℓ, hℓL, hℓ3, hℓ1⟩ := h.exists_ell
  obtain ⟨g, hgM, hgℓ⟩ := (mem_autI hU).1 (h.sup_le_autI (le_sup_left (b := autI hU (baum T)) hℓL))
  have hgX : (g : G) ∈ preAutM hU hMN (L ⊔ autI hU (baum T)) := by
    refine (mem_preAutM_iff_convI hMN hgM).2 ?_
    rw [show (⟨(g : G), hMN hgM⟩ : Subgroup.normalizer (V : Set G)) = g from rfl, hgℓ]
    exact le_sup_left (b := autI hU (baum T)) hℓL
  have hgA := (mem_preAutM_iff_convI hMN hgM).1 (hle hgX)
  rw [show (⟨(g : G), hMN hgM⟩ : Subgroup.normalizer (V : Set G)) = g from rfl, hgℓ] at hgA
  exact hℓ1 (eq_one_of_pow_three_of_isPGroup h.isPGroup_autI_baum hgA hℓ3)

end FFH0Hyp

section ConvI

variable {G : Type} [Group G] {V : Subgroup G} {hU : IsElemAbelian 2 V}

theorem convI_conj {g y : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G))
    (h' : g * y * g⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    convI hU ⟨g * y * g⁻¹, h'⟩ = convI hU ⟨g, hg⟩ * convI hU ⟨y, hy⟩ * (convI hU ⟨g, hg⟩)⁻¹ := by
  rw [show (⟨g * y * g⁻¹, h'⟩ : Subgroup.normalizer (V : Set G)) =
    ⟨g, hg⟩ * ⟨y, hy⟩ * (⟨g, hg⟩ : Subgroup.normalizer (V : Set G))⁻¹ from rfl]
  simp only [map_mul, map_inv]

theorem le_normalizer_inf_preAutM {M K : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hKM : K ≤ M) {Λ' : Subgroup (MulAut (IntMod V hU))}
    (hΛ' : autI hU K ≤ Subgroup.normalizer (Λ' : Set (MulAut (IntMod V hU)))) :
    K ≤ Subgroup.normalizer ((K ⊓ preAutM hU hMN Λ' : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, ∀ y ∈ K ⊓ preAutM hU hMN Λ', k * y * k⁻¹ ∈ K ⊓ preAutM hU hMN Λ' := by
    intro k hk y hy
    have hkyM : k * y * k⁻¹ ∈ M := hKM (K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk))
    refine ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk), ?_⟩
    show k * y * k⁻¹ ∈ preAutM hU hMN Λ'
    rw [mem_preAutM_iff_convI hMN hkyM, convI_conj (hMN (hKM hk)) (hMN (hKM hy.1))]
    have hyΛ := (mem_preAutM_iff_convI hMN (hKM hy.1)).1 hy.2
    have hkN := hΛ' (convI_mem_autI hU hk (hMN (hKM hk)))
    exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hyΛ
  intro k hk
  refine B6.mem_normalizer_of_forall_mem (fun y hy => key k hk y hy) (fun y hy => ?_)
  simpa using key k⁻¹ (K.inv_mem hk) y hy

end ConvI

namespace FFH0Hyp

variable {G : Type} [Group G] [Finite G] {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} {L : Subgroup (MulAut (IntMod V hU))}
  (h : FFH0Hyp M T V hU I L)
include h

theorem sup_le_normalizer_zpowers (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {ℓ : MulAut (IntMod V hU)}
    (hℓL : ℓ ∈ L) (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1) :
    L ⊔ autI hU (baum T) ≤
      Subgroup.normalizer (Subgroup.zpowers ℓ : Set (MulAut (IntMod V hU))) := by
  have key : ∀ x ∈ L ⊔ autI hU (baum T), x * ℓ * x⁻¹ ∈ Subgroup.zpowers ℓ := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) :=
      sup_le Subgroup.le_normalizer (h.autI_baum_le_normalizer hMN) hx
    have hmem : x * ℓ * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN ℓ).mp hℓL
    have h3 : (x * ℓ * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hℓ3]; group
    exact mem_zpowers_of_actsAsNaturalL2 (h.fam.nat L h.mem) hℓL hmem hℓ3 hℓ1 h3
  intro x hx
  refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (key x hx) n
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 := key x⁻¹ (Subgroup.inv_mem _ hx)
    have e : x⁻¹ * ℓ ^ n * x = (x⁻¹ * ℓ * x⁻¹⁻¹) ^ n := by rw [conj_zpow, inv_inv]
    rw [e]
    exact Subgroup.zpow_mem _ h1 n

theorem zpowers_inf_eq_bot {ℓ : MulAut (IntMod V hU)} (hℓ3 : ℓ ^ 3 = 1) :
    Subgroup.zpowers ℓ ⊓ autI hU (baum T) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
  have h3 : (ℓ ^ n) ^ 3 = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hℓ3, one_zpow]
  exact Subgroup.mem_bot.mpr (eq_one_of_pow_three_of_isPGroup h.isPGroup_autI_baum hx.2 h3)

end FFH0Hyp

structure IsFFH0Min {G : Type} [Group G] (M T V : Subgroup G) {hU : IsElemAbelian 2 V}
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (L : Subgroup (MulAut (IntMod V hU)))
    (K : Subgroup G) : Prop where
  le : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ K
  le_X : K ≤ preAutM hU hMN (L ⊔ autI hU (baum T))
  not_le : ¬ K ≤ preAutM hU hMN (autI hU (baum T))
  min : ∀ P' : Subgroup G, T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ P' → P' < K →
    P' ≤ preAutM hU hMN (autI hU (baum T))

namespace IsFFH0Min

variable {G : Type} [Group G] [Finite G] {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} {L : Subgroup (MulAut (IntMod V hU))}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)} {K : Subgroup G}
  (hK : IsFFH0Min M T V hMN L K)
include hK

omit [Finite G] in
theorem le_M : K ≤ M := hK.le_X.trans (preAutM_le hU hMN _)

omit [Finite G] in
theorem le_normalizer_V : K ≤ Subgroup.normalizer (V : Set G) := hK.le_M.trans hMN

omit [Finite G] in
theorem eq_of_not_le {P' : Subgroup G} (hSP' : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ P')
    (hP'K : P' ≤ K) (hP' : ¬ P' ≤ preAutM hU hMN (autI hU (baum T))) : P' = K := by
  by_contra hne
  exact hP' (hK.min P' hSP' (lt_of_le_of_ne hP'K hne))

variable (h : FFH0Hyp M T V hU I L)
include h

omit hK in
theorem inf_centralizer_le :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) :=
  fun _ hx => ⟨hx.1, centralizer_inf_le_preAutM hU hMN _ ⟨hx.2, h.sylow.1 hx.1⟩⟩

theorem isSylowTwoOf : IsSylowTwoOf (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) K :=
  B6.isSylowTwoOf_mono (h.isSylowTwoOf_inf hMN) hK.le hK.le_X

theorem pCoreOf_le : pCoreOf 2 M ≤ K := (h.pCoreOf_le_inf hMN).trans hK.le

theorem baum_le : baum T ≤ K := (h.baum_le_inf hMN).trans hK.le

theorem charTwo : CharTwo K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQK : pCoreOf 2 M ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hK.pCoreOf_le h)
      (hK.le_M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  intro x hx
  exact hQK (h.charTwo ⟨hK.le_M hx.1, Subgroup.centralizer_le hQK hx.2⟩)

theorem autI_eq : autI hU K = L ⊔ autI hU (baum T) := by
  rcases eq_or_eq_of_relIndex_eq_three (h.relIndex_eq_three hMN) (autI_mono hU (hK.baum_le h))
    ((autI_mono hU hK.le_X).trans (autI_preAutM_le hMN _)) with h1 | h1
  · exact absurd (le_preAutM_of_autI_le hMN hK.le_M h1.le) hK.not_le
  · exact h1

omit [Finite G] h in
theorem le_normalizer_inf_centralizer :
    K ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hK.le_normalizer_V)

theorem isSylowTwoOf_inf_centralizer :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) (K ⊓ Subgroup.centralizer (V : Set G)) := by
  have hsyl := B6.isSylowTwoOf_inf_normal (hK.isSylowTwoOf h) inf_le_left
    hK.le_normalizer_inf_centralizer
  have e : (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) ⊓ (K ⊓ Subgroup.centralizer (V : Set G)) =
      T ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2.2⟩
    · exact fun x hx => ⟨inf_centralizer_le h hx, hK.le (inf_centralizer_le h hx), hx.2⟩
  rwa [e] at hsyl

theorem le_normalizer_P₀ :
    K ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  set P₀ := T ⊓ Subgroup.centralizer (V : Set G) with hP₀
  have hF := B6.frattini_two inf_le_left hK.le_normalizer_inf_centralizer
    (hK.isSylowTwoOf_inf_centralizer h)
  have hSN : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤
      K ⊓ Subgroup.normalizer (P₀ : Set G) :=
    le_inf hK.le (B2F.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (B2F.le_normalizer_centralizer (inf_le_left.trans (h.sylow.1.trans hMN))))
  by_cases hle : K ⊓ Subgroup.normalizer (P₀ : Set G) ≤ preAutM hU hMN (autI hU (baum T))
  · exfalso
    apply hK.not_le
    refine hF.trans (sup_le ?_ hle)
    exact fun x hx => centralizer_inf_le_preAutM hU hMN _ ⟨hx.2, hK.le_M hx.1⟩
  · rw [← hK.eq_of_not_le hSN inf_le_left hle]
    exact inf_le_right

section Ell

variable {ℓ : MulAut (IntMod V hU)} (hℓL : ℓ ∈ L) (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1)
include hℓL hℓ3 hℓ1

theorem le_normalizer_W :
    K ≤ Subgroup.normalizer
      ((K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) : Subgroup G) : Set G) :=
  le_normalizer_inf_preAutM hMN hK.le_M
    ((hK.autI_eq h).le.trans (h.sup_le_normalizer_zpowers hMN hℓL hℓ3 hℓ1))

omit hℓ3 hℓ1 in
theorem autI_W : autI hU (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ)) = Subgroup.zpowers ℓ := by
  refine le_antisymm ((autI_mono hU inf_le_right).trans (autI_preAutM_le hMN _)) ?_
  rw [Subgroup.zpowers_le]
  have hℓK : ℓ ∈ autI hU K := by
    rw [hK.autI_eq h]
    exact le_sup_left (b := autI hU (baum T)) hℓL
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hU).1 hℓK
  refine (mem_autI hU).2 ⟨k, ⟨hkK, ?_⟩, rfl⟩
  exact (mem_preAutM_iff_convI hMN (hK.le_M hkK)).2 (Subgroup.mem_zpowers _)

omit [Finite G] h hℓL hℓ3 hℓ1 in
theorem inf_centralizer_le_W :
    K ⊓ Subgroup.centralizer (V : Set G) ≤ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) :=
  fun _ hx => ⟨hx.1, centralizer_inf_le_preAutM hU hMN _ ⟨hx.2, hK.le_M hx.1⟩⟩

theorem relIndex_W :
    (K ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) with hW
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hK.le_normalizer_V
  have e1 := card_autI_mul_card_inf hU hWN
  have e2 : W ⊓ Subgroup.centralizer (V : Set G) = K ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2⟩
    · exact fun x hx => ⟨hK.inf_centralizer_le_W hx, hx.2⟩
  rw [e2, hK.autI_W h hℓL, Nat.card_zpowers, orderOf_eq_prime hℓ3 hℓ1] at e1
  have e3 := Subgroup.relIndex_mul_card (K ⊓ Subgroup.centralizer (V : Set G)) W
  rw [inf_of_le_left (hK.inf_centralizer_le_W)] at e3
  have hpos : 0 < Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have : (K ⊓ Subgroup.centralizer (V : Set G)).relIndex W *
      Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) =
      3 * Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) := by rw [e3, e1]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem odd_relIndex_W :
    ¬ 2 ∣ (T ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ)) := by
  have hP₀N₀ : T ⊓ Subgroup.centralizer (V : Set G) ≤ K ⊓ Subgroup.centralizer (V : Set G) :=
    (hK.isSylowTwoOf_inf_centralizer h).1
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hP₀N₀ hK.inf_centralizer_le_W,
    hK.relIndex_W h hℓL hℓ3 hℓ1]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h2 | h2
  · exact (hK.isSylowTwoOf_inf_centralizer h).2.2 h2
  · omega

end Ell

theorem not_thompsonJ_le :
    ¬ thompsonJ (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) ≤
      Subgroup.centralizer (VZ (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) K : Set G) := by
  intro hle
  set S := T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) with hS
  set V₁ := VZ S K with hV₁
  have hJS : thompsonJ S = thompsonJ T :=
    B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum T).trans (h.baum_le_inf hMN)) inf_le_left
  obtain ⟨τ, hτL, hτJ, hτ2, hτ1⟩ := h.exists_tau
  obtain ⟨ℓ, hℓL, hℓ3, hℓ1⟩ := h.exists_ell
  obtain ⟨t, htJ, rfl⟩ := (mem_autI hU).1 hτJ
  have hℓK : ℓ ∈ autI hU K := by
    rw [hK.autI_eq h]
    exact le_sup_left (b := autI hU (baum T)) hℓL
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hU).1 hℓK
  have htC : (t : G) ∈ Subgroup.centralizer (V₁ : Set G) := hle (hJS ▸ htJ)
  have hkN : (k : G) ∈ Subgroup.normalizer (Subgroup.centralizer (V₁ : Set G) : Set G) :=
    B2F.normalizer_le_normalizer_centralizer V₁ (le_normalizer_conjClosure _ K hkK)
  have hc : (k : G) * t * (k : G)⁻¹ * (t : G)⁻¹ ∈ Subgroup.centralizer (V₁ : Set G) :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hkN _).mp htC) (Subgroup.inv_mem _ htC)
  obtain ⟨e, φ, -⟩ := h.fam.nat L h.mem
  have hcard : Nat.card (commV L) = 4 := by
    rw [Nat.card_congr φ.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hS2 : IsPGroup 2 S := h.sylow.2.1.to_le inf_le_left
  have hSI : autI hU S ≤ ⨆ L' ∈ I, L' :=
    (h.autI_inf_eq hMN).le.trans ((h.autI_baum_le hMN).trans h.thompsonJ_eq.le)
  obtain ⟨w, hwU, hw1, hwfix⟩ := exists_ne_one_fixed (isPGroup_autI hU hS2) hcard
    (fun p hp u hu => h.fam.mem_commV_of_mem_iSup h.mem (hSI hp) hu)
  have hwS : w.val ∈ S := (h.pCoreOf_le_inf hMN) (h.V_le_pCoreOf w.val_mem)
  have hwC : w.val ∈ Subgroup.centralizer (S : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have hsN : s ∈ Subgroup.normalizer (V : Set G) := hMN (h.sylow.1 hs.1)
    have hfix := hwfix (convI hU ⟨s, hsN⟩) (convI_mem_autI hU hs hsN)
    have h2 := congrArg IntMod.val hfix
    rw [convI_apply_val] at h2
    calc s * w.val = s * w.val * s⁻¹ * s := by group
      _ = w.val * s := by rw [h2]
  have hwZ : w.val ∈ quasithinOmegaOneCenter S :=
    Subgroup.subset_closure ⟨⟨hwS, hwC⟩, hU.2 w.val w.val_mem⟩
  have hwV₁ : w.val ∈ V₁ := le_conjClosure _ K hwZ
  have hcw := Subgroup.mem_centralizer_iff.1 hc w.val hwV₁
  set c : Subgroup.normalizer (V : Set G) := k * t * k⁻¹ * t⁻¹ with hcdef
  have hcfix : convI hU c w = w := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hcv : (c : G) = (k : G) * t * (k : G)⁻¹ * (t : G)⁻¹ := rfl
    rw [hcv]
    calc (k : G) * t * (k : G)⁻¹ * (t : G)⁻¹ * w.val * ((k : G) * t * (k : G)⁻¹ * (t : G)⁻¹)⁻¹ =
        (w.val * ((k : G) * t * (k : G)⁻¹ * (t : G)⁻¹)) *
          ((k : G) * t * (k : G)⁻¹ * (t : G)⁻¹)⁻¹ := by rw [hcw]
      _ = w.val := by group
  have hconv : convI hU c = convI hU k * convI hU t * (convI hU k)⁻¹ * (convI hU t)⁻¹ := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv]
  obtain ⟨h3, h1⟩ := comm_three_of_actsAsNaturalL2 (h.fam.nat L h.mem) hℓL hτL hℓ3 hℓ1 hτ2 hτ1
  have hmemL : convI hU c ∈ L := by
    rw [hconv]
    exact L.mul_mem (L.mul_mem (L.mul_mem hℓL hτL) (L.inv_mem hℓL)) (L.inv_mem hτL)
  rw [← hconv] at h3 h1
  exact hw1 (eq_one_of_fixed_of_actsAsNaturalL2 (h.fam.nat L h.mem) hmemL h3 h1 hwU hcfix)

theorem not_le_normalizer :
    ¬ K ≤ Subgroup.normalizer
      ((T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) : Subgroup G) : Set G) := by
  intro hKN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := hK.isSylowTwoOf h
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl (hK.charTwo h) le_rfl
  have hSO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hsyl.1 hKN hsyl.2.1
  apply hK.not_thompsonJ_le h
  exact (thompsonJ_le_self _).trans (hSO.trans (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hred))

theorem minParabolic :
    MinParabolic K (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)))
      (K ⊓ preAutM hU hMN (autI hU (baum T))) :=
  C1Pack.minParabolic_of_minimal (hK.isSylowTwoOf h) (h.inf_le_preAutM hMN) hK.not_le hK.min
    (hK.not_le_normalizer h)

section Z

variable {ℓ : MulAut (IntMod V hU)} (hℓL : ℓ ∈ L) (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1) {z : G}
  (hzW : z ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
  (hzN : z ∉ K ⊓ Subgroup.centralizer (V : Set G))
  (hzS : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ Subgroup.normalizer
    ((Subgroup.zpowers z ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G))
include hℓL hℓ3 hℓ1 hzW hzN hzS

omit hℓL hℓ1 hzW hzN hzS in
theorem not_mem_preAutM_of_mem_W {y : G} (hyW : y ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
    (hyN : y ∉ K ⊓ Subgroup.centralizer (V : Set G)) :
    y ∉ preAutM hU hMN (autI hU (baum T)) := by
  intro hy
  have hyM := hK.le_M hyW.1
  have h1 := (mem_preAutM_iff_convI hMN hyM).1 hy
  have h2 := (mem_preAutM_iff_convI hMN hyM).1 hyW.2
  have h3 : convI hU ⟨y, hMN hyM⟩ ∈ Subgroup.zpowers ℓ ⊓ autI hU (baum T) := ⟨h2, h1⟩
  rw [h.zpowers_inf_eq_bot hℓ3, Subgroup.mem_bot, convI_eq_one_iff] at h3
  exact hyN ⟨hyW.1, h3⟩

omit hℓL hℓ1 hzS in
theorem sup_eq_K :
    (Subgroup.zpowers z ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⊔
      (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) = K := by
  refine hK.eq_of_not_le le_sup_right (sup_le (sup_le ((Subgroup.zpowers_le).2 hzW.1)
    ((inf_centralizer_le h).trans hK.le)) hK.le) fun hle => ?_
  exact hK.not_mem_preAutM_of_mem_W h hℓ3 hzW hzN
    (hle (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))))

omit hℓL hℓ1 in
theorem W_eq :
    K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) =
      Subgroup.zpowers z ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
  set P₀ := T ⊓ Subgroup.centralizer (V : Set G) with hP₀
  set W := K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) with hW
  have hP₀W : P₀ ≤ W := fun x hx =>
    hK.inf_centralizer_le_W ⟨hK.le (inf_centralizer_le h hx), hx.2⟩
  have hZW : Subgroup.zpowers z ⊔ P₀ ≤ W := sup_le ((Subgroup.zpowers_le).2 hzW) hP₀W
  refine le_antisymm (fun w hw => ?_) hZW
  have hwK : w ∈ ((Subgroup.zpowers z ⊔ P₀ ⊔ (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) :
      Subgroup G) : Set G) := by
    rw [hK.sup_eq_K h hℓ3 hzW hzN]
    exact hw.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzS] at hwK
  obtain ⟨x, hx, s, hs, rfl⟩ := hwK
  have hsW : s ∈ W := by
    have := W.mul_mem (W.inv_mem (hZW hx)) hw
    simpa using this
  have hsM : s ∈ M := h.sylow.1 hs.1
  have h1 : convI hU ⟨s, hMN hsM⟩ ∈ autI hU (baum T) := by
    rw [← h.autI_inf_eq hMN]
    exact convI_mem_autI hU hs (hMN hsM)
  have h2 := (mem_preAutM_iff_convI hMN hsM).1 hsW.2
  have h3 : convI hU ⟨s, hMN hsM⟩ ∈ Subgroup.zpowers ℓ ⊓ autI hU (baum T) := ⟨h2, h1⟩
  rw [h.zpowers_inf_eq_bot hℓ3, Subgroup.mem_bot, convI_eq_one_iff] at h3
  exact Subgroup.mul_mem _ hx (Subgroup.mem_sup_right ⟨hs.1, h3⟩)

theorem isTwoQuotient_W :
    ∀ k ∈ K, ∃ j : ℕ, k ^ 2 ^ j ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) := by
  refine B6.isTwoQuotient_of_sup_eq
    (h.sylow.2.1.to_le (inf_le_left : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ T))
    (hK.le_normalizer_W h hℓL hℓ3 hℓ1) ?_
  rw [hK.W_eq h hℓ3 hzW hzN hzS, sup_comm]
  exact hK.sup_eq_K h hℓ3 hzW hzN

theorem twoResidual_le_W : twoResidual K ≤ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) :=
  twoResidual_le_of_isTwoQuotient inf_le_left (hK.le_normalizer_W h hℓL hℓ3 hℓ1)
    (hK.isTwoQuotient_W h hℓL hℓ3 hℓ1 hzW hzN hzS)

end Z

section Quot

variable {ℓ : MulAut (IntMod V hU)} (hℓL : ℓ ∈ L) (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1) {z : G}
  (hzW : z ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
  (hzN : z ∉ K ⊓ Subgroup.centralizer (V : Set G))
  (hzS : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ Subgroup.normalizer
    ((Subgroup.zpowers z ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G))
include hℓL hℓ3 hℓ1 hzW hzN hzS

omit hℓL hℓ1 hℓ3 hzW hzN hzS in
theorem P₀_le_W :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) := fun _ hx =>
  hK.inf_centralizer_le_W ⟨hK.le (inf_centralizer_le h hx), hx.2⟩

omit hℓL hℓ1 hℓ3 hzW hzN hzS in
theorem P₀_normal :
    ((T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf
      (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hK.P₀_le_W h)).2
    (inf_le_left.trans (hK.le_normalizer_P₀ h))

omit hℓL hℓ1 hℓ3 hzN hzS in
theorem zpowers_le_normalizer_P₀ :
    Subgroup.zpowers z ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  (Subgroup.zpowers_le).2 (hK.le_normalizer_P₀ h hzW.1)

omit hℓL hℓ1 in
theorem isCyclic_quotient :
    haveI := hK.P₀_normal h (ℓ := ℓ)
    IsCyclic (↥(K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ)) ⧸
      (T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf
        (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))) :=
  haveI := hK.P₀_normal h (ℓ := ℓ)
  isCyclic_quotient_of_eq hzW (hK.zpowers_le_normalizer_P₀ h hzW)
    (hK.W_eq h hℓ3 hzW hzN hzS)

theorem mem_W_of_pow_eq_one {x : G} (hxK : x ∈ K) {b : ℕ} (hb : Odd b) (hxb : x ^ b = 1) :
    x ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) := by
  obtain ⟨j, hj⟩ := hK.isTwoQuotient_W h hℓL hℓ3 hℓ1 hzW hzN hzS x hxK
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hb)) hj hxb

theorem isCyclic_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) : IsCyclic P := by
  have := hK.P₀_normal h (ℓ := ℓ)
  have := hK.isCyclic_quotient h hℓ3 hzW hzN hzS
  have hpodd : ∀ m : ℕ, Odd (p ^ m) := fun m => (hp.odd_of_ne_two hp2).pow
  refine isCyclic_of_inf_eq_bot (W := K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
    (P₀ := T ⊓ Subgroup.centralizer (V : Set G)) (fun x hx => ?_) ?_
  · obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
    exact hK.mem_W_of_pow_eq_one h hℓL hℓ3 hℓ1 hzW hzN hzS (hPK hx) (hpodd m)
      (by simpa using congrArg Subtype.val hm)
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨m, hm⟩ := hP ⟨x, hx.1⟩
    obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨x, hx.2.1⟩
    have hxm : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_of_pow_mem_of_coprime (H := ⊥)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (hpodd m))) (by rw [hxk]; exact one_mem _)
      hxm

theorem pRank_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p K ≤ 1 := by
  apply csSup_le'
  rintro k ⟨E, hEK, hEab, hcard⟩
  have hpow : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hEab.2 x x.2)
  have hEp : IsPGroup p E := fun x => ⟨1, by simpa using hpow x⟩
  have hcyc := hK.isCyclic_of_isPGroup h hℓL hℓ3 hℓ1 hzW hzN hzS hp hp2 hEK hEp
  have hexp : Monoid.exponent E ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have : p ^ k ∣ p ^ 1 := by rwa [pow_one]
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 this

theorem isSolvable : Group.IsSolvable ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) with hW
  set P₀ := T ⊓ Subgroup.centralizer (V : Set G) with hP₀
  have := hK.P₀_normal h (ℓ := ℓ)
  have hcyc := hK.isCyclic_quotient h hℓ3 hzW hzN hzS
  have hP₀W : P₀ ≤ W := hK.P₀_le_W h
  have hWsolv : Group.IsSolvable ↥W := by
    have h2 : IsPGroup 2 ↥(P₀.subgroupOf W) :=
      (h.sylow.2.1.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hP₀W).symm
    have : Group.IsNilpotent ↥(P₀.subgroupOf W) := h2.isNilpotent
    have : Group.IsSolvable (↥W ⧸ P₀.subgroupOf W) :=
      Group.isSolvable_of_comm (IsCyclic.commGroup (α := ↥W ⧸ P₀.subgroupOf W)).mul_comm
    exact Group.isSolvable_of_ker_le_range (P₀.subgroupOf W).subtype (QuotientGroup.mk' _)
      (by
        intro x hx
        rw [QuotientGroup.ker_mk'] at hx
        exact ⟨⟨x, hx⟩, rfl⟩)
  have hWK : W ≤ K := inf_le_left
  have hWn : (W.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWK).2 (hK.le_normalizer_W h hℓL hℓ3 hℓ1)
  have : Group.IsSolvable ↥(W.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hWK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hWK).injective
  have hq : IsPGroup 2 (↥K ⧸ W.subgroupOf K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j, hj⟩ := hK.isTwoQuotient_W h hℓL hℓ3 hℓ1 hzW hzN hzS x x.2
    refine ⟨j, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hj
  have : Group.IsNilpotent (↥K ⧸ W.subgroupOf K) := hq.isNilpotent
  exact Group.isSolvable_of_ker_le_range (W.subgroupOf K).subtype (QuotientGroup.mk' _)
    (by
      intro x hx
      rw [QuotientGroup.ker_mk'] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

end Quot

section Assembly

variable {ℓ : MulAut (IntMod V hU)} (hℓL : ℓ ∈ L) (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1) {z : G}
  (hzW : z ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
  (hzN : z ∉ K ⊓ Subgroup.centralizer (V : Set G))
  (hz3 : ∃ a : ℕ, z ^ 3 ^ a ∈ T ⊓ Subgroup.centralizer (V : Set G))
  (hzS : T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)) ≤ Subgroup.normalizer
    ((Subgroup.zpowers z ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G))
include hℓL hℓ3 hℓ1 hzW hzN hz3 hzS

omit [Finite G] h hℓL hℓ1 hzN hz3 hzS in
theorem pow_three_mem : z ^ 3 ∈ K ⊓ Subgroup.centralizer (V : Set G) := by
  have hzM := hK.le_M hzW.1
  have hz3M : z ^ 3 ∈ M := M.pow_mem hzM 3
  refine ⟨K.pow_mem hzW.1 3, ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ((mem_preAutM_iff_convI hMN hzM).1 hzW.2)
  have e : convI hU ⟨z ^ 3, hMN hz3M⟩ = (convI hU ⟨z, hMN hzM⟩) ^ 3 := by
    rw [← map_pow]
    rfl
  show z ^ 3 ∈ Subgroup.centralizer (V : Set G)
  refine (convI_eq_one_iff hU ⟨z ^ 3, hMN hz3M⟩).1 ?_
  rw [e, ← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hℓ3,
    one_zpow]

theorem exists_H₀ :
    ∃ H₀ : Subgroup G, H₀ ≤ M ∧ baum T ≤ H₀ ∧ IsSylowTwoOf (baum T) H₀ ∧ CharTwo H₀ ∧
      IsMinParabolicOf H₀ H₀ ∧ Group.IsSolvable ↥H₀ ∧ autI hU H₀ = L ⊔ autI hU (baum T) ∧
      pCoreOf 2 M ≤ Subgroup.normalizer (H₀ : Set G) ∧
      pCoreOf 2 M ≤ Subgroup.normalizer (twoResidual H₀ : Set G) ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) H₀ : Set G) ∧
      ∀ P : Subgroup G, P ≤ H₀ → IsPGroup 3 P → IsCyclic P := by
  have hsolv := hK.isSolvable h hℓL hℓ3 hℓ1 hzW hzN hzS
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p K ≤ 2 := fun p hp hp2 =>
    (hK.pRank_le_one h hℓL hℓ3 hℓ1 hzW hzN hzS hp hp2).trans (by norm_num)
  obtain ⟨P, hBP, hPY, hPM, -, hPmin, hPF, hPJ, hSyl⟩ :=
    C1Pack.exists_minimal_parabolic_over_baum (hK.minParabolic h) (hK.charTwo h) hsolv hSQT
      (hK.not_thompsonJ_le h)
  rw [h.baum_inf hMN] at hBP hPY hPmin hPJ hSyl
  have hOK : twoResidual K ≤ K := twoResidual_le K
  have hBK : baum T ≤ K := hK.baum_le h
  have hYK : twoResidual K ⊔ baum T ≤ K := sup_le hOK hBK
  have hPK : P ≤ K := hPY.trans hYK
  have hPMX : ¬ P ≤ preAutM hU hMN (autI hU (baum T)) := fun hle => hPM (le_inf hPK hle)
  obtain ⟨p, hpP, hpMX⟩ := Set.not_subset.1 hPMX
  have hBN : baum T ≤ Subgroup.normalizer (twoResidual K : Set G) :=
    hBK.trans (le_normalizer_twoResidual K)
  have hp' : p ∈ ((twoResidual K ⊔ baum T : Subgroup G) : Set G) := hPY hpP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hp'
  obtain ⟨w, hwO, b, hb, rfl⟩ := hp'
  have hwP : w ∈ P := by
    have := P.mul_mem hpP (P.inv_mem (hBP hb))
    simpa using this
  have hwW : w ∈ K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) :=
    hK.twoResidual_le_W h hℓL hℓ3 hℓ1 hzW hzN hzS hwO
  have hwN : w ∉ K ⊓ Subgroup.centralizer (V : Set G) := by
    intro hwC
    apply hpMX
    exact (preAutM hU hMN (autI hU (baum T))).mul_mem
      (centralizer_inf_le_preAutM hU hMN _ ⟨hwC.2, hK.le_M hwC.1⟩)
      (h.baum_le_preAutM hMN hb)
  obtain ⟨a, ha⟩ := hz3
  have := hK.P₀_normal h (ℓ := ℓ)
  have hP₀N₀ : T ⊓ Subgroup.centralizer (V : Set G) ≤ K ⊓ Subgroup.centralizer (V : Set G) :=
    (hK.isSylowTwoOf_inf_centralizer h).1
  have hzw : z ∈ Subgroup.zpowers w ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) :=
    mem_zpowers_sup_of_not_mem (W := K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
      (P₀ := T ⊓ Subgroup.centralizer (V : Set G)) hzW hwW (hK.zpowers_le_normalizer_P₀ h hzW)
      (hK.W_eq h hℓ3 hzW hzN hzS) hP₀N₀ (hK.pow_three_mem hℓ3 hzW) ha hwN
  have hOP₀ : twoResidual K ⊓ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ baum T := by
    have hn : twoResidual K ⊔ baum T ≤
        Subgroup.normalizer ((twoResidual K ⊓ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :
          Set G) :=
      hYK.trans (B2F.le_normalizer_inf (le_normalizer_twoResidual K) (hK.le_normalizer_P₀ h))
    have h2 : IsPGroup 2 (twoResidual K ⊓ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :=
      h.sylow.2.1.to_le (inf_le_right.trans inf_le_left)
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left)
      hn h2).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hSyl)
  have hwP₀ : Subgroup.zpowers w ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).2 (hK.le_normalizer_P₀ h (hOK hwO))
  have hOP : twoResidual K ≤ P := by
    intro y hy
    have hWle : K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ) ≤
        Subgroup.zpowers w ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
      rw [hK.W_eq h hℓ3 hzW hzN hzS]
      exact sup_le ((Subgroup.zpowers_le).2 hzw) le_sup_right
    have hy' : y ∈ ((Subgroup.zpowers w ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :
        Set G) :=
      hWle (hK.twoResidual_le_W h hℓL hℓ3 hℓ1 hzW hzN hzS hy)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hwP₀] at hy'
    obtain ⟨x, hx, d, hd, rfl⟩ := hy'
    have hxO : x ∈ twoResidual K := (Subgroup.zpowers_le).2 hwO hx
    have hdO : d ∈ twoResidual K := by
      have := (twoResidual K).mul_mem ((twoResidual K).inv_mem hxO) hy
      simpa using this
    exact P.mul_mem ((Subgroup.zpowers_le).2 hwP hx) (hBP (hOP₀ ⟨hdO, hd⟩))
  have hPeq : P = twoResidual K ⊔ baum T := le_antisymm hPY (sup_le hOP hBP)
  have hB2 : IsPGroup 2 (baum T) := h.sylow.2.1.to_le (inf_le_left : baum T ≤ T)
  have hOeq : twoResidual P = twoResidual K := by
    have hPN : P ≤ Subgroup.normalizer (twoResidual K : Set G) :=
      hPK.trans (le_normalizer_twoResidual K)
    refine le_antisymm (twoResidual_le_of_isTwoQuotient hOP hPN ?_) ?_
    · exact B6.isTwoQuotient_of_sup_eq hB2 hPN (by rw [sup_comm, hPeq])
    · have hle : twoResidual (twoResidual K) ≤ twoResidual K ⊓ twoResidual P := by
        refine twoResidual_le_of_isTwoQuotient inf_le_left
          (B2F.le_normalizer_inf Subgroup.le_normalizer
            (hOP.trans (le_normalizer_twoResidual P))) fun y hy => ?_
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient P y (hOP hy)
        exact ⟨k, (twoResidual K).pow_mem hy _, hk⟩
      rw [twoResidual_twoResidual] at hle
      exact hle.trans inf_le_right
  have hQK : pCoreOf 2 M ≤ K := hK.pCoreOf_le h
  refine ⟨P, hPK.trans hK.le_M, hBP, hPmin.isSylow, hPF, (minParabolic_iff.1 hPmin).1, ?_, ?_,
    ?_, ?_, hPJ, ?_⟩
  · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPK)
  · rcases eq_or_eq_of_relIndex_eq_three (h.relIndex_eq_three hMN) (autI_mono hU hBP)
      ((autI_mono hU hPK).trans (hK.autI_eq h).le) with h1 | h1
    · exact absurd (le_preAutM_of_autI_le hMN (hPK.trans hK.le_M) h1.le) hPMX
    · exact h1
  · rw [hPeq]
    exact B2F.le_normalizer_sup (hQK.trans (le_normalizer_twoResidual K))
      ((B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow).trans
        (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)))
  · rw [hOeq]
    exact hQK.trans (le_normalizer_twoResidual K)
  · intro P' hP'P hP'
    exact hK.isCyclic_of_isPGroup h hℓL hℓ3 hℓ1 hzW hzN hzS Nat.prime_three (by norm_num)
      (hP'P.trans hPK) hP'

end Assembly

end IsFFH0Min

@[expose] def InvariantCyclicSupplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W N₀ D S : Subgroup G), D ≤ N₀ → N₀ ≤ W →
    W ≤ Subgroup.normalizer (D : Set G) → W ≤ Subgroup.normalizer (N₀ : Set G) →
    N₀.relIndex W = 3 → ¬ 2 ∣ D.relIndex W → IsPGroup 2 S →
    S ≤ Subgroup.normalizer (W : Set G) → S ≤ Subgroup.normalizer (N₀ : Set G) →
    S ≤ Subgroup.normalizer (D : Set G) →
    ∃ z ∈ W, z ∉ N₀ ∧ (∃ a : ℕ, z ^ 3 ^ a ∈ D) ∧
      S ≤ Subgroup.normalizer ((Subgroup.zpowers z ⊔ D : Subgroup G) : Set G)

namespace FFH0Hyp

variable {G : Type} [Group G] [Finite G] {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} {L : Subgroup (MulAut (IntMod V hU))}

theorem exists_H₀ (hsup : InvariantCyclicSupplement) (h : FFH0Hyp M T V hU I L)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    ∃ H₀ : Subgroup G, H₀ ≤ M ∧ baum T ≤ H₀ ∧ IsSylowTwoOf (baum T) H₀ ∧ CharTwo H₀ ∧
      IsMinParabolicOf H₀ H₀ ∧ Group.IsSolvable ↥H₀ ∧ autI hU H₀ = L ⊔ autI hU (baum T) ∧
      pCoreOf 2 M ≤ Subgroup.normalizer (H₀ : Set G) ∧
      pCoreOf 2 M ≤ Subgroup.normalizer (twoResidual H₀ : Set G) ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) H₀ : Set G) ∧
      ∀ P : Subgroup G, P ≤ H₀ → IsPGroup 3 P → IsCyclic P := by
  obtain ⟨K, hSK, hKX, hKMX, hmin⟩ := C1Pack.exists_minimal_not_le
    (S := T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T))) inf_le_right (h.not_preAutM_le hMN)
  have hK : IsFFH0Min M T V hMN L K := ⟨hSK, hKX, hKMX, hmin⟩
  obtain ⟨ℓ, hℓL, hℓ3, hℓ1⟩ := h.exists_ell
  obtain ⟨z, hzW, hzN, hz3, hzS⟩ := hsup G (K ⊓ preAutM hU hMN (Subgroup.zpowers ℓ))
    (K ⊓ Subgroup.centralizer (V : Set G)) (T ⊓ Subgroup.centralizer (V : Set G))
    (T ⊓ preAutM hU hMN (L ⊔ autI hU (baum T)))
    (hK.isSylowTwoOf_inf_centralizer h).1 hK.inf_centralizer_le_W
    (inf_le_left.trans (hK.le_normalizer_P₀ h)) (inf_le_left.trans hK.le_normalizer_inf_centralizer)
    (hK.relIndex_W h hℓL hℓ3 hℓ1) (hK.odd_relIndex_W h hℓL hℓ3 hℓ1)
    (h.sylow.2.1.to_le inf_le_left) (hK.le.trans (hK.le_normalizer_W h hℓL hℓ3 hℓ1))
    (hK.le.trans hK.le_normalizer_inf_centralizer) (hK.le.trans (hK.le_normalizer_P₀ h))
  exact hK.exists_H₀ h hℓL hℓ3 hℓ1 hzW hzN hz3 hzS

end FFH0Hyp

open CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def FFH0Data : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      ∀ L ∈ I, ∃ H₀ : Subgroup G, H₀ ≤ M ∧ baum T ≤ H₀ ∧ IsSylowTwoOf (baum T) H₀ ∧
        CharTwo H₀ ∧ IsMinParabolicOf H₀ H₀ ∧ Group.IsSolvable ↥H₀ ∧
        autI hU H₀ = L ⊔ autI hU (baum T) ∧
        pCoreOf 2 M ≤ Subgroup.normalizer (H₀ : Set G) ∧
        pCoreOf 2 M ≤ Subgroup.normalizer (twoResidual H₀ : Set G) ∧
        ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) H₀ : Set G) ∧
        ∀ Q : Subgroup G, Q ≤ H₀ → IsPGroup 3 Q → IsCyclic Q

theorem ffH0Data_of_supplement (hsup : InvariantCyclicSupplement) : FFH0Data := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  have hF : CharTwo M := hc.glob.charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  exact FFH0Hyp.exists_H₀ hsup ⟨hF, hT, hle, hfam, hcard, hJM, hSyl, hperm, hL⟩ hMN

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
