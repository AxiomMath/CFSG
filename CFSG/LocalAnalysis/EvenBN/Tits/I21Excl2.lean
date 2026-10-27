module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl1

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

section Algebra

variable {K : Type*} [Group K]

theorem exists_zpow_mul_zpow_of_mem_closure {a b : K} (h : a * b = b * a) {x : K}
    (hx : x ∈ closure ({a, b} : Set K)) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  have h' : Commute a b := h
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨i', j', rfl⟩ := hy
    refine ⟨i + i', j + j', ?_⟩
    have hc : b ^ j * a ^ i' = a ^ i' * b ^ j := (Commute.zpow_zpow h' i' j).eq.symm
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [hc]
      _ = a ^ (i + i') * b ^ (j + j') := by
          rw [zpow_add, zpow_add]; simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, zpow_neg, zpow_neg, ← zpow_neg, ← zpow_neg]
    exact (Commute.zpow_zpow h' (-i) (-j)).eq.symm

theorem sq_mem_zpowers_of_mem_closure {a b : K} (h : a * b = b * a) (hb : b ^ 2 = 1) {x : K}
    (hx : x ∈ closure ({a, b} : Set K)) : ∃ i : ℤ, x ^ 2 = (a ^ 2) ^ i := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure h hx
  refine ⟨i, ?_⟩
  have h' : Commute a b := h
  rw [(Commute.zpow_zpow h' i j).mul_pow]
  have h1 : (b ^ j) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  rw [h1, mul_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem eq_sq_of_mem_zpowers {y x : K} (hy : orderOf y = 4) (hx : x ∈ zpowers y)
    (hx2 : orderOf x = 2) : x = y ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : y ^ (k % (4 : ℤ)) = y ^ k := by
    have := zpow_mod_orderOf y k
    rwa [hy, Nat.cast_ofNat] at this
  rw [← h1] at hx2 ⊢
  have h0 : 0 ≤ k % (4 : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h4 : k % (4 : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  generalize k % (4 : ℤ) = j at h0 h4 hx2 ⊢
  interval_cases j
  · rw [zpow_zero, orderOf_one] at hx2; omega
  · rw [zpow_one, hy] at hx2; omega
  · simp
  · have h4' : y ^ (4 : ℤ) = 1 := by
      have : y ^ (4 : ℕ) = 1 := hy ▸ pow_orderOf_eq_one y
      simpa using this
    have : y ^ (3 : ℤ) = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
      simpa using h4'
    rw [this, orderOf_inv, hy] at hx2
    omega

theorem mem_zpowers_of_central [Finite K] {M : Subgroup K} (hcard : Nat.card M = 16)
    (hnab : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) {c : K} (hcM : c ∈ M) (hc : orderOf c = 4)
    (hcc : ∀ m ∈ M, m * c = c * m) {x : K} (hxM : x ∈ M) (hx : ∀ m ∈ M, m * x = x * m) :
    x ∈ zpowers c := by
  set N : Subgroup M := Subgroup.center M with hN
  have hc' : (⟨c, hcM⟩ : M) ∈ N := Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hcc m m.2)
  have hx' : (⟨x, hxM⟩ : M) ∈ N := Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hx m m.2)
  have hz : zpowers (⟨c, hcM⟩ : M) ≤ N := (zpowers_le).mpr hc'
  have hzc : Nat.card (zpowers (⟨c, hcM⟩ : M)) = 4 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc]
  have h4 : 4 ∣ Nat.card N := hzc ▸ Subgroup.card_dvd_of_le hz
  have h16 : Nat.card N ∣ 16 := hcard ▸ N.card_subgroup_dvd_card
  have hidx : Nat.card N * N.index = 16 := hcard ▸ N.card_mul_index
  have hab : ¬ ∀ a b : M, a * b = b * a := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact hab (congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩))
  have hne8 : Nat.card N ≠ 8 := by
    intro h8
    have hi : N.index = 2 := by rw [h8] at hidx; omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic (M ⧸ Subgroup.center M) :=
      isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index]; exact hi)
    exact hab (isMulCommutative_iff.mp (isMulCommutative_of_isCyclic_quotient_center_self M))
  have hne16 : Nat.card N ≠ 16 := by
    intro h16'
    have hi : N.index = 1 := by rw [h16'] at hidx; omega
    have htop : N = ⊤ := Subgroup.index_eq_one.mp hi
    exact hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp htop))
  have hNc : Nat.card N = 4 := by
    have hle : Nat.card N ≤ 16 := Nat.le_of_dvd (by norm_num) h16
    have hpos : 0 < Nat.card N := Nat.card_pos
    interval_cases hn : Nat.card N <;> first | rfl | omega
  have heq : zpowers (⟨c, hcM⟩ : M) = N :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hzc, hNc])
  have hxz : (⟨x, hxM⟩ : M) ∈ zpowers (⟨c, hcM⟩ : M) := heq ▸ hx'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem orderOf_conj' (g z : K) : orderOf (g * z * g⁻¹) = orderOf z := by
  simpa using orderOf_conj_inv g⁻¹ z

theorem zpow_eq_one_or_self {z : K} (hz : orderOf z = 2) (i : ℤ) : z ^ i = 1 ∨ z ^ i = z := by
  have h1 : z ^ (i % (2 : ℤ)) = z ^ i := by
    have := zpow_mod_orderOf z i
    rwa [hz, Nat.cast_ofNat] at this
  rw [← h1]
  have h0 : 0 ≤ i % (2 : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h2 : i % (2 : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
  generalize i % (2 : ℤ) = j at h0 h2 ⊢
  interval_cases j
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (zpow_one z)

theorem conj_conj_inv (x q : K) : x⁻¹ * (x * q * x⁻¹) * x = q := by group

theorem conj_inv_conj (x q : K) : x * (x⁻¹ * q * x) * x⁻¹ = q := by group

theorem mem_map_conj_iff (H : Subgroup K) (x q : K) :
    q ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * q * x ∈ H := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hp
  · intro h
    exact ⟨x⁻¹ * q * x, h, by simp [MulAut.conj_apply, mul_assoc]⟩

end Algebra

section Sylow

variable {K : Type*} [Group K] [Finite K]

theorem centralizer_inf_eq_closure {M : Subgroup K} (hcard : Nat.card M = 16) {c : K}
    (hcM : c ∈ M) (hc : orderOf c = 4) (hcc : ∀ m ∈ M, m * c = c * m)
    (hZ : ∀ x ∈ M, (∀ m ∈ M, m * x = x * m) → x ∈ zpowers c) {e : K} (heM : e ∈ M)
    (heC : e ∉ zpowers c) :
    Nat.card (centralizer ({e} : Set K) ⊓ M : Subgroup K) = 8 ∧
      closure ({c, e} : Set K) = centralizer ({e} : Set K) ⊓ M := by
  set C : Subgroup K := centralizer ({e} : Set K) ⊓ M with hCdef
  have hcC : c ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcc e heM).symm, hcM⟩
  have heCC : e ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, heM⟩
  have hCM : C ≤ M := inf_le_right
  have hzC : zpowers c ≤ C := (zpowers_le).mpr hcC
  have hcard4 : Nat.card (zpowers c) = 4 := by rw [Nat.card_zpowers, hc]
  have hC4 : 4 ∣ Nat.card C := hcard4 ▸ Subgroup.card_dvd_of_le hzC
  have hC16 : Nat.card C ∣ 16 := hcard ▸ Subgroup.card_dvd_of_le hCM
  have hC8 : Nat.card C = 8 := by
    have hle : Nat.card C ≤ 16 := Nat.le_of_dvd (by norm_num) hC16
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hne4 : Nat.card C ≠ 4 := by
      intro h4
      have : zpowers c = C := Subgroup.eq_of_le_of_card_ge hzC (by rw [hcard4, h4])
      exact heC (this ▸ heCC)
    have hne16 : Nat.card C ≠ 16 := by
      intro h16'
      have hCeq : C = M := Subgroup.eq_of_le_of_card_ge hCM (by rw [h16', hcard])
      refine heC (hZ e heM fun m hm => ?_)
      have hmC : m ∈ C := hCeq ▸ hm
      exact Subgroup.mem_centralizer_singleton_iff.mp hmC.1
    interval_cases hn : Nat.card C <;> first | rfl | omega
  refine ⟨hC8, ?_⟩
  have hle : closure ({c, e} : Set K) ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hcC
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact heCC
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : zpowers c ≤ closure ({c, e} : Set K) :=
    (zpowers_le).mpr (Subgroup.subset_closure (by simp))
  have h2 : 4 ∣ Nat.card (closure ({c, e} : Set K)) := hcard4 ▸ Subgroup.card_dvd_of_le h1
  have h3 : Nat.card (closure ({c, e} : Set K)) ∣ 8 := hC8 ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (closure ({c, e} : Set K)) ≠ 4 := by
    intro h4
    have : zpowers c = closure ({c, e} : Set K) :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard4, h4])
    exact heC (this ▸ Subgroup.subset_closure (by simp))
  have hle8 : Nat.card (closure ({c, e} : Set K)) ≤ 8 := Nat.le_of_dvd (by norm_num) h3
  have hpos : 0 < Nat.card (closure ({c, e} : Set K)) := Nat.card_pos
  rw [hC8]
  omega

theorem mem_of_central_of_index_two {Q C : Subgroup K} (hCQ : C ≤ Q) (hQ : Nat.card Q = 16)
    (hC : Nat.card C = 8) (hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hnab : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) {y : K} (hyQ : y ∈ Q)
    (hyc : ∀ q ∈ Q, q * y = y * q) : y ∈ C := by
  by_contra hyC
  have hle : C ⊔ zpowers y ≤ Q := sup_le hCQ ((zpowers_le).mpr hyQ)
  have hd : Nat.card (C ⊔ zpowers y : Subgroup K) ∣ 16 := hQ ▸ Subgroup.card_dvd_of_le hle
  have h8 : 8 ∣ Nat.card (C ⊔ zpowers y : Subgroup K) :=
    hC ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card (C ⊔ zpowers y : Subgroup K) ≠ 8 := by
    intro h
    have : C = C ⊔ zpowers y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hC, h])
    exact hyC (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hle16 : Nat.card (C ⊔ zpowers y : Subgroup K) ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card (C ⊔ zpowers y : Subgroup K) := Nat.card_pos
  have hsup : C ⊔ zpowers y = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hQ]; omega)
  have h1 : ∀ a ∈ C, ∀ q ∈ Q, q * a = a * q := by
    intro a ha q hq
    rw [← hsup] at hq
    have hle' : C ⊔ zpowers y ≤ centralizer ({a} : Set K) := by
      refine sup_le (fun z hz => ?_) ((zpowers_le).mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hCcomm z hz a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc a (hCQ ha)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle' hq)
  have h2 : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    rw [← hsup] at ha
    have hle' : C ⊔ zpowers y ≤ centralizer ({b} : Set K) := by
      refine sup_le (fun z hz => ?_) ((zpowers_le).mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h1 z hz b hb).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc b hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle' ha)
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  exact hab (h2 a ha b hb)

theorem card_le_card_sylow (S : Sylow 2 K) {H : Subgroup K} (hH : IsPGroup 2 H) :
    Nat.card H ≤ Nat.card (S : Subgroup K) := by
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  have h1 : Nat.card H ≤ Nat.card (S' : Subgroup K) := Subgroup.card_le_of_le hS'
  have h2 : Nat.card (S' : Subgroup K) = Nat.card (S : Subgroup K) := by
    rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S]
  exact h1.trans h2.le

theorem exists_conj_sylow_le (P : Sylow 2 K) {E C : Subgroup K} (hCE : C ≤ E)
    (hC : IsPGroup 2 C) (hPE : ∃ g : K, ∀ p ∈ (P : Subgroup K), g⁻¹ * p * g ∈ E) :
    ∃ x : K, (∀ q ∈ C, x⁻¹ * q * x ∈ (P : Subgroup K)) ∧
      ∀ p ∈ (P : Subgroup K), x * p * x⁻¹ ∈ E := by
  obtain ⟨g, hg⟩ := hPE
  obtain ⟨Q₀, hQ₀⟩ := (hC.comap_subtype (K := E)).exists_le_sylow
  set Q : Subgroup K := (Q₀ : Subgroup E).map E.subtype with hQ
  have hQp : IsPGroup 2 Q := Q₀.isPGroup'.map E.subtype
  have hQE : Q ≤ E := Subgroup.map_subtype_le _
  have hCQ : C ≤ Q := fun x hx =>
    ⟨⟨x, hCE hx⟩, hQ₀ (show (⟨x, hCE hx⟩ : E) ∈ C.subgroupOf E from hx), rfl⟩
  set P' : Subgroup K := (P : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'p : IsPGroup 2 P' := P.isPGroup'.map _
  have hP'E : P' ≤ E := fun q hq => by
    rw [hP', mem_map_conj_iff, inv_inv] at hq
    simpa only [conj_conj_inv] using hg _ hq
  have hP'card : Nat.card P' = Nat.card (P : Subgroup K) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hQcard : Nat.card Q = Nat.card (P : Subgroup K) := by
    apply le_antisymm (card_le_card_sylow P hQp)
    calc Nat.card (P : Subgroup K) = Nat.card P' := hP'card.symm
      _ = Nat.card (P'.subgroupOf E) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'E).toEquiv).symm
      _ ≤ Nat.card (Q₀ : Subgroup E) := card_le_card_sylow Q₀ hP'p.comap_subtype
      _ = Nat.card Q := (Subgroup.card_map_of_injective E.subtype_injective).symm
  have hQsyl : Nat.card Q = 2 ^ (Nat.card K).factorization 2 := by
    rw [hQcard]
    exact Sylow.card_eq_multiplicity P
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq K P (Sylow.ofCard Q hQsyl)
  have hxQ : ∀ y : K, y ∈ Q ↔ ∃ s ∈ (P : Subgroup K), x * s * x⁻¹ = y := by
    intro y
    have h1 : y ∈ (x • P : Sylow 2 K) ↔ y ∈ Q := by
      rw [hx]
      exact Iff.rfl
    rw [← h1, ← SetLike.mem_coe, Sylow.coe_smul, Set.mem_smul_set]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    exact Iff.rfl
  refine ⟨x, fun q hq => ?_, fun p hp => hQE ((hxQ _).mpr ⟨p, hp, rfl⟩)⟩
  obtain ⟨s, hs, hsq⟩ := (hxQ q).mp (hCQ hq)
  have : x⁻¹ * q * x = s := by rw [← hsq]; group
  rwa [this]

end Sylow

section Main

variable {L : Type} [Group L] [Finite L]

theorem order16_false [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) (P : Sylow 2 L)
    (h16 : Sec622Order16 (P : Subgroup L)) : False := by
  obtain ⟨hcard, hnonab, c, hcP, hc4, hcc⟩ := h16
  have hZ : ∀ x ∈ (P : Subgroup L), (∀ m ∈ (P : Subgroup L), m * x = x * m) →
      x ∈ zpowers c := fun x hx hxc =>
    mem_zpowers_of_central hcard hnonab hcP hc4 hcc hx hxc
  have hz₀ : orderOf (c ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hc4]; norm_num), hc4]
  have hz₀P : c ^ 2 ∈ (P : Subgroup L) := pow_mem hcP 2
  have hz₀c : ∀ m ∈ (P : Subgroup L), m * c ^ 2 = c ^ 2 * m := fun m hm =>
    ((Commute.pow_right (show Commute m c from hcc m hm) 2)).eq
  obtain ⟨g, hgP, hgne⟩ := exists_conj_mem_ne hnab P hz₀P hz₀c hz₀
  set e : L := g⁻¹ * c ^ 2 * g with he
  have he2 : orderOf e = 2 := by rw [he, orderOf_conj_inv, hz₀]
  have heP : e ∈ (P : Subgroup L) := hgP
  have hesq : e ^ 2 = 1 := he2 ▸ pow_orderOf_eq_one e
  have heC : e ∉ zpowers c := fun h => hgne (eq_sq_of_mem_zpowers hc4 h he2)
  obtain ⟨hC8, hclos⟩ := centralizer_inf_eq_closure hcard hcP hc4 hcc hZ heP heC
  set C : Subgroup L := centralizer ({e} : Set L) ⊓ (P : Subgroup L) with hCdef
  have hcomm_ce : c * e = e * c := (hcc e heP).symm
  have hCsq : ∀ y ∈ C, ∃ i : ℤ, y ^ 2 = (c ^ 2) ^ i := fun y hy =>
    sq_mem_zpowers_of_mem_closure hcomm_ce hesq (hclos ▸ hy)
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    rw [← hclos] at ha hb
    have hcm : IsMulCommutative (closure ({c, e} : Set L)) := by
      apply Subgroup.isMulCommutative_closure
      intro u hu v hv _
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact hcomm_ce
      · rw [Set.mem_singleton_iff] at hu
        subst hu
        exact hcomm_ce.symm
      · rw [Set.mem_singleton_iff] at hu hv
        subst hu
        subst hv
        exact Commute.refl _
    exact congrArg Subtype.val (isMulCommutative_iff.mp hcm ⟨a, ha⟩ ⟨b, hb⟩)
  have hgE : ∀ p ∈ (P : Subgroup L), g⁻¹ * p * g ∈ centralizer ({e} : Set L) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff, he]
    have h1 := hz₀c p hp
    calc g⁻¹ * p * g * (g⁻¹ * c ^ 2 * g) = g⁻¹ * (p * c ^ 2) * g := by group
      _ = g⁻¹ * (c ^ 2 * p) * g := by rw [h1]
      _ = g⁻¹ * c ^ 2 * g * (g⁻¹ * p * g) := by group
  obtain ⟨x, hxC, hxE⟩ := exists_conj_sylow_le P (E := centralizer ({e} : Set L)) (C := C)
    inf_le_left (P.isPGroup'.to_le inf_le_right) ⟨g, hgE⟩
  set Q : Subgroup L := (P : Subgroup L).map (MulAut.conj x).toMonoidHom with hQ
  have hQ16 : Nat.card Q = 16 := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard]
  have hQE : ∀ q ∈ Q, q * e = e * q := fun q hq => by
    rw [hQ, mem_map_conj_iff] at hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (by simpa only [conj_inv_conj] using hxE _ hq)
  have hCQ : C ≤ Q := fun q hq => (mem_map_conj_iff _ _ _).mpr (hxC q hq)
  have heCC : e ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, heP⟩
  have heQ : e ∈ Q := hCQ heCC
  set y : L := x * c * x⁻¹ with hy
  have hyQ : y ∈ Q := (mem_map_conj_iff _ _ _).mpr (by simpa only [hy, conj_conj_inv] using hcP)
  have hyc : ∀ q ∈ Q, q * y = y * q := by
    intro q hq
    rw [hQ, mem_map_conj_iff] at hq
    have h1 := hcc _ hq
    calc q * y = x * (x⁻¹ * q * x * c) * x⁻¹ := by rw [hy]; group
      _ = x * (c * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
      _ = y * q := by rw [hy]; group
  have hy4 : orderOf y = 4 := by rw [hy, orderOf_conj', hc4]
  have hQnab : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    refine ⟨x * a * x⁻¹, (mem_map_conj_iff _ _ _).mpr (by simpa only [conj_conj_inv] using ha),
      x * b * x⁻¹, (mem_map_conj_iff _ _ _).mpr (by simpa only [conj_conj_inv] using hb),
      fun h => hab ?_⟩
    have h2 : x * (a * b) * x⁻¹ = x * (b * a) * x⁻¹ := by
      calc x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) := by group
        _ = x * b * x⁻¹ * (x * a * x⁻¹) := h
        _ = x * (b * a) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have heY : e ∈ zpowers y := mem_zpowers_of_central hQ16 hQnab hyQ hy4 hyc heQ hQE
  have hey : e = y ^ 2 := eq_sq_of_mem_zpowers hy4 heY he2
  have hyC : y ∈ C := mem_of_central_of_index_two hCQ hQ16 hC8 hCcomm hQnab hyQ hyc
  obtain ⟨i, hi⟩ := hCsq y hyC
  rw [← hey] at hi
  rcases zpow_eq_one_or_self hz₀ i with h | h
  · rw [h] at hi
    rw [hi] at he2
    simp at he2
  · rw [h] at hi
    exact hgne hi

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl
