module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.GH74.GLS.C3.Prop121

open MulAction Pointwise

variable {M : Type*} [Group M]

theorem zpowers_normal_of_central {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) :
    (Subgroup.zpowers t₀).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have : Commute g t₀ := hc g
  have h2 : g * t₀ ^ i * g⁻¹ = t₀ ^ i := by
    have := (this.zpow_right i).eq
    calc g * t₀ ^ i * g⁻¹ = (t₀ ^ i * g) * g⁻¹ := by rw [← this]
      _ = t₀ ^ i := by group
  rw [h2]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t₀) i

theorem card_zpowers_three {t₀ : M} (ht₃ : t₀ ^ 3 = 1) (ht₁ : t₀ ≠ 1) :
    Nat.card ↥(Subgroup.zpowers t₀) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime ht₃ ht₁

theorem odd_comap_of_odd [Finite M] (N : Subgroup M) [N.Normal] (hN : ∀ n ∈ N, n ^ 3 = 1)
    {Kbar : Subgroup (M ⧸ N)} (h : Odd (Nat.card Kbar)) :
    Odd (Nat.card (Kbar.comap (QuotientGroup.mk' N))) := by
  classical
  by_contra hnot
  have h2 : 2 ∣ Nat.card (Kbar.comap (QuotientGroup.mk' N)) := by
    rcases Nat.even_or_odd (Nat.card (Kbar.comap (QuotientGroup.mk' N))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hnot
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kbar.comap (QuotientGroup.mk' N)) 2 h2
  have hc2 : (c : M) ^ 2 = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  have hc1 : (c : M) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    omega
  have himg : QuotientGroup.mk' N (c : M) ∈ Kbar := c.2
  have h3 : (⟨QuotientGroup.mk' N (c : M), himg⟩ : Kbar) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hc2, map_one]
  have h4 : orderOf (⟨QuotientGroup.mk' N (c : M), himg⟩ : Kbar) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one h3
  have h5 : orderOf (⟨QuotientGroup.mk' N (c : M), himg⟩ : Kbar) ∣ Nat.card Kbar :=
    orderOf_dvd_natCard _
  have h6 : orderOf (⟨QuotientGroup.mk' N (c : M), himg⟩ : Kbar) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h7 | h7
    · exact h7
    · exfalso
      rw [h7] at h5
      exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 h5)
  have h7 : (⟨QuotientGroup.mk' N (c : M), himg⟩ : Kbar) = 1 := orderOf_eq_one_iff.1 h6
  have h8 : ((c : M) : M ⧸ N) = 1 := congrArg Subtype.val h7
  have h9 : (c : M) ∈ N := (QuotientGroup.eq_one_iff (c : M)).1 h8
  have h10 := hN _ h9
  apply hc1
  calc (c : M) = (c : M) ^ 3 * ((c : M) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h10, hc2]; group

theorem exists_lift_involution (N : Subgroup M) [N.Normal] (hN : ∀ n ∈ N, n ^ 3 = 1)
    {a : M ⧸ N} (ha : orderOf a = 2) :
    ∃ α : M, orderOf α = 2 ∧ QuotientGroup.mk' N α = a := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective a
  have ha2 : ((c : M ⧸ N)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((c : M ⧸ N))
    rwa [ha] at this
  have hc2N : c ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ha2
  have h6 : c ^ 6 = 1 := by
    have := hN _ hc2N
    calc c ^ 6 = (c ^ 2) ^ 3 := by group
      _ = 1 := this
  refine ⟨c ^ 3, ?_, ?_⟩
  · have h1 : (c ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact h6
    have h2 : c ^ 3 ≠ 1 := by
      intro h3
      have : ((c ^ 3 : M) : M ⧸ N) = 1 := by rw [h3]; rfl
      rw [QuotientGroup.mk_pow] at this
      have h4 : ((c : M ⧸ N)) = ((c : M ⧸ N)) ^ 3 := by
        calc ((c : M ⧸ N)) = ((c : M ⧸ N)) ^ 3 * (((c : M ⧸ N)) ^ 2)⁻¹ := by group
          _ = ((c : M ⧸ N)) ^ 3 := by rw [ha2]; group
      rw [this] at h4
      have : orderOf ((c : M ⧸ N)) = 1 := orderOf_eq_one_iff.2 h4
      omega
    exact orderOf_eq_prime h1 h2
  · show ((c ^ 3 : M) : M ⧸ N) = (c : M ⧸ N)
    rw [QuotientGroup.mk_pow]
    calc ((c : M ⧸ N)) ^ 3 = ((c : M ⧸ N)) ^ 2 * (c : M ⧸ N) := by group
      _ = (c : M ⧸ N) := by rw [ha2, one_mul]

theorem isConj_of_involutions (N : Subgroup M) [N.Normal] (hN : ∀ n ∈ N, n ^ 3 = 1)
    (hone : ∀ α β : M, orderOf α = 2 → orderOf β = 2 → IsConj α β)
    {a b : M ⧸ N} (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨α, hα, rfl⟩ := exists_lift_involution N hN ha
  obtain ⟨β, hβ, rfl⟩ := exists_lift_involution N hN hb
  exact (QuotientGroup.mk' N).map_isConj (hone α β hα hβ)

theorem card_centralizer_image [Finite M] (t₀ : M) (ht₃ : t₀ ^ 3 = 1) (ht₁ : t₀ ≠ 1)
    (hc : ∀ m : M, m * t₀ = t₀ * m) [(Subgroup.zpowers t₀).Normal] {z : M} (hz : z * z = 1) :
    Nat.card (Subgroup.centralizer ({z} : Set M)) =
      3 * Nat.card (Subgroup.centralizer ({QuotientGroup.mk' (Subgroup.zpowers t₀) z} :
        Set (M ⧸ Subgroup.zpowers t₀))) := by
  classical
  let N := Subgroup.zpowers t₀
  let η : M →* M ⧸ N := QuotientGroup.mk' N
  let C := Subgroup.centralizer ({z} : Set M)
  let φ : ↥C →* M ⧸ N := η.comp C.subtype
  have hord : orderOf t₀ = 3 := orderOf_eq_prime ht₃ ht₁
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzt : Commute z t₀ := hc z
  have hNC : ∀ n ∈ N, n ∈ C := by
    intro n hn
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzt.symm.zpow_left i).eq
  have hrange : φ.range = Subgroup.centralizer ({η z} : Set (M ⧸ N)) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcz : (c : M) * z = z * (c : M) := Subgroup.mem_centralizer_singleton_iff.1 c.2
      show η (c : M) * η z = η z * η (c : M)
      rw [← map_mul, ← map_mul, hcz]
    · intro hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : η c * η z = η z * η c := Subgroup.mem_centralizer_singleton_iff.1 hy
      have h2 : η (c * z * c⁻¹ * z⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h3 : c * z * c⁻¹ * z⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).1 h2
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h3
      have h4 : c * z * c⁻¹ = t₀ ^ i * z := by
        calc c * z * c⁻¹ = (c * z * c⁻¹ * z⁻¹) * z := by group
          _ = t₀ ^ i * z := by rw [← hi]
      have h5 : (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
        calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
          _ = 1 := by rw [hz]; group
      have hcomm : z * t₀ ^ i = t₀ ^ i * z := (hzt.zpow_right i).eq
      have h6 : t₀ ^ (2 * i) = 1 := by
        have h7 : t₀ ^ i * z * (t₀ ^ i * z) = t₀ ^ (2 * i) * (z * z) := by
          calc t₀ ^ i * z * (t₀ ^ i * z) = t₀ ^ i * (z * t₀ ^ i) * z := by group
            _ = t₀ ^ i * (t₀ ^ i * z) * z := by rw [hcomm]
            _ = t₀ ^ (2 * i) * (z * z) := by
              rw [two_mul, zpow_add]; group
        rw [h4] at h5
        rw [h7, hz, mul_one] at h5
        exact h5
      have h8 : (3 : ℤ) ∣ 2 * i := by
        have := (orderOf_dvd_iff_zpow_eq_one (x := t₀) (i := 2 * i)).2 h6
        rwa [hord] at this
      have h9 : (3 : ℤ) ∣ i := by omega
      have h10 : t₀ ^ i = 1 := by
        have := (orderOf_dvd_iff_zpow_eq_one (x := t₀) (i := i)).1 (by rwa [hord])
        exact this
      have h11 : c * z = z * c := by
        rw [h10, one_mul] at h4
        calc c * z = (c * z * c⁻¹) * c := by group
          _ = z * c := by rw [h4]
      exact ⟨⟨c, Subgroup.mem_centralizer_singleton_iff.2 h11⟩, rfl⟩
  have hker : Nat.card φ.ker = 3 := by
    have : Nat.card φ.ker = Nat.card N := by
      refine Nat.card_congr
        { toFun := fun c => ⟨(c.1 : M), ?_⟩
          invFun := fun n => ⟨⟨n.1, hNC n.1 n.2⟩, ?_⟩
          left_inv := fun c => rfl
          right_inv := fun n => rfl }
      · have h1 : φ c.1 = 1 := c.2
        exact (QuotientGroup.eq_one_iff _).1 h1
      · show φ ⟨n.1, hNC n.1 n.2⟩ = 1
        exact (QuotientGroup.eq_one_iff _).2 n.2
    rw [this, Nat.card_zpowers, hord]
  have h1 := Subgroup.index_mul_card φ.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [← h1]
  ring

theorem map_equiv_of_inf_zpowers_eq_bot (N : Subgroup M) [N.Normal] {K : Subgroup M}
    (hK : ∀ k ∈ K, k ∈ N → k = 1) : Nonempty (↥K ≃* ↥(K.map (QuotientGroup.mk' N))) := by
  let φ : ↥K →* M ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 : QuotientGroup.mk' N (k : M) = 1 := hk
    have h2 : (k : M) ∈ N := (QuotientGroup.eq_one_iff (k : M)).1 h1
    have h3 := hK _ k.2 h2
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  have hr : φ.range = K.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)⟩

theorem sylow_image [Finite M] (N : Subgroup M) [N.Normal] (hN : ∀ n ∈ N, n ^ 3 = 1)
    (hN3 : Nat.card N = 3) {D : Subgroup M} (hD : IsPGroup 2 D) (hS : ¬ 2 ∣ D.index) :
    ∃ S : Sylow 2 (M ⧸ N), (S : Subgroup (M ⧸ N)) = D.map (QuotientGroup.mk' N) ∧
      Nonempty (↥D ≃* ↥(D.map (QuotientGroup.mk' N))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDN : ∀ k ∈ D, k ∈ N → k = 1 := by
    intro k hkD hkN
    have h3 : k ^ 3 = 1 := hN k hkN
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hD) ⟨k, hkD⟩
    have h4 : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h5 : orderOf k = 2 ^ m := by
      rw [← hm, Subgroup.orderOf_mk]
    rw [h5] at h4
    have h6 : m = 0 := by
      by_contra hm0
      have : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
      have h7 : 2 ∣ 3 := this.trans h4
      omega
    rw [h6, pow_zero] at h5
    exact orderOf_eq_one_iff.1 h5
  obtain ⟨e⟩ := map_equiv_of_inf_zpowers_eq_bot N hDN
  have hpg : IsPGroup 2 ↥(D.map (QuotientGroup.mk' N)) := hD.of_equiv e
  have hcardD : Nat.card ↥(D.map (QuotientGroup.mk' N)) = Nat.card D :=
    (Nat.card_congr e.toEquiv).symm
  have hM : Nat.card (M ⧸ N) * 3 = Nat.card M := by
    have := Subgroup.index_mul_card N
    rw [hN3, Subgroup.index_eq_card] at this
    exact this
  have h1 := Subgroup.index_mul_card D
  have h2 := Subgroup.index_mul_card (D.map (QuotientGroup.mk' N))
  rw [hcardD] at h2
  have hind : D.index = 3 * (D.map (QuotientGroup.mk' N)).index := by
    have hpos : 0 < Nat.card D := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc D.index * Nat.card D = Nat.card M := h1
      _ = Nat.card (M ⧸ N) * 3 := hM.symm
      _ = 3 * (Nat.card (M ⧸ N)) := by ring
      _ = 3 * ((D.map (QuotientGroup.mk' N)).index * Nat.card D) := by rw [h2]
      _ = (3 * (D.map (QuotientGroup.mk' N)).index) * Nat.card D := by ring
  have hS' : ¬ 2 ∣ (D.map (QuotientGroup.mk' N)).index := by
    intro h2'
    apply hS
    rw [hind]
    exact Dvd.dvd.mul_left h2' 3
  exact ⟨hpg.toSylow hS', rfl, ⟨e⟩⟩

theorem pPrimeCore_eq_bot_of_forall [Finite M] (N : Subgroup M) [N.Normal]
    (hN : ∀ n ∈ N, n ^ 3 = 1)
    (hodd : ∀ R : Subgroup M, Odd (Nat.card R) → (∀ m : M, ∀ r ∈ R, m * r * m⁻¹ ∈ R) → R ≤ N) :
    CFSG.pPrimeCore 2 (M ⧸ N) = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro Kbar hKn hcop
  have hodd' : Odd (Nat.card Kbar) := Nat.coprime_two_left.1 hcop
  have hR := odd_comap_of_odd N hN hodd'
  have hRn : ∀ m : M, ∀ r ∈ Kbar.comap (QuotientGroup.mk' N),
      m * r * m⁻¹ ∈ Kbar.comap (QuotientGroup.mk' N) := by
    intro m r hr
    rw [Subgroup.mem_comap] at hr ⊢
    rw [map_mul, map_mul, map_inv]
    exact hKn.conj_mem _ hr _
  have hle := hodd _ hR hRn
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
  have hc : c ∈ Kbar.comap (QuotientGroup.mk' N) := hy
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff c).2 (hle hc))

theorem mem_smul_sylow_iff {p : ℕ} [Fact p.Prime] (P : Sylow p M) (g : M) (x : M) :
    x ∈ ((g • P : Sylow p M) : Subgroup M) ↔ g⁻¹ * x * g ∈ (P : Subgroup M) := by
  show x ∈ (MulAut.conj g • (P : Subgroup M)) ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem isConj_of_sylow [Finite M] (P : Sylow 2 M)
    (h : ∀ α ∈ (P : Subgroup M), ∀ β ∈ (P : Subgroup M), orderOf α = 2 → orderOf β = 2 →
      IsConj α β) :
    ∀ α β : M, orderOf α = 2 → orderOf β = 2 → IsConj α β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ α : M, orderOf α = 2 → ∃ α' ∈ (P : Subgroup M), orderOf α' = 2 ∧ IsConj α α' := by
    intro α hα
    have hpg : IsPGroup 2 (Subgroup.zpowers α) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hα]; norm_num
    obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
    obtain ⟨g, hg⟩ := exists_smul_eq M P Q
    have hαQ : α ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers α)
    rw [← hg, mem_smul_sylow_iff] at hαQ
    refine ⟨g⁻¹ * α * g, hαQ, ?_, ?_⟩
    · rw [← hα]
      have : g⁻¹ * α * g = (MulAut.conj g⁻¹) α := by simp
      rw [this]
      exact MulEquiv.orderOf_eq _ _
    · exact (isConj_iff.2 ⟨g⁻¹, by simp [mul_assoc]⟩)
  intro α β hα hβ
  obtain ⟨α', hα'P, hα'o, hα'c⟩ := key α hα
  obtain ⟨β', hβ'P, hβ'o, hβ'c⟩ := key β hβ
  exact hα'c.trans ((h α' hα'P β' hβ'P hα'o hβ'o).trans hβ'c.symm)

theorem normalizer_centralizes_of_center {D : Subgroup M}
    (e : ↥D ≃* DihedralGroup 4) {z : M} (hzD : z ∈ D) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hDz : ∀ d ∈ D, d * z = z * d) :
    ∀ m ∈ Subgroup.normalizer (D : Set M), m * z = z * m := by
  classical
  intro m hm
  rw [Subgroup.mem_normalizer_iff] at hm
  have : Finite ↥D := Finite.of_equiv _ e.symm.toEquiv
  have hcenter : Nat.card (Subgroup.center ↥D) = 2 := by
    have h1 : Nat.card (Subgroup.center ↥D) = Nat.card (Subgroup.center (DihedralGroup 4)) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [h1, DihedralGroup.center_eq_closure_of_even_ne_two (by decide) (by decide), Nat.card_zpowers,
      DihedralGroup.orderOf_r]
    decide
  let zD : ↥D := ⟨z, hzD⟩
  have hzDc : zD ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (hDz d.1 d.2)
  have hzD1 : zD ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzD2 : zD * zD = 1 := Subtype.ext hzz
  have hord : orderOf zD = 2 := by
    refine orderOf_eq_prime ?_ hzD1
    rw [sq]; exact hzD2
  have hzp : Subgroup.zpowers zD = Subgroup.center ↥D := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact (Subgroup.zpowers_le).2 hzDc
    · rw [hcenter, Nat.card_zpowers, hord]
  have hyD : m * z * m⁻¹ ∈ D := (hm z).1 hzD
  let yD : ↥D := ⟨m * z * m⁻¹, hyD⟩
  have hyDc : yD ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro d
    have hd' : m⁻¹ * (d : M) * m ∈ D := by
      have := (hm (m⁻¹ * (d : M) * m)).2
      have e : m * (m⁻¹ * (d : M) * m) * m⁻¹ = (d : M) := by group
      rw [e] at this
      exact this d.2
    apply Subtype.ext
    show (d : M) * (m * z * m⁻¹) = (m * z * m⁻¹) * (d : M)
    have h1 := hDz _ hd'
    calc (d : M) * (m * z * m⁻¹) = m * ((m⁻¹ * (d : M) * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * (d : M) * m)) * m⁻¹ := by rw [h1]
      _ = (m * z * m⁻¹) * (d : M) := by group
  rw [← hzp] at hyDc
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hyDc
  have hy : m * z * m⁻¹ = z ^ i := congrArg Subtype.val hi.symm
  have hy1 : m * z * m⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  have hzi : z ^ i = z ^ (i % 2) := by
    have h := Int.mul_ediv_add_emod i 2
    calc z ^ i = z ^ (2 * (i / 2) + i % 2) := by rw [h]
      _ = z ^ (i % 2) := by rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul]
  have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hyz : m * z * m⁻¹ = z := by
    rcases hmod with h0 | h1
    · exfalso
      apply hy1
      rw [hy, hzi, h0, zpow_zero]
    · rw [hy, hzi, h1, zpow_one]
  calc m * z = (m * z * m⁻¹) * m := by group
    _ = z * m := by rw [hyz]

end CFSG.GH74.GLS.C3.Prop121
