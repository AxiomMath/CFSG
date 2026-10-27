module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8)
open scoped Pointwise

theorem quaternion_sq_one_central (q g : QuaternionGroup 2) (hq : q ^ 2 = 1) :
    g * q = q * g := by
  revert q g
  decide

theorem exists_central_involution_of_Q8D8 {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (h : smallRankIsQ8D8 R) : ∃ c ∈ R, c ≠ 1 ∧ c ^ 2 = 1 ∧ ∀ r ∈ R, c * r = r * c := by
  obtain ⟨A, B, ⟨eA⟩, -, hcomm, hsup, hcard⟩ := h
  have hI : A ⊓ B ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨c', hc'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI
  have hc2' : c' ^ 2 = 1 := by
    have hord : orderOf c' ∣ 2 := by
      have := orderOf_dvd_natCard c'
      rwa [hcard] at this
    have hne : orderOf c' ≠ 1 := fun h1 => hc' (orderOf_eq_one_iff.mp h1)
    have h2 : orderOf c' = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h3 | h3
      · exact absurd h3 hne
      · exact h3
    rw [← h2]
    exact pow_orderOf_eq_one c'
  have hcA : (c' : G) ∈ A := (Subgroup.mem_inf.mp c'.2).1
  have hcB : (c' : G) ∈ B := (Subgroup.mem_inf.mp c'.2).2
  have hc1 : (c' : G) ≠ 1 := fun h1 => hc' (Subtype.ext h1)
  have hc2 : (c' : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hc2'
    simpa using this
  have hcentA : ∀ a ∈ A, (c' : G) * a = a * (c' : G) := by
    intro a ha
    have hca2 : eA ⟨c', hcA⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have h0 : (⟨c', hcA⟩ : A) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
      rw [h0, map_one]
    have key := quaternion_sq_one_central (eA ⟨c', hcA⟩) (eA ⟨a, ha⟩) hca2
    have key' : (⟨c', hcA⟩ : A) * ⟨a, ha⟩ = ⟨a, ha⟩ * ⟨c', hcA⟩ := by
      apply eA.injective
      rw [map_mul, map_mul]
      exact key.symm
    exact congrArg Subtype.val key'
  have hle : A ⊔ B ≤ Subgroup.centralizer ({(c' : G)} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact mem_centralizer_singleton_iff.mpr (hcentA a ha).symm
    · exact mem_centralizer_singleton_iff.mpr (hcomm (c' : G) hcA b hb).symm
  refine ⟨(c' : G), ?_, hc1, hc2, fun r hr => ?_⟩
  · rw [← hsup]
    exact Subgroup.mem_sup_left hcA
  · rw [← hsup] at hr
    exact (mem_centralizer_singleton_iff.mp (hle hr)).symm

theorem smallRankIsQ8D8_map {H K : Type} [Group H] [Group K] (φ : H →* K)
    (hφ : Function.Injective φ) {Q : Subgroup H} (hQ : smallRankIsQ8D8 Q) :
    smallRankIsQ8D8 (Q.map φ) := by
  obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hcomm, hsup, hcard⟩ := hQ
  refine ⟨A.map φ, B.map φ, ⟨(Subgroup.equivMapOfInjective A φ hφ).symm.trans eA⟩,
    ⟨(Subgroup.equivMapOfInjective B φ hφ).symm.trans eB⟩, ?_, ?_, ?_⟩
  · intro a' ha' b' hb'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_sup, hsup]
  · rw [← Subgroup.map_inf_eq A B φ hφ, Subgroup.card_map_of_injective hφ]
    exact hcard

theorem smallRankIsQ8D8_of_map {H K : Type} [Group H] [Group K] (φ : H →* K)
    (hφ : Function.Injective φ) {Q : Subgroup H} (hQ : smallRankIsQ8D8 (Q.map φ)) :
    smallRankIsQ8D8 Q := by
  obtain ⟨A', B', ⟨eA⟩, ⟨eB⟩, hcomm, hsup, hcard⟩ := hQ
  have hA'le : A' ≤ Q.map φ := hsup ▸ le_sup_left
  have hB'le : B' ≤ Q.map φ := hsup ▸ le_sup_right
  have hrange : Q.map φ ≤ φ.range := Subgroup.map_le_range φ Q
  have hAr : (A'.comap φ).map φ = A' := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hA'le.trans hrange)]
  have hBr : (B'.comap φ).map φ = B' := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hB'le.trans hrange)]
  refine ⟨A'.comap φ, B'.comap φ,
    ⟨(Subgroup.equivMapOfInjective (A'.comap φ) φ hφ).trans
      ((MulEquiv.subgroupCongr hAr).trans eA)⟩,
    ⟨(Subgroup.equivMapOfInjective (B'.comap φ) φ hφ).trans
      ((MulEquiv.subgroupCongr hBr).trans eB)⟩, ?_, ?_, ?_⟩
  · intro a ha b hb
    apply hφ
    rw [map_mul, map_mul]
    exact hcomm (φ a) ha (φ b) hb
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_sup, hAr, hBr, hsup]
  · have hc := Subgroup.card_map_of_injective (K := (A'.comap φ) ⊓ (B'.comap φ)) hφ
    rw [← hc, Subgroup.map_inf_eq _ _ φ hφ, hAr, hBr]
    exact hcard

theorem smallRankIsQ8D8_map_of_injOn {H K : Type} [Group H] [Group K] (φ : H →* K)
    (Q : Subgroup H) (hφ : ∀ x ∈ Q, ∀ y ∈ Q, φ x = φ y → x = y) (hQ : smallRankIsQ8D8 Q) :
    smallRankIsQ8D8 (Q.map φ) := by
  have hmap_top : (⊤ : Subgroup Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQ' : smallRankIsQ8D8 (⊤ : Subgroup Q) :=
    smallRankIsQ8D8_of_map Q.subtype Q.subtype_injective (by rw [hmap_top]; exact hQ)
  have hinj : Function.Injective (φ.comp Q.subtype) := fun x y hxy =>
    Subtype.ext (hφ x.1 x.2 y.1 y.2 hxy)
  have h := smallRankIsQ8D8_map (φ.comp Q.subtype) hinj hQ'
  have hcomp : (⊤ : Subgroup Q).map (φ.comp Q.subtype) = Q.map φ := by
    rw [← Subgroup.map_map, hmap_top]
  rw [hcomp] at h
  exact h

theorem mem_zpowers_of_sq_one {H : Type} [Group H] {c e : H} (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (he : e ∈ zpowers c) : e = 1 ∨ e = c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoc : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  have hmod : c ^ k = c ^ (k % (orderOf c : ℤ)) := (zpow_mod_orderOf c k).symm
  rw [hoc] at hmod
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    push_cast
    exact Int.emod_two_eq_zero_or_one k
  rw [hmod]
  rcases hk with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_conj_of_involution {Γ : Type} [Group Γ] [Finite Γ] {a b : Γ}
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1)
    (hia : ¬ 2 ∣ (zpowers a).index) (hib : ¬ 2 ∣ (zpowers b).index) :
    ∃ g : Γ, g * a * g⁻¹ = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoa : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hob : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hpa : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoa]; norm_num)
  have hpb : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hob]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hpa.toSylow hia) (hpb.toSylow hib)
  have hgs : MulAut.conj g • zpowers a = zpowers b := by
    have h1 : ((g • hpa.toSylow hia : Sylow 2 Γ) : Subgroup Γ) = zpowers b := by
      rw [hg]
      rfl
    exact h1
  refine ⟨g, ?_⟩
  have hmem : g * a * g⁻¹ ∈ zpowers b := by
    rw [← hgs]
    have := Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (zpowers a) (mem_zpowers a)
    simpa using this
  rcases mem_zpowers_of_sq_one hb2 hb1 hmem with h | h
  · exfalso
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group
  · exact h

theorem card_sup_zpowers {H : Type} [Group H] [Finite H] (C : Subgroup H) [C.Normal] {c : H}
    (hc2 : c ^ 2 = 1) (hcC : c ∉ C) :
    Nat.card ↥(C ⊔ zpowers c) = 2 * Nat.card C := by
  have hc1 : c ≠ 1 := fun h1 => hcC (h1 ▸ C.one_mem)
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hcΓ : c ∈ C ⊔ zpowers c := Subgroup.mem_sup_right (mem_zpowers c)
  have hCΓ : C ≤ C ⊔ zpowers c := le_sup_left
  have hidx : (C.subgroupOf (C ⊔ zpowers c)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hcΓ⟩, fun b => ?_⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp b.2
    rcases mem_zpowers_of_sq_one hc2 hc1 hz with h | h
    ·
      rw [h, mul_one] at hyz
      have hb : (b : H) = y := hyz.symm
      have h1 : b ∈ C.subgroupOf (C ⊔ zpowers c) := by
        rw [Subgroup.mem_subgroupOf, hb]
        exact hy
      have h2 : (b * (⟨c, hcΓ⟩ : ↥(C ⊔ zpowers c))) ∉ C.subgroupOf (C ⊔ zpowers c) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hb]
        intro hmem
        apply hcC
        have hc' : c = y⁻¹ * (y * c) := by group
        rw [hc']
        exact C.mul_mem (C.inv_mem hy) hmem
      simp [h1, h2]
    ·
      rw [h] at hyz
      have hb : (b : H) = y * c := hyz.symm
      have h1 : b ∉ C.subgroupOf (C ⊔ zpowers c) := by
        rw [Subgroup.mem_subgroupOf, hb]
        intro hmem
        apply hcC
        have hc' : c = y⁻¹ * (y * c) := by group
        rw [hc']
        exact C.mul_mem (C.inv_mem hy) hmem
      have h2 : (b * (⟨c, hcΓ⟩ : ↥(C ⊔ zpowers c))) ∈ C.subgroupOf (C ⊔ zpowers c) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hb, mul_assoc, hcc, mul_one]
        exact hy
      simp [h1, h2]
  have hcard := Subgroup.index_mul_card (H := C.subgroupOf (C ⊔ zpowers c))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCΓ).toEquiv] at hcard
  exact hcard.symm

theorem mem_mul_centralizer_of_involution {H : Type} [Group H] [Finite H] (C : Subgroup H)
    [C.Normal] (hodd : Odd (Nat.card C)) {c : H} (hc2 : c ^ 2 = 1) (hcC : c ∉ C)
    (hinv : ∀ n : H, ∃ e ∈ C, n * c * n⁻¹ = e * c) (n : H) :
    ∃ d ∈ C, ∃ m : H, m * c * m⁻¹ = c ∧ n = d * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : c ≠ 1 := fun h1 => hcC (h1 ▸ C.one_mem)
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  obtain ⟨e, he, hne⟩ := hinv n
  have hcΓ : c ∈ C ⊔ zpowers c := Subgroup.mem_sup_right (mem_zpowers c)
  have heΓ : e ∈ C ⊔ zpowers c := Subgroup.mem_sup_left he
  have htΓ : n * c * n⁻¹ ∈ C ⊔ zpowers c := by
    rw [hne]
    exact (C ⊔ zpowers c).mul_mem heΓ hcΓ
  have ht2 : (n * c * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hc2, mul_one, mul_inv_cancel]
  have ht1 : n * c * n⁻¹ ≠ 1 := by
    intro h
    apply hc1
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = n⁻¹ * 1 * n := by rw [h]
      _ = 1 := by group
  have hcard : Nat.card ↥(C ⊔ zpowers c) = 2 * Nat.card C := card_sup_zpowers C hc2 hcC
  have hidx : ∀ x : ↥(C ⊔ zpowers c), x ^ 2 = 1 → x ≠ 1 → ¬ 2 ∣ (zpowers x).index := by
    intro x hx2 hx1
    have hox : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hmul : (zpowers x).index * Nat.card (zpowers x) = Nat.card ↥(C ⊔ zpowers c) :=
      Subgroup.index_mul_card (zpowers x)
    rw [Nat.card_zpowers, hox, hcard] at hmul
    have hi : (zpowers x).index = Nat.card C := by omega
    rw [hi]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have ha2 : (⟨n * c * n⁻¹, htΓ⟩ : ↥(C ⊔ zpowers c)) ^ 2 = 1 :=
    Subtype.ext (by simpa using ht2)
  have ha1 : (⟨n * c * n⁻¹, htΓ⟩ : ↥(C ⊔ zpowers c)) ≠ 1 :=
    fun h => ht1 (congrArg Subtype.val h)
  have hb2 : (⟨c, hcΓ⟩ : ↥(C ⊔ zpowers c)) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
  have hb1 : (⟨c, hcΓ⟩ : ↥(C ⊔ zpowers c)) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_conj_of_involution ha2 ha1 hb2 hb1 (hidx _ ha2 ha1)
    (hidx _ hb2 hb1)
  have hgt : (g : H) * (n * c * n⁻¹) * (g : H)⁻¹ = c := by
    have := congrArg Subtype.val hg
    simpa using this
  obtain ⟨d₁, hd₁, z, hz, hgz⟩ := Subgroup.mem_sup_of_normal_left.mp g.2
  have hm : ((g : H) * n) * c * ((g : H) * n)⁻¹ = c := by
    calc ((g : H) * n) * c * ((g : H) * n)⁻¹ = (g : H) * (n * c * n⁻¹) * (g : H)⁻¹ := by
          group
      _ = c := hgt
  rcases mem_zpowers_of_sq_one hc2 hc1 hz with h | h
  ·
    rw [h, mul_one] at hgz
    refine ⟨d₁⁻¹, C.inv_mem hd₁, (g : H) * n, hm, ?_⟩
    rw [← hgz]
    group
  ·
    rw [h] at hgz
    refine ⟨c * d₁⁻¹ * c, ?_, c * ((g : H) * n), ?_, ?_⟩
    · have hconj := (‹C.Normal›).conj_mem d₁⁻¹ (C.inv_mem hd₁) c
      rw [hcinv] at hconj
      exact hconj
    · calc c * ((g : H) * n) * c * (c * ((g : H) * n))⁻¹
          = c * (((g : H) * n) * c * ((g : H) * n)⁻¹) * c⁻¹ := by group
        _ = c * c * c⁻¹ := by rw [hm]
        _ = c := by rw [hcinv, hcc, one_mul]
    · rw [← hgz]
      calc n = c * c * n := by rw [hcc, one_mul]
        _ = c * d₁⁻¹ * 1 * d₁ * c * n := by group
        _ = c * d₁⁻¹ * (c * c) * d₁ * c * n := by rw [hcc]
        _ = c * d₁⁻¹ * c * (c * (d₁ * c * n)) := by group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
