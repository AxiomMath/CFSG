module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure P4Data (L M T S P : Subgroup G) (t z w : G) : Prop where
  c : Conf L M T S P t z
  hNS : normalizer (S : Set G) ≤ centralizer ({z} : Set G)
  hSG : IsSylowOf 2 S ⊤
  hwM : w ∈ M
  hwS : w ∈ S
  hw : orderOf w = 2
  hwc : ∀ s ∈ S, s * w = w * s
  hwF : w ∈ footeF L t
  hzw : ¬ IsConj z w
  hzzw : ¬ IsConj z (z * w)
  hwzw : ¬ IsConj w (z * w)
  ht2c : ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → ¬ IsConj t x

theorem exists_mem_normalizer_of_isConj {S : Subgroup G} (hSG : IsSylowOf 2 S ⊤) {x y : G}
    (hx : ∀ s ∈ S, s * x = x * s) (hy : ∀ s ∈ S, s * y = y * s) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (S : Set G), y = n⁻¹ * x * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSp, hidx⟩ := isSylowOf_iff.mp hSG
  rw [Subgroup.relIndex_top_right] at hidx
  set S' := hSp.toSylow hidx with hS'
  have hS'S : (S' : Subgroup G) = S := IsPGroup.toSylow_coe hSp hidx
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hmem : ∀ s, s ∈ (S' : Set G) → s ∈ S := fun s hs => by
    have hs' : s ∈ (S' : Subgroup G) := hs
    rwa [hS'S] at hs'
  have hxC : x ∈ centralizer (S' : Set G) := mem_centralizer_iff.mpr fun s hs => hx s (hmem s hs)
  have hyC : c⁻¹⁻¹ * x * c⁻¹ ∈ centralizer (S' : Set G) := by
    rw [inv_inv, hc]
    exact mem_centralizer_iff.mpr fun s hs => hy s (hmem s hs)
  obtain ⟨n, hn, hny⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S' x c⁻¹ hxC hyC
  rw [inv_inv, hc] at hny
  change n ∈ normalizer ((S' : Subgroup G) : Set G) at hn
  rw [hS'S] at hn
  exact ⟨n, hn, hny⟩

theorem exists_central_involution_not_isConj_of_normalizer_le_of_involution_mem
    {M S K : Subgroup G} {z : G}
    (hSN : S ≤ normalizer (M : Set G))
    (hSz : IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hNS : normalizer (S : Set G) ≤ centralizer ({z} : Set G))
    (hSM : S ⊓ M ≠ ⊥) (hzM : z ∉ M)
    (hKM : K ≤ M)
    (hKN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKmem : ∀ u ∈ M ⊓ centralizer ({z} : Set G), orderOf u = 2 → u ∈ K) :
    IsSylowOf 2 S ⊤ ∧ ∃ w : G, w ∈ S ∧ w ∈ M ∧ orderOf w = 2 ∧
      (∀ s ∈ S, s * w = w * s) ∧ w ∈ K ∧
      ¬ IsConj z w ∧ ¬ IsConj z (z * w) ∧ ¬ IsConj w (z * w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSG : IsSylowOf 2 S ⊤ :=
    isSylowOf_of_normalizer_le hSz le_top (inf_le_right.trans hNS)
  obtain ⟨w, hwS, hwM, hw, hwc⟩ :=
    FooteLit.exists_involution_central_of_le_normalizer hSz.isPGroup hSN hSM
  have hzc : ∀ s ∈ S, s * z = z * s := fun s hs =>
    mem_centralizer_singleton_iff.mp (hSz.le hs)
  have hwK : w ∈ K := hKmem w (mem_inf.mpr ⟨hwM, hSz.le hwS⟩) hw
  have hzwc : ∀ s ∈ S, s * (z * w) = (z * w) * s := fun s hs => by
    rw [← mul_assoc, hzc s hs, mul_assoc, hwc s hs, mul_assoc]
  have hnz : ∀ n ∈ normalizer (S : Set G), n⁻¹ * z * n = z := fun n hn => by
    have h1 := mem_centralizer_singleton_iff.mp (hNS hn)
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  have hw1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hw; omega
  refine ⟨hSG, w, hwS, hwM, hw, hwc, hwK, ?_, ?_, ?_⟩
  · intro hzw
    obtain ⟨n, hn, hnw⟩ := exists_mem_normalizer_of_isConj hSG hzc hwc hzw
    rw [hnz n hn] at hnw
    exact hzM (hnw ▸ hwM)
  · intro hzw
    obtain ⟨n, hn, hnw⟩ := exists_mem_normalizer_of_isConj hSG hzc hzwc hzw
    rw [hnz n hn] at hnw
    exact hw1 (by
      calc w = z⁻¹ * (z * w) := by group
        _ = 1 := by rw [hnw]; group)
  · intro hwzw
    obtain ⟨n, hn, hnw⟩ := exists_mem_normalizer_of_isConj hSG hwc hzwc hwzw
    have hnK : n⁻¹ ∈ normalizer (K : Set G) := hKN (inv_mem (hNS hn))
    have h1 : n⁻¹ * w * n ∈ K := by
      have := (mem_normalizer_iff.mp hnK w).mp hwK
      rwa [inv_inv] at this
    rw [← hnw] at h1
    apply hzM
    have h2 : z = (z * w) * w⁻¹ := by group
    rw [h2]
    exact mul_mem (hKM h1) (inv_mem hwM)

theorem exists_central_involution_not_isConj_of_normalizer_le {M S : Subgroup G} {z : G}
    (hSN : S ≤ normalizer (M : Set G))
    (hSz : IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hNS : normalizer (S : Set G) ≤ centralizer ({z} : Set G))
    (hSM : S ⊓ M ≠ ⊥) (hzM : z ∉ M)
    (hfix : footeFixed M z ≤ M)
    (hfixN : centralizer ({z} : Set G) ≤ normalizer (footeFixed M z : Set G)) :
    IsSylowOf 2 S ⊤ ∧ ∃ w : G, w ∈ S ∧ w ∈ M ∧ orderOf w = 2 ∧
      (∀ s ∈ S, s * w = w * s) ∧ w ∈ footeFixed M z ∧
      ¬ IsConj z w ∧ ¬ IsConj z (z * w) ∧ ¬ IsConj w (z * w) := by
  exact exists_central_involution_not_isConj_of_normalizer_le_of_involution_mem
    hSN hSz hNS hSM hzM hfix hfixN
    (fun u hu hu2 => subset_closure ⟨mem_sup_left hu, 1, by rw [hu2, pow_one]⟩)

theorem not_isConj_of_isSylowOf_centralizer_of_twoData {S T P : Subgroup G} {t z : G}
    {Q₀ : Subgroup G}
    (hP : P = S ⊓ centralizer ({t} : Set G))
    (hPsyl : IsSylowOf 2 P (centralizer ({t} : Set G)))
    (hTS : T ≤ S) (htT : t ∈ T) (ht : orderOf t = 2)
    (hd : TwoData T t z Q₀) (hSp : IsPGroup 2 S) :
    ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → ¬ IsConj t x := by
  intro x hxS hxc htx
  obtain ⟨g, hg⟩ := isConj_iff.mp htx
  have hSt : conjugate S g ≤ centralizer ({t} : Set G) := by
    intro y hy
    have hy' := mem_conjugate_iff.mp hy
    have h1 := hxc _ hy'
    rw [← hg] at h1
    rw [mem_centralizer_singleton_iff]
    calc y * t = g⁻¹ * ((g * y * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = t * y := by group
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hPsyl hSt (hSp.map _)
  have hcard : Nat.card S ≤ Nat.card P := by
    have h1 := Subgroup.card_le_of_le (conjugate_le_of_forall hk)
    rwa [card_conjugate_eq_card, card_conjugate_eq_card] at h1
  have hPS : P ≤ S := hP ▸ inf_le_left
  have hPeq : P = S := Subgroup.eq_of_le_of_card_ge hPS hcard
  have htc : ∀ y ∈ T, t * y = y * t := fun y hy => by
    have h1 : y ∈ P := hPeq ▸ hTS hy
    rw [hP] at h1
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2).symm
  exact hd.t_ne_z (hd.hzZ t htT ht htc)

theorem exists_p4Data (h : FooteSec4 G L) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFG : Foote47FourgroupGeneration)
    {M T S P : Subgroup G} {t z : G} (c : Conf L M T S P t z) :
    ∃ w : G, P4Data L M T S P t z w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hd⟩ := c.hd
  have hNS := c.normalizer_le_centralizer_of_conf h hA5 hE8 hK hcalc hFG
  have hTS : T ≤ S := c.hT ▸ inf_le_left
  have hSp : IsPGroup 2 S := c.hSz.isPGroup
  have hRM : IsSylowOf 2 (S ⊓ M) M := c.hSN.inf_of_le_normalizer le_normalizer le_rfl
  have hRne : S ⊓ M ≠ ⊥ := by
    intro hb
    have hev : 2 ∣ Nat.card M := by
      by_contra hodd
      exact c.hv.hM.not_odd h (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
    obtain ⟨⟨v, hvM⟩, hv⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 hev
    have hv2 : orderOf v = 2 := by rw [← hv, Subgroup.orderOf_mk]
    have hvp : IsPGroup 2 (zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hRM (zpowers_le.mpr hvM) hvp
    have h1 := hk v (mem_zpowers v)
    rw [hb, mem_bot] at h1
    have h2 : v = 1 := by
      calc v = k * (k⁻¹ * v * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [h2, orderOf_one] at hv2
    omega
  have dz := zData_of h c.hv.hM c.hTsyl hd.hz hd.hzT hd.hzc
  have hzM : z ∉ M := by
    intro hzM
    have h1 := hd.hz
    have hzO := c.hv.hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hzM, dz.hzC⟩)
    have hzp : IsPGroup 2 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
    have h2 := eq_one_of_mem_of_odd hzp (odd_card_oddCoreIn M) (mem_zpowers z) hzO
    rw [h2, orderOf_one] at h1
    omega
  have hfixed : footeFixed M z = footeF L z :=
    (foote_lemma_4_5_i h c.hv.hM hd.hz dz.hzC).1
  obtain ⟨hSG, w, hwS, hwM, hw, hwc, _, hzw, hzzw, hwzw⟩ :=
    exists_central_involution_not_isConj_of_normalizer_le c.hSN.le c.hSz hNS hRne hzM
      (by rw [hfixed]; exact dz.hKM)
      (by rw [hfixed]; exact dz.centralizer_le_normalizer h)
  have hwF : w ∈ footeF L t := by
    rw [← (foote_lemma_4_5_i h c.hv.hM c.hv.ht c.hv.htC).1]
    exact subset_closure ⟨mem_sup_left ⟨hwM, mem_centralizer_singleton_iff.mpr
      (hwc t (hTS c.htT)).symm⟩, 1, by rw [hw, pow_one]⟩
  refine ⟨w, ⟨c, hNS, hSG, hwM, hwS, hw, hwc, hwF, hzw, hzzw, hwzw, ?_⟩⟩
  exact not_isConj_of_isSylowOf_centralizer_of_twoData c.hP c.hPsyl hTS c.htT c.hv.ht hd hSp

end CFSG.ComponentClassification.Foote47
