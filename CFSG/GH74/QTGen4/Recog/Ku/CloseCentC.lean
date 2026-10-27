module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseCentB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

variable {G : Type} [Group G]

lemma normalizer_lt_of_lt_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {H : Subgroup P} (hH : H < ⊤) :
    H < Subgroup.normalizer (H : Set P) := by
  classical
  have htop : IsPGroup p (⊤ : Subgroup P) :=
    IsPGroup.of_equiv (hG := hP) (Subgroup.topEquiv (G := P)).symm
  have hHp : IsPGroup p H := htop.to_le hH.le
  have hmod : Nat.card (P ⧸ H) ≡ Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) [MOD p] :=
    hHp.card_modEq_card_fixedPoints (α := P ⧸ H)
  have htotal : p ∣ Nat.card (P ⧸ H) := by
    rw [← Subgroup.index_eq_card]
    have hindex_ne_one : H.index ≠ 1 := by
      intro h1
      exact hH.ne' (Subgroup.index_eq_one.mp h1).symm
    rcases (hP.index H) with ⟨k, hk⟩
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hindex_ne_one
      simp [hk, hk0]
    rw [hk]
    exact dvd_pow_self p hk0
  have hfixed : p ∣ Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) :=
    Nat.modEq_zero_iff_dvd.mp ((hmod.symm).trans htotal.modEq_zero_nat)
  have hfixed_card : Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) =
      (H.comap (Subgroup.normalizer (H : Set P)).subtype).index := by
    calc
      Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) =
          Nat.card (Subgroup.normalizer (H : Set P) ⧸
            H.comap (Subgroup.normalizer (H : Set P)).subtype) := by
            exact Nat.card_congr
              (Sylow.fixedPointsMulLeftCosetsEquivQuotient (H := H))
      _ = (H.comap (Subgroup.normalizer (H : Set P)).subtype).index := by
            rw [Subgroup.index_eq_card]
  have hfixed' : p ∣ (H.subgroupOf (Subgroup.normalizer (H : Set P))).index := by
    simpa [hfixed_card, Subgroup.comap_subtype] using hfixed
  have hindex_ne_one : (H.subgroupOf (Subgroup.normalizer (H : Set P))).index ≠ 1 := by
    intro h1
    have : p ∣ (1 : ℕ) := by
      simpa [h1] using hfixed'
    exact (Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p)) this
  refine lt_of_le_of_ne H.le_normalizer ?_
  intro heq
  apply hindex_ne_one
  rw [← heq]
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.index_top

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem delta_sylow (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {S : Subgroup G}
    (hS : S ≤ Subgroup.centralizer ({x} : Set G)) (hS2 : IsPGroup 2 ↥S)
    (hΔS : kuDelta E x ≤ S) :
    S = kuDelta E x := by
  classical
  by_contra hne
  have hΔ4 : Nat.card ↥(kuDelta E x) = 4 := Ψ.card_delta hHN hxH hx
  have hlt : (kuDelta E x).subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun h => hne ?_)
    refine le_antisymm ?_ hΔS
    intro s hs
    have hmem : (⟨s, hs⟩ : ↥S) ∈ (kuDelta E x).subgroupOf S := by
      rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨n', hn'N, hn'H⟩ := IsConcreteLE.exists_of_lt
    (normalizer_lt_of_lt_of_isPGroup (p := 2) (P := ↥S) hS2 hlt)
  have hnS : (n' : G) ∈ S := n'.2
  have hnΔ : (n' : G) ∉ kuDelta E x := fun h => hn'H (Subgroup.mem_subgroupOf.mpr h)
  have hnormIff : ∀ d : G, d ∈ kuDelta E x ↔ (n' : G) * d * (n' : G)⁻¹ ∈ kuDelta E x := by
    intro d
    by_cases hdS : d ∈ S
    · have key := Subgroup.mem_normalizer_iff.mp hn'N ⟨d, hdS⟩
      simpa [Subgroup.mem_subgroupOf] using key
    · constructor
      · intro hd
        exact absurd (hΔS hd) hdS
      · intro hd
        have h1 : (n' : G) * d * (n' : G)⁻¹ ∈ S := hΔS hd
        exact absurd (by
          have : d = (n' : G)⁻¹ * ((n' : G) * d * (n' : G)⁻¹) * (n' : G) := by group
          rw [this]
          exact S.mul_mem (S.mul_mem (S.inv_mem hnS) h1) hnS) hdS
  have hnNorm : (n' : G) ∈ Subgroup.normalizer (kuDelta E x : Set G) :=
    Subgroup.mem_normalizer_iff.mpr hnormIff
  have hnK : (n' : G) ∈ Subgroup.normalizer (kuDelta E x : Set G) ⊓ S :=
    Subgroup.mem_inf.mpr ⟨hnNorm, hnS⟩
  have hKS : Subgroup.normalizer (kuDelta E x : Set G) ⊓ S ≤ S := inf_le_right
  have hKp : IsPGroup 2 ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S) :=
    hS2.to_le hKS
  have hkΔ : ∀ k : ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S), ∀ d ∈ kuDelta E x,
      (k : G) * d * (k : G)⁻¹ ∈ kuDelta E x := fun k d hd =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp k.2).1 d).mp hd
  let act : MulAction ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S) ↥(kuDelta E x) :=
    { smul := fun k d => ⟨(k : G) * (d : G) * (k : G)⁻¹, hkΔ k d d.2⟩
      one_smul := fun d => Subtype.ext (show (1 : G) * (d : G) * (1 : G)⁻¹ = d by simp)
      mul_smul := fun a b d => Subtype.ext (by
        show ((a : G) * (b : G)) * (d : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (d : G) * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  have hmod : Nat.card ↥(kuDelta E x) ≡
      Nat.card (MulAction.fixedPoints ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S)
        ↥(kuDelta E x)) [MOD 2] :=
    hKp.card_modEq_card_fixedPoints (α := ↥(kuDelta E x))
  rw [hΔ4] at hmod
  have hone : ∀ k : ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S),
      k • (⟨1, (kuDelta E x).one_mem⟩ : ↥(kuDelta E x)) = ⟨1, (kuDelta E x).one_mem⟩ :=
    fun k => Subtype.ext (by show (k : G) * 1 * (k : G)⁻¹ = 1; simp)
  have hne0 : Nonempty (MulAction.fixedPoints
      ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S) ↥(kuDelta E x)) :=
    ⟨⟨⟨1, (kuDelta E x).one_mem⟩, hone⟩⟩
  have hpos := Nat.card_pos (α := MulAction.fixedPoints
    ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S) ↥(kuDelta E x))
  have hnontriv : Nontrivial (MulAction.fixedPoints
      ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S) ↥(kuDelta E x)) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨y, hy⟩ := exists_ne
    (⟨⟨1, (kuDelta E x).one_mem⟩, hone⟩ :
      MulAction.fixedPoints ↥(Subgroup.normalizer (kuDelta E x : Set G) ⊓ S)
        ↥(kuDelta E x))
  have hi1 : y.1.1 ≠ 1 := fun h => hy (Subtype.ext (Subtype.ext h))
  have hnfix : (n' : G) * y.1.1 * (n' : G)⁻¹ = y.1.1 :=
    congrArg Subtype.val (y.2 ⟨n', hnK⟩)
  obtain ⟨i, hiΔ, hi1', hni⟩ : ∃ i ∈ kuDelta E x, i ≠ 1 ∧ (n' : G) * i * (n' : G)⁻¹ = i :=
    ⟨y.1.1, y.1.2, hi1, hnfix⟩
  have hiC : i ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hiΔ).2
  have hiE : i ∈ E := (Subgroup.mem_inf.mp hiΔ).1
  have hxi : x * i = i * x := Subgroup.mem_centralizer_iff.mp hiC x (Set.mem_singleton x)
  have hcommAB : ∀ a ∈ Subgroup.zpowers x, ∀ d ∈ kuDelta E x, a * d = d * a := by
    intro a ha d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hxd : Commute x d :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 x (Set.mem_singleton x)
    exact (hxd.zpow_left k).eq
  have hdisj : Subgroup.zpowers x ⊓ kuDelta E x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgz, hgd⟩ := Subgroup.mem_inf.mp hg
    have hg2 : g * g = 1 := Ψ.E_mul_self g (Subgroup.mem_inf.mp hgd).1
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have h3 : orderOf g ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hgz
      rwa [hx] at this
    have h1 : orderOf g = 1 := by
      have hgcd := Nat.dvd_gcd h3 h2
      have h4 : Nat.gcd 3 2 = 1 := by norm_num
      rw [h4] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hcardAB : Nat.card ↥(Subgroup.zpowers x ⊔ kuDelta E x) = 12 := by
    rw [card_sup_of_commute hcommAB hdisj, Nat.card_zpowers, hx, Ψ.card_delta hHN hxH hx]
  have hsupK : Subgroup.zpowers x ⊔ kuDelta E x ≤
      Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxi,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    · intro d hd
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Ψ.E_comm d (Subgroup.mem_inf.mp hd).1 i hiE), (Subgroup.mem_inf.mp hd).2⟩
  have hKle : Nat.card ↥(Subgroup.centralizer ({i} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) = 12 :=
    Ψ.card_centralizer_delta hHN hxH hx hiΔ hi1'
  have heq : Subgroup.zpowers x ⊔ kuDelta E x =
      Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hsupK (le_of_eq (by rw [hKle, hcardAB]))
  have hni' : (n' : G) * i = i * (n' : G) := mul_inv_eq_iff_eq_mul.mp hni
  have hn_mem : (n' : G) ∈ Subgroup.centralizer ({i} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hni', hS hnS⟩
  rw [← heq] at hn_mem
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcommAB hn_mem
  have ha_eq : a = (n' : G) * b⁻¹ := by rw [hab, mul_inv_cancel_right]
  have haS : a ∈ S := by
    rw [ha_eq]
    exact S.mul_mem hnS (S.inv_mem (hΔS hb))
  obtain ⟨k, hk⟩ := hS2 ⟨a, haS⟩
  have hak : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hak
  have h3 : orderOf a ∣ 3 := by
    have := orderOf_dvd_of_mem_zpowers ha
    rwa [hx] at this
  have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf a = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hc) h2
  have ha1 : a = 1 := orderOf_eq_one_iff.mp h1
  have hnb : (n' : G) = b := by rw [hab, ha1, one_mul]
  exact hnΔ (by rw [hnb]; exact hb)

end KuA6Model

end CFSG.GH74.QTGen4.Ku
