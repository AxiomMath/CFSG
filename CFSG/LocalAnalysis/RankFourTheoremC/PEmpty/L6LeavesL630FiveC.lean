module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_le_normalizer' {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  constructor
  · intro hx
    rw [sup_eq_closure] at hx
    refine closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, y, hy, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
      have hc : k₁ * h₂ * k₁⁻¹ ∈ H := (mem_normalizer_iff.mp (hK hk₁) h₂).mp hh₂
      exact ⟨h₁ * (k₁ * h₂ * k₁⁻¹), H.mul_mem hh₁ hc, k₁ * k₂, K.mul_mem hk₁ hk₂, by group⟩
    · rintro _ _ ⟨h, hh, k, hk, rfl⟩
      have hc : k⁻¹ * h⁻¹ * k⁻¹⁻¹ ∈ H :=
        (mem_normalizer_iff.mp (hK (K.inv_mem hk)) h⁻¹).mp (H.inv_mem hh)
      refine ⟨k⁻¹ * h⁻¹ * k⁻¹⁻¹, hc, k⁻¹, K.inv_mem hk, ?_⟩
      group
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact mul_mem_sup hh hk

theorem zpow_eq_one_of_mem_of_not_mem {z : G} {C : Subgroup G} (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1)
    (hzC : z ∉ C) {k : ℤ} (hk : z ^ k ∈ C) : z ^ k = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  have hmod : ∀ n : ℤ, z ^ (n % 5) = z ^ n := by
    intro n
    simpa [hord] using zpow_mod_orderOf z n
  have key : ∀ s : ℤ, (k * s) % 5 = 1 → z ∈ C := by
    intro s hs
    have h1 : (z ^ k) ^ s = z := by
      rw [← zpow_mul, ← hmod (k * s), hs, zpow_one]
    rw [← h1]
    exact C.zpow_mem hk s
  rcases (show k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 by omega) with
    h | h | h | h | h
  · rw [← hmod k, h, zpow_zero]
  · exact absurd (key 1 (by omega)) hzC
  · exact absurd (key 3 (by omega)) hzC
  · exact absurd (key 2 (by omega)) hzC
  · exact absurd (key 4 (by omega)) hzC

theorem card_le_five_of_centralizer {P : Subgroup G} {x z : G}
    (hB : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPlane 5 P x z)
    (C : Subgroup G) (hxC : x ∈ C) (hzN : z ∈ normalizer (C : Set G)) (hzC : z ∉ C)
    (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1)
    (hxF : ∀ Q : Subgroup G, IsPGroup 5 Q → x ∉ (frattini ↥Q).map Q.subtype)
    {D : Subgroup G} (hDC : D ≤ C) (hD : IsPGroup 5 D) : Nat.card D ≤ 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx1 : x ≠ 1 := by
    intro h
    have h2 : Nat.card ↥(zpowers x ⊔ zpowers z) = 5 ^ 2 := hB.card_eq
    rw [h, Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers,
      orderOf_eq_prime hz5 hz1] at h2
    norm_num at h2
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  have hBcard : Nat.card B = 5 ^ 2 := hB.card_eq
  have hBab := hB.isElemAbelian
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ B := mem_sup_right (mem_zpowers z)
  have hxp : x ^ 5 = 1 := hBab.2 x hxB
  have hxz : x * z = z * x := by
    have := hBab.1.is_comm.comm (⟨x, hxB⟩ : B) ⟨z, hzB⟩
    exact congrArg Subtype.val this
  have hxz' : Commute x z := hxz
  have hcommx : ∀ e ∈ zpowers x, e * z = z * e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left hxz' k).eq
  have hxord : Nat.card (zpowers x) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hSC : ∀ y : G, (∀ b ∈ B, b * y = y * b) → y ^ 5 = 1 → y ∈ B := fun y hy hy5 =>
    hB.mem_of_mem_centralizer y (mem_centralizer_iff.mpr hy) hy5
  set L : Subgroup G := C ⊔ zpowers z with hLdef
  have hzL : z ∈ L := mem_sup_right (mem_zpowers z)
  have hxL : x ∈ L := mem_sup_left hxC
  have hL_le : zpowers z ≤ normalizer (C : Set G) := zpowers_le.mpr hzN
  haveI hCL : (C.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hL_le)
  have hBL : B ≤ L := sup_le (zpowers_le.mpr hxL) (zpowers_le.mpr hzL)
  have hidx : (C.subgroupOf L).index = 5 := by
    set ζ : L := ⟨z, hzL⟩ with hζdef
    have hζ5 : ζ ^ 5 = 1 := Subtype.ext (by simpa using hz5)
    have hζ1 : ζ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hζord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
    set ρ : (zpowers ζ : Subgroup L) →* L ⧸ (C.subgroupOf L) :=
      (QuotientGroup.mk' (C.subgroupOf L)).comp (zpowers ζ).subtype with hρdef
    have hbij : Function.Bijective ρ := by
      constructor
      · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        rintro ⟨a, ha⟩ hker
        rw [MonoidHom.mem_ker] at hker
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        have hkC : (ζ ^ k : L) ∈ C.subgroupOf L := (QuotientGroup.eq_one_iff _).mp hker
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow] at hkC
        have hz : z ^ k = 1 := zpow_eq_one_of_mem_of_not_mem hz5 hz1 hzC hkC
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_zpow, Subgroup.coe_one]
        exact hz
      · intro q
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨h, hh, k, hk, hhk⟩ := (mem_sup_of_le_normalizer' hL_le).mp l.2
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hk
        have hhL : (⟨h, mem_sup_left hh⟩ : L) ∈ C.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh
        refine ⟨⟨ζ ^ m, (zpowers ζ).zpow_mem (Subgroup.mem_zpowers ζ) m⟩, ?_⟩
        have hl : l = (⟨h, mem_sup_left hh⟩ : L) * ζ ^ m := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_zpow]
          exact hhk.symm
        show QuotientGroup.mk' (C.subgroupOf L) (ζ ^ m) = QuotientGroup.mk' (C.subgroupOf L) l
        have hone : QuotientGroup.mk' (C.subgroupOf L) (⟨h, mem_sup_left hh⟩ : L) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hhL
        rw [hl, map_mul, hone, one_mul]
    have hcard := Nat.card_congr (Equiv.ofBijective ρ hbij)
    rw [Nat.card_zpowers, hζord] at hcard
    rw [Subgroup.index_eq_card]
    exact hcard.symm
  have hLcard : Nat.card L = 5 * Nat.card C := by
    have h1 := Subgroup.index_mul_card (C.subgroupOf L)
    rw [hidx, Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv] at h1
    exact h1.symm
  have hBp : IsPGroup 5 (B.subgroupOf L) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv, hBcard]
  obtain ⟨T, hBT⟩ := hBp.exists_le_sylow
  set T₁ : Subgroup G := (T : Subgroup L).map L.subtype with hT₁def
  have hT₁L : T₁ ≤ L := by
    rintro _ ⟨t, _, rfl⟩
    exact t.2
  have hT₁card : Nat.card T₁ = Nat.card (T : Subgroup L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hT₁p : IsPGroup 5 T₁ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
    exact IsPGroup.iff_card.mpr ⟨n, by rw [hT₁card, hn]⟩
  have hBT₁ : B ≤ T₁ := by
    intro b hb
    have hbT : (⟨b, hBL hb⟩ : L) ∈ (T : Subgroup L) := hBT (Subgroup.mem_subgroupOf.mpr hb)
    exact ⟨⟨b, hBL hb⟩, hbT, rfl⟩
  have hzT₁ : z ∈ T₁ := hBT₁ hzB
  have hxT₁ : x ∈ T₁ := hBT₁ hxB
  have hTidx : ¬ 5 ∣ (T : Subgroup L).index := T.not_dvd_index
  have hTL : (T : Subgroup L).index * Nat.card (T : Subgroup L) = Nat.card L :=
    Subgroup.index_mul_card (T : Subgroup L)
  set Cl : Subgroup L := C.subgroupOf L with hClDef
  set fT : T₁ →* L ⧸ Cl := (QuotientGroup.mk' Cl).comp (Subgroup.inclusion hT₁L) with hfTdef
  have hfT_range : Nat.card fT.range = 5 := by
    have hdvd : Nat.card fT.range ∣ Nat.card (L ⧸ Cl) := Subgroup.card_subgroup_dvd_card _
    have hquot : Nat.card (L ⧸ Cl) = 5 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    rw [hquot] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
    · exfalso
      rw [Subgroup.card_eq_one] at h1
      have hmem : fT ⟨z, hzT₁⟩ ∈ fT.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [h1, Subgroup.mem_bot] at hmem
      have hzCl : (⟨z, hzL⟩ : L) ∈ Cl := (QuotientGroup.eq_one_iff _).mp hmem
      exact hzC (Subgroup.mem_subgroupOf.mp hzCl)
    · exact h1
  have hcoat : IsCoatom fT.ker := by
    apply Subgroup.isCoatom_of_index_prime
    rw [Subgroup.index_ker, hfT_range]
    norm_num
  have hΦle : frattini T₁ ≤ fT.ker := frattini_le_coatom hcoat
  have hΦC : ∀ w ∈ frattini T₁, (w : G) ∈ C := by
    intro w hw
    have hw' : w ∈ fT.ker := hΦle hw
    rw [MonoidHom.mem_ker] at hw'
    have hwCl : (Subgroup.inclusion hT₁L w : L) ∈ Cl := (QuotientGroup.eq_one_iff _).mp hw'
    exact Subgroup.mem_subgroupOf.mp hwCl
  have hΦbot : frattini T₁ = ⊥ := by
    by_contra hne
    haveI : Fact (IsPGroup 5 T₁) := ⟨hT₁p⟩
    haveI : Group.IsNilpotent T₁ := hT₁p.isNilpotent
    obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hv1 : (v : T₁) ≠ 1 := fun h => hv (Subtype.ext (by simpa using h))
    have hH₀p : IsPGroup 5 ↥(frattini T₁ ⊓ Subgroup.center T₁) := hT₁p.to_subgroup _
    have h5dvd : 5 ∣ Nat.card ↥(frattini T₁ ⊓ Subgroup.center T₁) := by
      rcases hH₀p.card_eq_or_dvd with h1 | h1
      · exfalso
        rw [Subgroup.card_eq_one] at h1
        have hvbot : (v : T₁) ∈ (⊥ : Subgroup T₁) := by
          rw [← h1]
          exact v.2
        exact hv1 (Subgroup.mem_bot.mp hvbot)
      · exact h1
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(frattini T₁ ⊓ Subgroup.center T₁)) 5 h5dvd
    set u : T₁ := (w : T₁) with hudef
    have hu_mem : u ∈ frattini T₁ ⊓ Subgroup.center T₁ := w.2
    have hu_frat : u ∈ frattini T₁ := (Subgroup.mem_inf.mp hu_mem).1
    have hu_cen : u ∈ Subgroup.center T₁ := (Subgroup.mem_inf.mp hu_mem).2
    have hu5 : u ^ 5 = 1 := by
      have h1 : w ^ 5 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      have h2 := congrArg (fun a : ↥(frattini T₁ ⊓ Subgroup.center T₁) => (a : T₁)) h1
      simpa using h2
    have hu1 : u ≠ 1 := by
      intro h
      have h1 : w = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hw
      norm_num at hw
    set uG : G := (u : G) with huGdef
    have huG5 : uG ^ 5 = 1 := by
      have := congrArg (fun a : T₁ => (a : G)) hu5
      simpa using this
    have huG1 : uG ≠ 1 := fun h => hu1 (Subtype.ext h)
    have huGcomm : ∀ b ∈ B, b * uG = uG * b := by
      intro b hb
      have hbT : b ∈ T₁ := hBT₁ hb
      have := (Subgroup.mem_center_iff.mp hu_cen) ⟨b, hbT⟩
      exact congrArg Subtype.val this
    have huGB : uG ∈ B := hSC uG huGcomm huG5
    have huGC : uG ∈ C := hΦC u hu_frat
    have huGx : uG ∈ zpowers x := by
      by_contra hnot
      have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num : Nat.Prime 5)
        (zpowers x) huG5 hnot (fun e he => huGcomm e (zpowers_le.mpr hxB he))
      rw [hxord] at hcard
      have hle : zpowers x ⊔ zpowers uG ≤ B := sup_le (zpowers_le.mpr hxB) (zpowers_le.mpr huGB)
      have heq : zpowers x ⊔ zpowers uG = B :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hBcard]; norm_num)
      have hzC' : z ∈ zpowers x ⊔ zpowers uG := heq ▸ hzB
      have hle' : zpowers x ⊔ zpowers uG ≤ C :=
        sup_le (zpowers_le.mpr hxC) (zpowers_le.mpr huGC)
      exact hzC (hle' hzC')
    have hzeq : zpowers uG = zpowers x := by
      have hcu : Nat.card (zpowers uG) = 5 := by
        rw [Nat.card_zpowers, orderOf_eq_prime huG5 huG1]
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr huGx)
      rw [hcu, hxord]
    have hxu : x ∈ zpowers uG := by
      rw [hzeq]
      exact mem_zpowers x
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxu
    apply hxF T₁ hT₁p
    refine Subgroup.mem_map.mpr ⟨u ^ j, (frattini T₁).zpow_mem hu_frat j, ?_⟩
    simpa [hudef] using hj
  haveI : Fact (IsPGroup 5 T₁) := ⟨hT₁p⟩
  haveI hEA : IsElementaryAbelian 5 T₁ := CFSG.frattini_eq_bot_iff_isElementaryAbelian.mp hΦbot
  have hT₁B : T₁ ≤ B := by
    intro t ht
    have ht5 : t ^ 5 = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 5 T₁) (⟨t, ht⟩ : T₁)
      simpa using congrArg Subtype.val this
    apply hSC t _ ht5
    intro b hb
    have hcm := hEA.toIsMulCommutative.is_comm.comm (⟨b, hBT₁ hb⟩ : T₁) ⟨t, ht⟩
    exact congrArg Subtype.val hcm
  have hTB : T₁ = B := le_antisymm hT₁B hBT₁
  have hT₁card' : Nat.card T₁ = 5 ^ 2 := by rw [hTB, hBcard]
  have hcount : Nat.card C = 5 * (T : Subgroup L).index := by
    have h1 := hTL
    rw [← hT₁card, hT₁card', hLcard] at h1
    norm_num at h1
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD
  have hdvd : Nat.card D ∣ Nat.card C := Subgroup.card_dvd_of_le hDC
  rw [hk] at hdvd ⊢
  by_contra hgt
  push Not at hgt
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> norm_num at hgt
    · exact hk2
  have h25 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 hk2
  rw [hcount] at hdvd
  have h55 : 5 * 5 ∣ 5 * (T : Subgroup L).index := by
    have := h25.trans hdvd
    norm_num at this
    exact this
  exact hTidx ((Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5)) h55)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
