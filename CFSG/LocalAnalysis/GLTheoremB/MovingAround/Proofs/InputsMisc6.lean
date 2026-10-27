module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

section General

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_mem_center_of_commute_sylow (hG : commutator G = ⊤) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hzZ : z ∈ Subgroup.center G) : z = 1 := by
  classical
  let _ : CommGroup (P : Subgroup G) := { (inferInstance : Group (P : Subgroup G)) with
    mul_comm := fun a b => Subtype.ext (hP a a.2 b b.2) }
  set V : G →* (P : Subgroup G) := MonoidHom.transfer (MonoidHom.id (P : Subgroup G)) with hV
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hzZ k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀, inv_mul_cancel_left]
  have hVz := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup G)) z key
  have hker : commutator G ≤ V.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro w ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_comm (V a) (V b)]
    group
  have hV1 : V z = 1 := hker (hG ▸ Subgroup.mem_top z)
  have h3 : z ^ (P : Subgroup G).index = 1 := congrArg Subtype.val (hVz.symm.trans hV1)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨z, hzP⟩
  have hk' : orderOf z = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h4 : orderOf z ∣ (P : Subgroup G).index := orderOf_dvd_of_pow_eq_one h3
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [h0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  · exfalso
    rw [hk'] at h4
    exact P.not_dvd_index ((dvd_pow_self p h0.ne').trans h4)

theorem exists_mem_not_mem_comm_mod {p : ℕ} [Fact p.Prime] {R U Z : Subgroup G}
    (hR : IsPGroup p R) (hUR : U ≤ R) (hRU : R ≤ Subgroup.normalizer (U : Set G))
    (hRZ : R ≤ Subgroup.normalizer (Z : Set G)) (hUZ : ¬ U ≤ Z) :
    ∃ u ∈ U, u ∉ Z ∧ ∀ r ∈ R, u⁻¹ * (r * u * r⁻¹) ∈ Z := by
  set Z' : Subgroup R := (Z ⊓ R).subgroupOf R with hZ'
  have hZ'n : Z'.Normal := by
    constructor
    intro n hn g
    rw [hZ', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnZ, hnR⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, R.mul_mem (R.mul_mem g.2 hnR) (R.inv_mem g.2)⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hRZ g.2) n).1 hnZ
  have hUn : (U.subgroupOf R).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hRU g.2) n).1 hn
  set π : R →* R ⧸ Z' := QuotientGroup.mk' Z' with hπ
  set N : Subgroup (R ⧸ Z') := (U.subgroupOf R).map π with hN
  have hNn : N.Normal := hUn.map π (QuotientGroup.mk'_surjective _)
  have hmemZ : ∀ r : R, π r = 1 → (r : G) ∈ Z := fun r hr =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hr))).1
  have hN1 : N ≠ ⊥ := by
    intro hbot
    apply hUZ
    intro u hu
    have hmem : π ⟨u, hUR hu⟩ ∈ N := ⟨⟨u, hUR hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmemZ _ hmem
  have hQp : IsPGroup p (R ⧸ Z') := hR.to_quotient _
  haveI : Group.IsNilpotent (R ⧸ Z') := hQp.isNilpotent
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  obtain ⟨hwN, hwZ⟩ := Subgroup.mem_inf.1 w.2
  obtain ⟨s, hs, hsw⟩ := Subgroup.mem_map.1 hwN
  have hw1' : (w : R ⧸ Z') ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine ⟨(s : G), Subgroup.mem_subgroupOf.1 hs, fun hsZ => hw1' ?_, fun r hr => ?_⟩
  · rw [← hsw]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hsZ, s.2⟩))
  · have hcen := Subgroup.mem_center_iff.1 hwZ (π ⟨r, hr⟩)
    have h1 : π (s⁻¹ * (⟨r, hr⟩ * s * (⟨r, hr⟩ : R)⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hsw, hcen]
      group
    have h2 := hmemZ _ h1
    simpa using h2

end General

section Defect

variable {G : Type} [Group G] [Finite G]

theorem mem_center_of_mem_centerOf {K : Subgroup G} {z : G} (hzK : z ∈ K)
    (hz : z ∈ centerOf K) : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
  obtain ⟨w, hw, hwz⟩ := hz
  have hw' : w = ⟨z, hzK⟩ := Subtype.ext hwz
  exact hw' ▸ hw

theorem le_normalizer_inf {R K : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    R ≤ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem hr (Subgroup.mem_inf.1 hw).1) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.1 (hRK hr) w).1 (Subgroup.mem_inf.1 hw).2⟩
  · intro hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    have e : w = r⁻¹ * (r * w * r⁻¹) * r := by group
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_normalizer_iff.1 (hRK hr) w).2 hw2⟩
    rw [e]
    exact R.mul_mem (R.mul_mem (R.inv_mem hr) hw1) hr

theorem exists_noncentral_fixed {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K R : Subgroup G}
    (hK : commutator ↥K = ⊤) (hR : IsPGroup p R) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hS : IsSylowIn p K (R ⊓ K)) (hpK : p ∣ Nat.card K)
    (hZ : ¬ ∃ D : Subgroup G, D ≤ centerOf K ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2) :
    ∃ y ∈ R ⊓ K, y ∉ centerOf K ∧ y ^ p = 1 ∧ ∀ r ∈ R, y⁻¹ * (r * y * r⁻¹) ∈ centerOf K := by
  have hRS := le_normalizer_inf hRK
  by_cases hSc : IsCyclic ↥(R ⊓ K)
  ·
    have hScomm : ∀ a ∈ R ⊓ K, ∀ b ∈ R ⊓ K, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(R ⊓ K)) ⟨b, hb⟩)
    have hZS : ∀ z ∈ R ⊓ K, z ∈ centerOf K → z = 1 := by
      intro z hz hzZ
      have hzK : z ∈ K := (Subgroup.mem_inf.1 hz).2
      let P : Sylow p ↥K :=
        { toSubgroup := (R ⊓ K).subgroupOf K
          isPGroup' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
          is_maximal' := fun {Q} hQ hle => by
            have h1 : Q.map K.subtype = R ⊓ K := hS.2.2 _ (Subgroup.map_subtype_le _) (hQ.map _)
              (fun s hs => ⟨⟨s, hS.1 hs⟩, hle (Subgroup.mem_subgroupOf.2 hs), rfl⟩)
            rw [← h1]
            exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q).symm }
      have h1 := eq_one_of_mem_center_of_commute_sylow hK P
        (fun a ha b hb => Subtype.ext (hScomm _ (Subgroup.mem_subgroupOf.1 ha) _
          (Subgroup.mem_subgroupOf.1 hb)))
        (z := ⟨z, hzK⟩) (Subgroup.mem_subgroupOf.2 hz) (mem_center_of_mem_centerOf hzK hzZ)
      exact congrArg Subtype.val h1
    have hS1 : ¬ R ⊓ K ≤ ⊥ := by
      intro hbot
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpK
      have hwp : IsPGroup p (Subgroup.zpowers (w : G)) := by
        rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_coe, hw]
        exact ⟨1, (pow_one p).symm⟩
      have heq := hS.2.2 _ (Subgroup.zpowers_le.2 w.2) hwp (hbot.trans bot_le)
      have hw1 : (w : G) = 1 := Subgroup.mem_bot.1 (hbot (heq ▸ Subgroup.mem_zpowers _))
      have h1 : orderOf w = 1 := by rw [← Subgroup.orderOf_coe, hw1, orderOf_one]
      rw [hw] at h1
      exact (Fact.out : p.Prime).one_lt.ne' h1
    obtain ⟨u, huS, hu1, hu⟩ := exists_mem_not_mem_comm_mod (Z := ⊥) hR inf_le_left hRS
      (fun r _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top r) hS1
    have hu1' : u ≠ 1 := fun h => hu1 (h ▸ Subgroup.one_mem _)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨u, (Subgroup.mem_inf.1 huS).1⟩
    have hk' : orderOf u = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact hu1' hk'
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨u ^ p ^ j, Subgroup.pow_mem _ huS _, fun hyZ => ?_, ?_, fun r hr => ?_⟩
    · have h1 := hZS _ (Subgroup.pow_mem _ huS _) hyZ
      have h2 : orderOf u ∣ p ^ j := orderOf_dvd_of_pow_eq_one h1
      rw [hk'] at h2
      have h3 := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) h2
      have h4 : p ^ j < p ^ (j + 1) := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
      omega
    · rw [← pow_mul, ← pow_succ, ← hk', pow_orderOf_eq_one]
    · have h1 : u⁻¹ * (r * u * r⁻¹) = 1 := Subgroup.mem_bot.1 (hu r hr)
      have h2 : r * u * r⁻¹ = u := by
        calc r * u * r⁻¹ = u * (u⁻¹ * (r * u * r⁻¹)) := by group
          _ = u := by rw [h1, mul_one]
      have h3 : r * u ^ p ^ j * r⁻¹ = u ^ p ^ j := by rw [← conj_pow, h2]
      rw [h3, inv_mul_cancel]
      exact Subgroup.one_mem _
  · obtain ⟨V, hVS, hRV, hVc, hVp, hVab⟩ := CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le
      Fact.out hp2 hR inf_le_left hRS hSc
    have hVel : IsElemAbelian p V := ⟨⟨⟨fun a b => Subtype.ext (hVab _ a.2 _ b.2)⟩⟩, hVp⟩
    have hVZ : ¬ V ≤ centerOf K := fun h => hZ ⟨V, h, hVel, hVc⟩
    obtain ⟨u, huV, huZ, hu⟩ := exists_mem_not_mem_comm_mod hR (hVS.trans inf_le_left) hRV
      (fun r hr => Claims1113.mem_normalizer_centerOf (hRK hr)) hVZ
    exact ⟨u, hVS huV, huZ, hVp u huV, hu⟩

theorem exists_defect' (IU : Claims1113.InputU43) (hO : GLAPPrimeCore 3 G = ⊥)
    (hK : CFSG.Open.IsKGroup G) {c : Subgroup G} (hc : IsComponentOf c (⊤ : Subgroup G)) {x : G}
    (hxc : x ∈ Subgroup.normalizer (c : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ y ∈ c, y ^ 3 = 1 ∧ (∃ g ∈ c, y * g ≠ g * y) ∧ y⁻¹ * (x * y * x⁻¹) ∈ centerOf c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hxR, hS, -⟩ := Claims1113.exists_sylow_normalized hxc hx3
  have hRN : R ≤ Subgroup.normalizer (c : Set G) := hR.1
  have hnc : ∀ {y : G}, y ∈ c → y ∉ centerOf c → ∃ g ∈ c, y * g ≠ g * y := by
    intro y hyc hyZ
    by_contra hall
    push Not at hall
    exact hyZ (Claims1113.mem_centerOf_iff.2 ⟨hyc, hall⟩)
  by_cases hE : ∃ D : Subgroup G, D ≤ centerOf c ∧ IsElemAbelian 3 D ∧ Nat.card D = 3 ^ 2
  ·
    have hE' : ∃ D : Subgroup G, D ≤ centerOf c ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 := by
      obtain ⟨D, h1, h2, h3⟩ := hE
      exact ⟨D, h1, h2, by rw [h3]; norm_num⟩
    obtain ⟨h1, -, -, h4⟩ := IU G c hc.2.2 (hK.subgroup c) hE'
    obtain ⟨F, hFS, hFel, hFc, huniq⟩ := h4 _ hS
    have hRS := le_normalizer_inf hRN
    have hRF : R ≤ Subgroup.normalizer (F : Set G) := by
      intro r hr
      have h2 : GLBConj r⁻¹ F = F := by
        refine huniq _ ?_ (Lemma118T.isElemAbelian_gLBConj' hFel r⁻¹)
          (by rw [Lemma1112b.card_glbConj, hFc])
        intro w hw
        have hw' : r⁻¹ * w * r⁻¹⁻¹ ∈ F := mem_gLBConj.1 hw
        have e : w = r * (r⁻¹ * w * r⁻¹⁻¹) * r⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hRS hr) _).1 (hFS hw')
      have h3 : r⁻¹ ∈ Subgroup.normalizer (F : Set G) := mem_normalizer_iff_gLBConj_eq.2 h2
      simpa using Subgroup.inv_mem _ h3
    have hFZ : ¬ F ≤ centerOf c := fun hFZ => by
      have h2 := h1 F hFZ hFel
      rw [hFc] at h2
      norm_num at h2
    obtain ⟨u, huF, huZ, hu⟩ := exists_mem_not_mem_comm_mod hR.2.1 (hFS.trans inf_le_left) hRF
      (fun r hr => Claims1113.mem_normalizer_centerOf (hRN hr)) hFZ
    have huc : u ∈ c := (Subgroup.mem_inf.1 (hFS huF)).2
    exact ⟨u, huc, hFel.2 u huF, hnc huc huZ, hu x hxR⟩
  · obtain ⟨y, hyS, hyZ, hy3, hy⟩ := exists_noncentral_fixed (p := 3) (by norm_num) hc.2.2.1
      hR.2.1 hRN hS (Claims1113.three_dvd_card hO hc) hE
    have hyc : y ∈ c := (Subgroup.mem_inf.1 hyS).2
    exact ⟨y, hyc, hy3, hnc hyc hyZ, hy x hxR⟩

end Defect

section CentralCases

variable {Y : Type} [Group Y] [Finite Y] {V : Subgroup Y} {x : Y}

theorem not_centralizes' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c₀ : Subgroup Y} (hc₀ : IsComponentOf c₀ (⊤ : Subgroup Y))
    (hcen : ∀ u ∈ c₀, x * u = u * x) : False := by
  have hxN : x ∈ Subgroup.normalizer (c₀ : Set Y) :=
    Subgroup.centralizer_le_normalizer (c₀ : Set Y)
      (Subgroup.mem_centralizer_iff.2 fun h hh => (hcen h hh).symm)
  obtain ⟨y, hyc, hy3, ⟨g, hgc, hyg⟩, -⟩ := exists_defect' IU D.hO D.hK hc₀ hxN D.hx3
  obtain ⟨v, hv, b, hb, rfl⟩ := D.mem_sup hy3 (hcen y hyc)
    (fun w hw => (D.hVc c₀ hc₀ w hw y hyc).symm)
  apply hyg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : v * g = g * v := D.hVc c₀ hc₀ v hv g hgc
  have h2 : x ^ k * g = g * x ^ k := ((show Commute x g from hcen g hgc).zpow_left k).eq
  calc v * x ^ k * g = v * (x ^ k * g) := mul_assoc _ _ _
    _ = v * (g * x ^ k) := by rw [h2]
    _ = (v * g) * x ^ k := (mul_assoc _ _ _).symm
    _ = (g * v) * x ^ k := by rw [h1]
    _ = g * (v * x ^ k) := mul_assoc _ _ _

theorem mem_of_fixed' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hne : ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧ c' ≠ c) {u : Y} (huc : u ∈ c)
    (hu3 : u ^ 3 = 1) (hux : x * u = u * x) : u ∈ V := by
  obtain ⟨v, hv, b, hb, rfl⟩ := D.mem_sup hu3 hux (fun w hw => (D.hVc c hc w hw _ huc).symm)
  by_cases hb1 : b = 1
  · rw [hb1, mul_one]
    exact hv
  · exfalso
    obtain ⟨c', hc', hne'⟩ := hne
    have hxb := Claims1113.mem_zpowers_of_ne_one D.hx3 hb hb1
    have hbe : b = v⁻¹ * (v * b) := by group
    refine not_centralizes' IU D hc'
      (Claims1113.CentralData.centralizes_of_mem_zpowers (w := b) ?_ hxb)
    intro g hg
    have h1 : v * g = g * v := D.hVc c' hc' v hv g hg
    have h2 : (v * b) * g = g * (v * b) := Claims1113.comm_of_ne hc hc' (Ne.symm hne') huc hg
    rw [hbe]
    calc v⁻¹ * (v * b) * g = v⁻¹ * ((v * b) * g) := mul_assoc _ _ _
      _ = v⁻¹ * (g * (v * b)) := by rw [h2]
      _ = (v⁻¹ * g) * (v * b) := (mul_assoc _ _ _).symm
      _ = (g * v⁻¹) * (v * b) := by
          rw [show v⁻¹ * g = g * v⁻¹ by
            calc v⁻¹ * g = v⁻¹ * (g * v) * v⁻¹ := by group
              _ = v⁻¹ * (v * g) * v⁻¹ := by rw [h1]
              _ = g * v⁻¹ := by group]
      _ = g * (v⁻¹ * (v * b)) := mul_assoc _ _ _

theorem exists_mem_comp' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hne : ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧ c' ≠ c) :
    ∃ w ∈ V, w ∈ c ∧ w ≠ 1 := by
  have hxN := Claims1113.mem_normalizer_comp' D.hO D.hx3 D.hsolv hc
  obtain ⟨R, hR, hxR, -, -⟩ := Claims1113.exists_sylow_normalized hxN D.hx3
  obtain ⟨z, hzc, -, hzcen, hz1, hz3⟩ := Claims1113.exists_central_mem hR Subgroup.le_normalizer
    le_rfl (Claims1113.three_dvd_card D.hO hc)
  exact ⟨z, mem_of_fixed' IU D hc hne hzc hz3 (hzcen x hxR), hzc, hz1⟩

theorem exists_defect_mem' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hne : ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧ c' ≠ c) :
    ∃ y ∈ c, y ^ 3 = 1 ∧ (∃ g ∈ c, y * g ≠ g * y) ∧ ∃ z ∈ V, z ≠ 1 ∧ x * y * x⁻¹ = y * z := by
  have hxN := Claims1113.mem_normalizer_comp' D.hO D.hx3 D.hsolv hc
  obtain ⟨y, hyc, hy3, hync, hζZ⟩ := exists_defect' IU D.hO D.hK hc hxN D.hx3
  set ζ : Y := y⁻¹ * (x * y * x⁻¹) with hζ
  have hdef : x * y * x⁻¹ = y * ζ := by rw [hζ]; group
  have hζc : ∀ k ∈ c, ζ * k = k * ζ := (Claims1113.mem_centerOf_iff.1 hζZ).2
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : (x * y * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
    rw [hdef, (show Commute y ζ from (hζc y hyc).symm).mul_pow, hy3, one_mul] at h1
    exact h1
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hdef
    have hxy : x * y = y * x := by
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [hdef]
    have hyV := mem_of_fixed' IU D hc hne hyc hy3 hxy
    obtain ⟨g, hgc, hyg⟩ := hync
    exact hyg (D.hVc c hc y hyV g hgc)
  have hxζ := D.comm_of_center IU hc hζZ hζ3
  obtain ⟨v, hv, b, hb, hvb⟩ := D.mem_sup hζ3 hxζ
    (fun w hw => (D.hVc c hc w hw ζ (Claims1113.mem_centerOf_iff.1 hζZ).1).symm)
  refine ⟨y, hyc, hy3, hync, ζ, ?_, hζ1, hdef⟩
  by_cases hb1 : b = 1
  · rw [hvb, hb1, mul_one]
    exact hv
  · exfalso
    have hxb := Claims1113.mem_zpowers_of_ne_one D.hx3 hb hb1
    have hbe : b = v⁻¹ * ζ := by rw [hvb]; group
    refine not_centralizes' IU D hc
      (Claims1113.CentralData.centralizes_of_mem_zpowers (w := b) ?_ hxb)
    intro g hg
    have h1 : v * g = g * v := D.hVc c hc v hv g hg
    have h2 : ζ * g = g * ζ := hζc g hg
    rw [hbe]
    calc v⁻¹ * ζ * g = v⁻¹ * (ζ * g) := mul_assoc _ _ _
      _ = v⁻¹ * (g * ζ) := by rw [h2]
      _ = (v⁻¹ * g) * ζ := (mul_assoc _ _ _).symm
      _ = (g * v⁻¹) * ζ := by
          rw [show v⁻¹ * g = g * v⁻¹ by
            calc v⁻¹ * g = v⁻¹ * (g * v) * v⁻¹ := by group
              _ = v⁻¹ * (v * g) * v⁻¹ := by rw [h1]
              _ = g * v⁻¹ := by group]
      _ = g * (v⁻¹ * ζ) := mul_assoc _ _ _

theorem le_other' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c₁ c₂ : Subgroup Y} (hc₁ : IsComponentOf c₁ (⊤ : Subgroup Y))
    (hc₂ : IsComponentOf c₂ (⊤ : Subgroup Y))
    (hne : c₁ ≠ c₂)
    (hall : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c = c₁ ∨ c = c₂)
    (hV1 : V ≤ c₁) : V ≤ c₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hconj : ∃ n : Y, GLBConj n c₂ = c₁
  · obtain ⟨n, hn⟩ := hconj
    have hc₂' : GLBConj n⁻¹ c₁ = c₂ := by
      rw [← hn, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
    set D' : Subgroup Y := GLBConj n⁻¹ V with hD'
    have hD'c : D' ≤ c₂ := by
      rw [← hc₂']
      exact gLBConj_mono _ hV1
    have hD'Z : D' ≤ centerOf c₂ := by
      intro d hd
      refine Claims1113.mem_centerOf_iff.2 ⟨hD'c hd, fun k hk => ?_⟩
      have hd' : n⁻¹ * d * n⁻¹⁻¹ ∈ V := mem_gLBConj.1 hd
      have hk' : n⁻¹ * k * n⁻¹⁻¹ ∈ c₁ := by
        rw [← hc₂'] at hk
        exact mem_gLBConj.1 hk
      have h1 := D.hVc c₁ hc₁ _ hd' _ hk'
      calc d * k = n * ((n⁻¹ * d * n⁻¹⁻¹) * (n⁻¹ * k * n⁻¹⁻¹)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * k * n⁻¹⁻¹) * (n⁻¹ * d * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
        _ = k * d := by group
    have hD'el : IsElemAbelian 3 D' := Lemma118T.isElemAbelian_gLBConj' D.hVel _
    have hD'9 : Nat.card D' = 9 := by rw [hD', Lemma1112b.card_glbConj, D.hV9]
    have hxN := Claims1113.mem_normalizer_comp' D.hO D.hx3 D.hsolv hc₂
    obtain ⟨-, h2, -, -⟩ := IU Y c₂ hc₂.2.2 (D.hK.subgroup c₂) ⟨D', hD'Z, hD'el, hD'9⟩
    have hD'V : D' ≤ V := by
      intro d hd
      have hdZ := hD'Z hd
      obtain ⟨v, hv, b, hb, hvb⟩ := D.mem_sup (hD'el.2 d hd) (h2 x hxN D.hx3 d hdZ)
        (fun w hw => (D.hVc c₂ hc₂ w hw d (hD'c hd)).symm)
      by_cases hb1 : b = 1
      · rw [hvb, hb1, mul_one]
        exact hv
      · exfalso
        have hxb := Claims1113.mem_zpowers_of_ne_one D.hx3 hb hb1
        have hbe : b = v⁻¹ * d := by rw [hvb]; group
        refine not_centralizes' IU D hc₁
          (Claims1113.CentralData.centralizes_of_mem_zpowers (w := b) ?_ hxb)
        intro g hg
        have h1 : v * g = g * v := D.hVc c₁ hc₁ v hv g hg
        have h3 : d * g = g * d := Claims1113.central_comm_all hc₂ hdZ c₁ hc₁ g hg
        rw [hbe]
        calc v⁻¹ * d * g = v⁻¹ * (d * g) := mul_assoc _ _ _
          _ = v⁻¹ * (g * d) := by rw [h3]
          _ = (v⁻¹ * g) * d := (mul_assoc _ _ _).symm
          _ = (g * v⁻¹) * d := by
              rw [show v⁻¹ * g = g * v⁻¹ by
                calc v⁻¹ * g = v⁻¹ * (g * v) * v⁻¹ := by group
                  _ = v⁻¹ * (v * g) * v⁻¹ := by rw [h1]
                  _ = g * v⁻¹ := by group]
          _ = g * (v⁻¹ * d) := mul_assoc _ _ _
    have heq : D' = V := Subgroup.eq_of_le_of_card_ge hD'V (by rw [hD'9, D.hV9])
    rw [← heq]
    exact hD'c
  · push Not at hconj
    obtain ⟨w₂, hw₂V, hw₂c, hw₂1⟩ := exists_mem_comp' IU D hc₂ ⟨c₁, hc₁, hne⟩
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact c₂.one_mem
    obtain ⟨n, hn⟩ := D.htr w₂ hw₂V hw₂1 v hv hv1
    have hvn : v ∈ GLBConj n c₂ := mem_gLBConj.2 (by rw [← hn]; convert hw₂c using 1; group)
    rcases hall _ (Claims1113.isComp_conj hc₂ n) with h | h
    · exact absurd h (hconj n)
    · rw [h] at hvn
      exact hvn

theorem false_of_pair' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c₁ c₂ : Subgroup Y} (hc₁ : IsComponentOf c₁ (⊤ : Subgroup Y))
    (hc₂ : IsComponentOf c₂ (⊤ : Subgroup Y)) (hne : c₁ ≠ c₂)
    (hall : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c = c₁ ∨ c = c₂) : False := by
  obtain ⟨w₁, hw₁V, hw₁c, hw₁1⟩ := exists_mem_comp' IU D hc₁ ⟨c₂, hc₂, hne.symm⟩
  have hcover : ∀ v ∈ V, v ∈ c₁ ∨ v ∈ c₂ := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Or.inl c₁.one_mem
    obtain ⟨n, hn⟩ := D.htr w₁ hw₁V hw₁1 v hv hv1
    have hvn : v ∈ GLBConj n c₁ := mem_gLBConj.2 (by rw [← hn]; convert hw₁c using 1; group)
    rcases hall _ (Claims1113.isComp_conj hc₁ n) with h | h
    · rw [h] at hvn
      exact Or.inl hvn
    · rw [h] at hvn
      exact Or.inr hvn
  have hV : V ≤ c₁ ∨ V ≤ c₂ := by
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := hno
    obtain ⟨a, haV, hac⟩ := Set.not_subset.1 h1
    obtain ⟨b, hbV, hbc⟩ := Set.not_subset.1 h2
    have ha2 : a ∈ c₂ := (hcover a haV).resolve_left hac
    have hb1 : b ∈ c₁ := (hcover b hbV).resolve_right hbc
    rcases hcover (a * b) (V.mul_mem haV hbV) with h | h
    · apply hac
      have e : a = (a * b) * b⁻¹ := by group
      rw [e]
      exact c₁.mul_mem h (c₁.inv_mem hb1)
    · apply hbc
      have e : b = a⁻¹ * (a * b) := by group
      rw [e]
      exact c₂.mul_mem (c₂.inv_mem ha2) h
  rcases hV with h | h
  · exact D.false_of_two IU hc₁ hc₂ hne h (le_other' IU D hc₁ hc₂ hne hall h)
  · exact D.false_of_two IU hc₁ hc₂ hne (le_other' IU D hc₂ hc₁ hne.symm
      (fun c hc => (hall c hc).symm) h) h

theorem false_of_three' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    {c₁ c₂ c₃ : Subgroup Y} (hc₁ : IsComponentOf c₁ (⊤ : Subgroup Y))
    (hc₂ : IsComponentOf c₂ (⊤ : Subgroup Y)) (hc₃ : IsComponentOf c₃ (⊤ : Subgroup Y))
    (h12 : c₁ ≠ c₂) (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃) : False := by
  obtain ⟨y₁, hy₁c, hy₁3, -, z₁, hz₁V, hz₁1, hd₁⟩ :=
    exists_defect_mem' IU D hc₁ ⟨c₂, hc₂, h12.symm⟩
  obtain ⟨y₂, hy₂c, hy₂3, hy₂nc, z₂, hz₂V, hz₂1, hd₂⟩ :=
    exists_defect_mem' IU D hc₂ ⟨c₁, hc₁, h12⟩
  obtain ⟨y₃, hy₃c, hy₃3, hy₃nc, z₃, hz₃V, hz₃1, hd₃⟩ :=
    exists_defect_mem' IU D hc₃ ⟨c₁, hc₁, h13⟩
  have hzy : ∀ {c : Subgroup Y}, IsComponentOf c (⊤ : Subgroup Y) → ∀ {z y : Y}, z ∈ V → y ∈ c →
      Commute y z := fun hc z y hz hy => (D.hVc _ hc z hz y hy).symm
  have hdefpow : ∀ {c : Subgroup Y}, IsComponentOf c (⊤ : Subgroup Y) → ∀ {y z : Y}, y ∈ c →
      z ∈ V → x * y * x⁻¹ = y * z → ∀ a : ℤ, x * y ^ a * x⁻¹ = y ^ a * z ^ a := by
    intro c hc y z hy hz hd a
    rw [← conj_zpow, hd, (hzy hc hz hy).mul_zpow]
  have hzpow3 : ∀ {y : Y}, y ^ 3 = 1 → ∀ a : ℤ, (y ^ a) ^ 3 = 1 := by
    intro y hy a
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  by_cases hdep : z₂ ∈ Subgroup.zpowers z₁
  · obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hdep
    refine D.false_of_relation hc₂ hy₂c hy₂3 hy₂nc hz₂V hz₂1 hd₂ (w := y₁ ^ a) (hzpow3 hy₁3 a)
      (fun g hg => ?_) (fun v hv => ?_) ?_
    · exact ((show Commute y₁ g from Claims1113.comm_of_ne hc₁ hc₂ h12 hy₁c hg).zpow_left a).eq
    · exact ((show Commute y₁ v from (D.hVc c₁ hc₁ v hv y₁ hy₁c).symm).zpow_left a).eq
    · rw [hdefpow hc₁ hy₁c hz₁V hd₁ a, ha]
  · have hcz : z₂ * z₁ = z₁ * z₂ := D.hVel.comm hz₂V hz₁V
    obtain ⟨-, hcard⟩ :=
      Claims11x.plane_of_commute (D.hVel.2 z₂ hz₂V) (D.hVel.2 z₁ hz₁V) hz₁1 hcz hdep
    have hVeq : Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₁ = V :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hz₂V)
        (Subgroup.zpowers_le.2 hz₁V)) (by rw [D.hV9, hcard])
    have hz₃' : z₃ ∈ Subgroup.zpowers z₂ ⊔ Subgroup.zpowers z₁ := by rw [hVeq]; exact hz₃V
    have hcent : Subgroup.zpowers z₂ ≤
        Subgroup.centralizer ((Subgroup.zpowers z₁ : Subgroup Y) : Set Y) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact ((show Commute z₁ z₂ from hcz.symm).zpow_zpow j i).eq
    obtain ⟨u, hu, w, hw, huw⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_mul_of_mem_sup hcent hz₃'
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hc12 : Commute (y₂ ^ b) (y₁ ^ a) :=
      ((show Commute y₂ y₁ from
        Claims1113.comm_of_ne hc₂ hc₁ h12.symm hy₂c hy₁c).zpow_left b).zpow_right a
    refine D.false_of_relation hc₃ hy₃c hy₃3 hy₃nc hz₃V hz₃1 hd₃ (w := y₂ ^ b * y₁ ^ a) ?_
      (fun g hg => ?_) (fun v hv => ?_) ?_
    · rw [hc12.mul_pow, hzpow3 hy₂3 b, hzpow3 hy₁3 a, one_mul]
    · have h1 : Commute (y₂ ^ b) g :=
        ((show Commute y₂ g from Claims1113.comm_of_ne hc₂ hc₃ h23 hy₂c hg).zpow_left b)
      have h2 : Commute (y₁ ^ a) g :=
        ((show Commute y₁ g from Claims1113.comm_of_ne hc₁ hc₃ h13 hy₁c hg).zpow_left a)
      exact (h1.mul_left h2).eq
    · have h1 : Commute (y₂ ^ b) v :=
        ((show Commute y₂ v from (D.hVc c₂ hc₂ v hv y₂ hy₂c).symm).zpow_left b)
      have h2 : Commute (y₁ ^ a) v :=
        ((show Commute y₁ v from (D.hVc c₁ hc₁ v hv y₁ hy₁c).symm).zpow_left a)
      exact (h1.mul_left h2).eq
    · have hz1y2 : Commute (z₂ ^ b) (y₁ ^ a) :=
        (((hzy hc₁ hz₂V hy₁c).symm.zpow_left b).zpow_right a)
      calc x * (y₂ ^ b * y₁ ^ a) * x⁻¹ = (x * y₂ ^ b * x⁻¹) * (x * y₁ ^ a * x⁻¹) := by group
        _ = (y₂ ^ b * z₂ ^ b) * (y₁ ^ a * z₁ ^ a) := by
            rw [hdefpow hc₂ hy₂c hz₂V hd₂ b, hdefpow hc₁ hy₁c hz₁V hd₁ a]
        _ = y₂ ^ b * (z₂ ^ b * y₁ ^ a) * z₁ ^ a := by group
        _ = y₂ ^ b * (y₁ ^ a * z₂ ^ b) * z₁ ^ a := by rw [hz1y2.eq]
        _ = (y₂ ^ b * y₁ ^ a) * (z₂ ^ b * z₁ ^ a) := by group
        _ = (y₂ ^ b * y₁ ^ a) * z₃ := by rw [huw]

theorem central_core' (IU : Claims1113.InputU43) (D : Claims1113.CentralData Y V x)
    (hL : GLAPLayer 3 (⊤ : Subgroup Y) ≠ ⊥) : False := by
  obtain ⟨c₁, hc₁⟩ : ∃ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) := by
    by_contra hne
    push Not at hne
    exact hL (le_bot_iff.1 (Claims1113.layer_le_of D.hO fun c hc => (hne c hc).elim))
  by_cases h1 : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c = c₁
  · exact D.false_of_one IU hc₁ h1
  push Not at h1
  obtain ⟨c₂, hc₂, h21⟩ := h1
  by_cases h2 : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c = c₁ ∨ c = c₂
  · exact false_of_pair' IU D hc₁ hc₂ (Ne.symm h21) h2
  push Not at h2
  obtain ⟨c₃, hc₃, h31, h32⟩ := h2
  exact false_of_three' IU D hc₁ hc₂ hc₃ (Ne.symm h21) (Ne.symm h31) (Ne.symm h32)

end CentralCases

section Assembly

theorem lemma1113O3Claim_of_inputs' (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (hSolv : Claims11x.Lemma1113SolvClaim) (IU : Claims1113.InputU43) :
    Claims11x.Lemma1113O3Claim := by
  intro G _ _ m p B M E A a K h hp hL
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, x, R, hKY, hVL, hVel, hV9, hx3, hxV, hxnV, hsolv, hrk, htr, hRt, hZ⟩ :=
    Claims1113.exists_tilde_data h1111 h1112 h119 h104ii hSolv h hL
  have hO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3
  by_contra hP
  have hP3 : 3 ∣ Nat.card (CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1
      (CFSG.pCore_isPGroup (p := 3) (G := ↥M ⧸ GLAPPrimeCore 3 ↥M))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hP ((Subgroup.eq_bot_iff_card _).2 hk)
    rw [hk]
    exact dvd_pow_self 3 hk0
  have hVP := Claims1113.le_of_normal_three hRt hZ htr (CFSG.pCore_normal (p := 3)) hP3
  have hVc : ∀ c : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), IsComponentOf c ⊤ →
      ∀ v ∈ V, ∀ u ∈ c, v * u = u * v := by
    intro c hc v hv u hu
    have hvC := CFSG.WholeGroup.pCore_le_centralizer_layer 3 (hVP hv)
    have huL : u ∈ CFSG.layer (↥M ⧸ GLAPPrimeCore 3 ↥M) := by
      rw [CFSG.layer_eq_componentClassification]
      exact CFSG.ComponentClassification.Layer.component_le hc hu
    exact (Subgroup.mem_centralizer_iff.1 hvC u huL).symm
  exact central_core' IU ⟨hO, hKY, hVL, hVc, hVel, hV9, hx3, hxV, hxnV, hsolv, hrk, htr⟩ hL

theorem nonsolvQuasisimpleClaim_of_partI' (h1111 : Lemma1111Statement)
    (h1112 : Lemma1112Statement) (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (h111 : Prop111Statement) (hNorm : Claims11x.InputL34SylowNormalizer)
    (IU : Claims1113.InputU43) : Lemma1113b.NonsolvQuasisimpleClaim :=
  Claims11x.nonsolvQuasisimpleClaim_of_inputs h1111 h1112 h119 h104ii
    (lemma1113O3Claim_of_inputs' h1111 h1112 h119 h104ii
      (Claims11x.lemma1113SolvClaim_of_inputs h1111 h1112 h119 h111 hNorm) IU)
    (Claims1113.lemma1113SimpleClaim_of_inputs' h1111 h1112 h119 h104ii h111 hNorm)

theorem lemma1113_of_notBalanced' (I13 : Lemma1113b.Input13_4) (h1111 : Lemma1111Statement)
    (h1112 : Lemma1112Statement) (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hNB : Claims1113b.NotBalancedL34A5) (hI2320 : Input23_20_W)
    (hI29 : Claims1113.Input29_5') (hNorm : Claims11x.InputL34SylowNormalizer)
    (hAut : Claims11x.InputAutL34Order27) (IU : Claims1113.InputU43) :
    Lemma1113Statement :=
  have hQ := nonsolvQuasisimpleClaim_of_partI' h1111 h1112 h119 h104ii h111 hNorm IU
  lemma1113_of_inputs h1111 (Lemma1113b.tildeCore_of_inputs I13 hQ
    (Claims1113b.nonsolvChevClaim_core' hQ h1111 h1112 h119 h104v h111 h112 h115 hNB hI2320
      (Claims1113.input29_5_of' hI29) hNorm hAut))

theorem lemma1113_of_partI_cert'
    (I13 : Lemma1113b.Input13_4) (h1111 : Lemma1111Statement)
    (h1112 : Lemma1112Statement) (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hI2320 : Input23_20_W)
    (hI29 : Claims1113.Input29_5') (hNorm : Claims11x.InputL34SylowNormalizer)
    (hAut : Claims11x.InputAutL34Order27) (IU : Claims1113.InputU43) :
    Lemma1113Statement :=
  lemma1113_of_notBalanced' I13 h1111 h1112 h119 h104ii h104v h111 h112 h115
    Claims1113b.notBalancedL34A5_holds hI2320 hI29 hNorm hAut IU

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc6
