module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630FiveC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630FivePx
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Aux

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankF smallRankR smallRankIsQ8D8 SmallRankPlane)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_centralizer_of_mem {F : Subgroup G} {g : G}
    (hg : g ∈ normalizer (F : Set G)) :
    g ∈ normalizer ((centralizer (F : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact conj_mem_centralizer_of_mem_normalizer hg hk
  · intro hk
    have h := conj_mem_centralizer_of_mem_normalizer ((normalizer (F : Set G)).inv_mem hg) hk
    convert h using 1
    group

theorem stepFiveFPF_of (hGAP : KFactAutQ8D8Five) : StepFiveFPF := by
  intro G _ _ p P M x z T f hL
  have hp5 : p = 5 := by
    have h1 := hL.situation.p_ge
    have h2 := hL.lemma628.1
    omega
  subst hp5
  intro g hgN hgp hgC a ha ha1 hfix
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5' : Nat.Prime 5 := by norm_num
  have hf : f.Prime := hL.prime
  have hf2 : f ≠ 2 := hL.ne_two
  haveI : Fact f.Prime := ⟨hf⟩
  have hFc : Nat.card (smallRankF 5 f x) = f ^ 4 := hL.lemma629.2.2.2.2.1
  have hFM : smallRankF 5 f x ⊓ M = ⊥ := smallRankF_inf_eq_bot hf hf2 hL.lemma628.2.2.2
  have hFne : smallRankF 5 f x ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFc
    have h4 : 2 ≤ f ^ 4 := le_trans hf.two_le (Nat.le_self_pow (by norm_num) f)
    rw [← hFc] at h4
    norm_num at h4
  have hC_z : centralizer ({z} : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.centralizer_singleton_le hL.situation hL.central
  have hx : x ∈ (P : Subgroup G) := hL.point.mem
  have hx1 : x ≠ 1 := hL.point.ne_one hL.situation.prime
  have hx5 : x ^ 5 = 1 := hL.point.pow_eq_one
  have hz5 : z ^ 5 = 1 := hL.central.pow_eq_one
  have hz1 : z ≠ 1 := hL.central.ne_one
  have hQ8 : smallRankIsQ8D8 (smallRankR x z T) := hL.lemma628.2.2.1 rfl
  have hpx := px_eq_plane hL.situation hL.point hL.central hL.sylowTwo hQ8 hGAP
  have hB : SmallRankPlane 5 (P : Subgroup G) x z :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.plane_of_central hL.situation hL.point hL.central
  have hxF : ∀ Q : Subgroup G, IsPGroup 5 Q → x ∉ (frattini ↥Q).map Q.subtype :=
    fun Q hQ => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.x_not_mem_frattini
      hL.situation hL.point hQ
  have hcard5 : Nat.card (zpowers x) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx5 hx1]
  set F : Subgroup G := smallRankF 5 f x with hFdef
  set N : Subgroup G := normalizer (F : Set G) with hNdef
  set C : Subgroup G := centralizer (F : Set G) with hCdef
  set Px : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hPxdef
  have hPxpg : IsPGroup 5 Px := (P.isPGroup').to_le inf_le_left
  have hxC : x ∈ C := mem_centralizer_iff.mpr
    (fun a ha => mem_centralizer_singleton_iff.mp (smallRankF_le_centralizer (p := 5) hf ha))
  have hzN : z ∈ N := central_mem_normalizer_smallRankF hp5' hf hx hL.central.centralizes
  have hzNC : z ∈ normalizer (C : Set G) := normalizer_centralizer_of_mem hzN
  have hzC : z ∉ C := by
    intro hzC
    obtain ⟨a', ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
    have ha'G : (a' : G) ≠ 1 := fun h => ha' (Subtype.ext h)
    exact ha'G (eq_one_of_mem_smallRankF_comm hC_z hFM a'.2 (mem_centralizer_iff.mp hzC a' a'.2))
  have hxF' : ∀ Q : Subgroup G, IsPGroup 5 Q → x ∉ (frattini ↥Q).map Q.subtype := hxF
  have hsyl : ∀ D : Subgroup G, D ≤ C → IsPGroup 5 D → Nat.card D ≤ 5 :=
    fun D hD hDp => card_le_five_of_centralizer hB C hxC hzNC hzC hz5 hz1 hxF' hD hDp
  have hPxN : Px ≤ N := fun y hy => mem_normalizer_smallRankF hp5' hf hy.2
  have hxPx : x ∈ Px := ⟨hx, mem_centralizer_singleton_iff.mpr rfl⟩
  have hPx_max : ∀ Q : Subgroup G, IsPGroup 5 Q → Q ≤ N → Px ≤ Q → Q = Px := by
    intro Q hQ hQN hPxQ
    have hxQ : x ∈ Q := hPxQ hxPx
    have hA_le : zpowers x ≤ Q ⊓ C := zpowers_le.mpr ⟨hxQ, hxC⟩
    have hAcard : Nat.card ↥(Q ⊓ C) ≤ 5 := hsyl _ inf_le_right (hQ.to_le inf_le_left)
    have hAeq : Q ⊓ C = zpowers x :=
      (Subgroup.eq_of_le_of_card_ge hA_le (by rw [hcard5]; exact hAcard)).symm
    have hQC : Q ≤ centralizer ({x} : Set G) := by
      intro q hq
      have hqN : q ∈ N := hQN hq
      have hnorm : ∀ y ∈ zpowers x, q * y * q⁻¹ ∈ zpowers x := by
        intro y hy
        have hyA : y ∈ Q ⊓ C := by rw [hAeq]; exact hy
        have hqy : q * y * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hyA.1) (Q.inv_mem hq)
        have hqyC : q * y * q⁻¹ ∈ C := conj_mem_centralizer_of_mem_normalizer hqN hyA.2
        have hmem : q * y * q⁻¹ ∈ Q ⊓ C := ⟨hqy, hqyC⟩
        rw [hAeq] at hmem
        exact hmem
      obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
      have hqk : q ^ 5 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hcomm := centralizes_of_normalizes_zpowers (orderOf_eq_prime hx5 hx1) hqk hnorm
      exact mem_centralizer_singleton_iff.mpr (by
        calc q * x = (q * x * q⁻¹) * q := by group
          _ = x * q := by rw [hcomm])
    obtain ⟨Q₀, hQ₀⟩ := hL.point.sylow
    have hQ'p : IsPGroup 5 (Q.subgroupOf (centralizer ({x} : Set G))) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
      exact IsPGroup.iff_card.mpr ⟨k, by
        rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hk]⟩
    have hle : (Q₀ : Subgroup (centralizer ({x} : Set G))) ≤
        Q.subgroupOf (centralizer ({x} : Set G)) := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      have hm : (y : G) ∈ (Q₀ : Subgroup (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hQ₀] at hm
      exact hPxQ hm
    have hmax := Q₀.is_maximal' hQ'p hle
    calc Q = (Q.subgroupOf (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hQC).symm
      _ = (Q₀ : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype := by
          rw [hmax]
      _ = Px := hQ₀
  have hPxN_pg : IsPGroup 5 (Px.subgroupOf N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPxpg
    exact IsPGroup.iff_card.mpr ⟨k, by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPxN).toEquiv, hk]⟩
  have hPN_max : ∀ Q' : Subgroup N, IsPGroup 5 Q' → Px.subgroupOf N ≤ Q' →
      Q' = Px.subgroupOf N := by
    intro Q' hQ' hle
    have hmap : Q'.map N.subtype = Px := by
      apply hPx_max (Q'.map N.subtype) (hQ'.map N.subtype)
      · rintro _ ⟨y, _, rfl⟩
        exact y.2
      · intro y hy
        have hyN : (⟨y, hPxN hy⟩ : N) ∈ Q' := hle (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_map.mpr ⟨⟨y, hPxN hy⟩, hyN, rfl⟩
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q').symm
  let PN : Sylow 5 N :=
    { toSubgroup := Px.subgroupOf N
      isPGroup' := hPxN_pg
      is_maximal' := fun {Q'} hQ' hle => hPN_max Q' hQ' hle }
  obtain ⟨e, m, hm5, hgord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 5
    (by norm_num)
  set g' : G := g ^ m with hg'def
  have hg'N : g' ∈ N := N.pow_mem hgN m
  have hg'5 : g' ^ 5 ^ e = 1 := by
    rw [hg'def, ← pow_mul, mul_comm, ← hgord, pow_orderOf_eq_one]
  have hg'fix : g' * a * g'⁻¹ = a := by
    have h1 : MulAut.conj g a = a := by
      rw [MulAut.conj_apply]
      exact hfix
    have h2 := pow_fixes h1 m
    rw [← map_pow, MulAut.conj_apply] at h2
    exact h2
  have hg'C : g' ∉ C := by
    intro hg'C
    have hcop : Nat.Coprime m 5 := ((Nat.Prime.coprime_iff_not_dvd hp5').mpr hm5).symm
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    push_cast at huv
    have e1 : g ^ ((m : ℤ) * u) = g' ^ u := by
      rw [zpow_mul, zpow_natCast, hg'def]
    have e2 : g ^ ((5 : ℤ) * v) = (g ^ 5) ^ v := by
      rw [zpow_mul]
      simp
    have hgeq : g = g' ^ u * (g ^ 5) ^ v := by
      rw [← e1, ← e2, ← zpow_add, show (m : ℤ) * u + 5 * v = 1 by linear_combination huv,
        zpow_one]
    have hgC2 : g ∈ C := by
      rw [hgeq]
      exact C.mul_mem (C.zpow_mem hg'C u) (C.zpow_mem hgp v)
    exact hgC hgC2
  have hg'N_pg : IsPGroup 5 ((zpowers g').subgroupOf N) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp5').mp (orderOf_dvd_of_pow_eq_one hg'5)
    refine IsPGroup.iff_card.mpr ⟨k, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hg'N)).toEquiv, Nat.card_zpowers, hk]
  obtain ⟨QN, hQN⟩ := hg'N_pg.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥N) PN QN
  have hgQN : (⟨g', hg'N⟩ : N) ∈ (QN : Subgroup N) :=
    hQN (Subgroup.mem_subgroupOf.mpr (mem_zpowers g'))
  rw [← hn, Sylow.coe_subgroup_smul] at hgQN
  have hbPx : (n : G)⁻¹ * g' * (n : G) ∈ Px := by
    have h1 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hgQN
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [MulAut.conj_apply] using h2
  set b : G := (n : G)⁻¹ * g' * (n : G) with hbdef
  have hbB : b ∈ zpowers x ⊔ zpowers z := by
    rw [← hpx]
    exact hbPx
  have hb5 : b ^ 5 = 1 := hB.isElemAbelian.2 b hbB
  have hgb : (n : G) * b * (n : G)⁻¹ = g' := by
    rw [hbdef]
    group
  have ha'F : (n : G)⁻¹ * a * (n : G) ∈ F := by
    have h := (mem_normalizer_iff.mp (N.inv_mem n.2) a).mp ha
    simpa using h
  have ha'1 : (n : G)⁻¹ * a * (n : G) ≠ 1 := by
    intro h
    apply ha1
    calc a = (n : G) * ((n : G)⁻¹ * a * (n : G)) * (n : G)⁻¹ := by group
      _ = 1 := by rw [h]; group
  set a' : G := (n : G)⁻¹ * a * (n : G) with ha'def
  have hbfix : b * a' * b⁻¹ = a' := by
    have h1 : g' * a * g'⁻¹ = a := hg'fix
    rw [← hgb] at h1
    calc b * a' * b⁻¹ = (n : G)⁻¹ * ((n : G) * b * (n : G)⁻¹ * a *
          ((n : G) * b * (n : G)⁻¹)⁻¹) * (n : G) := by
          rw [ha'def, hbdef]
          group
      _ = a' := by rw [h1, ha'def]
  have hcomm_ba : b * a' = a' * b := by
    calc b * a' = (b * a' * b⁻¹) * b := by group
      _ = a' * b := by rw [hbfix]
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hxa' : x ∈ centralizer ({a'} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (smallRankF_le_centralizer (p := 5) hf ha'F)).symm
  have hba' : b ∈ centralizer ({a'} : Set G) := mem_centralizer_singleton_iff.mpr hcomm_ba
  have hbx : b ∈ zpowers x := by
    by_contra hbx
    have hcomm_e : ∀ e ∈ zpowers x, e * b = b * e := by
      intro e he
      have hes : e ∈ zpowers x ⊔ zpowers z := zpowers_le.mpr hxB he
      have := hB.isElemAbelian.1.is_comm.comm (⟨e, hes⟩ : ↥(zpowers x ⊔ zpowers z))
        ⟨b, hbB⟩
      exact congrArg Subtype.val this
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num : Nat.Prime 5)
      (zpowers x) hb5 hbx hcomm_e
    rw [hcard5] at hcard
    have hle : zpowers x ⊔ zpowers b ≤ zpowers x ⊔ zpowers z :=
      sup_le (zpowers_le.mpr hxB) (zpowers_le.mpr hbB)
    have heq : zpowers x ⊔ zpowers b = zpowers x ⊔ zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hB.card_eq]; norm_num)
    have hzb : z ∈ zpowers x ⊔ zpowers b := by
      rw [heq]
      exact mem_sup_right (mem_zpowers z)
    have hcent : zpowers x ⊔ zpowers b ≤ centralizer ({a'} : Set G) :=
      sup_le (zpowers_le.mpr hxa') (zpowers_le.mpr hba')
    have hza' : z * a' = a' * z := mem_centralizer_singleton_iff.mp (hcent hzb)
    have hM : a' ∈ M := hC_z (mem_centralizer_singleton_iff.mpr hza'.symm)
    have hFM' : a' ∈ F ⊓ M := ⟨ha'F, hM⟩
    rw [hFM, Subgroup.mem_bot] at hFM'
    exact ha'1 hFM'
  have hbC : b ∈ C := zpowers_le.mpr hxC hbx
  have hg'C' : g' ∈ C := by
    rw [← hgb]
    exact conj_mem_centralizer_of_mem_normalizer n.2 hbC
  exact hg'C hg'C'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
