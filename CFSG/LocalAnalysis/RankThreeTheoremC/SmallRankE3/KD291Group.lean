module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open Subgroup

section E0
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem kd291_aux_A_mem_sup {E F : Subgroup G} (hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a)
    {g : G} (hg : g ∈ E ⊔ F) : ∃ a ∈ E, ∃ b ∈ F, a * b = g := by
  have hEFc : E ⊔ F = Subgroup.closure ((E : Set G) ∪ F) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hEFc] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, F.one_mem, mul_one x⟩
    · exact ⟨1, E.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, E.one_mem, 1, F.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    obtain ⟨a', ha', b', hb', rfl⟩ := ihy
    refine ⟨a * a', E.mul_mem ha ha', b * b', F.mul_mem hb hb', ?_⟩
    calc a * a' * (b * b') = a * (a' * b) * b' := by simp only [mul_assoc]
      _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
      _ = a * b * (a' * b') := by simp only [mul_assoc]
  | inv x _ ihx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    refine ⟨a⁻¹, E.inv_mem ha, b⁻¹, F.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hc a⁻¹ (E.inv_mem ha) b⁻¹ (F.inv_mem hb)

theorem kd291_aux_A_inf_eq_bot {E F : Subgroup G} (hF : Nat.card F = p) (hFE : ¬ F ≤ E) :
    E ⊓ F = ⊥ := by
  have hpp : p.Prime := Fact.out
  have hdvd : Nat.card ↥(E ⊓ F) ∣ p := by
    have h0 := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ F ≤ F)
    rwa [hF] at h0
  rcases (Nat.dvd_prime hpp).1 hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hKeq : E ⊓ F = F := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    apply hFE
    intro y hy
    have hy' : y ∈ E ⊓ F := by rw [hKeq]; exact hy
    exact (Subgroup.mem_inf.1 hy').1

theorem kd291_aux_A_isElemAbelian_zpowers {y : G} (hy : y ^ p = 1) :
    IsElemAbelian p (zpowers y) := by
  rw [Subgroup.zpowers_eq_closure]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  · intro a ha
    rw [Set.mem_singleton_iff.1 ha]
    exact hy

theorem kd291_card_sup_of_commute {E F : Subgroup G} (hEF : E ⊓ F = ⊥)
    (hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) :
    Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F := by
  have hbij : Function.Bijective (fun ab : E × F =>
      (⟨(ab.1 : G) * (ab.2 : G), Subgroup.mul_mem_sup ab.1.2 ab.2.2⟩ : ↥(E ⊔ F))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have h1 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      have hmem : a'⁻¹ * a ∈ E ⊓ F := by
        refine Subgroup.mem_inf.2 ⟨E.mul_mem (E.inv_mem ha') ha, ?_⟩
        rw [h1]
        exact F.mul_mem hb' (F.inv_mem hb)
      rw [hEF, Subgroup.mem_bot] at hmem
      have ha_eq : a' = a := inv_mul_eq_one.1 hmem
      subst ha_eq
      have hb_eq : b = b' := mul_left_cancel h'
      subst hb_eq
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha, b, hb, hab⟩ := kd291_aux_A_mem_sup hc hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective _ hbij).symm

theorem kd291_pair_data {x z : G} (hxz : Commute x z) (hx : orderOf x = p) (hz : orderOf z = p)
    (hzx : z ∉ zpowers x) :
    IsElemAbelian p (zpowers x ⊔ zpowers z) ∧
      Nat.card (zpowers x ⊔ zpowers z : Subgroup G) = p ^ 2 := by
  have hEF : zpowers x ⊓ zpowers z = ⊥ :=
    kd291_aux_A_inf_eq_bot (by rw [Nat.card_zpowers, hz])
      (fun h => hzx (h (Subgroup.mem_zpowers z)))
  have hc : ∀ a ∈ zpowers x, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hxz.zpow_zpow n m).eq
  have hEab : IsElemAbelian p (zpowers x) :=
    kd291_aux_A_isElemAbelian_zpowers (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hFab : IsElemAbelian p (zpowers z) :=
    kd291_aux_A_isElemAbelian_zpowers (by rw [← hz]; exact pow_orderOf_eq_one z)
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hEab hFab hc, ?_⟩
  rw [kd291_card_sup_of_commute hEF hc, Nat.card_zpowers, Nat.card_zpowers, hx, hz, sq]

theorem kd291_mem_of_rank (hG : pRank p (⊤ : Subgroup G) ≤ 2) {B : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) {u : G} (hu : u ^ p = 1)
    (huc : ∀ b ∈ B, u * b = b * u) : u ∈ B := by
  by_contra huB
  have hpp : p.Prime := Fact.out
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact huB B.one_mem
  have hup : orderOf u = p := orderOf_eq_prime hu hu1
  have hEF : B ⊓ zpowers u = ⊥ :=
    kd291_aux_A_inf_eq_bot (by rw [Nat.card_zpowers, hup])
      (fun h => huB (h (Subgroup.mem_zpowers u)))
  have hc : ∀ a ∈ B, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hcu : Commute a u := (huc a ha).symm
    exact (hcu.zpow_right n).eq
  have hZ : IsElemAbelian p (zpowers u) := kd291_aux_A_isElemAbelian_zpowers hu
  have hsup : IsElemAbelian p (B ⊔ zpowers u) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hB hZ hc
  have hcard : Nat.card ↥(B ⊔ zpowers u) = p ^ 3 := by
    rw [kd291_card_sup_of_commute hEF hc, hBc, Nat.card_zpowers, hup]
    ring
  have hlow : 3 ≤ CFSG.pRank p (⊤ : Subgroup G) := by
    have hA : IsElemAbelian p ((B ⊔ zpowers u).subgroupOf (⊤ : Subgroup G)) :=
      CFSG.Open.IsElemAbelian.comap hsup (Subgroup.subtype_injective _)
    have hAcard : Nat.card ↥((B ⊔ zpowers u).subgroupOf (⊤ : Subgroup G)) = p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : B ⊔ zpowers u ≤ ⊤)).toEquiv,
        hcard]
    unfold CFSG.pRank
    refine le_csSup ?_ ⟨(B ⊔ zpowers u).subgroupOf (⊤ : Subgroup G), hA.isElementaryAbelian,
      hAcard⟩
    refine ⟨Nat.card ↥(⊤ : Subgroup G), ?_⟩
    rintro r ⟨A, -, hr⟩
    have h1 : Nat.card ↥A ≤ Nat.card ↥(⊤ : Subgroup G) := Subgroup.card_le_card_group A
    have h2 : r < p ^ r := Nat.lt_pow_self hpp.one_lt
    have h3 : p ^ r ≤ Nat.card ↥(⊤ : Subgroup G) := by rw [← hr]; exact h1
    exact le_of_lt (lt_of_lt_of_le h2 h3)
  omega

theorem kd291_pCore_le_sylow (Q : Sylow p G) : CFSG.pCore p G ≤ (Q : Subgroup G) := by
  haveI hN : (CFSG.pCore p G).Normal := CFSG.pCore_normal
  exact IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Q

theorem kd291_aux_B_comm {x z : G} (hxc : x ∈ Subgroup.center G)
    (hzR : ∀ y ∈ CFSG.pCore p G, y * z = z * y) {r : G} (hr : r ∈ CFSG.pCore p G) :
    ∀ b ∈ (zpowers x ⊔ zpowers z : Subgroup G), r * b = b * r := by
  have hx' : x ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_center_iff.1 hxc r
  have hz' : z ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hzR r hr
  have hle : (zpowers x ⊔ zpowers z : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hx') (Subgroup.zpowers_le.2 hz')
  intro b hb
  exact Subgroup.mem_centralizer_iff.1 (hle hb) r (Set.mem_singleton r)

theorem kd291_aux_B_coprime_eq_one (hp2 : p ≠ 2) {x z : G} (hxc : x ∈ Subgroup.center G)
    (hx : orderOf x = p) (hz : orderOf z = p) (hzx : z ∉ zpowers x)
    (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (hcon : centralizer ((CFSG.pCore p G : Subgroup G) : Set G) ≤ CFSG.pCore p G)
    (hzR : ∀ y ∈ CFSG.pCore p G, y * z = z * y)
    {a : G} (ha : a ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))
    (hcop : Nat.Coprime (orderOf a) p) : a = 1 := by
  have hxz : Commute x z := (Subgroup.mem_center_iff.1 hxc z).symm
  obtain ⟨hBab, hBc⟩ := kd291_pair_data hxz hx hz hzx
  haveI hN : (CFSG.pCore p G).Normal := CFSG.pCore_normal
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (CFSG.pCore p G),
      α = MulAut.conjNormal (H := CFSG.pCore p G) a := ⟨_, rfl⟩
  have hαapply : ∀ r : CFSG.pCore p G, ((α r : CFSG.pCore p G) : G) = a * (r : G) * a⁻¹ := by
    intro r
    rw [hαdef]
    exact MulAut.conjNormal_apply a r
  have hord : orderOf α ∣ orderOf a := by
    rw [hαdef]
    exact orderOf_map_dvd (MulAut.conjNormal (H := CFSG.pCore p G)) a
  have hαcop : Nat.Coprime (orderOf α) p := Nat.Coprime.coprime_dvd_left hord hcop
  have hfix : ∀ r : CFSG.pCore p G, r ^ p = 1 → α r = r := by
    intro r hrp
    have hrG : (r : G) ^ p = 1 := by
      simpa using congrArg Subtype.val hrp
    have hrB : (r : G) ∈ (zpowers x ⊔ zpowers z : Subgroup G) :=
      kd291_mem_of_rank hG hBab hBc hrG (kd291_aux_B_comm hxc hzR r.2)
    have hra : (r : G) * a = a * (r : G) := Subgroup.mem_centralizer_iff.1 ha (r : G) hrB
    apply Subtype.ext
    rw [hαapply, ← hra, mul_inv_cancel_right]
  have hα1 : α = 1 :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      hp2 CFSG.pCore_isPGroup hαcop hfix
  have haR : a ∈ centralizer ((CFSG.pCore p G : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    have h1 : α ⟨r, hr⟩ = ⟨r, hr⟩ := by simp [hα1]
    have h2 : a * r * a⁻¹ = r := by
      have h3 := hαapply ⟨r, hr⟩
      rw [h1] at h3
      exact h3.symm
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have haPR : a ∈ CFSG.pCore p G := hcon haR
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := G) ⟨a, haPR⟩
  have hak : a ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd : orderOf a ∣ p ^ k := orderOf_dvd_of_pow_eq_one hak
  have hone : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hcop) dvd_rfl hdvd
  exact orderOf_eq_one_iff.1 hone

theorem kd291_pair_normal {x z : G} (hxc : x ∈ Subgroup.center G)
    (hx : orderOf x = p) (hz : orderOf z = p) (hzx : z ∉ zpowers x)
    (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (hcon : centralizer ((CFSG.pCore p G : Subgroup G) : Set G) ≤ CFSG.pCore p G)
    (hzR : ∀ y ∈ CFSG.pCore p G, y * z = z * y) :
    ∀ g : G, g * z * g⁻¹ ∈ (zpowers x ⊔ zpowers z : Subgroup G) := by
  intro g
  have hxz : Commute x z := (Subgroup.mem_center_iff.1 hxc z).symm
  obtain ⟨hBab, hBc⟩ := kd291_pair_data hxz hx hz hzx
  have hzN : z ∈ CFSG.pCore p G :=
    hcon (Subgroup.mem_centralizer_iff.2 fun h hh => hzR h hh)
  have hu : g * z * g⁻¹ ∈ CFSG.pCore p G :=
    (CFSG.pCore_normal (p := p) (G := G)).conj_mem z hzN g
  have hzp : z ^ p = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hup : (g * z * g⁻¹) ^ p = 1 := by
    rw [conj_pow, hzp]
    simp
  exact kd291_mem_of_rank hG hBab hBc hup (fun b hb => kd291_aux_B_comm hxc hzR hu b hb)

theorem kd291_isPGroup_centralizer_pair (hp2 : p ≠ 2) {x z : G} (hxc : x ∈ Subgroup.center G)
    (hx : orderOf x = p) (hz : orderOf z = p) (hzx : z ∉ zpowers x)
    (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (hcon : centralizer ((CFSG.pCore p G : Subgroup G) : Set G) ≤ CFSG.pCore p G)
    (hzR : ∀ y ∈ CFSG.pCore p G, y * z = z * y) :
    IsPGroup p (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) := by
  have hpp : p.Prime := Fact.out
  have hpos : Nat.card (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) ≠ 0 :=
    Nat.card_pos.ne'
  have hprime : ∀ {d : ℕ}, d.Prime →
      d ∣ Nat.card (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) → d = p := by
    intro d hd hdA
    by_contra hne
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' d hdA
    have hbG : orderOf (b : G) = d := (Subgroup.orderOf_coe b).trans hb
    have hcop : Nat.Coprime (orderOf (b : G)) p := by
      rw [hbG]
      exact (Nat.coprime_primes hd hpp).2 hne
    have h1 : (b : G) = 1 :=
      kd291_aux_B_coprime_eq_one hp2 hxc hx hz hzx hG hcon hzR b.2 hcop
    rw [h1, orderOf_one] at hbG
    have := hd.one_lt
    omega
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos hprime)

theorem kd291_aux_C_mul_pair {x z : G} (hxz : Commute x z) (a b c d : ℤ) :
    x ^ a * z ^ b * (x ^ c * z ^ d) = x ^ (a + c) * z ^ (b + d) := by
  have h1 : z ^ b * x ^ c = x ^ c * z ^ b := (hxz.zpow_zpow c b).eq.symm
  calc x ^ a * z ^ b * (x ^ c * z ^ d) = x ^ a * (z ^ b * x ^ c) * z ^ d := by
        simp only [mul_assoc]
    _ = x ^ a * (x ^ c * z ^ b) * z ^ d := by rw [h1]
    _ = (x ^ a * x ^ c) * (z ^ b * z ^ d) := by simp only [mul_assoc]
    _ = x ^ (a + c) * z ^ (b + d) := by rw [zpow_add, zpow_add]

theorem kd291_aux_C_unique {x z : G} (hx : orderOf x = p) (hz : orderOf z = p)
    (hzx : z ∉ zpowers x) (i j : ℤ) (h : x ^ i * z ^ j = 1) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  have hp : Nat.Prime p := Fact.out
  have hzj : (p : ℤ) ∣ j := by
    by_contra hnd
    obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hnd
    have hzp : z ^ (u * p) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz]; exact dvd_mul_left _ _)
    have hzpow : z ^ (v * j) = z := by
      have h1 : z ^ (u * p + v * j) = z := by rw [huv, zpow_one]
      rw [zpow_add, hzp, one_mul] at h1
      exact h1
    apply hzx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-i * v, ?_⟩
    calc x ^ (-i * v) = (x ^ (-i)) ^ v := zpow_mul x (-i) v
      _ = ((x ^ i)⁻¹) ^ v := by rw [zpow_neg]
      _ = (z ^ j) ^ v := by rw [← eq_inv_of_mul_eq_one_right h]
      _ = z ^ (j * v) := (zpow_mul z j v).symm
      _ = z ^ (v * j) := by rw [mul_comm]
      _ = z := hzpow
  have hzj1 : z ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz]; exact hzj)
  have hxi : x ^ i = 1 := by rw [hzj1, mul_one] at h; exact h
  have hxi' : ((orderOf x : ℕ) : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.mpr hxi
  rw [hx] at hxi'
  exact ⟨hxi', hzj⟩

theorem kd291_aux_C_eq {x z : G} (hxz : Commute x z) (hx : orderOf x = p)
    (hz : orderOf z = p) (hzx : z ∉ zpowers x) (i j k l : ℤ)
    (h : x ^ i * z ^ j = x ^ k * z ^ l) :
    (i : ZMod p) = (k : ZMod p) ∧ (j : ZMod p) = (l : ZMod p) := by
  have h1 : x ^ (i - k) * z ^ (j - l) = 1 := by
    rw [sub_eq_add_neg i k, sub_eq_add_neg j l, ← kd291_aux_C_mul_pair hxz i j (-k) (-l), h,
      kd291_aux_C_mul_pair hxz k l (-k) (-l)]
    simp
  obtain ⟨hi, hj⟩ := kd291_aux_C_unique hx hz hzx _ _ h1
  exact ⟨((ZMod.intCast_eq_intCast_iff_dvd_sub k i p).mpr hi).symm,
    ((ZMod.intCast_eq_intCast_iff_dvd_sub l j p).mpr hj).symm⟩

theorem kd291_aux_C_form {x z : G} (hxz : Commute x z) :
    ∀ b ∈ (zpowers x ⊔ zpowers z : Subgroup G), ∃ i j : ℤ, b = x ^ i * z ^ j := by
  let S : Subgroup G :=
    { carrier := {b | ∃ i j : ℤ, b = x ^ i * z ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        exact ⟨i + k, j + l, kd291_aux_C_mul_pair hxz i j k l⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        have h2 : x ^ i * z ^ j * (x ^ (-i) * z ^ (-j)) = 1 := by
          rw [kd291_aux_C_mul_pair hxz i j (-i) (-j)]
          simp
        exact (eq_inv_of_mul_eq_one_right h2).symm }
  have hle : zpowers x ⊔ zpowers z ≤ S := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact ⟨1, 0, by simp⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨0, 1, by simp⟩
  intro b hb
  obtain ⟨i, j, hij⟩ := hle hb
  exact ⟨i, j, hij⟩

theorem kd291_derivedSeries_two_le {x z : G} (hxc : x ∈ Subgroup.center G) (hx : orderOf x = p)
    (hz : orderOf z = p) (hzx : z ∉ zpowers x)
    (hBn : ∀ g : G, g * z * g⁻¹ ∈ (zpowers x ⊔ zpowers z : Subgroup G)) :
    derivedSeries G 2 ≤ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
  have hcomm : Commute x z := (Subgroup.mem_center_iff.mp hxc z).symm
  have hcx : ∀ g : G, Commute g x := fun g => Subgroup.mem_center_iff.mp hxc g
  have hconjx : ∀ (g : G) (n : ℤ), g * x ^ n * g⁻¹ = x ^ n := by
    intro g n
    rw [((hcx g).zpow_right n).eq, mul_inv_cancel_right]
  have hex : ∀ g : G, ∃ i j : ℤ, g * z * g⁻¹ = x ^ i * z ^ j :=
    fun g => kd291_aux_C_form hcomm _ (hBn g)
  choose ia ib hcoef using hex
  obtain ⟨ax, hax⟩ : ∃ f : G → ZMod p, ∀ g, f g = ((ia g : ℤ) : ZMod p) :=
    ⟨fun g => ((ia g : ℤ) : ZMod p), fun g => rfl⟩
  obtain ⟨az, haz⟩ : ∃ f : G → ZMod p, ∀ g, f g = ((ib g : ℤ) : ZMod p) :=
    ⟨fun g => ((ib g : ℤ) : ZMod p), fun g => rfl⟩
  have hxpow : ∀ n : ℤ, (n : ZMod p) = 0 → x ^ n = 1 := by
    intro n hn
    have hd : (p : ℤ) ∣ 0 - n :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub n 0 p).mp (by simpa using hn)
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; simpa using hd)
  have hzpow : ∀ n : ℤ, (n : ZMod p) = 1 → z ^ n = z := by
    intro n hn
    have hd : (p : ℤ) ∣ n - 1 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub 1 n p).mp (by simpa using hn.symm)
    have h1 : z ^ (n - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz]; exact hd)
    calc z ^ n = z ^ (n - 1 + 1) := by rw [sub_add_cancel]
      _ = z ^ (n - 1) * z := zpow_add_one z (n - 1)
      _ = z := by rw [h1, one_mul]
  have hcomp : ∀ g h : G, g * h * z * (g * h)⁻¹ =
      x ^ (ia h + ia g * ib h) * z ^ (ib g * ib h) := by
    intro g h
    calc g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
      _ = g * (x ^ ia h * z ^ ib h) * g⁻¹ := by rw [hcoef h]
      _ = (g * x ^ ia h * g⁻¹) * (g * z ^ ib h * g⁻¹) := by group
      _ = x ^ ia h * (g * z ^ ib h * g⁻¹) := by rw [hconjx]
      _ = x ^ ia h * (g * z * g⁻¹) ^ ib h := by rw [conj_zpow]
      _ = x ^ ia h * (x ^ ia g * z ^ ib g) ^ ib h := by rw [hcoef g]
      _ = x ^ ia h * ((x ^ ia g) ^ ib h * (z ^ ib g) ^ ib h) := by
        rw [(hcomm.zpow_zpow (ia g) (ib g)).mul_zpow]
      _ = x ^ ia h * (x ^ (ia g * ib h) * z ^ (ib g * ib h)) := by
        rw [← zpow_mul, ← zpow_mul]
      _ = x ^ (ia h + ia g * ib h) * z ^ (ib g * ib h) := by
        rw [← mul_assoc, ← zpow_add]
  have hax_mul : ∀ g h : G, ax (g * h) = ax h + ax g * az h := by
    intro g h
    obtain ⟨e1, -⟩ := kd291_aux_C_eq hcomm hx hz hzx _ _ _ _
      ((hcoef (g * h)).symm.trans (hcomp g h))
    push_cast at e1
    simp only [hax, haz]
    linear_combination e1
  have haz_mul : ∀ g h : G, az (g * h) = az g * az h := by
    intro g h
    obtain ⟨-, e2⟩ := kd291_aux_C_eq hcomm hx hz hzx _ _ _ _
      ((hcoef (g * h)).symm.trans (hcomp g h))
    push_cast at e2
    simp only [haz]
    linear_combination e2
  have hcoef1 : x ^ ia 1 * z ^ ib 1 = x ^ (0 : ℤ) * z ^ (1 : ℤ) :=
    (hcoef 1).symm.trans (by simp)
  obtain ⟨e1, e2⟩ := kd291_aux_C_eq hcomm hx hz hzx _ _ _ _ hcoef1
  have hax1 : ax 1 = 0 := by rw [hax, e1, Int.cast_zero]
  have haz1 : az 1 = 1 := by rw [haz, e2, Int.cast_one]
  let K : Subgroup G :=
    { carrier := {g | az g = 1}
      mul_mem' := fun {g h} hg hh => by
        show az (g * h) = 1
        rw [haz_mul, show az g = 1 from hg, show az h = 1 from hh, one_mul]
      one_mem' := haz1
      inv_mem' := fun {g} hg => by
        show az g⁻¹ = 1
        have h1 := haz_mul g⁻¹ g
        rw [inv_mul_cancel, haz1, show az g = 1 from hg, mul_one] at h1
        exact h1.symm }
  have haz_inv : ∀ g : G, az g⁻¹ * az g = 1 := by
    intro g
    rw [← haz_mul, inv_mul_cancel, haz1]
  have hcommK : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ K := by
    intro g h
    show az (g * h * g⁻¹ * h⁻¹) = 1
    rw [haz_mul, haz_mul, haz_mul]
    linear_combination (az h * az h⁻¹) * haz_inv g + haz_inv h
  have hKK : ∀ u ∈ K, ∀ v ∈ K, u * v * u⁻¹ * v⁻¹ ∈
      centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
    intro u hu v hv
    have hu' : az u = 1 := hu
    have hv' : az v = 1 := hv
    have hu'' : az u⁻¹ = 1 := K.inv_mem hu
    have hv'' : az v⁻¹ = 1 := K.inv_mem hv
    have hc1 : az (u * v * u⁻¹ * v⁻¹) = 1 := hcommK u v
    have hfu : ax u + ax u⁻¹ = 0 := by
      have h1 := hax_mul u⁻¹ u
      rw [inv_mul_cancel, hax1, hu', mul_one] at h1
      exact h1.symm
    have hfv : ax v + ax v⁻¹ = 0 := by
      have h1 := hax_mul v⁻¹ v
      rw [inv_mul_cancel, hax1, hv', mul_one] at h1
      exact h1.symm
    have hexc : ax (u * v * u⁻¹ * v⁻¹) = 0 := by
      have e1 := hax_mul u v
      have e2 := hax_mul (u * v) u⁻¹
      have e3 := hax_mul (u * v * u⁻¹) v⁻¹
      rw [e3, e2, e1, hu'', hv'', hv']
      linear_combination hfu + hfv
    have hxc1 : x ^ ia (u * v * u⁻¹ * v⁻¹) = 1 :=
      hxpow _ ((hax (u * v * u⁻¹ * v⁻¹)).symm.trans hexc)
    have hzc : z ^ ib (u * v * u⁻¹ * v⁻¹) = z :=
      hzpow _ ((haz (u * v * u⁻¹ * v⁻¹)).symm.trans hc1)
    have hcz : u * v * u⁻¹ * v⁻¹ * z * (u * v * u⁻¹ * v⁻¹)⁻¹ = z := by
      rw [hcoef, hxc1, hzc, one_mul]
    have hcz' : Commute (u * v * u⁻¹ * v⁻¹) z := mul_inv_eq_iff_eq_mul.mp hcz
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨i, j, rfl⟩ := kd291_aux_C_form hcomm b hb
    exact (((hcx (u * v * u⁻¹ * v⁻¹)).zpow_right i).mul_right
      (hcz'.zpow_right j)).eq.symm
  have hG1 : derivedSeries G 1 ≤ K :=
    Subgroup.commutator_le.mpr (fun g _ h _ => hcommK g h)
  show derivedSeries G (1 + 1) ≤ _
  rw [derivedSeries_succ]
  exact le_trans (Subgroup.commutator_mono hG1 hG1)
    (Subgroup.commutator_le.mpr (fun u hu v hv => hKK u hu v hv))

theorem kd291_solvable_of_pair (hp2 : p ≠ 2) {x z : G} (hxc : x ∈ Subgroup.center G)
    (hx : orderOf x = p) (hz : orderOf z = p) (hzx : z ∉ zpowers x)
    (hG : pRank p (⊤ : Subgroup G) ≤ 2)
    (hcon : centralizer ((CFSG.pCore p G : Subgroup G) : Set G) ≤ CFSG.pCore p G)
    (hzR : ∀ y ∈ CFSG.pCore p G, y * z = z * y) :
    IsSolvable G := by
  have hBn : ∀ g : G, g * z * g⁻¹ ∈ (zpowers x ⊔ zpowers z : Subgroup G) :=
    kd291_pair_normal hxc hx hz hzx hG hcon hzR
  have hBconj : ∀ g : G, (zpowers x ⊔ zpowers z : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      (zpowers x ⊔ zpowers z : Subgroup G) := by
    intro g
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · have hxg : (MulAut.conj g).toMonoidHom x = x := by
        show g * x * g⁻¹ = x
        rw [(Subgroup.mem_center_iff.1 hxc) g, mul_inv_cancel_right]
      rw [hxg]
      exact le_sup_left
    · exact zpowers_le.2 (hBn g)
  haveI hBN : (zpowers x ⊔ zpowers z : Subgroup G).Normal :=
    ⟨fun n hn g => hBconj g (Subgroup.mem_map_of_mem _ hn)⟩
  have hAp : IsPGroup p (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) :=
    kd291_isPGroup_centralizer_pair hp2 hxc hx hz hzx hG hcon hzR
  have hDS : derivedSeries G 2 ≤ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
    kd291_derivedSeries_two_le hxc hx hz hzx hBn
  haveI hAn : (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)).Normal :=
    inferInstance
  haveI hAnil : Group.IsNilpotent (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) :=
    IsPGroup.isNilpotent hAp
  haveI hQ : Group.IsSolvable (G ⧸ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) := by
    refine ⟨⟨2, ?_⟩⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective
      (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))) 2]
    refine eq_bot_iff.2 (le_trans (Subgroup.map_mono hDS) ?_)
    simp
  exact Group.isSolvable_of_subgroup_quotient
    (centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))

end E0

section E1
variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem kd291_aux_D_pRank_sub (K : Subgroup Y) : CFSG.pRank p K = CFSG.Open.pRank p K := by
  unfold CFSG.pRank CFSG.Open.pRank
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hcard⟩
    refine ⟨A.map K.subtype, Subgroup.map_subtype_le A, ?_, ?_⟩
    · haveI : IsElementaryAbelian p (A.map K.subtype) :=
        IsElementaryAbelian.map_subtype (K := K) (H := A)
      exact ⟨this.toIsMulCommutative,
        fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := p) x hx⟩
    · rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact hcard
  · rintro ⟨E, hEK, hE, hcard⟩
    haveI : IsElementaryAbelian p E :=
      { toIsMulCommutative := hE.1
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
    refine ⟨E.subgroupOf K, IsElementaryAbelian.subgroupOf hEK, ?_⟩
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

theorem kd291_pRank_top_le_sylow (Q : Sylow p Y) :
    pRank p (⊤ : Subgroup Y) ≤ pRank p (Q : Subgroup Y) := by
  rw [kd291_aux_D_pRank_sub, kd291_aux_D_pRank_sub]
  have hp : 1 < p := Nat.Prime.one_lt (Fact.out : p.Prime)
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup Y)
  have hEp : IsPGroup p E := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨1, Subtype.ext ?_⟩
    simpa using hE.2 g.1 g.2
  obtain ⟨Q0, hEQ0⟩ := hEp.exists_le_sylow
  haveI : Finite (Sylow p Y) :=
    Finite.of_injective (fun P : Sylow p Y => (P : Set Y)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q0 Q
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hEQ0 hx)
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) =
      p ^ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
    rw [Subgroup.card_map_of_injective hinj, hEc]
  exact CFSG.SectionRank.le_pRank hp hle (CFSG.SectionRank.isElemAbelian_map hE _) hcard

theorem kd291_aux_E_pRank_mono (hp : 1 < p) {H K : Subgroup Y} (h : H ≤ K) :
    CFSG.pRank p ↥H ≤ CFSG.pRank p ↥K := by
  unfold CFSG.pRank
  refine csSup_le' ?_
  intro r hr
  obtain ⟨A, hA, hc⟩ := hr
  have hbdd : BddAbove {t : ℕ | ∃ B : Subgroup ↥K,
      IsElementaryAbelian p ↥B ∧ Nat.card ↥B = p ^ t} := by
    refine ⟨Nat.card ↥K, ?_⟩
    rintro t ⟨B, -, hBc⟩
    have h1 : Nat.card ↥B ≤ Nat.card ↥K := Subgroup.card_le_card_group B
    have h2 : t < p ^ t := Nat.lt_pow_self hp
    rw [hBc] at h1
    exact h2.le.trans h1
  refine le_csSup hbdd ⟨A.map (Subgroup.inclusion h),
    IsElementaryAbelian.map (Subgroup.inclusion h), ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective h)]
  exact hc

theorem kd291_aux_E_main {x : Y} (hx : orderOf x = p)
    (hY : 3 ≤ pRank p (⊤ : Subgroup Y)) (C : Subgroup Y)
    (hCx : ∀ g : Y, g ∈ C ↔ g * x = x * g) (hC : pRank p C ≤ 2) :
    ∃ z : ↥C, (∀ y ∈ CFSG.pCore p ↥C, y * z = z * y) ∧ orderOf z = p ∧
      z ∉ zpowers (⟨x, (hCx x).2 rfl⟩ : ↥C) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hxC : x ∈ C := (hCx x).2 rfl
  obtain ⟨Qc⟩ : Nonempty (Sylow p ↥C) := inferInstance
  have hPm : IsPGroup p ((Qc : Subgroup ↥C).map C.subtype) := Qc.isPGroup'.map C.subtype
  obtain ⟨Q', hQ'le⟩ := IsPGroup.exists_le_sylow hPm
  have hxC_ord : orderOf (⟨x, hxC⟩ : ↥C) = p :=
    (Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥C)).symm.trans hx
  have hzpC_norm : (zpowers (⟨x, hxC⟩ : ↥C)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * (⟨x, hxC⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) * g :=
      Subtype.ext ((hCx g.1).1 g.2)
    rw [(Commute.zpow_right (show Commute g (⟨x, hxC⟩ : ↥C) from hc) k).eq, mul_assoc,
      mul_inv_cancel, mul_one]
    exact zpow_mem (Subgroup.mem_zpowers _) k
  have hzpC_ip : IsPGroup p (zpowers (⟨x, hxC⟩ : ↥C)) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hxC_ord, pow_one]⟩
  have hle : zpowers (⟨x, hxC⟩ : ↥C) ≤ CFSG.pCore p ↥C :=
    le_sSup ⟨hzpC_norm, hzpC_ip⟩
  have hxCQc : (⟨x, hxC⟩ : ↥C) ∈ (Qc : Subgroup ↥C) :=
    kd291_pCore_le_sylow Qc (hle (Subgroup.mem_zpowers _))
  have hxQ' : x ∈ (Q' : Subgroup Y) := hQ'le (Subgroup.mem_map_of_mem C.subtype hxCQc)
  have hnc : ∃ y ∈ (Q' : Subgroup Y), y * x ≠ x * y := by
    by_contra hcon
    have hall : ∀ y ∈ (Q' : Subgroup Y), y * x = x * y := fun y hy =>
      Classical.byContradiction fun hne => hcon ⟨y, hy, hne⟩
    have hQC : (Q' : Subgroup Y) ≤ C := by
      intro y hy
      exact (hCx y).2 (hall y hy)
    have h1 := kd291_aux_E_pRank_mono hp1 hQC
    have h2 := kd291_pRank_top_le_sylow Q'
    omega
  obtain ⟨y0, hy0Q, hy0⟩ := hnc
  have hcentral : ∃ z : Y, z ∈ (Q' : Subgroup Y) ∧
      (∀ g ∈ (Q' : Subgroup Y), g * z = z * g) ∧ orderOf z = p := by
    have hx1Q : (⟨x, hxQ'⟩ : ↥(Q' : Subgroup Y)) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    haveI : Nontrivial ↥(Q' : Subgroup Y) := nontrivial_of_ne _ _ hx1Q
    have hR : IsPGroup p ↥(Q' : Subgroup Y) := Q'.isPGroup'
    haveI : Nontrivial ↥(Subgroup.center ↥(Q' : Subgroup Y)) := hR.center_nontrivial
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
    have hZdvd : Nat.card ↥(Subgroup.center ↥(Q' : Subgroup Y)) ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hZdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 := Finite.one_lt_card (α := ↥(Subgroup.center ↥(Q' : Subgroup Y)))
      rw [hk, pow_zero] at h1
      omega
    have hpZ : p ∣ Nat.card ↥(Subgroup.center ↥(Q' : Subgroup Y)) := by
      rw [hk]
      exact dvd_pow_self p hk0
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpZ
    refine ⟨(w.1 : ↥(Q' : Subgroup Y)).1, (w.1 : ↥(Q' : Subgroup Y)).2, ?_, ?_⟩
    · intro g hg
      have h1 := Subgroup.mem_center_iff.1 w.2 ⟨g, hg⟩
      exact congrArg Subtype.val h1
    · exact ((Subgroup.orderOf_coe (w.1 : ↥(Q' : Subgroup Y))).trans
        (Subgroup.orderOf_coe w)).trans hw
  obtain ⟨z, -, hzc, hzord⟩ := hcentral
  have hzx : z ∉ zpowers x := by
    intro h
    have hle' : zpowers z ≤ zpowers x := Subgroup.zpowers_le.2 h
    have hcard : Nat.card (zpowers x) ≤ Nat.card (zpowers z) := by
      simp only [Nat.card_zpowers, hx, hzord, le_refl]
    have heq : zpowers z = zpowers x := Subgroup.eq_of_le_of_card_ge hle' hcard
    have hxz : x ∈ zpowers z := by
      rw [heq]
      exact Subgroup.mem_zpowers x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hall : ∀ g ∈ (Q' : Subgroup Y), g * x = x * g := by
      intro g hg
      rw [← hm]
      exact (Commute.zpow_right (show Commute g z from hzc g hg) m).eq
    exact hy0 (hall y0 hy0Q)
  have hzC : z ∈ C := (hCx z).2 (hzc x hxQ').symm
  refine ⟨⟨z, hzC⟩, ?_, ?_, ?_⟩
  · intro y hy
    apply Subtype.ext
    have hyQc : y ∈ (Qc : Subgroup ↥C) := kd291_pCore_le_sylow Qc hy
    have hyQ' : (y : Y) ∈ (Q' : Subgroup Y) := hQ'le (Subgroup.mem_map_of_mem C.subtype hyQc)
    exact hzc (y : Y) hyQ'
  · exact ((Subgroup.orderOf_coe (⟨z, hzC⟩ : ↥C)).symm).trans hzord
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hzx
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have hk' : (((⟨x, hxC⟩ : ↥C) ^ k : ↥C) : Y) = z := congrArg Subtype.val hk
    simpa using hk'

theorem kd291_exists_central_pair {x : Y} (hx : orderOf x = p)
    (hY : 3 ≤ pRank p (⊤ : Subgroup Y)) (hC : pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    ∃ z : ↥(centralizer ({x} : Set Y)),
      (∀ y ∈ CFSG.pCore p ↥(centralizer ({x} : Set Y)), y * z = z * y) ∧ orderOf z = p ∧
      z ∉ zpowers (⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
        ↥(centralizer ({x} : Set Y))) :=
  kd291_aux_E_main hx hY (centralizer ({x} : Set Y))
    (fun g => Subgroup.mem_centralizer_singleton_iff) hC

theorem kd291_aux_F_pRank_coe {Z : Type*} [Group Z] [Finite Z] (H : Subgroup Z) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top p H).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm

theorem kd291_aux_F_group_form (C : Subgroup Y)
    (hcon : C ⊓ centralizer (pCoreOf p C : Set Y) ≤ pCoreOf p C) :
    centralizer ((CFSG.pCore p ↥C : Subgroup ↥C) : Set ↥C) ≤ CFSG.pCore p ↥C := by
  intro c hc
  have hcY : (c : Y) ∈ C ⊓ centralizer (pCoreOf p C : Set Y) := by
    refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ (CFSG.pCore p ↥C).map C.subtype := hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh'
    have hrc : r * c = c * r := Subgroup.mem_centralizer_iff.1 hc r hr
    have h1 := congrArg Subtype.val hrc
    simpa using h1
  have hmem : (c : Y) ∈ (CFSG.pCore p ↥C).map C.subtype := hcon hcY
  obtain ⟨r, hr, hrc⟩ := Subgroup.mem_map.1 hmem
  have hrc' : r = c := Subtype.ext hrc
  rw [← hrc']
  exact hr

theorem kd291_solvable_centralizer (hp2 : p ≠ 2) {x : Y} (hx : orderOf x = p)
    (hY : 3 ≤ pRank p (⊤ : Subgroup Y)) (hC : pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hcon : centralizer ({x} : Set Y) ⊓ centralizer (pCoreOf p (centralizer ({x} : Set Y)) : Set Y) ≤
      pCoreOf p (centralizer ({x} : Set Y))) :
    IsSolvable ↥(centralizer ({x} : Set Y)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hxC : x ∈ centralizer ({x} : Set Y) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨z, hzR, hz, hzx⟩ := kd291_exists_central_pair hx hY hC
  refine kd291_solvable_of_pair hp2 (x := (⟨x, hxC⟩ : ↥(centralizer ({x} : Set Y))))
    (z := z) ?_ ?_ hz hzx ?_ ?_ hzR
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : Y) * x = x * (g : Y) := Subgroup.mem_centralizer_singleton_iff.1 g.2
    simpa using hg
  · exact (Subgroup.orderOf_mk x hxC).trans hx
  · have hCo : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2 := by
      rw [← kd291_aux_F_pRank_coe]
      exact hC
    rw [kd291_aux_F_pRank_coe]
    refine le_trans (CFSG.SectionRank.pRank_le_map hp (centralizer ({x} : Set Y)).subtype
      (Subgroup.subtype_injective (centralizer ({x} : Set Y)))
      (⊤ : Subgroup ↥(centralizer ({x} : Set Y)))) ?_
    have e : (⊤ : Subgroup ↥(centralizer ({x} : Set Y))).map (centralizer ({x} : Set Y)).subtype
        = centralizer ({x} : Set Y) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [e]
    exact hCo
  · exact kd291_aux_F_group_form (centralizer ({x} : Set Y)) hcon

theorem kd291_solvable_centralizer_open (hp2 : p ≠ 2) {x : Y} (hx : orderOf x = p)
    (hY : 3 ≤ Open.pRank p (⊤ : Subgroup Y))
    (hC : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hcon : centralizer ({x} : Set Y) ⊓ centralizer (pCoreOf p (centralizer ({x} : Set Y)) : Set Y) ≤
      pCoreOf p (centralizer ({x} : Set Y))) :
    IsSolvable ↥(centralizer ({x} : Set Y)) := by
  refine kd291_solvable_centralizer hp2 hx ?_ ?_ hcon
  · rw [kd291_aux_D_pRank_sub]
    exact hY
  · rw [kd291_aux_D_pRank_sub]
    exact hC

end E1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
