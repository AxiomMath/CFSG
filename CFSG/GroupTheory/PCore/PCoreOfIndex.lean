module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {G : Type*} [Group G]

variable {p : ℕ}

private theorem pCoreOf_isPGroup' [Finite G] [Fact p.Prime] (H : Subgroup G) :
    IsPGroup p (pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

private theorem pCoreOf_le' (H : Subgroup G) : pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

private theorem le_pCoreOf_of_normal' {N H : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hsub : IsPGroup p (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ CFSG.pCore p ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf H) (le_iSup_of_le hN (le_iSup_of_le hsub le_rfl))
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

private theorem le_pCoreOf_of_le_normalizer' {N H : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) (hp : IsPGroup p N) :
    N ≤ pCoreOf p H :=
  le_pCoreOf_of_normal' hNH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnorm) hp

private theorem le_normalizer_pCoreOf' (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set G) := by
  have hforward : ∀ g ∈ H, ∀ x ∈ pCoreOf p H, g * x * g⁻¹ ∈ pCoreOf p H := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
      (inferInstance : (CFSG.pCore p ↥H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hforward g hg x, fun hx => by
    have h := hforward g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x from by group] at h⟩

private theorem normalizer_le_normalizer_pCoreOf' (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (pCoreOf p H : Set G) := by
  have hforward : ∀ g ∈ Subgroup.normalizer (H : Set G),
      ∀ x ∈ pCoreOf p H, g * x * g⁻¹ ∈ pCoreOf p H := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let φ : ↥H ≃* ↥H := H.normalizerMonoidHom ⟨g, hg⟩
    have hfix : (CFSG.pCore p ↥H).map φ.toMonoidHom = CFSG.pCore p ↥H :=
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : (CFSG.pCore p ↥H).Characteristic) φ
    refine Subgroup.mem_map.mpr ⟨φ y, ?_, ?_⟩
    · rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    · exact H.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hforward g hg x, fun hx => by
    have h := hforward g⁻¹ ((Subgroup.normalizer (H : Set G)).inv_mem hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x from by group] at h⟩

theorem pCoreOf_le_of_not_dvd_relIndex [Finite G] [Fact p.Prime] {L K : Subgroup G}
    (hLK : L ≤ K) (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hp : ¬ p ∣ L.relIndex K) : pCoreOf p K ≤ L := by
  haveI hN : (L.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
  have hcard : Nat.card (↥K ⧸ (L.subgroupOf K)) = L.relIndex K := rfl
  intro x hx
  have hxK : x ∈ K := pCoreOf_le' (p := p) K hx
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp (pCoreOf_isPGroup' (p := p) K)) ⟨x, hx⟩
  have hkx : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxK' : (⟨x, hxK⟩ : ↥K) ^ p ^ k = 1 := by
    apply Subtype.ext
    simpa using hkx
  let q : ↥K ⧸ (L.subgroupOf K) := QuotientGroup.mk ⟨x, hxK⟩
  have hq1 : orderOf q ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have hmap := map_pow (QuotientGroup.mk' (L.subgroupOf K)) ⟨x, hxK⟩ (p ^ k)
    rw [hxK', map_one] at hmap
    exact hmap.symm
  have hq2 : orderOf q ∣ L.relIndex K := by
    rw [← hcard]
    exact orderOf_dvd_natCard q
  have hcop : Nat.Coprime p (L.relIndex K) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
  have hone : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.of_dvd_left hq1 (hcop.pow_left k)) dvd_rfl hq2
  have hxL : (⟨x, hxK⟩ : ↥K) ∈ L.subgroupOf K :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)
  exact hxL

theorem pCoreOf_eq_of_not_dvd_relIndex [Finite G] [Fact p.Prime] {L K : Subgroup G}
    (hLK : L ≤ K) (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hp : ¬ p ∣ L.relIndex K) : pCoreOf p K = pCoreOf p L := by
  refine le_antisymm ?_ ?_
  · refine le_pCoreOf_of_le_normalizer' (pCoreOf_le_of_not_dvd_relIndex hLK hKL hp) ?_
      (pCoreOf_isPGroup' (p := p) K)
    exact hLK.trans (le_normalizer_pCoreOf' (p := p) K)
  · refine le_pCoreOf_of_le_normalizer' ((pCoreOf_le' (p := p) L).trans hLK) ?_
      (pCoreOf_isPGroup' (p := p) L)
    exact hKL.trans (normalizer_le_normalizer_pCoreOf' (p := p) L)

private lemma mem_pCoreOf_mul_conj_mem [Finite G] {P Q : Subgroup G}
    (hO : Q.relIndex (pCoreOf 2 P) ≤ 2) {c : G} (hcP : c ∈ P)
    (hcC : c ∈ Subgroup.centralizer (Q : Set G)) :
    ∀ o ∈ pCoreOf 2 P, o⁻¹ * (c * o * c⁻¹) ∈ Q := by
  have hPO : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) := le_normalizer_pCoreOf' (p := 2) P
  intro o ho
  have hcoO : c * o * c⁻¹ ∈ pCoreOf 2 P :=
    (Subgroup.mem_normalizer_iff.mp (hPO hcP) o).mp ho
  let O : Subgroup G := pCoreOf 2 P
  let o' : ↥O := ⟨o, ho⟩
  let co' : ↥O := ⟨c * o * c⁻¹, hcoO⟩
  let QO : Subgroup ↥O := Q.subgroupOf O
  have hQOindex : QO.index ≤ 2 := hO
  have hpos : QO.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiff : o' ∈ QO ↔ co' ∈ QO := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hoQ
      change c * o * c⁻¹ ∈ Q
      have hcomm : o * c = c * o := Subgroup.mem_centralizer_iff.mp hcC o hoQ
      have hco : c * o * c⁻¹ = o := by
        calc c * o * c⁻¹ = o * c * c⁻¹ := by rw [← hcomm]
          _ = o := by rw [mul_assoc, mul_inv_cancel, mul_one]
      simpa [hco] using hoQ
    · intro hcoQ
      change o ∈ Q
      have hcomm : (c * o * c⁻¹) * c = c * (c * o * c⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hcC (c * o * c⁻¹) hcoQ
      have hco' : c⁻¹ * (c * o * c⁻¹) * c = c * o * c⁻¹ := by
        calc c⁻¹ * (c * o * c⁻¹) * c = c⁻¹ * ((c * o * c⁻¹) * c) := by group
          _ = c⁻¹ * (c * (c * o * c⁻¹)) := by rw [hcomm]
          _ = c * o * c⁻¹ := by group
      have ho' : o = c⁻¹ * (c * o * c⁻¹) * c := by group
      rw [ho', hco']
      exact hcoQ
  have hq' : o'⁻¹ * co' ∈ QO := by
    rcases (by omega : QO.index = 1 ∨ QO.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · refine (Subgroup.mul_mem_iff_of_index_two (H := QO) h2 (a := o'⁻¹) (b := co')).mpr ?_
      constructor
      · intro hx
        exact hiff.mp (QO.inv_mem_iff.mp hx)
      · intro hx
        exact QO.inv_mem_iff.mpr (hiff.mpr hx)
  simpa [QO, o', co', Subgroup.mem_subgroupOf] using hq'

private lemma centralizes_pCoreOf_of_odd [Finite G] {P Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hO : Q.relIndex (pCoreOf 2 P) ≤ 2) {c : G} (hcP : c ∈ P)
    (hcC : c ∈ Subgroup.centralizer (Q : Set G)) (hodd : Odd (orderOf c)) :
    c ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := by
  classical
  have hmem := mem_pCoreOf_mul_conj_mem hO hcP hcC
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  set q : G := o⁻¹ * (c * o * c⁻¹) with hqdef
  have hqQ : q ∈ Q := hmem o ho
  have hcq : q * c = c * q := Subgroup.mem_centralizer_iff.mp hcC q hqQ
  have hcomm : Commute c q := hcq.symm
  have hiter : ∀ k : ℕ, c ^ k * o * (c ^ k)⁻¹ = o * q ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcqk : c * q ^ k * c⁻¹ = q ^ k := by
        rw [(hcomm.pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      have hco : c * o * c⁻¹ = o * q := by
        rw [hqdef]
        group
      calc c ^ (k + 1) * o * (c ^ (k + 1))⁻¹
          = c * (c ^ k * o * (c ^ k)⁻¹) * c⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            group
        _ = c * (o * q ^ k) * c⁻¹ := by rw [ih]
        _ = (c * o * c⁻¹) * (c * q ^ k * c⁻¹) := by group
        _ = (o * q) * q ^ k := by rw [hco, hcqk]
        _ = o * q ^ (k + 1) := by rw [pow_succ']; group
  have hm := hiter (orderOf c)
  have hqm : q ^ orderOf c = 1 := by
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
    exact (mul_left_cancel (a := o) (by rw [mul_one, hm.symm])).symm
  have hq1 : q = 1 := by
    have hcop : Nat.Coprime 2 (orderOf c) := Nat.coprime_two_left.mpr hodd
    have hord : (orderOf (⟨q, hqQ⟩ : ↥Q)).Coprime (orderOf c) :=
      hQ.orderOf_coprime hcop ⟨q, hqQ⟩
    rw [Subgroup.orderOf_mk] at hord
    exact orderOf_eq_one_iff.mp (hord.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hqm))
  have hco : c * o * c⁻¹ = o := by
    have h : o⁻¹ * (c * o * c⁻¹) = 1 := by
      rw [← hqdef]
      exact hq1
    calc c * o * c⁻¹ = o * (o⁻¹ * (c * o * c⁻¹)) := by group
      _ = o * 1 := by rw [h]
      _ = o := by rw [mul_one]
  calc o * c = (c * o * c⁻¹) * c := by rw [hco]
    _ = c * o := by group

theorem isPGroup_inf_centralizer_of_relIndex_le_two [Finite G] {P Q : Subgroup G}
    (hQ : IsPGroup 2 Q)
    (hchar : P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P)
    (hO : Q.relIndex (pCoreOf 2 P) ≤ 2) :
    IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (Q : Set G)) := by
  classical
  let C : Subgroup G := P ⊓ Subgroup.centralizer (Q : Set G)
  have hodd_eq_one : ∀ c : ↥C, Odd (orderOf c) → c = 1 := by
    intro c hodd
    have hcP : (c : G) ∈ P := c.2.1
    have hcC : (c : G) ∈ Subgroup.centralizer (Q : Set G) := c.2.2
    have horderc : orderOf c = orderOf (c : G) := Subgroup.orderOf_mk (c : G) c.2
    have hoddG : Odd (orderOf (c : G)) := horderc ▸ hodd
    have hcent : (c : G) ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) :=
      centralizes_pCoreOf_of_odd hQ hO hcP hcC hoddG
    have hcO : (c : G) ∈ pCoreOf 2 P := hchar ⟨hcP, hcent⟩
    have hcop : Nat.Coprime 2 (orderOf (c : G)) := Nat.coprime_two_left.mpr hoddG
    have h1 : orderOf (c : G) = 1 := by
      have h := (pCoreOf_isPGroup' (p := 2) P).orderOf_coprime hcop ⟨(c : G), hcO⟩
      rw [Subgroup.orderOf_mk] at h
      exact h.eq_one_of_dvd dvd_rfl
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro c
  obtain ⟨a, m, hm, hkam⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hdvd : 2 ^ a ∣ orderOf c := ⟨m, hkam⟩
  have hord : orderOf (c ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hkam,
      Nat.mul_div_cancel_left m (pow_pos two_pos a)]
  have hpow1 : c ^ 2 ^ a = 1 := hodd_eq_one (c ^ 2 ^ a) (by rw [hord]; exact hm)
  exact ⟨a, hpow1⟩

private theorem commute_of_card_inf_two [Finite G] {N K : Subgroup G} (hK : K.Normal)
    {c : ↥(N ⊓ K)} (hcne : c ≠ 1) (hk2 : Nat.card ↥(N ⊓ K) = 2) :
    ∀ n ∈ N, n * (c : G) = (c : G) * n := by
  intro n hn
  have hcN : (c : G) ∈ N := (Subgroup.mem_inf.mp c.2).1
  have hcK : (c : G) ∈ K := (Subgroup.mem_inf.mp c.2).2
  have hd_mem : n * (c : G) * n⁻¹ ∈ N ⊓ K :=
    ⟨N.mul_mem (N.mul_mem hn hcN) (N.inv_mem hn), hK.conj_mem (c : G) hcK n⟩
  let d : ↥(N ⊓ K) := ⟨n * (c : G) * n⁻¹, hd_mem⟩
  have hdne : d ≠ 1 := by
    intro hd
    apply hcne
    apply Subtype.ext
    have hd' : n * (c : G) * n⁻¹ = 1 := by
      have := congrArg Subtype.val hd
      simpa [d] using this
    calc (c : G) = n⁻¹ * (n * (c : G) * n⁻¹) * n := by group
      _ = 1 := by rw [hd']; simp
  have huniq : ∃! y : ↥(N ⊓ K), y ≠ 1 :=
    (Nat.card_eq_two_iff' (1 : ↥(N ⊓ K))).mp hk2
  have hdc : d = c := huniq.unique hdne hcne
  have hval : n * (c : G) * n⁻¹ = (c : G) := by
    have := congrArg Subtype.val hdc
    simpa [d] using this
  calc n * (c : G) = (n * (c : G) * n⁻¹) * n := by group
    _ = (c : G) * n := by rw [hval]

theorem card_inf_ne_two_of_le_centralizer [Finite G] {Q K N : Subgroup G}
    (hK : K.Normal) (hKQ : K ≤ Subgroup.centralizer (Q : Set G))
    (hNQ : N ⊓ Q = ⊥) (hcard : Nat.card Q * Nat.card N = Nat.card G)
    (hZ : ∀ c ∈ Subgroup.center G, c ^ 2 = 1 → c ∈ Q) :
    Nat.card ↥(N ⊓ K) ≠ 2 := by
  classical
  intro hk2
  have hdisj : Disjoint Q N := by
    rw [disjoint_iff, inf_comm]
    exact hNQ
  have hsup : Q ⊔ N = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj).sup_eq_top
  have hne : N ⊓ K ≠ ⊥ := by
    intro h
    rw [h] at hk2
    simp at hk2
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcN : (c : G) ∈ N := (Subgroup.mem_inf.mp c.2).1
  have hcK : (c : G) ∈ K := (Subgroup.mem_inf.mp c.2).2
  have hc2' : (c : G) ^ 2 = 1 := by
    have hdvd : orderOf c ∣ 2 := by
      rw [← hk2]
      exact orderOf_dvd_natCard c
    have hc2 : c ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val hc2
  have hc_central_N := commute_of_card_inf_two hK hcne hk2
  have hcentral : (c : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : Q ⊔ N ≤ Subgroup.centralizer ({(c : G)} : Set G) := by
      refine sup_le ?_ ?_
      · intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp (hKQ hcK) q hq).symm
      · intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hc_central_N n hn).symm
    have hg := hle (by rw [hsup]; exact Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg (c : G) (Set.mem_singleton _)).symm
  have hcQ : (c : G) ∈ Q := hZ (c : G) hcentral hc2'
  have hbot : (c : G) ∈ N ⊓ Q := ⟨hcN, hcQ⟩
  rw [hNQ] at hbot
  exact hcne (Subtype.ext (by simpa using hbot))

end CFSG.GroupTheory
