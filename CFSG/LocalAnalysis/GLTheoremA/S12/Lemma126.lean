module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma125
public import CFSG.GH74.Uniqueness.Section15HeringCyclic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem coprime_comm_self (hp : p.Prime) (hp2 : p ≠ 2) {R B' : Subgroup G} (hR : IsPGroup 2 R) (hB : IsPGroup p B')
    (hBR : B' ≤ Subgroup.normalizer (R : Set G)) (hne : (⁅R, B'⁆ : Subgroup G) ≠ ⊥) :
    (⁅(⁅R, B'⁆ : Subgroup G), B'⁆ : Subgroup G) ≠ ⊥ := by
  rw [commutator_commutator_eq_of_isPGroup hp hB hR hp2 hBR]
  exact hne

theorem normal_pcomplement_cyclic (hp : p.Prime) {Y : Subgroup G} {y : G} (hyY : y ∈ Y) (hyp : orderOf y = p)
    (hyc : ∀ g ∈ Y, g * y = y * g) (hcyc : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S) :
    ∀ g ∈ Y, ∃ n : ℕ, g ^ (p ^ n) ∈ GLAPPrimeCoreOf p Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  set y' : ↥Y := ⟨y, hyY⟩ with hy'
  have hy'ord : orderOf y' = p := by rw [hy', Subgroup.orderOf_mk]; exact hyp
  have hy'c : ∀ g : ↥Y, g * y' = y' * g := fun g => Subtype.ext (hyc g g.2)
  have hZp : IsPGroup p (Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'ord, pow_one])
  obtain ⟨Q, hQ⟩ := hZp.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥Y) := by
    have h1 : IsCyclic ↥((Q : Subgroup ↥Y).map Y.subtype) :=
      hcyc _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥Y) Y.subtype Y.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨r, hr⟩ := hQcyc.exists_generator
  have hQr : (Q : Subgroup ↥Y) = Subgroup.zpowers (r : ↥Y) := by
    refine le_antisymm (fun z hz => ?_) (Subgroup.zpowers_le.2 r.2)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
  have hy'Q : y' ∈ (Q : Subgroup ↥Y) := hQ (Subgroup.mem_zpowers y')
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf).1 Q.isPGroup' r
  have hm' : orderOf (r : ↥Y) = p ^ m := by rw [Subgroup.orderOf_coe]; exact hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm'
    rw [hQr, hm', Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hy'Q
    rw [hy'Q, orderOf_one] at hy'ord
    exact hp.one_lt.ne hy'ord
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hpb : p ^ b ∣ orderOf (r : ↥Y) := by rw [hm', pow_succ]; exact dvd_mul_right _ _
  have hcard : Nat.card (Subgroup.zpowers ((r : ↥Y) ^ p ^ b)) = p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero b hp.ne_zero) hpb, hm', pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos b)]
  have hy'mem : y' ∈ Subgroup.zpowers ((r : ↥Y) ^ p ^ b) := by
    rw [hQr] at hy'Q
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hy'Q
    have h1 : (r : ↥Y) ^ (i * (p : ℤ)) = 1 := by
      rw [zpow_mul, hi, zpow_natCast]
      have := pow_orderOf_eq_one y'
      rwa [hy'ord] at this
    have h2 : ((p ^ (b + 1) : ℕ) : ℤ) ∣ i * (p : ℤ) := by
      rw [← hm']
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have h3 : ((p ^ b : ℕ) : ℤ) ∣ i := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have : ((p ^ b : ℕ) : ℤ) * (p : ℤ) ∣ i * (p : ℤ) := by
        rw [← Nat.cast_mul, ← pow_succ]
        exact h2
      exact (mul_dvd_mul_iff_right hpz).1 this
    obtain ⟨j, hj⟩ := h3
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← hi, hj, zpow_mul, zpow_natCast]
  have hzeq : Subgroup.zpowers y' = Subgroup.zpowers ((r : ↥Y) ^ p ^ b) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy'mem)
      (by rw [hcard, Nat.card_zpowers, hy'ord])
  have hNC : Subgroup.normalizer ((Subgroup.zpowers ((r : ↥Y) ^ p ^ b) : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.centralizer ((Subgroup.zpowers ((r : ↥Y) ^ p ^ b) : Subgroup ↥Y) : Set ↥Y) := by
    intro g _
    rw [← hzeq, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute y' g from (hy'c g).symm) k).eq
  obtain ⟨N, hNn, hNcop, hNidx⟩ := CFSG.GH74.Uniqueness.Hering.exists_normal_pComplement_of_cyclic Q hQr hm' hNC
  have hle : N ≤ GLAPPrimeCore p ↥Y :=
    le_sSup ⟨hNn, (Nat.Prime.coprime_iff_not_dvd hp).2 hNcop⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 Q.isPGroup'
  intro g hg
  refine ⟨n, ?_⟩
  have h1 := Subgroup.pow_index_mem N (⟨g, hg⟩ : ↥Y)
  rw [hNidx, hn] at h1
  exact ⟨_, hle h1, rfl⟩

theorem centMod_cx_odd (h : Cfg12 G m p B x L D K)
    (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))))) :
    Odd (Nat.card ↥(centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G))) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hxcm : x ∈ centModSubgroup p L := by
    have : x ∈ B ⊓ centModSubgroup p L := by
      rw [B_inf_centMod_eq h]
      exact Subgroup.mem_zpowers x
    exact this.2
  have hxY : x ∈ centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.2 ⟨hxcm, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hord : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
  have hyc : ∀ g ∈ centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G), g * x = x * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
  have hcyc : ∀ S : Subgroup G, S ≤ centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) →
      IsPGroup p S → IsCyclic S := fun S hS hS' =>
    h.tri.cycMod S (fun g hg => centMod_iff.2 (Subgroup.mem_inf.1 (hS hg)).1) hS'
  have hcompl := normal_pcomplement_cyclic hp hxY hord hyc hcyc
  have hCY : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_inf'
      (L62.normalizer_le_normalizer_centModSubgroup p L (cx_le_normalizer_L h hc)) (Subgroup.le_normalizer hc)
  have hsub : IsSubnormal (centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G)) (Subgroup.centralizer ({x} : Set G)) :=
    IsSubnormal.step inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hCY) (IsSubnormal.refl _)
  have hO := glaPPrimeCoreOf_le_of_isSubnormal hp hsub
  by_contra hev
  have h2 : 2 ∣ Nat.card ↥(centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G)) := by
    by_contra hnd
    exact hev (Nat.odd_iff.2 (by omega))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G))) 2 h2
  have hgY : (g : G) ∈ centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) := g.2
  have hg2 : orderOf (g : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  obtain ⟨n, hn⟩ := hcompl (g : G) hgY
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two h.odd).pow (n := n)
  have hsq : (g : G) ^ 2 = 1 := by
    rw [← hg2]
    exact pow_orderOf_eq_one _
  have hgg : (g : G) ^ (p ^ n) = g := by
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [hgg] at hn
  have hmem := hO hn
  have hdvd : orderOf (g : G) ∣ Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) := by
    have := orderOf_dvd_natCard (⟨(g : G), hmem⟩ : ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))))
    rwa [Subgroup.orderOf_mk] at this
  rw [hg2] at hdvd
  have := Nat.odd_iff.1 hodd
  omega

abbrev Hlift (p : ℕ) (x : G) (L R₀ : Subgroup G) : Subgroup G :=
  L ⊓ (R₀ ⊔ (centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G)))

theorem Z_central_of_qs (h : Cfg12 G m p B x L D K) : L ⊓ centModSubgroup p L ≤ Subgroup.centralizer (L : Set G) := by
  have hp := h.prime
  have hOL : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) = ⊥ :=
    S9.commutator_eq_bot_of_isQuasisimple hp h.tri.comp (h.tri.qs h.ctx)
  have h1 : (⁅L, L ⊓ centModSubgroup p L⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L := by
    rw [Subgroup.commutator_le]
    intro l hl z hz
    exact (mem_centModSubgroup.1 (Subgroup.mem_inf.1 hz).2).2 l hl
  have h2 : (⁅(⁅L, L ⊓ centModSubgroup p L⁆ : Subgroup G), L⁆ : Subgroup G) = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono h1 le_rfl).trans ?_)
    rw [Subgroup.commutator_comm]
    exact hOL.le
  have h3 := CFSG.LocalCores.perfect_double_commutator
    (Subgroup.isPerfect_iff.2 (glaPComponent_perfect h.tri.comp)) h2
  rw [Subgroup.commutator_comm] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3

theorem pow_mul_mem_of_normalizes {C : Subgroup G} {r : G} (hr : r ∈ Subgroup.normalizer (C : Set G)) {c : G}
    (hc : c ∈ C) (n : ℕ) : ∃ c' ∈ C, (r * c) ^ n = r ^ n * c' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', hn⟩ := ih
    refine ⟨(r⁻¹ * c' * r) * c, mul_mem ?_ hc, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hr) c').1 hc'
      simpa using this
    · rw [pow_succ, hn]
      group

theorem H_two_power (h : Cfg12 G m p B x L D K) {R₀ : Subgroup G} (hR₀2 : IsPGroup 2 R₀)
    (hR₀x : R₀ ≤ Subgroup.centralizer ({x} : Set G)) :
    ∀ g ∈ Hlift p x L R₀, ∃ n : ℕ, g ^ (2 ^ n) ∈ L ⊓ centModSubgroup p L := by
  intro g hg
  have hR₀C : R₀ ≤ Subgroup.normalizer ((centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    fun r hr => mem_normalizer_inf'
      (L62.normalizer_le_normalizer_centModSubgroup p L (cx_le_normalizer_L h (hR₀x hr)))
      (Subgroup.le_normalizer (hR₀x hr))
  have hg' : g ∈ (R₀ ⊔ (centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G)) : Subgroup G) := hg.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hR₀C] at hg'
  obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.mp hg'
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR₀2
  have hr1 : r ^ (2 ^ n) = 1 := by
    have := pow_card_eq_one' (G := ↥R₀) (x := ⟨r, hr⟩)
    rw [hn] at this
    simpa using congrArg Subtype.val this
  obtain ⟨c', hc', hcc⟩ := pow_mul_mem_of_normalizes (hR₀C hr) hc (2 ^ n)
  refine ⟨n, Subgroup.mem_inf.2 ⟨pow_mem hg.1 _, ?_⟩⟩
  rw [hcc, hr1, one_mul]
  exact (Subgroup.mem_inf.1 hc').1

theorem B_norm_Hlift (h : Cfg12 G m p B x L D K) {R₀ : Subgroup G} (hBR₀ : B ≤ Subgroup.normalizer (R₀ : Set G)) :
    B ≤ Subgroup.normalizer ((Hlift p x L R₀ : Subgroup G) : Set G) := fun b hb =>
  mem_normalizer_inf' (h.tri.norm hb)
    (mem_normalizer_sup' (hBR₀ hb)
      (mem_normalizer_inf' (L62.normalizer_le_normalizer_centModSubgroup p L (h.tri.norm hb))
        (Subgroup.le_normalizer (B_le_cx h hb))))

theorem exists_char_sylow_two {H Z : Subgroup G} (hZH : Z ≤ H) (hZc : ∀ z ∈ Z, ∀ g ∈ H, z * g = g * z)
    (hq : ∀ g ∈ H, ∃ n : ℕ, g ^ (2 ^ n) ∈ Z) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup 2 S ∧ H ≤ S ⊔ Z ∧
      ∀ g ∈ Subgroup.normalizer (H : Set G), g ∈ Subgroup.normalizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ'c : Z.subgroupOf H ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc _ (Subgroup.mem_subgroupOf.1 hz) _ g.2).symm
  haveI hZ'n : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZ'c
  have hqq : IsPGroup 2 (↥H ⧸ Z.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H q =>
      obtain ⟨n, hn⟩ := hq q.1 q.2
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hn
  haveI hnilq : Group.IsNilpotent (↥H ⧸ Z.subgroupOf H) := hqq.isNilpotent
  haveI hnil : Group.IsNilpotent ↥H := isNilpotent_of_ker_le_center (QuotientGroup.mk' (Z.subgroupOf H))
    (by rw [QuotientGroup.ker_mk']; exact hZ'c)
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  haveI : Unique (Sylow 2 ↥H) := Sylow.unique_of_normal P inferInstance
  set S : Subgroup G := (P : Subgroup ↥H).map H.subtype with hS
  have hSH : S ≤ H := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := P.isPGroup'.map H.subtype
  refine ⟨S, hSH, hS2, ?_, ?_⟩
  · have h1 : ((P : Subgroup ↥H) ⊔ Z.subgroupOf H) = ⊤ := by
      have hd1 : ((P : Subgroup ↥H) ⊔ Z.subgroupOf H).index ∣ (P : Subgroup ↥H).index :=
        Subgroup.index_dvd_of_le le_sup_left
      have hd2 : ((P : Subgroup ↥H) ⊔ Z.subgroupOf H).index ∣ (Z.subgroupOf H).index :=
        Subgroup.index_dvd_of_le le_sup_right
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hqq
      have hZ'idx : (Z.subgroupOf H).index = 2 ^ k := by rw [Subgroup.index, hk]
      have hPi : ¬ 2 ∣ (P : Subgroup ↥H).index := P.not_dvd_index
      have hcop : Nat.Coprime (2 ^ k) (P : Subgroup ↥H).index :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hPi)
      rw [hZ'idx] at hd2
      exact Subgroup.index_eq_one.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd2) hd1)
    have h2 : ((P : Subgroup ↥H) ⊔ Z.subgroupOf H).map H.subtype = S ⊔ Z := by
      rw [Subgroup.map_sup, ← hS, Subgroup.subgroupOf_map_subtype, inf_of_le_left hZH]
    have h3 : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1, h3] at h2
    exact h2.le
  · have key : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
      intro g hg s hs
      have hgsH : g * s * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg s).1 (hSH hs)
      obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
      have hsk : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      set t : ↥H := ⟨g * s * g⁻¹, hgsH⟩ with ht_def
      have ht : t ^ (2 ^ k) = 1 := Subtype.ext (by simp [ht_def, conj_pow, hsk])
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ht)
      have hQ : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
      have hPP : P' = P := Subsingleton.elim P' P
      have htP : t ∈ (P : Subgroup ↥H) := hPP ▸ hP' (Subgroup.mem_zpowers t)
      exact ⟨t, htP, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key g hg w hw, fun hw => ?_⟩
    have h1 := key g⁻¹ (inv_mem hg) _ hw
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rwa [e] at h1

theorem exists_two_part (h : Cfg12 G m p B x L D K) {R₀ : Subgroup G} (hR₀2 : IsPGroup 2 R₀)
    (hR₀x : R₀ ≤ Subgroup.centralizer ({x} : Set G)) (hBR₀ : B ≤ Subgroup.normalizer (R₀ : Set G)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      Hlift p x L R₀ ≤ S ⊔ (L ⊓ centModSubgroup p L) := by
  have hZH : L ⊓ centModSubgroup p L ≤ Hlift p x L R₀ := fun z hz =>
    ⟨hz.1, Subgroup.mem_sup_right ⟨hz.2, h.tri.comp.1 hz.1⟩⟩
  have hZc : ∀ z ∈ L ⊓ centModSubgroup p L, ∀ g ∈ Hlift p x L R₀, z * g = g * z := fun z hz g hg =>
    (Subgroup.mem_centralizer_iff.1 (Z_central_of_qs h hz) g hg.1).symm
  obtain ⟨S, hSH, hS2, hHS, hchar⟩ := exists_char_sylow_two hZH hZc (H_two_power h hR₀2 hR₀x)
  exact ⟨S, hSH.trans inf_le_left, hS2, fun b hb => hchar b (B_norm_Hlift h hBR₀ hb), hHS⟩

theorem exists_centMod_of_inducesInnerMod {L : Subgroup G} {g : G} (h : InducesInnerMod p L g) :
    ∃ l ∈ L, l⁻¹ * g ∈ centModSubgroup p L := by
  have hg := S3.mem_normalizer_of_inducesInnerMod h
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨l, hl, ?_⟩
  have h1 : g⁻¹ * l ∈ centModSubgroup p L := by
    refine ⟨mul_mem (inv_mem hg) (Subgroup.le_normalizer hl), fun y hy' => ?_⟩
    have := hy (l * y⁻¹ * l⁻¹) (L.mul_mem (L.mul_mem hl (L.inv_mem hy')) (L.inv_mem hl))
    have e : (l⁻¹ * (l * y⁻¹ * l⁻¹) * l)⁻¹ * (g⁻¹ * (l * y⁻¹ * l⁻¹) * g) = ⁅y, g⁻¹ * l⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at this
  have h2 := inv_mem h1
  simpa [mul_inv_rev] using h2

theorem noncomm_of_two_part (h : Cfg12 G m p B x L D K) {R₀ S : Subgroup G} (hR₀2 : IsPGroup 2 R₀)
    (hR₀x : R₀ ≤ Subgroup.centralizer ({x} : Set G)) (hBR₀ : B ≤ Subgroup.normalizer (R₀ : Set G))
    (hCodd : Odd (Nat.card ↥(centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G))))
    (hinn : ∀ g ∈ R₀, InducesInnerMod p L g) (hSL : S ≤ L)
    (hHS : Hlift p x L R₀ ≤ S ⊔ (L ⊓ centModSubgroup p L)) (hne : (⁅R₀, B⁆ : Subgroup G) ≠ ⊥) :
    (⁅S, B⁆ : Subgroup G) ≠ ⊥ := by
  intro hS
  apply hne
  set C := centModSubgroup p L ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := h.tri.comp.1
  have hconjC : ∀ t ∈ Subgroup.normalizer (L : Set G), t ∈ Subgroup.centralizer ({x} : Set G) →
      ∀ c ∈ C, t * c * t⁻¹ ∈ C := fun t htL htx c hc =>
    Subgroup.mem_inf.2 ⟨S3.conj_mem_centModSubgroup htL (Subgroup.mem_inf.1 hc).1,
      mul_mem (mul_mem htx (Subgroup.mem_inf.1 hc).2) (inv_mem htx)⟩
  refine le_bot_iff.1 ?_
  rw [Subgroup.commutator_le]
  intro r hr b hb
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := h.tri.norm hb
  have hbx : b ∈ Subgroup.centralizer ({x} : Set G) := B_le_cx h hb
  obtain ⟨l, hlL, hc⟩ := exists_centMod_of_inducesInnerMod (hinn r hr)
  set c := l⁻¹ * r with hc_def
  have hcC : c ∈ C := Subgroup.mem_inf.2 ⟨hc, mul_mem (inv_mem (hLx hlL)) (hR₀x hr)⟩
  have hlr : l = r * c⁻¹ := by rw [hc_def]; group
  have hlH : l ∈ Hlift p x L R₀ :=
    Subgroup.mem_inf.2 ⟨hlL, by rw [hlr]; exact Subgroup.mul_mem_sup hr (inv_mem hcC)⟩
  have hSZ : S ≤ Subgroup.normalizer ((L ⊓ centModSubgroup p L : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_inf' (Subgroup.le_normalizer (hSL hs))
      (L62.normalizer_le_normalizer_centModSubgroup p L (Subgroup.le_normalizer (hSL hs)))
  have hl' : l ∈ (S ⊔ (L ⊓ centModSubgroup p L) : Subgroup G) := hHS hlH
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSZ] at hl'
  obtain ⟨s, hs, z, hz, hlsz⟩ := Set.mem_mul.mp hl'
  have hsb : ⁅s, b⁆ = 1 := Subgroup.mem_bot.1 (hS ▸ Subgroup.commutator_mem_commutator hs hb)
  have hzb : ⁅z, b⁆ ∈ L ⊓ centModSubgroup p L := by
    have e : ⁅z, b⁆ = z * (b * z⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    refine mul_mem hz (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.1 hbL z⁻¹).1 (inv_mem (Subgroup.mem_inf.1 hz).1)
    · exact S3.conj_mem_centModSubgroup hbL (inv_mem (Subgroup.mem_inf.1 hz).2)
  have hlb : ⁅l, b⁆ ∈ L ⊓ centModSubgroup p L := by
    have e : ⁅s * z, b⁆ = s * ⁅z, b⁆ * s⁻¹ * ⁅s, b⁆ := by simp only [commutatorElement_def]; group
    rw [← hlsz, e, hsb, mul_one]
    have hcen := Z_central_of_qs h hzb
    have : s * ⁅z, b⁆ * s⁻¹ = ⁅z, b⁆ := by
      have := (Subgroup.mem_centralizer_iff.1 hcen s (hSL hs))
      rw [this]
      group
    rw [this]
    exact hzb
  have hlbC : ⁅l, b⁆ ∈ C := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hlb).2, hLx (Subgroup.mem_inf.1 hlb).1⟩
  have hcb : ⁅c, b⁆ ∈ C := by
    have e : ⁅c, b⁆ = c * (b * c⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem hcC (hconjC b hbL hbx c⁻¹ (inv_mem hcC))
  have hrb : ⁅r, b⁆ ∈ C := by
    have e : ⁅r, b⁆ = l * ⁅c, b⁆ * l⁻¹ * ⁅l, b⁆ := by
      rw [show r = l * c by rw [hc_def]; group]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hconjC l (Subgroup.le_normalizer hlL) (hLx hlL) _ hcb) hlbC
  have hrbR : ⁅r, b⁆ ∈ R₀ := by
    have e : ⁅r, b⁆ = r * (b * r⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem hr ((Subgroup.mem_normalizer_iff.1 (hBR₀ hb) r⁻¹).1 (inv_mem hr))
  rw [Subgroup.mem_bot]
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hR₀2 ⟨⁅r, b⁆, hrbR⟩
  rw [Subgroup.orderOf_mk] at hj
  have hdvd : orderOf (⁅r, b⁆ : G) ∣ Nat.card ↥C := by
    have := orderOf_dvd_natCard (⟨⁅r, b⁆, hrb⟩ : ↥C)
    rwa [Subgroup.orderOf_mk] at this
  rw [hj] at hdvd
  by_cases hj0 : j = 0
  · rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · exfalso
    have h2 : 2 ∣ Nat.card ↥C := (dvd_pow_self 2 hj0).trans hdvd
    have := Nat.odd_iff.1 hCodd
    omega

theorem comm_inner (h : Cfg12 G m p B x L D K) (hin : Inputs123 G p) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRx : R ≤ Subgroup.centralizer ({x} : Set G)) (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    ∀ g ∈ (⁅R, B⁆ : Subgroup G), InducesInnerMod p L g := by
  have hp := h.prime
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian h.tri.bmax.1
  have h712 := hin.i712 hp h.odd (Subgroup.centralizer ({x} : Set G)) L B R
    (isKGroup_le_cx h h.tri.ne_one le_rfl) h.tri.comp (h.tri.chev2 h.ctx) hBp hR2 h.tri.norm
    (hRx.trans (cx_le_normalizer_L h)) hBR
  intro g hg
  rw [Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r, hr, b, hb, rfl⟩ := hg
    rw [← commutatorElement_inv]
    exact S3.inducesInnerMod_inv (h712 b hb r hr)
  | one => exact S3.inducesInnerMod_one p L
  | mul a b _ _ ha hb => exact S3.inducesInnerMod_mul ha hb
  | inv a _ ha => exact S3.inducesInnerMod_inv ha

theorem exists_S_L (h : Cfg12 G m p B x L D K) (hin : Inputs123 G p)
    (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))))) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧ (⁅S, B⁆ : Subgroup G) ≠ ⊥ := by
  have hp := h.prime
  obtain ⟨-, -, R, hRx, hR2, hBR, hRB, -⟩ := IsSStarMax.essential h.tri.star
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian h.tri.bmax.1
  have hR₀R : (⁅R, B⁆ : Subgroup G) ≤ R := comm_le_left hBR
  have hR₀2 : IsPGroup 2 (⁅R, B⁆ : Subgroup G) := hR2.to_le hR₀R
  have hR₀x : (⁅R, B⁆ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := hR₀R.trans hRx
  have hBR₀ : B ≤ Subgroup.normalizer ((⁅R, B⁆ : Subgroup G) : Set G) := fun b hb =>
    normalizer_commutator (hBR hb) (Subgroup.le_normalizer hb)
  have hne := coprime_comm_self hp h.odd hR2 hBp hBR hRB
  obtain ⟨S, hSL, hS2, hBS, hHS⟩ := exists_two_part h hR₀2 hR₀x hBR₀
  exact ⟨S, hSL, hS2, hBS, noncomm_of_two_part h hR₀2 hR₀x hBR₀ (centMod_cx_odd h hodd)
    (comm_inner h hin hR2 hRx hBR) hSL hHS hne⟩

theorem rank_of_normalizes (hp : p.Prime) {B' T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hB'T : B' ≤ Subgroup.normalizer (T : Set G)) : CFSG.Open.pRank p B' ≤ GLATwoLocalRank p G :=
  CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes hp hT1 hT2 hB'T

theorem isElemAbelian_card (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A) : ∃ k, Nat.card A = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p ↥A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 (g : G) g.2)⟩
  exact (IsPGroup.iff_card).1 hpg

theorem no_iv (h : Cfg12 G m p B x L D K) (hin : Inputs123 G p) (hnn : NoNbr12 p B x L D K) {B' U : Subgroup G}
    (hB'el : IsElemAbelian p B') (hBB' : B ≤ B') (hBne : B ≠ B') (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUK : U ≤ K)
    (hB'eq : B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set G))) : False := by
  have hp := h.prime
  have hDU : D ≤ Subgroup.centralizer (U : Set G) := Subgroup.le_centralizer_iff.2 (hUK.trans h.K_le_cs)
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _ (hDU h.xD)
  obtain ⟨hT₀2, hNT₀⟩ := pCoreOf_two_facts (Subgroup.normalizer (U : Set G))
  have hDN : D ≤ Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (U : Set G)) : Subgroup G) : Set G) :=
    fun d hd => hNT₀ (Subgroup.centralizer_le_normalizer _ (hDU hd))
  have hT1 := x_nontrivial h hU1 hU2 hxU
  have hKT := lemma124 h hin.to124 hnn hT₀2 hDN
  have hTK := Subgroup.le_centralizer_iff.1 hKT
  have hxT : Subgroup.zpowers x ≤ Subgroup.normalizer
      ((pCoreOf 2 (Subgroup.normalizer (U : Set G)) : Subgroup G) : Set G) := Subgroup.zpowers_le.2 (hDN h.xD)
  have hT2 := hT₀2.to_le (comm_le_left hxT)
  have hxB' : ∀ g ∈ B', g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := fun g hg => by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [S3.centralizer_zpowers x]
    exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB'el hg (hBB' h.tri.mem))
  have hB'T : B' ≤ Subgroup.normalizer ((⁅pCoreOf 2 (Subgroup.normalizer (U : Set G)), Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    refine le_trans (le_of_eq hB'eq) (sup_le (fun g hg => Subgroup.centralizer_le_normalizer _ (hTK hg.2)) (fun g hg => ?_))
    exact normalizer_commutator (hNT₀ hg.2) (hxB' g hg.1)
  have hrk := rank_of_normalizes hp hT2 hT1 hB'T
  obtain ⟨k, hk⟩ := isElemAbelian_card hp hB'el
  have hB'rk : CFSG.Open.pRank p B' = k := L6364.pRank_eq_of_card hp hB'el hk
  have hlt : Nat.card B < Nat.card B' := by
    by_contra hge
    exact hBne (Subgroup.eq_of_le_of_card_ge hBB' (not_lt.1 hge))
  rw [h.card_B, hk] at hlt
  have hmk : m < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  rw [hB'rk, h.ctx.rank] at hrk
  omega

theorem lemma126 (h : Cfg12 G m p B x L D K) (hin : Inputs123 G p) (hnn : NoNbr12 p B x L D K) :
    Type126 p L K (Jc B x K) := by
  obtain ⟨S, hSL, hS2, hSN, hSne⟩ := lemma125_i h hin.to124 hnn
  have hodd := lemma125_ii h hin.to124 hnn
  have hb := exists_S_L h hin hodd
  rcases hin.i173 p B x L D K h.prime h.odd h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx)
      h.tri.split h.pre hb ⟨S, hSL, hS2, hSN, hSne⟩ with h6 | ⟨B', U, hB'el, -, hBB', hBne, hU1, hU2, hUK, hB'eq⟩
  · exact h6
  · exact (no_iv h hin hnn hB'el hBB' hBne hU1 hU2 hUK hB'eq).elim

end S12

end CFSG.LocalAnalysis.GLTheoremA
