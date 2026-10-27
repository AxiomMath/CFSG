module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem isSec8Socle_of_mulEquiv {K₀ K₁ : Type} [Group K₀] [Group K₁] (e : K₀ ≃* K₁) {p f : ℕ}
    (hK : IsSec8Socle K₀ p f) : IsSec8Socle K₁ p f := by
  rcases hK with hm | ⟨hp, hf, ⟨e'⟩⟩
  · exact Or.inl (OddQuot.lieModel_of_equiv e hm)
  · exact Or.inr ⟨hp, hf, ⟨e.symm.trans e'⟩⟩

theorem mem_fixSubgroup_normalizerMonoidHom {G : Type*} [Group G] (L : Subgroup G) {s : G}
    (hs : s ∈ normalizer (L : Set G)) (l : L) :
    l ∈ fixSubgroup (L.normalizerMonoidHom ⟨s, hs⟩) ↔ s * (l : G) = l * s := by
  rw [mem_fixSubgroup]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    change s * (l : G) * s⁻¹ = l at this
    calc s * (l : G) = (s * (l : G) * s⁻¹) * s := by group
      _ = l * s := by rw [this]
  · intro h1
    apply Subtype.ext
    change s * (l : G) * s⁻¹ = l
    rw [h1, mul_inv_cancel_right]

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

abbrev C0 (h : Hyp52 X) : Subgroup X := centralizer ({h.a} : Set X) ⊓ coreActionKernel h.J

abbrev O0 (h : Hyp52 X) : Subgroup X := (pPrimeCore 2 h.C0).map h.C0.subtype

theorem odd_card_O0 (h : Hyp52 X) : Odd (Nat.card h.O0) := by
  rw [card_map_of_injective h.C0.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem P_le_C0 (h : Hyp52 X) : h.P ≤ h.C0 :=
  le_inf ((inf_le_left : h.P ≤ h.S).trans (h.S_le.trans inf_le_left)) inf_le_right

namespace L83Hyp

variable {H : L83Hyp h}

theorem centralizer_a_le_normalizer_C0 (H : L83Hyp h) :
    centralizer ({h.a} : Set X) ≤ normalizer (h.C0 : Set X) := by
  have hCaN := h.sec8_centralizer_a_le_normalizer_J H.J_normal
  refine le_normalizer_of_conj fun y hy w hw => ?_
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hy hw.1) (inv_mem hy), ?_⟩
  obtain ⟨hwN, hwc⟩ := mem_coreActionKernel.mp hw.2
  have hyN := hCaN hy
  have hON : y ∈ normalizer (((pPrimeCore 2 h.J).map h.J.subtype : Subgroup X) : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J (pPrimeCore 2 h.J) hyN
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem hyN hwN) (inv_mem hyN), fun j hj => ?_⟩
  have hj' : y⁻¹ * j * y ∈ h.J := by
    have := (mem_normalizer_iff.mp (inv_mem hyN) j).mp hj
    rwa [inv_inv] at this
  have h1 := hwc _ hj'
  have h2 := (mem_normalizer_iff.mp hON _).mp h1
  rw [show y * ((y⁻¹ * j * y)⁻¹ * w⁻¹ * (y⁻¹ * j * y) * w) * y⁻¹ =
    j⁻¹ * (y * w * y⁻¹)⁻¹ * j * (y * w * y⁻¹) by group] at h2
  exact h2

theorem centralizer_a_le_normalizer_O0 (H : L83Hyp h) :
    centralizer ({h.a} : Set X) ≤ normalizer (h.O0 : Set X) := fun _ hy =>
  UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.C0 (pPrimeCore 2 h.C0)
    (H.centralizer_a_le_normalizer_C0 hy)

theorem P_sylow_C0 (H : L83Hyp h) :
    ∃ T : Sylow 2 ↥h.C0, (T : Subgroup _) = h.P.subgroupOf h.C0 := by
  have h1 := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer
    (h.S_le.trans inf_le_left) H.S_sylow_C (inf_le_left : h.C0 ≤ centralizer ({h.a} : Set X))
    H.centralizer_a_le_normalizer_C0
  have h2 : h.S ⊓ h.C0 = h.P := by
    rw [C0, ← inf_assoc, inf_eq_left.mpr (h.S_le.trans inf_le_left)]
  rwa [h2] at h1

namespace Q3Data

variable (d : Q3Data H)
include d

theorem conj_pow_odd {n : X} (hna : n * h.a = h.a * n) (hnb : n * d.b * n⁻¹ = h.a * d.b) (i : ℕ) :
    n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹ = h.a * d.b := by
  have hn2 : n ^ 2 * d.b * (n ^ 2)⁻¹ = d.b := by
    have h1 : n * (h.a * d.b) * n⁻¹ = d.b := by
      rw [show n * (h.a * d.b) * n⁻¹ = (n * h.a * n⁻¹) * (n * d.b * n⁻¹) by group, hnb,
        show n * h.a * n⁻¹ = h.a by rw [hna, mul_inv_cancel_right], ← mul_assoc,
        Six.a_mul_a_self h, one_mul]
    rw [pow_two, show n * n * d.b * (n * n)⁻¹ = n * (n * d.b * n⁻¹) * n⁻¹ by group, hnb, h1]
  induction i with
  | zero => simpa using hnb
  | succ i ih =>
    rw [show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring, pow_add,
      show n ^ 2 * n ^ (2 * i + 1) * d.b * (n ^ 2 * n ^ (2 * i + 1))⁻¹ =
        n ^ 2 * (n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹) * (n ^ 2)⁻¹ by group, ih,
      show n ^ 2 * (h.a * d.b) * (n ^ 2)⁻¹ = (n ^ 2 * h.a * (n ^ 2)⁻¹) * (n ^ 2 * d.b * (n ^ 2)⁻¹)
        by group, hn2]
    congr 1
    have hna2 : n ^ 2 * h.a = h.a * n ^ 2 := by
      rw [pow_two, mul_assoc, hna, ← mul_assoc, hna, mul_assoc]
    rw [hna2, mul_inv_cancel_right]

theorem a_ne_b (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : h.a ≠ d.b := fun h1 =>
  d.b_not_mem_M3 hCF1 hCF2 (h1 ▸ h.a_mem_M3)

theorem normalizer_P_le_centralizer (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    normalizer ((h.P.subgroupOf h.C0 : Subgroup ↥h.C0) : Set ↥h.C0) ≤
      centralizer ((h.P.subgroupOf h.C0 : Subgroup ↥h.C0) : Set ↥h.C0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := H.P_sylow_C0
  have hbP : d.b ∈ h.P := by
    have hbB : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b
    exact ⟨(h.B_le hbB).1, (h.B_le hbB).2⟩
  have hbC : d.b ∈ h.C0 := P_le_C0 h hbP
  intro n hn
  have hna : (n : X) * h.a = h.a * n := mem_centralizer_singleton_iff.mp n.2.1
  have hnbP : (n : X) * d.b * (n : X)⁻¹ ∈ h.P := by
    have := (mem_normalizer_iff.mp hn ⟨d.b, hbC⟩).mp hbP
    exact this
  have key : d.b = (n : X)⁻¹ * ((n : X) * d.b * (n : X)⁻¹) * n := by group
  have hb1 : d.b ≠ 1 := by
    intro h1
    have := d.b_ord
    rw [h1, orderOf_one] at this
    norm_num at this
  have hnb : (n : X) * d.b * (n : X)⁻¹ = d.b := by
    rcases d.P_mem _ hnbP with h1 | h1 | h1 | h1
    · exfalso
      rw [h1] at key
      exact hb1 (by rw [key]; group)
    · exfalso
      rw [h1, show (n : X)⁻¹ * h.a * n = h.a by rw [mul_assoc, ← hna, inv_mul_cancel_left]] at key
      exact d.a_ne_b hCF1 hCF2 key.symm
    · exact h1
    · exfalso
      obtain ⟨k, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
      obtain ⟨i, rfl⟩ := hr
      set n' : ↥h.C0 := n ^ (2 * i + 1) with hn'
      have hn'b : (n' : X) * d.b * (n' : X)⁻¹ = h.a * d.b := by
        rw [hn', SubgroupClass.coe_pow]
        exact d.conj_pow_odd hna h1 i
      have hdvd : 2 * i + 1 ∣ orderOf n := by
        rw [hm]
        exact dvd_mul_left _ _
      have hn'2 : IsPGroup 2 (zpowers n') := by
        refine IsPGroup.of_card (n := k) ?_
        rw [Nat.card_zpowers, hn', orderOf_pow_of_dvd (by omega) hdvd, hm,
          Nat.mul_div_cancel _ (by omega)]
      have hT2 : IsPGroup 2 (T : Subgroup ↥h.C0) := T.isPGroup'
      have hle : zpowers n' ≤ normalizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) := by
        rw [zpowers_le, hT]
        exact pow_mem hn _
      have hsup := IsPGroup.to_sup_of_normal_left' hT2 hn'2 hle
      have hmax := T.is_maximal' hsup le_sup_left
      have hn'T : n' ∈ (T : Subgroup ↥h.C0) := by
        rw [← hmax]
        exact mem_sup_right (mem_zpowers n')
      rw [hT] at hn'T
      have hbQ : d.b ∈ h.Q := (d.P_eq ▸ hbP).1
      have hc : (n' : X) * d.b = d.b * n' := d.P_comm_Q hn'T hbQ
      rw [hc, mul_inv_cancel_right] at hn'b
      apply (show h.a ≠ 1 from fun h2 => by
        have := h.orderOf_a
        rw [h2, orderOf_one] at this
        norm_num at this)
      have := congrArg (fun t => t * d.b⁻¹) hn'b
      simp only [mul_inv_cancel, mul_inv_cancel_right] at this
      exact this.symm
  rw [mem_centralizer_iff]
  intro p hp
  have hp' : (p : X) ∈ h.P := hp
  have hnb' : (n : X) * d.b = d.b * n := by
    calc (n : X) * d.b = (n : X) * d.b * (n : X)⁻¹ * n := by group
      _ = d.b * n := by rw [hnb]
  apply Subtype.ext
  rcases d.P_mem _ hp' with h1 | h1 | h1 | h1 <;> simp only [Subgroup.coe_mul] <;> rw [h1]
  · group
  · exact hna.symm
  · exact hnb'.symm
  · rw [mul_assoc, ← hnb', ← mul_assoc, ← hna, mul_assoc]

theorem sq_mem_O0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ h.C0) : y * y ∈ h.O0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := H.P_sylow_C0
  have hP : normalizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) ≤
      centralizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) := by
    rw [hT]
    exact d.normalizer_P_le_centralizer hCF1 hCF2
  set φ := MonoidHom.transferSylow T hP with hφ
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow T hP
  have hker : φ.ker ≤ pPrimeCore 2 ↥h.C0 :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd⟩
  have h1 : (⟨y, hy⟩ : ↥h.C0) * ⟨y, hy⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    apply Subtype.ext
    have ht : ((φ ⟨y, hy⟩ : T) : ↥h.C0) ∈ h.P.subgroupOf h.C0 := hT ▸ (φ ⟨y, hy⟩).2
    exact Subtype.ext (d.P_mul_self ht)
  exact ⟨_, hker h1, rfl⟩

theorem exists_pow_mem_O0 (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hII : CFA6InnerInv) {y : X} (hya : y ∈ centralizer ({h.a} : Set X))
    (hyz : y * (d.b * d.z) = d.b * d.z * y) : ∃ k : ℕ, y ^ 2 ^ k ∈ h.O0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCaN := h.sec8_centralizer_a_le_normalizer_J H.J_normal
  have hyN := hCaN hya
  have hbS : d.b ∈ h.S := (h.B_le (d.B_eq ▸ mem_zpowers d.b)).1
  have hbP : d.b ∈ h.P := ⟨hbS, (h.B_le (d.B_eq ▸ mem_zpowers d.b)).2⟩
  have hbN : d.b ∈ normalizer (h.J : Set X) := h.sec8_S_le_normalizer_J hbS
  have hzJ : d.z ∈ h.J := h.sec8_D_le_J d.z_D
  have hσbz : Eight.oddBarAction h.J ⟨d.b * d.z, mul_mem hbN (le_normalizer hzJ)⟩ =
      MulAut.conj d.zbar := by
    rw [show (⟨d.b * d.z, mul_mem hbN (le_normalizer hzJ)⟩ : normalizer (h.J : Set X)) =
      ⟨d.b, hbN⟩ * ⟨d.z, le_normalizer hzJ⟩ from rfl, map_mul,
      Eight.mem_ker_oddBarAction.mpr hbP.2, one_mul]
    exact (h.conj_mk_eq ⟨d.z, hzJ⟩).symm
  have hz2 : d.zbar * d.zbar = 1 := by
    rw [← QuotientGroup.mk_mul]
    rw [show (⟨d.z, hzJ⟩ : h.J) * ⟨d.z, hzJ⟩ = 1 from Subtype.ext d.z_sq, QuotientGroup.mk_one]
  have h2 := (hII _ hq.2 d.zbar hz2 d.zbar_ne_one).2
  have hyC : Eight.oddBarAction h.J ⟨y, hyN⟩ ∈
      centralizer ({MulAut.conj d.zbar} : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    rw [mem_centralizer_singleton_iff, ← hσbz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  obtain ⟨m, hm⟩ := h2 ⟨_, hyC⟩
  have hm' : Eight.oddBarAction h.J ⟨y ^ 2 ^ m, pow_mem hyN _⟩ = 1 := by
    have := congrArg Subtype.val hm
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
    rw [← this, ← map_pow]
    rfl
  have hC0 : y ^ 2 ^ m ∈ h.C0 :=
    ⟨pow_mem hya _, Eight.mem_ker_oddBarAction.mp hm'⟩
  refine ⟨m + 1, ?_⟩
  rw [pow_succ, pow_mul, pow_two]
  exact d.sq_mem_O0 hCF1 hCF2 hC0

theorem b_not_conj_bz (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hII : CFA6InnerInv) (hNN : CFQ3NoNilp) (w : X) : w⁻¹ * d.b * w ≠ d.b * d.z := by
  intro hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := conjugate h.K w with hL
  have hLbz : ∀ l ∈ L, l * (d.b * d.z) = d.b * d.z * l := by
    intro l hl
    rw [hL, mem_conjugate_iff] at hl
    have h1 := mem_centralizer_singleton_iff.mp (d.K_le_centralizer_b hl)
    rw [← hw]
    calc l * (w⁻¹ * d.b * w) = w⁻¹ * ((w * l * w⁻¹) * d.b) * w := by group
      _ = w⁻¹ * (d.b * (w * l * w⁻¹)) * w := by rw [h1]
      _ = w⁻¹ * d.b * w * l := by group
  have hza : d.z * h.a = h.a * d.z :=
    mem_centralizer_singleton_iff.mp (h.J_le (h.sec8_D_le_J d.z_D))
  have hab : h.a * (d.b * d.z) = d.b * d.z * h.a := by
    rw [← mul_assoc, ← d.ba, mul_assoc, ← hza, mul_assoc]
  have haW : h.a ∈ conjugate (normalizer (h.B : Set X)) w := by
    rw [mem_conjugate_iff, d.normalizer_B, mem_centralizer_singleton_iff]
    rw [← hw] at hab
    calc w * h.a * w⁻¹ * d.b = w * (h.a * (w⁻¹ * d.b * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * d.b * w) * h.a) * w⁻¹ := by rw [hab]
      _ = d.b * (w * h.a * w⁻¹) := by group
  have haL : h.a ∈ normalizer (L : Set X) := by
    rw [hL, ← H.V_eq_K, Hyp52.V, Six.conjugate_layerIn]
    exact OddQuot.le_normalizer_layerIn _ haW
  let e : h.K ≃* L := h.K.equivMapOfInjective (MulAut.conj w⁻¹).toMonoidHom
    (MulAut.conj w⁻¹).injective
  have hsoc : IsSec8Socle (L ⧸ pPrimeCore 2 L) 3 1 :=
    Eight.isSec8Socle_of_mulEquiv
      (QuotientGroup.congr (pPrimeCore 2 h.K) (pPrimeCore 2 L) e (pPrimeCore_map_iso 2 e)) hq.1
  set σ := L.normalizerMonoidHom ⟨h.a, haL⟩ with hσdef
  have haa : (⟨h.a, haL⟩ : normalizer (L : Set X)) * ⟨h.a, haL⟩ = 1 :=
    Subtype.ext (Six.a_mul_a_self h)
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, haa, map_one]
  have hσ : IsPGroup 2 (zpowers σ) := isPGroup_zpowers_of_mul_self hσ2
  set α := Eight.oddBarAction L ⟨h.a, haL⟩ with hαdef
  have hα : α * α = 1 := by rw [hαdef, ← map_mul, haa, map_one]
  have hfix : Eight.fixSubgroup α =
      (Eight.fixSubgroup σ).map (QuotientGroup.mk' (pPrimeCore 2 L)) :=
    Eight.fixSubgroup_oddBarAut σ hσ
  have hfixσ : ∀ l : L, l ∈ Eight.fixSubgroup σ ↔ h.a * (l : X) = l * h.a :=
    Eight.mem_fixSubgroup_normalizerMonoidHom L haL
  have hO0a : h.O0 ≤ centralizer ({h.a} : Set X) := (map_subtype_le _).trans inf_le_left
  set N := (h.O0.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L)) with hNdef
  have hNle : N ≤ Eight.fixSubgroup α := by
    rw [hfix]
    refine map_mono fun l hl => (hfixσ l).mpr ?_
    exact (mem_centralizer_singleton_iff.mp (hO0a hl)).symm
  apply hNN _ hsoc α hα
  refine ⟨N, hNle, (normal_subgroupOf_iff hNle).mpr ?_, ?_, ?_⟩
  ·
    intro n k hn hk
    rw [hfix] at hk
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hk
    obtain ⟨o, ho, rfl⟩ := mem_map.mp hn
    rw [← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem _ ?_
    have hla : (l : X) ∈ centralizer ({h.a} : Set X) :=
      mem_centralizer_singleton_iff.mpr ((hfixσ l).mp hl).symm
    show (l : X) * o * (l : X)⁻¹ ∈ h.O0
    exact (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_O0 hla) o).mp ho
  ·
    have h1 : Nat.card N ∣ Nat.card (h.O0.subgroupOf L) := card_map_dvd _ _
    have h2 : Nat.card (h.O0.subgroupOf L) ∣ Nat.card h.O0 := by
      rw [← card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat (odd_card_O0 h) (h1.trans h2)
  ·
    intro y hy
    rw [hfix] at hy
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hy
    have hla : (l : X) ∈ centralizer ({h.a} : Set X) :=
      mem_centralizer_singleton_iff.mpr ((hfixσ l).mp hl).symm
    obtain ⟨k, hk⟩ := d.exists_pow_mem_O0 hq hCF1 hCF2 hII hla (hLbz l l.2)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    refine mem_map_of_mem _ ?_
    show ((l ^ 2 ^ k : L) : X) ∈ h.O0
    rw [SubgroupClass.coe_pow]
    exact hk

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
