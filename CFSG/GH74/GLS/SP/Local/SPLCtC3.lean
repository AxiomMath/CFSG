module

public import CFSG.GH74.GLS.SP.Local.SPLCtT2
public import CFSG.GH74.GLS.SP.Local.SPLCtDX2
public import CFSG.GH74.GLS.SP.Local.SPLCtC1aSyl
public import CFSG.GH74.GLS.SP.Local.SPLCtT1

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section C3a

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

@[expose] def SPLNot1.CcI : Subgroup G := D.Ct ⊓ centralizer (D.Ict : Set G)

omit [Finite G] in
theorem mem_CcI {x : G} : x ∈ D.CcI ↔ x ∈ D.Ct ∧ ∀ i ∈ D.Ict, i * x = x * i := by
  unfold SPLNot1.CcI
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

omit [Finite G] in
theorem CcI_normal (hA : SPLCtA D) : ∀ c ∈ D.Ct, ∀ m ∈ D.CcI, c * m * c⁻¹ ∈ D.CcI := by
  intro c hc m hm
  rw [mem_CcI] at hm ⊢
  refine ⟨D.Ct.mul_mem (D.Ct.mul_mem hc hm.1) (D.Ct.inv_mem hc), fun i hi => ?_⟩
  have hj : c⁻¹ * i * c ∈ D.Ict := by
    have := hA.I_normal c⁻¹ (D.Ct.inv_mem hc) i hi
    simpa using this
  have h1 := hm.2 _ hj
  calc i * (c * m * c⁻¹) = c * ((c⁻¹ * i * c) * m) * c⁻¹ := by group
    _ = c * (m * (c⁻¹ * i * c)) * c⁻¹ := by rw [h1]
    _ = (c * m * c⁻¹) * i := by group

omit [Finite G] in
theorem Act_le_CcI (hA : SPLCtA D) : D.Act ≤ D.CcI := fun a ha =>
  (mem_CcI D).mpr ⟨Act_le_Ct D ha, fun i hi => (hA.AI_comm a ha i hi).symm⟩

omit [Finite G] in
theorem T₀_le_CcI {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) : T₀ ≤ D.CcI :=
  fun c hc => by
    obtain ⟨hcT, hci⟩ := (hT.T₀_mem c).mp hc
    exact (mem_CcI D).mpr ⟨hT.T_le hcT, fun i hi => (hci i hi).symm⟩

omit [Finite G] in
theorem T₀_le_T {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) : T₀ ≤ T :=
  fun c hc => ((hT.T₀_mem c).mp hc).1

theorem Act_inf_T₀ {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    D.Act ⊓ T₀ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxT₀⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hT.T_p ⟨x, T₀_le_T D hT hxT₀⟩
  have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card ↥D.Act := by
    have := Subgroup.card_dvd_of_le (le_refl D.Act)
    rw [← Subgroup.orderOf_mk x hxA]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥D.Act) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Act_odd D))
  have := (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
  exact orderOf_eq_one_iff.mp this

theorem T₀_max_CcI (hA : SPLCtA D) {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    ∀ P : Subgroup G, P ≤ D.CcI → IsPGroup 2 P → T₀ ≤ P → P = T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hPM hPp hle
  have hPCt : P ≤ D.Ct := fun p hp => ((mem_CcI D).mp (hPM hp)).1
  obtain ⟨T', hPT', hT'Ct, hT'p, hT'max⟩ := exists_maximal_two_subgroup D.Ct P hPCt hPp
  obtain ⟨c, hc, hcT⟩ := sylow_conj_of_maximal D.Ct hT.T_le hT.T_p hT.T_max hT'Ct hT'p hT'max
  have hPc : P ≤ T₀.map (MulAut.conj c).toMonoidHom := by
    intro p hp
    have hpT' : p ∈ T.map (MulAut.conj c).toMonoidHom := hcT ▸ hPT' hp
    obtain ⟨s, hsT, hsp⟩ := hpT'
    have hsp' : c * s * c⁻¹ = p := by simpa [MulAut.conj_apply] using hsp
    have hsM : s ∈ D.CcI := by
      have := CcI_normal D hA c⁻¹ (D.Ct.inv_mem hc) p (hPM hp)
      have e : c⁻¹ * p * c⁻¹⁻¹ = s := by rw [← hsp']; group
      rwa [e] at this
    have hsT₀ : s ∈ T₀ := by
      rw [hT.T₀_mem]
      exact ⟨hsT, fun i hi => ((mem_CcI D).mp hsM).2 i hi |>.symm⟩
    exact ⟨s, hsT₀, hsp⟩
  have hcard : Nat.card ↥P ≤ Nat.card ↥T₀ := by
    calc Nat.card ↥P ≤ Nat.card ↥(T₀.map (MulAut.conj c).toMonoidHom) :=
          Subgroup.card_le_of_le hPc
      _ = Nat.card ↥T₀ := Subgroup.card_map_of_injective (MulAut.conj c).injective
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem ct_cenI (hA : SPLCtA D) (hK2 : SPLCenIAt D) {T T₀ T₁ : Subgroup G} {y : G}
    (hT : SPLCtT D T T₀ T₁ y) : D.CcI = D.Act ⊔ T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (sup_le (Act_le_CcI D hA) (T₀_le_CcI D hT))
  let M : Subgroup G := D.CcI
  let A' : Subgroup ↥M := D.Act.subgroupOf M
  have hA'n : A'.Normal := ⟨fun n hn g => by
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ D.Act
    exact Act_normal D g (((mem_CcI D).mp g.2).1) n hn⟩
  have hq2 : IsPGroup 2 (↥M ⧸ A') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m' =>
      have hm := (mem_CcI D).mp m'.2
      obtain ⟨k, hk⟩ := hK2 (m' : G) hm.1 (fun i hi => by
        have h1 : ⁅i, (m' : G)⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hm.2 i hi)
        rw [h1]; exact D.Act.one_mem)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).mp hq2
  have hA'card : Nat.card ↥A' = Nat.card ↥D.Act :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Act_le_CcI D hA)).toEquiv
  have hcardM : Nat.card ↥M = 2 ^ c * Nat.card ↥D.Act := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup A', hc, hA'card]
  let T₀' : Subgroup ↥M := T₀.subgroupOf M
  have hT₀'p : IsPGroup 2 T₀' := IsPGroup.comap_subtype (IsPGroup.to_le hT.T_p (T₀_le_T D hT))
  have hT₀'max : ∀ P : Subgroup ↥M, IsPGroup 2 P → T₀' ≤ P → P = T₀' := by
    intro P hP hle
    have hPp : IsPGroup 2 (P.map M.subtype) := hP.map _
    have hle' : T₀ ≤ P.map M.subtype := fun x hx =>
      ⟨⟨x, T₀_le_CcI D hT hx⟩, hle hx, rfl⟩
    have hPeq := T₀_max_CcI D hA hT (P.map M.subtype) (Subgroup.map_subtype_le P) hPp hle'
    apply le_antisymm
    · intro x hx
      have hx' : (x : G) ∈ P.map M.subtype := ⟨x, hx, rfl⟩
      rw [hPeq] at hx'
      exact hx'
    · exact hle
  obtain ⟨S, hS⟩ := SylowL2.exists_sylow_eq T₀' hT₀'p hT₀'max
  have hT₀'card : Nat.card ↥T₀' = Nat.card ↥T₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (T₀_le_CcI D hT)).toEquiv
  have hval : (Nat.card ↥M).factorization 2 = c := by
    have hodd := Act_odd D
    have hpos : Nat.card ↥D.Act ≠ 0 := Nat.card_pos.ne'
    have hn2 : ¬ 2 ∣ Nat.card ↥D.Act := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [hcardM, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hpos]
    simp [Nat.factorization_eq_zero_of_not_dvd hn2, Nat.Prime.factorization_self Nat.prime_two]
  have hcardT₀ : Nat.card ↥T₀ = 2 ^ c := by
    have h1 : Nat.card ↥T₀' = 2 ^ (Nat.card ↥M).factorization 2 := by
      rw [← hS]; exact Sylow.card_eq_multiplicity S
    rw [← hT₀'card, h1, hval]
  let φ : ↥T₀' →* (↥M ⧸ A') := (QuotientGroup.mk' A').comp T₀'.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ((t : ↥M) : ↥M ⧸ A') = 1 := ht
    have h2 : (t : ↥M) ∈ A' := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((t : ↥M) : G) ∈ D.Act ⊓ T₀ := ⟨h2, t.2⟩
    rw [Act_inf_T₀ D hT, Subgroup.mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hφbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le (by rw [hc, hT₀'card, hcardT₀])
  intro m hm
  obtain ⟨t', ht'⟩ := hφbij.2 ((⟨m, hm⟩ : ↥M) : ↥M ⧸ A')
  have h1 : ((t' : ↥M))⁻¹ * ⟨m, hm⟩ ∈ A' := QuotientGroup.eq.mp ht'
  have h2 : ((t' : G))⁻¹ * m ∈ D.Act := h1
  have h3 : (t' : G) ∈ T₀ := t'.2
  have hm' : m = (t' : G) * ((t' : G)⁻¹ * m) := by group
  have h4 : (t' : G) * ((t' : G)⁻¹ * m) ∈ T₀ ⊔ D.Act := Subgroup.mul_mem_sup h3 h2
  rw [← hm', sup_comm] at h4
  exact h4

end C3a

section C3b

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem ct_decomp (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hK2 : SPLCenIAt D)
    {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    ∀ c ∈ D.Ct, ∃ a ∈ D.Act, ∃ s ∈ T, ∃ c₁ ∈ D.C ⊓ D.Ct, c = a * s * c₁ := by
  intro c hc
  have hMeq := ct_cenI D hA hK2 hT
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hT₀M := T₀_le_CcI D hT
  have hT₀p : IsPGroup 2 T₀ := IsPGroup.to_le hT.T_p (T₀_le_T D hT)
  set T' : Subgroup G := T₀.map (MulAut.conj c).toMonoidHom with hT'
  have hT'M : T' ≤ D.CcI := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    simpa [MulAut.conj_apply] using CcI_normal D hA c hc t₀ (hT₀M ht₀)
  have hT'p : IsPGroup 2 T' := hT₀p.map _
  have hT'max : ∀ P : Subgroup G, P ≤ D.CcI → IsPGroup 2 P → T' ≤ P → P = T' := by
    intro P hPM hPp hle
    set P' : Subgroup G := P.map (MulAut.conj c⁻¹).toMonoidHom with hP'
    have hP'M : P' ≤ D.CcI := by
      rintro _ ⟨p, hp, rfl⟩
      simpa [MulAut.conj_apply] using CcI_normal D hA c⁻¹ (D.Ct.inv_mem hc) p (hPM hp)
    have hT₀P' : T₀ ≤ P' := by
      intro t₀ ht₀
      exact ⟨c * t₀ * c⁻¹, hle ⟨t₀, ht₀, rfl⟩, by simp; group⟩
    have hP'eq := T₀_max_CcI D hA hT P' hP'M (hPp.map _) hT₀P'
    apply le_antisymm
    · intro p hp
      have hmem : (MulAut.conj c⁻¹).toMonoidHom p ∈ T₀ := by
        rw [← hP'eq]; exact ⟨p, hp, rfl⟩
      exact ⟨_, hmem, by simp [MulAut.conj_apply]; group⟩
    · exact hle
  obtain ⟨m, hmM, hmeq⟩ := sylow_conj_of_maximal D.CcI hT₀M hT₀p (T₀_max_CcI D hA hT) hT'M hT'p hT'max
  set n : G := m⁻¹ * c with hn
  have hnCt : n ∈ D.Ct := D.Ct.mul_mem (D.Ct.inv_mem ((mem_CcI D).mp hmM).1) hc
  have hnT₀ : ∀ t₀ ∈ T₀, n * t₀ * n⁻¹ ∈ T₀ := by
    intro t₀ ht₀
    have h1 : c * t₀ * c⁻¹ ∈ T₀.map (MulAut.conj m).toMonoidHom := by
      rw [← hmeq]; exact ⟨t₀, ht₀, by simp [MulAut.conj_apply]⟩
    obtain ⟨t₁, ht₁, ht₁e⟩ := h1
    have e : n * t₀ * n⁻¹ = t₁ := by
      have h2 : m * t₁ * m⁻¹ = c * t₀ * c⁻¹ := by simpa [MulAut.conj_apply] using ht₁e
      calc n * t₀ * n⁻¹ = m⁻¹ * (c * t₀ * c⁻¹) * m := by rw [hn]; group
        _ = m⁻¹ * (m * t₁ * m⁻¹) * m := by rw [h2]
        _ = t₁ := by group
    rw [e]; exact ht₁
  have hzT₀ : D.z ∈ T₀ := hT.z_T₀
  have hz2 := hs.syl.z_inv
  have htc : ∀ a ∈ T₀ ⊔ zpowers y, D.t * a = a * D.t := by
    intro a ha
    have hYT : T₀ ⊔ zpowers y ≤ T := sup_le (T₀_le_T D hT) (zpowers_le.mpr hT.y_mem)
    exact (hT.t_central a (hYT ha)).symm
  have hzt : D.z ≠ D.t := fun h => hs.syl.t_nconj (h ▸ IsConj.refl _)
  have hz'ord : orderOf (n * D.z * n⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) D.z
    rw [MulAut.conj_apply] at this
    rw [this]; exact hz2
  have hz't : n * D.z * n⁻¹ ≠ D.t := by
    intro h
    apply hzt
    have hnt : n * D.t = D.t * n := mem_centralizer_singleton_iff.mp hnCt
    calc D.z = n⁻¹ * (n * D.z * n⁻¹) * n := by group
      _ = n⁻¹ * D.t * n := by rw [h]
      _ = D.t := by
        calc n⁻¹ * D.t * n = n⁻¹ * (D.t * n) := by group
          _ = n⁻¹ * (n * D.t) := by rw [hnt]
          _ = D.t := by group
  obtain ⟨g, hgY, hgz⟩ := dihedral_noncentral_involutions_conj hn3 (T₀ ⊔ zpowers y) T₀ le_sup_left
    hT.T₀y_dih hT.T₀_dih D.t (Subgroup.mem_sup_left hT.t_T₀) hs.syl.t_ord htc D.z
    (n * D.z * n⁻¹) hzT₀ (hnT₀ D.z hzT₀) hz2 hz'ord hzt hz't
  have hgT : g ∈ T := sup_le (T₀_le_T D hT) (zpowers_le.mpr hT.y_mem) hgY
  have hc₁C : g⁻¹ * n ∈ D.C := by
    show g⁻¹ * n ∈ centralizer ({D.z} : Set G)
    rw [mem_centralizer_singleton_iff]
    have : g * D.z * g⁻¹ = n * D.z * n⁻¹ := hgz
    calc g⁻¹ * n * D.z = g⁻¹ * (n * D.z * n⁻¹) * n := by group
      _ = g⁻¹ * (g * D.z * g⁻¹) * n := by rw [this]
      _ = D.z * (g⁻¹ * n) := by group
  have hc₁Ct : g⁻¹ * n ∈ D.Ct :=
    D.Ct.mul_mem (D.Ct.inv_mem (hT.T_le hgT)) hnCt
  have hmAT : m ∈ D.Act ⊔ T₀ := hMeq ▸ hmM
  have hT₀norm : T₀ ≤ normalizer (D.Act : Set G) := by
    intro t₀ ht₀
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha; exact Act_normal D t₀ (hT.T_le (T₀_le_T D hT ht₀)) a ha
    · intro ha
      have h1 := Act_normal D t₀⁻¹ (D.Ct.inv_mem (hT.T_le (T₀_le_T D hT ht₀))) _ ha
      have e : t₀⁻¹ * (t₀ * a * t₀⁻¹) * t₀⁻¹⁻¹ = a := by group
      rwa [e] at h1
  obtain ⟨a, ha, t₀', ht₀', hmat⟩ := sup_decomp_of_le_normalizer hT₀norm hmAT
  refine ⟨a, ha, t₀' * g, ?_, g⁻¹ * n, ⟨hc₁C, hc₁Ct⟩, ?_⟩
  · exact T.mul_mem (T₀_le_T D hT ht₀') hgT
  · calc c = m * n := by rw [hn]; group
      _ = (a * t₀') * n := by rw [hmat]
      _ = a * (t₀' * g) * (g⁻¹ * n) := by group

end C3b

end CFSG.GH74.GLS.SP.Local
