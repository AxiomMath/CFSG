module

public import CFSG.GH74.GLS.SP.Local.SPLCt0
public import CFSG.GH74.GLS.SP.Local.SPLCtFR
public import CFSG.GH74.GLS.SP.Local.SPLCtFour

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtA2a

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

private theorem Ict_le_L (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ pLayerOf 2 D.Ct :=
  CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf (s := D.z) (t := D.t)
    hs.syl.z_inv (mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)) (I_comp D hs)

private theorem Aprime_norm (hs : SPLSetup D.toSPLNot0) {i : G} (hi : i ∈ D.Ict) {a : G}
    (ha : a ∈ pLayerOf 2 D.Ct ⊓ D.Act) : i * a * i⁻¹ ∈ pLayerOf 2 D.Ct ⊓ D.Act := by
  have hiL : i ∈ pLayerOf 2 D.Ct := Ict_le_L D hs hi
  have haL : a ∈ pLayerOf 2 D.Ct := (Subgroup.mem_inf.mp ha).1
  have haA : a ∈ D.Act := (Subgroup.mem_inf.mp ha).2
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hiL haL) (Subgroup.inv_mem _ hiL),
      Act_normal D i (Ict_le_Ct D hs hi) a haA⟩

private theorem CA_involution (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e)
    {v : G} (hv : v ∈ D.Ict) (hvo : orderOf v = 2) :
    IsCyclic ↥(D.Act ⊓ centralizer ({v} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({v} : Set G)) ∣ D.e := by
  have hu' : orderOf (⟨u, hu.mem_I⟩ : ↥D.Ict) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu.ord
  have hv' : orderOf (⟨v, hv⟩ : ↥D.Ict) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hvo
  obtain ⟨j, hj⟩ := (L2facts D hs).2.1 ⟨u, hu.mem_I⟩ ⟨v, hv⟩ hu' hv'
  have hjuv : (j : G) * u * (j : G)⁻¹ = v := congrArg Subtype.val hj
  have hjI : (j : G) ∈ D.Ict := j.2
  have hu_eq : u = (j : G)⁻¹ * v * (j : G) := by rw [← hjuv]; group
  have hjct : (j : G)⁻¹ ∈ D.Ct := Subgroup.inv_mem _ (Ict_le_Ct D hs hjI)
  have hmem : ∀ a : ↥(D.Act ⊓ centralizer ({v} : Set G)),
      (j : G)⁻¹ * a * j ∈ D.Act ⊓ centralizer ({u} : Set G) := by
    intro a
    have haA : (a : G) ∈ D.Act := (Subgroup.mem_inf.mp a.2).1
    have hav : (a : G) * v = v * a := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp a.2).2
    refine Subgroup.mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have h := Act_normal D (j : G)⁻¹ hjct a haA
      simpa using h
    · calc (j : G)⁻¹ * a * j * u = (j : G)⁻¹ * (a * v) * j := by rw [hu_eq]; group
        _ = (j : G)⁻¹ * (v * a) * j := by rw [hav]
        _ = u * ((j : G)⁻¹ * a * j) := by rw [hu_eq]; group
  let ψ : ↥(D.Act ⊓ centralizer ({v} : Set G)) →* ↥(D.Act ⊓ centralizer ({u} : Set G)) :=
    { toFun := fun a => ⟨(j : G)⁻¹ * a * j, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h : (j : G)⁻¹ * a * j = (j : G)⁻¹ * b * j := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hcyc : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) := hA0.1
  exact ⟨isCyclic_of_injective ψ hψ, (Subgroup.card_dvd_of_injective ψ hψ).trans hA0.2⟩

private theorem gen_cent (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e)
    {v : G} (hv : v ∈ D.Ict) (hvo : orderOf v = 2) :
    ∃ c ∈ pLayerOf 2 D.Ct ⊓ D.Act, c ^ D.e = 1 ∧
      ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, v * a = a * v → a ∈ zpowers c := by
  obtain ⟨hcyc, hdvd⟩ := CA_involution D hs hu hA0 hv hvo
  have hle : (pLayerOf 2 D.Ct ⊓ D.Act) ⊓ centralizer ({v} : Set G) ≤
      D.Act ⊓ centralizer ({v} : Set G) := inf_le_inf_right _ inf_le_right
  have hC : IsCyclic ↥((pLayerOf 2 D.Ct ⊓ D.Act) ⊓ centralizer ({v} : Set G)) :=
    Subgroup.isCyclic_of_le hle
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥((pLayerOf 2 D.Ct ⊓ D.Act) ⊓ centralizer ({v} : Set G)))
  have hgmem : (g : G) ∈ pLayerOf 2 D.Ct ⊓ D.Act := (Subgroup.mem_inf.mp g.2).1
  have hcard : Nat.card ↥((pLayerOf 2 D.Ct ⊓ D.Act) ⊓ centralizer ({v} : Set G)) ∣ D.e :=
    (Subgroup.card_dvd_of_le hle).trans hdvd
  refine ⟨g, hgmem, ?_, ?_⟩
  · have h1 : g ^ D.e = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hcard)
    simpa using congrArg Subtype.val h1
  · intro a ha hva
    have haC : a ∈ (pLayerOf 2 D.Ct ⊓ D.Act) ⊓ centralizer ({v} : Set G) :=
      Subgroup.mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hva.symm⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, haC⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem second_involution (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    ∃ w ∈ D.Ict, orderOf w = 2 ∧ w ≠ u ∧ u * w = w * u := by
  have hu' : orderOf (⟨u, hu.mem_I⟩ : ↥D.Ict) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu.ord
  obtain ⟨φ⟩ := (L2facts D hs).2.2 ⟨u, hu.mem_I⟩ hu'
  have hd4 : 4 ≤ D.d := by
    have := hs.q_ge
    unfold SPLNot0.d
    split_ifs <;> omega
  have : Fact (1 < D.d / 2) := ⟨by omega⟩
  set u' : ↥D.Ict := ⟨u, hu.mem_I⟩ with hu'def
  let c₀ : ↥(centralizer ({u'} : Set ↥D.Ict)) :=
    ⟨u', mem_centralizer_singleton_iff.mpr rfl⟩
  have hex : ∃ i : ZMod (D.d / 2), DihedralGroup.sr i ≠ φ c₀ := by
    by_cases h : φ c₀ = DihedralGroup.sr 0
    · refine ⟨1, ?_⟩
      rw [h]
      simp
    · exact ⟨0, fun h' => h h'.symm⟩
  obtain ⟨i, hi⟩ := hex
  let w : ↥(centralizer ({u'} : Set ↥D.Ict)) := φ.symm (DihedralGroup.sr i)
  have hw_ord : orderOf w = 2 := by
    rw [MulEquiv.orderOf_eq φ.symm]
    exact DihedralGroup.orderOf_sr i
  have hw_ne : w ≠ c₀ := by
    intro h
    apply hi
    rw [← h]
    simp [w]
  have hwI : ((w : ↥D.Ict) : G) ∈ D.Ict := (w : ↥D.Ict).2
  refine ⟨((w : ↥D.Ict) : G), hwI, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw_ord
  · intro h
    apply hw_ne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · have h := mem_centralizer_singleton_iff.mp w.2
    exact (congrArg Subtype.val h).symm

private theorem Aprime_gen (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e) :
    ∃ c₁ ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∃ c₂ ∈ pLayerOf 2 D.Ct ⊓ D.Act,
      ∃ c₃ ∈ pLayerOf 2 D.Ct ⊓ D.Act, c₁ ^ D.e = 1 ∧ c₂ ^ D.e = 1 ∧ c₃ ^ D.e = 1 ∧
      ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∃ k₁ k₂ k₃ : ℤ, a = c₁ ^ k₁ * c₂ ^ k₂ * c₃ ^ k₃ := by
  obtain ⟨w, hwI, hwo, hwne, hcomm⟩ := second_involution D hs hu
  have huu : u * u = 1 := by
    rw [← sq]
    have h := pow_orderOf_eq_one u
    rwa [hu.ord] at h
  have hww : w * w = 1 := by
    rw [← sq]
    have h := pow_orderOf_eq_one w
    rwa [hwo] at h
  have h33 : (u * w) * (u * w) = 1 := by
    calc u * w * (u * w) = u * (w * u) * w := by group
      _ = u * (u * w) * w := by rw [← hcomm]
      _ = (u * u) * (w * w) := by group
      _ = 1 := by rw [huu, hww, one_mul]
  have hu3I : u * w ∈ D.Ict := Subgroup.mul_mem _ hu.mem_I hwI
  have hu3ne : u * w ≠ 1 := by
    intro h
    apply hwne
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right huu
  have hu3o : orderOf (u * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact h33) hu3ne
  have hAc : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ b ∈ pLayerOf 2 D.Ct ⊓ D.Act, a * b = b * a :=
    fun a ha b hb => Act_comm D hs a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2
  have hAodd : Odd (Nat.card ↥(pLayerOf 2 D.Ct ⊓ D.Act)) :=
    Odd.of_dvd_nat (Act_odd D) (Subgroup.card_dvd_of_le inf_le_right)
  have hfour := four_group_generation (pLayerOf 2 D.Ct ⊓ D.Act) hAc hAodd u w huu hww hcomm
    (fun a ha => Aprime_norm D hs hu.mem_I ha) (fun a ha => Aprime_norm D hs hwI ha)
  obtain ⟨c₁, hc₁, he₁, hg₁⟩ := gen_cent D hs hu hA0 hu.mem_I hu.ord
  obtain ⟨c₂, hc₂, he₂, hg₂⟩ := gen_cent D hs hu hA0 hwI hwo
  obtain ⟨c₃, hc₃, he₃, hg₃⟩ := gen_cent D hs hu hA0 hu3I hu3o
  refine ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, he₁, he₂, he₃, ?_⟩
  intro a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, e₁, e₂, e₃, rfl⟩ := hfour a ha
  obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ a₁ ha₁ (mul_inv_eq_iff_eq_mul.mp e₁))
  obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₂ a₂ ha₂ (mul_inv_eq_iff_eq_mul.mp e₂))
  obtain ⟨k₃, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₃ a₃ ha₃ (mul_inv_eq_iff_eq_mul.mp e₃))
  exact ⟨k₁, k₂, k₃, rfl⟩

private theorem Aprime_exp (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e) :
    ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, a ^ D.e = 1 := by
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, he₁, he₂, he₃, hgen⟩ := Aprime_gen D hs hu hA0
  intro a ha
  obtain ⟨k₁, k₂, k₃, rfl⟩ := hgen a ha
  have hpow : ∀ (c : G) (k : ℤ), c ^ D.e = 1 → (c ^ k) ^ D.e = 1 := by
    intro c k h
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  have c12 : Commute c₁ c₂ :=
    Act_comm D hs c₁ (Subgroup.mem_inf.mp hc₁).2 c₂ (Subgroup.mem_inf.mp hc₂).2
  have c13 : Commute c₁ c₃ :=
    Act_comm D hs c₁ (Subgroup.mem_inf.mp hc₁).2 c₃ (Subgroup.mem_inf.mp hc₃).2
  have c23 : Commute c₂ c₃ :=
    Act_comm D hs c₂ (Subgroup.mem_inf.mp hc₂).2 c₃ (Subgroup.mem_inf.mp hc₃).2
  have h12 : Commute (c₁ ^ k₁) (c₂ ^ k₂) := c12.zpow_zpow k₁ k₂
  have h123 : Commute (c₁ ^ k₁ * c₂ ^ k₂) (c₃ ^ k₃) :=
    (c13.zpow_zpow k₁ k₃).mul_left (c23.zpow_zpow k₂ k₃)
  rw [h123.mul_pow, h12.mul_pow, hpow c₁ k₁ he₁, hpow c₂ k₂ he₂, hpow c₃ k₃ he₃]
  simp

private theorem Aprime_coprime (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e) :
    Nat.Coprime (Nat.card ↥(pLayerOf 2 D.Ct ⊓ D.Act)) D.q := by
  have hexp := Aprime_exp D hs hu hA0
  have hepq : Nat.Coprime D.e D.q := by
    obtain ⟨k, -, hk⟩ := hs.q_pow
    rw [hk]
    exact (e_coprime D.ext3 hs).pow_right k
  refine Nat.coprime_of_dvd fun r hr hrA hrq => ?_
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrA
  have hxe : x ^ D.e = 1 := Subtype.ext (by simpa using hexp x x.2)
  have hre : r ∣ D.e := hx ▸ orderOf_dvd_of_pow_eq_one hxe
  have h1 : r ∣ Nat.gcd D.e D.q := Nat.dvd_gcd hre hrq
  rw [Nat.Coprime.gcd_eq_one hepq] at h1
  exact hr.one_lt.ne' (Nat.dvd_one.mp h1)

private def conjRep (I B : Subgroup G) (hB : ∀ i ∈ I, ∀ b ∈ B, i * b * i⁻¹ ∈ B) :
    ↥I →* MulAut ↥B where
  toFun i :=
    { toFun := fun b => ⟨(i : G) * b * (i : G)⁻¹, hB i i.2 b b.2⟩
      invFun := fun b => ⟨(i : G)⁻¹ * b * (i : G), by
        have h := hB ((i : G)⁻¹) (Subgroup.inv_mem _ i.2) b b.2
        simpa using h⟩
      left_inv := fun b => Subtype.ext (by
        show (i : G)⁻¹ * ((i : G) * b * (i : G)⁻¹) * (i : G) = b
        group)
      right_inv := fun b => Subtype.ext (by
        show (i : G) * ((i : G)⁻¹ * b * (i : G)) * (i : G)⁻¹ = b
        group)
      map_mul' := fun b c => Subtype.ext (by
        show (i : G) * ((b : G) * c) * (i : G)⁻¹ =
          ((i : G) * b * (i : G)⁻¹) * ((i : G) * c * (i : G)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show ((1 : ↥I) : G) * b * ((1 : ↥I) : G)⁻¹ = b
    simp)
  map_mul' := fun i j => MulEquiv.ext fun b => Subtype.ext (by
    show ((i * j : ↥I) : G) * b * ((i * j : ↥I) : G)⁻¹ =
      (i : G) * ((j : G) * b * (j : G)⁻¹) * (i : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

end CtA2a

theorem Aprime_centralizes_I {G : Type} [Group G] [Finite G] (D : SPLNot1 G)
    (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e) :
    ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a := by
  have _ := hK1
  intro a ha i hi
  by_cases hq : 9 ≤ D.q
  · obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, -, -, -, hgen⟩ := Aprime_gen D hs hu hA0
    have hAc : ∀ x y : ↥(pLayerOf 2 D.Ct ⊓ D.Act), x * y = y * x := fun x y =>
      Subtype.ext (Act_comm D hs x (Subgroup.mem_inf.mp x.2).2 y (Subgroup.mem_inf.mp y.2).2)
    have hAodd : Odd (Nat.card ↥(pLayerOf 2 D.Ct ⊓ D.Act)) :=
      Odd.of_dvd_nat (Act_odd D) (Subgroup.card_dvd_of_le inf_le_right)
    have hclos : Subgroup.closure
        ({⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨c₃, hc₃⟩} : Set ↥(pLayerOf 2 D.Ct ⊓ D.Act)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨k₁, k₂, k₃, hx⟩ := hgen x x.2
      have hx' : x = (⟨c₁, hc₁⟩ : ↥(pLayerOf 2 D.Ct ⊓ D.Act)) ^ k₁ *
          (⟨c₂, hc₂⟩ : ↥(pLayerOf 2 D.Ct ⊓ D.Act)) ^ k₂ *
          (⟨c₃, hc₃⟩ : ↥(pLayerOf 2 D.Ct ⊓ D.Act)) ^ k₃ :=
        Subtype.ext (by simpa using hx)
      rw [hx']
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _)
        (Subgroup.zpow_mem _ ?_ _)) (Subgroup.zpow_mem _ ?_ _)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hρ := L2_acts_trivially (I := ↥D.Ict) (A := ↥(pLayerOf 2 D.Ct ⊓ D.Act)) (q := D.q)
      (Ict_isL2 D hs) hq hs.odd_q hAc hAodd (Aprime_coprime D hs hu hA0)
      ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ ⟨c₃, hc₃⟩ hclos
      (conjRep D.Ict (pLayerOf 2 D.Ct ⊓ D.Act) fun j hj b hb => Aprime_norm D hs hj hb) ⟨i, hi⟩
    have h1 := congrArg Subtype.val
      (DFunLike.congr_fun hρ (⟨a, ha⟩ : ↥(pLayerOf 2 D.Ct ⊓ D.Act)))
    have h2 : i * a * i⁻¹ = a := h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · have hodd := hs.odd_q
    have hq5 := hs.q_ge
    have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hodd hq5
    have hde : D.d = D.e * 2 ^ (D.n - 1) := d_eq D.ext3 hs
    have heodd : Odd D.e := e_odd D.ext3 hs
    have hd8 : D.d ≤ 8 := by
      obtain ⟨m, hm⟩ := hodd
      unfold SPLNot0.d
      split_ifs <;> omega
    have hP : 4 ≤ 2 ^ (D.n - 1) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (D.n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have he1 : D.e = 1 := by
      obtain ⟨m, hm⟩ := heodd
      by_contra hne
      have hm1 : 1 ≤ m := by omega
      rw [hm] at hde
      nlinarith
    have hea := Aprime_exp D hs hu hA0 a ha
    rw [he1, pow_one] at hea
    rw [hea]
    simp

end CFSG.GH74.GLS.SP.Local
