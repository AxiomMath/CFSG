module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.C195
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_11bTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def C19_11aTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      (S : Subgroup G) ⊓ sec19Y K z ⊓ Subgroup.centralizer (W : Set G) ≤ W

@[expose] def C19_E2Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      ∀ j ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
        j * j = 1 → j = 1 ∨ j = z

@[expose] def IsDihedralSub {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ a b : G, 4 ≤ orderOf a ∧ Nat.card P = 2 * orderOf a ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧
    Subgroup.closure {a, b} = P

@[expose] def C19_6DihTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → ¬ IsDihedralSub ((S : Subgroup G) ⊓ sec19Y K z)

@[expose] def C19_16SNe9Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f ≠ 9 → (S : Subgroup G) ≤ sec19X K z

@[expose] def C19_16S9Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f = 9 → (S : Subgroup G) ≤ sec19X K z

variable {p f}

theorem c19_16STmp_of_split (hne : C19_16SNe9Tmp p f) (h9 : C19_16S9Tmp p f) :
    C19_16STmp p f := by
  intro G _ _ _ K z S W hd
  by_cases hq : p ^ f = 9
  · exact h9 G K z S W hd hq
  · exact hne G K z S W hd hq

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_inf_of_mem_cStar {K : Subgroup G} {S : Subgroup G} (hS : IsPGroup 2 S)
    {x : G} (hx : x ∈ cStar K) (hxS : x ∈ S) :
    x ∈ Subgroup.centralizer ((S ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hxN, h⟩ := mem_cStar_iff.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h1 := h ⟨r, hr.2⟩
  set y : K := (normalizerConj K ⟨x, hxN⟩ ⟨r, hr.2⟩)⁻¹ * ⟨r, hr.2⟩ with hy
  have hyS : (y : G) ∈ S := by
    rw [hy, Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe]
    exact S.mul_mem (S.inv_mem (S.mul_mem (S.mul_mem hxS hr.1) (S.inv_mem hxS))) hr.1
  have h2 : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) := (hS.to_le inf_le_left).comap_subtype
  have h3 : y ∈ (S ⊓ K).subgroupOf K ⊓ classicalInvolutionOddCore ↥K :=
    ⟨Subgroup.mem_subgroupOf.mpr ⟨hyS, y.2⟩, h1⟩
  rw [inf_oddCore_eq_bot h2, Subgroup.mem_bot, hy, inv_mul_eq_one] at h3
  have h4 : x * r * x⁻¹ = r := by
    simpa [normalizerConj_apply_coe] using congrArg Subtype.val h3
  calc r * x = (x * r * x⁻¹) * x := by rw [h4]
    _ = x * r := by group

variable [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W : Subgroup G}

theorem cStarTwoRankOne_of_c19_E2Tmp (hE : C19_E2Tmp p f) (hd : Sec19Data p f K z S W) :
    CStarTwoRankOne K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  intro a ha b hb ha2 hb2 hab
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := hNC ▸ cStar_le_normalizer K ha
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := hNC ▸ cStar_le_normalizer K hb
  have ha2' : a * a = 1 := by rw [← _root_.sq, ← ha2, pow_orderOf_eq_one]
  have hb2' : b * b = 1 := by rw [← _root_.sq, ← hb2, pow_orderOf_eq_one]
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    refine IsPGroup.iff_orderOf.mpr fun w => ?_
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_of_mem_sup hab w.2
    have hw2 : (w : G) ^ 2 = 1 := by
      rw [← hij, _root_.sq]
      have hc : Commute a b := hab
      calc a ^ i * b ^ j * (a ^ i * b ^ j) = (a ^ i * a ^ i) * (b ^ j * b ^ j) := by
            rw [mul_assoc, ← mul_assoc (b ^ j), ((hc.zpow_zpow i j).symm.eq), mul_assoc,
              mul_assoc]
        _ = 1 := by
            rw [← zpow_add, ← zpow_add, ← two_mul, ← two_mul, zpow_mul, zpow_mul, zpow_two,
              zpow_two, ha2', hb2', one_zpow, one_zpow, one_mul]
    have hdvd : orderOf w ∣ 2 ^ 1 := by
      rw [pow_one, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hw2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩
  have hEz : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr haC) (Subgroup.zpowers_le.mpr hbC)
  obtain ⟨c, hc, hcE⟩ := exists_conj_le_of_sylow_le S hd.hSz hEz hE2
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hc
  have hinv : ∀ x : G, x ∈ cStar K → orderOf x = 2 → x * x = 1 →
      c * x * c⁻¹ ∈ (S : Subgroup G) → c * x * c⁻¹ = z := by
    intro x hx hx2 hxx hcx
    have h1 := mem_centralizer_inf_of_mem_cStar S.isPGroup' (conj_mem_cStar hcN hx) hcx
    have h2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
      calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    refine (hE G K z S W hd _ ⟨hcx, h1⟩ h2).resolve_left fun h3 => ?_
    have : x = 1 := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = 1 := by rw [h3]; group
    rw [this, orderOf_one] at hx2
    omega
  have h1 := hinv a ha ha2 ha2'
    (hcE (conj_mem_conjSub (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))))
  have h2 := hinv b hb hb2 hb2'
    (hcE (conj_mem_conjSub (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))))
  calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
    _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [h1, h2]
    _ = b := by group

theorem c19_E2Tmp_of_c19_12Tmp (h6 : C19_6Tmp p f) (h14 : C19_14Tmp p f)
    (h12 : C19_12Tmp p f) : C19_E2Tmp p f := by
  intro G _ _ _ K z S W hd j hj hjj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := (h6 G K z S W hd).resolve_left (h14 G K z S W hd)
  have hCR := (h12 G K z S W hd hQ).2
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨Q₀, hQ₀⟩ := hd.sylow
  have hzR : z ∈ (S : Subgroup G) := hQ₀ (mem_of_uniqueInvolution_of_pGroup hI
    (Subgroup.map_subtype_le _) (Q₀.isPGroup'.map _)
    (by have := (exists_ne_comm_of_mem_rSet hd.tight.branch.odd hd.tight.branch.five
      hd.tight.branch.member (R := (Q₀ : Subgroup K).map K.subtype)
      ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩).2; omega))
  have hzC : z ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      ((normalizer_eq_centralizer_of_tight hd.tight.toTightBranch) ▸
        (Subgroup.le_normalizer hr.2 : r ∈ Subgroup.normalizer (K : Set G)))
    exact h1
  rw [← hCR] at hj
  have hz : z ∈ (S : Subgroup G) ⊓ sec19Y K z := hCR ▸ ⟨hzR, hzC⟩
  by_cases hj1 : j = 1
  · exact Or.inl hj1
  · exact Or.inr (IsQuaternionSub.eq_of_mul_self_eq_one hQ hj hz hjj hI.sq hj1 hI.ne_one)

end CFSG.ClassicalInvolution.Disconnected.AschTight
