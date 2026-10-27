module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Pre
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Nine81

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_mulAut_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q]
    (hQ : IsPGroup 2 Q) : IsPGroup 2 (MulAut Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have e := IsCyclic.mulAutMulEquiv (G := Q)
  rw [hn] at e
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rcases n with _ | n
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n)]
      simp
  exact (IsPGroup.of_card hcard).of_equiv e.symm

omit [Finite G] in
theorem conj_zpow_of_inv {p b : G} (hrel : b * p * b⁻¹ = p⁻¹) (k : ℤ) :
    b * p ^ k * b⁻¹ = (p ^ k)⁻¹ := by
  rw [← conj_zpow, hrel, inv_zpow]

structure DihData (P : Subgroup G) (p b : G) : Prop where
  hp : p ∈ P
  hb : b ∈ P
  hcard : 2 * orderOf p = Nat.card P
  hbp : b ∉ zpowers p
  hb2 : b * b = 1
  hrel : b * p * b⁻¹ = p⁻¹
  hp4 : 4 ≤ orderOf p
  hpow : ∃ n : ℕ, orderOf p = 2 ^ n

namespace DihData

variable {P : Subgroup G} {p b : G} (D : DihData P p b)
include D

omit [Finite G] in
theorem zpowers_le : zpowers p ≤ P := zpowers_le_of_mem D.hp

theorem index_eq : ((zpowers p).subgroupOf P).index = 2 := by
  have h1 := relIndex_mul_card (H := zpowers p) (K := P)
  rw [inf_eq_left.mpr D.zpowers_le, Nat.card_zpowers, ← D.hcard] at h1
  have hpos : 0 < orderOf p := orderOf_pos p
  have : (zpowers p).relIndex P * orderOf p = 2 * orderOf p := h1
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem inv_mul_mem {σ : G} (hσ : σ ∈ P) (hσp : σ ∉ zpowers p) : b⁻¹ * σ ∈ zpowers p := by
  have h := (Subgroup.mul_mem_iff_of_index_two D.index_eq (a := ⟨b⁻¹, inv_mem D.hb⟩)
    (b := ⟨σ, hσ⟩)).mpr (by
      constructor
      · intro h
        exfalso
        apply D.hbp
        have := inv_mem (mem_subgroupOf.mp h)
        simpa using this
      · intro h
        exact absurd (mem_subgroupOf.mp h) hσp)
  exact mem_subgroupOf.mp h

theorem of_not_mem {σ : G} (hσ : σ ∈ P) (hσp : σ ∉ zpowers p) :
    σ * σ = 1 ∧ ∀ x ∈ zpowers p, σ * x * σ⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (D.inv_mul_mem hσ hσp)
  have hσe : σ = b * p ^ k := by rw [hk]; group
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right D.hb2
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hσe, show b * p ^ k * (b * p ^ k) = (b * p ^ k * b⁻¹) * p ^ k by
      rw [hbinv, ← mul_assoc],
      conj_zpow_of_inv D.hrel k, inv_mul_cancel]
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    rw [hσe, show b * p ^ k * p ^ m * (b * p ^ k)⁻¹ = b * p ^ m * b⁻¹ by
      rw [mul_inv_rev, ← mul_assoc, mul_assoc (b * p ^ k), ← zpow_neg, mul_assoc b,
        ← zpow_add, ← zpow_add]
      congr 2
      ring_nf, conj_zpow_of_inv D.hrel m]

theorem four_le_card {Q₀ : Subgroup G} (hQ₀ : Q₀ ≤ zpowers p)
    (hQa : ¬ Q₀ ≤ zpowers (p ^ (orderOf p / 2))) : 4 ≤ Nat.card Q₀ := by
  obtain ⟨n, hn⟩ := D.hpow
  have hcyc : IsCyclic (zpowers p) := inferInstance
  have hdvd : Nat.card Q₀ ∣ 2 ^ n := by
    rw [← hn, ← Nat.card_zpowers]
    exact card_dvd_of_le hQ₀
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hlt
  push Not at hlt
  have hj1 : j ≤ 1 := by
    by_contra h
    push Not at h
    have : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega
  apply hQa
  have h2 : 2 ∣ orderOf p := by
    rw [hn]
    refine dvd_pow_self 2 ?_
    rintro rfl
    have h4 := D.hp4
    rw [hn] at h4
    norm_num at h4
  have hord : orderOf (p ^ (orderOf p / 2)) = 2 :=
    orderOf_pow_orderOf_div (by have := D.hp4; omega) h2
  have haP : p ^ (orderOf p / 2) ∈ zpowers p := pow_mem (mem_zpowers p) _
  have hle : Q₀.subgroupOf (zpowers p) ≤ (zpowers (p ^ (orderOf p / 2))).subgroupOf
      (zpowers p) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (zpowers_le_of_mem haP)).toEquiv, Nat.card_zpowers,
      hord, hj]
    interval_cases j <;> norm_num
  intro x hx
  have := hle (show (⟨x, hQ₀ hx⟩ : ↥(zpowers p)) ∈ Q₀.subgroupOf (zpowers p) from hx)
  exact mem_subgroupOf.mp this

theorem comm_of_odd_of_le {Q : Subgroup G} (hQP : Q ≤ P) {y : G}
    (hy : y ∈ normalizer (Q : Set G)) (ho : Odd (orderOf y))
    (hya : y * p ^ (orderOf p / 2) = p ^ (orderOf p / 2) * y) {x : G} (hx : x ∈ Q) :
    y * x * y⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := D.hpow
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := n + 1) (by rw [← D.hcard, hn, pow_succ]; ring)
  have hQ2 : IsPGroup 2 Q := hP2.to_le hQP
  set a := p ^ (orderOf p / 2) with ha
  have h2 : 2 ∣ orderOf p := by
    rw [hn]
    refine dvd_pow_self 2 ?_
    rintro rfl
    have h4 := D.hp4
    rw [hn] at h4
    norm_num at h4
  have hord : orderOf a = 2 := orderOf_pow_orderOf_div (by have := D.hp4; omega) h2
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at hord; norm_num at hord
  have haa : a * a = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have haP : a ∈ zpowers p := pow_mem (mem_zpowers p) _
  by_cases hQp : Q ≤ zpowers p
  ·
    have : IsCyclic Q := Subgroup.isCyclic_of_le hQp
    exact Eight2.comm_of_odd_of_isPGroup_mulAut (isPGroup_mulAut_of_isCyclic hQ2) hy ho hx
  · rw [IsConcreteLE.not_le_iff_exists] at hQp
    obtain ⟨σ, hσQ, hσp⟩ := hQp
    obtain ⟨hσσ, hσinv⟩ := D.of_not_mem (hQP hσQ) hσp
    have hcoset : ∀ w ∈ Q, w ∉ zpowers p → σ⁻¹ * w ∈ Q ⊓ zpowers p := by
      intro w hw hwp
      refine mem_inf.mpr ⟨mul_mem (inv_mem hσQ) hw, ?_⟩
      have h1 := D.inv_mul_mem (hQP hσQ) hσp
      have h2' := D.inv_mul_mem (hQP hw) hwp
      have := mul_mem (inv_mem h1) h2'
      rwa [show (b⁻¹ * σ)⁻¹ * (b⁻¹ * w) = σ⁻¹ * w by group] at this
    by_cases hQa : Q ⊓ zpowers p ≤ zpowers a
    ·
      have hQ0 : ∀ w ∈ Q ⊓ zpowers p, w = 1 ∨ w = a := fun w hw =>
        Eight2.eq_one_or_of_mem_zpowers_sq haa (hQa hw)
      have hyσQ : y * σ * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hy σ).mp hσQ
      have hyσ : y * σ * y⁻¹ = σ ∨ y * σ * y⁻¹ = σ * a := by
        by_cases hp' : y * σ * y⁻¹ ∈ zpowers p
        · exfalso
          rcases hQ0 _ (mem_inf.mpr ⟨hyσQ, hp'⟩) with h | h
          · apply hσp
            have : σ = 1 := by
              calc σ = y⁻¹ * (y * σ * y⁻¹) * y := by group
                _ = 1 := by rw [h]; group
            rw [this]
            exact one_mem _
          · apply hσp
            have : σ = a := by
              calc σ = y⁻¹ * (y * σ * y⁻¹) * y := by group
                _ = y⁻¹ * (a * y) := by rw [h, mul_assoc]
                _ = y⁻¹ * (y * a) := by rw [hya]
                _ = a := by group
            rw [this]
            exact haP
        · rcases hQ0 _ (hcoset _ hyσQ hp') with h | h
          · left
            calc y * σ * y⁻¹ = σ * (σ⁻¹ * (y * σ * y⁻¹)) := by group
              _ = σ := by rw [h, mul_one]
          · right
            calc y * σ * y⁻¹ = σ * (σ⁻¹ * (y * σ * y⁻¹)) := by group
              _ = σ * a := by rw [h]
      have hfix : y * σ * y⁻¹ = σ := by
        rcases hyσ with h | h
        · exact h
        · exfalso
          have hstep : ∀ m : ℕ, y ^ (2 * m + 1) * σ * (y ^ (2 * m + 1))⁻¹ = σ * a := by
            intro m
            induction m with
            | zero => simpa using h
            | succ m ih =>
              have hya' : y * a * y⁻¹ = a := by rw [hya]; group
              calc y ^ (2 * (m + 1) + 1) * σ * (y ^ (2 * (m + 1) + 1))⁻¹ =
                  y * (y * (y ^ (2 * m + 1) * σ * (y ^ (2 * m + 1))⁻¹) * y⁻¹) * y⁻¹ := by
                    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, pow_succ, pow_succ]
                    group
                _ = σ * a := by
                    rw [ih, show y * (σ * a) * y⁻¹ = (y * σ * y⁻¹) * (y * a * y⁻¹) by group,
                      h, hya', mul_assoc σ a a, haa, mul_one, h]
          obtain ⟨m, hm⟩ := ho
          have h1 := hstep m
          rw [← hm, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
          apply ha1
          calc a = σ⁻¹ * (σ * a) := by group
            _ = 1 := by rw [← h1, inv_mul_cancel]
      by_cases hxp : x ∈ zpowers p
      · rcases hQ0 _ (mem_inf.mpr ⟨hx, hxp⟩) with h | h
        · rw [h, mul_one, mul_inv_cancel]
        · rw [h, hya]; group
      · rcases hQ0 _ (hcoset _ hx hxp) with h | h
        · have hxe : x = σ := by
            calc x = σ * (σ⁻¹ * x) := by group
              _ = σ := by rw [h, mul_one]
          rw [hxe, hfix]
        · have hxe : x = σ * a := by
            calc x = σ * (σ⁻¹ * x) := by group
              _ = σ * a := by rw [h]
          rw [hxe, show y * (σ * a) * y⁻¹ = (y * σ * y⁻¹) * (y * a * y⁻¹) by group, hfix,
            show y * a * y⁻¹ = a by rw [hya]; group]
    ·
      have h4 := D.four_le_card inf_le_right hQa
      have hcyc : IsCyclic ↥(Q ⊓ zpowers p) := Subgroup.isCyclic_of_le inf_le_right
      obtain ⟨ρ₀, hρ₀⟩ := IsCyclic.exists_generator (α := ↥(Q ⊓ zpowers p))
      have hρQ : (ρ₀ : G) ∈ Q := (mem_inf.mp ρ₀.2).1
      have hρp : (ρ₀ : G) ∈ zpowers p := (mem_inf.mp ρ₀.2).2
      set ρ : ↥Q := ⟨ρ₀, hρQ⟩ with hρ
      set σ' : ↥Q := ⟨σ, hσQ⟩ with hσ'
      have hgenQ0 : ∀ w ∈ Q ⊓ zpowers p, ∃ k : ℤ, w = (ρ₀ : G) ^ k := by
        intro w hw
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hρ₀ ⟨w, hw⟩)
        exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩
      have hgen : (⊤ : Subgroup ↥Q) = zpowers ρ ⊔ zpowers σ' := by
        refine (eq_top_iff.mpr fun w _ => ?_).symm
        by_cases hwp : (w : G) ∈ zpowers p
        · obtain ⟨k, hk⟩ := hgenQ0 _ (mem_inf.mpr ⟨w.2, hwp⟩)
          refine mem_sup_left (mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩)
          simp [hρ, hk]
        · obtain ⟨k, hk⟩ := hgenQ0 _ (hcoset _ w.2 hwp)
          have : w = σ' * ρ ^ k := Subtype.ext (by
            simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hσ', hρ, ← hk]
            group)
          rw [this]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (zpow_mem (mem_zpowers _) k))
      have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simp [hσ', pow_two, hσσ])
      have hrel : σ' * ρ * σ'⁻¹ = ρ⁻¹ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ', hρ]
        exact hσinv _ hρp)
      have hσρ : σ' ∉ zpowers ρ := by
        intro h
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
        apply hσp
        have : σ = (ρ₀ : G) ^ k := by simpa [hσ', hρ] using (congrArg Subtype.val hk).symm
        rw [this]
        exact zpow_mem hρp k
      obtain ⟨e⟩ := GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ' hgen hσ2 hrel hσρ
      have hoρ : orderOf ρ = Nat.card ↥(Q ⊓ zpowers p) := by
        rw [hρ, Subgroup.orderOf_mk, Subgroup.orderOf_coe ρ₀,
          orderOf_eq_card_of_forall_mem_zpowers hρ₀]
      obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.card ↥(Q ⊓ zpowers p) = 2 ^ j :=
        (hQ2.to_le inf_le_left).exists_card_eq
      have hj2 : 2 ≤ j := by
        by_contra hlt
        push Not at hlt
        interval_cases j <;> omega
      rw [hoρ, hj] at e
      exact Eight2.comm_of_odd_of_isPGroup_mulAut
        ((GorensteinWalter.dihedral_mulAut_is_twoGroup hj2).of_equiv (MulAut.congr e.symm))
        hy ho hx

end DihData

theorem hasNormalPComplement_of_dihedral {P : Subgroup G} {p b : G} (D : DihData P p b)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = P)
    (ha : ∀ x : G, x * p ^ (orderOf p / 2) = p ^ (orderOf p / 2) * x) :
    HasNormalPComplement 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ
  obtain ⟨S, hSP⟩ := hS
  have hS' : ∃ P₀ : Sylow 2 ↥(⊤ : Subgroup G), (P₀ : Subgroup _) = P.subgroupOf ⊤ :=
    ⟨S.subtype le_top, by rw [Sylow.coe_subtype, hSP]⟩
  obtain ⟨g, -, hgQ⟩ := exists_conjugate_le_of_sylow hS' le_top hQ
  intro m
  induction m using QuotientGroup.induction_on with
  | H m =>
    obtain ⟨k, o, hodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    set y : G := ((m ^ 2 ^ k : ↥(normalizer (Q : Set G))) : G) with hy
    have hyN : y ∈ normalizer (Q : Set G) := (m ^ 2 ^ k).2
    have hyo : Odd (orderOf y) := by
      have h1 : orderOf (m ^ 2 ^ k) ∣ o := orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, ← hord, pow_orderOf_eq_one])
      rw [hy, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hodd h1
    have hy'N : g⁻¹ * y * g ∈ normalizer ((conjugate Q g : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      rw [mem_conjugate_iff, mem_conjugate_iff,
        show g * (g⁻¹ * y * g * x * (g⁻¹ * y * g)⁻¹) * g⁻¹ = y * (g * x * g⁻¹) * y⁻¹ by group]
      exact mem_normalizer_iff.mp hyN _
    have hy'o : Odd (orderOf (g⁻¹ * y * g)) := by
      rwa [← SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * y = g⁻¹ * y * g * g⁻¹ by group)]
    have hc := fun x hx => D.comm_of_odd_of_le hgQ hy'N hy'o (ha _) (x := x) hx
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : g⁻¹ * q * g ∈ conjugate Q g := by
      rw [mem_conjugate_iff, show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
      exact hq
    have h1 := hc _ hq'
    have h2 : y * q * y⁻¹ = q := by
      calc y * q * y⁻¹ = g * ((g⁻¹ * y * g) * (g⁻¹ * q * g) * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
        _ = q := by rw [h1]; group
    calc q * y = y * (y⁻¹ * q * y) := by group
      _ = y * q := by
        congr 1
        calc y⁻¹ * q * y = y⁻¹ * (y * q * y⁻¹) * y := by rw [h2]
          _ = q := by group

end Nine81

end CFSG.ComponentClassification.GSThmB
