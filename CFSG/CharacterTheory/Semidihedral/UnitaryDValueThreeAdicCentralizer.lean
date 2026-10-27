module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicFusion

public section

namespace CFSG.Semidihedral.UnitaryDValue

theorem centralizer_zpowers_eq {G : Type*} [Group G] (v : G) :
    Subgroup.centralizer (Subgroup.zpowers v : Set G) = Subgroup.centralizer {v} := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h v (Subgroup.mem_zpowers v)).symm
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (h.symm : Commute v x) n)).eq

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

abbrev CQ (v : G) : Subgroup G := D.QT ⊓ Subgroup.centralizer {v}

theorem isPGroup_CQ (v : G) : IsPGroup 3 (D.CQ v) :=
  D.isPGroup_QT.to_le inf_le_left

theorem mem_CQ_self {v : G} (hv : v ∈ D.QT) : v ∈ D.CQ v :=
  ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem mul_inv_or_mul_mem_P {s v : G} (hs : s ∈ D.QT) (hsP : s ∉ D.primaryPart 3)
    (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    s * v⁻¹ ∈ D.primaryPart 3 ∨ s * v ∈ D.primaryPart 3 := by
  obtain ⟨p₁, hp₁, a, ha, rfl⟩ := D.exists_of_mem_QT_not_mem_P hs hsP
  obtain ⟨p₂, hp₂, b, hb, rfl⟩ := D.exists_of_mem_QT_not_mem_P hv hvP
  have key : (3 : ℤ) ∣ a - b ∨ (3 : ℤ) ∣ a + b := by
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  rcases key with h | h
  · left
    have e : p₁ * D.tThree ^ a * (p₂ * D.tThree ^ b)⁻¹ =
        p₁ * (D.tThree ^ (a - b) * p₂⁻¹ * (D.tThree ^ (a - b))⁻¹) * D.tThree ^ (a - b) := by
      rw [zpow_sub]
      group
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem hp₁
      (D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T _)
        ((D.primaryPart 3).inv_mem hp₂))) (D.tThree_zpow_mem_P3 h)
  · right
    have e : p₁ * D.tThree ^ a * (p₂ * D.tThree ^ b) =
        p₁ * (D.tThree ^ a * p₂ * (D.tThree ^ a)⁻¹) * D.tThree ^ (a + b) := by
      rw [zpow_add]
      group
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem hp₁
      (D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T _) hp₂))
      (D.tThree_zpow_mem_P3 h)

namespace Exceptional

variable {D} (E : D.Exceptional)

theorem Z_le_CQ {v : G} (hv : v ∈ D.QT) : E.Z ≤ D.CQ v := by
  intro z hz
  refine ⟨D.P_le_QT (E.Z_le_P hz), ?_⟩
  show z ∈ Subgroup.centralizer {v}
  exact Subgroup.mem_centralizer_singleton_iff.mpr (E.Z_comm_QT hz hv).symm

theorem exists_of_mem_CQ {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) {s : G}
    (hs : s ∈ D.CQ v) : ∃ j : ℤ, ∃ z ∈ E.Z, s = v ^ j * z := by
  have hsv : s * v = v * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
  have hZ : ∀ p ∈ D.primaryPart 3, p * v = v * p → p ∈ E.Z := fun p hp hpv =>
    (E.conj_fix_iff hv hvP hp).mp (conj_eq_of_comm hpv.symm)
  have hc : Commute s v := hsv
  by_cases hsP : s ∈ D.primaryPart 3
  · exact ⟨0, s, hZ s hsP hsv, by rw [zpow_zero, one_mul]⟩
  · rcases D.mul_inv_or_mul_mem_P hs.1 hsP hv hvP with h | h
    · refine ⟨1, s * v⁻¹, hZ _ h (hc.mul_left (Commute.refl v).inv_left).eq, ?_⟩
      rw [zpow_one, ← mul_assoc, ← hsv, mul_inv_cancel_right]
    · refine ⟨-1, s * v, hZ _ h (hc.mul_left (Commute.refl v)).eq, ?_⟩
      rw [zpow_neg_one, hsv, ← mul_assoc, inv_mul_cancel, one_mul]

include E in
theorem CQ_comm {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) {a b : G}
    (ha : a ∈ D.CQ v) (hb : b ∈ D.CQ v) : a * b = b * a := by
  obtain ⟨i, z, hz, rfl⟩ := E.exists_of_mem_CQ hv hvP ha
  obtain ⟨j, w, hw, rfl⟩ := E.exists_of_mem_CQ hv hvP hb
  have hvz : Commute v z := (E.Z_comm_QT hz hv)
  have hvw : Commute v w := (E.Z_comm_QT hw hv)
  have hzw : Commute z w := D.C_comm z (E.Z_le_C hz) w (E.Z_le_C hw)
  have h1 : Commute (v ^ i * z) (v ^ j * w) :=
    ((Commute.zpow_zpow_self v i j).mul_right (hvw.zpow_left i)).mul_left
      ((hvz.zpow_left j).symm.mul_right hzw)
  exact h1.eq

theorem le_factorization_card_CQ {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    ∃ a : ℕ, Nat.card (D.CQ v) = 3 ^ a ∧ E.h ≤ a := by
  obtain ⟨a, ha⟩ := (D.isPGroup_CQ v).exists_card_eq
  refine ⟨a, ha, ?_⟩
  have h1 : Nat.card E.Z ∣ Nat.card (D.CQ v) := Subgroup.card_dvd_of_le (E.Z_le_CQ hv)
  rw [E.card_Z, ha] at h1
  have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hne : E.h - 1 ≠ a := by
    intro heq
    apply hvP
    have hcard : Nat.card (D.CQ v) ≤ Nat.card E.Z := by rw [ha, E.card_Z, heq]
    have := Subgroup.eq_of_le_of_card_ge (E.Z_le_CQ hv) hcard
    exact E.Z_le_P (this ▸ D.mem_CQ_self hv)
  have := E.three_le_h
  omega

theorem factorization_card_centralizer (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT)
    (hvP : v ∉ D.primaryPart 3) :
    (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h := by
  have hpos : Nat.card (Subgroup.centralizer ({v} : Set G)) ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 (Subgroup.centralizer ({v} : Set G))))
    set S' : Subgroup G := (S : Subgroup _).map (Subgroup.centralizer ({v} : Set G)).subtype
    have hS'card :
        Nat.card S' = 3 ^ (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective, Sylow.card_eq_multiplicity]
    have hS'p : IsPGroup 3 S' := S.isPGroup'.map _
    obtain ⟨R, hR⟩ := hS'p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R (D.sylowQT E.three_dvd_q)
    set R' : Subgroup G := S'.map (MulAut.conj g).toMonoidHom
    have hR'Q : R' ≤ D.QT := by
      rintro _ ⟨s, hs, rfl⟩
      rw [← D.coe_sylowQT E.three_dvd_q, ← hg, Sylow.coe_subgroup_smul]
      exact ⟨s, hR hs, rfl⟩
    have hR'card : Nat.card R' = Nat.card S' :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hidx : (D.primaryPart 3).relIndex R' ≤ 3 := by
      have h1 : (D.primaryPart 3).relIndex D.QT = 3 := by
        have h2 := Subgroup.card_mul_index ((D.primaryPart 3).subgroupOf D.QT)
        rw [card_subgroupOf_of_le' D.P_le_QT, E.card_P_eq, E.card_QT_eq] at h2
        rw [Subgroup.relIndex]
        rw [pow_succ] at h2
        rw [show E.h + 2 = (E.h + 1) + 1 by omega, pow_succ] at h2
        have := Nat.eq_of_mul_eq_mul_left (by positivity) h2
        omega
      exact (Subgroup.relIndex_le_of_le_right hR'Q (by rw [h1]; norm_num)).trans h1.le
    have hmul := Subgroup.card_mul_index ((D.primaryPart 3).subgroupOf R')
    rw [← Subgroup.relIndex] at hmul
    obtain ⟨w, hwR, hwP, hwZ⟩ : ∃ w ∈ R', w ∈ D.primaryPart 3 ∧ w ∉ E.Z := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hle : Nat.card ((D.primaryPart 3).subgroupOf R') ≤ Nat.card E.Z := by
        refine Nat.card_le_card_of_injective (fun x => ⟨(x : R'), hcon _ (x : R').2 x.2⟩) ?_
        intro x y hxy
        have h := congrArg Subtype.val hxy
        simp only at h
        exact Subtype.ext (Subtype.ext h)
      rw [E.card_Z] at hle
      have h3 : Nat.card R' ≤ 3 ^ (E.h - 1) * 3 := by
        rw [← hmul]
        exact Nat.mul_le_mul hle hidx
      rw [hR'card, hS'card] at h3
      have h4 : 3 ^ (E.h + 1) ≤
          3 ^ (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) hlt
      have h5 : 3 ^ (E.h - 1) * 3 < 3 ^ (E.h + 1) := by
        rw [← pow_succ]
        exact Nat.pow_lt_pow_right (by norm_num) (by have := E.three_le_h; omega)
      omega
    have hgv : g * v * g⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := by
      obtain ⟨s, hsS', hsw⟩ := hwR
      obtain ⟨s', -, hs's⟩ := hsS'
      have hsv : s * v = v * s := by
        rw [← hs's]
        exact Subgroup.mem_centralizer_singleton_iff.mp s'.2
      have hw : w = g * s * g⁻¹ := by rw [← hsw]; rfl
      rw [Subgroup.mem_centralizer_singleton_iff, hw]
      calc g * v * g⁻¹ * (g * s * g⁻¹) = g * (v * s) * g⁻¹ := by group
        _ = g * (s * v) * g⁻¹ := by rw [hsv]
        _ = g * s * g⁻¹ * (g * v * g⁻¹) := by group
    obtain ⟨Rw, hRw⟩ := E.exists_sylow_le_QT hwP
    obtain ⟨k, hk⟩ := D.three_element_of_mem_QT hv
    have hp : IsPGroup 3 (Subgroup.zpowers
        (⟨g * v * g⁻¹, hgv⟩ : Subgroup.centralizer ({w} : Set G))) := by
      apply IsPGroup.of_card (n := k)
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_conj_eq, hk]
    obtain ⟨R₁, hR₁⟩ := hp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Subgroup.centralizer ({w} : Set G)) R₁ Rw
    have hmem : (⟨g * v * g⁻¹, hgv⟩ : Subgroup.centralizer ({w} : Set G)) ∈
        (R₁ : Subgroup _) := hR₁ (Subgroup.mem_zpowers _)
    have h2 : c * ⟨g * v * g⁻¹, hgv⟩ * c⁻¹ ∈ (Rw : Subgroup _) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨_, hmem, rfl⟩
    have h3 := hRw _ h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    have hcw : (c : G) * (g * v * g⁻¹) * (c : G)⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hgv) (Subgroup.inv_mem _ c.2)
    have h4 : (c : G) * (g * v * g⁻¹) * (c : G)⁻¹ ∈ D.primaryPart 3 := by
      by_contra hnot
      apply hwZ
      refine (E.conj_fix_iff h3 hnot hwP).mp ?_
      exact conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hcw)
    apply E.not_conj_mem_P hgw hv hvP (g := (c : G) * g)
    have e : (c : G) * g * v * ((c : G) * g)⁻¹ = (c : G) * (g * v * g⁻¹) * (c : G)⁻¹ := by group
    rw [e]
    exact h4
  · obtain ⟨a, ha, hla⟩ := E.le_factorization_card_CQ hv hvP
    have h1 : Nat.card (D.CQ v) ∣ Nat.card (Subgroup.centralizer ({v} : Set G)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [ha] at h1
    exact hla.trans ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).mp h1)

theorem card_CQ (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    Nat.card (D.CQ v) = 3 ^ E.h := by
  obtain ⟨a, ha, hla⟩ := E.le_factorization_card_CQ hv hvP
  have h1 : Nat.card (D.CQ v) ∣ Nat.card (Subgroup.centralizer ({v} : Set G)) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [ha] at h1
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h1
  rw [E.factorization_card_centralizer hgw hv hvP] at h2
  rw [ha, le_antisymm h2 hla]

theorem u₀_pow_three_ne_one : E.u₀ ^ 3 ≠ 1 := by
  intro h
  apply E.u₀_cube_inv_ne
  rw [h, inv_one]

include E in
theorem comm_of_normalizes_CQ (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT)
    (hvP : v ∉ D.primaryPart 3) {n : G} (hnv : n * v = v * n)
    (hn : ∀ c ∈ D.CQ v, n * c * n⁻¹ ∈ D.CQ v) {s : G} (hs : s ∈ D.CQ v) : n * s = s * n := by
  have hnZ : ∀ z ∈ E.Z, n * z * n⁻¹ ∈ E.Z := by
    intro z hz
    have h1 := hn z (E.Z_le_CQ hv hz)
    have h2 : n * z * n⁻¹ ∈ D.primaryPart 3 := by
      by_contra hnot
      apply E.not_conj_mem_P hgw h1.1 hnot (g := n⁻¹)
      have e : n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z := by group
      rw [e]
      exact E.Z_le_P hz
    refine (E.conj_fix_iff hv hvP h2).mp ?_
    have h3 := Subgroup.mem_centralizer_singleton_iff.mp h1.2
    exact conj_eq_of_comm h3.symm
  have hnN : n ∈ Subgroup.normalizer (E.Z : Set G) :=
    mem_normalizer_of_conj_mem_of_finite hnZ
  have htZ : ∀ u ∈ Subgroup.zpowers (E.u₀ ^ 3), D.t * u * D.t⁻¹ ∈ Subgroup.zpowers (E.u₀ ^ 3) :=
    fun u hu => by rw [E.t_conj_Z hu]; exact hu
  have hodd : Odd (orderOf n) := by
    have h1 : n ∈ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hnv
    have h2 : orderOf n ∣ Nat.card (Subgroup.centralizer ({v} : Set G)) := by
      rw [← Subgroup.orderOf_mk n h1]
      exact orderOf_dvd_natCard _
    exact (E.odd_card_centralizer hgw hv hvP).of_dvd_nat h2
  have hcentZ : ∀ z ∈ E.Z, n * z * n⁻¹ = z := by
    rcases D.normalizer_conj_of_le_W (E.Z_le_W E.u₀_cube_mem_Z) E.u₀_pow_three_ne_one htZ
      hnN with h | h
    · exact h
    · exfalso
      have heven := even_orderOf_of_conj_eq_inv (h _ E.u₀_cube_mem_Z) (by
        intro h2
        apply E.u₀_cube_inv_ne
        rw [pow_two] at h2
        exact (eq_inv_of_mul_eq_one_left h2).symm)
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨j, z, hz, rfl⟩ := E.exists_of_mem_CQ hv hvP hs
  have h1 : Commute n (v ^ j) := (Commute.zpow_right (hnv : Commute n v) j)
  have h2 : Commute n z := comm_of_conj_eq (hcentZ z hz)
  exact (h1.mul_right h2).eq

include E in
theorem hasNormalPComplement_centralizer (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT)
    (hvP : v ∉ D.primaryPart 3) :
    CFSG.HasNormalPComplement 3 (Subgroup.centralizer (Subgroup.zpowers v : Set G)) := by
  set K := Subgroup.centralizer (Subgroup.zpowers v : Set G) with hK
  have hKv : K = Subgroup.centralizer {v} := centralizer_zpowers_eq v
  have hCQK : D.CQ v ≤ K := hKv ▸ inf_le_right
  have hcard : Nat.card ((D.CQ v).subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [card_subgroupOf_of_le' hCQK, E.card_CQ hgw hv hvP, hKv,
      E.factorization_card_centralizer hgw hv hvP]
  let S : Sylow 3 K := Sylow.ofCard _ hcard
  apply CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 3 S
  intro s hs
  refine ⟨Subgroup.le_normalizer hs, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro n hn
  have hsCQ : (s : G) ∈ D.CQ v := hs
  have hnv : (n : G) * v = v * n :=
    (Subgroup.mem_centralizer_iff.mp n.2 v (Subgroup.mem_zpowers v)).symm
  have hnCQ : ∀ c ∈ D.CQ v, (n : G) * c * (n : G)⁻¹ ∈ D.CQ v := by
    intro c hc
    have h1 : (⟨c, hCQK hc⟩ : K) ∈ (S : Subgroup K) := hc
    have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    exact h2
  have := E.comm_of_normalizes_CQ hgw hv hvP hnv hnCQ hsCQ
  exact Subtype.ext this

end Exceptional

end DValueData

end CFSG.Semidihedral.UnitaryDValue
