module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Bar
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Omega
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartI
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Norm

theorem zmod3_aux : ∀ u v : ZMod 3, u * v - 1 = 0 → u + v * v = 0 → u = 2 ∧ v = 2 := by decide

theorem zmod3_aux2 : ((2 : ZMod 3) + 1) = 0 := by decide

variable {Ω : Type*} [Group Ω]

theorem norm_triple_trivial [Finite Ω] {V : Subgroup Ω} (hV : IsElemAbelian 3 V)
    (hVcard : Nat.card V ≤ 9) {φ : Ω ≃* Ω} {a b d : Ω} (ha : a ∈ V) (hb : b ∈ V) (hd : d ∈ V)
    (hab : φ a = b) (hbd : φ b = d) (hda : φ d = a) : a * b * d = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hV hx hy
  have hcube : ∀ x ∈ V, x ^ 3 = 1 := hV.2
  by_cases ha1 : a = 1
  · have hb1 : b = 1 := by rw [← hab, ha1, map_one]
    have hd1 : d = 1 := by rw [← hbd, hb1, map_one]
    rw [ha1, hb1, hd1]; simp
  by_cases hab' : a = b
  · have hbd' : b = d := by rw [← hbd, ← hab', hab, hab']
    rw [← hbd', ← hab']
    calc a * a * a = a ^ 3 := (pow_three' a).symm
      _ = 1 := hcube a ha
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    apply φ.injective
    rw [hab, h, map_one]
  have hord : ∀ x ∈ V, x ≠ 1 → orderOf x = 3 := fun x hx hx1 => orderOf_eq_prime (hcube x hx) hx1
  have hoa : orderOf a = 3 := hord a ha ha1
  have hob : orderOf b = 3 := hord b hb hb1
  have hbP : b ∉ Subgroup.zpowers a := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hmod : a ^ (k % 3) = b := by
      rw [← hk]
      have := zpow_mod_orderOf a k
      rw [hoa] at this
      exact_mod_cast this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0] at hmod; simp at hmod; exact hb1 hmod.symm
    · rw [h1] at hmod; simp at hmod; exact hab' hmod
    · rw [h2] at hmod
      have hb2 : b = a * a := by rw [← hmod, zpow_two]
      have hd2 : d = a := by
        rw [← hbd, hb2, map_mul, hab, hb2]
        calc a * a * (a * a) = (a * a * a) * a := by simp only [mul_assoc]
          _ = a := by rw [← pow_three', hcube a ha, one_mul]
      exact hab' (hda.symm.trans ((congrArg φ hd2).trans hab))
  have hcQ : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (hcomm a ha b hb) m n)).eq
  have hPcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hoa]
  have hQcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have hPQ : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    by_contra hne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hxP : (x : Ω) ∈ Subgroup.zpowers a := x.2.1
    have hxQ : (x : Ω) ∈ Subgroup.zpowers b := x.2.2
    have hx1' : (x : Ω) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxo : orderOf (x : Ω) = 3 :=
      hord x (Subgroup.zpowers_le.2 ha hxP) hx1'
    have hxPe : Subgroup.zpowers (x : Ω) = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxP)
        (by rw [hPcard, Nat.card_zpowers, hxo])
    have hxQe : Subgroup.zpowers (x : Ω) = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxQ)
        (by rw [hQcard, Nat.card_zpowers, hxo])
    apply hbP
    rw [← hxPe, hxQe]
    exact Subgroup.mem_zpowers b
  have hPQcard : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 := by
    rw [i224_card_sup hcQ hPQ, hPcard, hQcard]
  have hPQV : Subgroup.zpowers a ⊔ Subgroup.zpowers b = V :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb))
      (by rw [hPQcard]; exact hVcard)
  have hdPQ : d ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := hPQV ▸ hd
  obtain ⟨x, hx, y, hy, hxy⟩ := i224_mem_sup_of_comm hcQ hdPQ
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hcab : Commute a b := hcomm a ha b hb
  have hkey : a = a ^ (m * n) * b ^ (m + n * n) := by
    have h1 : φ d = (φ a) ^ m * (φ b) ^ n := by rw [hxy, map_mul, map_zpow, map_zpow]
    rw [hab, hbd, hda] at h1
    have h2 : d ^ n = a ^ (m * n) * b ^ (n * n) := by
      rw [hxy, ((hcab.zpow_zpow m n)).mul_zpow n, ← zpow_mul, ← zpow_mul]
    rw [h2] at h1
    have h3 : b ^ m * (a ^ (m * n) * b ^ (n * n)) = a ^ (m * n) * b ^ (m + n * n) := by
      rw [← mul_assoc, ((hcab.symm.zpow_zpow m (m * n))).eq, mul_assoc, ← zpow_add]
    rw [h3] at h1
    exact h1
  have hrel : a ^ (m * n - 1) * b ^ (m + n * n) = 1 := by
    have : a ^ (m * n - 1) * b ^ (m + n * n) = a⁻¹ * (a ^ (m * n) * b ^ (m + n * n)) := by group
    rw [this, ← hkey]; group
  have hP1 : a ^ (m * n - 1) ∈ Subgroup.zpowers a := Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hQ1 : a ^ (m * n - 1) ∈ Subgroup.zpowers b := by
    have : a ^ (m * n - 1) = (b ^ (m + n * n))⁻¹ := eq_inv_of_mul_eq_one_left hrel
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)
  have hA1 : a ^ (m * n - 1) = 1 := by
    have : a ^ (m * n - 1) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨hP1, hQ1⟩
    rwa [hPQ, Subgroup.mem_bot] at this
  have hB1 : b ^ (m + n * n) = 1 := by
    rw [hA1, one_mul] at hrel
    exact hrel
  have h3a : (3 : ℤ) ∣ m * n - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := Ω) (x := a) (i := m * n - 1)).2 hA1
    rwa [hoa] at this
  have h3b : (3 : ℤ) ∣ m + n * n := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := Ω) (x := b) (i := m + n * n)).2 hB1
    rwa [hob] at this
  have hza := (ZMod.intCast_zmod_eq_zero_iff_dvd (m * n - 1) 3).2 h3a
  have hzb := (ZMod.intCast_zmod_eq_zero_iff_dvd (m + n * n) 3).2 h3b
  push_cast at hza hzb
  obtain ⟨hm2, hn2⟩ := zmod3_aux _ _ hza hzb
  have h3m : (3 : ℤ) ∣ m + 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m + 1) 3).1 ?_
    push_cast
    rw [hm2]; exact zmod3_aux2
  have h3n : (3 : ℤ) ∣ n + 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (n + 1) 3).1 ?_
    push_cast
    rw [hn2]; exact zmod3_aux2
  have hAm : a ^ (m + 1) = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := Ω) (x := a) (i := m + 1)).1
    exact this (by rw [hoa]; exact h3m)
  have hBn : b ^ (n + 1) = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := Ω) (x := b) (i := n + 1)).1
    exact this (by rw [hob]; exact h3n)
  calc a * b * d = a * b * (a ^ m * b ^ n) := by rw [hxy]
    _ = a * (b * a ^ m) * b ^ n := by group
    _ = a * (a ^ m * b) * b ^ n := by rw [(hcab.symm.zpow_right m).eq]
    _ = a ^ (m + 1) * b ^ (n + 1) := by group
    _ = 1 := by rw [hAm, hBn, one_mul]

theorem norm_center_trivial [Finite Ω] {V : Subgroup Ω} (hV : IsElemAbelian 3 V)
    (hVcard : Nat.card V ≤ 9) {c z : Ω} (hc3 : c ^ 3 = 1) (hz : z ∈ V)
    (hz₂ : c * z * c⁻¹ ∈ V) (hz₃ : c * c * z * c⁻¹ * c⁻¹ ∈ V) :
    z * (c * z * c⁻¹) * (c * c * z * c⁻¹ * c⁻¹) = 1 := by
  have hccc : c * c * c = 1 := (pow_three' c).symm.trans hc3
  refine norm_triple_trivial hV hVcard (φ := MulAut.conj c) hz hz₂ hz₃ ?_ ?_ ?_
  · simp [MulAut.conj_apply]
  · simp only [MulAut.conj_apply]; group
  · simp only [MulAut.conj_apply]
    calc c * (c * c * z * c⁻¹ * c⁻¹) * c⁻¹ = (c * c * c) * z * (c * c * c)⁻¹ := by group
      _ = z := by rw [hccc]; simp

end Norm

section Rel

variable {X : Type} [Group X] [Finite X]

theorem center_comm_conj {K B : Subgroup X} (hH : I271Hyp 3 K B) {b : X} (hb : b ∈ B) {y z : X}
    (hy : y ∈ GLBConj b K) (hz : z ∈ K ⊓ Subgroup.centralizer (K : Set X)) : z * y = y * z := by
  have hKc : CFSG.Open.IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  have hyb : b * y * b⁻¹ ∈ K := mem_gLBConj.1 hy
  by_cases hbN : b ∈ Subgroup.normalizer (K : Set X)
  · have hyK : y ∈ K := by
      have := i224_conj_mem_of_normalizer hbN hyb
      have e : b⁻¹ * (b * y * b⁻¹) * b = y := by group
      rw [e] at this
      exact this
    exact (Subgroup.mem_centralizer_iff.1 hz.2 y hyK).symm
  · have hne : i224Cj (1 : X) K ≠ i224Cj b⁻¹ K := by
      intro heq
      have := mem_normalizer_of_i224Cj_eq heq
      apply hbN
      have h1 : b⁻¹ ∈ Subgroup.normalizer (K : Set X) := by simpa using this
      simpa using (Subgroup.normalizer (K : Set X)).inv_mem h1
    refine i224_comm_cj hKc 1 b⁻¹ hne z ?_ y ?_
    · rw [mem_i224Cj]; simpa using hz.1
    · rw [mem_i224Cj]; simpa using hyb

theorem conj_center_mem {K B : Subgroup X} (hH : I271Hyp 3 K B) {g : X} (hg : g ∈ B) {z : X}
    (hz : z ∈ K ⊓ Subgroup.centralizer (K : Set X)) :
    g * z * g⁻¹ ∈ bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X) := by
  refine ⟨?_, ?_⟩
  · refine Subgroup.mem_iSup_of_mem g⁻¹ (Subgroup.mem_iSup_of_mem (B.inv_mem hg) ?_)
    rw [mem_gLBConj]
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rw [e]
    exact hz.1
  · have hle : bClosure B K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set X) := by
      refine iSup₂_le fun b hb y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy' : g⁻¹ * y * g ∈ GLBConj (b * g) K := by
        rw [mem_gLBConj]
        have e : b * g * (g⁻¹ * y * g) * (b * g)⁻¹ = b * y * b⁻¹ := by group
        rw [e]
        exact mem_gLBConj.1 hy
      have := center_comm_conj hH (B.mul_mem hb hg) hy' hz
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = (g * z * g⁻¹) * y := by group
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem rel_of_ZJ {K B : Subgroup X} (hH : I271Hyp 3 K B)
    (hZ1 : IsElemAbelian 3 (bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)))
    (hZ2 : Nat.card ↥(bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)) ≤ 9) :
    ∀ c ∈ B, c ∉ Subgroup.normalizer (K : Set X) →
      ∀ z ∈ K ⊓ Subgroup.centralizer (K : Set X),
        z * (c * z * c⁻¹) * (c * c * z * c⁻¹ * c⁻¹) = 1 := by
  intro c hc _ z hz
  have hc3 : c ^ 3 = 1 := hH.scp.2.1.2 c hc
  have h1 : z ∈ bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X) := by
    simpa using conj_center_mem hH B.one_mem hz
  have h2 : c * z * c⁻¹ ∈ bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X) :=
    conj_center_mem hH hc hz
  have h3 : c * c * z * c⁻¹ * c⁻¹ ∈
      bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X) := by
    have := conj_center_mem hH (B.mul_mem hc hc) hz
    have e : (c * c) * z * (c * c)⁻¹ = c * c * z * c⁻¹ * c⁻¹ := by group
    rwa [e] at this
  exact norm_center_trivial hZ1 hZ2 hc3 h1 h2 h3

end Rel

end CFSG.HardMathSupport.Solomon.Coordinator
