module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseFrattini
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement Pointwise

section A4Model

@[expose] def a4c3 : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem a4c3_pow : a4c3 ^ 3 = 1 := by decide

theorem a4c3_ne : a4c3 ≠ 1 := by decide

theorem a4_conj_ne : ∀ h : alternatingGroup (Fin 4), h * h = 1 → h ≠ 1 → a4c3 * h * a4c3⁻¹ ≠ h := by
  decide

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem a4_irreducible : ∀ v w : alternatingGroup (Fin 4), v * v = 1 → v ≠ 1 → w * w = 1 → w ≠ 1 →
    w = v ∨ w = a4c3 * v * a4c3⁻¹ ∨ w = a4c3 * a4c3 * v * a4c3⁻¹ * a4c3⁻¹ := by
  decide

theorem a4_gen_odd : ∀ g : alternatingGroup (Fin 4),
    ∃ a b : alternatingGroup (Fin 4), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ g = a * b := by
  decide

theorem a4_pow_two_or_three : ∀ g : alternatingGroup (Fin 4), g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

end A4Model

section Transport

variable {G : Type*} [Group G] {Z : Subgroup G} (e : Z ≃* alternatingGroup (Fin 4))

def a4x : G := ((e.symm a4c3 : Z) : G)

theorem a4x_mem : a4x e ∈ Z := (e.symm a4c3).2

theorem a4x_pow : a4x e ^ 3 = 1 := by
  have : (e.symm a4c3) ^ 3 = 1 := by rw [← map_pow, a4c3_pow, map_one]
  have h := congrArg Subtype.val this
  simpa [a4x] using h

theorem a4x_ne : a4x e ≠ 1 := fun h => a4c3_ne (by
  have h1 : e.symm a4c3 = 1 := Subtype.ext h
  have h2 := congrArg e h1
  simpa using h2)

theorem e_conj (a : alternatingGroup (Fin 4)) (z : Z) :
    e (e.symm a * z * (e.symm a)⁻¹) = a * e z * a⁻¹ := by simp [map_mul, map_inv]

variable {e} {V : Subgroup G} (hV : ∀ y, y ∈ V ↔ y ∈ Z ∧ y * y = 1)
include hV

theorem V_conj_mem {z v : G} (hz : z ∈ Z) (hv : v ∈ V) : z * v * z⁻¹ ∈ V := by
  obtain ⟨hvZ, hvv⟩ := (hV v).1 hv
  refine (hV _).2 ⟨Z.mul_mem (Z.mul_mem hz hvZ) (Z.inv_mem hz), ?_⟩
  calc z * v * z⁻¹ * (z * v * z⁻¹) = z * (v * v) * z⁻¹ := by group
    _ = 1 := by rw [hvv]; group

theorem le_normalizer_V : Z ≤ Subgroup.normalizer (V : Set G) := fun z hz => by
  refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨V_conj_mem hV hz, fun hv => ?_⟩
  have := V_conj_mem hV (Z.inv_mem hz) hv
  rwa [show z⁻¹ * (z * v * z⁻¹) * z⁻¹⁻¹ = v by group] at this

theorem a4x_conj_ne {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    a4x e * v * (a4x e)⁻¹ ≠ v := by
  obtain ⟨hvZ, hvv⟩ := (hV v).1 hv
  intro h
  set zv : Z := ⟨v, hvZ⟩ with hzv
  have ha : e zv * e zv = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext (by simpa using hvv)
  have ha1 : e zv ≠ 1 := fun h1 => hv1 (by
    have : zv = 1 := e.injective (by simpa using h1)
    simpa [hzv] using congrArg Subtype.val this)
  have h2 : e.symm a4c3 * zv * (e.symm a4c3)⁻¹ = zv := Subtype.ext (by simpa [a4x, hzv] using h)
  have h3 := congrArg e h2
  rw [e_conj] at h3
  exact a4_conj_ne _ ha ha1 h3

theorem V_irreducible {v w : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hw : w ∈ V) (hw1 : w ≠ 1) :
    w = v ∨ w = a4x e * v * (a4x e)⁻¹ ∨
      w = a4x e * a4x e * v * (a4x e)⁻¹ * (a4x e)⁻¹ := by
  obtain ⟨hvZ, hvv⟩ := (hV v).1 hv
  obtain ⟨hwZ, hww⟩ := (hV w).1 hw
  set zv : Z := ⟨v, hvZ⟩ with hzv
  set zw : Z := ⟨w, hwZ⟩ with hzw
  have ha : e zv * e zv = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext (by simpa using hvv)
  have hb : e zw * e zw = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext (by simpa using hww)
  have ha1 : e zv ≠ 1 := fun h1 => hv1 (by
    have : zv = 1 := e.injective (by simpa using h1)
    simpa [hzv] using congrArg Subtype.val this)
  have hb1 : e zw ≠ 1 := fun h1 => hw1 (by
    have : zw = 1 := e.injective (by simpa using h1)
    simpa [hzw] using congrArg Subtype.val this)
  rcases a4_irreducible _ _ ha ha1 hb hb1 with h | h | h
  · left
    have : zw = zv := e.injective h
    simpa [hzw, hzv] using congrArg Subtype.val this
  · right; left
    have : zw = e.symm a4c3 * zv * (e.symm a4c3)⁻¹ := by
      apply e.injective
      rw [e_conj]; exact h
    simpa [a4x, hzw, hzv] using congrArg Subtype.val this
  · right; right
    have : zw = e.symm a4c3 * e.symm a4c3 * zv * (e.symm a4c3)⁻¹ * (e.symm a4c3)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h
    simpa [a4x, hzw, hzv] using congrArg Subtype.val this

theorem mem_V_of_two_pow (e : Z ≃* alternatingGroup (Fin 4)) {y : G} (hy : y ∈ Z) {k : ℕ} (hk : y ^ (2 ^ k) = 1) : y ∈ V := by
  refine (hV y).2 ⟨hy, ?_⟩
  set zy : Z := ⟨y, hy⟩
  have hzk : zy ^ (2 ^ k) = 1 := Subtype.ext (by simpa [zy] using hk)
  have hek : (e zy) ^ (2 ^ k) = 1 := by rw [← map_pow, hzk, map_one]
  rcases a4_pow_two_or_three (e zy) with h2 | h3
  · have : e zy * e zy = 1 := by rw [← pow_two]; exact h2
    have h4 : zy * zy = 1 := e.injective (by simpa using this)
    simpa [zy] using congrArg Subtype.val h4
  · have hone : e zy = 1 := by
      have hd1 : orderOf (e zy) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hd2 : orderOf (e zy) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hek
      have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      have h6 := Nat.dvd_gcd hd1 hd2
      rw [hc.gcd_eq_one] at h6
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)
    have : zy = 1 := e.injective (by simpa using hone)
    have h5 : y = 1 := by simpa [zy] using congrArg Subtype.val this
    simp [h5]

omit hV in
theorem oTwoUpper_eq_of_a4 (e : Z ≃* alternatingGroup (Fin 4)) : oTwoUpper Z = Z := by
  refine le_antisymm (oTwoUpper_le Z) fun z hz => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := a4_gen_odd (e ⟨z, hz⟩)
  have hodd : ∀ c : alternatingGroup (Fin 4), c ^ 3 = 1 → Odd (orderOf ((e.symm c : Z) : G)) := by
    intro c hc
    have h1 : ((e.symm c : Z) : G) ^ 3 = 1 := by
      have : (e.symm c) ^ 3 = 1 := by rw [← map_pow, hc, map_one]
      simpa using congrArg Subtype.val this
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h1)
  have hz' : (⟨z, hz⟩ : Z) = e.symm a * e.symm b := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hab
  have hz'' : z = ((e.symm a : Z) : G) * ((e.symm b : Z) : G) := by
    simpa using congrArg Subtype.val hz'
  rw [hz'']
  exact (oTwoUpper Z).mul_mem (mem_oTwoUpper_of_odd (e.symm a).2 (hodd a ha))
    (mem_oTwoUpper_of_odd (e.symm b).2 (hodd b hb))

end Transport

theorem eq_one_of_pow_three_of_pow_two {G : Type*} [Group G] {y : G} (h3 : y ^ 3 = 1) {k : ℕ}
    (h2 : y ^ (2 ^ k) = 1) : y = 1 := by
  have hd1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h6 := Nat.dvd_gcd hd1 hd2
  rw [hc.gcd_eq_one] at h6
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)


theorem noA4 {G : Type} [Group G] [Finite G] {X₁ L R Q Z : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hQle : Q ≤ X₁) (hQX₁ : X₁ ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : ∀ g ∈ X₁, (∀ q ∈ Q, g * q = q * g) → g ∈ Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLperf : ⁅L, L⁆ = L)
    (hR : R ≤ pCoreOf 2 X₁) (hodd : ∀ g ∈ X₁, g ^ 3 = 1 → g ∈ L)
    (hlie : ∀ g ∈ L, g ^ 3 = 1 → (∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ Q) →
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ Q)
    (hZX : Z ≤ X₁) (e : Z ≃* alternatingGroup (Fin 4)) (hZ : IsSubnormal Z X₁) : False := by
  obtain ⟨V, hVcard, hV⟩ := CFSG.Glauberman.Dickson.MaxCases.exists_kleinFour e
  set x : G := a4x e with hxdef
  have hxZ : x ∈ Z := a4x_mem e
  have hx3 : x ^ 3 = 1 := a4x_pow e
  have hx1 : x ≠ 1 := a4x_ne e
  have hxX : x ∈ X₁ := hZX hxZ
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := hQX₁ hxX
  have hQ2' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ3' : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := pCoreOf 2 X₁ with hPdef
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 X₁
  have hPX : X₁ ≤ Subgroup.normalizer (P : Set G) := localGroup_le_normalizer_pCoreOf 2 X₁
  have hPle : P ≤ X₁ := pCoreOf_le 2 X₁
  have hVZ : V ≤ Z := fun v hv => ((hV v).1 hv).1
  have hV2 : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by
    have := ((hV v).1 v.2).2
    simpa [pow_two] using this)⟩
  have hVsub : IsSubnormal V X₁ :=
    IsSubnormal.step hVZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hVZ).mpr
      (le_normalizer_V hV)) hZ
  have hVP : V ≤ P := CFSG.Quasithin.F6.le_pCoreOf_of_isSubnormal hVsub hV2
  have hQP : Q ≤ P := normal_pGroup_le_pCoreOf 2 Q X₁ hQle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr hQX₁) hQ2
  have hZP : (P : Set G) * Z = Z * P := by
    have h1 := Subgroup.coe_mul_of_right_le_normalizer_left P Z (fun z hz => by
      have := hPX (hZX hz)
      exact (Subgroup.mem_normalizer_iff.mpr (fun p => by
        have := Subgroup.mem_normalizer_iff.mp this p
        exact this)))
    have h2 := Subgroup.coe_mul_of_left_le_normalizer_right Z P (fun z hz => hPX (hZX hz))
    rw [← h1, sup_comm, h2]
  obtain ⟨-, hZn⟩ := CFSG.Quasithin.a4_2_2 (X := Z) (M := X₁) (oTwoUpper_eq_of_a4 e).symm hZ hPle
    hP2 hZP
  have hZPn : Z ⊔ P ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hZn
  have hPV : ∀ p ∈ P, p * x * p⁻¹ * x⁻¹ ∈ V := by
    intro p hp
    have hpN := hZPn (Subgroup.mem_sup_right hp)
    have h1 : p * x * p⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hpN x).mp hxZ
    have h2 : p * x * p⁻¹ * x⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hxZ)
    have h3 : p * x * p⁻¹ * x⁻¹ ∈ P := by
      have hxP : x ∈ Subgroup.normalizer (P : Set G) := hPX hxX
      have : x * p⁻¹ * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxP _).mp (P.inv_mem hp)
      have h4 := P.mul_mem hp this
      rwa [show p * (x * p⁻¹ * x⁻¹) = p * x * p⁻¹ * x⁻¹ by group] at h4
    obtain ⟨k, hk⟩ := hP2 ⟨_, h3⟩
    exact mem_V_of_two_pow hV e h2 (congrArg Subtype.val hk)
  have hxL : x ∈ L := hodd x hxX hx3
  have hxQ : x ∉ Q := fun h => by
    obtain ⟨k, hk⟩ := hQ2 ⟨x, h⟩
    exact hx1 (eq_one_of_pow_three_of_pow_two hx3 (congrArg Subtype.val hk))
  obtain ⟨q0, hq0, hq0x⟩ : ∃ q0 ∈ Q, x * q0 ≠ q0 * x := by
    by_contra hcon
    push Not at hcon
    exact hxQ (hCQ x hxX hcon)
  have hQV : ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ V := fun q hq => hPV q (hQP hq)
  have hcQ : ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ Q := fun q hq => by
    have h1 : x * q⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN _).mp (Q.inv_mem hq)
    have h2 := Q.mul_mem hq h1
    rwa [show q * (x * q⁻¹ * x⁻¹) = q * x * q⁻¹ * x⁻¹ by group] at h2
  set v0 : G := q0 * x * q0⁻¹ * x⁻¹ with hv0
  have hv0V : v0 ∈ V := hQV q0 hq0
  have hv01 : v0 ≠ 1 := fun h => hq0x (by
    have hc : ⁅q0, x⁆ = 1 := h
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm)
  set E' : Subgroup G := Subgroup.closure {c | ∃ q ∈ Q, c = q * x * q⁻¹ * x⁻¹} with hE'
  have hE'Q : E' ≤ Q := (Subgroup.closure_le _).2 (by rintro _ ⟨q, hq, rfl⟩; exact hcQ q hq)
  have hE'inv : ∀ w ∈ E', x * w * x⁻¹ ∈ E' := by
    intro w hw
    have hmap : E'.map (MulAut.conj x).toMonoidHom ≤ E' := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨q, hq, rfl⟩
      have hq' : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN _).mp hq
      show x * (q * x * q⁻¹ * x⁻¹) * x⁻¹ ∈ E'
      rw [show x * (q * x * q⁻¹ * x⁻¹) * x⁻¹ =
        (x * q * x⁻¹) * x * (x * q * x⁻¹)⁻¹ * x⁻¹ by group]
      exact Subgroup.subset_closure ⟨_, hq', rfl⟩
    exact hmap ⟨w, hw, rfl⟩
  have hv0E : v0 ∈ E' := Subgroup.subset_closure ⟨q0, hq0, rfl⟩
  have hVE : V ≤ E' := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]; exact E'.one_mem
    · rcases V_irreducible hV hv0V hv01 hw hw1 with h | h | h
      · rw [h]; exact hv0E
      · rw [h]; exact hE'inv _ hv0E
      · rw [h, show x * x * v0 * x⁻¹ * x⁻¹ = x * (x * v0 * x⁻¹) * x⁻¹ by group]
        exact hE'inv _ (hE'inv _ hv0E)
  have hVQ : V ≤ Q := hVE.trans hE'Q
  have hcent : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Q := by
    refine hlie x hxL hx3 (fun r hr => ?_)
    have h1 := hVQ (hPV r (hR hr))
    have : (r * x * r⁻¹ * x⁻¹)⁻¹ = x * r * x⁻¹ * r⁻¹ := by group
    rw [← this]
    exact Q.inv_mem h1
  have hΦ := comm_comm_mem_phiG hQ2 hLQ hLperf hxL hcent (by rw [hVcard]) hQV
  by_cases hVΦ : ∀ w ∈ V, w ∈ phiG Q
  ·
    have htriv : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ (frattini Q).map Q.subtype := by
      intro y hy
      have h1 := hVΦ _ (hQV y hy)
      have : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
      rw [← this]
      exact (phiG Q).inv_mem h1
    have hxz : IsPGroup 3 (Subgroup.zpowers x) := fun y => ⟨1, by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
      have h3 : (y : G) ^ 3 = 1 := by
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      exact Subtype.ext (by simpa using h3)⟩
    exact hq0x (by
      have := centralizes_of_trivial_on_frattini_quotient_gen (r := 2) (q := 3) hQ2
        (by norm_num) hxN hxz htriv q0 hq0
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this)
  ·
    push Not at hVΦ
    have hnoΦ : ∀ u ∈ V, u ∈ phiG Q → u = 1 := by
      intro u hu huΦ
      by_contra hu1
      obtain ⟨w, hw, hwΦ⟩ := hVΦ
      by_cases hw1 : w = 1
      · exact hwΦ (hw1 ▸ (phiG Q).one_mem)
      · rcases V_irreducible hV hu hu1 hw hw1 with h | h | h
        · exact hwΦ (h ▸ huΦ)
        · exact hwΦ (h ▸ conj_mem_phiG hxN huΦ)
        · exact hwΦ (h ▸ (by
            rw [show x * x * u * x⁻¹ * x⁻¹ = x * (x * u * x⁻¹) * x⁻¹ by group]
            exact conj_mem_phiG hxN (conj_mem_phiG hxN huΦ)))
    have h1 : x * v0 * x⁻¹ * v0⁻¹ ∈ V :=
      V.mul_mem (V_conj_mem hV hxZ hv0V) (V.inv_mem hv0V)
    have h2 := hΦ q0 hq0
    have h3 := hnoΦ _ h1 h2
    have h4 : x * v0 * x⁻¹ = v0 := by
      rw [mul_inv_eq_one] at h3
      exact h3
    exact a4x_conj_ne hV hv0V hv01 h4

end CFSG.HardMathSupport.Cooperstein.StructureLie
