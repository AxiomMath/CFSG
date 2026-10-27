module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Psi
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Two

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement Pointwise

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

@[expose] def secImg (a : A) (X J S : Subgroup A) : Subgroup (secB a X J) :=
  (S.subgroupOf (secY a X J)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(secY a X J)))

theorem mem_secImg_iff {S : Subgroup A} (hS : S ≤ secY a X J) {b : secB a X J} :
    b ∈ secImg a X J S ↔ ∃ (s : A) (hs : s ∈ S), b = secMk a X J s (hS hs) := by
  constructor
  · intro hb
    obtain ⟨⟨y, hy⟩, hyS, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨y, hyS, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨s, hS hs⟩, hs, rfl⟩

theorem secImg_sup {S T : Subgroup A} (hS : S ≤ secY a X J) (hT : T ≤ secY a X J) :
    secImg a X J (S ⊔ T) = secImg a X J S ⊔ secImg a X J T := by
  unfold secImg
  rw [Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

theorem secMk_inj (hN : pPrimeCore 2 ↥(secY a X J) = ⊥) {y y' : A} (hy : y ∈ secY a X J)
    (hy' : y' ∈ secY a X J) : secMk a X J y hy = secMk a X J y' hy' ↔ y = y' := by
  rw [secMk_eq_iff, hN, Subgroup.mem_bot, inv_mul_eq_one]
  exact Subtype.mk_eq_mk

theorem secMk_zpow {y : A} (hy : y ∈ secY a X J) (m : ℤ) :
    secMk a X J (y ^ m) ((secY a X J).zpow_mem hy m) = (secMk a X J y hy) ^ m := rfl

theorem secImg_zpowers : secImg a X J (zpowers a) = zpowers (secZ a X J) := by
  have hS : zpowers a ≤ secY a X J := Subgroup.zpowers_le.mpr (z_mem_secY a X J)
  ext b
  rw [mem_secImg_iff hS]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, (secMk_zpow (z_mem_secY a X J) m).symm⟩
  · intro hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨a ^ m, Subgroup.zpow_mem_zpowers a m, secMk_zpow (z_mem_secY a X J) m⟩

theorem secMk_injective (hN : pPrimeCore 2 ↥(secY a X J) = ⊥) :
    Function.Injective (QuotientGroup.mk' (pPrimeCore 2 ↥(secY a X J))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]

@[expose] noncomputable def secImgEquiv (hN : pPrimeCore 2 ↥(secY a X J) = ⊥) {S : Subgroup A}
    (hS : S ≤ secY a X J) : ↥S ≃* ↥(secImg a X J S) :=
  (Subgroup.subgroupOfEquivOfLe hS).symm.trans
    (Subgroup.equivMapOfInjective _ _ (secMk_injective hN))

theorem mem_secY_cases (ha2 : a * a = 1) (haM : a ∈ normalizer ((J ⊔ X : Subgroup A) : Set A)) {y : A}
    (hy : y ∈ secY a X J) : ∃ m ∈ J ⊔ X, y = m ∨ y = m * a := by
  have hle : zpowers a ≤ normalizer ((J ⊔ X : Subgroup A) : Set A) := Subgroup.zpowers_le.mpr haM
  have h1 : y ∈ (((J ⊔ X) ⊔ zpowers a : Subgroup A) : Set A) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (J ⊔ X) (zpowers a) hle] at h1
  obtain ⟨m, hm, w, hw, rfl⟩ := h1
  rcases mem_zpowers_involution ha2 hw with rfl | rfl
  · exact ⟨m, hm, Or.inl (mul_one m)⟩
  · exact ⟨m, hm, Or.inr rfl⟩

theorem mem_of_sq_mem_of_odd {M : Subgroup A} {n : A} (hodd : Odd (orderOf n)) (h : n * n ∈ M) :
    n ∈ M := by
  obtain ⟨r, hr⟩ := hodd
  have : n = (n * n) ^ (r + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, ← hr,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact M.pow_mem h _

theorem SubData.a_mem_normalizer_sup {c : E4Ctx G z A a p X} (d : SubData c J) :
    a ∈ normalizer ((J ⊔ X : Subgroup A) : Set A) := by
  refine mem_normalizer_of_map_conj_eq' ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer d.zJ,
    map_conj_eq_of_mem_normalizer c.a_mem_normalizer]

theorem pPrimeCore_secY_eq_bot {c : E4Ctx G z A a p X} (d : SubData c J) (hJn : J.Normal)
    (hker : (secPsi a X J).ker = ⊥) (hXC : X ⊓ centralizer (J : Set A) = ⊥)
    (hKX : secX a X J ⊓ secJ a X J = ⊥) : pPrimeCore 2 ↥(secY a X J) = ⊥ := by
  have hz2 := c.z2
  have haM := d.a_mem_normalizer_sup
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨m, hm, hcase⟩ := mem_secY_cases hz2 haM n.2
  have hn2 : (n : A) * n ∈ J ⊔ X := by
    rcases hcase with h1 | h1
    · rw [h1]; exact mul_mem hm hm
    · rw [h1]
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right hz2
      have : m * a * (m * a) = m * (a * m * a⁻¹) := by
        calc m * a * (m * a) = m * (a * m * a) := by group
          _ = m * (a * m * a⁻¹) := by rw [hai]
      rw [this]
      exact mul_mem hm ((Subgroup.mem_normalizer_iff.mp haM m).mp hm)
  have hodd : Odd (orderOf (n : A)) := by
    have h1 : orderOf (⟨n, hn⟩ : ↥(pPrimeCore 2 ↥(secY a X J))) ∣
        Nat.card (pPrimeCore 2 ↥(secY a X J)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat N_odd h1
  have hnM : (n : A) ∈ J ⊔ X := mem_of_sq_mem_of_odd hodd hn2
  have hJX : ((J ⊔ X : Subgroup A) : Set A) = (J : Set A) * (X : Set A) := Subgroup.normal_mul J X
  have hnM' : (n : A) ∈ (J : Set A) * (X : Set A) := by rw [← hJX]; exact hnM
  obtain ⟨j, hj, x, hx, hjx⟩ := hnM'
  have hjY : j ∈ secY a X J := J_le_secY a X J hj
  have hxY : x ∈ secY a X J := X_le_secY a X J hx
  have h1 : secMk a X J j hjY * secMk a X J x hxY = 1 := by
    rw [← secMk_mul hjY hxY, secMk_congr hjx _ n.2]
    exact (secMk_eq_one_iff n.2).mpr hn
  have h2 : secMk a X J x hxY = (secMk a X J j hjY)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : secMk a X J x hxY ∈ secX a X J ⊓ secJ a X J :=
    Subgroup.mem_inf.mpr ⟨secMk_mem_secX hx, by rw [h2]; exact inv_mem (secMk_mem_secJ hj)⟩
  rw [hKX, Subgroup.mem_bot] at h3
  have h4 : x ∈ centralizer (J : Set A) := (secB_X_ker d.hyp hx).mp h3
  have h5 : x ∈ X ⊓ centralizer (J : Set A) := Subgroup.mem_inf.mpr ⟨hx, h4⟩
  rw [hXC, Subgroup.mem_bot] at h5
  have h6 : secMk a X J j hjY = 1 := by
    rw [h3, mul_one] at h1
    exact h1
  have h7 : (⟨j, hj⟩ : ↥J) ∈ (secPsi a X J).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h6
  rw [hker, Subgroup.mem_bot] at h7
  have hj1 : j = 1 := congrArg Subtype.val h7
  exact Subtype.ext (by rw [← hjx, hj1, h5]; simp)

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
