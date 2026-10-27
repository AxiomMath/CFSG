module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx1
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem not_isCyclic_of_isDihedralTwoGroup {Y : Type} [Group Y] {n : ℕ} (h : IVK.IsDihedralTwoGroup Y n) :
    ¬ IsCyclic Y := by
  obtain ⟨-, k, hk, hk2, ⟨e⟩⟩ := h
  intro hc
  haveI : NeZero k := ⟨by omega⟩
  have hcD : IsCyclic (DihedralGroup k) := isCyclic_of_surjective e.toMonoidHom e.surjective
  obtain ⟨g, hg⟩ := hcD.exists_generator
  have hcard : Nat.card (DihedralGroup k) = 2 * k := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hord : orderOf g = 2 * k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  cases g with
  | r i =>
    rw [DihedralGroup.orderOf_r] at hord
    have h1 : k / k.gcd i.val ≤ k := Nat.div_le_self _ _
    omega
  | sr i =>
    rw [DihedralGroup.orderOf_sr] at hord
    omega

theorem not_isCyclic_of_isSemidihedralTwoGroup {Y : Type} [Group Y] {n : ℕ}
    (h : IVK.IsSemidihedralTwoGroup Y n) : ¬ IsCyclic Y := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  intro hc
  have hcS : IsCyclic (Open.SemidihedralGroup n) := isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcomm : ∀ x y : Open.SemidihedralGroup n, x * y = y * x := by
    letI := IsCyclic.commGroup (α := Open.SemidihedralGroup n)
    intro x y
    exact mul_comm x y
  have hcen : Subgroup.center (Open.SemidihedralGroup n) = ⊤ := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    intro y
    exact hcomm y x
  have h1 := Semidihedral.center_card n hn
  rw [hcen, Subgroup.card_top, Semidihedral.card n (by omega)] at h1
  have : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
  omega

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem mem_cSec {K : Subgroup G} {x : G} :
    x ∈ cSec K ↔ x ∈ normalizer (K : Set G) ∧ x ∈ normalizer (pPrimeCoreOf 2 K : Set G) ∧
      ∀ k ∈ K, ⁅k, x⁆ ∈ pPrimeCoreOf 2 K := Iff.rfl

theorem P₁_le_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Pof S K₁ ≤ Qof S K₂ := fun _ hx => ⟨hx.1, (hs.m4 hII).cs₂ hx.2⟩

theorem P₂_le_Q₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Pof S K₂ ≤ Qof S K₁ := fun _ hx => ⟨hx.1, (hs.m4 hII).cs₁ hx.2⟩

theorem Q₁_le_S1 (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : Qof S K₁ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, (mem_cSec.1 hx.2).1⟩

theorem Q₂_le_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Qof S K₂ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, (hs.norm_iff hII hx.1).2 (mem_cSec.1 hx.2).1⟩

theorem S1_le_S : S1 S K₁ ≤ S := inf_le_left

theorem P_le_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : Pof S K ≤ S1 S K₁ := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hK with rfl | rfl
  · exact Subgroup.le_normalizer hx.2
  · exact (hs.m4 hII).n₂₁ hx.2

theorem Pz_le_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Pz S z ≤ S1 S K₁ := by
  rw [hs.Pz_eq_sup hII]
  exact sup_le (hs.P_le_S1 hII (Or.inl rfl)) (hs.P_le_S1 hII (Or.inr rfl))

theorem S1_normalizes_P (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : ∀ x ∈ S1 S K₁, ∀ p ∈ Pof S K, x * p * x⁻¹ ∈ Pof S K := by
  intro x hx p hp
  have hxK : x ∈ normalizer (K : Set G) := by
    rcases hK with rfl | rfl
    · exact hx.2
    · exact (hs.norm_iff hII hx.1).1 hx.2
  have hxS : x ∈ S := hx.1
  have hpS : p ∈ S := hp.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hxS hpS) (inv_mem hxS),
    (Subgroup.mem_normalizer_iff.1 hxK p).1 hp.2⟩

theorem S1_pgroup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    IsPGroup 2 ↥(S1 S K₁) := (hs.S_pgroup hII).to_le S1_le_S

theorem Q_comm_P {K : Subgroup G} (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hK : K = K₁ ∨ K = K₂) : ∀ q ∈ Qof S K, ∀ p ∈ Pof S K, q * p = p * q := by
  have hM := hs.m4 hII
  intro q hq p hp
  have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := (mem_cSec.1 hq.2).2.2 p hp.2
  have h2 : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp.1 hq.1) (inv_mem hp.1)) (inv_mem hq.1)
  have h3 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
  rw [M.inf_eq_bot_of_pgroup_odd hM.S_pgroup (hM.core K hK).odd, Subgroup.mem_bot,
    commutatorElement_def] at h3
  have h4 : p * q = q * p := by
    have h5 : p * q * p⁻¹ * q⁻¹ = 1 := h3
    calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
      _ = q * p := by rw [h5, one_mul]
  exact h4.symm

theorem Q_inf_Q (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Qof S K₁ ⊓ Qof S K₂ = zpowers z := by
  have hM := hs.m4 hII
  apply le_antisymm
  · rintro c ⟨hc1, hc2⟩
    have hcS : c ∈ S := hc1.1
    have hcC : c ∈ centralizer ({z} : Set G) := hM.S_syl.1 hcS
    have h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun x hx =>
      hM.O_le_OK (Or.inl rfl) ((mem_cSec.1 hc1.2).2.2 x hx)
    have h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun y hy =>
      hM.O_le_OK (Or.inr rfl) ((mem_cSec.1 hc2.2).2.2 y hy)
    have hcs : c ∈ M.secCent (K₁ ⊔ K₂) (pPrimeCoreOf 2 (K₁ ⊔ K₂)) := hM.secCent_of_gen hcC h1 h2
    have hcQ : c ∈ Qz S z := by
      rw [Qz_eq hs.fused.std]
      exact ⟨hcS, hcs⟩
    rw [hs.fused.hQ] at hcQ
    exact hcQ
  · exact zpowers_le.2 ⟨hs.z_mem_Q hII (Or.inl rfl), hs.z_mem_Q hII (Or.inr rfl)⟩

theorem card_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Nat.card ↥(Qof S K₂) = e * Nat.card ↥(Pof S K₁) := by
  have h1 := Basic.card_mul_relIndex_of_le (hs.P₁_le_Q₂ hII)
  have h2 := hs.fused.p66.1.2.2.2
  have h3 := Basic.relIndex_ne_zero' (Pof S K₁) (Qof S K₂)
  exact ⟨(Pof S K₁).relIndex (Qof S K₂), by omega, by rw [← h1]; ring⟩

theorem card_Q₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Nat.card ↥(Qof S K₁) = e * Nat.card ↥(Pof S K₂) := by
  have h1 := Basic.card_mul_relIndex_of_le (hs.P₂_le_Q₁ hII)
  have h2 := hs.fused.p66.1.2.2.1
  have h3 := Basic.relIndex_ne_zero' (Pof S K₂) (Qof S K₁)
  exact ⟨(Pof S K₂).relIndex (Qof S K₁), by omega, by rw [← h1]; ring⟩

theorem card_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ((Pz S z).relIndex (S1 S K₁) = 1 ∨ (Pz S z).relIndex (S1 S K₁) = 2 ∨
        (Pz S z).relIndex (S1 S K₁) = 4) ∧
      Nat.card ↥(S1 S K₁) = (Pz S z).relIndex (S1 S K₁) * Nat.card ↥(Pz S z) := by
  have h1 := Basic.card_mul_relIndex_of_le (hs.Pz_le_S1 hII)
  have h2 := hs.fused.p66.2.1.2
  have h3 := Basic.relIndex_ne_zero' (Pz S z) (S1 S K₁)
  obtain ⟨s, hsc⟩ := (IsPGroup.iff_card).1 (hs.S1_pgroup hII)
  have hdvd : (Pz S z).relIndex (S1 S K₁) ∣ 2 ^ s := by
    rw [← hsc, ← h1]; exact Dvd.intro_left _ rfl
  obtain ⟨i, hi, hri⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨?_, by rw [← h1]; ring⟩
  have hi2 : i ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases i <;> simp_all

theorem normalizer_of_normal_subgroupOf {A X : Subgroup G} (hAX : A ≤ X) (hN : (A.subgroupOf X).Normal) :
    X ≤ normalizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : (⟨y, hAX hy⟩ : ↥X) ∈ A.subgroupOf X := hy
    have h2 := hN.conj_mem _ h1 ⟨x, hx⟩
    exact h2
  · intro hy
    have hyX : x * y * x⁻¹ ∈ X := hAX hy
    have h1 : (⟨x * y * x⁻¹, hAX hy⟩ : ↥X) ∈ A.subgroupOf X := hy
    have h2 := hN.conj_mem _ h1 ⟨x⁻¹, inv_mem hx⟩
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    have h3 : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ A := h2
    rw [inv_inv] at h3
    rwa [e] at h3

theorem two_mul_card_S1_of_four (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (h4 : (Pz S z).relIndex (S1 S K₁) = 4) :
    2 * Nat.card ↥(S1 S K₁) = Nat.card ↥(Qof S K₁) * Nat.card ↥(Qof S K₂) := by
  obtain ⟨-, hS1⟩ := hs.fused.p66.2.2.2 h4
  have hK₁ : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := by simp
  obtain ⟨hN₁, -⟩ := hs.fused.p66.2.2.1 K₁ hK₁
  have hnorm : Qof S K₂ ≤ normalizer (Qof S K₁ : Set G) :=
    (hs.Q₂_le_S1 hII).trans (normalizer_of_normal_subgroupOf (hs.Q₁_le_S1) hN₁)
  have h1 := M.card_sup_mul_card_inf hnorm
  rw [← hS1, hs.Q_inf_Q hII, M.card_zpowers_of_sq hs.z_sq hs.z_ne] at h1
  omega

theorem nc_quot {K : Subgroup G} (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hK : K = K₁ ∨ K = K₂) :
    ∃ _ : ((Qof S K).subgroupOf (S1 S K₁)).Normal,
      ¬ IsCyclic (↥(S1 S K₁) ⧸ (Qof S K).subgroupOf (S1 S K₁)) := by
  have hK' : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by rcases hK with rfl | rfl <;> simp
  obtain ⟨hN, hds⟩ := hs.fused.p66.2.2.1 K hK'
  refine ⟨hN, ?_⟩
  rcases hds with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact not_isCyclic_of_isDihedralTwoGroup hn
  · exact not_isCyclic_of_isSemidihedralTwoGroup hn

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
