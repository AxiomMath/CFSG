module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma24

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

theorem exists_mem_ne_ne' [Finite G] {T : Subgroup G} (hT : 3 ≤ Nat.card T) (a b : G) :
    ∃ c ∈ T, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (T : Set G) ⊆ {a, b} := by
    intro c hc
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hcon c hc hca)
  have h1 : Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq _
  have h2 : (T : Set G).ncard ≤ ({a, b} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({a, b} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
  omega

theorem dihedral_center_cases : ∀ c : DihedralGroup 4, (∀ x : DihedralGroup 4, c * x = x * c) →
    c = 1 ∨ c = DihedralGroup.r 2 := by
  decide

theorem dihedral_mul_cases : ∀ a b : DihedralGroup 4, a ≠ 1 → b ≠ 1 → a ≠ b →
    a ≠ DihedralGroup.r 2 → b ≠ DihedralGroup.r 2 → a * a ≠ DihedralGroup.r 2 →
    b * b ≠ DihedralGroup.r 2 →
    a * b = DihedralGroup.r 2 ∨ a * b * (a * b) = DihedralGroup.r 2 := by
  decide

theorem dihedral_r_two_mem {V : Subgroup (DihedralGroup 4)} (hV : 4 ≤ Nat.card V) :
    DihedralGroup.r 2 ∈ V := by
  by_contra h
  have hsq : ∀ x ∈ V, x * x ≠ DihedralGroup.r 2 := fun x hx e => h (e ▸ mul_mem hx hx)
  obtain ⟨a, haV, ha1, ha2⟩ := exists_mem_ne_ne' (T := V) (by omega) 1 (DihedralGroup.r 2)
  obtain ⟨b, hbV, hb1, hba⟩ := exists_mem_ne_ne' (T := V) (by omega) 1 a
  have hb2 : b ≠ DihedralGroup.r 2 := fun e => h (e ▸ hbV)
  rcases dihedral_mul_cases a b ha1 hb1 hba.symm ha2 hb2 (hsq a haV) (hsq b hbV) with e | e
  · exact h (e ▸ mul_mem haV hbV)
  · exact h (e ▸ mul_mem (mul_mem haV hbV) (mul_mem haV hbV))

variable {P : Subgroup G}

@[expose] noncomputable def dihedralCenter (e : P ≃* DihedralGroup 4) : G :=
  ((e.symm (DihedralGroup.r 2) : P) : G)

theorem dihedralCenter_ne_one (e : P ≃* DihedralGroup 4) : dihedralCenter e ≠ 1 := by
  intro h
  have h1 : e.symm (DihedralGroup.r 2) = 1 := Subtype.ext h
  have h2 : (DihedralGroup.r 2 : DihedralGroup 4) = 1 := by
    rw [← e.apply_symm_apply (DihedralGroup.r 2), h1, map_one]
  exact absurd h2 (by decide)

theorem eq_of_central (e : P ≃* DihedralGroup 4) {u : G} (huP : u ∈ P)
    (hu : ∀ s ∈ P, u * s = s * u) : u = 1 ∨ u = dihedralCenter e := by
  have hc : ∀ x : DihedralGroup 4, e ⟨u, huP⟩ * x = x * e ⟨u, huP⟩ := fun x => by
    have h1 := hu (e.symm x : P) (e.symm x).2
    have h2 : (⟨u, huP⟩ : P) * e.symm x = e.symm x * ⟨u, huP⟩ := Subtype.ext h1
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, e.apply_symm_apply] at h3
  rcases dihedral_center_cases _ hc with h | h
  · left
    have h1 : (⟨u, huP⟩ : P) = 1 := by rw [← map_one e.symm, ← h, e.symm_apply_apply]
    exact congrArg Subtype.val h1
  · right
    have h1 : (⟨u, huP⟩ : P) = e.symm (DihedralGroup.r 2) := by rw [← h, e.symm_apply_apply]
    exact congrArg Subtype.val h1

theorem dihedralCenter_mem_of_le (e : P ≃* DihedralGroup 4) {V : Subgroup G} (hVP : V ≤ P)
    (hV : 4 ≤ Nat.card V) : dihedralCenter e ∈ V := by
  set V' := (V.subgroupOf P).map e.toMonoidHom with hV'
  have hcard : Nat.card V' = Nat.card V := by
    rw [hV', card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv]
  have h1 := dihedral_r_two_mem (V := V') (by rw [hcard]; exact hV)
  obtain ⟨v, hv, hve⟩ := h1
  have h2 : v = e.symm (DihedralGroup.r 2) := by
    rw [← hve]
    exact (e.symm_apply_apply v).symm
  show ((e.symm (DihedralGroup.r 2) : P) : G) ∈ V
  rw [← h2]
  exact hv

namespace Setting

variable {K R S : Subgroup G} [Finite G]

theorem normal_or_cyclic (h : Setting K R S) (hRP : R ≤ P) (hPS : P ≤ S) (hP8 : Nat.card P ∣ 8)
    (hcen : ∀ u ∈ P, (∀ s ∈ P, u * s = s * u) → u ∈ R) (Q : Subgroup G) [hQn : Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hQP : Q ≤ P) (hQ1 : Q ≠ ⊥) :
    R.Normal ∨ ∃ U : Subgroup G, U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2 ∧
      IsMulCommutative (normalClosure (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := by
    obtain ⟨k, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card P ∣ 2 ^ 3 from hP8)
    exact IsPGroup.of_card hk.2
  have hQPn : P ≤ normalizer (Q : Set G) := by
    rw [normalizer_eq_top_iff.mpr hQn]
    exact le_top
  obtain ⟨⟨u, hu⟩, hu1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (inf_center_ne_bot' hP2 hQP hQPn hQ1)
  have huQ : u ∈ Q := (mem_inf.mp hu).1
  have huc : ∀ s ∈ P, s * u = u * s :=
    fun s hs => mem_centralizer_iff.mp (mem_inf.mp (mem_inf.mp hu).2).2 s hs
  have huR : u ∈ R := hcen u (hQP huQ) fun s hs => (huc s hs).symm
  have hu1' : u ≠ 1 := fun e => hu1 (Subtype.ext e)
  by_cases hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  ·
    right
    refine ⟨zpowers u, zpowers_le.mpr huR, inferInstance, ?_, ?_⟩
    · have hu2 : u ^ 2 = 1 := h.elem.2 u huR
      have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1'
      have hU : Nat.card (zpowers u) = 2 := by rw [Nat.card_zpowers, hord]
      have h1 := card_mul_index ((zpowers u).subgroupOf R)
      rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr huR)).toEquiv, hU, h.card] at h1
      change ((zpowers u).subgroupOf R).index = 2
      omega
    · have hle : normalClosure ((zpowers u : Subgroup G) : Set G) ≤ Q :=
        normalClosure_le_normal (zpowers_le.mpr huQ)
      exact ⟨⟨fun a b => Subtype.ext (hQab a (hle a.2) b (hle b.2))⟩⟩
  ·
    left
    have hQ8 : Nat.card Q = 8 := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      have hdvd : 2 ^ k ∣ 2 ^ 3 := hk ▸ (card_dvd_of_le hQP).trans hP8
      have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
      by_contra h8
      have hk2 : k ≤ 2 := by
        by_contra hk2
        exact h8 (by rw [hk, show k = 3 by omega]; norm_num)
      apply hQab
      intro a ha b hb
      have hab : (⟨a, ha⟩ : Q) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        interval_cases k
        · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by rw [hk]; rfl)).1
          exact Subsingleton.elim _ _
        · have : IsCyclic Q := isCyclic_of_prime_card (p := 2) (by rw [hk]; norm_num)
          obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
          obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
          obtain ⟨j, hj⟩ := hg ⟨b, hb⟩
          rw [← hi, ← hj]
          exact (Commute.zpow_zpow_self g i j).eq
        · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := Q) hk
          exact this.is_comm.comm _ _
      exact congrArg Subtype.val hab
    have hQPeq : Q = P := eq_of_le_of_card_ge hQP (by
      rw [hQ8]
      exact Nat.le_of_dvd (by norm_num) hP8)
    have hRQ : R ≤ Q := hQPeq ▸ hRP
    have hQS : Q ≤ S := hQP.trans hPS
    constructor
    intro r hr g
    have h1 : rightConjugate R g⁻¹ ≤ S := fun x hx => by
      rw [mem_rightConjugate_iff, inv_inv] at hx
      have h2 : g⁻¹ * x * g ∈ Q := hRQ hx
      have h3 := hQn.conj_mem _ h2 g
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e] at h3
      exact hQS h3
    have h4 := h.wc g⁻¹ h1
    have h5 : g * r * g⁻¹ ∈ rightConjugate R g⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      have e : g⁻¹ * (g * r * g⁻¹) * g = r := by group
      rw [e]
      exact hr
    rw [h4] at h5
    exact h5

end Setting

end CFSG.ComponentClassification.Asc76X.Thm3Four
