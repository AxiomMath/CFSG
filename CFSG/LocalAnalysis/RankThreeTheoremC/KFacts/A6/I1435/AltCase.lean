module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Common

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Subgroup CFSG.Open Equiv

theorem comm_of_card_le_three {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 3) (a b : G) :
    a * b = b * a := by
  have hpos := Nat.card_pos (α := G)
  have hcyc : Nat.card G = 1 ∨ IsCyclic G := by
    rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3) with h1 | h2 | h3
    · exact Or.inl h1
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Or.inr (isCyclic_of_prime_card h2)
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact Or.inr (isCyclic_of_prime_card h3)
  rcases hcyc with h1 | hc
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg⟩ := hc.exists_generator
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm]

theorem card_alt {n : ℕ} (hn : 2 ≤ n) : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

section Alt

variable {X : Type} [Group X] [Finite X]

theorem three_dvd_card_alt {K : Subgroup X} (hnab : ∃ a b : ↥K, a * b ≠ b * a) {n : ℕ}
    (ψ : ↥K ≃* alternatingGroup (Fin n)) : 3 ∣ Nat.card K := by
  rw [Nat.card_congr ψ.toEquiv]
  by_cases hn : 3 ≤ n
  · rw [card_alt (by omega)]
    have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hk] at h3
    exact (Nat.Coprime.dvd_mul_left (by norm_num)).mp h3
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply comm_of_card_le_three
    rw [Nat.card_congr ψ.toEquiv]
    by_cases h2 : 2 ≤ n
    · rw [card_alt h2]
      interval_cases n <;> decide
    · calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Perm (Fin n)) :=
            card_le_card_group _
        _ = n.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        _ ≤ 3 := by interval_cases n <;> decide

theorem nine_le_of_alt {K : Subgroup X} {P : Sylow 3 X} (e : ↥(P : Subgroup X) ≃* W3) {n : ℕ}
    (ψ : ↥K ≃* alternatingGroup (Fin n)) (hEK : Open.thompsonSubgroup (P : Subgroup X) ≤ K) :
    9 ≤ n ∧ n ≤ 11 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27 : 27 ∣ Nat.card K := by
    have := card_dvd_of_le hEK
    rwa [thompsonSubgroup_eq_baseIn e, card_baseIn] at this
  have h243 : ¬ 3 ^ 5 ∣ Nat.card K := by
    intro h
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 h
    have hc : Nat.card (H.map K.subtype) = 3 ^ 5 := by
      rw [card_map_of_injective K.subtype_injective, hH]
    have hp : IsPGroup 3 (H.map K.subtype) := IsPGroup.of_card hc
    have := card_dvd_of_isPGroup e hp
    rw [hc] at this
    norm_num at this
  rw [Nat.card_congr ψ.toEquiv] at h27 h243
  by_cases hlo : n ≤ 8
  · exfalso
    by_cases h2 : 2 ≤ n
    · rw [card_alt h2] at h27
      interval_cases n <;> norm_num [Nat.factorial] at h27
    · have hle : Nat.card (alternatingGroup (Fin n)) ≤ 1 := by
        calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Perm (Fin n)) :=
              card_le_card_group _
          _ = n.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
          _ ≤ 1 := by interval_cases n <;> decide
      have := Nat.le_of_dvd (Nat.card_pos) h27
      omega
  · refine ⟨by omega, ?_⟩
    by_contra hhi
    apply h243
    rw [card_alt (by omega)]
    have h12 : (12 : ℕ).factorial ∣ n.factorial := Nat.factorial_dvd_factorial (by omega)
    have h486 : 3 ^ 5 * 2 ∣ n.factorial := (by decide : 3 ^ 5 * 2 ∣ (12 : ℕ).factorial).trans h12
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hk, mul_comm 2 k] at h486
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h486

theorem card_alt_eq {n : ℕ} (h9 : 9 ≤ n) (h11 : n ≤ 11) :
    ∃ m, ¬ 3 ∣ m ∧ Nat.card (alternatingGroup (Fin n)) = 81 * m := by
  rw [card_alt (by omega)]
  interval_cases n
  · exact ⟨2240, by norm_num, by decide⟩
  · exact ⟨22400, by norm_num, by decide⟩
  · exact ⟨246400, by norm_num, by decide⟩

theorem sylow_alt_W3 {n : ℕ} (h9 : 9 ≤ n) (h11 : n ≤ 11) (Q : Sylow 3 (alternatingGroup (Fin n))) :
    Nonempty (↥(Q : Subgroup (alternatingGroup (Fin n))) ≃* W3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm, hcard⟩ := card_alt_eq h9 h11
  have hc : Nat.card (phiAlt n h9).range =
      3 ^ (Nat.card (alternatingGroup (Fin n))).factorization 3 := by
    rw [hcard, factorization_three hm, ← Nat.card_congr
      (MonoidHom.ofInjective (phiAlt_injective n h9)).toEquiv, card_W3]
    norm_num
  let P₀ : Sylow 3 (alternatingGroup (Fin n)) := Sylow.ofCard _ hc
  exact ⟨(Sylow.equiv Q P₀).trans (MonoidHom.ofInjective (phiAlt_injective n h9)).symm⟩

theorem false_of_alternating {K : Subgroup X} (hKn : K.Normal)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) {P : Sylow 3 X} (e : ↥(P : Subgroup X) ≃* W3) {n : ℕ}
    (ψ : ↥K ≃* alternatingGroup (Fin n)) {x : X}
    (hxJ : x ∈ Open.thompsonSubgroup (P : Subgroup X)) (hx1 : x ≠ 1)
    (hlines : conjLinesIn (Open.thompsonSubgroup (P : Subgroup X)) x = 3)
    (hd1 : ∀ D : Subgroup X, D ≤ Open.thompsonSubgroup (P : Subgroup X) →
      (∀ g ∈ normalizer (Open.thompsonSubgroup (P : Subgroup X) : Set X), ∀ d ∈ D,
        g * d * g⁻¹ ∈ D) →
        D = ⊥ ∨ D = Open.thompsonSubgroup (P : Subgroup X))
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X))) : False := by
  set E := Open.thompsonSubgroup (P : Subgroup X) with hE
  have hEK : E ≤ K := thompson_le_of_three_dvd hKn e hd1 (three_dvd_card_alt hnab ψ)
  have hxK : x ∈ K := hEK hxJ
  obtain ⟨h9, h11⟩ := nine_le_of_alt e ψ hEK
  have hEB : E = baseIn e := thompsonSubgroup_eq_baseIn e
  set L := alternatingGroup (Fin n)
  set F : Subgroup L := (E.subgroupOf K).map ψ.toMonoidHom with hF
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [SetLike.mem_coe, mem_subgroupOf, hEB] at ha hb
    exact baseIn_comm e ha hb
  have hFcard : Nat.card F = 27 := by
    rw [hF, card_map_of_injective ψ.injective, Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv,
      hEB, card_baseIn]
  have hF₀c : ∀ a ∈ (betaAlt n h9).range, ∀ b ∈ (betaAlt n h9).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hF₀card : Nat.card (betaAlt n h9).range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (betaAlt_injective n h9)).toEquiv, Nat.card_fun,
      card_M3]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_eq (sylow_alt_W3 h9 h11) hFc hF₀c hFcard hF₀card
  set ψ' : ↥K ≃* L := ψ.trans (MulAut.conj g⁻¹) with hψ'
  have hF' : (E.subgroupOf K).map ψ'.toMonoidHom = (betaAlt n h9).range := map_trans_conj ψ _ hg
  have hxB : ψ' ⟨x, hxK⟩ ∈ (betaAlt n h9).range := by
    rw [← hF']
    exact mem_map_of_mem _ (show (⟨x, hxK⟩ : ↥K) ∈ E.subgroupOf K from hxJ)
  obtain ⟨f, hf⟩ := hxB
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [map_one] at hf
    have : (⟨x, hxK⟩ : ↥K) = 1 := ψ'.injective (by rw [← hf, map_one])
    exact hx1 (congrArg Subtype.val this)
  rcases alt_check f hf1 with ⟨q₀, -, hsupp⟩ | hld
  ·
    let F₁ : alternatingGroup (offBlock q₀) →* L :=
      ((iotaΩ n h9).comp (Perm.ofSubtype.comp (alternatingGroup (offBlock q₀)).subtype)).codRestrict
        _ fun σ => by
          rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, sign_iotaΩ, MonoidHom.comp_apply,
            Perm.sign_ofSubtype]
          exact Perm.mem_alternatingGroup.mp σ.2
    have hF₁ : Function.Injective F₁ := by
      intro a b h
      apply Subtype.ext
      apply Perm.ofSubtype_injective
      apply iotaΩ_injective n h9
      exact congrArg Subtype.val h
    set H : Subgroup ↥K := F₁.range.map ψ'.symm.toMonoidHom
    have hH : H ≤ centralizer ({⟨x, hxK⟩} : Set ↥K) := by
      rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      apply ψ'.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply, ← hf]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, F₁, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
        Subgroup.coe_subtype, coe_betaAlt, ← map_mul]
      rw [commute_ofSubtype hsupp]
    have hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥H := by
      intro hs
      apply not_isPSolvable_altSix q₀
      exact isPSolvable_of_equiv
        (((equivMapOfInjective F₁.range ψ'.symm.toMonoidHom ψ'.symm.injective).symm).trans
          (MonoidHom.ofInjective hF₁).symm) hs
    exact not_isPSolvable_centralizer hxK H hH hns hsolv
  ·
    have hact : ∀ i : Fin 4, ψ' (ψ'.symm (altOf n h9 (cperm (pick f i)) (sign_cperm _)) *
        ⟨x, hxK⟩ * (ψ'.symm (altOf n h9 (cperm (pick f i)) (sign_cperm _)))⁻¹) =
          betaAlt n h9 (cact (pick f i) f) := by
      intro i
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hf]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, altOf, coe_betaAlt, ← map_mul, ← map_inv]
      rw [cperm_conj]
    refine conjLinesIn_ne_three hEK ψ'.toMonoidHom ψ'.injective hxK
      (fun i => ψ'.symm (altOf n h9 (cperm (pick f i)) (sign_cperm _))) (fun i => ?_)
      (fun i j hij => ?_) hlines
    · show ψ' _ ∈ (E.subgroupOf K).map ψ'.toMonoidHom
      rw [hact i, hF']
      exact ⟨_, rfl⟩
    · change zpowers (ψ' _) = zpowers (ψ' _) at hij
      rw [hact i, hact j] at hij
      by_contra hne
      obtain ⟨d1, d2, d3⟩ := hld i j hne
      rcases eq_of_zpowers_betaAlt n h9 hij with h | h | h
      · exact d1 h
      · exact d2 h
      · exact d3 h

end Alt

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
