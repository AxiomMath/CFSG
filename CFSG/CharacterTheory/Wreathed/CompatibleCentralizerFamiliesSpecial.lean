module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesSupport

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

universe u

variable {G : Type u} [Group G]

structure LocalConfig (J J₁ η : G) : Prop where
  sq : J * J = 1
  sq₁ : J₁ * J₁ = 1
  ne_one : J ≠ 1
  ne_one₁ : J₁ ≠ 1
  ne : J ≠ J₁
  comm : J * J₁ = J₁ * J
  conj_eq : ∀ y : G, orderOf y = 2 → ∃ g : G, g⁻¹ * y * g = J
  conj_eq₁ : ∀ y ∈ Subgroup.centralizer {J}, orderOf y = 2 → y ≠ J →
    ∃ c ∈ Subgroup.centralizer {J}, c⁻¹ * y * c = J₁
  involution_mem : ∀ y ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G),
    orderOf y = 2 → y ∈ Subgroup.closure {J, J₁}
  eta_mem : η ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G)
  eta_cycle : ∀ t ∈ Subgroup.closure {J, J₁}, t ≠ 1 → ∃ j : ℕ, (η ^ j)⁻¹ * t * η ^ j = J

namespace LocalConfig

variable {J J₁ η : G} (cfg : LocalConfig J J₁ η)
include cfg

omit cfg in
theorem mem_left : J ∈ Subgroup.closure {J, J₁} :=
  Subgroup.subset_closure (Set.mem_insert _ _)

omit cfg in
theorem mem_right : J₁ ∈ Subgroup.closure {J, J₁} :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem orderOf_of_mem {t : G} (ht : t ∈ Subgroup.closure {J, J₁}) (ht1 : t ≠ 1) :
    orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime _ ht1
  rw [pow_two]
  rcases mem_four_cases cfg.sq cfg.sq₁ cfg.comm ht with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact cfg.sq
  · exact cfg.sq₁
  · calc J * J₁ * (J * J₁) = J * (J₁ * J) * J₁ := by simp only [mul_assoc]
      _ = J * (J * J₁) * J₁ := by rw [cfg.comm]
      _ = 1 := by rw [← mul_assoc, cfg.sq, one_mul, cfg.sq₁]

theorem orderOf_eq : orderOf J = 2 := cfg.orderOf_of_mem mem_left cfg.ne_one

theorem orderOf_eq₁ : orderOf J₁ = 2 := cfg.orderOf_of_mem mem_right cfg.ne_one₁

theorem le_of_two {Q : Subgroup G} {y y' : G} (hy : y ∈ Subgroup.closure {J, J₁})
    (hy' : y' ∈ Subgroup.closure {J, J₁}) (hy1 : y ≠ 1) (hy'1 : y' ≠ 1) (hne : y ≠ y')
    (hyQ : y ∈ Q) (hy'Q : y' ∈ Q) : Subgroup.closure {J, J₁} ≤ Q := by
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right cfg.sq
  have hJ₁inv : J₁⁻¹ = J₁ := inv_eq_of_mul_eq_one_right cfg.sq₁
  have hboth : J ∈ Q ∧ J₁ ∈ Q := by
    rcases mem_four_cases cfg.sq cfg.sq₁ cfg.comm hy with rfl | rfl | rfl | rfl <;>
      rcases mem_four_cases cfg.sq cfg.sq₁ cfg.comm hy' with rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hy1
      | exact absurd rfl hy'1
      | exact absurd rfl hne
      | skip
    · exact ⟨hyQ, hy'Q⟩
    · refine ⟨hyQ, ?_⟩
      have h := Q.mul_mem (Q.inv_mem hyQ) hy'Q
      rwa [hJinv, ← mul_assoc, cfg.sq, one_mul] at h
    · exact ⟨hy'Q, hyQ⟩
    · refine ⟨?_, hyQ⟩
      have h := Q.mul_mem hy'Q (Q.inv_mem hyQ)
      rwa [hJ₁inv, mul_assoc, cfg.sq₁, mul_one] at h
    · refine ⟨hy'Q, ?_⟩
      have h := Q.mul_mem (Q.inv_mem hy'Q) hyQ
      rwa [hJinv, ← mul_assoc, cfg.sq, one_mul] at h
    · refine ⟨?_, hy'Q⟩
      have h := Q.mul_mem hyQ (Q.inv_mem hy'Q)
      rwa [hJ₁inv, mul_assoc, cfg.sq₁, mul_one] at h
  rw [Subgroup.closure_le]
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz <;> rw [hz]
  · exact hboth.1
  · exact hboth.2

omit cfg in
theorem centralizer_le : Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) ≤
    Subgroup.centralizer {J} :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr mem_left)

omit cfg in
theorem conj_mem_centralizer {T : Subgroup G} {h c : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    h⁻¹ * c * h ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : h * t * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hh t).mp ht
  have hct := Subgroup.mem_centralizer_iff.mp hc _ ht'
  calc t * (h⁻¹ * c * h) = h⁻¹ * ((h * t * h⁻¹) * c) * h := by group
    _ = h⁻¹ * (c * (h * t * h⁻¹)) * h := by rw [hct]
    _ = h⁻¹ * c * h * t := by group

theorem le_center_conj {Q : Subgroup G} {h : G}
    (hT : Subgroup.closure {J, J₁} ≤ Q ⊓ Subgroup.centralizer (Q : Set G))
    (hsp : IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj h⁻¹).toMonoidHom)) :
    Subgroup.closure {J, J₁} ≤ Q.map (MulAut.conj h⁻¹).toMonoidHom ⊓
      Subgroup.centralizer (Q.map (MulAut.conj h⁻¹).toMonoidHom : Set G) := by
  rcases hsp with ⟨-, huniq⟩ | h4
  · exfalso
    have h1 := huniq _ (conj_mem_center_conj (hT mem_left))
      ((orderOf_conj h J).trans cfg.orderOf_eq)
    have h2 := huniq _ (conj_mem_center_conj (hT mem_right))
      ((orderOf_conj h J₁).trans cfg.orderOf_eq₁)
    apply cfg.ne
    have h3 : h⁻¹ * J * h = h⁻¹ * J₁ * h := h1.trans h2.symm
    simpa using h3
  · exact h4

theorem mem_normalizer_of_le_center [Finite G] {Q : Subgroup G} {h : G}
    (hT : Subgroup.closure {J, J₁} ≤ Q ⊓ Subgroup.centralizer (Q : Set G))
    (hT' : Subgroup.closure {J, J₁} ≤ Q.map (MulAut.conj h⁻¹).toMonoidHom ⊓
      Subgroup.centralizer (Q.map (MulAut.conj h⁻¹).toMonoidHom : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G) := by
  set T := Subgroup.closure {J, J₁}
  have hle : T.map (MulAut.conj h⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    change h⁻¹ * t * h⁻¹⁻¹ ∈ T
    rw [inv_inv]
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, inv_mul_cancel]
      exact T.one_mem
    · apply cfg.involution_mem
      · exact le_centralizer_of_le_center hT' (conj_mem_conj (hT ht).1)
      · rw [orderOf_conj]
        exact cfg.orderOf_of_mem ht ht1
  have heq : T.map (MulAut.conj h⁻¹).toMonoidHom = T := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
  have hmem : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq
  simpa using (Subgroup.normalizer (T : Set G)).inv_mem hmem

theorem exists_isSpecial_conj [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    ∃ k : G, IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj k⁻¹).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyZ, hy2⟩ := exists_center_orderOf_eq hQ hQ1
  obtain ⟨g, hg⟩ := cfg.conj_eq y hy2
  set Q₁ := Q.map (MulAut.conj g⁻¹).toMonoidHom
  have hJ : J ∈ Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) := by
    rw [← hg]
    exact conj_mem_center_conj hyZ
  by_cases huniq : ∀ y' ∈ Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G), orderOf y' = 2 → y' = J
  · exact ⟨g, Or.inl ⟨hJ, huniq⟩⟩
  · push Not at huniq
    obtain ⟨y', hy'Z, hy'2, hy'J⟩ := huniq
    have hy'N : y' ∈ Subgroup.centralizer {J} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy'Z.2 J hJ.1).symm
    obtain ⟨c, hcN, hc⟩ := cfg.conj_eq₁ y' hy'N hy'2 hy'J
    refine ⟨g * c, Or.inr ?_⟩
    rw [← map_conj_map_conj, Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · have hcJ : c⁻¹ * J * c = J := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hcN
        rw [mul_assoc, ← h, inv_mul_cancel_left]
      rw [SetLike.mem_coe, ← hcJ]
      exact conj_mem_center_conj hJ
    · rw [SetLike.mem_coe, ← hc]
      exact conj_mem_center_conj hy'Z

theorem extend_conj_eq [Finite G] {lam : Subgroup.centralizer {J} →* ℂˣ}
    (hinv : ∀ h ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G),
      ∀ c ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G),
        extend _ lam (h⁻¹ * c * h) = extend _ lam c)
    {Q : Subgroup G} {h g : G} (hsp : IsSpecial J (Subgroup.closure {J, J₁}) Q)
    (hsp' : IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj h⁻¹).toMonoidHom))
    (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    extend _ lam (h⁻¹ * g * h) = extend _ lam g := by
  by_cases hT : Subgroup.closure {J, J₁} ≤ Q ⊓ Subgroup.centralizer (Q : Set G)
  · have hT' := cfg.le_center_conj hT hsp'
    exact hinv h (cfg.mem_normalizer_of_le_center hT hT') g (centralizer_le_of_le_center hT hg)
  · have hsp1 := hsp.resolve_right hT
    have hT' : ¬ Subgroup.closure {J, J₁} ≤ Q.map (MulAut.conj h⁻¹).toMonoidHom ⊓
        Subgroup.centralizer (Q.map (MulAut.conj h⁻¹).toMonoidHom : Set G) := by
      intro hT'
      apply hT
      have h4 := cfg.le_center_conj hT' (h := h⁻¹) (by rw [map_conj_inv_map_conj]; exact hsp)
      rwa [map_conj_inv_map_conj] at h4
    have hsp1' := hsp'.resolve_right hT'
    have hJh : h⁻¹ * J * h = J :=
      hsp1'.2 _ (conj_mem_center_conj hsp1.1) ((orderOf_conj h J).trans cfg.orderOf_eq)
    have hhN : h ∈ Subgroup.centralizer {J} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * J = h * (h⁻¹ * J * h) := by rw [hJh]
        _ = J * h := by group
    have hgN : g ∈ Subgroup.centralizer {J} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsp1.1.1) hg
    exact extend_conj hhN hgN

theorem exists_isSpecial_eta_conj [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) (hQC : Q ≤ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G))
    (hns : ¬ IsSpecial J (Subgroup.closure {J, J₁}) Q) :
    ∃ j : ℕ, IsSpecial J (Subgroup.closure {J, J₁})
      (Q.map (MulAut.conj (η ^ j)⁻¹).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := Subgroup.closure {J, J₁}
  obtain ⟨y₀, hy₀Z, hy₀2⟩ := exists_center_orderOf_eq hQ hQ1
  have hy₀T : y₀ ∈ T := cfg.involution_mem y₀ (hQC hy₀Z.1) hy₀2
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy₀2
    omega
  have hTQ : T ≤ Subgroup.centralizer (Q : Set G) := Subgroup.le_centralizer_iff.mp hQC
  have huniq : ∀ y ∈ Q, orderOf y = 2 → y = y₀ := by
    intro y hy hy2
    by_contra hne
    have hyT : y ∈ T := cfg.involution_mem y (hQC hy) hy2
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy2
      omega
    exact hns (Or.inr (le_inf (cfg.le_of_two hyT hy₀T hy1 hy₀1 hne hy hy₀Z.1) hTQ))
  obtain ⟨j, hj⟩ := cfg.eta_cycle y₀ hy₀T hy₀1
  have hηj : η ^ j ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ cfg.eta_mem j
  refine ⟨j, Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [← hj]
    exact conj_mem_conj hy₀Z.1
  · change J ∈ Subgroup.centralizer
      ((Q.map (MulAut.conj (η ^ j)⁻¹).toMonoidHom : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have hqC : (η ^ j)⁻¹ * q * η ^ j ∈ Subgroup.centralizer (T : Set G) :=
      conj_mem_centralizer hηj (hQC hq)
    have h' := Subgroup.mem_centralizer_iff.mp hqC J mem_left
    change ((η ^ j)⁻¹ * q * (η ^ j)⁻¹⁻¹) * J = J * ((η ^ j)⁻¹ * q * (η ^ j)⁻¹⁻¹)
    rw [inv_inv]
    exact h'.symm
  · intro y' hy'Z hy'2
    have hy' : η ^ j * y' * (η ^ j)⁻¹ ∈ Q := mem_conj_iff.mp hy'Z.1
    have hy'0 := huniq _ hy' (by
      rw [show η ^ j * y' * (η ^ j)⁻¹ = (η ^ j)⁻¹⁻¹ * y' * (η ^ j)⁻¹ by rw [inv_inv],
        orderOf_conj]
      exact hy'2)
    rw [← hj, ← hy'0]
    group

omit cfg in
theorem exists_center_involution_ne [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) (hns : ¬ IsSpecial J (Subgroup.closure {J, J₁}) Q) :
    ∃ y ∈ Q ⊓ Subgroup.centralizer (Q : Set G), orderOf y = 2 ∧ y ≠ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₀, hy₀Z, hy₀2⟩ := exists_center_orderOf_eq hQ hQ1
  by_cases hy₀J : y₀ = J
  · rw [hy₀J] at hy₀Z
    by_contra hne
    push Not at hne
    exact hns (Or.inl ⟨hy₀Z, fun y hy hy2 => hne y hy hy2⟩)
  · exact ⟨y₀, hy₀Z, hy₀2, hy₀J⟩

end LocalConfig

end CFSG.Wreathed.CompatibleFamilies
