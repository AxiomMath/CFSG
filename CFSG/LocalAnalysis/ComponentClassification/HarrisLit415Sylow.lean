module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Prod

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

namespace L415

theorem eq_of_mem_center_dihedral {D : Type*} [Group D] {m : ℕ}
    (e : D ≃* DihedralGroup (2 ^ m)) (hm : 2 ≤ m) {z x : D} (hz : z ∈ center D) (hz1 : z ≠ 1)
    (hx : x ∈ center D) : x = 1 ∨ x = z := by
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hc := DihedralGroup.center_eq_closure_of_even_ne_two (n := 2 ^ m)
    ((Nat.even_pow' (by omega)).mpr even_two) (by omega)
  set c : DihedralGroup (2 ^ m) := DihedralGroup.r ((2 ^ m / 2 : ℕ) : ZMod (2 ^ m)) with hcdef
  have hc2 : c ^ 2 = 1 := by
    rw [sq, hcdef, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero]
    congr 1
    rw [← Nat.cast_add, ← two_mul, Nat.mul_div_cancel' (dvd_pow_self 2 (by omega)),
      ZMod.natCast_self]
  have key : ∀ y ∈ center D, y = 1 ∨ y = e.symm c := by
    intro y hy
    have hy' : e y ∈ center (DihedralGroup (2 ^ m)) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨y, hy, rfl⟩
    rw [hc, mem_zpowers_iff] at hy'
    obtain ⟨k, hk⟩ := hy'
    obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      apply e.injective
      rw [← hk, map_one, zpow_mul, zpow_two, ← sq, hc2, one_zpow]
    · right
      apply e.injective
      rw [← hk, MulEquiv.apply_symm_apply, zpow_add_one, zpow_mul, zpow_two, ← sq, hc2,
        one_zpow, one_mul]
  rcases key z hz with h1 | h1
  · exact absurd h1 hz1
  rcases key x hx with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (h2.trans h1.symm)

variable {G : Type*} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

namespace IsProd

variable (h : IsProd E K₁ K₂ s)
include h

theorem le_normalizer₁ : E ≤ normalizer (K₁ : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h.conj_mem_K₁_of_mem hx hk, fun hk => ?_⟩
  have := h.conj_mem_K₁_of_mem (inv_mem hx) hk
  simpa [mul_assoc] using this

theorem le_normalizer₂ : E ≤ normalizer (K₂ : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h.conj_mem_K₂_of_mem hx hk, fun hk => ?_⟩
  have := h.conj_mem_K₂_of_mem (inv_mem hx) hk
  simpa [mul_assoc] using this

variable {P : Subgroup G} (hE : E.Normal) (hP : IsSylowOf 2 P ⊤)
include hE hP

omit h in
theorem isSylowOf_inf_E : IsSylowOf 2 (P ⊓ E) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hP.inf_of_le_normalizer le_top fun g _ => ?_
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hE.conj_mem x hx g, fun hx => ?_⟩
  have := hE.conj_mem _ hx g⁻¹
  simpa [mul_assoc] using this

theorem isSylowOf_inf_K₁ : IsSylowOf 2 (P ⊓ K₁) K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_inf_E hE hP).inf_of_le_normalizer h.K₁_le h.le_normalizer₁
  rwa [inf_assoc, inf_of_le_right h.K₁_le] at h1

theorem isSylowOf_inf_K₂ : IsSylowOf 2 (P ⊓ K₂) K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_inf_E hE hP).inf_of_le_normalizer h.K₂_le h.le_normalizer₂
  rwa [inf_assoc, inf_of_le_right h.K₂_le] at h1

theorem inf_E_eq : P ⊓ E = (P ⊓ K₁) ⊔ (P ⊓ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ a ∈ P ⊓ K₁, ∀ b ∈ P ⊓ K₂, a * b = b * a := fun a ha b hb => h.comm ha.2 hb.2
  have hbot : (P ⊓ K₁) ⊓ (P ⊓ K₂) = ⊥ := by
    rw [eq_bot_iff, ← h.inf_eq]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  obtain ⟨hcard, -⟩ := GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
  rw [hbot, Subgroup.card_bot, mul_one] at hcard
  obtain ⟨hE', -⟩ := GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ fun a ha b hb =>
    h.comm ha hb
  rw [h.inf_eq, Subgroup.card_bot, mul_one, h.sup_eq] at hE'
  have hle : (P ⊓ K₁) ⊔ (P ⊓ K₂) ≤ P ⊓ E :=
    sup_le (inf_le_inf_left _ h.K₁_le) (inf_le_inf_left _ h.K₂_le)
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, (isSylowOf_inf_E hE hP).card_eq, (h.isSylowOf_inf_K₁ hE hP).card_eq,
    (h.isSylowOf_inf_K₂ hE hP).card_eq, hE', Nat.factorization_mul Nat.card_pos.ne'
      Nat.card_pos.ne', Finsupp.add_apply, pow_add]

theorem exists_mul_inf {x : G} (hx : x ∈ P ⊓ E) :
    ∃ a ∈ P ⊓ K₁, ∃ b ∈ P ⊓ K₂, x = a * b := by
  obtain ⟨-, hset⟩ := GroupTheory.card_sup_mul_card_inf_of_commute (P ⊓ K₁) (P ⊓ K₂)
    fun a ha b hb => h.comm ha.2 hb.2
  have hx' : x ∈ (((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup G) : Set G) := by
    rw [← h.inf_E_eq hE hP]
    exact hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_diag (hs : s * s = 1) {x : G} (hx : x ∈ P ⊓ E) (hsx : s * x = x * s) :
    ∃ k ∈ P ⊓ K₁, x = k * (s⁻¹ * k * s) := by
  obtain ⟨k, rfl⟩ := (h.mem_centralizer_iff hs hx.2).mp hsx
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_inf hE hP hx
  rw [diag_apply] at hab
  obtain ⟨h1, -⟩ := h.eq_of_mul_eq k.2 ha.2 (h.conj_mem_K₂ k.2) hb.2 hab
  refine ⟨k, ?_, rfl⟩
  rw [h1]
  exact ha

theorem card_mul_le (hs : s * s = 1) {T : Subgroup G} (hTP : T ≤ P)
    (hTs : T ≤ centralizer {s}) : Nat.card ↥(P ⊓ K₁) * Nat.card T ≤ Nat.card P := by
  classical
  have hTE : Nat.card ↥(E ⊓ T) ≤ Nat.card ↥(P ⊓ K₁) := by
    have hsurj : ∀ x ∈ E ⊓ T, ∃ k ∈ P ⊓ K₁, x = k * (s⁻¹ * k * s) := fun x hx =>
      h.exists_diag hE hP hs ⟨hTP hx.2, hx.1⟩
        (mem_centralizer_singleton_iff.mp (hTs hx.2)).symm
    let f : ↥(E ⊓ T) → ↥(P ⊓ K₁) := fun x =>
      ⟨(hsurj x x.2).choose, (hsurj x x.2).choose_spec.1⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hx := (hsurj x x.2).choose_spec.2
      have hy := (hsurj y y.2).choose_spec.2
      have hxy' : (hsurj x x.2).choose = (hsurj y y.2).choose := congrArg Subtype.val hxy
      apply Subtype.ext
      rw [hx, hy, hxy']
    exact Nat.card_le_card_of_injective f hf
  have h1 := Subgroup.relIndex_mul_card (H := E) (K := P)
  have h2 := Subgroup.relIndex_mul_card (H := E) (K := T)
  have h3 : E.relIndex T ≤ E.relIndex P := by
    refine Subgroup.relIndex_le_of_le_right hTP fun h0 => ?_
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥P)).ne h1
  have hPE : Nat.card ↥(E ⊓ P) = Nat.card ↥(P ⊓ K₁) * Nat.card ↥(P ⊓ K₁) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [inf_comm, h.inf_E_eq hE hP]
    obtain ⟨hcard, -⟩ := GroupTheory.card_sup_mul_card_inf_of_commute (P ⊓ K₁) (P ⊓ K₂)
      fun a ha b hb => h.comm ha.2 hb.2
    have hbot : (P ⊓ K₁) ⊓ (P ⊓ K₂) = ⊥ := by
      rw [eq_bot_iff, ← h.inf_eq]
      exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    rw [hbot, Subgroup.card_bot, mul_one] at hcard
    rw [hcard, (h.isSylowOf_inf_K₁ hE hP).card_eq, (h.isSylowOf_inf_K₂ hE hP).card_eq,
      ← Nat.card_congr h.equivK₂.toEquiv]
  calc Nat.card ↥(P ⊓ K₁) * Nat.card T
      = Nat.card ↥(P ⊓ K₁) * (E.relIndex T * Nat.card ↥(E ⊓ T)) := by rw [h2]
    _ ≤ Nat.card ↥(P ⊓ K₁) * (E.relIndex P * Nat.card ↥(P ⊓ K₁)) := by
        gcongr
    _ = E.relIndex P * Nat.card ↥(E ⊓ P) := by rw [hPE]; ring
    _ = Nat.card P := h1

theorem exists_central (hs : s * s = 1) (hsP : s ∈ P) {D : Subgroup G}
    (hD : IsSylowOf 2 D (E ⊓ centralizer {s})) (hDP : D ≤ P) {m : ℕ} (hm : 2 ≤ m)
    (eD : ↥D ≃* DihedralGroup (2 ^ m)) {z : G} (hzD : z ∈ D) (hzc : ∀ d ∈ D, z * d = d * z)
    (hz1 : z ≠ 1) :
    ∃ z₁ ∈ P ⊓ K₁, z = z₁ * (s⁻¹ * z₁ * s) ∧ z₁ ≠ 1 ∧ z₁ ^ 2 = 1 ∧
      (∀ d ∈ P ⊓ K₁, z₁ * d = d * z₁) ∧
      ∀ c ∈ P ⊓ K₁, (∀ d ∈ P ⊓ K₁, c * d = d * c) → c = 1 ∨ c = z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPD : P ⊓ (E ⊓ centralizer {s}) = D :=
    hD.eq_of_le (le_inf hDP hD.le) inf_le_right (hP.isPGroup.to_le inf_le_left)
  have hdiagD : ∀ c (hc : c ∈ P ⊓ K₁), h.diag ⟨c, hc.2⟩ ∈ D := by
    intro c hc
    rw [← hPD]
    refine mem_inf.mpr ⟨mul_mem hc.1 (mul_mem (mul_mem (inv_mem hsP) hc.1) hsP),
      mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact mul_mem (h.K₁_le hc.2) (h.K₂_le (h.conj_mem_K₂ hc.2))
    · refine mem_centralizer_singleton_iff.mpr ?_
      exact ((h.mem_centralizer_iff hs (mul_mem (h.K₁_le hc.2)
        (h.K₂_le (h.conj_mem_K₂ hc.2)))).mpr ⟨⟨c, hc.2⟩, rfl⟩).symm
  have hDdiag : ∀ y ∈ D, ∃ d ∈ P ⊓ K₁, y = d * (s⁻¹ * d * s) := by
    intro y hy
    have hy' : y ∈ P ⊓ (E ⊓ centralizer {s}) := hPD ▸ hy
    exact h.exists_diag hE hP hs ⟨hy'.1, hy'.2.1⟩
      (mem_centralizer_singleton_iff.mp hy'.2.2).symm
  have hcenD : ∀ y ∈ D, (∀ d ∈ D, y * d = d * y) → y = 1 ∨ y = z := by
    intro y hy hyc
    have hz' : (⟨z, hzD⟩ : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    have hy' : (⟨y, hy⟩ : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => Subtype.ext (hyc g g.2).symm
    rcases eq_of_mem_center_dihedral eD hm hz' (fun h1 => hz1 (congrArg Subtype.val h1))
      hy' with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  have hzE : z ∈ P ⊓ E := by
    have := hPD ▸ hzD
    exact ⟨this.1, this.2.1⟩
  have hzs : s * z = z * s := (mem_centralizer_singleton_iff.mp (hD.le hzD).2).symm
  obtain ⟨z₁, hz₁, hzz⟩ := h.exists_diag hE hP hs hzE hzs
  have hδz : h.diag ⟨z₁, hz₁.2⟩ = z := hzz.symm
  have hmul : ∀ (a b : G) (ha : a ∈ K₁) (hb : b ∈ K₁),
      h.diag ⟨a * b, mul_mem ha hb⟩ = h.diag ⟨a, ha⟩ * h.diag ⟨b, hb⟩ := fun a b ha hb => by
    rw [← map_mul]
    rfl
  have hinj : ∀ (a b : G) (ha : a ∈ K₁) (hb : b ∈ K₁), h.diag ⟨a, ha⟩ = h.diag ⟨b, hb⟩ →
      a = b := fun a b ha hb hab => congrArg Subtype.val (h.diag_injective hab)
  have hz₁c : ∀ d ∈ P ⊓ K₁, z₁ * d = d * z₁ := by
    intro d hd
    refine hinj _ _ (mul_mem hz₁.2 hd.2) (mul_mem hd.2 hz₁.2) ?_
    rw [hmul _ _ hz₁.2 hd.2, hmul _ _ hd.2 hz₁.2, hδz]
    exact hzc _ (hdiagD d hd)
  have hz₁1 : z₁ ≠ 1 := by
    rintro rfl
    apply hz1
    rw [hzz]
    group
  have hcen : ∀ c ∈ P ⊓ K₁, (∀ d ∈ P ⊓ K₁, c * d = d * c) → c = 1 ∨ c = z₁ := by
    intro c hc hcc
    have hδc : h.diag ⟨c, hc.2⟩ ∈ D := hdiagD c hc
    have hδcc : ∀ y ∈ D, h.diag ⟨c, hc.2⟩ * y = y * h.diag ⟨c, hc.2⟩ := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := hDdiag y hy
      have h1 : h.diag ⟨d, hd.2⟩ = d * (s⁻¹ * d * s) := rfl
      rw [← h1, ← hmul _ _ hc.2 hd.2, ← hmul _ _ hd.2 hc.2]
      congr 2
      exact hcc d hd
    rcases hcenD _ hδc hδcc with h1 | h1
    · left
      have h2 : h.diag ⟨c, hc.2⟩ = h.diag ⟨1, one_mem _⟩ := by
        rw [h1]
        exact (map_one h.diag).symm
      exact hinj _ _ _ _ h2
    · right
      exact hinj _ _ _ _ (h1.trans hδz.symm)
  refine ⟨z₁, hz₁, hzz, hz₁1, ?_, hz₁c, hcen⟩
  rcases hcen z₁⁻¹ (mem_inf.mpr ⟨inv_mem hz₁.1, inv_mem hz₁.2⟩) (fun d hd => by
      have := hz₁c d hd
      calc z₁⁻¹ * d = z₁⁻¹ * (d * z₁) * z₁⁻¹ := by group
        _ = z₁⁻¹ * (z₁ * d) * z₁⁻¹ := by rw [this]
        _ = d * z₁⁻¹ := by group) with h1 | h1
  · exact absurd (inv_eq_one.mp h1) hz₁1
  · have h2 : z₁ * z₁⁻¹ = 1 := mul_inv_cancel z₁
    rw [h1] at h2
    rw [sq]
    exact h2

omit [Finite G] hE hP in
theorem conj_z₁ {z₁ : G} (hz₁ : z₁ ∈ P ⊓ K₁) (hz₁1 : z₁ ≠ 1)
    (hcen : ∀ c ∈ P ⊓ K₁, (∀ d ∈ P ⊓ K₁, c * d = d * c) → c = 1 ∨ c = z₁)
    (hz₁c : ∀ d ∈ P ⊓ K₁, z₁ * d = d * z₁) {g : G} (hg : g ∈ P) :
    (K₁.map (MulAut.conj g).toMonoidHom = K₁ → g * z₁ * g⁻¹ = z₁) ∧
      (K₁.map (MulAut.conj g).toMonoidHom = K₂ → g * z₁ * g⁻¹ ≠ z₁) := by
  refine ⟨fun hK => ?_, fun hK hc => ?_⟩
  · have hmem : ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁ := fun k hk => by
      rw [← hK]
      exact ⟨k, hk, rfl⟩
    have hmem' : ∀ k ∈ K₁, g⁻¹ * k * g ∈ K₁ := fun k hk => by
      rw [← hK] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      rw [← hkk]
      simpa [MulAut.conj_apply, mul_assoc] using hk'
    have hzP : g * z₁ * g⁻¹ ∈ P ⊓ K₁ :=
      mem_inf.mpr ⟨mul_mem (mul_mem hg hz₁.1) (inv_mem hg), hmem z₁ hz₁.2⟩
    rcases hcen _ hzP (fun d hd => by
        have hd' : g⁻¹ * d * g ∈ P ⊓ K₁ :=
          mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) hd.1) hg, hmem' d hd.2⟩
        have h1 := hz₁c _ hd'
        calc g * z₁ * g⁻¹ * d = g * (z₁ * (g⁻¹ * d * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * d * g) * z₁) * g⁻¹ := by rw [h1]
          _ = d * (g * z₁ * g⁻¹) := by group) with h1 | h1
    · exfalso
      apply hz₁1
      calc z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  · have hz₂ : g * z₁ * g⁻¹ ∈ K₂ := by
      rw [← hK]
      exact ⟨z₁, hz₁.2, rfl⟩
    have : z₁ ∈ K₁ ⊓ K₂ := ⟨hz₁.2, hc ▸ hz₂⟩
    rw [h.inf_eq, mem_bot] at this
    exact hz₁1 this

end IsProd

end L415

end CFSG.ComponentClassification.HarrisLit
