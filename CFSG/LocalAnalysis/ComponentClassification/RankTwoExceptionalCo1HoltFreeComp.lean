module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeEleven
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQbarComp

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ComponentClassification.AS81.Qbar

variable {Y : Type} [Group Y] [Finite Y]

theorem isEmpty_componentIndex_of_eleven
    (Sb : Sylow 2 Y) {A : Subgroup Y} (hO : goldschmidtOddCore Y = ⊥) (hAS : A ≤ Sb)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : Nat.card A = 2 ^ 11)
    (hcl : fusionStronglyClosed (A : Set Y) Sb)
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 Sb)
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x)
    (σ : MulAut Y) (hσA : ∀ x ∈ A, σ x ∈ A) (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {u : Y}
    (hu : ∀ x ∈ A, σ x = x ↔ x = 1 ∨ x = u) {ea eb : Y} (hea : ea ∈ A) (heb : eb ∈ A)
    (ha1 : ea * σ ea ≠ 1) (hb1 : eb * σ eb ≠ 1) (hab : ¬ IsConj (ea * σ ea) (eb * σ eb))
    (habu : ¬ IsConj (ea * σ ea) (eb * σ eb * u)) :
    IsEmpty (ComponentIndex Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWmem, -, -, -, hWcard, huA, hu1, huW, -⟩ :=
    exists_commutatorSubgroup hA2 hAc σ hσA hσ11 hu
  have hu2 : u * u = 1 := hA2 u huA
  have hzu : ∀ x ∈ zpowers u, x = 1 ∨ x = u := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu2]
    rw [zpow_eq_zpow_emod k h2]
    have h0 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> rw [h]
    · exact Or.inl (zpow_zero u)
    · exact Or.inr (zpow_one u)
  have hcardu : Nat.card (zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq, hu2]) hu1
  have hc5 : Nat.card (ComponentIndex Y) ≤ 5 := by
    have h := four_pow_card_componentIndex_le Sb htype hind hcover
    rw [hAc] at h
    by_contra hc
    push Not at hc
    have h6 : 4 ^ 6 ≤ 4 ^ Nat.card (ComponentIndex Y) := Nat.pow_le_pow_right (by norm_num) hc
    have h7 := h6.trans h
    norm_num at h7
  have hτK : ∀ K : ComponentIndex Y, K.1.map (σ ^ 120).toMonoidHom = K.1 := by
    intro K
    have h1 : compPermHom (σ ^ 120) = 1 := by
      rw [map_pow]
      apply orderOf_dvd_iff_pow_eq_one.mp
      refine (_root_.orderOf_dvd_natCard (compPermHom σ)).trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
      exact (Nat.factorial_dvd_factorial hc5).trans (by decide)
    have h2 := congrArg (fun π : Equiv.Perm (ComponentIndex Y) => (π K).1) h1
    simpa only [compPermHom_apply, Equiv.Perm.one_apply] using h2
  have h120 : ¬ 11 ∣ 120 := by norm_num
  refine ⟨fun K => ?_⟩
  have hKo : IsComponentOf K.1 ⊤ := (CFSG.isComponent_iff_open K.1).mp K.2
  have hτ : ∀ x ∈ K.1, (σ ^ 120) x ∈ K.1 := fun x hx => by
    rw [← hτK K]
    exact ⟨x, hx, rfl⟩
  have hτ' : ∀ y ∈ K.1, ∃ x ∈ K.1, (σ ^ 120) x = y := fun y hy => by
    rw [← hτK K] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  set Φ := conjAutOn K.1 A (le_normalizer_of_inducesOmega1 Sb (hind K)) with hΦ
  have hW4 : 4 ≤ Nat.card Φ.range := four_le_card_range Sb K.2 (htype K) (hind K)
  have hker : ∀ a : A, a ∈ Φ.ker ↔ (a : Y) ∈ centralizer (K.1 : Set Y) := by
    intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      rw [mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun e : MulAut K.1 => ((e ⟨y, hy⟩ : K.1) : Y)) h1
      simp only [hΦ, conjAutOn_apply, MulAut.one_apply] at h2
      calc y * a = (a * y * (a : Y)⁻¹) * a := by rw [h2]
        _ = a * y := by group
    · intro h1
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hΦ, conjAutOn_apply, MulAut.one_apply, ← mem_centralizer_iff.mp h1 y y.2]
      group
  have hcardA : Nat.card A = Nat.card Φ.range * Nat.card Φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  set C := A ⊓ centralizer (K.1 : Set Y) with hC
  have hCker : Nat.card C = Nat.card Φ.ker :=
    Nat.card_congr
      { toFun := fun c => ⟨⟨c, c.2.1⟩, (hker _).mpr c.2.2⟩
        invFun := fun k => ⟨k.1.1, k.1.2, (hker k.1).mp k.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hCτ : ∀ x ∈ C, (σ ^ 120) x ∈ C := by
    intro x hx
    refine ⟨pow_apply_mem hσA 120 hx.1, mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨y', hy', rfl⟩ := hτ' y hy
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hx.2 y' hy']
  have hCu : C ≤ zpowers u := by
    rcases eleven_invariant_of_pow hA2 hAc σ hσA hσ11 hu h120 inf_le_left hCτ with h | h
    · exact h
    · exfalso
      have hWC : W ≤ C := fun w hw => by
        obtain ⟨e, he, rfl⟩ := (hWmem w).mp hw
        exact h e he
      have h1 := Subgroup.card_le_of_le hWC
      rw [hWcard, hCker] at h1
      have h2 := Nat.mul_le_mul hW4 h1
      rw [← hcardA, hAc] at h2
      norm_num at h2
  have hC2 : Nat.card Φ.ker ≤ 2 := by
    rw [← hCker, ← hcardu]
    exact Subgroup.card_le_of_le hCu
  have hsurj : Function.Surjective (fun x : ↥(A ⊓ K.1) =>
      (⟨Φ ⟨x, x.2.1⟩, ⟨_, rfl⟩⟩ : Φ.range)) := by
    rintro ⟨_, ⟨b, rfl⟩⟩
    obtain ⟨x, hx, hbx⟩ := hcover K b b.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact (conjAutOn_eq_of_sameOn _ hbx).symm
  have hAK : 2 ^ 10 ≤ Nat.card ↥(A ⊓ K.1) := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card Φ.range * Nat.card Φ.ker ≤ Nat.card Φ.range * 2 :=
      Nat.mul_le_mul_left _ hC2
    rw [← hcardA, hAc] at h2
    have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    have h2048 : (2 : ℕ) ^ 11 = 2048 := by norm_num
    omega
  have hWK : ∀ e ∈ A, e * σ e ∈ K.1 := by
    rcases eleven_invariant_of_pow hA2 hAc σ hσA hσ11 hu h120 (inf_le_left : A ⊓ K.1 ≤ A)
        (fun x hx => ⟨pow_apply_mem hσA 120 hx.1, hτ x hx.2⟩) with h | h
    · exfalso
      have h1 := Subgroup.card_le_of_le h
      rw [hcardu] at h1
      have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
      omega
    · exact fun e he => (h e he).2
  set a := ea * σ ea with ha
  set b := eb * σ eb with hb
  have haA : a ∈ A := mul_mem hea (hσA ea hea)
  have hbA : b ∈ A := mul_mem heb (hσA eb heb)
  have haK : a ∈ K.1 := hWK ea hea
  have hbK : b ∈ K.1 := hWK eb heb
  have hnc : ∀ e ∈ A, e * σ e ≠ 1 → e * σ e ∉ centralizer (K.1 : Set Y) := by
    intro e he he1 hc
    rcases hzu _ (hCu ⟨mul_mem he (hσA e he), hc⟩) with h | h
    · exact he1 h
    · exact huW (h ▸ (hWmem _).mpr ⟨e, he, rfl⟩)
  have : IsSimpleGroup (K.1 ⧸ center K.1) := hKo.2.2.2
  obtain ⟨P, hP⟩ := isSylowOf_inf_component Sb K.2
  set TL : Sylow 2 (K.1 ⧸ center K.1) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center K.1)) with hTL
  have hTLcoe : (TL : Subgroup (K.1 ⧸ center K.1)) =
      (P : Subgroup K.1).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  set Ω := Omega1 (TL : Subgroup (K.1 ⧸ center K.1)) with hΩ
  have hΩab : IsMulCommutative Ω := isMulCommutative_omega1 (htype K) TL
  have hZS : ∀ ζ : K.1, ζ ∈ center K.1 → (ζ : Y) ∈ (Sb : Subgroup Y) := by
    intro ζ hζ
    have h1 := RankTwoAltFive.center_component_le_pCore hO hKo hζ
    have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := Y) 2
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).le_sylow_of_normal Sb h1
  have hmemS : ∀ k : K.1, (QuotientGroup.mk k : K.1 ⧸ center K.1) ∈
      (TL : Subgroup (K.1 ⧸ center K.1)) → (k : Y) ∈ (Sb : Subgroup Y) := by
    intro k hk
    rw [hTLcoe] at hk
    obtain ⟨p, hp, hpk⟩ := hk
    have hpS : (p : Y) ∈ (Sb : Subgroup Y) := by
      have : (p : Y) ∈ (P : Subgroup K.1).map K.1.subtype := ⟨p, hp, rfl⟩
      rw [hP] at this
      exact this.1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hpk
    have h1 := hZS _ hpk
    have e : (k : Y) = p * ((p⁻¹ * k : K.1) : Y) := by simp
    rw [e]
    exact mul_mem hpS h1
  have hAΩ : ∀ x : K.1, (x : Y) ∈ A → (QuotientGroup.mk x : K.1 ⧸ center K.1) ∈ Ω := by
    intro x hx
    refine GoldType.mem_omega1 ?_ ?_
    · rw [hTLcoe]
      refine ⟨x, ?_, rfl⟩
      have hxS : (x : Y) ∈ (Sb : Subgroup Y) ⊓ K.1 := ⟨hAS hx, x.2⟩
      rw [← hP] at hxS
      obtain ⟨y, hy, hyx⟩ := hxS
      rwa [Subtype.ext hyx] at hy
    · rw [← QuotientGroup.mk_pow]
      have h2 : x ^ 2 = 1 := Subtype.ext (by simpa [sq] using hA2 x hx)
      rw [h2, QuotientGroup.mk_one]
  have hmk1 : ∀ e ∈ A, ∀ h : e * σ e ∈ K.1, e * σ e ≠ 1 →
      (QuotientGroup.mk (⟨e * σ e, h⟩ : K.1) : K.1 ⧸ center K.1) ≠ 1 := by
    intro e he h he1 h1
    rw [QuotientGroup.eq_one_iff, mem_center_iff] at h1
    exact hnc e he he1 (mem_centralizer_iff.mpr fun y hy =>
      (congrArg Subtype.val (h1 ⟨y, hy⟩) : _))
  obtain ⟨nb, -, hnb⟩ := (N11b (K.1 ⧸ center K.1) (htype K) TL hΩab).2 _
    (hAΩ ⟨a, haK⟩ haA) _ (hAΩ ⟨b, hbK⟩ hbA) (hmk1 ea hea haK ha1) (hmk1 eb heb hbK hb1)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective nb
  have hmx : (QuotientGroup.mk (m⁻¹ * ⟨a, haK⟩ * m) : K.1 ⧸ center K.1) =
      QuotientGroup.mk ⟨b, hbK⟩ := by
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hnb
  have hS : (m : Y)⁻¹ * a * m ∈ (Sb : Subgroup Y) := by
    have h1 := hmemS (m⁻¹ * ⟨a, haK⟩ * m)
      (by rw [hmx]; exact GoldType.omega1_le _ (hAΩ ⟨b, hbK⟩ hbA))
    simpa using h1
  have hmA : (m : Y)⁻¹ * a * m ∈ A := hcl a haA m hS
  rw [QuotientGroup.eq] at hmx
  have hζc : ((m : Y)⁻¹ * a * m)⁻¹ * b ∈ centralizer (K.1 : Set Y) :=
    mem_centralizer_iff.mpr fun y hy => by
      simpa using congrArg Subtype.val (mem_center_iff.mp hmx ⟨y, hy⟩)
  have hζA : ((m : Y)⁻¹ * a * m)⁻¹ * b ∈ A := mul_mem (inv_mem hmA) hbA
  rcases hzu _ (hCu (mem_inf.mpr ⟨hζA, hζc⟩)) with h | h
  · apply hab
    refine isConj_iff.mpr ⟨(m : Y)⁻¹, ?_⟩
    rw [inv_inv]
    exact inv_mul_eq_one.mp h
  · apply habu
    refine isConj_iff.mpr ⟨(m : Y)⁻¹, ?_⟩
    have h' : b = (m : Y)⁻¹ * a * m * u := by
      rw [← h]
      group
    rw [inv_inv, h', mul_assoc _ u u, hu2, mul_one]

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
