module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410BenderAct
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Sylow

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem Foote410Config.card_le_eight_of_le
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    {M : Subgroup G} (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t) {V : Subgroup G} (hV : IsKleinFour V)
    (hVM' : V ≤ conjugate M g) (hVC : V ≤ coreActionKernel M) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXC : X ≤ coreActionKernel M) : Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M' := conjugate M g with hM'def
  set C' := coreActionKernel M' with hC'def
  set O := oddCoreIn M' with hO
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hVO : V ≤ normalizer (O : Set G) := fun v hv =>
    mem_normalizer_oddCoreIn (le_normalizer (hVM' hv))
  set W := O ⊔ V with hW
  have hWset : (W : Set G) = (V : Set G) * O := by
    rw [hW, sup_comm]
    exact coe_mul_of_left_le_normalizer_right V O hVO
  have hmap : ∀ c ∈ C', ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    rw [← SetLike.mem_coe, hWset] at hw ⊢
    obtain ⟨v, hv, o, ho, rfl⟩ := Set.mem_mul.mp hw
    have h1 : v⁻¹ * c * v * c⁻¹ ∈ O := by
      have := (mem_coreActionKernel.mp (inv_mem hc)).2 v (hVM' hv)
      rwa [inv_inv] at this
    have h2 : c * o * c⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (mem_coreActionKernel.mp hc).1) o).mp ho
    refine Set.mem_mul.mpr ⟨v, hv, v⁻¹ * c * v * c⁻¹ * (c * o * c⁻¹), mul_mem h1 h2, ?_⟩
    group
  have hC'W : C' ≤ normalizer (W : Set G) := fun c hc => mem_normalizer_iff.mpr fun w =>
    ⟨fun hw => hmap c hc w hw, fun hw => by
      have := hmap c⁻¹ (inv_mem hc) _ hw
      rwa [show c⁻¹ * (c * w * c⁻¹) * c⁻¹⁻¹ = w by group] at this⟩
  have hVO1 : O ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (mem_bot).mpr (eq_one_of_mem_of_odd hVp (odd_card_oddCoreIn M') (mem_inf.mp hx).2
      (mem_inf.mp hx).1)
  have hWcard : Nat.card W = 2 ^ 2 * Nat.card O := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hVO
    rw [hVO1, card_bot, mul_one, hV.card_four] at h1
    rw [h1]
    ring
  have hVW : IsSylowOf 2 V W := by
    apply isSylowOf_of_card (le_sup_right : V ≤ W)
    have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
    have hO2 : ¬ 2 ∣ Nat.card O := fun h2 =>
      (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn M')) (even_iff_two_dvd.mpr h2)
    rw [hWcard, hV.card_four, Nat.factorization_mul (by norm_num) hO0, Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd hO2]
  have hC'8 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ C' → Nat.card Y ≤ 8 := by
    intro Y hY hYC
    have hYN : W ⊔ Y ≤ normalizer (W : Set G) := sup_le le_normalizer (hYC.trans hC'W)
    obtain ⟨S, hS, hYS⟩ := exists_isSylowOf_ge_of_le (le_sup_right : Y ≤ W ⊔ Y) hY
    have hSW := hS.inf_of_le_normalizer (le_sup_left : W ≤ W ⊔ Y) hYN
    obtain ⟨k, hkW, hk⟩ := exists_conj_le_of_isSylowOf hVW (inf_le_right : S ⊓ W ≤ W)
      (hS.isPGroup.to_le inf_le_left)
    rw [← SetLike.mem_coe, hWset] at hkW
    obtain ⟨v₀, hv₀, o₀, ho₀, rfl⟩ := Set.mem_mul.mp hkW
    set o := v₀ * o₀ * v₀⁻¹ with hodef
    have ho : o ∈ O := (mem_normalizer_iff.mp (hVO hv₀) o₀).mp ho₀
    have hle : conjugate (S ⊓ W) o ≤ V := conjugate_le_of_forall fun a ha => by
      have h1 := hk a ha
      have h2 : v₀ * ((v₀ * o₀)⁻¹ * a * (v₀ * o₀)) * v₀⁻¹ ∈ V :=
        mul_mem (mul_mem hv₀ h1) (inv_mem hv₀)
      rwa [show v₀ * ((v₀ * o₀)⁻¹ * a * (v₀ * o₀)) * v₀⁻¹ = o⁻¹ * a * o by rw [hodef]; group]
        at h2
    have heq : conjugate (S ⊓ W) o = V := eq_of_le_of_card_ge hle (by
      rw [card_conjugate_eq_card, hSW.card_eq, hVW.card_eq])
    have hYo : conjugate Y o ≤ coreActionKernel M' ⊓ normalizer (M : Set G) := by
      intro y hy
      rw [mem_conjugate_iff] at hy
      have hyC : y ∈ C' := by
        have h1 := mul_mem (mul_mem (inv_mem (GSThmB.oddCoreIn_le_coreActionKernel M' ho))
          (hYC hy)) (GSThmB.oddCoreIn_le_coreActionKernel M' ho)
        rwa [show o⁻¹ * (o * y * o⁻¹) * o = y by group] at h1
      refine mem_inf.mpr ⟨hyC, foote_cor_4_8_iv h h47 hST hM hVC hV le_rfl ?_⟩
      rw [← heq, mem_normalizer_iff]
      intro z
      rw [mem_conjugate_iff, mem_conjugate_iff]
      have hxS : o * y * o⁻¹ ∈ normalizer ((S ⊓ W : Subgroup G) : Set G) :=
        mem_normalizer_inf' (le_normalizer (hYS hy)) (hYN (mem_sup_right hy))
      have h2 := mem_normalizer_iff.mp hxS (o * z * o⁻¹)
      rw [show o * (y * z * y⁻¹) * o⁻¹ = o * y * o⁻¹ * (o * z * o⁻¹) * (o * y * o⁻¹)⁻¹ by
        group]
      exact h2
    have h8 := card_le_of_isSylowOf hc.hESyl hYo (hY.map (MulAut.conj o⁻¹).toMonoidHom)
    rwa [card_conjugate_eq_card, hc.hE8] at h8
  have hXg : conjugate X g ≤ C' := fun x hx => by
    rw [mem_conjugate_iff] at hx
    exact mem_coreActionKernel_conjugate (hXC hx)
  have h1 := hC'8 (conjugate X g) (hX.map (MulAut.conj g⁻¹).toMonoidHom) hXg
  rwa [card_conjugate_eq_card] at h1

theorem dihedral_four_eq_sq_of_commute : ∀ a b : DihedralGroup 4, a ^ 2 = 1 → b ^ 2 = 1 →
    a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
    a = DihedralGroup.r 1 ^ 2 ∨ b = DihedralGroup.r 1 ^ 2 ∨ a * b = DihedralGroup.r 1 ^ 2 := by
  decide

omit [Finite G] in
theorem exists_sq_eq_of_isKleinFour [Finite G] {X V : Subgroup G}
    (hD : ∀ P : Sylow 2 (X ⧸ pPrimeCore 2 X),
      Nonempty ((P : Subgroup (X ⧸ pPrimeCore 2 X)) ≃* DihedralGroup 4))
    (hV : IsKleinFour V) (hVX : V ≤ X) :
    ∃ y ∈ V, y ≠ 1 ∧ ∃ s : G, (∃ k : ℕ, orderOf s = 2 ^ k) ∧ s ^ 2 = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨P, hP, hVP⟩ := exists_isSylowOf_ge_of_le hVX hVp
  obtain ⟨R₁, hR₁⟩ := hP
  set ρ := QuotientGroup.mk' (pPrimeCore 2 X) with hρ
  set Rsyl : Sylow 2 (X ⧸ pPrimeCore 2 X) :=
    R₁.mapSurjective (QuotientGroup.mk'_surjective _) with hRsyl
  have hRsc : (Rsyl : Subgroup (X ⧸ pPrimeCore 2 X)) = (R₁ : Subgroup X).map ρ :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨eD⟩ := hD Rsyl
  have hmemR : ∀ a : ↥X, a ∈ (R₁ : Subgroup X) ↔ (a : G) ∈ P := fun a => by
    rw [← hR₁]
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hinj : ∀ a ∈ (R₁ : Subgroup X), ∀ b ∈ (R₁ : Subgroup X), ρ a = ρ b → a = b := by
    intro a ha b hb hab
    have := eq_one_of_mk_eq_one_of_isPGroup R₁.isPGroup' (mul_mem ha (inv_mem hb))
      (by rw [map_mul, map_inv, hab, mul_inv_cancel])
    rwa [mul_inv_eq_one] at this
  set σ : ↥(R₁ : Subgroup X) →* DihedralGroup 4 := eD.toMonoidHom.comp
    ((ρ.comp (R₁ : Subgroup X).subtype).codRestrict (Rsyl : Subgroup (X ⧸ pPrimeCore 2 X))
      fun a => by rw [hRsc]; exact mem_map_of_mem ρ a.2) with hσ
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : ρ a = 1 := by
      have h2 : σ a = 1 := ha
      rw [hσ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ eD.injective]
        at h2
      exact congrArg Subtype.val h2
    exact Subtype.ext (eq_one_of_mk_eq_one_of_isPGroup R₁.isPGroup' a.2 h1)
  obtain ⟨a, haV, ha1, -⟩ := exists_ne_of_isKleinFour hV 1
  obtain ⟨b, hbV, hb1, hba⟩ := exists_ne_of_isKleinFour hV a
  have hR : ∀ v (hv : v ∈ V), (⟨v, hVX hv⟩ : ↥X) ∈ (R₁ : Subgroup X) := fun v hv =>
    (hmemR _).mpr (hVP hv)
  set aR : ↥(R₁ : Subgroup X) := ⟨⟨a, hVX haV⟩, hR a haV⟩ with haR
  set bR : ↥(R₁ : Subgroup X) := ⟨⟨b, hVX hbV⟩, hR b hbV⟩ with hbR
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => sq_eq_one_of_isKleinFour hV hv
  have haR2 : aR ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hV2 a haV))
  have hbR2 : bR ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hV2 b hbV))
  have haR1 : aR ≠ 1 := by
    intro h1
    apply ha1
    have h2 := congrArg (fun x : ↥(R₁ : Subgroup X) => ((x : ↥X) : G)) h1
    simpa [haR] using h2
  have hbR1 : bR ≠ 1 := by
    intro h1
    apply hb1
    have h2 := congrArg (fun x : ↥(R₁ : Subgroup X) => ((x : ↥X) : G)) h1
    simpa [hbR] using h2
  have haRbR : aR ≠ bR := by
    intro h1
    apply hba
    have h2 := congrArg (fun x : ↥(R₁ : Subgroup X) => ((x : ↥X) : G)) h1
    simpa [haR, hbR] using h2.symm
  have hcomm : aR * bR = bR * aR := Subtype.ext (Subtype.ext
    (by simpa using commute_of_sq_eq_one hV2 haV hbV))
  have hne1 : ∀ x : ↥(R₁ : Subgroup X), x ≠ 1 → σ x ≠ 1 := fun x hx h1 =>
    hx (hσinj (by rw [h1, map_one]))
  obtain ⟨zR, hzR, hzRV⟩ : ∃ zR : ↥(R₁ : Subgroup X), σ zR = DihedralGroup.r 1 ^ 2 ∧
      ((zR : ↥X) : G) ∈ V := by
    rcases dihedral_four_eq_sq_of_commute (σ aR) (σ bR) (by rw [← map_pow, haR2, map_one])
        (by rw [← map_pow, hbR2, map_one]) (hne1 aR haR1) (hne1 bR hbR1)
        (fun h1 => haRbR (hσinj h1)) (by rw [← map_mul, ← map_mul, hcomm]) with h1 | h1 | h1
    · exact ⟨aR, h1, haV⟩
    · exact ⟨bR, h1, hbV⟩
    · exact ⟨aR * bR, by rw [map_mul]; exact h1, mul_mem haV hbV⟩
  obtain ⟨uR, huR⟩ : ∃ uR : ↥(R₁ : Subgroup X), σ uR = DihedralGroup.r 1 := by
    have h1 : ((eD.symm (DihedralGroup.r 1) : ↥(Rsyl : Subgroup (X ⧸ pPrimeCore 2 X))) :
        X ⧸ pPrimeCore 2 X) ∈ (R₁ : Subgroup X).map ρ := by
      rw [← hRsc]
      exact (eD.symm (DihedralGroup.r 1)).2
    obtain ⟨u, hu, hρu⟩ := mem_map.mp h1
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hσ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show (ρ.comp (R₁ : Subgroup X).subtype).codRestrict (Rsyl : Subgroup (X ⧸ pPrimeCore 2 X))
        (fun a => by rw [hRsc]; exact mem_map_of_mem ρ a.2) ⟨u, hu⟩ =
        eD.symm (DihedralGroup.r 1) from Subtype.ext hρu]
    exact eD.apply_symm_apply _
  have huR2 : uR ^ 2 = zR := hσinj (by rw [map_pow, huR, hzR])
  refine ⟨((zR : ↥X) : G), hzRV, fun h1 => ?_, ((uR : ↥X) : G), ?_, ?_⟩
  · have hz1 : zR = 1 := Subtype.ext (Subtype.ext h1)
    have h2 : DihedralGroup.r 1 ^ 2 = (1 : DihedralGroup 4) := by
      rw [← hzR, hz1, map_one]
    exact absurd h2 (by decide)
  · obtain ⟨k, hk⟩ := R₁.isPGroup' uR
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    refine ⟨i, ?_⟩
    rw [← hi, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  · rw [← huR2]
    rfl

end CFSG.ComponentClassification.FooteLit
