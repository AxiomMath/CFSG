module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP21b3

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped IsMulCommutative
open scoped Pointwise

public lemma fzl21b_V'_data (N : Type) [Group N] (φ : N →* MulAut fz21b_X) (N₀ : Subgroup N)
    [N₀.Normal] (e : N ⧸ N₀ ≃* FzSigma4) (ρ lam : N) (hφ : Function.Injective φ)
    (hInv : ∀ n ∈ N₀, n ≠ 1 → ∀ x : fz21b_X, φ n x = x⁻¹) (hN₀ : Nat.card N₀ = 2)
    (hρ : orderOf ρ = 3)
    (hlam : orderOf lam = 2) (hrel : lam * ρ * lam⁻¹ = ρ⁻¹) :
    ∃ V' : Subgroup N, Nat.card V' = 4 ∧
      V' ≤ fz21b_V.comap (e.toMonoidHom.comp (QuotientGroup.mk' N₀)) ∧
      V' ⊓ N₀ = ⊥ ∧ ρ ∈ Subgroup.normalizer (V' : Set N) ∧
      lam ∈ Subgroup.normalizer (V' : Set N) := by
  classical
  let π : N →* FzSigma4 := e.toMonoidHom.comp (QuotientGroup.mk' N₀)
  have hπker : π.ker = N₀ := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' N₀)).ker = N₀
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N₀) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N₀)
  obtain ⟨N₁, hN₁normal, hN₁sq, hN₀N₁, hN₁eq, K, hKnormal, hN₀K, hN₁K, hKfix⟩ :=
    fzl21b_stage1_strong N φ N₀ e hφ hInv
  have hN₁mem : ∀ x : N, x ∈ N₁ → π x ∈ fz21b_V := by
    intro x hx
    rw [hN₁eq] at hx
    exact Subgroup.mem_comap.mp hx
  have hcardSigma : Nat.card FzSigma4 = 24 := by rw [Nat.card_eq_fintype_card]; decide
  have hNq : Nat.card (N ⧸ N₀) = 24 := by rw [Nat.card_congr e.toEquiv, hcardSigma]
  have hcardN : Nat.card N = 48 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N₀
    rw [hNq, hN₀] at h
    omega
  haveI : Finite N := Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  let f : N₁ →* fz21b_V := (π.domRestrict N₁).codRestrict fz21b_V
    (fun x => Subgroup.mem_comap.mp (hN₁eq ▸ x.2))
  have hfker : f.ker = N₀.subgroupOf N₁ := by
    simp only [f]
    rw [MonoidHom.ker_codRestrict, MonoidHom.ker_domRestrict, hπker]
  have hfrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [MonoidHom.mem_range]
    obtain ⟨n, hn⟩ := hπsurj (x : FzSigma4)
    refine ⟨⟨n, ?_⟩, ?_⟩
    · rw [hN₁eq, Subgroup.mem_comap, hn]; exact x.2
    · exact Subtype.ext hn
  have hcardN₁ : Nat.card N₁ = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hq' : Nat.card (N₁ ⧸ f.ker) = Nat.card fz21b_V := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfrange]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have hker : Nat.card f.ker = Nat.card N₀ := by
      rw [hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀N₁).toEquiv]
    rw [hq', fz21b_V_card, hker, hN₀] at h
    omega
  haveI : Finite N₁ := Nat.finite_of_card_ne_zero (by rw [hcardN₁]; norm_num)
  have hcenter : N₀ ≤ Subgroup.center N := by
    intro n hn
    by_cases hn1 : n = 1
    · rw [hn1]; exact Subgroup.one_mem _
    rw [Subgroup.mem_center_iff]
    intro g
    have hphin : φ n = fz21b_invAut fz21b_X :=
      MulEquiv.ext (fun x => hInv n hn hn1 x)
    have hcomm : φ n * φ g = φ g * φ n := by
      rw [hphin]
      exact (Subgroup.mem_center_iff.mp (fz21b_invAut_mem_center fz21b_X) (φ g)).symm
    have hconj : φ (g * n) = φ (n * g) := by rw [map_mul, map_mul]; exact hcomm.symm
    exact hφ hconj
  haveI : IsMulCommutative N₁ := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa using hN₁sq (a : N) a.2)
    have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa using hN₁sq (b : N) b.2)
    have hab2 : (a * b) ^ 2 = 1 := Subtype.ext (by
      simpa using hN₁sq ((a : N) * (b : N)) (N₁.mul_mem a.2 b.2))
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hab2)
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha, hb]
  let T : N₁ →* N₁ :=
    { toFun := fun x => ⟨ρ * (x : N) * ρ⁻¹, hN₁normal.conj_mem (x : N) x.2 ρ⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  let S : N₁ →* N₁ :=
    { toFun := fun x => ⟨lam * (x : N) * lam⁻¹, hN₁normal.conj_mem (x : N) x.2 lam⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  let normH : N₁ →* N₁ := (MonoidHom.id N₁) * T * (T.comp T)
  let V' : Subgroup N := (normH.ker).map N₁.subtype
  have hρ3 : ρ ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hlam2 : lam ^ 2 = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hTeq : ∀ y : N₁, normH (T y) = T (normH y) := by
    intro y
    show (MonoidHom.id N₁ * T * (T.comp T)) (T y) =
      T ((MonoidHom.id N₁ * T * (T.comp T)) y)
    simp only [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply, map_mul]
  have hρ2 : ρ ^ 2 = ρ⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ']
    exact hρ3
  have hρ2' : ρ * ρ = ρ⁻¹ := by rw [← pow_two]; exact hρ2
  have hρinv2' : ρ⁻¹ * ρ⁻¹ = ρ := by rw [← mul_inv_rev, ← pow_two, hρ2, inv_inv]
  have hTT : ∀ y : N₁, (T (T y) : N) = ρ⁻¹ * (y : N) * ρ := by
    intro y
    show ρ * (ρ * (y : N) * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * (y : N) * ρ
    have h1 : ρ * (ρ * (y : N) * ρ⁻¹) * ρ⁻¹ =
        (ρ * ρ) * (y : N) * (ρ⁻¹ * ρ⁻¹) := by group
    rw [h1, hρ2', hρinv2']
  have hc1 : lam * ρ * lam⁻¹ = ρ⁻¹ := hrel
  have hc2 : lam * ρ⁻¹ * lam⁻¹ = ρ := by
    calc lam * ρ⁻¹ * lam⁻¹ = (lam * ρ * lam⁻¹)⁻¹ := by group
      _ = (ρ⁻¹)⁻¹ := by rw [hrel]
      _ = ρ := inv_inv ρ
  have hTS : ∀ y : N₁, T (S y) = S (T (T y)) := by
    intro y
    apply Subtype.ext
    show ρ * (lam * (y : N) * lam⁻¹) * ρ⁻¹ =
      lam * (ρ * (ρ * (y : N) * ρ⁻¹) * ρ⁻¹) * lam⁻¹
    change ρ * (lam * (y : N) * lam⁻¹) * ρ⁻¹ = lam * ((T (T y) : N)) * lam⁻¹
    rw [hTT y]
    have hR : lam * (ρ⁻¹ * (y : N) * ρ) * lam⁻¹ =
        (lam * ρ⁻¹ * lam⁻¹) * (lam * (y : N) * lam⁻¹) * (lam * ρ * lam⁻¹) := by
      group
    rw [hR, hc2, hc1]
  have hTTS : ∀ y : N₁, T (T (S y)) = S (T y) := by
    intro y
    apply Subtype.ext
    show ρ * (ρ * (lam * (y : N) * lam⁻¹) * ρ⁻¹) * ρ⁻¹ =
      lam * (ρ * (y : N) * ρ⁻¹) * lam⁻¹
    have h1 : ρ * (ρ * (lam * (y : N) * lam⁻¹) * ρ⁻¹) * ρ⁻¹ =
        (ρ * ρ) * (lam * (y : N) * lam⁻¹) * (ρ⁻¹ * ρ⁻¹) := by group
    rw [h1, hρ2', hρinv2']
    have hR : lam * (ρ * (y : N) * ρ⁻¹) * lam⁻¹ =
        (lam * ρ * lam⁻¹) * (lam * (y : N) * lam⁻¹) * (lam * ρ⁻¹ * lam⁻¹) := by
      group
    rw [hR, hc1, hc2]
  have hSeq' : ∀ y : N₁, normH (S y) = S (normH y) := by
    intro y
    have h1 : normH (S y) = S y * T (S y) * T (T (S y)) := by
      show (MonoidHom.id N₁ * T * (T.comp T)) (S y) = _
      simp only [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply]
    have h2 : S (normH y) = S y * S (T y) * S (T (T y)) := by
      show S ((MonoidHom.id N₁ * T * (T.comp T)) y) = S y * S (T y) * S (T (T y))
      simp only [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply, map_mul]
    rw [h1, h2, hTTS y, hTS y]
    ac_rfl
  have hTker : ∀ y ∈ normH.ker, T y ∈ normH.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [hTeq y, hy, map_one]
  have hT2ker : ∀ y ∈ normH.ker, T (T y) ∈ normH.ker := fun y hy => hTker (T y) (hTker y hy)
  have hSker : ∀ y ∈ normH.ker, S y ∈ normH.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [hSeq' y, hy, map_one]
  have hfixN₀ : ∀ y : N₁, (y : N) ∈ N₀ → normH y = y := by
    intro y hy
    have hTy : T y = y := by
      apply Subtype.ext
      have hcomm : ρ * (y : N) = (y : N) * ρ :=
        (Subgroup.mem_center_iff.mp (hcenter hy)) ρ
      show ρ * (y : N) * ρ⁻¹ = (y : N)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hTTy : T (T y) = y := by rw [hTy]; exact hTy
    show normH y = y
    simp only [normH, MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply]
    have hy2 : y * y = 1 := by
      apply Subtype.ext
      show (y : N) * (y : N) = 1
      rw [← pow_two]; exact hN₁sq (y : N) y.2
    rw [hTTy, hTy, hy2, one_mul]
  have hπT : ∀ y : N₁, π (T y : N) = π ρ * π y * (π ρ)⁻¹ := by
    intro y
    show π (ρ * (y : N) * ρ⁻¹) = π ρ * π y * (π ρ)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hπρ3 : (π ρ) ^ 3 = 1 := by rw [← map_pow, hρ3, map_one]
  have hπρne : π ρ ≠ 1 := by
    intro h
    have hmem : ρ ∈ N₀ := by rw [← hπker, MonoidHom.mem_ker]; exact h
    have hρ2 : ρ ^ 2 = 1 := by
      have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ
      have hphi : φ ρ = fz21b_invAut fz21b_X := MulEquiv.ext (fun x => hInv ρ hmem hρ1 x)
      have h1 : φ (ρ ^ 2) = 1 := by
        have hsq : fz21b_invAut fz21b_X * fz21b_invAut fz21b_X = 1 := by
          apply MulEquiv.ext
          intro x
          show x⁻¹⁻¹ = x
          exact inv_inv x
        rw [map_pow, hphi]
        change fz21b_invAut fz21b_X * fz21b_invAut fz21b_X = 1
        exact hsq
      exact hφ (by rw [h1, map_one])
    have hdv : orderOf ρ ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact hρ2
    rw [hρ] at hdv
    norm_num at hdv
  have hπlam2 : (π lam) ^ 2 = 1 := by rw [← map_pow, hlam2, map_one]
  have hπrel : π lam * π ρ * (π lam)⁻¹ = (π ρ)⁻¹ := by
    have h := congrArg π hrel
    simpa only [map_mul, map_inv] using h
  have hnormx : ∀ x : N₁, π (normH x : N) =
      (π x) * (π ρ * π x * (π ρ)⁻¹) * (π ρ * (π ρ * π x * (π ρ)⁻¹) * (π ρ)⁻¹) := by
    intro x
    show π ((MonoidHom.id N₁ * T * (T.comp T)) x : N) = _
    simp only [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.comp_apply,
      Subgroup.coe_mul, map_mul, hπT]
  have hrange_le : normH.range ≤ N₀.subgroupOf N₁ := by
    rintro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [Subgroup.mem_subgroupOf, ← hπker, MonoidHom.mem_ker]
    rw [hnormx x]
    exact fz21b_hVtrace (π ρ) (π x) hπρ3 hπρne (hN₁mem (x : N) x.2)
  have hrange_ge : N₀.subgroupOf N₁ ≤ normH.range := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    exact MonoidHom.mem_range.mpr ⟨y, hfixN₀ y hy⟩
  have hran : normH.range = N₀.subgroupOf N₁ := le_antisymm hrange_le hrange_ge
  have hcardker : Nat.card normH.ker = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup normH.ker
    have hq' : Nat.card (N₁ ⧸ normH.ker) = 2 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange normH).toEquiv, hran,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀N₁).toEquiv, hN₀]
    rw [hcardN₁, hq'] at h
    omega
  have hcardV' : Nat.card V' = 4 := by
    rw [show V' = (normH.ker).map N₁.subtype from rfl,
      Subgroup.card_map_of_injective (K := normH.ker) (f := N₁.subtype)
        (Subgroup.subtype_injective N₁), hcardker]
  have hV'leN₁ : V' ≤ N₁ := Subgroup.map_subtype_le normH.ker
  have hV'disj : V' ⊓ N₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxN₀⟩ := hx
    rw [Subgroup.mem_bot]
    rw [show V' = (normH.ker).map N₁.subtype from rfl] at hxV
    rw [Subgroup.mem_map] at hxV
    obtain ⟨y, hyker, hyx⟩ := hxV
    have hyN₀ : (y : N) ∈ N₀ := by
      rw [show (y : N) = x from hyx]
      exact hxN₀
    have hkery : normH y = 1 := MonoidHom.mem_ker.mp hyker
    have hfix := hfixN₀ y hyN₀
    have hy1 : y = 1 := by rw [← hfix]; exact hkery
    rw [← show (y : N) = x from hyx, hy1]
    rfl
  have hρ_forw : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V' := by
    intro x hx
    rw [show V' = (normH.ker).map N₁.subtype from rfl] at hx ⊢
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨y, hyker, hyx⟩ := hx
    refine ⟨T y, hTker y hyker, ?_⟩
    show ρ * (y : N) * ρ⁻¹ = ρ * x * ρ⁻¹
    rw [show (y : N) = x from hyx]
  have hρnorm : ρ ∈ Subgroup.normalizer (V' : Set N) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hρ_forw x hx
    · exact le_of_eq (Nat.card_congr (Subgroup.equivMapOfInjective V'
        (MulAut.conj ρ).toMonoidHom (MulAut.conj ρ).injective).toEquiv)
  have hlam_forw : ∀ x ∈ V', lam * x * lam⁻¹ ∈ V' := by
    intro x hx
    rw [show V' = (normH.ker).map N₁.subtype from rfl] at hx ⊢
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨y, hyker, hyx⟩ := hx
    refine ⟨S y, hSker y hyker, ?_⟩
    show lam * (y : N) * lam⁻¹ = lam * x * lam⁻¹
    rw [show (y : N) = x from hyx]
  have hlamnorm : lam ∈ Subgroup.normalizer (V' : Set N) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hlam_forw x hx
    · exact le_of_eq (Nat.card_congr (Subgroup.equivMapOfInjective V'
        (MulAut.conj lam).toMonoidHom (MulAut.conj lam).injective).toEquiv)
  exact ⟨V', hcardV', by rw [← hN₁eq]; exact hV'leN₁, hV'disj, hρnorm, hlamnorm⟩

end CFSG.OddStandard.SmallF3.FritzII
