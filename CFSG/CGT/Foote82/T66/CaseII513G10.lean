module

public import CFSG.CGT.Foote82.T66.CitedCaseII

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem mem_center_map_iff {Δ : Type*} [Group Δ] {P : Subgroup Δ} {c : Δ} :
    c ∈ (Subgroup.center ↥P).map P.subtype ↔ c ∈ P ∧ ∀ p ∈ P, p * c = c * p := by
  constructor
  · rintro ⟨c', hc', rfl⟩
    refine ⟨c'.2, fun p hp => ?_⟩
    have := Subgroup.mem_center_iff.1 hc' ⟨p, hp⟩
    exact congrArg Subtype.val this
  · rintro ⟨hcP, hc⟩
    exact ⟨⟨c, hcP⟩, Subgroup.mem_center_iff.2 fun p => Subtype.ext (hc p p.2), rfl⟩

theorem card_le_of_sylow {G Sy : Subgroup Γ} (hSy : Sy ≤ G) (hSy2 : IsPGroup 2 ↥Sy)
    (hmax : ∀ Y : Subgroup Γ, Sy ≤ Y → Y ≤ G → IsPGroup 2 ↥Y → Y = Sy) :
    ∀ Y : Subgroup Γ, Y ≤ G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥Sy := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := (hSy2.of_equiv (Subgroup.subgroupOfEquivOfLe hSy).symm).exists_le_sylow
  have hS₁Γ : (S₁ : Subgroup ↥G).map G.subtype = Sy := by
    refine hmax _ ?_ (Subgroup.map_subtype_le _) (S₁.isPGroup'.map _)
    intro x hx
    exact ⟨⟨x, hSy hx⟩, hS₁ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  intro Y hYG hY2
  obtain ⟨Ys, hYs⟩ := (hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYG).symm).exists_le_sylow
  have h1 := Subgroup.card_le_of_le hYs
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYG).toEquiv] at h1
  rw [← hS₁Γ, Subgroup.card_map_of_injective G.subtype_injective, Sylow.card_eq_multiplicity,
    ← Sylow.card_eq_multiplicity Ys]
  exact h1

theorem card_le_of_G10 (hG10 : CaseIIG10) {G P : Subgroup Γ} {z : Γ}
    (hPG : P ≤ G ⊓ Subgroup.centralizer ({z} : Set Γ)) (hP2 : IsPGroup 2 ↥P)
    (hPc : Nat.card ↥P = 64) (hD : Nonempty (↥P ≃* DihedralGroup 4 × DihedralGroup 4))
    (hZ : Nat.card ↥(Subgroup.center ↥P) = 4) (hzP : z ∈ P) (hz2 : orderOf z = 2)
    (hmax : ∀ Y : Subgroup Γ, Y ≤ G ⊓ Subgroup.centralizer ({z} : Set Γ) → IsPGroup 2 ↥Y →
      Nat.card ↥Y ≤ 64)
    (h128 : 128 ∣ Nat.card ↥G) :
    ∀ Y : Subgroup Γ, Y ≤ G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eD⟩ := hD
  have hPG' : P ≤ G := fun p hp => (hPG hp).1
  obtain ⟨K, hK, hPK⟩ := Sylow.exists_subgroup_card_pow_succ (p := 2) (n := 6)
    (by simpa using h128) (H := P.subgroupOf G)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG').toEquiv, hPc]; norm_num)
  set Ps := K.map G.subtype with hPs
  have hPsG : Ps ≤ G := Subgroup.map_subtype_le _
  have hPsc : Nat.card ↥Ps = 128 := by
    rw [hPs, Subgroup.card_map_of_injective G.subtype_injective, hK]
    norm_num
  have hPs2 : IsPGroup 2 ↥Ps := IsPGroup.of_card (n := 7) (by rw [hPsc]; norm_num)
  have hPPs : P ≤ Ps := fun p hp => ⟨⟨p, hPG' hp⟩, hPK (Subgroup.mem_subgroupOf.2 hp), rfl⟩
  have hidx : (P.subgroupOf Ps).index = 2 := by
    have h := (P.subgroupOf Ps).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPPs).toEquiv, hPc, hPsc] at h
    omega
  have hmove : ∃ g ∈ Ps, g * z * g⁻¹ ≠ z := by
    by_contra hno
    push Not at hno
    have hle : Ps ≤ G ⊓ Subgroup.centralizer ({z} : Set Γ) := by
      intro g hg
      refine ⟨hPsG hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hno g hg
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    have := hmax Ps hle hPs2
    omega
  obtain ⟨g₀, hg₀, hg₀z⟩ := hmove
  set Zg := (Subgroup.center ↥P).map P.subtype with hZg
  have hZgc : Nat.card ↥Zg = 4 := by
    rw [hZg, Subgroup.card_map_of_injective P.subtype_injective, hZ]
  have hzZ : z ∈ Zg := mem_center_map_iff.2 ⟨hzP, fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.1 (hPG hp).2⟩
  set P' := P.subgroupOf Ps with hP'
  have hG10' := hG10 ↥Ps hPsc P' hidx
    ⟨(Subgroup.subgroupOfEquivOfLe hPPs).trans eD⟩
    ⟨⟨g₀, hg₀⟩, ⟨⟨z, hPPs hzP⟩, Subgroup.mem_subgroupOf.2 hzP⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hPG (Subgroup.mem_subgroupOf.1 p.2)).2
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2]
  · intro h
    apply hg₀z
    exact congrArg Subtype.val h
  have hnorm : ∀ n ∈ G, Ps.map (MulAut.conj n).toMonoidHom = Ps → ∀ c ∈ Zg, n * c * n⁻¹ ∈ Zg := by
    intro n hnG hnPs c hc
    obtain ⟨hcP, hcc⟩ := mem_center_map_iff.1 hc
    set M₀ := P.map (MulAut.conj n).toMonoidHom with hM₀
    have hM₀Ps : M₀ ≤ Ps := by
      rw [← hnPs]
      exact Subgroup.map_mono hPPs
    have hM₀c : Nat.card ↥M₀ = 64 := by
      rw [hM₀, Subgroup.card_map_of_injective (MulAut.conj n).injective, hPc]
    set M := M₀.subgroupOf Ps with hM
    have hMidx : M.index = 2 := by
      have h := M.card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM₀Ps).toEquiv, hM₀c, hPsc] at h
      omega
    have hMiso : Nonempty (↥M ≃* DihedralGroup 4 × DihedralGroup 4) :=
      ⟨((Subgroup.subgroupOfEquivOfLe hM₀Ps).trans
        (P.equivMapOfInjective _ (MulAut.conj n).injective).symm).trans eD⟩
    have hncP : n * c * n⁻¹ ∈ M₀ := ⟨c, hcP, rfl⟩
    have h1 : (⟨n * c * n⁻¹, hM₀Ps hncP⟩ : ↥Ps) ∈ (Subgroup.center ↥M).map M.subtype := by
      rw [mem_center_map_iff]
      refine ⟨Subgroup.mem_subgroupOf.2 hncP, fun m hm => ?_⟩
      apply Subtype.ext
      obtain ⟨p, hp, hpm⟩ := Subgroup.mem_subgroupOf.1 hm
      simp only [Subgroup.coe_mul]
      rw [← hpm]
      show n * p * n⁻¹ * (n * c * n⁻¹) = n * c * n⁻¹ * (n * p * n⁻¹)
      calc n * p * n⁻¹ * (n * c * n⁻¹) = n * (p * c) * n⁻¹ := by group
        _ = n * (c * p) * n⁻¹ := by rw [hcc p hp]
        _ = n * c * n⁻¹ * (n * p * n⁻¹) := by group
    rw [hG10' M hMidx hMiso, mem_center_map_iff] at h1
    obtain ⟨h2, h3⟩ := h1
    refine mem_center_map_iff.2 ⟨Subgroup.mem_subgroupOf.1 h2, fun p hp => ?_⟩
    have := h3 ⟨p, hPPs hp⟩ (Subgroup.mem_subgroupOf.2 hp)
    exact congrArg Subtype.val this
  refine fun Y hYG hY2 => hPsc ▸ card_le_of_sylow hPsG hPs2 ?_ Y hYG hY2
  intro Y hPsY hYG hY2
  by_contra hne
  have hlt : Ps < Y := lt_of_le_of_ne hPsY (Ne.symm hne)
  haveI : Group.IsNilpotent ↥Y := hY2.isNilpotent
  have hT' : Ps.subgroupOf Y < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm _ hPsY
    intro x hx
    have : (⟨x, hx⟩ : ↥Y) ∈ Ps.subgroupOf Y := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨y', hy'N, hy'T⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hT')
  set y : Γ := (y' : Γ) with hy
  have hyY : y ∈ Y := y'.2
  have hyG : y ∈ G := hYG hyY
  have hyPs : y ∉ Ps := fun h => hy'T (Subgroup.mem_subgroupOf.2 h)
  have hyN : Ps.map (MulAut.conj y).toMonoidHom = Ps := by
    have hconj : ∀ t ∈ Ps, y * t * y⁻¹ ∈ Ps := by
      intro t ht
      have hN := Subgroup.mem_normalizer_iff.1 hy'N
      have := (hN ⟨t, hPsY ht⟩).1 (Subgroup.mem_subgroupOf.2 ht)
      exact Subgroup.mem_subgroupOf.1 this
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨t, ht, rfl⟩
      exact hconj t ht
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective]
  set W := Ps ⊔ Subgroup.zpowers y with hW
  have hWY : W ≤ Y := sup_le hPsY (Subgroup.zpowers_le.2 hyY)
  have hW2 : IsPGroup 2 ↥W := hY2.to_le hWY
  have hWN : W ≤ Subgroup.normalizer (Zg : Set Γ) := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 ?_)
    ·
      intro t ht
      have hPn : (P.subgroupOf Ps).Normal := Subgroup.normal_of_index_eq_two hidx
      have hmemP : ∀ t ∈ Ps, ∀ p ∈ P, t * p * t⁻¹ ∈ P := by
        intro t ht p hp
        have := hPn.conj_mem ⟨p, hPPs hp⟩ (Subgroup.mem_subgroupOf.2 hp) ⟨t, ht⟩
        exact Subgroup.mem_subgroupOf.1 this
      have hconjP : ∀ t ∈ Ps, ∀ c ∈ Zg, t * c * t⁻¹ ∈ Zg := by
        intro t ht c hc
        obtain ⟨hcP, hcc⟩ := mem_center_map_iff.1 hc
        refine mem_center_map_iff.2 ⟨hmemP t ht c hcP, fun p hp => ?_⟩
        have hp' : t⁻¹ * p * t ∈ P := by simpa using hmemP t⁻¹ (Ps.inv_mem ht) p hp
        have h1 := hcc _ hp'
        calc p * (t * c * t⁻¹) = t * ((t⁻¹ * p * t) * c) * t⁻¹ := by group
          _ = t * (c * (t⁻¹ * p * t)) * t⁻¹ := by rw [h1]
          _ = t * c * t⁻¹ * p := by group
      rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => hconjP t ht c hc, fun hc => ?_⟩
      have := hconjP t⁻¹ (Ps.inv_mem ht) _ hc
      simpa [mul_assoc] using this
    · rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => hnorm y hyG hyN c hc, fun hc => ?_⟩
      have hyN' : Ps.map (MulAut.conj y⁻¹).toMonoidHom = Ps := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨t, ht, rfl⟩
          rw [← hyN] at ht
          obtain ⟨t', ht', htt'⟩ := ht
          have e : (MulAut.conj y⁻¹).toMonoidHom t = t' := by
            rw [← htt']
            show y⁻¹ * (y * t' * y⁻¹) * y⁻¹⁻¹ = t'
            group
          rw [e]
          exact ht'
        · rw [Subgroup.card_map_of_injective (f := (MulAut.conj y⁻¹).toMonoidHom)
            (MulAut.conj y⁻¹).injective]
      have := hnorm y⁻¹ (G.inv_mem hyG) hyN' _ hc
      simpa [mul_assoc] using this
  set C := (Subgroup.centralizer ({z} : Set Γ)).subgroupOf W with hC
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hconjZ : ∀ w : ↥W, (w : Γ) * z * (w : Γ)⁻¹ ∈ Zg := fun w =>
    (Subgroup.mem_normalizer_iff.1 (hWN w.2) z).1 hzZ
  let f₀ : ↥W → ↥Zg := fun w => ⟨(w : Γ) * z * (w : Γ)⁻¹, hconjZ w⟩
  have hf₀ : ∀ a b : ↥W, a⁻¹ * b ∈ C → f₀ a = f₀ b := by
    intro a b hab
    apply Subtype.ext
    have h1 : ((a⁻¹ * b : ↥W) : Γ) * z = z * ((a⁻¹ * b : ↥W) : Γ) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hab)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    show (a : Γ) * z * (a : Γ)⁻¹ = (b : Γ) * z * (b : Γ)⁻¹
    calc (a : Γ) * z * (a : Γ)⁻¹ =
          (a : Γ) * z * ((a : Γ)⁻¹ * b) * ((a : Γ)⁻¹ * b)⁻¹ * (a : Γ)⁻¹ := by group
      _ = (a : Γ) * (z * ((a : Γ)⁻¹ * b)) * ((a : Γ)⁻¹ * b)⁻¹ * (a : Γ)⁻¹ := by group
      _ = (a : Γ) * (((a : Γ)⁻¹ * b) * z) * ((a : Γ)⁻¹ * b)⁻¹ * (a : Γ)⁻¹ := by rw [h1]
      _ = (b : Γ) * z * (b : Γ)⁻¹ := by group
  let f : ↥W ⧸ C → ↥Zg :=
    Quotient.lift f₀ fun a b hab => hf₀ a b (QuotientGroup.leftRel_apply.mp hab)
  have hfmk : ∀ a : ↥W, f (a : ↥W ⧸ C) = f₀ a := fun a => rfl
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    rw [hfmk, hfmk] at h
    have h1 : (a : Γ) * z * (a : Γ)⁻¹ = (b : Γ) * z * (b : Γ)⁻¹ := congrArg Subtype.val h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : Γ)⁻¹ * b * z = (a : Γ)⁻¹ * ((b : Γ) * z * (b : Γ)⁻¹) * b := by group
      _ = (a : Γ)⁻¹ * ((a : Γ) * z * (a : Γ)⁻¹) * b := by rw [h1]
      _ = z * ((a : Γ)⁻¹ * b) := by group
  have hf1 : ∀ q, f q ≠ 1 := by
    intro q h
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [hfmk] at h
    have h1 : (a : Γ) * z * (a : Γ)⁻¹ = 1 := congrArg Subtype.val h
    apply hz1
    calc z = (a : Γ)⁻¹ * ((a : Γ) * z * (a : Γ)⁻¹) * a := by group
      _ = 1 := by rw [h1]; group
  let F : Option (↥W ⧸ C) → ↥Zg := fun o => o.elim 1 f
  have hF : Function.Injective F := by
    rintro (_ | q₁) (_ | q₂) h
    · rfl
    · exact absurd h.symm (hf1 q₂)
    · exact absurd h (hf1 q₁)
    · exact congrArg some (hf h)
  have hcardq := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option, hZgc] at hcardq
  have hidxC : C.index ≤ 2 := by
    have h3 : C.index ≤ 3 := by
      rw [Subgroup.index_eq_card]
      omega
    have hdvd : C.index ∣ Nat.card ↥W := C.index_dvd_card
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hW2
    rw [hk] at hdvd
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hi'] at h3 ⊢
    rcases i with _ | _ | i
    · norm_num
    · norm_num
    · exfalso
      have : 4 ≤ 2 ^ (i + 1 + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (i + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hCc : Nat.card ↥C ≤ 64 := by
    have hle : C.map W.subtype ≤ G ⊓ Subgroup.centralizer ({z} : Set Γ) := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨hYG (hWY w.2), Subgroup.mem_subgroupOf.1 hw⟩
    have := hmax _ hle (hW2.to_subgroup C |>.map _)
    rwa [Subgroup.card_map_of_injective W.subtype_injective] at this
  have hWc : Nat.card ↥W ≤ 128 := by
    have h := C.card_mul_index
    calc Nat.card ↥W = Nat.card ↥C * C.index := h.symm
      _ ≤ 64 * 2 := Nat.mul_le_mul hCc hidxC
      _ = 128 := by norm_num
  have hPsW : Ps < W := lt_of_le_of_ne le_sup_left fun h =>
    hyPs (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have := Subgroup.card_lt_of_lt hPsW
  omega

end CaseII

end CFSG.CGT.Foote82
