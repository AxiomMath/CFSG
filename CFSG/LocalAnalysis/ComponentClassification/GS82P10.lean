module

public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Chain
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Loc
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Centre
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Typ
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3
public import CFSG.LieType.Multipliers.L34CenterExponent

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open CFSG Subgroup GSThmB.HConfig
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem typC_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B)
    (h : TypC A) : TypC B := by
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' e
  let eO : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  have hc : (center (A ⧸ pPrimeCore 2 A)).map eO.toMonoidHom = center (B ⧸ pPrimeCore 2 B) :=
    Subgroup.map_center_eq eO
  let eC := QuotientGroup.congr _ _ eO hc
  rcases h with hO | ⟨n, hn, hQ, hcard, ⟨eAlt⟩⟩ | ⟨hL, hE⟩
  · exact Or.inl (oddLieType_of_mulEquiv eZ hO)
  · refine Or.inr (Or.inl ⟨n, hn, LocalCores.isQuasisimple_of_mulEquiv eO hQ, ?_,
      ⟨eC.symm.trans eAlt⟩⟩)
    rw [← Nat.card_congr (Subgroup.centerCongr eO).toEquiv]
    exact hcard
  · exact Or.inr (Or.inr ⟨Blueprint.LieModel.of_mulEquiv eC hL, fun hEB =>
      hE (IsElementaryAbelian.of_mulEquiv (Subgroup.centerCongr eO).symm hEB)⟩)

theorem eq_of_isPComponent_subgroupOf {H : Type} [Group H] [Finite H] {M K : Subgroup H}
    (hM : IsPComponent 2 M) (hKM : K ≤ M) (hK : IsPComponent 2 (K.subgroupOf M)) : K = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have hMp : Group.IsPerfect M := CatalogueBHeldSmallCore.pComponent_perfect 2 M hM
  have htop : IsPComponent 2 (⊤ : Subgroup ↥M) := by
    rw [← HarrisLit.isTwoComponent_iff_isPComponent]
    let e : ↥(⊤ : Subgroup ↥M) ≃* ↥M := Subgroup.topEquiv
    refine ⟨Subgroup.IsSubnormal.top, Group.IsPerfect.top_iff.mpr hMp, ?_⟩
    exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm hMq
  have hK' := hK
  obtain ⟨Kc, hKc, -, hKmap, -⟩ := hK'
  have hKc1 : Kc = ⊤ := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hMq hKc.2 with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hKc.1
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hab' : a * b = b * a := Subtype.ext (mem_center_iff.mp (h a.2) b).symm
      rw [← QuotientGroup.mk_mul, hab', QuotientGroup.mk_mul]
  have h1 : K.subgroupOf M = ⊤ := by
    refine UnbalancedLayer.pComponent_eq_of_map_eq hK htop ?_
    rw [hKmap, hKc1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact le_antisymm hKM (Subgroup.subgroupOf_eq_top.mp h1)

theorem orbJoin_le_orbJoin_of_le_sup {H : Type} [Group H] {B T K : Subgroup H} {b : H}
    (hb : b ∈ B) (hT : T ≤ K ⊔ cj b K) : orbJoin B T ≤ orbJoin B K := by
  refine iSup₂_le fun g hg => ?_
  calc cj g T ≤ cj g (K ⊔ cj b K) := map_mono hT
    _ = cj g K ⊔ cj (g * b) K := by rw [cj, Subgroup.map_sup, cj_mul]
    _ ≤ orbJoin B K := sup_le (cj_le_orbJoin hg) (cj_le_orbJoin (mul_mem hg hb))

theorem center_quot_ne_bot_of_mem_fusionZStar {H : Type} [Group H] [Finite H] {M : Subgroup H}
    {w : H} (hw : orderOf w = 2) (hwM : w ∈ (Open.fusionZStar ↥M).map M.subtype) :
    center (↥M ⧸ pPrimeCore 2 ↥M) ≠ ⊥ := by
  obtain ⟨k, hk, rfl⟩ := hwM
  intro hZ
  have hkc : (QuotientGroup.mk k : ↥M ⧸ pPrimeCore 2 ↥M) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := GSThmB.OddQuot.mem_fusionZStar_iff.mp hk m
    have h2 : (QuotientGroup.mk ⁅k, m⁆ : ↥M ⧸ pPrimeCore 2 ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hkc
  have h3 : orderOf k ∣ Nat.card ↥(pPrimeCore 2 ↥M) := Subgroup.orderOf_dvd_natCard _ hkc
  have hk2 : orderOf k = 2 := (Subgroup.orderOf_coe k).symm.trans hw
  rw [hk2] at h3
  exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    (even_iff_two_dvd.mpr h3)

theorem p10_disjunction
    {M : Type} [Group M] [Finite M] (hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M)) (h : TypC M)
    (q₀ : ℕ) :
    (∃ q₂ : ℕ, Odd q₂ ∧ q₀ ≤ q₂ ∧ HarrisLit.IsSLTwoOver q₂ (M ⧸ pPrimeCore 2 M)) ∨
      Blueprint.OddLieType (M ⧸ Open.fusionZStar M) ∨
      (∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (M ⧸ pPrimeCore 2 M) n) ∨
      (GH74.GLS.IsL34Quotient (M ⧸ pPrimeCore 2 M) ∧
        Monoid.exponent ↥(center (M ⧸ pPrimeCore 2 M)) = 4) := by
  rcases h with hO | hA | ⟨hL, hE⟩
  · exact Or.inr (Or.inl hO)
  · exact Or.inr (Or.inr (Or.inl hA))
  · refine Or.inr (Or.inr (Or.inr ⟨hL, ?_⟩))
    have hd := exponent_center_dvd_four hMq (isPGroup_center_quot M) hL
    have hnd : ¬ Monoid.exponent ↥(center (M ⧸ pPrimeCore 2 M)) ∣ 2 := fun h2 =>
      hE { toIsMulCommutative := inferInstance, exponent_dvd_p := h2 }
    obtain ⟨c, hc, hce⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Monoid.exponent ↥(center (M ⧸ pPrimeCore 2 M)) ∣ 2 ^ 2 by simpa using hd)
    rw [hce] at hnd ⊢
    interval_cases c
    · exact absurd (by norm_num) hnd
    · exact absurd (by norm_num) hnd
    · norm_num

theorem typC_pump_sub (hP : TypPumpInput) {X : Type} [Group X] [Finite X]
    (hKX : SectionRank.IsKGroupCat X) (β : MulAut X) (hβ : ∀ x, β (β x) = x)
    {X₁ : Subgroup X} (hX₁ : IsPComponent 2 X₁) (hinv : X₁.map β.toMonoidHom = X₁)
    (hZX₁ : center (↥X₁ ⧸ pPrimeCore 2 ↥X₁) ≠ ⊥) {T : Subgroup X} (hTF : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) (hTX : T ≤ X₁)
    (hZT : center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥) (hTyp : TypC ↥T) : TypC ↥X₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX₁q : HarrisLit.IsTwoQuasisimple ↥X₁ :=
    ((HarrisLit.isTwoComponent_iff_isPComponent X₁).mpr hX₁).2
  let β₁ : MulAut ↥X₁ := (β.subgroupMap X₁).trans (MulEquiv.subgroupCongr hinv)
  have hβ₁ : ∀ y : ↥X₁, ((β₁ y : ↥X₁) : X) = β y := fun y => rfl
  have hβ₁β₁ : ∀ y, β₁ (β₁ y) = y := fun y => Subtype.ext (by rw [hβ₁, hβ₁]; exact hβ y)
  have hfix : fixedSubgroup β₁ = (fixedSubgroup β).subgroupOf X₁ := by
    ext y
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf,
      LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, ← hβ₁]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set T₁ := T.subgroupOf X₁ with hT₁
  have hT₁F : T₁ ≤ fixedSubgroup β₁ := by
    rw [hfix]
    intro y hy
    exact hTF hy
  have hT₁p : IsPComponent 2 (T₁.subgroupOf (fixedSubgroup β₁)) := by
    rw [hfix, OddStandard.Solomon75.isPComponent_subgroupOf_subgroupOf_iff hTF hTX]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTF hTX) inf_le_left hT
  let eT : ↥T₁ ≃* ↥T := subgroupOfEquivOfLe hTX
  have hZT₁ : center (↥T₁ ⧸ pPrimeCore 2 ↥T₁) ≠ ⊥ := fun h =>
    hZT (center_eq_bot_of_mulEquiv' (QuotientGroup.congr _ _ eT (pPrimeCore_map_iso 2 eT)).symm h)
  exact hP ↥X₁ (hKX.subgroup X₁) hX₁q hZX₁ β₁ hβ₁β₁ T₁ hT₁F hT₁p hZT₁
    (typC_of_mulEquiv eT.symm hTyp)

theorem p10Claim (hP : TypPumpInput) (n : ℕ) :
    ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ Bs : Subgroup H, IsPGroup 2 Bs → Bs ≤ normalizer (M : Set H) →
    ∀ w : H, orderOf w = 2 → w ∈ (Open.fusionZStar ↥M).map M.subtype →
    ∀ B : Subgroup H, B ≤ Bs → Bs ≤ normalizer (B : Set H) → Nat.card B ≤ n →
    ∀ T : Subgroup H, T ≤ M ⊓ centralizer (B : Set H) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer (B : Set H))) →
      w ∈ orbJoin Bs T → TypC ↥T → TypC ↥M := by
  induction n with
  | zero =>
    intro H _ _ _ M _ Bs _ _ w _ _ B _ _ hcard
    exact absurd hcard (by have := Nat.card_pos (α := B); omega)
  | succ n ih =>
  intro H _ _ hK M hM Bs hBs hBsN w hw hwM B hBBs hBsB hcard T hT hTp hwT hTyp
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 B := hBs.to_le hBBs
  have hBN : B ≤ normalizer (M : Set H) := hBBs.trans hBsN
  by_cases hB1 : B = ⊥
  ·
    subst hB1
    have hMC : M ⊓ centralizer ((⊥ : Subgroup H) : Set H) = M := by
      rw [centralizer_eq_top_iff_subset.mpr (by
        rw [coe_bot, Set.singleton_subset_iff]; exact one_mem _), inf_top_eq]
    rw [hMC] at hT hTp
    obtain rfl := eq_of_isPComponent_subgroupOf hM hT hTp
    exact hTyp
  obtain ⟨B₁', hidx, hBsB₁⟩ := exists_index_two_normalized hBs hBBs hBsB hB1
  have hB₁'n : B₁'.Normal := Subgroup.normal_of_index_eq_two hidx
  set B₁ := B₁'.map B.subtype with hB₁def
  have hB₁B : B₁ ≤ B := map_subtype_le _
  have hB₁card : Nat.card B₁ ≤ n := by
    have h1 : Nat.card B₁ = Nat.card B₁' :=
      (Nat.card_congr (B₁'.equivMapOfInjective _ B.subtype_injective).toEquiv).symm
    have h2 := B₁'.card_mul_index
    rw [hidx] at h2
    have h3 : Nat.card B₁' < Nat.card B := by
      have := Nat.card_pos (α := B₁')
      omega
    omega
  obtain ⟨b', hb'⟩ : ∃ b' : B, b' ∉ B₁' := by
    by_contra hall
    push Not at hall
    have : B₁' = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [this, index_top] at hidx
    exact absurd hidx (by norm_num)
  set b : H := (b' : H) with hbdef
  have hbB : b ∈ B := b'.2
  have hb2 : b ^ 2 ∈ B₁ :=
    ⟨b' ^ 2, Subgroup.sq_mem_of_index_two hidx b', by simp [hbdef]⟩
  have hbN₁ : b ∈ normalizer (B₁ : Set H) := hBsB₁ (hBBs hbB)
  have hCB : centralizer (B : Set H) = centralizer (B₁ : Set H) ⊓ centralizer ({b} : Set H) := by
    apply le_antisymm
    · exact le_inf (centralizer_le hB₁B) (centralizer_le (Set.singleton_subset_iff.mpr hbB))
    · rintro c ⟨hc1, hc2⟩
      rw [mem_centralizer_iff]
      intro x hx
      by_cases hxB : (⟨x, hx⟩ : B) ∈ B₁'
      · exact mem_centralizer_iff.mp hc1 x ⟨_, hxB, rfl⟩
      · have hy : b'⁻¹ * ⟨x, hx⟩ ∈ B₁' := by
          by_contra hy
          have := (Subgroup.mul_mem_iff_of_index_two hidx (a := b'⁻¹) (b := ⟨x, hx⟩)).mpr
          exact hy (this ⟨fun h => (hb' (by simpa using inv_mem h)).elim,
            fun h => (hxB h).elim⟩)
        set y : H := ((b'⁻¹ * ⟨x, hx⟩ : B) : H) with hydef
        have hyc : y * c = c * y := mem_centralizer_iff.mp hc1 _ ⟨_, hy, rfl⟩
        have hbc : b * c = c * b := by
          have := mem_centralizer_singleton_iff.mp hc2
          first | exact this | exact this.symm
        have hx' : x = b * y := by simp [hydef, hbdef]
        rw [hx']
        calc b * y * c = b * (y * c) := by group
          _ = b * (c * y) := by rw [hyc]
          _ = (b * c) * y := by group
          _ = (c * b) * y := by rw [hbc]
          _ = c * (b * y) := by group
  set X := M ⊓ centralizer (B₁ : Set H) with hXdef
  have hbX : b ∈ normalizer (X : Set H) :=
    GSThmB.Pump516.mem_normalizer_inf (hBN hbB) (mem_normalizer_centralizer hbN₁)
  have hBsX : Bs ≤ normalizer (X : Set H) := fun g hg =>
    GSThmB.Pump516.mem_normalizer_inf (hBsN hg) (mem_normalizer_centralizer (hBsB₁ hg))
  let β : MulAut ↥X := X.normalizerMonoidHom ⟨b, hbX⟩
  have hβapp : ∀ x : ↥X, ((β x : ↥X) : H) = b * x * b⁻¹ := fun x => rfl
  have hb2c : ∀ x : ↥X, b ^ 2 * x = x * b ^ 2 := fun x =>
    mem_centralizer_iff.mp (mem_inf.mp x.2).2 _ hb2
  have hββ : ∀ x, β (β x) = x := by
    intro x
    apply Subtype.ext
    rw [hβapp, hβapp]
    calc b * (b * (x : H) * b⁻¹) * b⁻¹ = (b * b) * x * (b * b)⁻¹ := by group
      _ = x := by rw [← sq, hb2c x]; group
  have hfix : fixedSubgroup β = (M ⊓ centralizer (B : Set H)).subgroupOf X := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, hCB, ← inf_assoc,
      mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have h1 := congrArg Subtype.val h
      rw [hβapp] at h1
      calc (x : H) * b = b * x * b⁻¹ * b := by rw [h1]
        _ = b * x := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hβapp, ← h]
      group
  have hMBX : M ⊓ centralizer (B : Set H) ≤ X := inf_le_inf_left _ (centralizer_le hB₁B)
  have hTX : T ≤ X := hT.trans hMBX
  set T₁ := T.subgroupOf X with hT₁def
  have hT₁F : T₁ ≤ fixedSubgroup β := by
    rw [hfix]
    intro x hx
    exact hT hx
  have hT₁p : IsPComponent 2 (T₁.subgroupOf (fixedSubgroup β)) := by
    rw [hfix, OddStandard.Solomon75.isPComponent_subgroupOf_subgroupOf_iff hT hTX,
      inf_eq_left.mpr hMBX]
    exact hTp
  let eT : ↥T₁ ≃* ↥T := subgroupOfEquivOfLe hTX
  have hBsMB : Bs ≤ normalizer ((M ⊓ centralizer (B : Set H) : Subgroup H) : Set H) := fun g hg =>
    GSThmB.Pump516.mem_normalizer_inf (hBsN hg) (mem_normalizer_centralizer (hBsB hg))
  have hZT : center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥ :=
    center_ne_bot_of_mem_orbJoin inf_le_left hBsMB hT hTp hw hwT hwM
  have hZT₁ : center (↥T₁ ⧸ pPrimeCore 2 ↥T₁) ≠ ⊥ := fun h =>
    hZT (center_eq_bot_of_mulEquiv' (QuotientGroup.congr _ _ eT (pPrimeCore_map_iso 2 eT)).symm h)
  have hTyp₁ : TypC ↥T₁ := typC_of_mulEquiv eT.symm hTyp
  obtain ⟨X₁, hX₁, hcase⟩ := fixedTwoComponentLocation' β hββ hT₁F hT₁p
  set K₁ := X₁.map X.subtype with hK₁def
  have hK₁X : K₁ ≤ X := map_subtype_le _
  have hK₁p : IsPComponent 2 (K₁.subgroupOf X) := by
    have hK₁X₁ : K₁.subgroupOf X = X₁ :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective X₁
    rw [hK₁X₁]
    exact hX₁
  let eK : ↥X₁ ≃* ↥K₁ := X₁.equivMapOfInjective X.subtype X.subtype_injective
  have hβK : (X₁.map β.toMonoidHom).map X.subtype = cj b K₁ := by
    rw [hK₁def, cj, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hTK : T ≤ K₁ ⊔ cj b K₁ := by
    have h1 : T₁ ≤ X₁ ⊔ X₁.map β.toMonoidHom := by
      rcases hcase with ⟨-, h⟩ | ⟨-, h, -⟩
      · exact h.trans le_sup_left
      · exact h
    have h2 := map_mono (f := X.subtype) h1
    rw [Subgroup.map_sup, hβK, hT₁def, map_subgroupOf_eq_of_le hTX] at h2
    exact h2
  have hwK₁ : w ∈ orbJoin Bs K₁ := orbJoin_le_orbJoin_of_le_sup (hBBs hbB) hTK hwT
  have hZK₁ : center (↥K₁ ⧸ pPrimeCore 2 ↥K₁) ≠ ⊥ :=
    center_ne_bot_of_mem_orbJoin inf_le_left hBsX hK₁X hK₁p hw hwK₁ hwM
  have hZX₁ : center (↥X₁ ⧸ pPrimeCore 2 ↥X₁) ≠ ⊥ := fun h =>
    hZK₁ (center_eq_bot_of_mulEquiv' (QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)).symm h)
  have hTypX₁ : TypC ↥X₁ := by
    rcases hcase with ⟨hinv, hT₁X₁⟩ | ⟨-, -, ⟨φ, hφ⟩⟩
    · exact typC_pump_sub hP (hK.subgroup X) β hββ hX₁ hinv hZX₁ hT₁F hT₁p hT₁X₁ hZT₁ hTyp₁
    · have hX₁q : IsQuasisimple (↥X₁ ⧸ pPrimeCore 2 ↥X₁) :=
        ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 X₁).mp hX₁).2.2
      have hT₁q : IsQuasisimple (↥T₁ ⧸ pPrimeCore 2 ↥T₁) :=
        GH74.GLS.TwoThin.isQuasisimple_hat_of_isPComponent hT₁p |> fun h =>
          LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hT₁F)
            (pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hT₁F))) h
      exact typC_of_surjective_quot hX₁q hT₁q φ hφ hZX₁ hTyp₁
  exact ih H hK M hM Bs hBs hBsN w hw hwM B₁ (hB₁B.trans hBBs) hBsB₁ hB₁card K₁
    (le_inf (hK₁X.trans inf_le_left) (hK₁X.trans inf_le_right)) (by simpa [hXdef] using hK₁p)
    hwK₁ (typC_of_mulEquiv eK hTypX₁)

end CFSG.ComponentClassification.GS82PumpInputs.P10

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

theorem kgSLTwoSmallInput_of_typPump (hP : TypPumpInput) :
    KGSLTwoSmallInput := by
  intro H _ _ hK M hM B hB hBN T hT hTp q₀ hq₀ hSL w hw hwT hwM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTyp, -⟩ := P10.typC_of_isSLTwoOver hq₀ hSL
  have hMT : TypC ↥M := P10.p10Claim hP (Nat.card B) H hK M hM B hB hBN w hw hwM B le_rfl
    le_normalizer le_rfl T hT hTp (GSThmB.HConfig.le_orbJoin B T hwT) hTyp
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  exact P10.p10_disjunction hMq hMT q₀

end CFSG.ComponentClassification.GS82PumpInputs
