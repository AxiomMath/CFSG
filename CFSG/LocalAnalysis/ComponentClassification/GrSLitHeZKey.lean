module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZCase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.Sporadic.He.Simple
public import Certificates.Certificate2022
public import Certificates.Certificate3168
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.HeZ

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem center_eq_bot_of_held {L : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) : center ↥L = ⊥ := by
  have : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_held
    apply hab
    have hb : e.symm b ∈ center ↥L := by rw [h]; exact mem_top _
    have h1 := mem_center_iff.mp hb (e.symm a)
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h1

theorem card_gsFixedLayer (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact) {L : Subgroup X}
    (hL : Nonempty (↥L ≃* Blueprint.NativeSporadic.He)) {u : X} (hu : HeldTwoA L u) :
    Nat.card (gsFixedLayer L u) = 80640 := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (center ↥(gsFixedLayer L u))
  rw [GSThmB.card_of_lieModel_L34 (hLay X L hL u hu).2, (hAK X L hL u hu).1] at h1
  exact h1

theorem eq_of_le_normalizer {L L' : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) (hOut : Group.IsSolvable (OuterAutomorphisms.Outer ↥L))
    (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1) (hL'N : L' ≤ normalizer (L : Set X))
    (e' : ↥L' ≃* Blueprint.NativeSporadic.He) (hL'p : ⁅L', L'⁆ = L')
    (hfour : ∃ y₁ ∈ L', ∃ y₂ ∈ L', y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁) : L' = L := by
  have hZ := center_eq_bot_of_held e
  have : IsSimpleGroup ↥L' := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He e'
  set hQ := SeitzReduction.perfect_le_sup_centralizer hOut hL'p hL'N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sndHom hZ hQ).ker with h | h
  · exfalso
    have hinj : Function.Injective (sndHom hZ hQ) := (MonoidHom.ker_eq_bot_iff _).mp h
    obtain ⟨y₁, h₁, y₂, h₂, hy₁, hy₂, h1, h2, hne, hc⟩ := hfour
    have hsq : ∀ (y : X) (hy : y ∈ L'), y * y = 1 →
        ((sndHom hZ hQ ⟨y, hy⟩ : ↥(centralizer (L : Set X))) : X) *
          (sndHom hZ hQ ⟨y, hy⟩ : X) = 1 := fun y hy hyy => by
      rw [← coe_mul, ← map_mul, show (⟨y, hy⟩ : ↥L') * ⟨y, hy⟩ = 1 from Subtype.ext hyy,
        map_one, OneMemClass.coe_one]
    have hne1 : ∀ (y : X) (hy : y ∈ L'), y ≠ 1 →
        ((sndHom hZ hQ ⟨y, hy⟩ : ↥(centralizer (L : Set X))) : X) ≠ 1 := fun y hy hy1 h => by
      apply hy1
      have : sndHom hZ hQ ⟨y, hy⟩ = sndHom hZ hQ 1 := by rw [map_one]; exact Subtype.ext h
      exact congrArg Subtype.val (hinj this)
    refine false_of_pair hrank (sndHom hZ hQ ⟨y₁, h₁⟩).2 (sndHom hZ hQ ⟨y₂, h₂⟩).2
      (hsq y₁ h₁ hy₁) (hsq y₂ h₂ hy₂) (hne1 y₁ h₁ h1) (hne1 y₂ h₂ h2) (fun h => hne ?_) ?_
    · exact congrArg Subtype.val (hinj (Subtype.ext h))
    · rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul,
        show (⟨y₁, h₁⟩ : ↥L') * ⟨y₂, h₂⟩ = ⟨y₂, h₂⟩ * ⟨y₁, h₁⟩ from Subtype.ext hc]
  · have hle : L' ≤ L := fun x hx =>
      (mem_ker_sndHom_iff hZ hQ ⟨x, hx⟩).mp (by rw [h]; exact mem_top _)
    exact le_antisymm hle (by
      have := eq_of_le_of_card_ge hle
        (by rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv])
      exact this.ge)

omit [Finite X] in
theorem mem_map_conj_iff {L : Subgroup X} {g x : X} :
    x ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g⁻¹ * (g * l * g⁻¹) * g = l by group]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem key
    (hOutS : HeldOuterSolvableFact) (hInv : HeldInvolAutFact) (hAK : HeldTwoAKFact)
    (hB2 : HeldTwoBFact) (hSyl : HeldSylowFourFact) (hLay : HeldTwoALayerFact)
    (hFour : HeldTwoAFourFact) (hBC : HeldTwoBCentralizerFact)
    {L : Subgroup X} (hstd : IsStandardSubgroup L) (eL : ↥L ≃* Blueprint.NativeSporadic.He)
    (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1)
    (h37 : ∀ u : X, HeldTwoA L u → centralizer ({u} : Set X) ≤ normalizer (L : Set X))
    {a : X} (ha : orderOf a = 2) (haC : a ∈ centralizer (L : Set X))
    {g : X} (hga : g * a * g⁻¹ * a = a * (g * a * g⁻¹)) (hne : g * a * g⁻¹ ≠ a)
    {u₁ : X} (hu₁ : HeldTwoA L u₁) (hcomm : g * a * g⁻¹ * u₁ = u₁ * (g * a * g⁻¹)) :
    ∃ y : X, y ≠ 1 ∧ y ∈ (center ↥(gsFixedLayer L u₁)).map (gsFixedLayer L u₁).subtype ∧
      g * a * g⁻¹ = a * y := by
  set t₁ := g * a * g⁻¹ with ht₁def
  have hZ := center_eq_bot_of_held eL
  have hOut := hOutS X L ⟨eL⟩
  have hLp : ⁅L, L⁆ = L := isPerfect_iff.mp hstd.1.1
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have ht₁t₁ : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = g * (a * a) * g⁻¹ := by rw [ht₁def]; group
      _ = 1 := by rw [haa]; group
  have ht₁1 : t₁ ≠ 1 := fun h => ha1 (by
    calc a = g⁻¹ * t₁ * g := by rw [ht₁def]; group
      _ = 1 := by rw [h]; group)
  have hCa := centralizer_le_normalizer hstd haC ha
  have ht₁N : t₁ ∈ normalizer (L : Set X) := hCa (mem_centralizer_singleton_iff.mpr hga)
  have ht₁C : t₁ ∉ centralizer (L : Set X) := fun h =>
    false_of_pair hrank haC h haa ht₁t₁ ha1 ht₁1 (fun h' => hne h'.symm) hga.symm
  set L₁ : Subgroup X := L.map (MulAut.conj g).toMonoidHom with hL₁def
  have eL₁ : ↥L₁ ≃* Blueprint.NativeSporadic.He :=
    (L.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans eL
  have hL₁p : ⁅L₁, L₁⁆ = L₁ := by rw [hL₁def, ← map_commutator, hLp]
  have ht₁L₁ : t₁ ∈ centralizer (L₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' := mem_map_conj_iff.mp hx
    have hal := mem_centralizer_iff.mp haC _ hx'
    calc x * t₁ = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by rw [ht₁def]; group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [hal]
      _ = t₁ * x := by rw [ht₁def]; group
  have hN₁ : centralizer ({t₁} : Set X) ≤ normalizer (L₁ : Set X) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.mp hy
      calc g⁻¹ * y * g * a = g⁻¹ * (y * t₁) * g := by rw [ht₁def]; group
        _ = g⁻¹ * (t₁ * y) * g := by rw [h1]
        _ = a * (g⁻¹ * y * g) := by rw [ht₁def]; group
    have hyN := hCa hy'
    rw [mem_normalizer_iff]
    intro x
    rw [mem_map_conj_iff, mem_map_conj_iff, mem_normalizer_iff.mp hyN]
    rw [show g⁻¹ * y * g * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g by group]
  have hu₁N₁ : u₁ ∈ normalizer (L₁ : Set X) := hN₁ (mem_centralizer_singleton_iff.mpr hcomm.symm)
  obtain ⟨z₁, hz₁, z₂, hz₂, hzz₁, hzz₂, hz₁1, hz₂1, hz12, hzc⟩ := hFour X L ⟨eL⟩ u₁ hu₁
  have hKL : gsFixedLayer L u₁ ≤ L := (gsFixedLayer_le_inf L u₁).trans inf_le_left
  have hconj : ∀ x : X, g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := fun x => by group
  have hfour₁ : ∃ y₁ ∈ L₁, ∃ y₂ ∈ L₁, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧
      y₁ ≠ y₂ ∧ y₁ * y₂ = y₂ * y₁ := by
    refine ⟨g * z₁ * g⁻¹, ⟨z₁, hKL hz₁, rfl⟩, g * z₂ * g⁻¹, ⟨z₂, hKL hz₂, rfl⟩, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hconj, hzz₁]; group
    · rw [hconj, hzz₂]; group
    · intro h; apply hz₁1
      calc z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h; apply hz₂1
      calc z₂ = g⁻¹ * (g * z₂ * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h; apply hz12
      calc z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
        _ = z₂ := by rw [h]; group
    · calc g * z₁ * g⁻¹ * (g * z₂ * g⁻¹) = g * (z₁ * z₂) * g⁻¹ := by group
        _ = g * (z₂ * z₁) * g⁻¹ := by rw [hzc]
        _ = g * z₂ * g⁻¹ * (g * z₁ * g⁻¹) := by group
  have hL₁M : ¬ L₁ ≤ normalizer (L : Set X) := by
    intro h
    have heq := eq_of_le_normalizer eL hOut hrank h eL₁ hL₁p hfour₁
    have hgN : g ∈ normalizer (L : Set X) := mem_normalizer_iff_map_conj_eq.mpr heq
    exact ht₁C ((mem_normalizer_iff.mp (HeEnd.normalizer_le_normalizer_centralizer L hgN) a).mp
      haC)
  have hu₁M := h37 u₁ hu₁
  obtain ⟨hKp, hKt⟩ := hLay X L ⟨eL⟩ u₁ hu₁
  obtain ⟨hKZ, hKS, hKC⟩ := hAK X L ⟨eL⟩ u₁ hu₁
  have hKc := card_gsFixedLayer hLay hAK ⟨eL⟩ hu₁
  have hu₁L : u₁ ∈ L := hu₁.1
  have ht₁Q : ∀ Q : Subgroup X, Q ≤ L₁ → ∀ q ∈ Q, t₁ * q = q * t₁ := fun Q hQ q hq =>
    (mem_centralizer_iff.mp ht₁L₁ q (hQ hq)).symm
  have hQN : ∀ Q : Subgroup X, Q ≤ centralizer ({u₁} : Set X) → Q ≤ normalizer (L : Set X) :=
    fun Q hQ => hQ.trans hu₁M
  have hcent : ∀ k ∈ gsFixedLayer L u₁, t₁ * k = k * t₁ := by
    by_cases hu₁C₁ : u₁ ∈ centralizer (L₁ : Set X)
    · exfalso
      apply hL₁M
      intro x hx
      apply hu₁M
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hu₁C₁ x hx
    have hu₁u₁ : u₁ * u₁ ∈ centralizer (L₁ : Set X) := by
      rw [← sq, ← hu₁.2.1, pow_orderOf_eq_one]
      exact one_mem _
    rcases hInv X L₁ ⟨eL₁⟩ u₁ hu₁N₁ hu₁u₁ hu₁C₁ with ⟨y', hy'L₁, hy'2, hy'c⟩ |
        ⟨-, -, -, Q, hQL₁, hQu, hQp, hQc, hQZ, hQs, hQf⟩
    ·
      have hcy' : ∀ x ∈ L₁ ⊓ centralizer ({y'} : Set X), u₁ * x = x * u₁ := by
        intro x hx
        obtain ⟨hxL₁, hxy⟩ := mem_inf.mp hx
        have h1 := mem_centralizer_iff.mp hy'c x hxL₁
        have h2 := mem_centralizer_singleton_iff.mp hxy
        calc u₁ * x = y' * (y'⁻¹ * u₁ * x) := by group
          _ = y' * (x * (y'⁻¹ * u₁)) := by rw [← h1]
          _ = (y' * x) * (y'⁻¹ * u₁) := by group
          _ = (x * y') * (y'⁻¹ * u₁) := by rw [h2]
          _ = x * u₁ := by group
      have hQu' : L₁ ⊓ centralizer ({y'} : Set X) ≤ centralizer ({u₁} : Set X) := fun x hx =>
        mem_centralizer_singleton_iff.mpr (hcy' x hx).symm
      by_cases hK : gsFixedLayer L₁ y' = ⊥
      ·
        exfalso
        obtain ⟨hHp, -, -, -, w₁, hw₁H, -, -, hw₁A, -⟩ := hBC X L₁ ⟨eL₁⟩ y' hy'L₁ hy'2 hK
        obtain ⟨hQc', hQn'⟩ := hB2 X L₁ ⟨eL₁⟩ y' hy'L₁ hy'2 hK
        have hy'y' : y' * y' = 1 := by rw [← sq, ← hy'2, pow_orderOf_eq_one]
        have hw₁w₁ : w₁ * w₁ = 1 := by rw [← sq, ← hw₁A.2.1, pow_orderOf_eq_one]
        have hy'1 : y' ≠ 1 := fun h => by rw [h, orderOf_one] at hy'2; norm_num at hy'2
        have hw₁1 : w₁ ≠ 1 := fun h => by
          have h' := hw₁A.2.1
          rw [h, orderOf_one] at h'
          norm_num at h'
        have hy'w : y' ≠ w₁ := fun h => hw₁A.2.2 (h ▸ hK)
        have hy'wc : y' * w₁ = w₁ * y' :=
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hw₁H).2).symm
        exact false_of_case_twoB hZ hOut hrank (hQN _ hQu') hHp hu₁L hQu' hKS hKc hQc'
          (fun N hNQ hNn hNne => hQn' N hNQ hNn hNne)
          ⟨y', mem_inf.mpr ⟨hy'L₁, mem_centralizer_singleton_iff.mpr rfl⟩, w₁, hw₁H, hy'y',
            hw₁w₁, hy'1, hw₁1, hy'w, hy'wc⟩
          (fun T hTQ hT N hNT hNn hN4 =>
            hSyl X L₁ ⟨eL₁⟩ T (hTQ.trans inf_le_left) hT N hNT hNn hN4)
          ht₁N (ht₁Q _ inf_le_left)
      ·
        have hy'A : HeldTwoA L₁ y' := ⟨hy'L₁, hy'2, hK⟩
        obtain ⟨hQp', hQt'⟩ := hLay X L₁ ⟨eL₁⟩ y' hy'A
        obtain ⟨hQZ', -, -⟩ := hAK X L₁ ⟨eL₁⟩ y' hy'A
        obtain ⟨v₁, hv₁, v₂, hv₂, hvv₁, hvv₂, hv₁1, hv₂1, hv12, hvc⟩ :=
          hFour X L₁ ⟨eL₁⟩ y' hy'A
        have hQL : gsFixedLayer L₁ y' ≤ L₁ ⊓ centralizer ({y'} : Set X) :=
          gsFixedLayer_le_inf L₁ y'
        exact comm_of_case_twoA hZ hOut hrank (hQN _ (hQL.trans hQu')) hQp' hu₁L
          (hQL.trans hQu') hKS hKt hKp hKZ hQt' hQZ'
          ⟨v₁, hv₁, v₂, hv₂, hvv₁, hvv₂, hv₁1, hv₂1, hv12, hvc⟩ ht₁N
          (ht₁Q _ (hQL.trans inf_le_left))
    ·
      exfalso
      exact false_of_case_outer hZ hOut hrank (hQN _ hQu) hQp hu₁L hQu hKS hKt hKZ hKc hQc hQZ
        hQs hQf ht₁N (ht₁Q _ hQL₁)
  have ht₁t₁C : t₁ * t₁ ∈ centralizer (L : Set X) := by rw [ht₁t₁]; exact one_mem _
  rcases hInv X L ⟨eL⟩ t₁ ht₁N ht₁t₁C ht₁C with ⟨y, hyL, hy2, hyc⟩ | ⟨-, -, hbound, -⟩
  · have hyK : ∀ k ∈ gsFixedLayer L u₁, y * k = k * y := by
      intro k hk
      have h1 := hcent k hk
      have h2 : k * (y⁻¹ * t₁) = (y⁻¹ * t₁) * k := mem_centralizer_iff.mp hyc k (hKL hk)
      have hyt : y * (y⁻¹ * t₁) = t₁ := by group
      calc y * k = y * (k * (y⁻¹ * t₁)) * (y⁻¹ * t₁)⁻¹ := by group
        _ = y * ((y⁻¹ * t₁) * k) * (y⁻¹ * t₁)⁻¹ := by rw [h2]
        _ = t₁ * k * (y⁻¹ * t₁)⁻¹ := by rw [← hyt]; group
        _ = k * t₁ * (y⁻¹ * t₁)⁻¹ := by rw [h1]
        _ = k * y := by group
    rcases hKC y hyL hyK with h1 | ⟨hyA, hyZ⟩
    · exfalso
      rw [h1, orderOf_one] at hy2
      norm_num at hy2
    · set c := y⁻¹ * t₁ with hcdef
      have hcy : t₁ = y * c := by rw [hcdef]; group
      have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
      have hyc' : y * c = c * y := mem_centralizer_iff.mp hyc y hyL
      have hcc : c * c = 1 := by
        have h1 : y * y * (c * c) = 1 := by
          calc y * y * (c * c) = y * (y * c) * c := by group
            _ = y * (c * y) * c := by rw [hyc']
            _ = (y * c) * (y * c) := by group
            _ = 1 := by rw [← hcy, ht₁t₁]
        rwa [hyy, one_mul] at h1
      have hay : y * a = a * y := mem_centralizer_iff.mp haC y hyL
      have hca : c * a = a * c := by
        calc c * a = y⁻¹ * (t₁ * a) := by rw [hcdef]; group
          _ = y⁻¹ * (a * t₁) := by rw [hga]
          _ = (y⁻¹ * a) * t₁ := by group
          _ = (a * y⁻¹) * t₁ := by
            rw [show y⁻¹ * a = a * y⁻¹ from by
              calc y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
                _ = y⁻¹ * (y * a) * y⁻¹ := by rw [hay]
                _ = a * y⁻¹ := by group]
          _ = a * c := by rw [hcdef]; group
      by_cases hc1 : c = 1
      · exfalso
        have ht₁y : t₁ = y := by rw [hcy, hc1, mul_one]
        apply hL₁M
        intro x hx
        apply h37 y hyA
        rw [mem_centralizer_singleton_iff, ← ht₁y]
        exact mem_centralizer_iff.mp ht₁L₁ x hx
      · by_cases hca' : c = a
        · refine ⟨y, fun h => by rw [h, orderOf_one] at hy2; norm_num at hy2, hyZ, ?_⟩
          rw [hcy, hca', hay]
        · exfalso
          exact false_of_pair hrank haC hyc haa hcc ha1 hc1 (fun h => hca' h.symm) hca.symm
  · exfalso
    have h1 := hbound (gsFixedLayer L u₁) hKL
      (fun k hk => mem_centralizer_singleton_iff.mpr (hcent k hk).symm)
    rw [hKc] at h1
    norm_num at h1

end CFSG.ComponentClassification.GrSLit.HeZ
