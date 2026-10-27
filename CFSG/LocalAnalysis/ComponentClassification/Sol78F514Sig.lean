module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma42
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCoreOfCentralizer_inf_le {a b : Y} (ha : orderOf a = 2) (hab : a * b = b * a)
    (hb : Group.IsSolvable ↥(centralizer ({b} : Set Y))) :
    oddCoreOfCentralizer a ⊓ centralizer ({b} : Set Y) ≤ oddCoreOfCentralizer b :=
  le_oddCoreOfCentralizer_of_le_coreActionKernel ha hab le_rfl fun _ _ hJ =>
    absurd hJ (@CatalogueBLinearTwoInvolution.no_pComponent_of_solvable _ _ hb 2 _)

omit [Finite Y] in
theorem commute_of_mul_mem {V : Subgroup Y} {f : Y} (hf : f * f = 1)
    (hfV : ∀ v ∈ V, v * f = f * v) {x : Y} (hx : x ∈ V ∨ x * f ∈ V) : x * f = f * x := by
  rcases hx with hx | hx
  · exact hfV x hx
  · have h1 := hfV _ hx
    calc x * f = x * f * f * f := by rw [mul_assoc (x * f), hf, mul_one]
      _ = f * (x * f) * f := by rw [h1]
      _ = f * x := by rw [mul_assoc, mul_assoc, hf, mul_one]

@[expose] def unionMul (V : Subgroup Y) (f : Y) (hf : f * f = 1)
    (hfV : ∀ v ∈ V, v * f = f * v) : Subgroup Y where
  carrier := {x | x ∈ V ∨ x * f ∈ V}
  one_mem' := Or.inl V.one_mem
  mul_mem' := by
    rintro x y hx hy
    have hyf := commute_of_mul_mem hf hfV hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (V.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact V.mul_mem hx hy)
    · right
      rw [mul_assoc, hyf, ← mul_assoc]
      exact V.mul_mem hx hy
    · left
      have : x * y = x * f * (y * f) := by
        rw [hyf, ← mul_assoc, mul_assoc x f f, hf, mul_one]
      rw [this]
      exact V.mul_mem hx hy
  inv_mem' := by
    rintro x hx
    have hxf := commute_of_mul_mem hf hfV hx
    rcases hx with hx | hx
    · exact Or.inl (V.inv_mem hx)
    · right
      have : x⁻¹ * f = (x * f)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hf]
        calc x⁻¹ * f = x⁻¹ * (f * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * f) * x⁻¹ := by rw [hxf]
          _ = f * x⁻¹ := by group
      rw [this]
      exact V.inv_mem hx

omit [Finite Y] in
theorem commute_of_mul_self {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a :=
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha]

omit [Finite Y] in
theorem isElemAbelian_of_sq {E : Subgroup Y} (hsq : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (commute_of_mul_self (hsq a a.2) (hsq b b.2)
    (hsq _ (mul_mem a.2 b.2)))⟩⟩, fun x hx => by rw [sq]; exact hsq x hx⟩

omit [Finite Y] in
theorem mul_self_of_mem_unionMul {V : Subgroup Y} {f : Y} (hf : f * f = 1)
    (hfV : ∀ v ∈ V, v * f = f * v) (hV2 : ∀ v ∈ V, v * v = 1) :
    ∀ x ∈ unionMul V f hf hfV, x * x = 1 := by
  intro x hx
  rcases hx with hx | hx
  · exact hV2 x hx
  · have h1 := hV2 _ hx
    have hvf := hfV _ hx
    have hx' : x = x * f * f := by rw [mul_assoc, hf, mul_one]
    calc x * x = (x * f * f) * (x * f * f) := by rw [← hx']
      _ = (x * f) * (f * (x * f)) * f := by group
      _ = (x * f) * ((x * f) * f) * f := by rw [hvf]
      _ = (x * f) * (x * f) * (f * f) := by group
      _ = 1 := by rw [h1, hf, one_mul]

omit [Finite Y] in
theorem two_mul_card_le_card_unionMul {V : Subgroup Y} {f : Y} (hf : f * f = 1)
    (hfV : ∀ v ∈ V, v * f = f * v) (hfnot : f ∉ V) [Finite Y] :
    2 * Nat.card V ≤ Nat.card (unionMul V f hf hfV) := by
  let φ : V ⊕ V → unionMul V f hf hfV := fun x => match x with
    | Sum.inl v => ⟨v, Or.inl v.2⟩
    | Sum.inr v => ⟨v * f, Or.inr (by rw [mul_assoc, hf, mul_one]; exact v.2)⟩
  have hφ : Function.Injective φ := by
    intro x y h
    have h' := congrArg Subtype.val h
    rcases x with v | v <;> rcases y with w | w
    · exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      apply hfnot
      have h'' : (v : Y) = w * f := h'
      rw [show f = (w : Y)⁻¹ * v by rw [h'']; group]
      exact V.mul_mem (V.inv_mem w.2) v.2
    · exfalso
      apply hfnot
      have h'' : (v : Y) * f = w := h'
      rw [show f = (v : Y)⁻¹ * w by rw [← h'']; group]
      exact V.mul_mem (V.inv_mem v.2) w.2
    · have h'' : (v : Y) * f = w * f := h'
      exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h''))
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_sum, ← two_mul] at h1

omit [Finite Y] in
theorem mem_kleinFour_iff {a b : Y} {ha : a * a = 1} {hb : b * b = 1} {hab : Commute a b}
    {x : Y} : x ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab ↔
      x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
  change x ∈ ({a * b, a, b, 1} : Set Y) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

omit [Finite Y] in
theorem mul_self_of_mem_kleinFour {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) :
    ∀ x ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab, x * x = 1 := by
  intro x hx
  rcases mem_kleinFour_iff.mp hx with h | h | h | h <;> rw [h]
  · calc a * b * (a * b) = a * (b * a) * b := by group
      _ = 1 := by rw [← hab.eq, ← mul_assoc, ha, one_mul, hb]
  · exact ha
  · exact hb
  · exact one_mul 1

omit [Finite Y] in
theorem iSup_kleinFour {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (F : Y → Subgroup Y) :
    ⨆ (v : Y) (_ : v ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab)
      (_ : v ≠ 1), F v = F (a * b) ⊔ F a ⊔ F b := by
  have hab1 : a * b ≠ 1 := fun h => hba (by
    calc b = a⁻¹ * (a * b) := by group
      _ = a := by rw [h, mul_one, inv_eq_of_mul_eq_one_right ha])
  apply le_antisymm
  · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
    rcases mem_kleinFour_iff.mp hv with h | h | h | h <;> rw [h]
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
    · exact absurd h hv1
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup₂_of_le (a * b) (mem_kleinFour_iff.mpr (Or.inl rfl)) (le_iSup_of_le hab1 le_rfl)
    · exact le_iSup₂_of_le a (mem_kleinFour_iff.mpr (Or.inr (Or.inl rfl)))
        (le_iSup_of_le ha1 le_rfl)
    · exact le_iSup₂_of_le b (mem_kleinFour_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
        (le_iSup_of_le hb1 le_rfl)

@[expose] def sigW (t f : Y) : Subgroup Y :=
  oddCoreOfCentralizer (t * f) ⊔ oddCoreOfCentralizer t ⊔ oddCoreOfCentralizer f

omit [Finite Y] in
theorem mem_normalizer_sup {A B : Subgroup Y} {x : Y} (hA : x ∈ normalizer (A : Set Y))
    (hB : x ∈ normalizer (B : Set Y)) : x ∈ normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

section Completion

variable {R : Subgroup Y} {t f : Y} (ht : t * t = 1) (ht1 : t ≠ 1) (htR : t ∈ R)
  (htc : ∀ r ∈ R, r * t = t * r) (hf : f * f = 1) (hfc : ∀ r ∈ R, r * f = f * r) (hfR : f ∉ R)
  (hsR : ∀ r ∈ R, r * r = 1 → r ≠ 1 → Group.IsSolvable ↥(centralizer ({r} : Set Y)))
  (hsF : ∀ r ∈ R, r * r = 1 → Group.IsSolvable ↥(centralizer ({r * f} : Set Y)))
include ht ht1 htR htc hf hfc hfR hsR hsF

theorem sigW_spec {b : Y} (hbR : b ∈ R) (hb : b * b = 1) (hb1 : b ≠ 1) (hbt : b ≠ t) :
    Odd (Nat.card (sigW t f)) ∧
      sigW t f = oddCoreOfCentralizer (t * b) ⊔ oddCoreOfCentralizer t ⊔ oddCoreOfCentralizer b ∧
      b ∈ normalizer (sigW t f : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb : Commute t b := (htc b hbR).symm
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions t b ht hb htb with hV
  have hVR : V ≤ R := fun x hx => by
    rcases mem_kleinFour_iff.mp hx with h | h | h | h <;> rw [h]
    · exact R.mul_mem htR hbR
    · exact htR
    · exact hbR
    · exact R.one_mem
  have hfV : ∀ v ∈ V, v * f = f * v := fun v hv => hfc v (hVR hv)
  set A := unionMul V f hf hfV with hA
  have hA2 := mul_self_of_mem_unionMul hf hfV (mul_self_of_mem_kleinFour ht hb htb)
  have hAe : IsElemAbelian 2 A := isElemAbelian_of_sq hA2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    commute_of_mul_self (hA2 x hx) (hA2 y hy) (hA2 _ (mul_mem hx hy))
  have hA8 : 8 ≤ Nat.card A := by
    have h1 : 2 * Nat.card V ≤ Nat.card A :=
      two_mul_card_le_card_unionMul hf hfV (fun h => hfR (hVR h))
    have h4 : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      t b ht hb ht1 hb1 (Ne.symm hbt) htb).card_four
    omega
  have hsA : ∀ a ∈ A, a ≠ 1 → Group.IsSolvable ↥(centralizer ({a} : Set Y)) := by
    intro a ha ha1
    rcases ha with ha | ha
    · exact hsR a (hVR ha) (hA2 a (Or.inl ha)) ha1
    · have h := hsF (a * f) (hVR ha) (mul_self_of_mem_kleinFour ht hb htb _ ha)
      rwa [mul_assoc, hf, mul_one] at h
  obtain ⟨hWodd, hAW, hWC, -, -⟩ := SignalizerFunctorTheorem.two_signalizer_completion A hAe hA8
    oddCoreOfCentralizer (fun a _ _ => oddCoreOfCentralizer_le_centralizer a)
    (fun a _ _ => odd_card_oddCoreOfCentralizer a)
    (fun a ha _ x hx => mem_normalizer_oddCoreOfCentralizer
      (mem_centralizer_singleton_iff.mpr (hAc x hx a ha)))
    (fun a ha ha1 c hc hc1 => oddCoreOfCentralizer_inf_le
      (orderOf_eq_prime (by rw [sq]; exact hA2 a ha) ha1) (hAc a ha c hc) (hsA c hc hc1))
  set W := ⨆ (a : Y) (_ : a ∈ A) (_ : a ≠ 1), oddCoreOfCentralizer a with hWdef
  have hgen : ∀ (u v : Y) (hu : u * u = 1) (hv : v * v = 1) (huv : Commute u v), u ≠ 1 →
      v ≠ 1 → v ≠ u → GorensteinWalter.kleinFourOfCommutingInvolutions u v hu hv huv ≤ A →
      W = oddCoreOfCentralizer (u * v) ⊔ oddCoreOfCentralizer u ⊔ oddCoreOfCentralizer v := by
    intro u v hu hv huv hu1 hv1 hvu hle
    have h4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions u v hu hv hu1 hv1
      (Ne.symm hvu) huv).card_four
    have hg := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
      (isElemAbelian_of_sq (mul_self_of_mem_kleinFour hu hv huv)) (by rw [h4]; norm_num)
      (hle.trans hAW) (Nat.coprime_two_left.mpr hWodd)
    rw [← iSup_kleinFour hu hv huv hu1 hv1 hvu]
    calc W = _ := hg.symm
      _ = _ := iSup_congr fun a => iSup_congr fun ha => iSup_congr fun ha1 =>
          hWC a (hle ha) ha1
  have htf : Commute t f := hfc t htR
  have hft : f ≠ t := fun h => hfR (h ▸ htR)
  have hf1 : f ≠ 1 := fun h => hfR (h ▸ R.one_mem)
  have hW₀ : W = sigW t f := hgen t f ht hf htf ht1 hf1 hft fun x hx => by
    rcases mem_kleinFour_iff.mp hx with h | h | h | h <;> rw [h]
    · right
      rw [mul_assoc, hf, mul_one]
      exact mem_kleinFour_iff.mpr (Or.inr (Or.inl rfl))
    · exact Or.inl (mem_kleinFour_iff.mpr (Or.inr (Or.inl rfl)))
    · exact Or.inr (by rw [hf]; exact V.one_mem)
    · exact A.one_mem
  have hWb : W = oddCoreOfCentralizer (t * b) ⊔ oddCoreOfCentralizer t ⊔
      oddCoreOfCentralizer b := hgen t b ht hb htb ht1 hb1 hbt fun x hx => Or.inl hx
  rw [← hW₀]
  exact ⟨hWodd, hWb, hAW (Or.inl (mem_kleinFour_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))))⟩

end Completion

section Normalizer

variable {R : Subgroup Y} {t f : Y} (ht : t * t = 1) (ht1 : t ≠ 1) (htR : t ∈ R)
  (htc : ∀ r ∈ R, r * t = t * r) (hf : f * f = 1) (hfc : ∀ r ∈ R, r * f = f * r) (hfR : f ∉ R)
  (hsR : ∀ r ∈ R, r * r = 1 → r ≠ 1 → Group.IsSolvable ↥(centralizer ({r} : Set Y)))
  (hsF : ∀ r ∈ R, r * r = 1 → Group.IsSolvable ↥(centralizer ({r * f} : Set Y)))
include ht ht1 htR htc hf hfc hfR hsR hsF

theorem normalizer_le_normalizer_sigW
    (hcen : ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r * r = 1 → r ≠ 1 → r = t)
    {b : Y} (hbR : b ∈ R) (hb : b * b = 1) (hb1 : b ≠ 1) (hbt : b ≠ t) :
    normalizer (R : Set Y) ≤ normalizer (sigW t f : Set Y) := by
  intro x hx
  obtain ⟨-, hW, -⟩ := sigW_spec ht ht1 htR htc hf hfc hfR hsR hsF hbR hb hb1 hbt
  have hxR : ∀ r, r ∈ R ↔ x * r * x⁻¹ ∈ R := mem_normalizer_iff.mp hx
  have hb'R : x * b * x⁻¹ ∈ R := (hxR b).mp hbR
  have hb'2 : x * b * x⁻¹ * (x * b * x⁻¹) = 1 := by
    rw [show x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ by group, hb]; group
  have hb'1 : x * b * x⁻¹ ≠ 1 := fun h => hb1 (by
    calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hxt : x * t * x⁻¹ = t := by
    refine hcen _ ((hxR t).mp htR) (fun s hs => ?_) ?_ ?_
    · have hs' : x⁻¹ * s * x ∈ R :=
        (hxR (x⁻¹ * s * x)).mpr (by rw [show x * (x⁻¹ * s * x) * x⁻¹ = s by group]; exact hs)
      have h1 := htc _ hs'
      calc x * t * x⁻¹ * s = x * (t * (x⁻¹ * s * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * s * x) * t) * x⁻¹ := by rw [h1]
        _ = s * (x * t * x⁻¹) := by group
    · rw [show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, ht]; group
    · exact fun h => ht1 (by
        calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group)
  have hb't : x * b * x⁻¹ ≠ t := fun h => hbt (by
    calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [h, hxt]
      _ = t := by group)
  obtain ⟨-, hW', -⟩ := sigW_spec ht ht1 htR htc hf hfc hfR hsR hsF hb'R hb'2 hb'1 hb't
  have key : ∀ a, (oddCoreOfCentralizer a).map (MulAut.conj x : Y →* Y) =
      oddCoreOfCentralizer (x * a * x⁻¹) := fun a =>
    map_oddCoreOfCentralizer_mulEquiv (MulAut.conj x) a
  rw [mem_normalizer_iff_map_conj_eq, hW, Subgroup.map_sup, Subgroup.map_sup, key, key, key, hxt,
    show x * (t * b) * x⁻¹ = x * t * x⁻¹ * (x * b * x⁻¹) by group, hxt, ← hW']
  exact hW

omit [Finite Y] ht1 htc hf hfR hsR hsF in
theorem t_mem_normalizer_sigW : t ∈ normalizer (sigW t f : Set Y) := by
  have htf : t * f = f * t := hfc t htR
  refine mem_normalizer_sup (mem_normalizer_sup ?_ ?_) ?_ <;>
    refine mem_normalizer_oddCoreOfCentralizer (mem_centralizer_singleton_iff.mpr ?_)
  · rw [← mul_assoc, ht, one_mul, htf, mul_assoc, ht, mul_one]
  · rfl
  · exact htf

theorem le_normalizer_sigW
    (hgen : ∀ r ∈ R, ∃ c₁ ∈ R, ∃ c₂ ∈ R, c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧ r = c₁ * c₂) :
    R ≤ normalizer (sigW t f : Set Y) := by
  have hinv : ∀ c ∈ R, c * c = 1 → c ∈ normalizer (sigW t f : Set Y) := by
    intro c hc hc2
    by_cases hc1 : c = 1
    · rw [hc1]; exact one_mem _
    by_cases hct : c = t
    · rw [hct]; exact t_mem_normalizer_sigW ht htR hfc
    exact (sigW_spec ht ht1 htR htc hf hfc hfR hsR hsF hc hc2 hc1 hct).2.2
  intro r hr
  obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, rfl⟩ := hgen r hr
  exact mul_mem (hinv c₁ hc₁ h1) (hinv c₂ hc₂ h2)

end Normalizer

end CFSG.ComponentClassification.Sol78.F514
