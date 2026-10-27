module

public import CFSG.GH74.Filter.Small.Eigenbasis
public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation
public import CFSG.Assembly.Defs

public section

namespace CFSG.GroupTheory.DiagonalTwentySeven

theorem conjAction_injective {M : Type*} [Group M] {Y L : Subgroup M}
    (hLY : L ≤ Subgroup.normalizer (Y : Set M))
    (hfaith : ∀ s ∈ L, (∀ y ∈ Y, s * y = y * s) → s = 1) :
    Function.Injective
      ((Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hLY)) := by
  intro s t hst
  let u : L := ⟨(s : M) * (t : M)⁻¹, L.mul_mem s.2 (L.inv_mem t.2)⟩
  have hu : (u : M) = (s : M) * (t : M)⁻¹ := rfl
  have h1 : ((Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hLY)) u = 1 := by
    rw [show u = s * t⁻¹ from Subtype.ext rfl, map_mul, hst, map_inv, mul_inv_cancel]
  have hcentral : ∀ y ∈ Y, (u : M) * y = y * (u : M) := by
    intro y hy
    have h2 := congrArg (fun f : MulAut Y => ((f ⟨y, hy⟩ : Y) : M)) h1
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion] at h2
    simp only [MulAut.one_apply, Subgroup.coe_mk] at h2
    calc
      (u : M) * y = (u : M) * y * (u : M)⁻¹ * (u : M) := by group
      _ = y * (u : M) := by rw [h2]
  have hu1 : u = 1 := Subtype.ext (hfaith (u : M) u.2 hcentral)
  have hst1 : (s : M) * (t : M)⁻¹ = 1 := by rw [← hu, hu1]; rfl
  exact Subtype.ext (mul_inv_eq_one.mp hst1)

@[expose] def eprod {M : Type*} [Group M] (e : Fin 3 → M) (c : Fin 3 → ZMod 3) : M :=
  e 0 ^ (c 0).val * e 1 ^ (c 1).val * e 2 ^ (c 2).val

theorem eprod_mem {M : Type*} [Group M] {Y : Subgroup M} {e : Fin 3 → M}
    (he : ∀ i, e i ∈ Y) (c : Fin 3 → ZMod 3) : eprod e c ∈ Y := by
  unfold eprod
  exact Y.mul_mem (Y.mul_mem (Y.pow_mem (he 0) _) (Y.pow_mem (he 1) _))
    (Y.pow_mem (he 2) _)

theorem eprod_zero {M : Type*} [Group M] (e : Fin 3 → M) :
    eprod e (0 : Fin 3 → ZMod 3) = 1 := by
  simp [eprod]

private theorem card_sign_zmod3 : Nat.card {x : ZMod 3 // x = 1 ∨ x = -1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem two_ne_zero_zmod3 : (2 : ZMod 3) ≠ 0 := by decide

private theorem val_neg_one_zmod3 : ((-1 : ZMod 3)).val = 2 := by decide

private theorem val_one_zmod3 : (1 : ZMod 3).val = 1 := by decide

private theorem val_one_zmod2 : (1 : ZMod 2).val = 1 := by decide

private theorem neg_one_ne_one_zmod3 : (-1 : ZMod 3) ≠ 1 := by decide

private theorem sign_inj_zmod3 : ∀ (a b : ZMod 3), (a = 1 ∨ a = -1) →
    (b = 1 ∨ b = -1) →
    (if a = 1 then (0 : ZMod 2) else 1) = (if b = 1 then 0 else 1) → a = b := by
  decide

theorem pow_add_zmod3 {M : Type*} [Group M] (x : M) (hx : x ^ 3 = 1)
    (a b : ZMod 3) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  have hmod : a.val + b.val ≡ (a + b).val [MOD 3] := by
    rw [ZMod.val_add]
    exact (Nat.mod_modEq (a.val + b.val) 3).symm
  have hmod' : a.val + b.val ≡ (a + b).val [MOD orderOf x] :=
    Nat.ModEq.of_dvd hord hmod
  rw [← pow_add, pow_eq_pow_iff_modEq.mpr hmod']

theorem eprod_add {M : Type*} [Group M] (e : Fin 3 → M)
    (hcomm : ∀ i j, e i * e j = e j * e i) (hcube : ∀ i, e i ^ 3 = 1)
    (c c' : Fin 3 → ZMod 3) :
    eprod e (c + c') = eprod e c * eprod e c' := by
  unfold eprod
  simp only [Pi.add_apply]
  rw [pow_add_zmod3 (e 0) (hcube 0), pow_add_zmod3 (e 1) (hcube 1),
    pow_add_zmod3 (e 2) (hcube 2)]
  have hpc : ∀ i j, e i ^ (c i).val * e j ^ (c' j).val =
      e j ^ (c' j).val * e i ^ (c i).val := by
    intro i j
    exact ((show Commute (e i) (e j) from hcomm i j).pow_left (c i).val).pow_right
      (c' j).val
  grind

theorem eprod_mulEquiv {M : Type*} [Group M] {Y : Subgroup M} (e : Fin 3 → M)
    (he : ∀ i, e i ∈ Y) (hcomm : ∀ i j, e i * e j = e j * e i)
    (hcube : ∀ i, e i ^ 3 = 1)
    (hbij : Function.Bijective (fun c : Fin 3 → ZMod 3 =>
      (⟨eprod e c, eprod_mem he c⟩ : Y))) :
    ∃ F : Multiplicative (Fin 3 → ZMod 3) ≃* Y,
      (∀ c, F (Multiplicative.ofAdd c) = ⟨eprod e c, eprod_mem he c⟩) ∧
      (∀ i, F (Multiplicative.ofAdd (Pi.single i 1)) = ⟨e i, he i⟩) := by
  classical
  let f : Multiplicative (Fin 3 → ZMod 3) →* Y :=
    { toFun := fun c => ⟨eprod e (Multiplicative.toAdd c), eprod_mem he _⟩
      map_one' := by
        apply Subtype.ext
        show eprod e (Multiplicative.toAdd 1) = 1
        rw [show Multiplicative.toAdd (1 : Multiplicative (Fin 3 → ZMod 3)) = 0 from rfl,
          eprod_zero]
      map_mul' := by
        intro c c'
        apply Subtype.ext
        show eprod e (Multiplicative.toAdd (c * c')) =
          eprod e (Multiplicative.toAdd c) * eprod e (Multiplicative.toAdd c')
        rw [show Multiplicative.toAdd (c * c') =
          Multiplicative.toAdd c + Multiplicative.toAdd c' from rfl]
        exact eprod_add e hcomm hcube _ _ }
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact Multiplicative.toAdd.injective (hbij.1 (by simpa [f] using hab))
    · intro y
      obtain ⟨c, hc⟩ := hbij.2 y
      exact ⟨Multiplicative.ofAdd c, by simpa [f] using hc⟩
  refine ⟨MulEquiv.ofBijective f hf, ?_, ?_⟩
  · intro c
    rfl
  · intro i
    apply Subtype.ext
    change eprod e (Pi.single i 1) = e i
    have hsingle : ∀ i : Fin 3, eprod e (Pi.single i 1) = e i := by
      intro i
      fin_cases i <;> simp [eprod, Pi.single, val_one_zmod3]
    exact hsingle i

theorem isElementaryAbelian_of_faithful {M : Type*} [Group M] [Finite M] {Y L : Subgroup M}
    (hY : Nat.card Y = 27) (hLY : L ≤ Subgroup.normalizer (Y : Set M))
    (hLc : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s) (hL2 : ∀ s ∈ L, s * s = 1)
    (hL8 : Nat.card L = 8)
    (hfaith : ∀ s ∈ L, (∀ y ∈ Y, s * y = y * s) → s = 1) :
    CFSG.IsElementaryAbelian 3 Y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hY3 : IsPGroup 3 Y := IsPGroup.of_card (n := 3) (by rw [hY]; norm_num)
  haveI : Fact (IsPGroup 3 Y) := ⟨hY3⟩
  let ρ : L →* MulAut Y := (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hLY)
  have hρ_coe : ∀ (s : L) (y : Y), ((ρ s) y : M) = (s : M) * (y : M) * (s : M)⁻¹ := by
    intro s y
    dsimp only [ρ]
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hρ_inj : Function.Injective ρ := by
    dsimp only [ρ]
    exact conjAction_injective hLY hfaith
  let Q := Y ⧸ frattini Y
  letI : CommGroup Q :=
    CFSG.OrderReductions.ElementaryRepresentation.frattiniQuotientCommGroup 3 hY3
  letI : Module (ZMod 3) (Additive Q) :=
    CFSG.OrderReductions.ElementaryRepresentation.exponentModule 3
      (CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent 3 hY3)
  let ρbar : L →* MulAut Q := (CFSG.Walter.Huppert.frattiniAut Y).comp ρ
  have hρbar_inj : Function.Injective ρbar := by
    intro s t hst
    let u : L := ⟨(s : M) * (t : M)⁻¹, L.mul_mem s.2 (L.inv_mem t.2)⟩
    have hu : (u : M) = (s : M) * (t : M)⁻¹ := rfl
    have hu2 : u * u = 1 := Subtype.ext (hL2 (u : M) u.2)
    have h1 : ρbar u = 1 := by
      rw [show u = s * t⁻¹ from Subtype.ext rfl, map_mul, hst, map_inv, mul_inv_cancel]
    have hτ : ρ u = 1 := by
      refine CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hY3 ?_ ?_
      · have hτ2 : (ρ u) ^ 2 = 1 := by
          simpa [pow_two, map_mul] using congrArg ρ hu2
        have hdvd : orderOf (ρ u) ∣ 2 := orderOf_dvd_of_pow_eq_one hτ2
        exact Nat.Coprime.coprime_dvd_right hdvd (by norm_num : Nat.Coprime 3 2)
      · dsimp only [ρbar] at h1
        simpa using h1
    have hu1 : u = 1 := hρ_inj (by rw [hτ, map_one])
    have hst1 : (s : M) * (t : M)⁻¹ = 1 := by rw [← hu, hu1]; rfl
    exact Subtype.ext (mul_inv_eq_one.mp hst1)
  let V := Additive Q
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V), Nat.card_zmod]
  have hVle : Nat.card V ≤ Nat.card Y := by
    refine Nat.card_le_card_of_surjective
      (fun y : Y => Additive.ofMul (QuotientGroup.mk' (frattini Y) y)) ?_
    intro v
    obtain ⟨q, hq⟩ := Additive.ofMul.surjective v
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (frattini Y) q
    exact ⟨y, by rw [← hq, ← hy]⟩
  have hd3 : Module.finrank (ZMod 3) V ≤ 3 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V ≤ 3 ^ 3 := by
      calc
        3 ^ Module.finrank (ZMod 3) V = Nat.card V := hVcard.symm
        _ ≤ Nat.card Y := hVle
        _ = 27 := hY
        _ = 3 ^ 3 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  let f : L → Module.End (ZMod 3) V := fun s =>
    CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρbar s
  have hfcomm : ∀ s t, Commute (f s) (f t) := by
    intro s t
    change f s * f t = f t * f s
    dsimp only [f]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hLc s s.2 t t.2)
  have hfsq : ∀ s, f s ^ 2 = 1 := by
    intro s
    change f s * f s = 1
    dsimp only [f]
    rw [← map_mul, show s * s = 1 from Subtype.ext (by simpa using hL2 s s.2), map_one]
  obtain ⟨b, μ, hb⟩ :=
    CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one
      (K := ZMod 3) (V := V) two_ne_zero_zmod3 f hfcomm hfsq
  have hμsign : ∀ (s : L) (i : Fin (Module.finrank (ZMod 3) V)),
      μ s i = 1 ∨ μ s i = -1 := by
    intro s i
    have hsq : μ s i * μ s i = 1 := by
      have h1 : f s (f s (b i)) = b i := by
        have := congrArg (fun g : Module.End (ZMod 3) V => g (b i)) (hfsq s)
        simpa [pow_two, Module.End.mul_apply] using this
      rw [hb s, map_smul, hb s, smul_smul] at h1
      have h3 : (μ s i * μ s i - 1) • b i = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (b.ne_zero i))
    have h4 : (μ s i - 1) * (μ s i + 1) = 0 := by
      calc
        (μ s i - 1) * (μ s i + 1) = μ s i * μ s i - 1 := by ring
        _ = 0 := by rw [hsq]; ring
    rcases mul_eq_zero.mp h4 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hμ_inj : Function.Injective (fun s : L => μ s) := by
    intro s t hst
    have hlin : f s = f t := by
      refine b.ext fun i => ?_
      calc
        f s (b i) = μ s i • b i := hb s i
        _ = μ t i • b i := by simpa using congrArg (fun x : ZMod 3 => x • b i) (congrFun hst i)
        _ = f t (b i) := (hb t i).symm
    have hρbar : ρbar s = ρbar t := by
      refine MulEquiv.ext fun q => ?_
      have hq := congrArg (fun g : Module.End (ZMod 3) V => g (Additive.ofMul q)) hlin
      have hs : (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρbar)
          s (Additive.ofMul q) = Additive.ofMul (ρbar s q) := by
        rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply,
          toMul_ofMul]
      have ht : (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρbar)
          t (Additive.ofMul q) = Additive.ofMul (ρbar t q) := by
        rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply,
          toMul_ofMul]
      dsimp only [f] at hq
      rw [hs, ht] at hq
      exact Additive.ofMul.injective hq
    exact hρbar_inj hρbar
  have hsign_card : Nat.card {x : Fin (Module.finrank (ZMod 3) V) → ZMod 3 //
      ∀ i, x i = 1 ∨ x i = -1} = 2 ^ Module.finrank (ZMod 3) V := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ x => x = 1 ∨ x = -1)),
      Nat.card_pi]
    simp only [card_sign_zmod3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsign_le : Nat.card L ≤ 2 ^ Module.finrank (ZMod 3) V := by
    have h := Nat.card_le_card_of_injective
      (fun s : L => (⟨μ s, hμsign s⟩ : {x : Fin (Module.finrank (ZMod 3) V) → ZMod 3 //
        ∀ i, x i = 1 ∨ x i = -1})) (fun s t hst =>
          hμ_inj (Subtype.ext_iff.mp hst))
    rwa [hsign_card] at h
  have h8le : 8 ≤ 2 ^ Module.finrank (ZMod 3) V := by
    calc
      8 = Nat.card L := hL8.symm
      _ ≤ 2 ^ Module.finrank (ZMod 3) V := hsign_le
  have hdge : 3 ≤ Module.finrank (ZMod 3) V := by
    have h8 : 2 ^ 3 ≤ 2 ^ Module.finrank (ZMod 3) V := by simpa using h8le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8
  have hdeq : Module.finrank (ZMod 3) V = 3 := le_antisymm hd3 hdge
  have hquotcard : Nat.card Q = 27 := by
    have h := hVcard
    rw [hdeq, show 3 ^ 3 = 27 by norm_num] at h
    exact h
  have hcard_eq : Nat.card Q = Nat.card Y := by rw [hquotcard, hY]
  obtain ⟨e⟩ := Finite.card_eq.mp hcard_eq
  have hmk_inj : Function.Injective (QuotientGroup.mk' (frattini Y) : Y → Q) :=
    Function.Surjective.injective_of_finite e.symm
      (QuotientGroup.mk'_surjective (frattini Y))
  have hker : (QuotientGroup.mk' (frattini Y)).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr hmk_inj
  have hPhi : frattini Y = ⊥ := by
    rwa [QuotientGroup.ker_mk' (frattini Y)] at hker
  exact CFSG.frattini_eq_bot_iff_isElementaryAbelian.mp hPhi

theorem exists_diagonal {M : Type*} [Group M] [Finite M] {Y L : Subgroup M}
    (hY : Nat.card Y = 27) (hLY : L ≤ Subgroup.normalizer (Y : Set M))
    (hLc : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s) (hL2 : ∀ s ∈ L, s * s = 1)
    (hL8 : Nat.card L = 8)
    (hfaith : ∀ s ∈ L, (∀ y ∈ Y, s * y = y * s) → s = 1) :
    (∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
    ∃ (e l : Fin 3 → M) (he : ∀ i, e i ∈ Y),
      (∀ i, l i ∈ L) ∧
      (∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹) ∧
      (∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) ∧
      Function.Bijective (fun c : Fin 3 → ZMod 3 =>
        (⟨eprod e c, eprod_mem he c⟩ : Y)) ∧
      (∀ s ∈ L, ∃ c : Fin 3 → ZMod 2,
        s = l 0 ^ (c 0).val * l 1 ^ (c 1).val * l 2 ^ (c 2).val) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hYel : CFSG.IsElementaryAbelian 3 Y :=
    isElementaryAbelian_of_faithful hY hLY hLc hL2 hL8 hfaith
  haveI : CFSG.IsElementaryAbelian 3 Y := hYel
  haveI : IsMulCommutative Y := hYel.toIsMulCommutative
  letI : CommGroup Y := IsMulCommutative.instCommGroup
  have hYcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
    intro y hy y' hy'
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Y) (⟨y', hy'⟩ : Y))
  have hYcube : ∀ y ∈ Y, y ^ 3 = 1 := fun y hy =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) y hy
  have hfindimY : Module.finrank (ZMod 3) (Additive Y) = 3 := by
    have h := FiniteField.pow_finrank_eq_natCard 3 (Additive Y)
    rw [Nat.card_congr Additive.toMul, hY] at h
    have h' : 3 ^ Module.finrank (ZMod 3) (Additive Y) = 3 ^ 3 := by
      rw [h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h' 
  let ρ : L →* MulAut Y := (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hLY)
  have hρ_coe : ∀ (s : L) (y : Y), ((ρ s) y : M) = (s : M) * (y : M) * (s : M)⁻¹ := by
    intro s y
    dsimp only [ρ]
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hρ_inj : Function.Injective ρ := by
    dsimp only [ρ]
    exact conjAction_injective hLY hfaith
  let f : L → Module.End (ZMod 3) (Additive Y) := fun s =>
    CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρ s
  have hfcomm : ∀ s t, Commute (f s) (f t) := by
    intro s t
    change f s * f t = f t * f s
    dsimp only [f]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hLc s s.2 t t.2)
  have hfsq : ∀ s, f s ^ 2 = 1 := by
    intro s
    change f s * f s = 1
    dsimp only [f]
    rw [← map_mul, show s * s = 1 from Subtype.ext (by simpa using hL2 s s.2), map_one]
  obtain ⟨b, μ, hb⟩ :=
    CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one
      (K := ZMod 3) (V := Additive Y) two_ne_zero_zmod3 f hfcomm hfsq
  let b₀ : Module.Basis (Fin 3) (ZMod 3) (Additive Y) := b.reindex (finCongr hfindimY)
  let μ₀ : L → Fin 3 → ZMod 3 := fun s i => μ s ((finCongr hfindimY).symm i)
  have hb₀ : ∀ s i, f s (b₀ i) = μ₀ s i • b₀ i := by
    intro s i
    dsimp only [b₀, μ₀]
    rw [Module.Basis.reindex_apply]
    exact hb s _
  have hμsign : ∀ (s : L) (i : Fin 3), μ₀ s i = 1 ∨ μ₀ s i = -1 := by
    intro s i
    have hsq : μ₀ s i * μ₀ s i = 1 := by
      have h1 : f s (f s (b₀ i)) = b₀ i := by
        have := congrArg (fun g : Module.End (ZMod 3) (Additive Y) => g (b₀ i)) (hfsq s)
        simpa [pow_two, Module.End.mul_apply] using this
      rw [hb₀ s, map_smul, hb₀ s, smul_smul] at h1
      have h3 : (μ₀ s i * μ₀ s i - 1) • b₀ i = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (b₀.ne_zero i))
    have h4 : (μ₀ s i - 1) * (μ₀ s i + 1) = 0 := by
      calc
        (μ₀ s i - 1) * (μ₀ s i + 1) = μ₀ s i * μ₀ s i - 1 := by ring
        _ = 0 := by rw [hsq]; ring
    rcases mul_eq_zero.mp h4 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hμ_inj : Function.Injective (fun s : L => μ₀ s) := by
    intro s t hst
    have hlin : f s = f t := by
      refine b₀.ext fun i => ?_
      calc
        f s (b₀ i) = μ₀ s i • b₀ i := hb₀ s i
        _ = μ₀ t i • b₀ i := by simpa using congrArg (fun x : ZMod 3 => x • b₀ i) (congrFun hst i)
        _ = f t (b₀ i) := (hb₀ t i).symm
    have hρ : ρ s = ρ t := by
      refine MulEquiv.ext fun y => ?_
      have hq := congrArg (fun g : Module.End (ZMod 3) (Additive Y) =>
        g (Additive.ofMul y)) hlin
      have hs : (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρ)
          s (Additive.ofMul y) = Additive.ofMul (ρ s y) := by
        rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply,
          toMul_ofMul]
      have ht : (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation 3 ρ)
          t (Additive.ofMul y) = Additive.ofMul (ρ t y) := by
        rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply,
          toMul_ofMul]
      dsimp only [f] at hq
      rw [hs, ht] at hq
      exact Additive.ofMul.injective hq
    exact hρ_inj hρ
  let e : Fin 3 → Y := fun i => Additive.toMul (b₀ i)
  have he : ∀ i, (e i : M) ∈ Y := fun i => (e i).2
  have htoMul_smul : ∀ (a : ZMod 3) (v : Additive Y),
      Additive.toMul (a • v) = Additive.toMul v ^ a.val := by
    intro a v
    have hsmul : a • v = a.val • v := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      rw [Nat.cast_smul_eq_nsmul]
    rw [hsmul, toMul_nsmul]
  let Φ : (Fin 3 → ZMod 3) → Y := fun c =>
    ⟨eprod (fun i => (e i : M)) c, eprod_mem he c⟩
  have hΦ_sum : ∀ c : Fin 3 → ZMod 3,
      Φ c = Additive.toMul (∑ i : Fin 3, c i • b₀ i) := by
    intro c
    apply Subtype.ext
    change eprod (fun i => ((e i : Y) : M)) c =
      Additive.toMul (∑ i : Fin 3, c i • b₀ i)
    rw [show (∑ i : Fin 3, c i • b₀ i) = c 0 • b₀ 0 + c 1 • b₀ 1 + c 2 • b₀ 2 by
      simp [Fin.sum_univ_three]]
    simp only [toMul_add, htoMul_smul, eprod]
    rfl
  have hcoord_eprod : ∀ c : Fin 3 → ZMod 3,
      (fun y : Y => fun i => b₀.repr (Additive.ofMul y) i) (Φ c) = c := by
    intro c
    funext i
    dsimp only
    rw [hΦ_sum c, ofMul_toMul]
    exact congrFun (Module.Basis.repr_sum_self b₀ c) i
  have heprod_coord : ∀ y : Y,
      Φ (fun i => b₀.repr (Additive.ofMul y) i) = y := by
    intro y
    apply Additive.ofMul.injective
    rw [hΦ_sum, ofMul_toMul]
    exact Module.Basis.sum_repr b₀ (Additive.ofMul y)
  have hbij : Function.Bijective Φ := by
    refine ⟨?_, ?_⟩
    · intro c c' hcc
      have h := congrArg (fun y : Y => fun i => b₀.repr (Additive.ofMul y) i) hcc
      have hc : (fun i => b₀.repr (Additive.ofMul (Φ c)) i) = c := hcoord_eprod c
      have hc' : (fun i => b₀.repr (Additive.ofMul (Φ c')) i) = c' := hcoord_eprod c'
      exact hc.symm.trans (h.trans hc')
    · intro y
      exact ⟨fun i => b₀.repr (Additive.ofMul y) i, heprod_coord y⟩
  have hact : ∀ (s : L) (i : Fin 3),
      (s : M) * ((e i : Y) : M) * (s : M)⁻¹ = ((e i : Y) : M) ^ (μ₀ s i).val := by
    intro s i
    have h := congrArg (fun y : Y => (y : M)) (congrArg Additive.toMul (hb₀ s i))
    have hleft : ((Additive.toMul (f s (b₀ i)) : Y) : M) =
        (s : M) * ((e i : Y) : M) * (s : M)⁻¹ := by
      dsimp only [f, e]
      rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply,
        toMul_ofMul]
      dsimp only [ρ]
      rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion]
    have hright : ((Additive.toMul (μ₀ s i • b₀ i) : Y) : M) =
        ((e i : Y) : M) ^ (μ₀ s i).val := by
      rw [htoMul_smul]
      rfl
    rw [hleft, hright] at h
    exact h
  let sd : L → Fin 3 → ZMod 2 := fun s i => if μ₀ s i = 1 then 0 else 1
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hsd_inj : Function.Injective sd := by
    intro s t hst
    apply hμ_inj
    funext i
    exact sign_inj_zmod3 _ _ (hμsign s i) (hμsign t i) (congrFun hst i)
  have hsd_bij : Function.Bijective sd := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hsd_inj, ?_⟩
    rw [hL8, Nat.card_pi]
    simp only [Nat.card_zmod, Nat.card_fin, Finset.prod_const, Finset.card_univ]
    norm_num
  let l : Fin 3 → L := fun i => Classical.choose (hsd_bij.2 (Pi.single i 1))
  have hl : ∀ i, sd (l i) = Pi.single i 1 := fun i =>
    Classical.choose_spec (hsd_bij.2 (Pi.single i 1))
  have hlμ : ∀ i j, μ₀ (l i) j = if j = i then -1 else 1 := by
    intro i j
    by_cases hji : j = i
    · rw [hji]
      have hsd1 : sd (l i) i = 1 := by
        rw [hl i]
        simp
      have hne : μ₀ (l i) i ≠ 1 := by
        intro h1
        have : (0 : ZMod 2) = 1 := by simpa [sd, h1] using hsd1
        exact zero_ne_one this
      rcases hμsign (l i) i with h1 | h1
      · exact absurd h1 hne
      · simpa using h1
    · have hsd0 : sd (l i) j = 0 := by
        rw [hl i]
        simp [hji]
      have hμ1 : μ₀ (l i) j = 1 := by
        by_contra hne
        rcases hμsign (l i) j with h1 | h1
        · exact hne h1
        · have : (1 : ZMod 2) = 0 := by simpa [sd, hne] using hsd0
          exact one_ne_zero this
      simp [hji, hμ1]
  have hsquare : ∀ i, ((e i : Y) : M) ^ 2 = (((e i : Y) : M))⁻¹ := by
    intro i
    have hcube := hYcube (e i : M) (e i).2
    have h2 : ((e i : Y) : M) ^ 2 * ((e i : Y) : M) = 1 := by
      rw [← pow_succ, show 2 + 1 = 3 by norm_num, hcube]
    exact eq_inv_of_mul_eq_one_left h2
  have hact_diag : ∀ i, (l i : M) * (e i : M) * ((l i : M))⁻¹ = ((e i : M))⁻¹ := by
    intro i
    have h := hact (l i) i
    have hμ : μ₀ (l i) i = -1 := by simpa using hlμ i i
    rw [hμ, val_neg_one_zmod3, hsquare i] at h
    exact h
  have hoff : ∀ i j, i ≠ j → (l i : M) * (e j : M) * ((l i : M))⁻¹ = e j := by
    intro i j hij
    have h := hact (l i) j
    have hμ : μ₀ (l i) j = 1 := by
      have := hlμ i j
      rw [if_neg (Ne.symm hij)] at this
      exact this
    rw [hμ, val_one_zmod3] at h
    simpa using h
  have hmu_mul : ∀ (s t : L) (i : Fin 3), μ₀ (s * t) i = μ₀ s i * μ₀ t i := by
    intro s t i
    have h1 : f (s * t) (b₀ i) = f s (f t (b₀ i)) := by
      change (f (s * t)) (b₀ i) = (f s * f t) (b₀ i)
      dsimp only [f]
      rw [map_mul, Module.End.mul_apply]
    rw [hb₀ (s * t) i] at h1
    rw [hb₀ t i, map_smul, hb₀ s i, smul_smul] at h1
    have h3 : (μ₀ (s * t) i - μ₀ t i * μ₀ s i) • b₀ i = 0 := by
      rw [sub_smul, h1, sub_self]
    have h4 : μ₀ (s * t) i = μ₀ t i * μ₀ s i :=
      sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (b₀.ne_zero i))
    rw [mul_comm] at h4
    exact h4
  have hmu_one : ∀ i, μ₀ 1 i = 1 := by
    intro i
    have h1 : f 1 (b₀ i) = b₀ i := by
      dsimp only [f]
      rw [map_one]
      rfl
    rw [hb₀ 1 i] at h1
    have h3 : (μ₀ 1 i - 1) • b₀ i = 0 := by
      rw [sub_smul, h1, one_smul]
      exact sub_self _
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (b₀.ne_zero i))
  have hmu_pow : ∀ (s : L) (n : ℕ) (i : Fin 3), μ₀ (s ^ n) i = (μ₀ s i) ^ n := by
    intro s n
    induction n with
    | zero =>
        intro i
        rw [pow_zero, hmu_one i, pow_zero]
    | succ n ih =>
        intro i
        rw [pow_succ, hmu_mul (s ^ n) s i, ih i, pow_succ]
  let w : (Fin 3 → ZMod 2) → L := fun c =>
    (l 0) ^ (c 0).val * (l 1) ^ (c 1).val * (l 2) ^ (c 2).val
  have hmu_w : ∀ (c : Fin 3 → ZMod 2) (i : Fin 3),
      μ₀ (w c) i = if c i = 0 then 1 else -1 := by
    intro c i
    dsimp only [w]
    rw [hmu_mul, hmu_mul, hmu_pow, hmu_pow, hmu_pow]
    fin_cases i
    · change μ₀ (l 0) (0 : Fin 3) ^ (c 0).val * μ₀ (l 1) (0 : Fin 3) ^ (c 1).val *
          μ₀ (l 2) (0 : Fin 3) ^ (c 2).val =
        if c (0 : Fin 3) = 0 then 1 else -1
      rw [show μ₀ (l 0) (0 : Fin 3) = -1 from by simpa using hlμ 0 0,
        show μ₀ (l 1) (0 : Fin 3) = 1 from by simpa using hlμ 1 0,
        show μ₀ (l 2) (0 : Fin 3) = 1 from by simpa using hlμ 2 0]
      rcases hz2 (c 0) with h0 | h1
      · simp [h0]
      · simp [h1, val_one_zmod2]
    · change μ₀ (l 0) (1 : Fin 3) ^ (c 0).val * μ₀ (l 1) (1 : Fin 3) ^ (c 1).val *
          μ₀ (l 2) (1 : Fin 3) ^ (c 2).val =
        if c (1 : Fin 3) = 0 then 1 else -1
      rw [show μ₀ (l 0) (1 : Fin 3) = 1 from by simpa using hlμ 0 1,
        show μ₀ (l 1) (1 : Fin 3) = -1 from by simpa using hlμ 1 1,
        show μ₀ (l 2) (1 : Fin 3) = 1 from by simpa using hlμ 2 1]
      rcases hz2 (c 1) with h0 | h1
      · simp [h0]
      · simp [h1, val_one_zmod2]
    · change μ₀ (l 0) (2 : Fin 3) ^ (c 0).val * μ₀ (l 1) (2 : Fin 3) ^ (c 1).val *
          μ₀ (l 2) (2 : Fin 3) ^ (c 2).val =
        if c (2 : Fin 3) = 0 then 1 else -1
      rw [show μ₀ (l 0) (2 : Fin 3) = 1 from by simpa using hlμ 0 2,
        show μ₀ (l 1) (2 : Fin 3) = 1 from by simpa using hlμ 1 2,
        show μ₀ (l 2) (2 : Fin 3) = -1 from by simpa using hlμ 2 2]
      rcases hz2 (c 2) with h0 | h1
      · simp [h0]
      · simp [h1, val_one_zmod2]
  have hsd_w : ∀ c : Fin 3 → ZMod 2, sd (w c) = c := by
    intro c
    funext i
    have h := hmu_w c i
    rcases hz2 (c i) with h0 | h1
    · have hμ : μ₀ (w c) i = 1 := by rw [h, h0]; simp
      simp [sd, h0, hμ]
    · have hμ : μ₀ (w c) i = -1 := by rw [h, h1]; simp
      have hneg : ¬ μ₀ (w c) i = 1 := by
        rw [hμ]
        exact neg_one_ne_one_zmod3
      simp [sd, h1, hneg]
  let eM : Fin 3 → M := fun i => (e i : M)
  let lM : Fin 3 → M := fun i => (l i : M)
  have heM : ∀ i, eM i ∈ Y := fun i => (e i).2
  have hlM : ∀ i, lM i ∈ L := fun i => (l i).2
  have hact_diagM : ∀ i, lM i * eM i * (lM i)⁻¹ = (eM i)⁻¹ := hact_diag
  have hoffM : ∀ i j, i ≠ j → lM i * eM j * (lM i)⁻¹ = eM j := hoff
  have hbijM : Function.Bijective (fun c : Fin 3 → ZMod 3 =>
      (⟨eprod eM c, eprod_mem heM c⟩ : Y)) := hbij
  have hgen : ∀ s ∈ L, ∃ c : Fin 3 → ZMod 2,
      s = lM 0 ^ (c 0).val * lM 1 ^ (c 1).val * lM 2 ^ (c 2).val := by
    intro s hs
    let c : Fin 3 → ZMod 2 := sd ⟨s, hs⟩
    refine ⟨c, ?_⟩
    have hw : w c = ⟨s, hs⟩ := by
      apply hsd_inj
      rw [hsd_w c]
    have hcoe : (w c : M) = s := by
      simpa using congrArg (fun t : L => (t : M)) hw
    rw [← hcoe]
    simp [w, lM]
  exact ⟨hYcomm, hYcube, eM, lM, heM, hlM, hact_diagM, hoffM, hbijM, hgen⟩

theorem exists_diagonal_mulEquiv {M : Type*} [Group M] [Finite M] {Y L : Subgroup M}
    (hY : Nat.card Y = 27) (hLY : L ≤ Subgroup.normalizer (Y : Set M))
    (hLc : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s) (hL2 : ∀ s ∈ L, s * s = 1)
    (hL8 : Nat.card L = 8)
    (hfaith : ∀ s ∈ L, (∀ y ∈ Y, s * y = y * s) → s = 1) :
    (∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
    ∃ (e l : Fin 3 → M) (he : ∀ i, e i ∈ Y)
        (F : Multiplicative (Fin 3 → ZMod 3) ≃* Y),
      (∀ i, l i ∈ L) ∧
      (∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹) ∧
      (∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) ∧
      (∀ c, F (Multiplicative.ofAdd c) = ⟨eprod e c, eprod_mem he c⟩) ∧
      (∀ i, F (Multiplicative.ofAdd (Pi.single i 1)) = ⟨e i, he i⟩) ∧
      (∀ s ∈ L, ∃ c : Fin 3 → ZMod 2,
        s = l 0 ^ (c 0).val * l 1 ^ (c 1).val * l 2 ^ (c 2).val) := by
  obtain ⟨hcomm, hcube, e, l, he, hl, hdiag, hoff, hbij, hgen⟩ :=
    exists_diagonal hY hLY hLc hL2 hL8 hfaith
  obtain ⟨F, hF, hsingle⟩ := eprod_mulEquiv e he
    (fun i j => hcomm (e i) (he i) (e j) (he j))
    (fun i => hcube (e i) (he i)) hbij
  exact ⟨hcomm, hcube, e, l, he, F, hl, hdiag, hoff, hF, hsingle, hgen⟩

end CFSG.GroupTheory.DiagonalTwentySeven
