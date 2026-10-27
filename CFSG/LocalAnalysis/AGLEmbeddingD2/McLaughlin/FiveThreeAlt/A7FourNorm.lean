module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Gen

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module

variable {Γ : Type*} [Group Γ] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

def vecStab (ρ : Representation (ZMod 2) Γ Q) (v : Q) : Subgroup Γ where
  carrier := {h | ρ h v = v}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    have hx' : ρ x v = v := hx
    have hy' : ρ y v = v := hy
    show ρ (x * y) v = v
    rw [map_mul, Module.End.mul_apply, hy', hx']
  inv_mem' := fun {x} hx => by
    have hx' : ρ x v = v := hx
    show ρ x⁻¹ v = v
    have := congrArg (fun w => ρ x⁻¹ w) hx'
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem card_ker_of_order_seven [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {g : Γ}
    (hg : orderOf g = 7) (hρ : ρ g ≠ 1) (hdim : finrank (ZMod 2) Q = 4) :
    Nat.card (LinearMap.ker (ρ g - 1)) = 2 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let K := Subgroup.zpowers g
  let _ : MulAction K Q := MulAction.compHom Q (ρ.comp K.subtype)
  have hK : IsPGroup 7 K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hK.card_modEq_card_fixedPoints Q
  have hfix : ∀ v : Q, v ∈ MulAction.fixedPoints K Q ↔ v ∈ LinearMap.ker (ρ g - 1) := by
    intro v
    rw [MulAction.mem_fixedPoints, LinearMap.mem_ker]
    constructor
    · intro h
      have h1 : ρ g v = v := h ⟨g, Subgroup.mem_zpowers g⟩
      rw [LinearMap.sub_apply, h1, Module.End.one_apply, sub_self]
    · intro h
      have h1 : ρ g v = v := by
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
        exact h
      have h2 : K ≤ vecStab ρ v := (Subgroup.zpowers_le (H := vecStab ρ v)).2 h1
      intro u
      exact h2 u.2
  have hcardfix : Nat.card (MulAction.fixedPoints K Q) = Nat.card (LinearMap.ker (ρ g - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  rw [hcardfix] at hmod
  have hQ : Nat.card Q = 2 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  have hker : Nat.card (LinearMap.ker (ρ g - 1)) = 2 ^ finrank (ZMod 2) (LinearMap.ker (ρ g - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : finrank (ZMod 2) (LinearMap.ker (ρ g - 1)) ≤ 4 := hdim ▸ Submodule.finrank_le _
  have hne4 : finrank (ZMod 2) (LinearMap.ker (ρ g - 1)) ≠ 4 := by
    intro h4
    apply hρ
    have : LinearMap.ker (ρ g - 1) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4, hdim])
    have h5 : ρ g - 1 = 0 := by
      ext v
      have hv : v ∈ LinearMap.ker (ρ g - 1) := this ▸ Submodule.mem_top
      exact hv
    rwa [sub_eq_zero] at h5
  rw [hker, hQ] at hmod
  rw [hker]
  generalize finrank (ZMod 2) (LinearMap.ker (ρ g - 1)) = k at hle hne4 hmod ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem exists_nonzero_of_card_two {M : Type*} [Zero M] (h : Nat.card M = 2) :
    ∃ v : M, v ≠ 0 ∧ ∀ w : M, w = 0 ∨ w = v := by
  obtain ⟨a, b, hab, hset⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ w : M, w = a ∨ w = b := fun w => by
    have : w ∈ ({a, b} : Set M) := hset ▸ Set.mem_univ w
    simpa using this
  rcases hmem 0 with h0 | h0
  · refine ⟨b, fun hb => hab (h0.symm.trans hb.symm), fun w => ?_⟩
    rcases hmem w with hw | hw
    · exact Or.inl (hw.trans h0.symm)
    · exact Or.inr hw
  · refine ⟨a, fun ha => hab (ha.trans h0), fun w => ?_⟩
    rcases hmem w with hw | hw
    · exact Or.inr hw
    · exact Or.inl (hw.trans h0.symm)

theorem faithful_of_irr [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {L : Subgroup Γ}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) Q = 4)
    (hirr : ∀ N : Submodule (ZMod 2) Q, (∀ l ∈ L, ∀ q ∈ N, ρ l q ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∀ l : ↥L, ρ l = 1 → l = 1 := by
  classical
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  have hsimpleA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hsimple : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hnt : ∃ l ∈ L, ρ l ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨q, hq⟩ : ∃ q : Q, q ≠ 0 := by
      have : 0 < finrank (ZMod 2) Q := by omega
      have := Module.finrank_pos_iff.1 this
      exact exists_ne (0 : Q)
    rcases hirr (Submodule.span (ZMod 2) {q}) (fun l hl y hy => by simpa [h l hl] using hy) with
      h0 | h1
    · apply hq
      have : q ∈ Submodule.span (ZMod 2) {q} := Submodule.subset_span rfl
      rw [h0] at this
      exact this
    · have h2 := finrank_span_singleton (K := ZMod 2) hq
      rw [h1, finrank_top, hdim] at h2
      omega
  intro l hl
  let φ : ↥L →* (Module.End (ZMod 2) Q)ˣ := ρ.asGroupHom.comp L.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hl' : l ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      simp [φ, Representation.asGroupHom_apply, hl]
    rw [h] at hl'
    exact Subgroup.mem_bot.1 hl'
  · exfalso
    obtain ⟨l0, hl0, hne⟩ := hnt
    have h3 : (⟨l0, hl0⟩ : ↥L) ∈ φ.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h3
    have h4 := congrArg Units.val h3
    simp [φ, Representation.asGroupHom_apply] at h4
    exact hne h4

theorem a7_four_centralizer_trivial [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {L : Subgroup Γ}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) Q = 4)
    (hirr : ∀ N : Submodule (ZMod 2) Q, (∀ l ∈ L, ∀ q ∈ N, ρ l q ∈ N) → N = ⊥ ∨ N = ⊤)
    {c : Γ} (hc : ∀ l ∈ L, c * l = l * c) : ρ c = 1 := by
  classical
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  have hfaith := faithful_of_irr ρ eL hdim hirr
  have h7 : 7 ∣ Nat.card ↥L := by
    rw [Nat.card_congr eL.toEquiv, card_alt7]
    norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite ↥L := Finite.of_equiv _ eL.symm.toEquiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 h7
  have hxg : orderOf (x : Γ) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx1 : ρ (x : Γ) ≠ 1 := fun h => by
    have := hfaith x h
    rw [this, orderOf_one] at hx
    omega
  have hcard := card_ker_of_order_seven ρ hxg hx1 hdim
  obtain ⟨v, hv0, hvall⟩ := exists_nonzero_of_card_two hcard
  have hcx : ρ c * ρ (x : Γ) = ρ (x : Γ) * ρ c := by
    rw [← map_mul, ← map_mul, hc _ x.2]
  have hcinj : ∀ w : Q, ρ c w = 0 → w = 0 := by
    intro w hw
    have := congrArg (fun u => ρ c⁻¹ u) hw
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hvker : (v : Q) ∈ LinearMap.ker (ρ (x : Γ) - 1) := v.2
  have hcv : ρ c (v : Q) ∈ LinearMap.ker (ρ (x : Γ) - 1) := by
    rw [LinearMap.mem_ker] at hvker ⊢
    have h1 : ρ (x : Γ) (v : Q) = v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvker
      exact hvker
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    calc ρ (x : Γ) (ρ c (v : Q)) = (ρ (x : Γ) * ρ c) (v : Q) := rfl
      _ = (ρ c * ρ (x : Γ)) (v : Q) := by rw [hcx]
      _ = ρ c (v : Q) := by rw [Module.End.mul_apply, h1]
  have hcvv : ρ c (v : Q) = v := by
    rcases hvall ⟨ρ c (v : Q), hcv⟩ with h | h
    · exfalso
      apply hv0
      have h' : ρ c (v : Q) = 0 := congrArg Subtype.val h
      exact Subtype.ext (hcinj _ h')
    · exact congrArg Subtype.val h
  have hinv : ∀ l ∈ L, ∀ q ∈ LinearMap.ker (ρ c - 1), ρ l q ∈ LinearMap.ker (ρ c - 1) := by
    intro l hl q hq
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hq ⊢
    calc ρ c (ρ l q) = (ρ c * ρ l) q := rfl
      _ = (ρ l * ρ c) q := by rw [← map_mul, ← map_mul, hc l hl]
      _ = ρ l q := by rw [Module.End.mul_apply, hq]
  rcases hirr _ hinv with h | h
  · exfalso
    apply hv0
    have : (v : Q) ∈ LinearMap.ker (ρ c - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hcvv
    rw [h] at this
    exact Subtype.ext ((Submodule.mem_bot _).1 this)
  · ext w
    have : w ∈ LinearMap.ker (ρ c - 1) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    simpa using this

theorem card_modEq_inf_ker [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {p : ℕ} [Fact p.Prime]
    {y : Γ} (hy : orderOf y = p) (C : Submodule (ZMod 2) Q)
    (hC : ∀ k ∈ Subgroup.zpowers y, ∀ v ∈ C, ρ k v ∈ C) :
    Nat.card C ≡ Nat.card ↥(C ⊓ LinearMap.ker (ρ y - 1)) [MOD p] := by
  classical
  let K := Subgroup.zpowers y
  have hK : IsPGroup p K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  let act : MulAction K C :=
    { smul := fun k v => ⟨ρ k v, hC k k.2 v v.2⟩
      one_smul := fun v => Subtype.ext (by
        show ρ ((1 : K) : Γ) (v : Q) = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        show ρ ((a * b : K) : Γ) (v : Q) = ρ (a : Γ) (ρ (b : Γ) (v : Q))
        simp [Module.End.mul_apply]) }
  have hmod := hK.card_modEq_card_fixedPoints C
  have hfixy : ∀ v : Q, ρ y v = v → ∀ k ∈ K, ρ k v = v := by
    intro v hv k hk
    have h2 : K ≤ vecStab ρ v := (Subgroup.zpowers_le (H := vecStab ρ v)).2 hv
    exact h2 hk
  have hcard : Nat.card (MulAction.fixedPoints K C) = Nat.card ↥(C ⊓ LinearMap.ker (ρ y - 1)) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨(v.1 : Q), v.1.2, by
          rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
          exact congrArg Subtype.val (v.2 ⟨y, Subgroup.mem_zpowers y⟩)⟩
        invFun := fun v => ⟨⟨(v.1 : Q), v.2.1⟩, fun k => Subtype.ext (by
          have h1 : ρ y (v.1 : Q) = v.1 := by
            have := v.2.2
            rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
              sub_eq_zero] at this
            exact this
          exact hfixy _ h1 k k.2)⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  rw [hcard] at hmod
  exact hmod

theorem four_involution_trivial [Finite Q] (ρ : Representation (ZMod 2) Γ Q)
    (hdim : finrank (ZMod 2) Q = 4) {y t : Γ} (hy : y ^ 5 = 1) (hρy : ρ y ≠ 1)
    (hty : t * y = y * t) (ht : ρ t * ρ t = 1) : ρ t = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hord : orderOf y = 5 := orderOf_eq_prime hy hy1
  have hQ : Nat.card Q = 2 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  have hpow : ∀ D : Submodule (ZMod 2) Q, Nat.card D = 2 ^ finrank (ZMod 2) D := fun D => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hker : LinearMap.ker (ρ y - 1) = ⊥ := by
    have hmod := card_modEq_inf_ker ρ hord ⊤ (fun _ _ v _ => Submodule.mem_top)
    rw [top_inf_eq] at hmod
    have h1 : Nat.card (⊤ : Submodule (ZMod 2) Q) = 2 ^ 4 := by
      rw [← hQ]; exact Nat.card_congr Submodule.topEquiv.toEquiv
    rw [h1, hpow] at hmod
    have hle : finrank (ZMod 2) (LinearMap.ker (ρ y - 1)) ≤ 4 := hdim ▸ Submodule.finrank_le _
    have hne4 : finrank (ZMod 2) (LinearMap.ker (ρ y - 1)) ≠ 4 := by
      intro h4
      apply hρy
      have : LinearMap.ker (ρ y - 1) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4, hdim])
      have h5 : ρ y - 1 = 0 := by
        ext v
        have hv : v ∈ LinearMap.ker (ρ y - 1) := this ▸ Submodule.mem_top
        exact hv
      rwa [sub_eq_zero] at h5
    have h0 : finrank (ZMod 2) (LinearMap.ker (ρ y - 1)) = 0 := by
      generalize finrank (ZMod 2) (LinearMap.ker (ρ y - 1)) = k at hle hne4 hmod ⊢
      interval_cases k <;> simp_all [Nat.ModEq]
    exact Submodule.finrank_eq_zero.1 h0
  by_contra htne
  set C := LinearMap.ker (ρ t - 1) with hCdef
  have hcomm : ∀ k ∈ Subgroup.zpowers y, t * k = k * t := fun k hk => by
    have h1 : y ∈ Subgroup.centralizer ({t} : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hty]
    have h2 : Subgroup.zpowers y ≤ Subgroup.centralizer ({t} : Set Γ) :=
      (Subgroup.zpowers_le).2 h1
    exact Subgroup.mem_centralizer_iff.1 (h2 hk) t (Set.mem_singleton t)
  have hCinv : ∀ k ∈ Subgroup.zpowers y, ∀ v ∈ C, ρ k v ∈ C := by
    intro k hk v hv
    rw [hCdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    calc ρ t (ρ k v) = (ρ t * ρ k) v := rfl
      _ = (ρ k * ρ t) v := by rw [← map_mul, ← map_mul, hcomm k hk]
      _ = ρ k v := by rw [Module.End.mul_apply, hv]
  have hmod := card_modEq_inf_ker ρ hord C hCinv
  have hinf : C ⊓ LinearMap.ker (ρ y - 1) = ⊥ := by rw [hker, inf_bot_eq]
  rw [hinf, hpow, hpow] at hmod
  obtain ⟨v, hv⟩ : ∃ v : Q, ρ t v ≠ v := by
    by_contra h
    push Not at h
    exact htne (LinearMap.ext fun v => by simpa using h v)
  have htwo : ∀ u : Q, u + u = 0 := fun u => by
    rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hw : v + ρ t v ∈ C := by
    rw [hCdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_add]
    have : ρ t (ρ t v) = v := by
      have := congrArg (fun m => m v) ht
      simpa [Module.End.mul_apply] using this
    rw [this, add_comm]
  have hw0 : v + ρ t v ≠ 0 := fun h => hv (by
    have := neg_eq_of_add_eq_zero_right h
    rw [← this]
    exact (neg_eq_of_add_eq_zero_left (htwo v)).symm ▸ rfl)
  have hCne : finrank (ZMod 2) C ≠ 0 := fun h => hw0 (by
    have : C = ⊥ := Submodule.finrank_eq_zero.1 h
    rw [this] at hw
    exact (Submodule.mem_bot _).1 hw)
  have hle : finrank (ZMod 2) C ≤ 4 := hdim ▸ Submodule.finrank_le _
  have h4 : finrank (ZMod 2) C = 4 := by
    simp only [finrank_bot, pow_zero] at hmod
    generalize finrank (ZMod 2) C = k at hle hCne hmod ⊢
    interval_cases k <;> simp_all [Nat.ModEq]
  have : C = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4, hdim])
  apply hv
  have : v ∈ C := this ▸ Submodule.mem_top
  rw [hCdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

open Equiv Equiv.Perm in
theorem a7_four_normal [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {L : Subgroup Γ} [L.Normal]
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) Q = 4)
    (hirr : ∀ N : Submodule (ZMod 2) Q, (∀ l ∈ L, ∀ q ∈ N, ρ l q ∈ N) → N = ⊥ ∨ N = ⊤)
    (g : Γ) : ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * g) * m = m * (l⁻¹ * g) := by
  classical
  have hfaith := faithful_of_irr ρ eL hdim hirr
  obtain ⟨e, he1, hconj, hker1, -⟩ := exists_conj_embedding7 L eL
  have hcent : ∀ c : Γ, e c = 1 → ∀ m ∈ L, c * m = m * c := by
    intro c hc m hm
    have h1 : c * m * c⁻¹ = m := hker1 c hc ⟨m, hm⟩
    calc c * m = (c * m * c⁻¹) * c := by group
      _ = m * c := by rw [h1]
  have hevenAll : ∀ g : Γ, e g ∈ alternatingGroup (Fin 7) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hcon
    set τ : Perm (Fin 7) := swap 0 1 with hτdef
    set c5 : Perm (Fin 7) := swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6 with hc5def
    set d3 : Perm (Fin 7) := swap 0 2 * swap 2 3 with hd3def
    have hτ : sign τ = -1 := by decide
    have hc5 : c5 ∈ alternatingGroup (Fin 7) := by rw [mem_alternatingGroup]; decide
    have hd3 : d3 ∈ alternatingGroup (Fin 7) := by rw [mem_alternatingGroup]; decide
    have hc5pow : c5 ^ 5 = 1 := by decide
    have hc5ne : c5 ≠ 1 := by decide
    have hτc5 : τ * c5 * τ⁻¹ = c5 := by decide
    have hτd3 : τ * d3 * τ⁻¹ ≠ d3 := by decide
    have hττ : τ * τ = 1 := by decide
    have hsg : sign (e g) = -1 := by
      rcases Int.units_eq_one_or (sign (e g)) with h | h
      · exact absurd ((mem_alternatingGroup).2 h) hg
      · exact h
    have ha : τ * (e g)⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hτ, hsg]
      decide
    set l₁ : ↥L := eL.symm ⟨τ * (e g)⁻¹, ha⟩ with hl₁
    have hel₁ : e (l₁ : Γ) = τ * (e g)⁻¹ := by
      rw [he1, hl₁, MulEquiv.apply_symm_apply]
    set g'' : Γ := (l₁ : Γ) * g with hg''
    have heg'' : e g'' = τ := by
      rw [hg'', map_mul, hel₁, inv_mul_cancel_right]
    set xy : ↥L := eL.symm ⟨c5, hc5⟩ with hxy
    set y : Γ := (xy : Γ) with hy
    have hexy : eL xy = ⟨c5, hc5⟩ := by rw [hxy, MulEquiv.apply_symm_apply]
    have hy5 : y ^ 5 = 1 := by
      have : xy ^ 5 = 1 := by
        apply eL.injective
        rw [map_pow, hexy, map_one]
        exact Subtype.ext (by simpa using hc5pow)
      rw [hy, ← Subgroup.coe_pow, this]
      rfl
    have hρy : ρ y ≠ 1 := fun h => by
      have h1 : xy = 1 := hfaith xy h
      have h2 := hexy
      rw [h1, map_one] at h2
      exact hc5ne (congrArg Subtype.val h2).symm
    have hty : g'' * y = y * g'' := by
      have h1 := hconj g'' xy
      rw [hexy, heg''] at h1
      have h2 : (eL (MulAut.conjNormal g'' xy) : Perm (Fin 7)) = c5 := by
        rw [h1]
        simpa using hτc5
      have h3 : MulAut.conjNormal g'' xy = xy := by
        apply eL.injective
        exact Subtype.ext (by rw [h2, hexy])
      have h4 : g'' * y * g''⁻¹ = y := by
        have := congrArg Subtype.val h3
        simpa using this
      calc g'' * y = (g'' * y * g''⁻¹) * g'' := by group
        _ = y * g'' := by rw [h4]
    have ht2 : ρ g'' * ρ g'' = 1 := by
      have hc : e (g'' * g'') = 1 := by rw [map_mul, heg'', hττ]
      have := a7_four_centralizer_trivial ρ eL hdim hirr (c := g'' * g'') (hcent _ hc)
      rwa [map_mul] at this
    have hT : ρ g'' = 1 := four_involution_trivial ρ hdim hy5 hρy hty ht2
    have hTinv : ρ g''⁻¹ = 1 := by
      have : ρ g''⁻¹ * ρ g'' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [hT, mul_one] at this
    set xd : ↥L := eL.symm ⟨d3, hd3⟩ with hxd
    have hexd : eL xd = ⟨d3, hd3⟩ := by rw [hxd, MulEquiv.apply_symm_apply]
    have hconjd : MulAut.conjNormal g'' xd = xd := by
      have hw : ρ ((MulAut.conjNormal g'' xd * xd⁻¹ : ↥L) : Γ) = 1 := by
        have hcoe : ((MulAut.conjNormal g'' xd * xd⁻¹ : ↥L) : Γ) = g'' * (xd : Γ) * g''⁻¹ * (xd : Γ)⁻¹ := by
          simp
        rw [hcoe, map_mul, map_mul, map_mul, hT, hTinv, one_mul, mul_one, ← map_mul, mul_inv_cancel,
          map_one]
      have := hfaith _ hw
      exact mul_inv_eq_one.1 this
    have h5 := hconj g'' xd
    rw [hconjd, hexd, heg''] at h5
    exact hτd3 h5.symm
  have h := hevenAll g
  set l : ↥L := eL.symm ⟨e g, h⟩ with hl
  have hel : e (l : Γ) = e g := by rw [he1, hl, MulEquiv.apply_symm_apply]
  refine ⟨l, l.2, ?_⟩
  apply hcent
  rw [map_mul, map_inv, hel, inv_mul_cancel]

theorem a7_four_normalizer [Finite Q] (ρ : Representation (ZMod 2) Γ Q) {L : Subgroup Γ}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) Q = 4)
    (hirr : ∀ N : Submodule (ZMod 2) Q, (∀ l ∈ L, ∀ q ∈ N, ρ l q ∈ N) → N = ⊥ ∨ N = ⊤)
    {g : Γ} (hg : g ∈ Subgroup.normalizer (L : Set Γ)) :
    ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * g) * m = m * (l⁻¹ * g) := by
  set N : Subgroup Γ := Subgroup.normalizer (L : Set Γ) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  let L' : Subgroup ↥N := L.subgroupOf N
  have : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  let eL' : ↥L' ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLN).trans eL
  let ρ' : Representation (ZMod 2) ↥N Q := ρ.comp N.subtype
  have hirr' : ∀ M : Submodule (ZMod 2) Q, (∀ l ∈ L', ∀ q ∈ M, ρ' l q ∈ M) → M = ⊥ ∨ M = ⊤ :=
    fun M hM => hirr M fun l hl q hq => hM ⟨l, hLN hl⟩ (Subgroup.mem_subgroupOf.2 hl) q hq
  obtain ⟨l', hl', hall⟩ := a7_four_normal ρ' eL' hdim hirr' ⟨g, hg⟩
  refine ⟨(l' : Γ), Subgroup.mem_subgroupOf.1 hl', fun m hm => ?_⟩
  have h := hall ⟨m, hLN hm⟩ (Subgroup.mem_subgroupOf.2 hm)
  have h2 := congrArg Subtype.val h
  simpa using h2

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
