module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Component
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Orbit
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

theorem alt5_eq_one_of_forall_commute :
    ∀ x : alternatingGroup (Fin 5), (∀ y : alternatingGroup (Fin 5), x * y = y * x) → x = 1 := by
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem eq_one_of_forall_commute_of_alt5 {X : Type*} [Group X]
    (φ : X ≃* alternatingGroup (Fin 5)) {x : X} (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  apply φ.injective
  rw [map_one]
  refine alt5_eq_one_of_forall_commute _ fun y => ?_
  obtain ⟨y', rfl⟩ := φ.surjective y
  rw [← map_mul, ← map_mul, hx]

theorem card_centralizer_alt5_of_involution :
    ∀ c : alternatingGroup (Fin 5), c * c = 1 → c ≠ 1 →
      Fintype.card {a : alternatingGroup (Fin 5) // a * c = c * a} = 4 := by
  decide +kernel

theorem card_centralizer_of_alt5 {H : Type*} [Group H] (φ : H ≃* alternatingGroup (Fin 5))
    {c : H} (hc : c * c = 1) (hc1 : c ≠ 1) : Nat.card {a : H // a * c = c * a} = 4 := by
  have hec : φ c * φ c = 1 := by rw [← map_mul, hc, map_one]
  have hec1 : φ c ≠ 1 := fun h => hc1 (φ.injective (by rw [h, map_one]))
  have hiff : ∀ a : H, a * c = c * a ↔ φ a * φ c = φ c * φ a := fun a => by
    rw [← map_mul, ← map_mul, φ.injective.eq_iff]
  have hcard : Nat.card {a : H // a * c = c * a} =
      Nat.card {a : alternatingGroup (Fin 5) // a * φ c = φ c * a} :=
    Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv hiff)
  rw [hcard, Nat.card_eq_fintype_card]
  exact card_centralizer_alt5_of_involution (φ c) hec hec1

theorem eq_one_of_conj_eq_mul {X : Type*} [Group X] {ω s e : X} (he2 : e * e = 1)
    (hωe : ω * e * ω⁻¹ = e) (hωs : ω * s * ω⁻¹ = s * e) (hω9 : ω ^ 9 = 1) : e = 1 := by
  have hek : ∀ k : ℕ, ω * e ^ k * ω⁻¹ = e ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ω * e ^ (k + 1) * ω⁻¹ = (ω * e ^ k * ω⁻¹) * (ω * e * ω⁻¹) := by
            rw [pow_succ]; group
        _ = e ^ (k + 1) := by rw [ih, hωe, pow_succ]
  have hk : ∀ k : ℕ, ω ^ k * s * (ω ^ k)⁻¹ = s * e ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ω ^ (k + 1) * s * (ω ^ (k + 1))⁻¹ = ω * (ω ^ k * s * (ω ^ k)⁻¹) * ω⁻¹ := by
            rw [pow_succ']; group
        _ = (ω * s * ω⁻¹) * (ω * e ^ k * ω⁻¹) := by rw [ih]; group
        _ = s * e * e ^ k := by rw [hωs, hek]
        _ = s * e ^ (k + 1) := by rw [mul_assoc, ← pow_succ']
  have h9 := hk 9
  rw [hω9, one_mul, inv_one, mul_one] at h9
  have he9 : e ^ 9 = e := by
    rw [show (9 : ℕ) = 2 * 4 + 1 from rfl, pow_succ, pow_mul, pow_two, he2, one_pow, one_mul]
  rw [he9] at h9
  have := congrArg (s⁻¹ * ·) h9
  simpa using this.symm

section Generic

variable {X : Type*} [Group X]

theorem eq_one_of_mem_of_alt5 {E : Subgroup X} (φ : E ≃* alternatingGroup (Fin 5)) {x : X}
    (hx : x ∈ E) (hxE : ∀ y ∈ E, x * y = y * x) : x = 1 := by
  have h := eq_one_of_forall_commute_of_alt5 φ (x := ⟨x, hx⟩) fun y => Subtype.ext (hxE y y.2)
  exact congrArg Subtype.val h

theorem mem_of_commute_of_alt5 {E T : Subgroup X} (φ : E ≃* alternatingGroup (Fin 5))
    (hTE : T ≤ E) (hT4 : Nat.card T = 4) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {e : X}
    (heT : e ∈ T) (he1 : e ≠ 1) (he2 : e * e = 1) {a : X} (haE : a ∈ E)
    (hae : a * e = e * a) : a ∈ T := by
  have hc := card_centralizer_of_alt5 φ (c := ⟨e, hTE heT⟩) (Subtype.ext he2)
    fun h => he1 (congrArg Subtype.val h)
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Finite E := Finite.of_equiv _ φ.symm.toEquiv
  by_contra haT
  let f : Option T → {x : E // x * ⟨e, hTE heT⟩ = ⟨e, hTE heT⟩ * x} := fun o =>
    match o with
    | none => ⟨⟨a, haE⟩, Subtype.ext hae⟩
    | some s => ⟨⟨s, hTE s.2⟩, Subtype.ext (hTc s s.2 e heT)⟩
  have hf : Function.Injective f := by
    intro o₁ o₂ h12
    rcases o₁ with _ | s₁ <;> rcases o₂ with _ | s₂
    · rfl
    · have hv : a = (s₂ : X) := congrArg (fun x => ((x.1 : E) : X)) h12
      exact (haT (hv ▸ s₂.2)).elim
    · have hv : (s₁ : X) = a := congrArg (fun x => ((x.1 : E) : X)) h12
      exact (haT (hv ▸ s₁.2)).elim
    · exact congrArg some (Subtype.ext (congrArg (fun x => ((x.1 : E) : X)) h12))
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option, hT4, hc] at h5
  omega

theorem false_of_five_mem {T : Subgroup X} (hT4 : Nat.card T = 4) {a b c d x : X}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) (hx : x ∈ T) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hax : a ≠ x) (hbc : b ≠ c) (hbd : b ≠ d) (hbx : b ≠ x)
    (hcd : c ≠ d) (hcx : c ≠ x) (hdx : d ≠ x) : False := by
  have hfin : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have h1 : a ∉ ({b, c, d, x} : Set X) := by simp [hab, hac, had, hax]
  have h2 : b ∉ ({c, d, x} : Set X) := by simp [hbc, hbd, hbx]
  have h3 : c ∉ ({d, x} : Set X) := by simp [hcd, hcx]
  have h5 : ({a, b, c, d, x} : Set X).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_pair hdx]
  have hsub : ({a, b, c, d, x} : Set X) ⊆ (T : Set X) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hle := Set.ncard_le_ncard hsub ((Set.finite_coe_iff (s := (T : Set X))).mp hfin)
  rw [h5, ← Nat.card_coe_set_eq] at hle
  have hT : Nat.card (T : Set X) = 4 := hT4
  omega

theorem commute_of_conj_mem_card_four {T : Subgroup X} (hT4 : Nat.card T = 4) {e ω : X}
    (heT : e ∈ T) (he1 : e ≠ 1) (he2 : e * e = 1) (hωe : ω * e * ω⁻¹ = e)
    (hωT : ∀ s ∈ T, ω * s * ω⁻¹ ∈ T) (hω9 : ω ^ 9 = 1) {s : X} (hsT : s ∈ T) :
    s * ω = ω * s := by
  by_cases hs1 : s = 1
  · rw [hs1, one_mul, mul_one]
  by_cases hse : s = e
  · rw [hse]
    exact (mul_inv_eq_iff_eq_mul.mp hωe).symm
  have hmem : ω * s * ω⁻¹ = s ∨ ω * s * ω⁻¹ = s * e := by
    by_contra hcon
    have hcon' := not_or.mp hcon
    have hs_e : s * e ≠ 1 := fun h => hse (by
      rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left he2])
    exact false_of_five_mem hT4 (one_mem T) heT hsT (mul_mem hsT heT) (hωT s hsT)
      (Ne.symm he1) (Ne.symm hs1) (Ne.symm hs_e)
      (fun h => hs1 (conj_eq_one_iff.mp h.symm)) (Ne.symm hse)
      (fun h => hs1 (mul_right_cancel (h.symm.trans (one_mul e).symm)))
      (fun h => hse (mul_left_cancel (mul_right_cancel (h.symm.trans hωe.symm))))
      (fun h => he1 (mul_left_cancel (h.symm.trans (mul_one s).symm)))
      (Ne.symm hcon'.1) (Ne.symm hcon'.2)
  rcases hmem with h | h
  · exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · exact absurd (eq_one_of_conj_eq_mul he2 hωe h hω9) he1

theorem conj_mul_eq_of_commute_layer {E : Subgroup X} (φ : E ≃* alternatingGroup (Fin 5))
    {ω t l : X} (hωt : ω * t = t * ω) (hlE : ∀ y ∈ E, l * y = y * l)
    (hE : ∀ y ∈ E, ω * y * ω⁻¹ ∈ E) (hE' : ∀ y ∈ E, ω⁻¹ * y * ω ∈ E) (htl : t * l ∈ E) :
    ω * (t * l) * ω⁻¹ = t * l := by
  have hc : (t * l)⁻¹ * (ω * (t * l) * ω⁻¹) = l⁻¹ * (ω * l * ω⁻¹) := by
    calc (t * l)⁻¹ * (ω * (t * l) * ω⁻¹) = l⁻¹ * t⁻¹ * ((ω * t) * l * ω⁻¹) := by group
      _ = l⁻¹ * t⁻¹ * (t * ω * l * ω⁻¹) := by rw [hωt]
      _ = l⁻¹ * (ω * l * ω⁻¹) := by group
  have hcE : (t * l)⁻¹ * (ω * (t * l) * ω⁻¹) ∈ E := mul_mem (inv_mem htl) (hE _ htl)
  have h1 := eq_one_of_mem_of_alt5 φ hcE fun y hy => by
    rw [hc]
    have h1 : l * (ω⁻¹ * y * ω) = (ω⁻¹ * y * ω) * l := hlE _ (hE' y hy)
    have h2 : l⁻¹ * y = y * l⁻¹ := by
      calc l⁻¹ * y = l⁻¹ * (y * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * y) * l⁻¹ := by rw [hlE y hy]
        _ = y * l⁻¹ := by group
    calc l⁻¹ * (ω * l * ω⁻¹) * y = l⁻¹ * (ω * (l * (ω⁻¹ * y * ω)) * ω⁻¹) := by group
      _ = l⁻¹ * (ω * ((ω⁻¹ * y * ω) * l) * ω⁻¹) := by rw [h1]
      _ = l⁻¹ * y * (ω * l * ω⁻¹) := by group
      _ = y * l⁻¹ * (ω * l * ω⁻¹) := by rw [h2]
      _ = y * (l⁻¹ * (ω * l * ω⁻¹)) := by group
  exact (inv_mul_eq_one.mp h1).symm

theorem card_inf_eq_four {L E : Subgroup X} (φ : E ≃* alternatingGroup (Fin 5))
    (hL : Nat.card L = 8) (h4 : 4 ≤ Nat.card (L ⊓ E : Subgroup X)) :
    Nat.card (L ⊓ E : Subgroup X) = 4 := by
  have hE : Nat.card E = 60 := by rw [Nat.card_congr φ.toEquiv, card_alt5]
  have h1 : Nat.card (L ⊓ E : Subgroup X) ∣ 8 := by
    rw [← hL]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (L ⊓ E : Subgroup X) ∣ 60 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card (L ⊓ E : Subgroup X) ∣ 4 := by
    have := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd 8 60 = 4 by norm_num] at this
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem exists_commute_of_alt5 {L E P : Subgroup X} (φ : E ≃* alternatingGroup (Fin 5))
    (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) (hL2 : ∀ a ∈ L, a * a = 1)
    (hT4 : Nat.card (L ⊓ E : Subgroup X) = 4) {t l : X} (ht : t ∈ L) (hl : l ∈ L)
    (ht1 : t ≠ 1) (hlt : l ≠ t) (hlE : ∀ y ∈ E, l * y = y * l) (hcov : t ∈ E ∨ t * l ∈ E)
    (hPE : ∀ ω ∈ P, ∀ y ∈ E, ω * y * ω⁻¹ ∈ E) (hPt : ∀ ω ∈ P, ω * t = t * ω)
    (hP9 : Nat.card P = 9) :
    ∃ u ∈ L, u ≠ 1 ∧ u ≠ t ∧ ∀ x ∈ P, u * x = x * u := by
  have hTc : ∀ a ∈ L ⊓ E, ∀ b ∈ L ⊓ E, a * b = b * a := fun a ha b hb =>
    hLc a (mem_inf.mp ha).1 b (mem_inf.mp hb).1
  obtain ⟨e, heT, he1, hPe⟩ : ∃ e ∈ L ⊓ E, e ≠ 1 ∧ ∀ ω ∈ P, ω * e * ω⁻¹ = e := by
    rcases hcov with h | h
    · exact ⟨t, mem_inf.mpr ⟨ht, h⟩, ht1, fun ω hω => by rw [hPt ω hω, mul_inv_cancel_right]⟩
    · refine ⟨t * l, mem_inf.mpr ⟨mul_mem ht hl, h⟩, fun h1 => hlt ?_, fun ω hω => ?_⟩
      · exact (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_left (hL2 t ht))
      · refine conj_mul_eq_of_commute_layer φ (hPt ω hω) hlE (hPE ω hω) (fun y hy => ?_) h
        have := hPE ω⁻¹ (inv_mem hω) y hy
        rwa [inv_inv] at this
  have he2 : e * e = 1 := hL2 e (mem_inf.mp heT).1
  have hPT : ∀ ω ∈ P, ∀ s ∈ L ⊓ E, s * ω = ω * s := by
    intro ω hω s hs
    have hω9 : ω ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := P) (x := ⟨ω, hω⟩)
      rw [hP9] at h
      exact congrArg Subtype.val h
    have hωe := hPe ω hω
    refine commute_of_conj_mem_card_four hT4 heT he1 he2 hωe (fun r hr => ?_) hω9 hs
    refine mem_of_commute_of_alt5 φ inf_le_right hT4 hTc heT he1 he2
      (hPE ω hω r (mem_inf.mp hr).2) ?_
    calc ω * r * ω⁻¹ * e = ω * r * ω⁻¹ * (ω * e * ω⁻¹) := by rw [hωe]
      _ = ω * (r * e) * ω⁻¹ := by group
      _ = ω * (e * r) * ω⁻¹ := by rw [hTc r hr e heT]
      _ = (ω * e * ω⁻¹) * (ω * r * ω⁻¹) := by group
      _ = e * (ω * r * ω⁻¹) := by rw [hωe]
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu12⟩ :=
    S5.exists_ne_one_ne_one_ne (A := L ⊓ E) (by omega)
  obtain ⟨u, huT, hu1, hut⟩ : ∃ u ∈ L ⊓ E, u ≠ 1 ∧ u ≠ t := by
    by_cases h : u₁ = t
    · exact ⟨u₂, hu₂, hu₂1, fun h2 => hu12 (h.trans h2.symm)⟩
    · exact ⟨u₁, hu₁, hu₁1, h⟩
  exact ⟨u, (mem_inf.mp huT).1, hu1, hut, fun x hx => hPT x hx u huT⟩

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem conj_mem_layer {ω y : S.O} (hω : ω ∈ S.Mbar)
    (hy : y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype) :
    ω * y * ω⁻¹ ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨ω, hω⟩ * y' * ⟨ω, hω⟩⁻¹,
    (CFSG.ComponentClassification.Layer.normal S.Mbar).conj_mem y' hy' ⟨ω, hω⟩, rfl⟩

theorem layer_faithful_of_data (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (hnoAll : S11.NoA2All S) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : PlusTypeAt S g ht)
    (hdata : ∀ l ∈ S.Lbar g, l ≠ 1 →
      (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) →
      Nonempty ((timmesfeldLayer S.Mbar).map S.Mbar.subtype ≃* alternatingGroup (Fin 5)) ∧
        Nat.card (RmodN S g l) = 60 ∧
        4 ≤ Nat.card (S.Lbar g ⊓ (timmesfeldLayer S.Mbar).map S.Mbar.subtype : Subgroup S.O) ∧
        ∀ s ∈ S.Lbar g, s ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype ∨
          s * l ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype) :
    ∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) →
      l = 1 := by
  intro l hl hlE
  by_contra hl1
  obtain ⟨⟨φ⟩, h60, h4E, hcov⟩ := hdata l hl hl1 hlE
  have hNo : NoA2 S g := S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hlt : l ≠ t := fun h => by
    have h36 := TriPlus.card_RmodN_eq_thirtysix H C ht ht1 hVQ hΩ h4 hplus
    rw [h] at h60
    omega
  have hLcard : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  obtain ⟨P, hPR, hP9⟩ := exists_le_Rbar_card_nine H C ht ht1 hVQ hΩ h4 hplus
  obtain ⟨u, huL, hu1, hut, huP⟩ := exists_commute_of_alt5 φ
    (fun a ha b hb => Lbar_comm S H.conj_mem ha hb)
    (fun a ha => mul_self_of_mem_Lbar S H.conj_mem ha) (card_inf_eq_four φ hLcard h4E) ht hl
    ht1 hlt hlE (hcov t ht) (fun ω hω y hy => conj_mem_layer (Rbar_le_Mbar (hPR hω)) hy)
    (fun ω hω => mem_centralizer_singleton_iff.mp (Rbar_le_centralizer H.conj_mem (hPR hω)))
    hP9
  rcases eq_one_or_eq_of_commute_card_nine hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 huL
      huP with h | h
  · exact hu1 h
  · exact hut h

theorem layer_faithful (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (hnoAll : S11.NoA2All S) (hirr : ¬ S.IsReducible) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : PlusTypeAt S g ht) (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar)) :
    ∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) →
      l = 1 :=
  layer_faithful_of_data hCE hw hnoAll H C ht ht1 hVQ hΩ h4 hplus fun _ hl hl1 hlE =>
    layer_data_of_commute hCE (S14.irr_of_not_isReducible hirr) hw H
      (S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)) C hq hl hl1 hlE

end CFSG.GF2Type.Smith1979.OmegaPlus
