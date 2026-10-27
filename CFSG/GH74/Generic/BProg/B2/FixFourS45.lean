module

public import CFSG.GH74.Generic.BProg.Vocab
import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.GH74.Generic.S45.AutE8
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup
open scoped Pointwise

@[expose] def InvolFixFour (Pr : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → Pr ↥L → ∀ y : X, orderOf y = 2 →
    ∃ E : Subgroup X, E ≤ L ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧ ∀ e ∈ E, y * e = e * y

@[expose] def FourConj (Pr : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (Kt : Type) [Group Kt] [Finite Kt], Pr Kt → ∀ E E' : Subgroup Kt, CFSG.IsElementaryAbelian 2 ↥E →
    Nat.card ↥E = 4 → CFSG.IsElementaryAbelian 2 ↥E' → Nat.card ↥E' = 4 →
      ∃ g : Kt, E' = E.map (MulAut.conj g).toMonoidHom

namespace FixFourS45

@[expose] def HasE8Sylow (T : Type) [Group T] : Prop :=
  ∃ P : Sylow 2 T, CFSG.IsElementaryAbelian 2 ↥(P : Subgroup T) ∧ Nat.card ↥(P : Subgroup T) = 8

@[expose] def InvolConj (T : Type) [Group T] : Prop :=
  ∀ x y : T, orderOf x = 2 → orderOf y = 2 → ∃ g : T, g * x * g⁻¹ = y

theorem sylow_eq_map_conj {T : Type} [Group T] [Finite T] (P Q : Sylow 2 T) :
    ∃ g : T, (Q : Subgroup T) = (P : Subgroup T).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T P Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem HasE8Sylow.all {T : Type} [Group T] [Finite T] (h : HasE8Sylow T) (Q : Sylow 2 T) :
    CFSG.IsElementaryAbelian 2 ↥(Q : Subgroup T) ∧ Nat.card ↥(Q : Subgroup T) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPel, hP8⟩ := h
  obtain ⟨g, hg⟩ := sylow_eq_map_conj P Q
  rw [hg]
  exact ⟨CFSG.IsElementaryAbelian.map _,
    by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP8]⟩

theorem HasE8Sylow.of_mulEquiv {T T' : Type} [Group T] [Finite T] [Group T'] (e : T ≃* T')
    (h : HasE8Sylow T) : HasE8Sylow T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPel, hP8⟩ := h
  let P' : Sylow 2 T' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP' : (P' : Subgroup T') = (P : Subgroup T).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  refine ⟨P', ?_, ?_⟩
  · rw [hP']
    exact CFSG.IsElementaryAbelian.map _
  · rw [hP', Subgroup.card_map_of_injective e.injective, hP8]

theorem InvolConj.of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : InvolConj T) :
    InvolConj T' := by
  intro x y hx hy
  obtain ⟨g, hg⟩ := h (e.symm x) (e.symm y) (by rw [MulEquiv.orderOf_eq]; exact hx)
    (by rw [MulEquiv.orderOf_eq]; exact hy)
  refine ⟨e g, ?_⟩
  have := congrArg e hg
  simpa using this

theorem isElementaryAbelian_of_le {X : Type} [Group X] {V E : Subgroup X}
    [hV : CFSG.IsElementaryAbelian 2 V] (h : E ≤ V) : CFSG.IsElementaryAbelian 2 E := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    have := (IsMulCommutative.is_comm (M := V)).comm ⟨a, h a.2⟩ ⟨b, h b.2⟩
    exact congrArg (fun z : V => (z : X)) this
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun x => ?_)
    apply Subtype.ext
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 V) ⟨x, h x.2⟩
    simpa using congrArg Subtype.val this

theorem exists_four_fixed {X : Type} [Group X] [Finite X] (V : Subgroup X)
    [CFSG.IsElementaryAbelian 2 V] (hV8 : Nat.card V = 8) {y : X}
    (hy : y ∈ normalizer (V : Set X)) (hy2 : y * y = 1) :
    ∃ E : Subgroup X, E ≤ V ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      ∀ e ∈ E, y * e = e * y := by
  classical
  have hsq : ∀ v : V, v * v = 1 := by
    intro v
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 V) v
    simpa [pow_two] using this
  have hcomm : ∀ a b : V, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := V)).comm a b
  set φ : MulAut V := V.normalizerMonoidHom ⟨y, hy⟩ with hφ
  have hφapp : ∀ v : V, ((φ v : V) : X) = y * v * y⁻¹ := fun v => rfl
  have hφφ : ∀ v : V, φ (φ v) = v := by
    intro v
    apply Subtype.ext
    rw [hφapp, hφapp]
    have : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    simp only [this]
    calc y * (y * (v : X) * y) * y = (y * y) * (v : X) * (y * y) := by group
      _ = v := by rw [hy2]; group
  let f : V →* V := MonoidHom.mk' (fun v => v * φ v) (by
    intro a b
    simp only [map_mul]
    calc a * b * (φ a * φ b) = a * (b * φ a) * φ b := by group
      _ = a * (φ a * b) * φ b := by rw [hcomm b (φ a)]
      _ = a * φ a * (b * φ b) := by group)
  have hker : ∀ v : V, v ∈ f.ker ↔ φ v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    show v * φ v = 1 ↔ φ v = v
    constructor
    · intro h
      have h1 : φ v = v⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (hsq v)
    · intro h
      rw [h]
      exact hsq v
  have hrange : f.range ≤ f.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker]
    show φ (v * φ v) = v * φ v
    rw [map_mul, hφφ, hcomm]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hV8] at hcard
  have hle : Nat.card f.range ≤ Nat.card f.ker := Subgroup.card_le_of_le hrange
  have hdvd : Nat.card f.ker ∣ 8 := by
    rw [← hV8]; exact Subgroup.card_subgroup_dvd_card _
  have h4 : 4 ∣ Nat.card f.ker := by
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have hle8 : Nat.card f.ker ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hk : 0 < Nat.card f.ker := Nat.card_pos
    interval_cases h : Nat.card f.ker <;> omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥f.ker) 2 (n := 2)
    (by simpa using h4)
  have hEV : (Q.map f.ker.subtype).map V.subtype ≤ V := Subgroup.map_subtype_le _
  refine ⟨(Q.map f.ker.subtype).map V.subtype, hEV, isElementaryAbelian_of_le hEV, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective V.subtype_injective,
      Subgroup.card_map_of_injective f.ker.subtype_injective, hQ]; norm_num
  · intro e he
    obtain ⟨w, ⟨q, hq, rfl⟩, rfl⟩ := Subgroup.mem_map.1 he
    have h1 : φ (q : V) = q := (hker _).1 q.2
    have h2 := congrArg Subtype.val h1
    rw [hφapp] at h2
    show y * ((q : V) : X) = ((q : V) : X) * y
    calc y * ((q : V) : X) = (y * ((q : V) : X) * y⁻¹) * y := by group
      _ = ((q : V) : X) * y := by rw [h2]

theorem exists_invariant_sylow {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal] {y : X}
    (hy2 : y * y = 1) :
    ∃ P : Sylow 2 ↥L, y ∈ normalizer (((P : Subgroup ↥L).map L.subtype : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : MulAut ↥L := MulAut.conjNormal y with ha
  let S : Subgroup (MulAut ↥L) := Subgroup.zpowers a
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, hy2, map_one]
  have hS : IsPGroup 2 S := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hfp := hS.card_modEq_card_fixedPoints (Sylow 2 ↥L)
  have h1 := card_sylow_modEq_one (p := 2) (G := ↥L)
  have h2 : Nat.card (MulAction.fixedPoints S (Sylow 2 ↥L)) ≡ 1 [MOD 2] := hfp.symm.trans h1
  have hpos : 0 < Nat.card (MulAction.fixedPoints S (Sylow 2 ↥L)) := by
    rcases Nat.eq_zero_or_pos (Nat.card (MulAction.fixedPoints S (Sylow 2 ↥L))) with h | h
    · rw [h] at h2; exact absurd h2 (by decide)
    · exact h
  obtain ⟨⟨P0, hP0⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  refine ⟨P0, ?_⟩
  have hinv : ∀ v ∈ (P0 : Subgroup ↥L), a v ∈ (P0 : Subgroup ↥L) := by
    intro v hv
    have h : ((⟨a, Subgroup.mem_zpowers a⟩ : S) • P0 : Sylow 2 ↥L) = P0 := hP0 _
    have e : (⟨a, Subgroup.mem_zpowers a⟩ : S) • ((P0 : Sylow 2 ↥L) : Subgroup ↥L) =
        ((P0 : Sylow 2 ↥L) : Subgroup ↥L) :=
      (Sylow.pointwise_smul_def (g := (⟨a, Subgroup.mem_zpowers a⟩ : S)) (P := P0)).symm.trans
        (congrArg (fun Q : Sylow 2 ↥L => (Q : Subgroup ↥L)) h)
    have := Subgroup.smul_mem_pointwise_smul v (⟨a, Subgroup.mem_zpowers a⟩ : S)
      (P0 : Subgroup ↥L) hv
    exact e ▸ this
  have hinv' : ∀ v ∈ ((P0 : Subgroup ↥L).map L.subtype : Subgroup X),
      y * v * y⁻¹ ∈ ((P0 : Subgroup ↥L).map L.subtype : Subgroup X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨a v, hinv v hv, by rw [ha]; rfl⟩
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hinv' h
  · intro hh
    have := hinv' _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      rw [hyinv]
      calc y * (y * h * y) * y = (y * y) * h * (y * y) := by group
        _ = h := by rw [hy2]; group
    rwa [e] at this

theorem involFixFour_of_hasE8Sylow {Pr : ∀ (Kt : Type) [Group Kt], Prop}
    (h : ∀ (Kt : Type) [Group Kt] [Finite Kt], Pr Kt → HasE8Sylow Kt) : InvolFixFour Pr := by
  intro X _ _ L hL hPr y hy
  have hy2 : y * y = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (hy ▸ dvd_rfl)
  obtain ⟨P, hPn⟩ := exists_invariant_sylow L hy2
  obtain ⟨hPel, hP8⟩ := (h ↥L hPr).all P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 ↥(P : Subgroup ↥L) := hPel
  have : CFSG.IsElementaryAbelian 2 ↥((P : Subgroup ↥L).map L.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hV8 : Nat.card ↥((P : Subgroup ↥L).map L.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hP8
  obtain ⟨E, hEV, hEel, hE4, hEfix⟩ := exists_four_fixed _ hV8 hPn hy2
  exact ⟨E, hEV.trans (Subgroup.map_subtype_le _), hEel, hE4, hEfix⟩

theorem exists_order_seven {T : Type} [Group T] [Finite T] (P : Sylow 2 T)
    (hP : CFSG.IsElementaryAbelian 2 ↥(P : Subgroup T)) (hP8 : Nat.card ↥(P : Subgroup T) = 8)
    (hconj : InvolConj T) :
    ∃ a ∈ (P : Subgroup T).normalizerMonoidHom.range, orderOf a = 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set R : Subgroup T := (P : Subgroup T) with hR
  set ρ := R.normalizerMonoidHom with hρ
  have hsq : ∀ x : R, x * x = 1 := by
    intro v
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 R) v
    simpa [pow_two] using this
  have hord2 : ∀ r : R, r ≠ 1 → orderOf (r : T) = 2 := fun r hr =>
    orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val (hsq r))
      (fun h => hr (Subtype.ext h))
  have htrans : ∀ r s : R, r ≠ 1 → s ≠ 1 → ∃ f ∈ ρ.range, f r = s := by
    intro r s hr hs
    obtain ⟨g, hg⟩ := hconj _ _ (hord2 r hr) (hord2 s hs)
    have hsP : (s : T) ∈ (P : Subgroup T) := s.2
    obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem P (r : T) g⁻¹ r.2
      (by rw [inv_inv, hg]; exact hsP)
    refine ⟨ρ ⟨n⁻¹, inv_mem hn⟩, ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show n⁻¹ * (r : T) * n⁻¹⁻¹ = s
    rw [inv_inv, ← hn', inv_inv, hg]
  set A := ρ.range with hA
  have hfinA : Finite A := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨r0, hr0⟩ := CFSG.GH74.Generic.S45.exists_ne_one_of_card (R := R) hP8
  have horb : MulAction.orbit A r0 = {x : R | x ≠ 1} := by
    ext s
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      show f r0 ≠ 1
      intro h
      apply hr0
      apply f.injective
      rw [h, map_one]
    · intro hs
      obtain ⟨f, hf, hfs⟩ := htrans r0 s hr0 hs
      exact ⟨⟨f, hf⟩, hfs⟩
  have hcard7 : (MulAction.orbit A r0).ncard = 7 := by
    rw [horb, ← Nat.card_coe_set_eq]
    have := CFSG.GH74.Generic.S45.card_ne_one_aux (R := R)
    rw [hP8] at this
    have e : Nat.card ↥{x : R | x ≠ 1} = Nat.card {y : R // y ≠ 1} := rfl
    omega
  have h7 : 7 ∣ Nat.card A := by
    have := Subgroup.index_dvd_card (MulAction.stabilizer A r0)
    rwa [MulAction.index_stabilizer, hcard7] at this
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := A) 7 h7
  exact ⟨b, b.2, (Subgroup.orderOf_coe b).trans hb⟩

section Hyp7

variable {R : Type} [Group R] [Finite R]

theorem exists_mem_ne_one_apply_mem (hR : Nat.card R = 8) (a : MulAut R) {W : Subgroup R}
    (hW : Nat.card W = 4) : ∃ u ∈ W, u ≠ 1 ∧ a u ∈ W := by
  set W₁ : Subgroup R := W.map a.toMonoidHom with hW₁
  have hW1 : Nat.card W₁ = 4 := by
    rw [hW₁, Subgroup.card_map_of_injective a.injective]; exact hW
  have hidx : W.index = 2 := by
    have := Subgroup.card_mul_index W; rw [hW, hR] at this; omega
  have hidx1 : W₁.index = 2 := by
    have := Subgroup.card_mul_index W₁; rw [hW1, hR] at this; omega
  have hle : (W ⊓ W₁).index ≤ 4 := by
    have : (W ⊓ W₁).index ≤ W.index * W₁.index := Subgroup.index_inf_le
    rw [hidx, hidx1] at this; omega
  have hcard : Nat.card ↥(W ⊓ W₁) * (W ⊓ W₁).index = 8 := by
    rw [← hR]; exact Subgroup.card_mul_index _
  have hpos : 0 < Nat.card ↥(W ⊓ W₁) := Nat.card_pos
  have h2 : 1 < Nat.card ↥(W ⊓ W₁) := by
    by_contra hlt
    have h1 : Nat.card ↥(W ⊓ W₁) = 1 := by omega
    rw [h1] at hcard; omega
  obtain ⟨⟨w, hw⟩, hw1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 ((Subgroup.one_lt_card_iff_ne_bot _).1 h2)
  obtain ⟨hwW, hwW₁⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨u, huW, hu⟩ := Subgroup.mem_map.1 hwW₁
  refine ⟨u, huW, ?_, ?_⟩
  · rintro rfl
    apply hw1
    apply Subtype.ext
    simpa using hu.symm
  · have : a u = w := hu
    rw [this]; exact hwW

theorem eq_four_of_mem (hR : Nat.card R = 8) (hsq : ∀ x : R, x * x = 1) {a : MulAut R}
    (ha : orderOf a = 7) {W : Subgroup R} (hW : Nat.card W = 4) {u : R} (huW : u ∈ W)
    (hu1 : u ≠ 1) (hauW : a u ∈ W) : ∀ x ∈ W, x = 1 ∨ x = u ∨ x = a u ∨ x = u * a u := by
  have hinv : ∀ x : R, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hau1 : a u ≠ 1 := fun h => hu1 (a.injective (by rw [h, map_one]))
  have hau : a u ≠ u := fun h => hu1 (CFSG.GH74.Generic.S45.fix_seven_eight hR a ha u h)
  have h1 : u * a u ≠ 1 := fun h => hau (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hinv])
  have h2 : u * a u ≠ u := fun h => hau1 (by simpa using h)
  have h3 : u * a u ≠ a u := fun h => hu1 (by simpa using h)
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxu, hxau, hxuau⟩ := hcon
  have hsub : (insert x (insert 1 (insert u (insert (a u) {u * a u}))) : Set R) ⊆ W := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact W.one_mem
    · exact huW
    · exact hauW
    · exact W.mul_mem huW hauW
  have hcnt : (insert x (insert 1 (insert u (insert (a u) {u * a u}))) : Set R).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_singleton]
    · simp only [Set.mem_singleton_iff]; exact h3.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨hau.symm, h2.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hu1.symm, hau1.symm, h1.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨hx1, hxu, hxau, hxuau⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hWn : (W : Set R).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hW
  omega

theorem exists_zpowers_map_eq (hR : Nat.card R = 8) (hsq : ∀ x : R, x * x = 1) {a : MulAut R}
    (ha : orderOf a = 7) {W W' : Subgroup R} (hW : Nat.card W = 4) (hW' : Nat.card W' = 4) :
    ∃ g ∈ Subgroup.zpowers a, W.map g.toMonoidHom = W' := by
  obtain ⟨u, huW, hu1, hauW⟩ := exists_mem_ne_one_apply_mem hR a hW
  obtain ⟨u', huW', hu1', hauW'⟩ := exists_mem_ne_one_apply_mem hR a hW'
  obtain ⟨g, hg, hgu⟩ := CFSG.GH74.Generic.S45.exists_zpowers_apply_eq hR ha hu1 hu1'
  have hcomm : g * a = a * g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.self_zpow a k).symm.eq
  have hgau : g (a u) = a u' := by
    have := congrArg (fun m : MulAut R => m u) hcomm
    simpa [MulAut.mul_apply, hgu] using this
  refine ⟨g, hg, ?_⟩
  have hle : W.map g.toMonoidHom ≤ W' := by
    rintro _ ⟨w, hw, rfl⟩
    rcases eq_four_of_mem hR hsq ha hW huW hu1 hauW w hw with h | h | h | h
    · rw [h]; simp
    · rw [h]
      show g u ∈ W'
      rw [hgu]; exact huW'
    · rw [h]
      show g (a u) ∈ W'
      rw [hgau]; exact hauW'
    · rw [h]
      show g (u * a u) ∈ W'
      rw [map_mul, hgu, hgau]; exact W'.mul_mem huW' hauW'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective g.injective, hW, hW']

end Hyp7

theorem exists_conj_four_of_sylow {T : Type} [Group T] [Finite T] (P : Sylow 2 T)
    (hP : CFSG.IsElementaryAbelian 2 ↥(P : Subgroup T)) (hP8 : Nat.card ↥(P : Subgroup T) = 8)
    (hconj : InvolConj T) {E E' : Subgroup T} (hE : E ≤ (P : Subgroup T))
    (hE' : E' ≤ (P : Subgroup T)) (hE4 : Nat.card E = 4) (hE'4 : Nat.card E' = 4) :
    ∃ n : T, E' = E.map (MulAut.conj n).toMonoidHom := by
  classical
  set R : Subgroup T := (P : Subgroup T) with hR
  obtain ⟨a, haA, ha7⟩ := exists_order_seven P hP hP8 hconj
  have hsq : ∀ x : R, x * x = 1 := by
    intro v
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 R) v
    simpa [pow_two] using this
  have hW : Nat.card (E.subgroupOf R) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv]; exact hE4
  have hW' : Nat.card (E'.subgroupOf R) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE').toEquiv]; exact hE'4
  obtain ⟨g, hg, hgW⟩ := exists_zpowers_map_eq hP8 hsq ha7 hW hW'
  obtain ⟨n, hn⟩ := (Subgroup.zpowers_le.2 haA) hg
  refine ⟨n.1, ?_⟩
  ext x
  constructor
  · intro hx
    have hxR : x ∈ R := hE' hx
    have hxW' : (⟨x, hxR⟩ : R) ∈ E'.subgroupOf R := hx
    rw [← hgW] at hxW'
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 hxW'
    refine Subgroup.mem_map.2 ⟨(w : T), hw, ?_⟩
    have := congrArg Subtype.val hwx
    rw [← hn] at this
    exact this
  · intro hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    have heR : e ∈ R := hE he
    have heW : (⟨e, heR⟩ : R) ∈ E.subgroupOf R := he
    have : g ⟨e, heR⟩ ∈ E'.subgroupOf R := by
      rw [← hgW]; exact Subgroup.mem_map_of_mem _ heW
    rw [← hn] at this
    exact this

theorem fourConj_of_data {Pr : ∀ (Kt : Type) [Group Kt], Prop}
    (h : ∀ (Kt : Type) [Group Kt] [Finite Kt], Pr Kt → HasE8Sylow Kt ∧ InvolConj Kt) :
    FourConj Pr := by
  intro Kt _ _ hPr E E' hEel hE4 hE'el hE'4
  obtain ⟨hex, hconj⟩ := h Kt hPr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 ↥E := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hE'p : IsPGroup 2 ↥E' := IsPGroup.of_card (n := 2) (by rw [hE'4]; norm_num)
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  obtain ⟨Q', hQ'⟩ := hE'p.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_map_conj Q' Q
  have hE''le : E'.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Kt) := by
    rw [hg]; exact Subgroup.map_mono hQ'
  have hE''4 : Nat.card ↥(E'.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE'4]
  obtain ⟨hQel, hQ8⟩ := hex.all Q
  obtain ⟨n, hn⟩ := exists_conj_four_of_sylow Q hQel hQ8 hconj hQ hE''le hE4 hE''4
  refine ⟨g⁻¹ * n, ?_⟩
  have h1 : E' = (E'.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Kt := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  rw [h1, hn, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

open CFSG.Blueprint CFSG.GH74.Generic.BProg in
theorem reeTitsModel_of_lieModel {T : Type} [Group T] {f : ℕ}
    (h : LieModel T .twistedG2 0 3 f) : ReeTitsModel T .twistedG2 3 f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.Walter.Ree.Model


theorem shape4_data {T : Type} [Group T] [Finite T] (h : QShape4 T) :
    HasE8Sylow T ∧ InvolConj T := by
  obtain ⟨f, hf⟩ := h
  have hR := reeTitsModel_of_lieModel hf
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  have : Finite ↥(ReeTag.G2.reeGamma K a) := Finite.of_equiv T e.toEquiv
  have hΓ : HasE8Sylow ↥(ReeTag.G2.reeGamma K a) := by
    obtain ⟨hE, hcard, P, hPS⟩ := smallRee_E8_sylow hK hw₀
    exact ⟨P, by rw [hPS]; exact hE, by rw [hPS]; exact hcard⟩
  have hcΓ : InvolConj ↥(ReeTag.G2.reeGamma K a) := by
    intro x y hx hy
    have hx' : orderOf (x : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hy' : orderOf (y : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    obtain ⟨g₁, hg₁, hg₁x⟩ := exists_conj_eq_smallReeH_of_orderOf hK hw₀ x.2 hx'
    obtain ⟨g₂, hg₂, hg₂y⟩ := exists_conj_eq_smallReeH_of_orderOf hK hw₀ y.2 hy'
    refine ⟨⟨g₂⁻¹ * g₁, mul_mem (inv_mem hg₂) hg₁⟩, Subtype.ext ?_⟩
    show g₂⁻¹ * g₁ * (x : ModGL ReeTag.G2.tag K) * (g₂⁻¹ * g₁)⁻¹ = (y : ModGL ReeTag.G2.tag K)
    calc g₂⁻¹ * g₁ * (x : ModGL ReeTag.G2.tag K) * (g₂⁻¹ * g₁)⁻¹
        = g₂⁻¹ * (g₁ * (x : ModGL ReeTag.G2.tag K) * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * (y : ModGL ReeTag.G2.tag K) * g₂⁻¹) * g₂ := by rw [hg₁x, hg₂y]
      _ = (y : ModGL ReeTag.G2.tag K) := by group
  exact ⟨hΓ.of_mulEquiv e.symm, hcΓ.of_mulEquiv e.symm⟩

end Ree

section J1

open CFSG.Walter CFSG.Walter.J1Props CFSG.Open

theorem shape5_data {T : Type} [Group T] [Finite T] (h : QShape5 T) :
    HasE8Sylow T ∧ InvolConj T := by
  obtain ⟨e0⟩ := h
  let e : walterJ1 ≃* T := walterJ1EquivNative.trans e0.symm
  have : Finite walterJ1 := Finite.of_equiv T e.symm.toEquiv
  let hj := jankoHyp
  have hc : InvolConj walterJ1 := by
    intro x y hx hy
    obtain ⟨g₁, hg₁⟩ := hj.exists_conj_eq_t hx
    obtain ⟨g₂, hg₂⟩ := hj.exists_conj_eq_t hy
    refine ⟨g₂⁻¹ * g₁, ?_⟩
    calc g₂⁻¹ * g₁ * x * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * x * g₁⁻¹) * g₂ := by group
      _ = y := by rw [hg₁, ← hg₂]; group
  have hS : HasE8Sylow walterJ1 := by
    have ht2 : IsPGroup 2 (zpowers hj.t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj.orderOf_t, pow_one])
    obtain ⟨S, hS⟩ := ht2.exists_le_sylow
    have htS : hj.t ∈ S := hS (mem_zpowers _)
    have hab : IsMulCommutative ↥(S : Subgroup walterJ1) := hj.abelian_sylow S
    refine ⟨S, { toIsMulCommutative := hab, exponent_dvd_p := ?_ }, hj.card_sylow S htS⟩
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun x => ?_)
    apply Subtype.ext
    simpa [pow_two] using hj.mul_self_of_mem_sylow S htS x.2
  exact ⟨hS.of_mulEquiv e, hc.of_mulEquiv e⟩

end J1

end FixFourS45

section Ree


theorem involFixFour_shape4 : InvolFixFour QShape4 :=
  FixFourS45.involFixFour_of_hasE8Sylow (fun _ _ _ h => (FixFourS45.shape4_data h).1)

end Ree

theorem involFixFour_shape5 : InvolFixFour QShape5 :=
  FixFourS45.involFixFour_of_hasE8Sylow (fun _ _ _ h => (FixFourS45.shape5_data h).1)

section Ree


theorem fourConj_shape4 : FourConj QShape4 :=
  FixFourS45.fourConj_of_data (fun _ _ _ h => FixFourS45.shape4_data h)

end Ree

theorem fourConj_shape5 : FourConj QShape5 :=
  FixFourS45.fourConj_of_data (fun _ _ _ h => FixFourS45.shape5_data h)

end CFSG.GH74.Generic.BProg.B2
