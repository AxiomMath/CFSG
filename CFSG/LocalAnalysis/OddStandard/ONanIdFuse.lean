module

public import CFSG.LocalAnalysis.OddStandard.ONanIdQ

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def InZTE (e : AlpE) : Prop := e = 1 ∨ e = zc ∨ e = gen 1 ^ 2 ∨ e = zc * gen 1 ^ 2

instance (e : AlpE) : Decidable (InZTE e) := inferInstanceAs (Decidable (_ ∨ _))

@[expose] def WEL : List AlpE :=
  [⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, ⟨0, 0, 2, 0⟩, ⟨0, 0, 0, 2⟩, ⟨0, 2, 2, 0⟩, ⟨0, 2, 0, 2⟩,
    ⟨0, 0, 2, 2⟩, ⟨0, 2, 2, 2⟩]

set_option maxRecDepth 100000 in
theorem inWE_iff_mem_WEL : ∀ e : AlpE, InWE e ↔ e ∈ WEL := by decide +kernel

@[expose] def sig0E (e : AlpE) : AlpE := ⟨0, e.v0 + e.v1, e.v1, e.v2⟩

@[expose] def sig1E (e : AlpE) : AlpE := ⟨0, e.v0, e.v2, e.v1⟩

set_option maxRecDepth 100000 in
theorem sig0E_W : ∀ e ∈ WEL, sig0E e ∈ WEL := by decide +kernel
set_option maxRecDepth 100000 in
theorem sig1E_W : ∀ e ∈ WEL, sig1E e ∈ WEL := by decide +kernel
set_option maxRecDepth 100000 in
theorem sig0E_invol : ∀ e ∈ WEL, sig0E (sig0E e) = e := by decide +kernel
set_option maxRecDepth 100000 in
theorem sig1E_invol : ∀ e ∈ WEL, sig1E (sig1E e) = e := by decide +kernel
set_option maxRecDepth 100000 in
theorem sig0E_mul : ∀ e ∈ WEL, ∀ f ∈ WEL, sig0E (e * f) = sig0E e * sig0E f := by decide +kernel
set_option maxRecDepth 100000 in
theorem sig1E_mul : ∀ e ∈ WEL, ∀ f ∈ WEL, sig1E (e * f) = sig1E e * sig1E f := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig0_conj : ∀ e ∈ WEL, sig0E (s2E * sig0E e * s2E⁻¹) = tE * e * tE⁻¹ := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig1_conj : ∀ e ∈ WEL, sig1E (stE * sig1E e * stE⁻¹) = s2E * e * s2E⁻¹ := by decide +kernel

set_option maxRecDepth 100000 in
theorem conj_W_mem : ∀ q ∈ [s2E, tE, stE], ∀ e ∈ WEL, q * e * q⁻¹ ∈ WEL := by decide +kernel

@[expose] def s2VWit : List (AlpE × AlpE) :=
  [(⟨2, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩), (⟨2, 0, 1, 0⟩, ⟨1, 0, 0, 1⟩), (⟨2, 0, 2, 3⟩, ⟨0, 0, 1, 3⟩),
    (⟨2, 0, 3, 2⟩, ⟨1, 0, 1, 2⟩), (⟨2, 1, 0, 0⟩, ⟨0, 0, 0, 1⟩), (⟨2, 1, 1, 3⟩, ⟨1, 0, 1, 1⟩),
    (⟨2, 1, 2, 2⟩, ⟨0, 0, 1, 0⟩), (⟨2, 1, 3, 1⟩, ⟨1, 0, 0, 0⟩), (⟨2, 2, 0, 3⟩, ⟨0, 0, 0, 2⟩),
    (⟨2, 2, 1, 2⟩, ⟨1, 0, 0, 3⟩), (⟨2, 2, 2, 1⟩, ⟨0, 0, 1, 1⟩), (⟨2, 2, 3, 0⟩, ⟨1, 0, 1, 0⟩),
    (⟨2, 3, 0, 2⟩, ⟨0, 0, 0, 3⟩), (⟨2, 3, 1, 1⟩, ⟨1, 0, 1, 3⟩), (⟨2, 3, 2, 0⟩, ⟨0, 0, 1, 2⟩),
    (⟨2, 3, 3, 3⟩, ⟨1, 0, 0, 2⟩)]

@[expose] def y2E : AlpE := ⟨2, 0, 0, 1⟩

set_option maxRecDepth 100000 in
theorem s2V_conj : ∀ y : AlpE, y.d = 2 → y ^ 4 = 1 → y * y ≠ 1 →
    ((s2VWit.lookup y).getD 1) * y * ((s2VWit.lookup y).getD 1)⁻¹ = y2E := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem order_four_cosets : ∀ y : AlpE, y.d ≠ 0 → y ^ 4 = 1 → y * y ≠ 1 →
    y.d = 2 ∨ y.d = 4 ∨ y.d = 5 ∨ y.d = 6 ∨ y.d = 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s_conj_cosets : ∀ y : AlpE, (y.d = 6 → ((gen 3)⁻¹ * y * gen 3).d = 4) ∧
    (y.d = 7 → ((gen 3)⁻¹ * y * gen 3).d = 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s2_central_mod_V : ∀ y : AlpE, (s2E⁻¹ * (y * s2E * y⁻¹)).d = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem d_of_s2V : ∀ y : AlpE, (s2E⁻¹ * y).d = 0 → y.d = 2 := by decide +kernel

theorem coset_d : ∀ y : AlpE, (y.d = 2 → (s2E⁻¹ * y).d = 0) ∧ (y.d = 4 → (tE⁻¹ * y).d = 0) ∧
    (y.d = 5 → (stE⁻¹ * y).d = 0) := by
  intro y
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [AlpE.mul_def, AlpE.mul, AlpE.inv_def, AlpE.inv, h] <;> decide

section CentMod

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) := by
  intro n hn
  have key : ∀ m : G, m ∈ normalizer (V : Set G) → ∀ c : G, c ∈ centralizer (V : Set G) →
      m * c * m⁻¹ ∈ centralizer (V : Set G) := by
    intro m hm c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem hm) v).1 hv
      rwa [inv_inv] at this
    have h := hc _ hv'
    calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [h]
      _ = m * c * m⁻¹ * v := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key n hn c, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this

@[expose] def centMod (V : Subgroup G) (g : G) : Subgroup G where
  carrier := {n | n ∈ normalizer (V : Set G) ∧ g⁻¹ * (n * g * n⁻¹) ∈ centralizer (V : Set G)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h1 : a * (g⁻¹ * (b * g * b⁻¹)) * a⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V ha) _).1 hb'
    have e : g⁻¹ * (a * b * g * (a * b)⁻¹) =
        (g⁻¹ * (a * g * a⁻¹)) * (a * (g⁻¹ * (b * g * b⁻¹)) * a⁻¹) := by group
    rw [e]
    exact mul_mem ha' h1
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h1 : a⁻¹ * (g⁻¹ * (a * g * a⁻¹))⁻¹ * a⁻¹⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (inv_mem ha)) _).1
        (inv_mem ha')
    have e : g⁻¹ * (a⁻¹ * g * a⁻¹⁻¹) = a⁻¹ * (g⁻¹ * (a * g * a⁻¹))⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

end CentMod

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

@[expose] def ActsAs (n : G) (f : AlpE → AlpE) : Prop :=
  ∀ e ∈ WEL, n * D.E.φ e * n⁻¹ = D.E.φ (f e)

theorem mem_W_phi_iff (e : AlpE) : D.E.φ e ∈ alpW v1 v2 v3 ↔ e ∈ WEL := by
  rw [D.mem_W_phi, inWE_iff_mem_WEL]

theorem exists_phi_WEL {w : G} (hw : w ∈ alpW v1 v2 v3) : ∃ e ∈ WEL, D.E.φ e = w := by
  obtain ⟨e, he, rfl⟩ := D.exists_phi_of_mem_W hw
  exact ⟨e, (inWE_iff_mem_WEL e).1 he, rfl⟩

theorem inv_mul_mem_centralizer_W_of_actsAs {n m : G} {f : AlpE → AlpE} (hn : D.ActsAs n f)
    (hm : D.ActsAs m f) : n⁻¹ * m ∈ centralizer (alpW v1 v2 v3 : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨e, he, rfl⟩ := D.exists_phi_WEL hw
  have h1 := hn e he
  have h2 := hm e he
  have h3 : n * D.E.φ e * n⁻¹ = m * D.E.φ e * m⁻¹ := by rw [h1, h2]
  calc D.E.φ e * (n⁻¹ * m) = n⁻¹ * (n * D.E.φ e * n⁻¹) * m := by group
    _ = n⁻¹ * (m * D.E.φ e * m⁻¹) * m := by rw [h3]
    _ = n⁻¹ * m * D.E.φ e := by group

noncomputable def wAut (f : AlpE → AlpE) (hW : ∀ e ∈ WEL, f e ∈ WEL)
    (hinv : ∀ e ∈ WEL, f (f e) = e) (hmul : ∀ e ∈ WEL, ∀ e' ∈ WEL, f (e * e') = f e * f e') :
    MulAut (alpW v1 v2 v3) :=
  have pre : ∀ w : alpW v1 v2 v3, ∃ e ∈ WEL, D.E.φ e = w := fun w => D.exists_phi_WEL w.2
  let g : alpW v1 v2 v3 → alpW v1 v2 v3 := fun w =>
    ⟨D.E.φ (f (pre w).choose), (D.mem_W_phi_iff _).2 (hW _ (pre w).choose_spec.1)⟩
  have hg : ∀ w : alpW v1 v2 v3, ∀ e ∈ WEL, D.E.φ e = w → (g w : G) = D.E.φ (f e) := by
    intro w e he hew
    have h1 := (pre w).choose_spec.2
    have h2 : (pre w).choose = e := D.E.inj (by rw [h1, hew])
    show D.E.φ (f (pre w).choose) = _
    rw [h2]
  have hgg : ∀ w, g (g w) = w := by
    intro w
    obtain ⟨e, he, hew⟩ := pre w
    apply Subtype.ext
    rw [hg (g w) (f e) (hW e he) (hg w e he hew).symm, hinv e he, hew]
  { toFun := g
    invFun := g
    left_inv := hgg
    right_inv := hgg
    map_mul' := by
      intro w w'
      obtain ⟨e, he, hew⟩ := pre w
      obtain ⟨e', he', hew'⟩ := pre w'
      have hee' : e * e' ∈ WEL := by
        rw [← D.mem_W_phi_iff, map_mul, hew, hew']
        exact (w * w').2
      apply Subtype.ext
      rw [Subgroup.coe_mul, hg (w * w') (e * e') hee' (by rw [map_mul, hew, hew']; rfl),
        hg w e he hew, hg w' e' he' hew', hmul e he e' he', map_mul] }

theorem wAut_apply (f : AlpE → AlpE) (hW : ∀ e ∈ WEL, f e ∈ WEL)
    (hinv : ∀ e ∈ WEL, f (f e) = e) (hmul : ∀ e ∈ WEL, ∀ e' ∈ WEL, f (e * e') = f e * f e')
    (e : AlpE) (he : e ∈ WEL) :
    ((D.wAut f hW hinv hmul ⟨D.E.φ e, (D.mem_W_phi_iff e).2 he⟩ : alpW v1 v2 v3) : G) =
      D.E.φ (f e) := by
  have h1 := (D.exists_phi_WEL ((D.mem_W_phi_iff e).2 he)).choose_spec.2
  have h2 := D.E.inj h1
  show D.E.φ (f (D.exists_phi_WEL ((D.mem_W_phi_iff e).2 he)).choose) = D.E.φ (f e)
  rw [h2]

theorem normalizerMonoidHom_W_surjective :
    Function.Surjective (alpW v1 v2 v3).normalizerMonoidHom := by
  have hAB := D.fus_AB
  have hAC := D.fus_AC hAB
  have hcard := D.card_normalizer_W fun _ hw hw1 => D.transitive_W hAB hAC hw hw1
  have hle : centralizer (alpW v1 v2 v3 : Set G) ≤ normalizer (alpW v1 v2 v3 : Set G) :=
    centralizer_le_normalizer _
  have hidx : ((alpW v1 v2 v3).normalizerMonoidHom.ker).index = 168 := by
    rw [normalizerMonoidHom_ker]
    have h := ((centralizer (alpW v1 v2 v3 : Set G)).subgroupOf
      (normalizer (alpW v1 v2 v3 : Set G))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hcard] at h
    have hpos : 0 < Nat.card (centralizer (alpW v1 v2 v3 : Set G)) := Nat.card_pos
    nlinarith
  have hrange : Nat.card (alpW v1 v2 v3).normalizerMonoidHom.range = 168 := by
    rw [← index_ker, hidx]
  obtain ⟨e⟩ := nonempty_mulAut_equiv_GL32 D.isElemAbelian_W (AlpEmb.card_alpW D.E D.hF)
  have hAut : Nat.card (MulAut (alpW v1 v2 v3)) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_GL32_gh]
  have htop : (alpW v1 v2 v3).normalizerMonoidHom.range = ⊤ :=
    eq_top_of_card_eq _ (hrange.trans hAut.symm)
  exact MonoidHom.range_eq_top.1 htop

theorem isSylowOf_V_centralizer_W :
    IsSylowOf 2 (alpV v1 v2 v3) (centralizer (alpW v1 v2 v3 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 (alpP v1 v2 v3 s t) (normalizer (alpW v1 v2 v3 : Set G)) :=
    D.isSylowOf_P.of_le D.P_le_normalizer_W le_top
  have hN : normalizer (alpW v1 v2 v3 : Set G) ≤
      normalizer (centralizer (alpW v1 v2 v3 : Set G) : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro c
    exact ⟨fun hc => conj_mem_centralizer_W hn hc, fun hc => by
      have := conj_mem_centralizer_W (inv_mem hn) hc
      rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this⟩
  have h := hS.inf_of_le_normalizer (centralizer_le_normalizer _) hN
  rwa [D.P_inf_centralizer_W] at h

theorem exists_normalizer_V_of_W {m : G} (hm : m ∈ normalizer (alpW v1 v2 v3 : Set G)) :
    ∃ c ∈ centralizer (alpW v1 v2 v3 : Set G), c * m ∈ normalizer (alpV v1 v2 v3 : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := (alpV v1 v2 v3).map (MulAut.conj m).toMonoidHom with hR
  have hRle : R ≤ centralizer (alpW v1 v2 v3 : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    exact conj_mem_centralizer_W hm (D.V_le_centralizer_W hv)
  have hRp : IsPGroup 2 R := (D.isPGroup_P.to_le D.V_le_P).map _
  obtain ⟨c, hc, hcR⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_V_centralizer_W hRle hRp
  refine ⟨c, hc, ?_⟩
  have hle : ∀ v ∈ alpV v1 v2 v3, (c * m) * v * (c * m)⁻¹ ∈ alpV v1 v2 v3 := by
    intro v hv
    have := hcR (m * v * m⁻¹) ⟨v, hv, rfl⟩
    rwa [show c * (m * v * m⁻¹) * c⁻¹ = (c * m) * v * (c * m)⁻¹ by group] at this
  set V' := (alpV v1 v2 v3).map (MulAut.conj (c * m)).toMonoidHom with hV'
  have hV'le : V' ≤ alpV v1 v2 v3 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hle v hv
  have heq : V' = alpV v1 v2 v3 := eq_of_le_of_card_ge hV'le (by
    rw [hV', card_map_of_injective (MulAut.conj (c * m)).injective])
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hle v hv, fun hv => ?_⟩
  rw [← heq] at hv
  obtain ⟨u, hu, hu'⟩ := hv
  have e : u = v := by
    have := congrArg (fun y => (c * m)⁻¹ * y * (c * m)) hu'
    simpa [MulAut.conj_apply, mul_assoc] using this
  rw [← e]
  exact hu

theorem exists_normalizer_V_actsAs (f : AlpE → AlpE) (hW : ∀ e ∈ WEL, f e ∈ WEL)
    (hinv : ∀ e ∈ WEL, f (f e) = e) (hmul : ∀ e ∈ WEL, ∀ e' ∈ WEL, f (e * e') = f e * f e') :
    ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G), D.ActsAs n f := by
  obtain ⟨⟨m, hm⟩, hmσ⟩ := D.normalizerMonoidHom_W_surjective (D.wAut f hW hinv hmul)
  obtain ⟨c, hc, hcm⟩ := D.exists_normalizer_V_of_W hm
  refine ⟨c * m, hcm, fun e he => ?_⟩
  have h1 : m * D.E.φ e * m⁻¹ = D.E.φ (f e) := by
    have := congrArg (fun φ : MulAut (alpW v1 v2 v3) =>
      ((φ ⟨D.E.φ e, (D.mem_W_phi_iff e).2 he⟩ : alpW v1 v2 v3) : G)) hmσ
    rw [D.wAut_apply f hW hinv hmul e he] at this
    rw [← this]
    rfl
  have hcW := mem_centralizer_iff.1 hc
  have h2 : c * D.E.φ (f e) * c⁻¹ = D.E.φ (f e) := by
    rw [← hcW _ ((D.mem_W_phi_iff _).2 (hW e he)), mul_inv_cancel_right]
  calc c * m * D.E.φ e * (c * m)⁻¹ = c * (m * D.E.φ e * m⁻¹) * c⁻¹ := by group
    _ = D.E.φ (f e) := by rw [h1, h2]

theorem actsAs_phi (q : AlpE) : D.ActsAs (D.E.φ q) (fun e => q * e * q⁻¹) := by
  intro e _
  simp only [map_mul, map_inv]

theorem exists_s2_of_t : ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G),
    (s ^ 2)⁻¹ * (n⁻¹ * t * n) ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  obtain ⟨n, hn, hact⟩ := D.exists_normalizer_V_actsAs sig0E sig0E_W sig0E_invol sig0E_mul
  refine ⟨n, hn, ?_⟩
  have hs2 := D.actsAs_phi s2E
  have ht := D.actsAs_phi tE
  rw [D.phi_s2] at hs2
  rw [D.phi_t] at ht
  have hninv : ∀ e ∈ WEL, n⁻¹ * D.E.φ e * n = D.E.φ (sig0E e) := by
    intro e he
    have h1 := hact (sig0E e) (sig0E_W e he)
    rw [sig0E_invol e he] at h1
    calc n⁻¹ * D.E.φ e * n = n⁻¹ * (n * D.E.φ (sig0E e) * n⁻¹) * n := by rw [h1]
      _ = D.E.φ (sig0E e) := by group
  have hconj : D.ActsAs (n * s ^ 2 * n⁻¹) (fun e => tE * e * tE⁻¹) := by
    intro e he
    have hw1 := sig0E_W e he
    have hw2 : s2E * sig0E e * s2E⁻¹ ∈ WEL := conj_W_mem s2E (by simp) _ hw1
    calc n * s ^ 2 * n⁻¹ * D.E.φ e * (n * s ^ 2 * n⁻¹)⁻¹ =
        n * (s ^ 2 * (n⁻¹ * D.E.φ e * n) * (s ^ 2)⁻¹) * n⁻¹ := by group
      _ = n * D.E.φ (s2E * sig0E e * s2E⁻¹) * n⁻¹ := by rw [hninv e he, hs2 _ hw1]
      _ = D.E.φ (sig0E (s2E * sig0E e * s2E⁻¹)) := hact _ hw2
      _ = D.E.φ (tE * e * tE⁻¹) := by rw [sig0_conj e he]
  have hC := D.inv_mul_mem_centralizer_W_of_actsAs hconj ht
  have hNV : (n * s ^ 2 * n⁻¹)⁻¹ * t ∈ normalizer (alpV v1 v2 v3 : Set G) :=
    mul_mem (inv_mem (mul_mem (mul_mem hn D.s2_mem_N) (inv_mem hn))) D.t_mem_N
  have hCV := D.mem_centralizer_V_of_W hNV hC
  have hconjV : n⁻¹ * ((n * s ^ 2 * n⁻¹)⁻¹ * t) * n⁻¹⁻¹ ∈
      centralizer (alpV v1 v2 v3 : Set G) :=
    normalizer_V_le_normalizer_centralizer (inv_mem hn) |> fun h =>
      (mem_normalizer_iff.1 h _).1 hCV
  rwa [show n⁻¹ * ((n * s ^ 2 * n⁻¹)⁻¹ * t) * n⁻¹⁻¹ = (s ^ 2)⁻¹ * (n⁻¹ * t * n) by group]
    at hconjV

theorem st_mem_N : s * t ∈ normalizer (alpV v1 v2 v3 : Set G) :=
  D.P_le_normalizer_V (mul_mem s_mem_P t_mem_P)

theorem exists_s2_of_st : ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G),
    (s ^ 2)⁻¹ * (n * (s * t) * n⁻¹) ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  obtain ⟨n, hn, hact⟩ := D.exists_normalizer_V_actsAs sig1E sig1E_W sig1E_invol sig1E_mul
  refine ⟨n, hn, ?_⟩
  have hs2 := D.actsAs_phi s2E
  have hst := D.actsAs_phi stE
  rw [D.phi_s2] at hs2
  rw [AlpEmb.φ_stE D.E] at hst
  have hninv : ∀ e ∈ WEL, n⁻¹ * D.E.φ e * n = D.E.φ (sig1E e) := by
    intro e he
    have h1 := hact (sig1E e) (sig1E_W e he)
    rw [sig1E_invol e he] at h1
    calc n⁻¹ * D.E.φ e * n = n⁻¹ * (n * D.E.φ (sig1E e) * n⁻¹) * n := by rw [h1]
      _ = D.E.φ (sig1E e) := by group
  have hconj : D.ActsAs (n * (s * t) * n⁻¹) (fun e => s2E * e * s2E⁻¹) := by
    intro e he
    have hw1 := sig1E_W e he
    have hw2 : stE * sig1E e * stE⁻¹ ∈ WEL := conj_W_mem stE (by simp) _ hw1
    calc n * (s * t) * n⁻¹ * D.E.φ e * (n * (s * t) * n⁻¹)⁻¹ =
        n * ((s * t) * (n⁻¹ * D.E.φ e * n) * (s * t)⁻¹) * n⁻¹ := by group
      _ = n * D.E.φ (stE * sig1E e * stE⁻¹) * n⁻¹ := by rw [hninv e he, hst _ hw1]
      _ = D.E.φ (sig1E (stE * sig1E e * stE⁻¹)) := hact _ hw2
      _ = D.E.φ (s2E * e * s2E⁻¹) := by rw [sig1_conj e he]
  have hC := D.inv_mul_mem_centralizer_W_of_actsAs hs2 hconj
  have hNV : (s ^ 2)⁻¹ * (n * (s * t) * n⁻¹) ∈ normalizer (alpV v1 v2 v3 : Set G) :=
    mul_mem (inv_mem D.s2_mem_N) (mul_mem (mul_mem hn D.st_mem_N) (inv_mem hn))
  exact D.mem_centralizer_V_of_W hNV hC

theorem P_le_centMod : alpP v1 v2 v3 s t ≤ centMod (alpV v1 v2 v3) (s ^ 2) := by
  intro p hp
  refine ⟨D.P_le_normalizer_V hp, ?_⟩
  obtain ⟨y, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hp
  have h := s2_central_mod_V y
  have e : (s ^ 2)⁻¹ * (D.E.φ y * s ^ 2 * (D.E.φ y)⁻¹) =
      D.E.φ (s2E⁻¹ * (y * s2E * y⁻¹)) := by
    rw [← D.phi_s2]
    simp only [map_mul, map_inv]
  rw [e]
  apply D.V_le_centralizer_V
  rw [AlpEmb.alpV_eq_map D.E]
  exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 h)

theorem exists_conj_mem_s2V {u : G} (hu : u ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hus : (s ^ 2)⁻¹ * u ∈ centralizer (alpV v1 v2 v3 : Set G)) (hu4 : u ^ 4 = 1) :
    ∃ m : G, (s ^ 2)⁻¹ * (m * u * m⁻¹) ∈ alpV v1 v2 v3 ∧ m * u * m⁻¹ ∈ alpP v1 v2 v3 s t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := (s ^ 2)⁻¹ * u with hc
  have hue : u = s ^ 2 * c := by rw [hc]; group
  have hN := normalizer_le_normalizer_centralizer (alpV v1 v2 v3)
  have huM : u ∈ centMod (alpV v1 v2 v3) (s ^ 2) := by
    refine ⟨hu, ?_⟩
    have h1 : s ^ 2 * c⁻¹ * (s ^ 2)⁻¹ ∈ centralizer (alpV v1 v2 v3 : Set G) :=
      (mem_normalizer_iff.1 (hN D.s2_mem_N) _).1 (inv_mem hus)
    have e : (s ^ 2)⁻¹ * (u * s ^ 2 * u⁻¹) = c * (s ^ 2 * c⁻¹ * (s ^ 2)⁻¹) := by
      rw [hue]; group
    rw [e]
    exact mul_mem hus h1
  have hpg : IsPGroup 2 (zpowers u) := by
    have hd : orderOf u ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hu4)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hS : IsSylowOf 2 (alpP v1 v2 v3 s t) (centMod (alpV v1 v2 v3) (s ^ 2)) :=
    D.isSylowOf_P.of_le D.P_le_centMod le_top
  obtain ⟨m, hm, hmu⟩ := exists_conj_le_of_isSylowOf hS
    ((zpowers_le).2 huM) hpg
  have hmuP := hmu u (mem_zpowers u)
  refine ⟨m, ?_, hmuP⟩
  have h1 : (s ^ 2)⁻¹ * (m * s ^ 2 * m⁻¹) ∈ centralizer (alpV v1 v2 v3 : Set G) := hm.2
  have h2 : m * c * m⁻¹ ∈ centralizer (alpV v1 v2 v3 : Set G) :=
    (mem_normalizer_iff.1 (hN hm.1) _).1 hus
  have e : (s ^ 2)⁻¹ * (m * u * m⁻¹) = (s ^ 2)⁻¹ * (m * s ^ 2 * m⁻¹) * (m * c * m⁻¹) := by
    rw [hue]; group
  have hCV : (s ^ 2)⁻¹ * (m * u * m⁻¹) ∈ centralizer (alpV v1 v2 v3 : Set G) := by
    rw [e]; exact mul_mem h1 h2
  have hP : (s ^ 2)⁻¹ * (m * u * m⁻¹) ∈ alpP v1 v2 v3 s t :=
    mul_mem (inv_mem (pow_mem s_mem_P 2)) hmuP
  have h3 : (s ^ 2)⁻¹ * (m * u * m⁻¹) ∈ alpP v1 v2 v3 s t ⊓ centralizer (alpV v1 v2 v3 : Set G) :=
    ⟨hP, hCV⟩
  rwa [AlpEmb.centralizer_alpV D.E D.hF] at h3

theorem conj_y2_of_s2V {y : G} (hy : (s ^ 2)⁻¹ * y ∈ alpV v1 v2 v3) (hy4 : y ^ 4 = 1)
    (hy2 : y * y ≠ 1) : ∃ g : G, g * y * g⁻¹ = D.E.φ y2E := by
  have hyP : y ∈ alpP v1 v2 v3 s t := by
    have := mul_mem (pow_mem s_mem_P 2) (D.V_le_P hy)
    rwa [mul_inv_cancel_left] at this
  obtain ⟨e, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hyP
  have hd : e.d = 2 := by
    apply d_of_s2V
    rw [← D.phi_s2, ← map_inv, ← map_mul, AlpEmb.alpV_eq_map D.E,
      Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub] at hy
    exact hy
  have he4 : e ^ 4 = 1 := D.E.inj (by rw [map_pow, hy4, map_one])
  have he2 : e * e ≠ 1 := fun h => hy2 (by rw [← map_mul, h, map_one])
  refine ⟨D.E.φ ((s2VWit.lookup e).getD 1), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, s2V_conj e hd he4 he2]

theorem conj_s_phi (e : AlpE) : s⁻¹ * D.E.φ e * s = D.E.φ ((gen 3)⁻¹ * e * gen 3) := by
  rw [map_mul, map_mul, map_inv, AlpEmb.φ_s]

theorem conj_y2_of_order_four {y : G} (hyP : y ∈ alpP v1 v2 v3 s t) (hyV : y ∉ alpV v1 v2 v3)
    (hy4 : y ^ 4 = 1) (hy2 : y * y ≠ 1) : ∃ g : G, g * y * g⁻¹ = D.E.φ y2E := by
  have key : ∀ u : G, u ∈ normalizer (alpV v1 v2 v3 : Set G) →
      (s ^ 2)⁻¹ * u ∈ centralizer (alpV v1 v2 v3 : Set G) → u ^ 4 = 1 → u * u ≠ 1 →
      ∃ g : G, g * u * g⁻¹ = D.E.φ y2E := by
    intro u hu hus hu4 hu2
    obtain ⟨m, hm, -⟩ := D.exists_conj_mem_s2V hu hus hu4
    have hm4 : (m * u * m⁻¹) ^ 4 = 1 := by rw [conj_pow, hu4]; group
    have hm2 : m * u * m⁻¹ * (m * u * m⁻¹) ≠ 1 := by
      intro h
      apply hu2
      calc u * u = m⁻¹ * (m * u * m⁻¹ * (m * u * m⁻¹)) * m := by group
        _ = 1 := by rw [h]; group
    obtain ⟨g, hg⟩ := D.conj_y2_of_s2V hm hm4 hm2
    exact ⟨g * m, by rw [← hg]; group⟩
  obtain ⟨e, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hyP
  have hd0 : e.d ≠ 0 := fun h => hyV (by
    rw [AlpEmb.alpV_eq_map D.E]
    exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 h))
  have he4 : e ^ 4 = 1 := D.E.inj (by rw [map_pow, hy4, map_one])
  have he2 : e * e ≠ 1 := fun h => hy2 (by rw [← map_mul, h, map_one])
  have hN : ∀ q : AlpE, D.E.φ q ∈ normalizer (alpV v1 v2 v3 : Set G) := fun q =>
    D.P_le_normalizer_V (AlpEmb.φ_mem D.E q)
  have hVphi : ∀ q : AlpE, q.d = 0 → D.E.φ q ∈ alpV v1 v2 v3 := fun q hq => by
    rw [AlpEmb.alpV_eq_map D.E]
    exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 hq)
  have case4 : ∀ f : AlpE, f.d = 4 → f ^ 4 = 1 → f * f ≠ 1 →
      ∃ g : G, g * D.E.φ f * g⁻¹ = D.E.φ y2E := by
    intro f hf hf4 hf2
    obtain ⟨n, hn, hnt⟩ := D.exists_s2_of_t
    have hv := hVphi _ ((coset_d f).2.1 hf)
    set v := D.E.φ (tE⁻¹ * f) with hvdef
    have hfe : D.E.φ f = t * v := by
      calc D.E.φ f = D.E.φ tE * D.E.φ (tE⁻¹ * f) := by rw [← map_mul, mul_inv_cancel_left]
        _ = t * v := by rw [D.phi_t]
    set u := n⁻¹ * D.E.φ f * n with hu
    have hus : (s ^ 2)⁻¹ * u ∈ centralizer (alpV v1 v2 v3 : Set G) := by
      have e : (s ^ 2)⁻¹ * u = (s ^ 2)⁻¹ * (n⁻¹ * t * n) * (n⁻¹ * v * n) := by
        rw [hu, hfe]; group
      rw [e]
      refine mul_mem hnt (D.V_le_centralizer_V ?_)
      have := conj_mem_V (inv_mem hn) hv
      rwa [inv_inv] at this
    have huN : u ∈ normalizer (alpV v1 v2 v3 : Set G) :=
      mul_mem (mul_mem (inv_mem hn) (hN f)) hn
    have hu4 : u ^ 4 = 1 := by
      rw [hu, show n⁻¹ * D.E.φ f * n = n⁻¹ * D.E.φ f * n⁻¹⁻¹ by rw [inv_inv], conj_pow,
        ← map_pow, hf4, map_one]; group
    have hu2 : u * u ≠ 1 := by
      intro h
      apply hf2
      apply D.E.inj
      rw [map_mul, map_one]
      calc D.E.φ f * D.E.φ f = n * (u * u) * n⁻¹ := by rw [hu]; group
        _ = 1 := by rw [h]; group
    obtain ⟨g, hg⟩ := key u huN hus hu4 hu2
    exact ⟨g * n⁻¹, by rw [← hg, hu]; group⟩
  have case5 : ∀ f : AlpE, f.d = 5 → f ^ 4 = 1 → f * f ≠ 1 →
      ∃ g : G, g * D.E.φ f * g⁻¹ = D.E.φ y2E := by
    intro f hf hf4 hf2
    obtain ⟨n, hn, hnst⟩ := D.exists_s2_of_st
    have hv := hVphi _ ((coset_d f).2.2 hf)
    set v := D.E.φ (stE⁻¹ * f) with hvdef
    have hfe : D.E.φ f = s * t * v := by
      calc D.E.φ f = D.E.φ stE * D.E.φ (stE⁻¹ * f) := by rw [← map_mul, mul_inv_cancel_left]
        _ = s * t * v := by rw [AlpEmb.φ_stE D.E]
    set u := n * D.E.φ f * n⁻¹ with hu
    have hus : (s ^ 2)⁻¹ * u ∈ centralizer (alpV v1 v2 v3 : Set G) := by
      have e : (s ^ 2)⁻¹ * u = (s ^ 2)⁻¹ * (n * (s * t) * n⁻¹) * (n * v * n⁻¹) := by
        rw [hu, hfe]; group
      rw [e]
      exact mul_mem hnst (D.V_le_centralizer_V (conj_mem_V hn hv))
    have huN : u ∈ normalizer (alpV v1 v2 v3 : Set G) :=
      mul_mem (mul_mem hn (hN f)) (inv_mem hn)
    have hu4 : u ^ 4 = 1 := by rw [hu, conj_pow, ← map_pow, hf4, map_one]; group
    have hu2 : u * u ≠ 1 := by
      intro h
      apply hf2
      apply D.E.inj
      rw [map_mul, map_one]
      calc D.E.φ f * D.E.φ f = n⁻¹ * (u * u) * n := by rw [hu]; group
        _ = 1 := by rw [h]; group
    obtain ⟨g, hg⟩ := key u huN hus hu4 hu2
    exact ⟨g * n, by rw [← hg, hu]; group⟩
  have hconj : ∀ f : AlpE, (∃ g : G, g * D.E.φ ((gen 3)⁻¹ * f * gen 3) * g⁻¹ = D.E.φ y2E) →
      ∃ g : G, g * D.E.φ f * g⁻¹ = D.E.φ y2E := by
    rintro f ⟨g, hg⟩
    refine ⟨g * s⁻¹, ?_⟩
    rw [← hg, ← D.conj_s_phi]
    group
  have hpow : ∀ f : AlpE, f ^ 4 = 1 → ((gen 3)⁻¹ * f * gen 3) ^ 4 = 1 := fun f hf => by
    rw [show (gen 3)⁻¹ * f * gen 3 = (gen 3)⁻¹ * f * (gen 3)⁻¹⁻¹ by rw [inv_inv], conj_pow, hf]
    group
  have hsq : ∀ f : AlpE, f * f ≠ 1 → (gen 3)⁻¹ * f * gen 3 * ((gen 3)⁻¹ * f * gen 3) ≠ 1 :=
    fun f hf h => hf (by
      calc f * f = gen 3 * ((gen 3)⁻¹ * f * gen 3 * ((gen 3)⁻¹ * f * gen 3)) * (gen 3)⁻¹ := by
            group
        _ = 1 := by rw [h]; group)
  rcases order_four_cosets e hd0 he4 he2 with h | h | h | h | h
  ·
    refine D.conj_y2_of_s2V ?_ hy4 hy2
    rw [← D.phi_s2, ← map_inv, ← map_mul]
    exact hVphi _ ((coset_d e).1 h)
  · exact case4 e h he4 he2
  · exact case5 e h he4 he2
  · exact hconj e (case4 _ ((s_conj_cosets e).1 h) (hpow e he4) (hsq e he2))
  · exact hconj e (case5 _ ((s_conj_cosets e).2 h) (hpow e he4) (hsq e he2))

theorem isConj_order_four {y y' : G} (hyP : y ∈ alpP v1 v2 v3 s t) (hyV : y ∉ alpV v1 v2 v3)
    (hy4 : y ^ 4 = 1) (hy2 : y * y ≠ 1) (hyP' : y' ∈ alpP v1 v2 v3 s t)
    (hyV' : y' ∉ alpV v1 v2 v3) (hy4' : y' ^ 4 = 1) (hy2' : y' * y' ≠ 1) :
    ∃ g : G, g * y * g⁻¹ = y' := by
  obtain ⟨g, hg⟩ := D.conj_y2_of_order_four hyP hyV hy4 hy2
  obtain ⟨g', hg'⟩ := D.conj_y2_of_order_four hyP' hyV' hy4' hy2'
  refine ⟨g'⁻¹ * g, ?_⟩
  calc g'⁻¹ * g * y * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * y * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * y' * g'⁻¹) * g' := by rw [hg, hg']
    _ = y' := by group

end FusCtx

end CFSG.OddStandard.ONanRec
