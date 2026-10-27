module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModFix

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

section Pow

variable {F : Type} [Field F]

theorem upperSL_pow (t : F) (k : ℕ) : upperSL t ^ k = upperSL ((k : F) * t) := by
  induction k with
  | zero => simp [upperSL_zero]
  | succ k ih =>
    rw [pow_succ, ih, upperSL_add]
    congr 1
    push_cast
    ring

theorem upperSL_pow_prime [Finite F] {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) (t : F) :
    upperSL t ^ p = 1 := by
  have : CharP F p := charP_of_natCard_eq hp hF
  rw [upperSL_pow, CharP.cast_eq_zero, zero_mul, upperSL_zero]

end Pow

section Semi

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

theorem mem_of_mem_normalizer (hp : p.Prime) (hF : Nat.card F = p ^ n) {P : Subgroup (SL2 F)}
    (hP : Nat.card P = Nat.card F) {x : SL2 F} (hx : x ∈ normalizer (P : Set (SL2 F)))
    (hxp : x ^ p = 1) : x ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hsyl := isPGroup_and_index_of_card_eq hp hF hP
  let Q : Sylow p (SL2 F) := hsyl.1.toSylow hsyl.2
  have hpg : IsPGroup p (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have h1 := hpg.inf_normalizer_sylow Q
  have hxm : x ∈ Subgroup.zpowers x ⊓ normalizer (Q : Set (SL2 F)) :=
    ⟨Subgroup.mem_zpowers x, hx⟩
  rw [h1] at hxm
  exact hxm.2

theorem mem_fixSub_Qup_of_fixed (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2)
    {x : SL2 F} (hx : x ∈ Qup F) (hx1 : x ≠ 1) {v : V} (hv : v ≠ 0) (hxv : ρ x v = v) :
    v ∈ fixSub ρ (Qup F) := by
  obtain ⟨P, hP, hPv⟩ := exists_sylow_fixes hp hp2 hF hD ρ hneg hV hv
  obtain ⟨P', hP'def⟩ : ∃ P' : Subgroup (SL2 F), P' = P.map (MulAut.conj x).toMonoidHom := ⟨_, rfl⟩
  have hP'mem : ∀ y, y ∈ P' ↔ ∃ z ∈ P, x * z * x⁻¹ = y := by
    intro y
    rw [hP'def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  have hP'card : Nat.card P' = Nat.card F := by
    rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj x).injective, hP]
  have hxinv : ρ x⁻¹ v = v := by
    have h3 := congrArg (ρ x⁻¹) hxv
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h3
    exact h3.symm
  have hvP' : v ∈ fixSub ρ P' := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (hP'mem y).1 hy
    calc ρ (x * z * x⁻¹) v = ρ x (ρ z (ρ x⁻¹ v)) := by simp [map_mul]
      _ = v := by rw [hxinv, hPv z hz, hxv]
  have hPeq : P = P' := by
    by_contra hne
    have h0 := fixSub_inf_eq_bot hp hp2 hF hD ρ hρ hneg hV hP hP'card hne
    have hmem : v ∈ fixSub ρ P ⊓ fixSub ρ P' := ⟨fun h hh => hPv h hh, hvP'⟩
    rw [h0] at hmem
    exact hv (Submodule.mem_bot _ |>.1 hmem)
  have hxnorm : x ∈ normalizer (P : Set (SL2 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : x * h * x⁻¹ ∈ P' := (hP'mem _).2 ⟨h, hh, rfl⟩
      rwa [← hPeq] at this
    · intro hh
      rw [hPeq] at hh
      obtain ⟨z, hz, hzh⟩ := (hP'mem _).1 hh
      have : z = h := by
        have := mul_inv_cancel_right (x * z) x⁻¹
        simpa [mul_assoc] using hzh
      rw [← this]
      exact hz
  have hxP : x ∈ P := by
    obtain ⟨t, rfl⟩ := mem_Qup.1 hx
    exact mem_of_mem_normalizer hp hF hP hxnorm (upperSL_pow_prime hp hF t)
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq hp hF hP
  have hgx : g⁻¹ * x * g ∈ Qup F := (hg x).1 hxP
  have hgBor : g⁻¹ ∈ Bor F := by
    by_contra hn
    exact hx1 (eq_one_of_conj_mem hn hx (by simpa using hgx))
  have hgB : g ∈ Bor F := by simpa using inv_mem hgBor
  have hgN := Bor_le_normalizer hgB
  rw [Subgroup.mem_normalizer_iff] at hgN
  intro y hy
  apply hPv y
  rw [hg y, hgN (g⁻¹ * y * g)]
  simpa [mul_assoc] using hy

end Semi

section Dual

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

noncomputable instance instAddCommGroupDualZMod {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] : AddCommGroup (Module.Dual (ZMod p) V) :=
  @LinearMap.addCommGroup (ZMod p) (ZMod p) V (ZMod p) _ _ _ (ZMod.commRing p).toRing.toAddCommGroup
    _ _ (RingHom.id _)

@[expose] def commSub (ρ : Representation (ZMod p) (SL2 F) V) (H : Subgroup (SL2 F)) :
    Submodule (ZMod p) V :=
  Submodule.span (ZMod p) {w | ∃ x ∈ H, ∃ v : V, w = ρ x v - v}

omit [Finite F] [Finite V] in
theorem sub_mem_commSub (ρ : Representation (ZMod p) (SL2 F) V) {H : Subgroup (SL2 F)} {x : SL2 F}
    (hx : x ∈ H) (v : V) : ρ x v - v ∈ commSub ρ H :=
  Submodule.subset_span ⟨x, hx, v, rfl⟩

omit [Finite F] [Finite V] in
theorem fixSub_dual_eq (ρ : Representation (ZMod p) (SL2 F) V) (H : Subgroup (SL2 F)) :
    fixSub (Representation.dual ρ) H = (commSub ρ H).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hφ w hw
    refine Submodule.span_induction (p := fun w _ => φ w = 0) ?_ (map_zero φ) (fun a b _ _ ha hb => by
      rw [map_add, ha, hb, add_zero]) (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hw
    rintro _ ⟨x, hx, v, rfl⟩
    have h1 := hφ x⁻¹ (inv_mem hx)
    have h2 : (Representation.dual ρ x⁻¹) φ v = φ v := by rw [h1]
    rw [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply] at h2
    have h3 : φ (ρ x v) = φ v := h2
    rw [map_sub, h3, sub_self]
  · intro hφ h hh
    ext v
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    have := hφ _ (sub_mem_commSub ρ (inv_mem hh) v)
    rw [map_sub, sub_eq_zero] at this
    simpa using this

omit [Finite F] [Finite V] in
theorem dual_injective [Fact p.Prime] [Module.Finite (ZMod p) V] (ρ : Representation (ZMod p) (SL2 F) V)
    (hρ : Function.Injective ρ) : Function.Injective (Representation.dual ρ) := by
  intro g g' h
  have key : ρ g⁻¹ = ρ g'⁻¹ := by
    ext v
    refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (ρ g⁻¹ v - ρ g'⁻¹ v)).1 ?_)
    intro φ
    have h1 := congrArg (fun r => r φ v) h
    simp only [Representation.dual_apply, Module.Dual.transpose_apply] at h1
    have h2 : φ (ρ g⁻¹ v) = φ (ρ g'⁻¹ v) := h1
    rw [map_sub]
    exact sub_eq_zero.2 h2
  exact inv_injective (hρ key)

omit [Finite F] [Finite V] in
theorem dual_neg_one (ρ : Representation (ZMod p) (SL2 F) V) (hneg : ∀ v, ρ (-1) v = -v)
    (φ : Module.Dual (ZMod p) V) : Representation.dual ρ (-1) φ = -φ := by
  have hinv : (-1 : SL2 F)⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)
  ext v
  rw [Representation.dual_apply, hinv, Module.Dual.transpose_apply]
  show φ (ρ (-1) v) = -φ v
  rw [hneg, map_neg]

theorem finrank_commSub_Qup (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    Module.finrank (ZMod p) (commSub ρ (Qup F)) = n := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfind : Module.Finite (ZMod p) (Module.Dual (ZMod p) V) := inferInstance
  have hfind' : Finite (Module.Dual (ZMod p) V) := Module.finite_of_finite (ZMod p)
  have hVd : Nat.card (Module.Dual (ZMod p) V) = Nat.card F ^ 2 := by
    rw [← hV]
    exact Nat.card_congr (Module.Free.chooseBasis (ZMod p) V).toDualEquiv.toEquiv.symm
  have h1 := card_fixSub_Qup hp hp2 hF hD (Representation.dual ρ) (dual_injective ρ hρ)
    (dual_neg_one ρ hneg) hVd
  have hpn : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W] (k : ℕ),
      Nat.card W = p ^ k → Module.finrank (ZMod p) W = k := by
    intro W _ _ _ k hk
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := W)
    rw [hk, hpn] at this
    exact (Nat.pow_right_injective hp.two_le this).symm
  have h2 : Module.finrank (ZMod p) (fixSub (Representation.dual ρ) (Qup F)) = n :=
    hfr _ n (by rw [h1, hF])
  have h3 : Module.finrank (ZMod p) V = 2 * n := hfr V (2 * n) (by rw [hV, hF, ← pow_mul]; ring_nf)
  have h4 := Subspace.finrank_add_finrank_dualAnnihilator_eq (commSub ρ (Qup F))
  rw [← fixSub_dual_eq, h2, h3] at h4
  omega

end Dual

section Quad

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

theorem exists_mem_V2 (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    ∃ u : V, u ∉ fixSub ρ (Qup F) ∧ ∀ x ∈ Qup F, ρ x u - u ∈ fixSub ρ (Qup F) := by
  have : Fact p.Prime := ⟨hp⟩
  have hAcard : Nat.card (fixSub ρ (Qup F)) = Nat.card F :=
    card_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV
  obtain ⟨A, hAdef⟩ : ∃ A : Submodule (ZMod p) V, A = fixSub ρ (Qup F) := ⟨_, rfl⟩
  rw [← hAdef] at hAcard ⊢
  let ρQ : Representation (ZMod p) (Qup F) V := ρ.comp (Qup F).subtype
  have hstab : ∀ g : Qup F, A ≤ A.comap (ρQ g) := by
    intro g a ha
    rw [hAdef] at ha
    show ρ g.1 a ∈ A
    rw [hAdef, ha g.1 g.2]
    exact ha
  let σ : Representation (ZMod p) (Qup F) (V ⧸ A) := ρQ.quotient A hstab
  let _ : MulAction (Qup F) (V ⧸ A) := MulAction.compHom _ σ
  have hpg : IsPGroup p (Qup F) := IsPGroup.of_card (n := n) (card_Qup.trans hF)
  have hfinQ : Finite (V ⧸ A) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := A)) (Submodule.Quotient.mk_surjective A)
  have hmod := hpg.card_modEq_card_fixedPoints (V ⧸ A)
  have hq : Nat.card (V ⧸ A) = Nat.card F := by
    have h1 := Submodule.card_eq_card_quotient_mul_card A
    rw [hV, hAcard] at h1
    have hpos : 0 < Nat.card F := Nat.card_pos
    rw [sq] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    simp at this
  have hpq : p ∣ Nat.card F := hF ▸ dvd_pow_self p hn
  have hfix : Nat.card (MulAction.fixedPoints (Qup F) (V ⧸ A)) ≡ 0 [MOD p] := by
    rw [hq] at hmod
    exact hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 hpq)
  have h0 : (0 : V ⧸ A) ∈ MulAction.fixedPoints (Qup F) (V ⧸ A) := by
    intro g
    show σ g 0 = 0
    exact map_zero _
  have hcard1 : 1 < Nat.card (MulAction.fixedPoints (Qup F) (V ⧸ A)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints (Qup F) (V ⧸ A)) := Nat.card_pos_iff.2
      ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    by_contra hle
    have h1 : Nat.card (MulAction.fixedPoints (Qup F) (V ⧸ A)) = 1 := by omega
    rw [h1] at hfix
    have := (Nat.modEq_zero_iff_dvd).1 hfix
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hnt : Nontrivial (MulAction.fixedPoints (Qup F) (V ⧸ A)) :=
    Finite.one_lt_card_iff_nontrivial.1 hcard1
  obtain ⟨⟨y, hy⟩, hy0⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints (Qup F) (V ⧸ A))
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective A y
  refine ⟨u, ?_, ?_⟩
  · intro huA
    apply hy0
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero A).2 huA
  · intro x hx
    have h1 := hy ⟨x, hx⟩
    have h2 : (Submodule.Quotient.mk (ρ x u) : V ⧸ A) = Submodule.Quotient.mk u := h1
    exact (Submodule.Quotient.eq A).1 h2

theorem fixSub_le_commSub (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    fixSub ρ (Qup F) ≤ commSub ρ (Qup F) := by
  obtain ⟨u, huA, hu⟩ := exists_mem_V2 hp hp2 hF hD ρ hρ hneg hV
  have hu0 : u ≠ 0 := fun h => huA (h ▸ (fixSub ρ (Qup F)).zero_mem)
  let ψ : Qup F → fixSub ρ (Qup F) := fun x => ⟨ρ x u - u, hu x x.2⟩
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ρ x u - u = ρ y u - u := congrArg Subtype.val hxy
    have h2 : ρ x u = ρ y u := sub_left_injective h1
    have h3 : ρ ((y⁻¹ * x : Qup F) : SL2 F) u = u := by
      have := congrArg (ρ (y : SL2 F)⁻¹) h2
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
        map_one] at this
      simpa using this
    by_contra hne
    have hne' : ((y⁻¹ * x : Qup F) : SL2 F) ≠ 1 := by
      intro h
      apply hne
      have : y⁻¹ * x = 1 := Subtype.ext h
      exact (inv_mul_eq_one.1 this).symm
    exact huA (mem_fixSub_Qup_of_fixed hp hp2 hF hD ρ hρ hneg hV (y⁻¹ * x : Qup F).2 hne' hu0 h3)
  have hcard : Nat.card (fixSub ρ (Qup F)) ≤ Nat.card (Qup F) := by
    rw [card_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV, card_Qup]
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le hcard
  intro a ha
  obtain ⟨x, hx⟩ := hbij.2 ⟨a, ha⟩
  have : ρ x u - u = a := congrArg Subtype.val hx
  rw [← this]
  exact sub_mem_commSub ρ x.2 u

theorem commSub_Qup_eq (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    commSub ρ (Qup F) = fixSub ρ (Qup F) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hpn : Nat.card (ZMod p) = p := Nat.card_zmod p
  have h1 := finrank_commSub_Qup hp hp2 hF hD ρ hρ hneg hV
  have h2 : Module.finrank (ZMod p) (fixSub ρ (Qup F)) = n := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := fixSub ρ (Qup F))
    rw [card_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV, hF, hpn] at this
    exact (Nat.pow_right_injective hp.two_le this).symm
  exact (Submodule.eq_of_le_of_finrank_le (fixSub_le_commSub hp hp2 hF hD ρ hρ hneg hV)
    (by omega)).symm

theorem sub_mem_fixSub_Qup (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) {x : SL2 F} (hx : x ∈ Qup F)
    (v : V) : ρ x v - v ∈ fixSub ρ (Qup F) := by
  rw [← commSub_Qup_eq hp hp2 hF hD ρ hρ hneg hV]
  exact sub_mem_commSub ρ hx v

omit [Finite F] [Finite V] in
theorem rho_mul_apply (ρ : Representation (ZMod p) (SL2 F) V) (g h : SL2 F) (v : V) :
    ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul]
  rfl

theorem sub_mem_fixSub_of_card_eq (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) {P : Subgroup (SL2 F)}
    (hP : Nat.card P = Nat.card F) {x : SL2 F} (hx : x ∈ P) (v : V) :
    ρ x v - v ∈ fixSub ρ P := by
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq hp hF hP
  have hy : g⁻¹ * x * g ∈ Qup F := (hg x).1 hx
  have h1 := sub_mem_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV hy (ρ g⁻¹ v)
  have e1 : ρ g (ρ (g⁻¹ * x * g) (ρ g⁻¹ v)) = ρ x v := by
    rw [← rho_mul_apply, ← rho_mul_apply]
    congr 1
    group
  have e2 : ρ g (ρ g⁻¹ v) = v := by
    rw [← rho_mul_apply, mul_inv_cancel, map_one]
    rfl
  have h2 : ρ x v - v = ρ g (ρ (g⁻¹ * x * g) (ρ g⁻¹ v) - ρ g⁻¹ v) := by
    rw [map_sub, e1, e2]
  rw [h2]
  intro z hz
  have hz' : g⁻¹ * z * g ∈ Qup F := (hg z).1 hz
  have e3 : ∀ w : V, ρ z (ρ g w) = ρ g (ρ (g⁻¹ * z * g) w) := by
    intro w
    rw [← rho_mul_apply, ← rho_mul_apply]
    congr 1
    group
  rw [e3, h1 _ hz']

end Quad

end CFSG.GH74.GLS.IVK.Proofs2
