module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import CFSG.GH74.GLS.IVK.Proofs2.NatModZ

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.SL2MinimalFaithful

@[expose] def OddSylowStmt (F : Type) [Field F] [Finite F] : Prop :=
  ∀ S : Subgroup (SL2 F), Odd (Nat.card S) → Nat.card F ≤ Nat.card S →
    ∃ P : Subgroup (SL2 F), P ≤ S ∧ Nat.card P = Nat.card F

section Fix

variable {F : Type} [Field F] [Finite F] {p n : ℕ}

theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')

theorem exists_sylow_fixes (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) (SL2 F) V) (hneg : ∀ v, ρ (-1) v = -v)
    (hV : Nat.card V = Nat.card F ^ 2) {v : V} (hv : v ≠ 0) :
    ∃ P : Subgroup (SL2 F), Nat.card P = Nat.card F ∧ ∀ x ∈ P, ρ x v = v := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hp2
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_card_eq hp hp2 hF
  let _ : MulAction (SL2 F) V := MulAction.compHom V ρ
  let S : Subgroup (SL2 F) := MulAction.stabilizer (SL2 F) v
  have hmem : ∀ g, g ∈ S ↔ ρ g v = v := fun g => Iff.rfl
  have hodd : Odd (Nat.card S) := by
    by_contra hne
    have h2dvd : 2 ∣ Nat.card S := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hg2 : (g : SL2 F) ^ 2 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Subtype.val this
    have hg1 : (g : SL2 F) ≠ 1 := by
      intro h1
      have : g = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hg
      omega
    rcases eq_one_or_neg_one_of_sq_eq_one h2F hg2 with h | h
    · exact hg1 h
    · have hgv := (hmem g).1 g.2
      rw [h, hneg] at hgv
      apply hv
      have h3 : (2 : ZMod p) • v = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← hgv]
        exact neg_add_cancel v
      exact (smul_eq_zero.1 h3).resolve_left h2
  have hge : Nat.card F ≤ Nat.card S := by
    have h1 : Nat.card (MulAction.orbit (SL2 F) v) * Nat.card S = Nat.card (SL2 F) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (SL2 F) v)
    have hsmul : ∀ (g : SL2 F) (w : V), g • w = ρ g w := fun _ _ => rfl
    have hsub : ∀ w ∈ MulAction.orbit (SL2 F) v, w ≠ 0 := by
      rintro _ ⟨g, rfl⟩ h0
      apply hv
      have h0' : ρ g v = 0 := h0
      have h3 := congrArg (ρ g⁻¹) h0'
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h3
      simpa using h3
    have horb : Nat.card (MulAction.orbit (SL2 F) v) ≤ Nat.card F ^ 2 - 1 := by
      have hinj : Function.Injective
          (fun x : MulAction.orbit (SL2 F) v => (⟨x.1, hsub x.1 x.2⟩ : {w : V // w ≠ 0})) := by
        intro x y hxy
        exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
      have h4 := Nat.card_le_card_of_injective _ hinj
      have h5 : Nat.card {w : V // w ≠ 0} = Nat.card V - 1 := by
        have : Fintype V := Fintype.ofFinite V
        classical
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp [Fintype.card_subtype_compl]
      rw [h5, hV] at h4
      exact h4
    have hq : 1 < Nat.card F := Finite.one_lt_card
    rw [card_specialLinearGroup_fin_two] at h1
    have hpos : 0 < Nat.card F ^ 2 - 1 := by
      have : 4 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    by_contra hlt
    push Not at hlt
    have h6 : Nat.card (MulAction.orbit (SL2 F) v) * Nat.card S ≤
        (Nat.card F ^ 2 - 1) * Nat.card S := Nat.mul_le_mul_right _ horb
    have h7 : (Nat.card F ^ 2 - 1) * Nat.card S < (Nat.card F ^ 2 - 1) * Nat.card F :=
      Nat.mul_lt_mul_of_pos_left hlt hpos
    have h8 : Nat.card F * (Nat.card F ^ 2 - 1) = (Nat.card F ^ 2 - 1) * Nat.card F := mul_comm _ _
    have h9 : Nat.card (MulAction.orbit (SL2 F) v) * Nat.card S = Nat.card F * (Nat.card F ^ 2 - 1) := h1
    omega
  obtain ⟨P, hPS, hP⟩ := hD S hodd hge
  exact ⟨P, hP, fun x hx => (hmem x).1 (hPS hx)⟩

section FixSub

variable {F : Type} [Field F] {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def fixSub (ρ : Representation (ZMod p) (SL2 F) V) (H : Subgroup (SL2 F)) :
    Submodule (ZMod p) V where
  carrier := {v | ∀ h ∈ H, ρ h v = v}
  add_mem' := fun {a b} ha hb h hh => by rw [map_add, ha h hh, hb h hh]
  zero_mem' := fun h _ => map_zero _
  smul_mem' := fun c v hv h hh => by rw [map_smul, hv h hh]

theorem mem_fixSub {ρ : Representation (ZMod p) (SL2 F) V} {H : Subgroup (SL2 F)} {v : V} :
    v ∈ fixSub ρ H ↔ ∀ h ∈ H, ρ h v = v := Iff.rfl

theorem card_fixSub_conj (ρ : Representation (ZMod p) (SL2 F) V) {P Q : Subgroup (SL2 F)}
    (g : SL2 F) (hg : ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ Q) :
    Nat.card (fixSub ρ P) = Nat.card (fixSub ρ Q) := by
  have hfwd : ∀ v ∈ fixSub ρ Q, ρ g v ∈ fixSub ρ P := by
    intro v hv x hx
    have h1 : g⁻¹ * x * g ∈ Q := (hg x).1 hx
    have h2 : ρ (g⁻¹ * x * g) v = v := hv _ h1
    calc ρ x (ρ g v) = ρ (x * g) v := by rw [map_mul]; rfl
      _ = ρ (g * (g⁻¹ * x * g)) v := by group
      _ = ρ g (ρ (g⁻¹ * x * g) v) := by rw [map_mul]; rfl
      _ = ρ g v := by rw [h2]
  have hbwd : ∀ v ∈ fixSub ρ P, ρ g⁻¹ v ∈ fixSub ρ Q := by
    intro v hv y hy
    have h1 : g * y * g⁻¹ ∈ P := (hg _).2 (by simpa [mul_assoc] using hy)
    have h2 : ρ (g * y * g⁻¹) v = v := hv _ h1
    calc ρ y (ρ g⁻¹ v) = ρ (y * g⁻¹) v := by rw [map_mul]; rfl
      _ = ρ g⁻¹ (ρ (g * y * g⁻¹) v) := by
        rw [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = ρ g⁻¹ v := by rw [h2]
  refine Nat.card_congr
    { toFun := fun v => ⟨ρ g v.1, hfwd v.1 v.2⟩
      invFun := fun v => ⟨ρ g⁻¹ v.1, hbwd v.1 v.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        show ρ g⁻¹ (ρ g v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun v => by
        apply Subtype.ext
        show ρ g (ρ g⁻¹ v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl } |>.symm

end FixSub

end Fix

section Count

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

open scoped Classical in
omit [Finite F] [Finite V] in
theorem card_nonzero_fix [Fintype V] (ρ : Representation (ZMod p) (SL2 F) V) (H : Subgroup (SL2 F)) :
    (Finset.univ.filter (fun v : V => v ≠ 0 ∧ v ∈ fixSub ρ H)).card = Nat.card (fixSub ρ H) - 1 := by
  classical
  have h1 : Finset.univ.filter (fun v : V => v ≠ 0 ∧ v ∈ fixSub ρ H) =
      (Finset.univ.filter (fun v : V => v ∈ fixSub ρ H)).erase 0 := by
    ext v
    simp
  rw [h1, Finset.card_erase_of_mem (by simp), Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_fixSub_Qup_ge (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hneg : ∀ v, ρ (-1) v = -v)
    (hV : Nat.card V = Nat.card F ^ 2) : Nat.card F ≤ Nat.card (fixSub ρ (Qup F)) := by
  have : Fintype V := Fintype.ofFinite V
  classical
  let Syl := {P : Subgroup (SL2 F) // Nat.card P = Nat.card F}
  have hfin : Finite Syl := by
    have : Finite (Subgroup (SL2 F)) := inferInstance
    exact Subtype.finite
  have : Fintype Syl := Fintype.ofFinite Syl
  set a := Nat.card (fixSub ρ (Qup F)) with ha
  have hcard : ∀ P : Syl, Nat.card (fixSub ρ P.1) = a := by
    intro P
    obtain ⟨g, hg⟩ := exists_conj_of_card_eq hp hF P.2
    exact card_fixSub_conj ρ g hg
  let T : Syl → Finset V := fun P => Finset.univ.filter (fun v => v ≠ 0 ∧ v ∈ fixSub ρ P.1)
  have hT : ∀ P, (T P).card = a - 1 := fun P => by
    rw [card_nonzero_fix, hcard P]
  have hcover : (Finset.univ.filter (fun v : V => v ≠ 0)) ⊆ Finset.univ.biUnion T := by
    intro v hv
    have hv0 : v ≠ 0 := by simpa using hv
    obtain ⟨P, hP, hPv⟩ := exists_sylow_fixes hp hp2 hF hD ρ hneg hV hv0
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨⟨P, hP⟩, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv0, hPv⟩
  have h1 : (Finset.univ.filter (fun v : V => v ≠ 0)).card ≤ ∑ P : Syl, (T P).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (Finset.univ.filter (fun v : V => v ≠ 0)).card = Nat.card F ^ 2 - 1 := by
    rw [← hV]
    have h3 : Finset.univ.filter (fun v : V => v ≠ 0) = Finset.univ.erase 0 := by
      ext v; simp
    rw [h3, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.card_eq_fintype_card]
  rw [h2] at h1
  simp only [hT, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  have hSyl : Fintype.card Syl ≤ Nat.card F + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_subgroups_card_eq_le hp hF
  have hq : 1 < Nat.card F := Finite.one_lt_card
  by_contra hlt
  push Not at hlt
  have ha1 : 1 ≤ a := by
    have : 0 < Nat.card (fixSub ρ (Qup F)) := Nat.card_pos
    omega
  have h4 : Fintype.card Syl * (a - 1) ≤ (Nat.card F + 1) * (a - 1) := Nat.mul_le_mul_right _ hSyl
  have h5 : (Nat.card F + 1) * (a - 1) < (Nat.card F + 1) * (Nat.card F - 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have h6 : (Nat.card F + 1) * (Nat.card F - 1) = Nat.card F ^ 2 - 1 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 - 1 = m * (m + 2) := by
      have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
      omega
    rw [this]
    ring
  omega

end Count

section Upper

open CFSG.RankThree.FFModules (repMulAut repMulAut_apply repMulAut_injective)

variable {F : Type} [Field F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem card_fixSub_Qup_le [Finite F] [Finite V] (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hV : Nat.card V = Nat.card F ^ 2) : Nat.card (fixSub ρ (Qup F)) ≤ Nat.card F := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this, pow_zero] at hF
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ v : Multiplicative V, v ^ p = 1 := by
    intro v
    have h1 : (p : ZMod p) • Multiplicative.toAdd v = 0 := by
      rw [ZMod.natCast_self, zero_smul]
    have h2 : p • Multiplicative.toAdd v = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
      exact h1
    apply Multiplicative.toAdd.injective
    simpa [toAdd_pow] using h2
  have hJ : Nat.card (SL2 F) = p ^ n * ((p ^ n) ^ 2 - 1) := by
    rw [card_specialLinearGroup_fin_two, hF]
  have hQ : Nat.card (Qup F) = p ^ n := card_Qup.trans hF
  have hQs : Nat.card (Qlow F) = p ^ n := card_Qlow.trans hF
  have hV' : Nat.card (Multiplicative V) = (p ^ n) ^ 2 := by
    rw [← hF, ← hV]
    exact Nat.card_congr Multiplicative.toAdd
  have h := card_fixedPoints_le hp hp2 hn hJ (fun v w => mul_comm v w) hexp hV' (repMulAut ρ)
    (repMulAut_injective hρ) hQ hQs Qup_inf_Qlow Qup_sup_Qlow
  rw [hF]
  refine le_trans (le_of_eq ?_) h
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.ofAdd v.1, fun u hu => by
        rw [repMulAut_apply]
        exact congrArg Multiplicative.ofAdd (v.2 u hu)⟩
      invFun := fun v => ⟨Multiplicative.toAdd v.1, fun u hu => by
        have := v.2 u hu
        rw [repMulAut_apply] at this
        exact congrArg Multiplicative.toAdd this⟩
      left_inv := fun v => by simp
      right_inv := fun v => by simp }

end Upper

section Disjoint

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

theorem card_fixSub_Qup (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    Nat.card (fixSub ρ (Qup F)) = Nat.card F :=
  le_antisymm (card_fixSub_Qup_le hp hp2 hF ρ hρ hV) (card_fixSub_Qup_ge hp hp2 hF hD ρ hneg hV)

theorem fixSub_inf_eq_bot (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hD : OddSylowStmt F) (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2)
    {P P' : Subgroup (SL2 F)} (hP : Nat.card P = Nat.card F) (hP' : Nat.card P' = Nat.card F)
    (hne : P ≠ P') : fixSub ρ P ⊓ fixSub ρ P' = ⊥ := by
  have : Fintype V := Fintype.ofFinite V
  classical
  let Syl := {P : Subgroup (SL2 F) // Nat.card P = Nat.card F}
  have hfin : Finite Syl := by
    have : Finite (Subgroup (SL2 F)) := inferInstance
    exact Subtype.finite
  have : Fintype Syl := Fintype.ofFinite Syl
  have ha : Nat.card (fixSub ρ (Qup F)) = Nat.card F := card_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV
  have hcard : ∀ R : Syl, Nat.card (fixSub ρ R.1) = Nat.card F := by
    intro R
    obtain ⟨g, hg⟩ := exists_conj_of_card_eq hp hF R.2
    exact (card_fixSub_conj ρ g hg).trans ha
  let T : Syl → Finset V := fun R => Finset.univ.filter (fun v => v ≠ 0 ∧ v ∈ fixSub ρ R.1)
  have hT : ∀ R, (T R).card = Nat.card F - 1 := fun R => by
    rw [card_nonzero_fix, hcard R]
  have hSyl : Fintype.card Syl ≤ Nat.card F + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_subgroups_card_eq_le hp hF
  refine eq_bot_iff.2 fun v hv => ?_
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨hvP, hvP'⟩ := Submodule.mem_inf.1 hv
  let R₀ : Syl := ⟨P, hP⟩
  let R₁ : Syl := ⟨P', hP'⟩
  have hR : R₀ ≠ R₁ := fun h => hne (congrArg Subtype.val h)
  have hcover : (Finset.univ.filter (fun v : V => v ≠ 0)) ⊆
      (T R₁).erase v ∪ (Finset.univ.erase R₁).biUnion T := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa using hw
    obtain ⟨Q, hQ, hQw⟩ := exists_sylow_fixes hp hp2 hF hD ρ hneg hV hw0
    have hwT : w ∈ T ⟨Q, hQ⟩ := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hw0, hQw⟩
    by_cases hQR : (⟨Q, hQ⟩ : Syl) = R₁
    · rw [hQR] at hwT
      by_cases hwv : w = v
      · apply Finset.mem_union_right
        simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨R₀, hR, ?_⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hwv ▸ hv0, hwv ▸ hvP⟩
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwv, hwT⟩)
    · apply Finset.mem_union_right
      simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨⟨Q, hQ⟩, hQR, hwT⟩
  have h1 := Finset.card_le_card hcover
  have h2 : (Finset.univ.filter (fun v : V => v ≠ 0)).card = Nat.card F ^ 2 - 1 := by
    rw [← hV]
    have h3 : Finset.univ.filter (fun v : V => v ≠ 0) = Finset.univ.erase 0 := by
      ext v; simp
    rw [h3, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.card_eq_fintype_card]
  have hvT : v ∈ T R₁ := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv0, hvP'⟩
  have h4 : ((T R₁).erase v ∪ (Finset.univ.erase R₁).biUnion T).card ≤
      ((T R₁).erase v).card + ∑ R ∈ Finset.univ.erase R₁, (T R).card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
  rw [Finset.card_erase_of_mem hvT, hT R₁] at h4
  simp only [hT, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ R₁), Finset.card_univ,
    smul_eq_mul] at h4
  rw [h2] at h1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h5 : (Fintype.card Syl - 1) * (Nat.card F - 1) ≤ Nat.card F * (Nat.card F - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 - 1 = m * (m + 2) := by
      have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
      omega
    rw [this]
    ring
  have h7 : Nat.card F * (Nat.card F - 1) + (Nat.card F - 1 - 1) < (Nat.card F + 1) * (Nat.card F - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 2 := ⟨Nat.card F - 2, by omega⟩
    rw [hm]
    simp only [show m + 2 - 1 = m + 1 from by omega, show m + 1 - 1 = m from by omega]
    nlinarith
  omega

end Disjoint

end CFSG.GH74.GLS.IVK.Proofs2
