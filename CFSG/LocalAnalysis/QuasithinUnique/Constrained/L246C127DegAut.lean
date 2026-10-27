module

public import CFSG.Quasithin.Background.C116Two.NatLin2
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.L246C127.Deg

open CFSG.Quasithin.C116Two CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open

theorem gen_of_card {F : Type} [Field F] [Fintype F] (m : Submodule F (Fin 2 → F))
    (h : Nat.card m = Fintype.card F) (x : Fin 2 → F) (hx : x ≠ 0) (hxm : x ∈ m) :
    ∀ y ∈ m, ∃ c : F, y = c • x := by
  have hfin : Finite m := Nat.finite_of_card_ne_zero (by rw [h]; exact Fintype.card_ne_zero)
  let f : F → m := fun c => ⟨c • x, Submodule.smul_mem m c hxm⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h2 : a • x = b • x := congrArg Subtype.val hab
    have h3 : (a - b) • x = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hx
  have hle : Nat.card m ≤ Nat.card F := le_of_eq (by rw [h, Nat.card_eq_fintype_card])
  have hsurj : Function.Surjective f := (hinj.bijective_of_nat_card_le hle).2
  intro y hy
  obtain ⟨c, hc⟩ := hsurj ⟨y, hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem linear_of_fixes_line {F : Type} [Field F] (ℓ : Submodule F (Fin 2 → F)) (hℓ : ℓ ≠ ⊥)
    (g : MulAut (Multiplicative (Fin 2 → F))) (σ : F ≃+* F) (hg : IsSemilinear σ g)
    (hfix : ∀ x ∈ ℓ, addMap g x = x) : σ = RingEquiv.refl F := by
  obtain ⟨e, he, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓ
  have hfe : addMap g e = e := hfix e he
  ext c
  have h1 : addMap g (c • e) = c • e := hfix (c • e) (Submodule.smul_mem ℓ c he)
  have h2 : addMap g (c • e) = σ c • e := by
    rw [hg c e, hfe]
  have h3 : (σ c - c) • e = 0 := by
    rw [sub_smul, ← h2, h1, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

theorem lines_eq_of_inter {F : Type} [Field F] [Fintype F] (ℓ ℓ' : Submodule F (Fin 2 → F))
    (h : Nat.card ℓ = Fintype.card F) (h' : Nat.card ℓ' = Fintype.card F)
    (x : Fin 2 → F) (hx : x ≠ 0) (hx1 : x ∈ ℓ) (hx2 : x ∈ ℓ') : ℓ = ℓ' := by
  apply le_antisymm
  · intro y hy
    obtain ⟨c, rfl⟩ := gen_of_card ℓ h x hx hx1 y hy
    exact Submodule.smul_mem ℓ' c hx2
  · intro y hy
    obtain ⟨c, rfl⟩ := gen_of_card ℓ' h' x hx hx2 y hy
    exact Submodule.smul_mem ℓ c hx1

theorem exists_line_gen {F : Type} [Field F] [Fintype F] (ℓ : Submodule F (Fin 2 → F))
    (h : Nat.card ℓ = Fintype.card F) :
    ∃ e : Fin 2 → F, e ≠ 0 ∧ e ∈ ℓ ∧ ∀ x ∈ ℓ, ∃ c : F, x = c • e := by
  have hℓ : ℓ ≠ ⊥ := by
    intro hbot
    subst hbot
    have hsub : Subsingleton (↥(⊥ : Submodule F (Fin 2 → F))) := ⟨fun a b => Subtype.ext (by
      have ha : (a : Fin 2 → F) = 0 := by
        have ha' := a.2
        rwa [Submodule.mem_bot] at ha'
      have hb : (b : Fin 2 → F) = 0 := by
        have hb' := b.2
        rwa [Submodule.mem_bot] at hb'
      rw [ha, hb])⟩
    have h1 : Nat.card (↥(⊥ : Submodule F (Fin 2 → F))) = 1 :=
      Nat.card_of_subsingleton (0 : ↥(⊥ : Submodule F (Fin 2 → F)))
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  obtain ⟨e, he, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓ
  exact ⟨e, hne, he, gen_of_card ℓ h e hne he⟩

theorem fixes_line_of_linear_two_power {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : Nat.card ℓ = Fintype.card F)
    (g : MulAut (Multiplicative (Fin 2 → F))) (hg : IsSemilinear (RingEquiv.refl F) g)
    (hpres : ∀ x ∈ ℓ, addMap g x ∈ ℓ) (k : ℕ) (hgk : g ^ (2 ^ k) = 1) :
    ∀ x ∈ ℓ, addMap g x = x := by
  intro x hx
  obtain ⟨e, he0, he, hgen⟩ := exists_line_gen ℓ hℓ
  obtain ⟨l, hl⟩ := hgen (addMap g e) (hpres e he)
  have hglin : ∀ (c : F) (y : Fin 2 → F), addMap g (c • y) = c • addMap g y :=
    fun c y => hg c y
  have hpow : ∀ m : ℕ, addMap (g ^ m) e = (l ^ m) • e := by
    intro m
    induction m with
    | zero => simp [addMap_one]
    | succ m ih =>
      rw [pow_succ' g m, addMap_mul, ih, hglin, hl, smul_smul, ← pow_succ]
  have hl2 : l ^ (2 ^ k) = 1 := by
    have h1 : addMap (g ^ (2 ^ k)) e = e := by rw [hgk, addMap_one]
    rw [hpow] at h1
    have h2 : (l ^ (2 ^ k) - 1) • e = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h he0
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply he0
    apply addMap_injective_aut g
    rw [hl, zero_smul, addMap_zero_aut]
  have hq1 : l ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one l hl0
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq2dvd : 2 ∣ Fintype.card F := by
    obtain ⟨m, _, hm⟩ := FiniteField.card F 2
    rw [hm]
    exact dvd_pow_self 2 (PNat.ne_zero m)
  have hcop : Nat.Coprime (2 ^ k) (Fintype.card F - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.prime_two.coprime_iff_not_dvd]
    omega
  have hgcd : Nat.gcd (2 ^ k) (Fintype.card F - 1) = 1 := hcop
  have hl1 : l ^ Nat.gcd (2 ^ k) (Fintype.card F - 1) = 1 := pow_gcd_eq_one.mpr ⟨hl2, hq1⟩
  rw [hgcd, pow_one] at hl1
  obtain ⟨c, rfl⟩ := hgen x hx
  rw [hglin, hl, hl1, one_smul]

theorem exists_trace_ne_zero {F : Type} [Field F] [Fintype F] {ι : Type} [Fintype ι] [Nonempty ι]
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : ℓ ≠ ⊥) (g : ι → MulAut (Multiplicative (Fin 2 → F)))
    (σ : ι → (F ≃+* F)) (hsem : ∀ i, IsSemilinear (σ i) (g i)) (hinj : Function.Injective σ) :
    ∃ x ∈ ℓ, ∑ i, addMap (g i) x ≠ 0 := by
  obtain ⟨e, he, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓ
  by_contra hcon
  push Not at hcon
  have hkey : ∀ c : F, ∑ i, σ i c • addMap (g i) e = 0 := by
    intro c
    refine Eq.trans ?_ (hcon (c • e) (ℓ.smul_mem c he))
    exact Finset.sum_congr rfl (fun i _ => (hsem i c e).symm)
  have hcoord : ∀ (c : F) (j : Fin 2), ∑ i, addMap (g i) e j * σ i c = 0 := by
    intro c j
    have h := congrFun (hkey c) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    calc ∑ i, addMap (g i) e j * σ i c = ∑ i, σ i c * addMap (g i) e j :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = 0 := h
  have hli : LinearIndependent F (fun i : ι => (⇑(σ i) : F → F)) := by
    have hmono : Function.Injective (fun i : ι => (σ i).toRingHom.toMonoidHom) := by
      intro i k hik
      apply hinj
      ext c
      exact congrArg (fun φ : F →* F => φ c) hik
    exact (linearIndependent_monoidHom F F).comp _ hmono
  have hfun : ∀ (j : Fin 2) (i : ι), addMap (g i) e j = 0 := by
    intro j
    have hsum : ∑ i, addMap (g i) e j • (⇑(σ i) : F → F) = 0 := by
      funext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcoord c j
    intro i
    exact (Fintype.linearIndependent_iff.mp hli (fun i => addMap (g i) e j) hsum) i
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hzero : addMap (g i0) e = 0 := funext (fun j => hfun j i0)
  apply hne
  apply addMap_injective_aut (g i0)
  rw [hzero, addMap_zero_aut]

theorem card_top_submodule {F : Type} [Field F] [Fintype F] :
    Nat.card (⊤ : Submodule F (Fin 2 → F)) = Fintype.card F ^ 2 := by
  rw [Nat.card_congr (Submodule.topEquiv (R := F) (M := Fin 2 → F)).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem addMap_inv_apply {F : Type} [Field F] (b : MulAut (Multiplicative (Fin 2 → F)))
    (x : Fin 2 → F) : addMap b⁻¹ (addMap b x) = x := by
  rw [← addMap_mul, inv_mul_cancel, addMap_one]

theorem exists_ne_zero_mem {F : Type} [Field F] [Fintype F] (ℓ : Submodule F (Fin 2 → F))
    (h : Nat.card ℓ = Fintype.card F) : ∃ x ∈ ℓ, x ≠ 0 := by
  have h1 : 1 < Nat.card ℓ := by
    rw [h]
    exact Fintype.one_lt_card
  haveI : Nontrivial ℓ := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨x, hx⟩ := exists_ne (0 : ℓ)
  exact ⟨x, x.2, fun h0 => hx (Subtype.ext h0)⟩

theorem free_action_of_linear {F : Type} [Field F] [Fintype F] [CharP F 2]
    (B₁ : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) (hB₁ : IsElemAbelian 2 B₁)
    (hlin : ∀ b ∈ B₁, IsSemilinear (RingEquiv.refl F) b)
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : Nat.card ℓ = Fintype.card F)
    (hfix : ∀ x : Fin 2 → F, (∀ b ∈ B₁, addMap b x = x) ↔ x ∈ ℓ)
    (v : Fin 2 → F) (hv : v ∉ ℓ) (c : MulAut (Multiplicative (Fin 2 → F))) (hc : c ∈ B₁)
    (hcv : addMap c v = v) : c = 1 := by
  by_contra hc1
  let Bc : Subgroup (MulAut (Multiplicative (Fin 2 → F))) := Subgroup.zpowers c
  have hBcle : Bc ≤ B₁ := (Subgroup.zpowers_le).mpr hc
  have hBc : IsElemAbelian 2 Bc := CFSG.Open.IsElemAbelian.mono hB₁ hBcle
  have hBcne : Bc ≠ ⊥ := by
    intro h
    apply hc1
    have : c ∈ Bc := Subgroup.mem_zpowers c
    rw [h] at this
    exact (Subgroup.mem_bot.mp this)
  obtain ⟨-, ℓ'', hℓ''card, hℓ''⟩ :=
    linear_part_card Bc hBc (fun b hb => hlin b (hBcle hb)) hBcne
  have hsub : ∀ x ∈ ℓ, x ∈ ℓ'' :=
    fun x hx => (hℓ'' x).mp (fun b hb => (hfix x).mpr hx b (hBcle hb))
  obtain ⟨x₀, hx₀, hx₀ne⟩ := exists_ne_zero_mem ℓ hℓ
  have hℓeq : ℓ = ℓ'' := lines_eq_of_inter ℓ ℓ'' hℓ hℓ''card x₀ hx₀ne hx₀ (hsub x₀ hx₀)
  have hpow : ∀ k : ℤ, addMap (c ^ k) v = v := by
    intro k
    induction k using Int.induction_on with
    | zero => simp [addMap_one]
    | succ k ih => rw [zpow_add_one, addMap_mul, hcv, ih]
    | pred k ih =>
      rw [zpow_sub_one, addMap_mul]
      have h1 : addMap c⁻¹ v = v := by
        calc addMap c⁻¹ v = addMap c⁻¹ (addMap c v) := by rw [hcv]
          _ = v := addMap_inv_apply c v
      rw [h1, ih]
  have hvfix : ∀ b ∈ Bc, addMap b v = v := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hpow k
  exact hv (hℓeq ▸ (hℓ'' v).mp hvfix)

theorem offender_classification {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hq : 4 ≤ Fintype.card F)
    (B : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) (hB : IsElemAbelian 2 B)
    (hN : ∀ b ∈ B, ∀ l ∈ (slAct F).range, b * l * b⁻¹ ∈ (slAct F).range)
    (hne : B ≠ ⊥)
    (hoff : Nat.card (Multiplicative (Fin 2 → F)) ≤
      Nat.card B * Nat.card {x : Multiplicative (Fin 2 → F) // ∀ b ∈ B, b x = x}) :
    (∀ b ∈ B, IsSemilinear (RingEquiv.refl F) b) ∧ Nat.card B = Fintype.card F ∧
      ∃ ℓ : Submodule F (Fin 2 → F), Nat.card ℓ = Fintype.card F ∧
        ∀ x : Fin 2 → F, (∀ b ∈ B, addMap b x = x) ↔ x ∈ ℓ := by
  classical
  haveI : Finite (Multiplicative (Fin 2 → F)) := inferInstanceAs (Finite (Fin 2 → F))
  haveI : Finite (MulAut (Multiplicative (Fin 2 → F))) := MulEquiv.finite_left
  set q := Fintype.card F with hqdef
  rw [card_multiplicative_pi (F := F), card_fix_eq B] at hoff
  obtain ⟨B₁, hB₁B, hlin, hcardB, hcase⟩ := exists_linear_subgroup B hB hN
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  rcases hcase with hEq | ⟨φ, hφB, σ, hσ1, hσ2, hφ, hφ2⟩
  · have hlinB : ∀ b ∈ B, IsSemilinear (RingEquiv.refl F) b := by
      intro b hb
      rw [← hEq] at hb
      exact hlin b hb
    obtain ⟨hcard, ℓ, hℓcard, hℓ⟩ := linear_part_card B hB hlinB hne
    have hCℓ : Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} = q := by
      rw [hqdef, ← hℓcard]
      exact Nat.card_congr (Equiv.subtypeEquivRight hℓ)
    rw [hCℓ] at hoff
    refine ⟨hlinB, le_antisymm hcard ?_, ℓ, hℓcard, hℓ⟩
    have h1 : q * q ≤ Nat.card B * q := by simpa [sq] using hoff
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  · exfalso
    set C := Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} with hC
    have hPφ : Nat.card {x : Fin 2 → F // x ∈ (⊤ : Submodule F (Fin 2 → F)) ∧ addMap φ x = x} =
        q := by
      have h := card_fixed_semilinear_involution σ hσ1 hσ2 φ hφ hφ2 ⊤ (fun _ _ => trivial)
      rw [card_top_submodule] at h
      exact Nat.pow_left_injective (by norm_num) h
    by_cases hB₁bot : B₁ = ⊥
    · have hBle : Nat.card B ≤ 2 := by
        have := hcardB
        rw [hB₁bot, Subgroup.card_bot] at this
        omega
      have hCle : C ≤ q := by
        rw [← hPφ]
        refine Nat.card_le_card_of_injective (fun x => ⟨x.1, trivial, x.2 φ hφB⟩) ?_
        intro x y h
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        simpa using h'
      have h1 : q * q ≤ 2 * q := calc
        q * q = q ^ 2 := (sq q).symm
        _ ≤ Nat.card B * C := hoff
        _ ≤ 2 * q := Nat.mul_le_mul hBle hCle
      have h2 : q ≤ 2 := by nlinarith
      omega
    · obtain ⟨hcard1, ℓ', hℓ'card, hℓ'⟩ :=
        linear_part_card B₁ (isElemAbelian_of_le' hB₁B hB) hlin hB₁bot
      have hφinv : ∀ x ∈ ℓ', addMap φ x ∈ ℓ' := by
        intro x hx
        rw [← hℓ'] at hx ⊢
        intro b hb
        have hcomm : b * φ = φ * b := hBcomm b (hB₁B hb) φ hφB
        have h1 : addMap b (addMap φ x) = addMap φ (addMap b x) := by
          have := congrArg (fun g => addMap g x) hcomm
          simpa [addMap_mul] using this
        rw [h1, hx b hb]
      have hsq := card_fixed_semilinear_involution σ hσ1 hσ2 φ hφ hφ2 ℓ' hφinv
      set s := Nat.card {x : Fin 2 → F // x ∈ ℓ' ∧ addMap φ x = x} with hs
      have hsq' : s ^ 2 = q := by rw [hsq, hℓ'card]
      have hCs : C ≤ s := by
        refine Nat.card_le_card_of_injective (fun x =>
          (⟨x.1, (hℓ' x.1).mp (fun b hb => x.2 b (hB₁B hb)), x.2 φ hφB⟩ :
            {x : Fin 2 → F // x ∈ ℓ' ∧ addMap φ x = x})) ?_
        intro x y h
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        simpa using h'
      set Pφ : Set (Fin 2 → F) := {x | addMap φ x = x} with hPφset
      have hPφn : Pφ.ncard = q := by
        rw [← Nat.card_coe_set_eq, ← hPφ]
        exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [Pφ]))
      have hsn : (Pφ ∩ (ℓ' : Set (Fin 2 → F))).ncard = s := by
        rw [← Nat.card_coe_set_eq, hs]
        exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [Pφ, and_comm]))
      have hsplit := Set.ncard_inter_add_ncard_diff_eq_ncard Pφ (ℓ' : Set (Fin 2 → F))
        (Set.toFinite _)
      set t := (Pφ \ (ℓ' : Set (Fin 2 → F))).ncard with ht
      have hst : s + t = q := by rw [← hPφn, ← hsplit, hsn]
      have hs2 : 2 ≤ s := by
        by_contra h
        push Not at h
        have : s ^ 2 ≤ 1 := by interval_cases s <;> simp
        omega
      have htpos : t ≠ 0 := by
        intro h0
        rw [h0] at hst
        nlinarith
      obtain ⟨v, hvS⟩ := Set.nonempty_of_ncard_ne_zero htpos
      have hvP : addMap φ v = v := hvS.1
      have hvℓ : v ∉ ℓ' := hvS.2
      let f : ↥B₁ → ↥(Pφ \ (ℓ' : Set (Fin 2 → F))) := fun b =>
        ⟨addMap b.1 v, ⟨by
            show addMap φ (addMap b.1 v) = addMap b.1 v
            have hcomm : φ * b.1 = b.1 * φ := hBcomm φ hφB b.1 (hB₁B b.2)
            have := congrArg (fun g => addMap g v) hcomm
            simp only [addMap_mul] at this
            rw [this, hvP], by
            intro hmem
            apply hvℓ
            have h1 : addMap b.1⁻¹ (addMap b.1 v) = addMap b.1 v :=
              ((hℓ' _).mpr hmem) b.1⁻¹ (B₁.inv_mem b.2)
            rw [addMap_inv_apply] at h1
            rw [h1]
            exact hmem⟩⟩
      have hfinj : Function.Injective f := by
        intro b b' hbb
        have h1 : addMap b.1 v = addMap b'.1 v := congrArg Subtype.val hbb
        have h2 : addMap (b.1⁻¹ * b'.1) v = v := by
          rw [addMap_mul, ← h1, addMap_inv_apply]
        have h3 : b.1⁻¹ * b'.1 = 1 :=
          free_action_of_linear B₁ (isElemAbelian_of_le' hB₁B hB) hlin ℓ' hℓ'card hℓ' v hvℓ _
            (B₁.mul_mem (B₁.inv_mem b.2) b'.2) h2
        apply Subtype.ext
        have := inv_mul_eq_one.mp h3
        exact this
      have hB₁t : Nat.card B₁ ≤ t := by
        have := Nat.card_le_card_of_injective f hfinj
        rw [ht, ← Nat.card_coe_set_eq]
        exact this
      have h3 : q * q ≤ 2 * t * s := calc
        q * q = q ^ 2 := (sq q).symm
        _ ≤ Nat.card B * C := hoff
        _ ≤ (2 * t) * s := Nat.mul_le_mul (by omega) hCs
      nlinarith [sq_nonneg t, hsq', hst]

theorem h4_smul {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {g : MulAut (Multiplicative N)} (hg : IsSemilinear (RingEquiv.refl F) g) (c : F) (x : N) :
    addMap g (c • x) = c • addMap g x := by
  rw [hg c x, RingEquiv.refl_apply]

theorem h4_ext {N : Type} [AddCommGroup N] {g h : MulAut (Multiplicative N)}
    (H : ∀ y : N, addMap g y = addMap h y) : g = h := by
  ext x
  have hx : Multiplicative.toAdd (g (Multiplicative.ofAdd (Multiplicative.toAdd x))) =
      Multiplicative.toAdd (h (Multiplicative.ofAdd (Multiplicative.toAdd x))) :=
    H (Multiplicative.toAdd x)
  exact Multiplicative.toAdd.injective hx

theorem h4_decomp {F : Type} [Field F] (e₁ e₂ : Fin 2 → F)
    (hdet : e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0 ≠ 0) :
    ∀ v : Fin 2 → F, ∃ α β : F, v = α • e₁ + β • e₂ := by
  intro v
  have hinv : (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0) * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  refine ⟨(v 0 * e₂ 1 - v 1 * e₂ 0) * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0)⁻¹,
    (e₁ 0 * v 1 - e₁ 1 * v 0) * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0)⁻¹, ?_⟩
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(v 0)) * hinv
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(v 1)) * hinv

theorem h4_coord {F : Type} [Field F] (e₁ e₂ : Fin 2 → F)
    (hdet : e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0 ≠ 0) (a d a' d' : F)
    (h : a • e₁ + d • e₂ = a' • e₁ + d' • e₂) : d = d' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
  have hy : (d - d') * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0) = 0 := by
    linear_combination e₁ 0 * h1 - e₁ 1 * h0
  rcases mul_eq_zero.mp hy with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hdet

theorem h4_pow_two_pow {F : Type} [Field F] [Fintype F] [CharP F 2] (l : F) (k : ℕ)
    (hl : l ^ (2 ^ k) = 1) : l = 1 := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero k two_ne_zero)] at hl
    exact zero_ne_one hl
  have hq1 : l ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one l hl0
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq2dvd : 2 ∣ Fintype.card F := by
    obtain ⟨m, _, hm⟩ := FiniteField.card F 2
    rw [hm]
    exact dvd_pow_self 2 (PNat.ne_zero m)
  have hcop : Nat.Coprime (2 ^ k) (Fintype.card F - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.prime_two.coprime_iff_not_dvd]
    omega
  have hgcd : Nat.gcd (2 ^ k) (Fintype.card F - 1) = 1 := hcop
  have hl1 : l ^ Nat.gcd (2 ^ k) (Fintype.card F - 1) = 1 := pow_gcd_eq_one.mpr ⟨hl, hq1⟩
  rw [hgcd, pow_one] at hl1
  exact hl1

theorem h4_pow_coeff {F : Type} [Field F] (g : MulAut (Multiplicative (Fin 2 → F)))
    (e₁ e₂ : Fin 2 → F) (a d : F) (hg : IsSemilinear (RingEquiv.refl F) g)
    (h1 : addMap g e₁ = e₁) (h2 : addMap g e₂ = a • e₁ + d • e₂) (j : ℕ) :
    ∃ α : F, addMap (g ^ j) e₂ = α • e₁ + d ^ j • e₂ := by
  induction j with
  | zero => exact ⟨0, by simp [addMap_one]⟩
  | succ j ih =>
    obtain ⟨α, hα⟩ := ih
    refine ⟨α + d ^ j * a, ?_⟩
    rw [show g ^ (j + 1) = g * g ^ j from pow_succ' g j, addMap_mul, hα, addMap_add,
      h4_smul hg, h4_smul hg, h1, h2]
    simp only [smul_add, smul_smul, add_smul, pow_succ, add_assoc]

theorem h4_d_one {F : Type} [Field F] [Fintype F] [CharP F 2] (e₁ e₂ : Fin 2 → F)
    (hdet : e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0 ≠ 0) (g : MulAut (Multiplicative (Fin 2 → F)))
    (a d : F) (hg : IsSemilinear (RingEquiv.refl F) g)
    (h1 : addMap g e₁ = e₁) (h2 : addMap g e₂ = a • e₁ + d • e₂) (k : ℕ)
    (hgk : g ^ (2 ^ k) = 1) : d = 1 := by
  obtain ⟨α, hα⟩ := h4_pow_coeff g e₁ e₂ a d hg h1 h2 (2 ^ k)
  rw [hgk, addMap_one] at hα
  have hα' : (0 : F) • e₁ + (1 : F) • e₂ = α • e₁ + d ^ (2 ^ k) • e₂ := by
    rw [zero_smul, one_smul, zero_add]
    exact hα
  exact h4_pow_two_pow d k (h4_coord e₁ e₂ hdet 0 1 α (d ^ (2 ^ k)) hα').symm

theorem h4_eq {F : Type} [Field F] (e₁ e₂ : Fin 2 → F)
    (hdec : ∀ v : Fin 2 → F, ∃ α β : F, v = α • e₁ + β • e₂)
    (h h' : MulAut (Multiplicative (Fin 2 → F)))
    (hh : IsSemilinear (RingEquiv.refl F) h) (hh' : IsSemilinear (RingEquiv.refl F) h')
    (hh1 : addMap h e₁ = e₁) (hh1' : addMap h' e₁ = e₁) (a : F)
    (h2 : addMap h e₂ = a • e₁ + (1 : F) • e₂) (h2' : addMap h' e₂ = a • e₁ + (1 : F) • e₂) :
    h = h' := by
  refine h4_ext (fun v => ?_)
  obtain ⟨α, β, rfl⟩ := hdec v
  have key : ∀ f : MulAut (Multiplicative (Fin 2 → F)), IsSemilinear (RingEquiv.refl F) f →
      addMap f e₁ = e₁ → addMap f e₂ = a • e₁ + (1 : F) • e₂ →
      addMap f (α • e₁ + β • e₂) = α • e₁ + β • (a • e₁ + (1 : F) • e₂) := by
    intro f hf hf1 hf2
    rw [addMap_add, h4_smul hf, h4_smul hf, hf1, hf2]
  rw [key h hh hh1 h2, key h' hh' hh1' h2']

theorem mem_of_linear_fixes_line {F : Type} [Field F] [Fintype F] [CharP F 2]
    (B : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) (hB : IsElemAbelian 2 B)
    (hlin : ∀ b ∈ B, IsSemilinear (RingEquiv.refl F) b) (hcard : Nat.card B = Fintype.card F)
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : Nat.card ℓ = Fintype.card F)
    (hfix : ∀ x : Fin 2 → F, (∀ b ∈ B, addMap b x = x) ↔ x ∈ ℓ)
    (g : MulAut (Multiplicative (Fin 2 → F))) (hg : IsSemilinear (RingEquiv.refl F) g)
    (hgℓ : ∀ x ∈ ℓ, addMap g x = x) (k : ℕ) (hgk : g ^ (2 ^ k) = 1) : g ∈ B := by
  obtain ⟨e₁, he₁0, he₁, -⟩ := exists_line_gen ℓ hℓ
  obtain ⟨e₂, hdet⟩ : ∃ e₂ : Fin 2 → F, e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0 ≠ 0 := by
    by_cases h0 : e₁ 0 = 0
    · refine ⟨![1, 0], ?_⟩
      have h1 : e₁ 1 ≠ 0 := fun h1 => he₁0 (by funext i; fin_cases i <;> simp [h0, h1])
      simp [h0, h1]
    · exact ⟨![0, 1], by simpa using h0⟩
  have hdec := h4_decomp e₁ e₂ hdet
  choose A D hAD using hdec
  have hB1 : ∀ b ∈ B, addMap b e₁ = e₁ := (hfix e₁).mpr he₁
  have hBd : ∀ b ∈ B, D (addMap b e₂) = 1 := by
    intro b hb
    have hb2 : b ^ (2 ^ 1) = 1 := by simpa using hB.2 b hb
    exact h4_d_one e₁ e₂ hdet b _ _ (hlin b hb) (hB1 b hb) (hAD (addMap b e₂)) 1 hb2
  have hgd : D (addMap g e₂) = 1 :=
    h4_d_one e₁ e₂ hdet g _ _ hg (hgℓ e₁ he₁) (hAD (addMap g e₂)) k hgk
  let φ : B → F := fun b => A (addMap (b : MulAut (Multiplicative (Fin 2 → F))) e₂)
  have hφ : Function.Injective φ := by
    intro b b' hbb'
    have hA : A (addMap (b : MulAut (Multiplicative (Fin 2 → F))) e₂) =
        A (addMap (b' : MulAut (Multiplicative (Fin 2 → F))) e₂) := hbb'
    have e1 := hAD (addMap (b : MulAut (Multiplicative (Fin 2 → F))) e₂)
    have e2 := hAD (addMap (b' : MulAut (Multiplicative (Fin 2 → F))) e₂)
    rw [hBd _ b.2, hA] at e1
    rw [hBd _ b'.2] at e2
    apply Subtype.ext
    exact h4_eq e₁ e₂ (h4_decomp e₁ e₂ hdet) _ _ (hlin _ b.2) (hlin _ b'.2)
      (hB1 _ b.2) (hB1 _ b'.2) _ e1 e2
  have hle : Nat.card F ≤ Nat.card B := le_of_eq (by rw [hcard, Nat.card_eq_fintype_card])
  obtain ⟨b₀, hb₀⟩ := (hφ.bijective_of_nat_card_le hle).2 (A (addMap g e₂))
  have hb₀' : A (addMap (b₀ : MulAut (Multiplicative (Fin 2 → F))) e₂) =
      A (addMap g e₂) := hb₀
  have hgb : g = (b₀ : MulAut (Multiplicative (Fin 2 → F))) := by
    have e1 := hAD (addMap g e₂)
    have e2 := hAD (addMap (b₀ : MulAut (Multiplicative (Fin 2 → F))) e₂)
    rw [hgd] at e1
    rw [hBd _ b₀.2, hb₀'] at e2
    exact h4_eq e₁ e₂ (h4_decomp e₁ e₂ hdet) g _ hg (hlin _ b₀.2) (hgℓ e₁ he₁)
      (hB1 _ b₀.2) _ e1 e2
  rw [hgb]
  exact b₀.2

end CFSG.QuasithinUnique.L246C127.Deg
