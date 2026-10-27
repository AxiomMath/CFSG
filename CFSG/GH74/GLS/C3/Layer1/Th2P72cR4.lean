module

public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.GLS.IVK

open Equiv Equiv.Perm Subgroup CFSG

theorem conj_swap_mul_swap_mem {e f g : Fin 7} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {w : Perm (Fin 7)} (he : w e = e ∨ w e = f ∨ w e = g) (hf : w f = e ∨ w f = f ∨ w f = g)
    (hg : w g = e ∨ w g = f ∨ w g = g) :
    w * (swap e f * swap e g) * w⁻¹ = swap e f * swap e g ∨
      w * (swap e f * swap e g) * w⁻¹ = (swap e f * swap e g)⁻¹ := by
  have key : w * (swap e f * swap e g) * w⁻¹ = swap (w e) (w f) * swap (w e) (w g) := by
    have h : w * (swap e f * swap e g) * w⁻¹ = (w * swap e f * w⁻¹) * (w * swap e g * w⁻¹) := by
      group
    rw [h, ← swap_apply_apply, ← swap_apply_apply]
  have hwef : w e ≠ w f := fun h => hef (w.injective h)
  have hweg : w e ≠ w g := fun h => heg (w.injective h)
  have hwfg : w f ≠ w g := fun h => hfg (w.injective h)
  rw [key]
  have hinv : (swap e f * swap e g)⁻¹ = swap e g * swap e f := by
    rw [mul_inv_rev, swap_inv, swap_inv]
  rw [hinv]
  rcases he with h1 | h1 | h1 <;> rcases hf with h2 | h2 | h2 <;> rcases hg with h3 | h3 | h3 <;>
    first
      | (exfalso; grind)
      | (rw [h1, h2, h3]; left; ext x; simp only [Perm.mul_apply, swap_apply_def] <;> grind)
      | (rw [h1, h2, h3]; right; ext x; simp only [Perm.mul_apply, swap_apply_def] <;> grind)


theorem exists_unique_fixed_of_ncard_six {F : Subgroup (Perm (Fin 7))}
    (hsix : Set.ncard {i : Fin 7 | ∃ d ∈ F, d i ≠ i} = 6) :
    ∃ g : Fin 7, (∀ d ∈ F, d g = g) ∧ ∀ i : Fin 7, (∀ d ∈ F, d i = i) → i = g := by
  have hcompl : {i : Fin 7 | ∀ d ∈ F, d i = i} = {i : Fin 7 | ∃ d ∈ F, d i ≠ i}ᶜ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_not]
  have hc : Set.ncard {i : Fin 7 | ∀ d ∈ F, d i = i} = 1 := by
    rw [hcompl, Set.ncard_compl, hsix]
    simp
  obtain ⟨g, hg⟩ := Set.ncard_eq_one.1 hc
  refine ⟨g, ?_, ?_⟩
  · intro d hd
    have : g ∈ {i : Fin 7 | ∀ d ∈ F, d i = i} := by rw [hg]; exact rfl
    exact this d hd
  · intro i hi
    have : i ∈ {i : Fin 7 | ∀ d ∈ F, d i = i} := hi
    rw [hg] at this
    exact this


theorem ivk_10_6_A7 {H B : Subgroup (Perm (Fin 7))} (hH : alternatingGroup (Fin 7) ≤ H)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hcard : Nat.card ↥(B ⊓ alternatingGroup (Fin 7)) = 4)
    (hsix : Set.ncard {i : Fin 7 | ∃ d ∈ B ⊓ alternatingGroup (Fin 7), d i ≠ i} = 6) :
    ∃ V : Subgroup (Perm (Fin 7)), V ≤ B ∧ ∃ b ∈ B ⊓ alternatingGroup (Fin 7),
      Nat.card ↥B = 2 * Nat.card ↥V ∧ ∃ c : Perm (Fin 7), orderOf c = 3 ∧
        c ∈ pPrimeCoreOf 2 (centralizer (V : Set (Perm (Fin 7))) ⊓ H) ∧ b * c * b⁻¹ = c⁻¹ := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨g, hgfix, hguniq⟩ := exists_unique_fixed_of_ncard_six hsix
  set B₁ : Subgroup (Perm (Fin 7)) := B ⊓ alternatingGroup (Fin 7) with hB₁
  have hB₁B : B₁ ≤ B := inf_le_left
  have hB₁A : B₁ ≤ alternatingGroup (Fin 7) := inf_le_right
  have hct : ∀ f ∈ B₁, f ≠ 1 → f.cycleType = {2, 2} := by
    intro f hf hf1
    have hfu : f ^ 2 = 1 := by rw [pow_two]; exact hBsq f (hB₁B hf)
    have hs := Equiv.Perm.mem_alternatingGroup.1 (hB₁A hf)
    rw [Equiv.Perm.sign_of_cycleType] at hs
    rcases A7.involution_cycleType f hfu hf1 with h | h | h
    · exfalso
      rw [h] at hs
      have h3 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2} : Multiset ℕ) + Multiset.card ({2} : Multiset ℕ)) =
          -1 := Odd.neg_one_pow (by decide)
      rw [h3] at hs
      exact absurd hs (by decide)
    · exact h
    · exfalso
      rw [h] at hs
      have h3 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2, 2} : Multiset ℕ) +
          Multiset.card ({2, 2, 2} : Multiset ℕ)) = -1 := Odd.neg_one_pow (by decide)
      rw [h3] at hs
      exact absurd hs (by decide)
  obtain ⟨u₁, hu₁B₁, hu₁1⟩ : ∃ u ∈ B₁, u ≠ 1 := by
    by_contra hno
    push Not at hno
    have : B₁ = ⊥ := (Subgroup.eq_bot_iff_forall B₁).2 hno
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hu₁supp : u₁.support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, hct u₁ hu₁B₁ hu₁1]
    rfl
  set Fx : Finset (Fin 7) := u₁.supportᶜ with hFx
  have hFxcard : Fx.card = 3 := by
    rw [hFx, Finset.card_compl, hu₁supp]
    simp
  have hmemFx : ∀ x, x ∈ Fx ↔ u₁ x = x := by
    intro x
    simp [hFx, Equiv.Perm.mem_support]
  have hgFx : g ∈ Fx := (hmemFx g).2 (hgfix u₁ hu₁B₁)
  obtain ⟨e, f, hef, hFxeq⟩ := Finset.card_eq_two.1
    (show (Fx.erase g).card = 2 by rw [Finset.card_erase_of_mem hgFx, hFxcard])
  have heE : e ∈ Fx.erase g := by rw [hFxeq]; simp
  have hfE : f ∈ Fx.erase g := by rw [hFxeq]; simp
  have heg : e ≠ g := Finset.ne_of_mem_erase heE
  have hfg : f ≠ g := Finset.ne_of_mem_erase hfE
  have hue : u₁ e = e := (hmemFx e).1 (Finset.mem_of_mem_erase heE)
  have huf : u₁ f = f := (hmemFx f).1 (Finset.mem_of_mem_erase hfE)
  have hFx3 : ∀ x, u₁ x = x → x = g ∨ x = e ∨ x = f := by
    intro x hx
    by_cases hxg : x = g
    · exact Or.inl hxg
    · have : x ∈ Fx.erase g := Finset.mem_erase.2 ⟨hxg, (hmemFx x).2 hx⟩
      rw [hFxeq] at this
      simpa using Or.inr this
  have hBg : ∀ β ∈ B, β g = g := by
    intro β hβ
    apply hguniq
    intro d hd
    have h1 : d * β = β * d := hBc d (hB₁B hd) β hβ
    have h2 : d (β g) = β (d g) := by
      have := congrArg (fun p : Perm (Fin 7) => p g) h1
      simpa using this
    rw [h2, hgfix d hd]
  have hBFx : ∀ β ∈ B, ∀ x, u₁ x = x → β x = g ∨ β x = e ∨ β x = f := by
    intro β hβ x hx
    apply hFx3
    have h1 : u₁ * β = β * u₁ := hBc u₁ (hB₁B hu₁B₁) β hβ
    have h2 : u₁ (β x) = β (u₁ x) := by
      have := congrArg (fun p : Perm (Fin 7) => p x) h1
      simpa using this
    rw [h2, hx]
  obtain ⟨b, hbB₁, hbe⟩ : ∃ b ∈ B₁, b e ≠ e := by
    by_contra hno
    push Not at hno
    exact heg (hguniq e hno)
  have hbsq : b * b = 1 := hBsq b (hB₁B hbB₁)
  have hbbx : ∀ x, b (b x) = x := fun x => by
    have := congrArg (fun p : Perm (Fin 7) => p x) hbsq
    simpa using this
  have hbg : b g = g := hBg b (hB₁B hbB₁)
  have hbe' : b e = f := by
    rcases hBFx b (hB₁B hbB₁) e hue with h | h | h
    · exfalso
      apply heg
      have : b e = b g := by rw [h, hbg]
      exact b.injective this
    · exact absurd h hbe
    · exact h
  have hbf' : b f = e := by rw [← hbe', hbbx]
  set V : Subgroup (Perm (Fin 7)) := (MulAction.stabilizer ↥B e).map B.subtype with hV
  have hVB : V ≤ B := Subgroup.map_subtype_le _
  have hVe : ∀ v ∈ V, v ∈ B ∧ v e = e := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  have hVfix : ∀ v ∈ V, v e = e ∧ v f = f ∧ v g = g := by
    intro v hv
    obtain ⟨hvB, hve⟩ := hVe v hv
    have hvg : v g = g := hBg v hvB
    refine ⟨hve, ?_, hvg⟩
    rcases hBFx v hvB f huf with h | h | h
    · exfalso
      apply hfg
      have : v f = v g := by rw [h, hvg]
      exact v.injective this
    · exfalso
      apply hef
      have : v e = v f := by rw [hve, h]
      exact v.injective this
    · exact h
  have hu₁V : u₁ ∈ V := ⟨⟨u₁, hB₁B hu₁B₁⟩, hue, rfl⟩
  have hFixV : ∀ x, (∀ v ∈ V, v x = x) → x = g ∨ x = e ∨ x = f :=
    fun x hx => hFx3 x (hx u₁ hu₁V)
  have horb : MulAction.orbit ↥B e = {e, f} := by
    ext x
    constructor
    · rintro ⟨β, rfl⟩
      have hβ : (β : Perm (Fin 7)) e = β • e := rfl
      rcases hBFx β β.2 e hue with h | h | h
      · exfalso
        apply heg
        have : (β : Perm (Fin 7)) e = (β : Perm (Fin 7)) g := by rw [h, hBg β β.2]
        exact (β : Perm (Fin 7)).injective this
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨⟨b, hB₁B hbB₁⟩, hbe'⟩
  have horbcard : Nat.card (MulAction.orbit ↥B e) = 2 := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_pair hef]
  have hcardB : Nat.card ↥B = Nat.card (MulAction.orbit ↥B e) * Nat.card (MulAction.stabilizer ↥B e) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥B e)).symm
  have hcardV : Nat.card ↥V = Nat.card (MulAction.stabilizer ↥B e) :=
    Subgroup.card_map_of_injective B.subtype_injective
  set c : Perm (Fin 7) := swap e f * swap e g with hc
  have hc3 : c.IsThreeCycle := isThreeCycle_swap_mul_swap_same hef heg hfg
  have hbc : b * c * b⁻¹ = c⁻¹ := by
    have h1 : b * c * b⁻¹ = (b * swap e f * b⁻¹) * (b * swap e g * b⁻¹) := by rw [hc]; group
    rw [h1, ← swap_apply_apply, ← swap_apply_apply, hbe', hbf', hbg, hc, mul_inv_rev, swap_inv,
      swap_inv]
    ext x
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  have hcV : ∀ v ∈ V, v * c * v⁻¹ = c := by
    intro v hv
    obtain ⟨hve, hvf, hvg⟩ := hVfix v hv
    have h1 : v * c * v⁻¹ = (v * swap e f * v⁻¹) * (v * swap e g * v⁻¹) := by rw [hc]; group
    rw [h1, ← swap_apply_apply, ← swap_apply_apply, hve, hvf, hvg]
  have hnorm : ∀ w : Perm (Fin 7), w ∈ centralizer (V : Set (Perm (Fin 7))) →
      w * c * w⁻¹ = c ∨ w * c * w⁻¹ = c⁻¹ := by
    intro w hw
    have hwS : ∀ x, (x = g ∨ x = e ∨ x = f) → (w x = g ∨ w x = e ∨ w x = f) := by
      intro x hx
      apply hFixV
      intro v hv
      have h1 : v * w = w * v := (Subgroup.mem_centralizer_iff.1 hw v hv)
      have h2 : v (w x) = w (v x) := by
        have := congrArg (fun p : Perm (Fin 7) => p x) h1
        simpa using this
      have hvx : v x = x := by
        obtain ⟨hve, hvf, hvg⟩ := hVfix v hv
        rcases hx with rfl | rfl | rfl
        · exact hvg
        · exact hve
        · exact hvf
      rw [h2, hvx]
    have hwe := hwS e (Or.inr (Or.inl rfl))
    have hwf := hwS f (Or.inr (Or.inr rfl))
    have hwg := hwS g (Or.inl rfl)
    exact conj_swap_mul_swap_mem hef heg hfg (by grind) (by grind) (by grind)
  refine ⟨V, hVB, b, hbB₁, ?_, c, hc3.orderOf, ?_, hbc⟩
  · rw [hcardB, horbcard, hcardV]
  ·
    set C : Subgroup (Perm (Fin 7)) := centralizer (V : Set (Perm (Fin 7))) ⊓ H with hC
    have hcA : c ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.2 hc3.sign
    have hcC : c ∈ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_, hH hcA⟩
      have := hcV v hv
      calc v * c = (v * c * v⁻¹) * v := by group
        _ = c * v := by rw [this]
    set N : Subgroup ↥C := (Subgroup.zpowers c).subgroupOf C with hN
    have hNnorm : N.Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hkc : (k : Perm (Fin 7)) ∈ centralizer (V : Set (Perm (Fin 7))) := k.2.1
      have h1 : ((k * n * k⁻¹ : ↥C) : Perm (Fin 7)) =
          ((k : Perm (Fin 7)) * c * (k : Perm (Fin 7))⁻¹) ^ m := by
        have : ((k * n * k⁻¹ : ↥C) : Perm (Fin 7)) =
            (k : Perm (Fin 7)) * (n : Perm (Fin 7)) * (k : Perm (Fin 7))⁻¹ := rfl
        rw [this, ← hm]
        exact conj_zpow.symm
      rw [h1]
      rcases hnorm k hkc with h | h
      · rw [h]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
      · rw [h]
        exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) _
    have hNcop : Nat.Coprime 2 (Nat.card N) := by
      have h1 : Nat.card N = Nat.card (Subgroup.zpowers c) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
          intro x hx
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          exact Subgroup.zpow_mem _ hcC _)).toEquiv
      rw [h1, Nat.card_zpowers, hc3.orderOf]
      norm_num
    have hsub : N ≤ pPrimeCore 2 ↥C := le_sSup ⟨hNnorm, hNcop⟩
    rw [C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff]
    exact ⟨hcC, hsub (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers c))⟩

end CFSG.GH74.GLS.IVK
