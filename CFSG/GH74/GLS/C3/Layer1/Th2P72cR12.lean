module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR3

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open CFSG.Walter.Huppert
open scoped commutatorElement

section Module

variable {M : Type*} [Group M]

@[expose] noncomputable def diffHom (hc : ∀ a b : M, a * b = b * a) (α : MulAut M) : M →* M :=
  MonoidHom.mk' (fun m => m⁻¹ * α m) (by
    intro a b
    simp only [mul_inv_rev, map_mul]
    calc b⁻¹ * a⁻¹ * (α a * α b) = (a⁻¹ * b⁻¹) * (α a * α b) := by rw [hc a⁻¹ b⁻¹]
      _ = a⁻¹ * (b⁻¹ * α a) * α b := by group
      _ = a⁻¹ * (α a * b⁻¹) * α b := by rw [hc b⁻¹ (α a)]
      _ = a⁻¹ * α a * (b⁻¹ * α b) := by group)

@[expose] noncomputable def nuHom (hc : ∀ a b : M, a * b = b * a) (α : MulAut M) : M →* M :=
  (diffHom hc α).comp (diffHom hc α)

theorem nuHom_apply (hc : ∀ a b : M, a * b = b * a) (α : MulAut M) (m : M) :
    nuHom hc α m = (m⁻¹ * α m)⁻¹ * α (m⁻¹ * α m) := rfl

theorem nuHom_comm (hc : ∀ a b : M, a * b = b * a) (α γ : MulAut M) (hαγ : ∀ m, α (γ m) = γ (α m))
    (m : M) : nuHom hc α (γ m) = γ (nuHom hc α m) := by
  simp only [nuHom_apply, map_mul, map_inv, hαγ]

end Module

section FrattiniModule

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

abbrev FMod (P : Subgroup G) : Type := ↥P ⧸ frattini ↥P

variable [Finite G]

theorem FMod.comm {P : Subgroup G} (hP : IsPGroup p ↥P) : ∀ a b : FMod P, a * b = b * a :=
  (frattini_quotient_facts hP).1

@[expose] noncomputable def fAct (P : Subgroup G) (x : normalizer (P : Set G)) : MulAut (FMod P) :=
  frattiniAut ↥P (P.normalizerMonoidHom x)

omit [Finite G] in
theorem fAct_mk (P : Subgroup G) (x : normalizer (P : Set G)) (z : ↥P) :
    fAct P x (QuotientGroup.mk z) = QuotientGroup.mk (P.normalizerMonoidHom x z) :=
  frattiniAut_mk _ _

@[expose] noncomputable def nuP {P : Subgroup G} (hP : IsPGroup p ↥P) (x : normalizer (P : Set G)) :
    FMod P →* FMod P :=
  nuHom (FMod.comm hP) (fAct P x)

@[expose] def NQ {P : Subgroup G} (hP : IsPGroup p ↥P) (x : normalizer (P : Set G)) (z : ↥P) : Prop :=
  nuP hP x (QuotientGroup.mk z) ≠ 1

theorem nuP_mk {P : Subgroup G} (hP : IsPGroup p ↥P) (x : normalizer (P : Set G)) (z : ↥P) :
    nuP hP x (QuotientGroup.mk z) =
      QuotientGroup.mk ((z⁻¹ * P.normalizerMonoidHom x z)⁻¹ *
        P.normalizerMonoidHom x (z⁻¹ * P.normalizerMonoidHom x z)) := by
  rw [nuP, nuHom_apply, ← QuotientGroup.mk_inv, fAct_mk, ← QuotientGroup.mk_mul, fAct_mk,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]

theorem nuP_mk_eq {P : Subgroup G} (hP : IsPGroup p ↥P) {x : G} (hx : x ∈ normalizer (P : Set G))
    (z : ↥P) :
    ∃ hw : ⁅(⁅(z : G)⁻¹, x⁆)⁻¹, x⁆ ∈ P,
      nuP hP ⟨x, hx⟩ (QuotientGroup.mk z) = QuotientGroup.mk ⟨⁅(⁅(z : G)⁻¹, x⁆)⁻¹, x⁆, hw⟩ := by
  have hcoe : (((z⁻¹ * P.normalizerMonoidHom ⟨x, hx⟩ z)⁻¹ *
      P.normalizerMonoidHom ⟨x, hx⟩ (z⁻¹ * P.normalizerMonoidHom ⟨x, hx⟩ z) : ↥P) : G) =
      ⁅(⁅(z : G)⁻¹, x⁆)⁻¹, x⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
    group
  refine ⟨by rw [← hcoe]; exact (_ : ↥P).2, ?_⟩
  rw [nuP_mk]
  congr 1
  exact Subtype.ext hcoe

theorem exists_selection {P V : Subgroup G} (hP : IsPGroup p ↥P) (hp2 : p ≠ 2)
    (hVel : CFSG.IsElementaryAbelian 2 ↥V) (hrk : 3 ≤ pRank 2 ↥V)
    (hVN : V ≤ normalizer (P : Set G)) {x : G} (hx : x ∈ normalizer (P : Set G)) {z₀ : ↥P}
    (hz₀ : NQ hP ⟨x, hx⟩ z₀) :
    (∃ z : ↥P, (z : G) ∈ centralizer (V : Set G) ∧ NQ hP ⟨x, hx⟩ z) ∨
      (∃ F : Subgroup G, F ≤ V ∧ Nat.card V = 2 * Nat.card F ∧
        (∃ z : ↥P, (z : G) ∈ centralizer (F : Set G) ∧ NQ hP ⟨x, hx⟩ z) ∧
        ∀ z : ↥P, (z : G) ∈ centralizer (V : Set G) → ¬ NQ hP ⟨x, hx⟩ z) := by
  classical
  by_cases hα : ∃ z : ↥P, (z : G) ∈ centralizer (V : Set G) ∧ NQ hP ⟨x, hx⟩ z
  · exact Or.inl hα
  right
  have hα' : ∀ z : ↥P, (z : G) ∈ centralizer (V : Set G) → ¬ NQ hP ⟨x, hx⟩ z := by
    intro z hz hnq
    exact hα ⟨z, hz, hnq⟩
  by_contra hno
  let W : Subgroup ↥P := (nuP hP ⟨x, hx⟩).ker.comap (QuotientGroup.mk' (frattini ↥P))
  let WG : Subgroup G := W.map P.subtype
  have hmem : ∀ z : ↥P, (z : G) ∈ WG ↔ ¬ NQ hP ⟨x, hx⟩ z := by
    intro z
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Subtype.ext hwz
      subst this
      intro hnq
      exact hnq hw
    · intro hnq
      exact ⟨z, by simpa [W, NQ] using hnq, rfl⟩
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    intro h2
    have h2' : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans (dvd_refl _))
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).1 h2').symm
  have hle : ∀ F : Subgroup G, F ≤ V → pRank 2 ↥V - 1 ≤ pRank 2 ↥F → P ⊓ centralizer (F : Set G) ≤ WG := by
    intro F hFV hFrk g hg
    obtain ⟨hgP, hgF⟩ := hg
    have hF : CFSG.IsElementaryAbelian 2 ↥F := isElementaryAbelian_le hVel hFV
    have hcF := C3.Layer1.Back.card_eq_two_pow_pRank hF
    have hcV := C3.Layer1.Back.card_eq_two_pow_pRank hVel
    have hFV' : pRank 2 ↥F ≤ pRank 2 ↥V := C3.Layer1.Back.pRank_mono' hFV
    have := (hmem ⟨g, hgP⟩).2
    refine (hmem ⟨g, hgP⟩).2 ?_
    intro hnq
    rcases Nat.lt_or_ge (pRank 2 ↥F) (pRank 2 ↥V) with hlt | hge
    ·
      apply hno
      refine ⟨F, hFV, ?_, ⟨⟨g, hgP⟩, hgF, hnq⟩, hα'⟩
      have : pRank 2 ↥V = pRank 2 ↥F + 1 := by omega
      rw [hcV, hcF, this, pow_succ]
      ring
    ·
      have hFeq : pRank 2 ↥F = pRank 2 ↥V := le_antisymm hFV' hge
      have hFeqV : F = V := by
        refine Subgroup.eq_of_le_of_card_ge hFV ?_
        rw [hcV, hcF, hFeq]
      subst hFeqV
      exact hα ⟨⟨g, hgP⟩, hgF, hnq⟩
  have hPW : P ≤ WG := Th2.L83.le_of_forall_inf_centralizer_rank (pRank 2 ↥V - 1) hVel
    (by omega) hodd hVN hle
  exact (hmem z₀).1 (hPW z₀.2) hz₀

omit [Finite G] in
theorem fAct_mul_comm {P : Subgroup G} {x v : G} (hx : x ∈ normalizer (P : Set G))
    (hv : v ∈ normalizer (P : Set G)) (hxv : x * v = v * x) (m : FMod P) :
    fAct P ⟨x, hx⟩ (fAct P ⟨v, hv⟩ m) = fAct P ⟨v, hv⟩ (fAct P ⟨x, hx⟩ m) := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective m
  rw [fAct_mk, fAct_mk, fAct_mk, fAct_mk]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  calc x * (v * (z : G) * v⁻¹) * x⁻¹ = (x * v) * (z : G) * (x * v)⁻¹ := by group
    _ = (v * x) * (z : G) * (v * x)⁻¹ := by rw [hxv]
    _ = v * (x * (z : G) * x⁻¹) * v⁻¹ := by group

omit [Finite G] in
theorem fAct_involutive {P : Subgroup G} {v : G} (hv : v ∈ normalizer (P : Set G)) (hv2 : v * v = 1)
    (m : FMod P) : fAct P ⟨v, hv⟩ (fAct P ⟨v, hv⟩ m) = m := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective m
  rw [fAct_mk, fAct_mk]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [this]
  calc v * (v * (z : G) * v) * v = (v * v) * (z : G) * (v * v) := by group
    _ = z := by rw [hv2]; group

theorem eq_of_sq_eq_of_odd {M : Type*} [Group M] [Finite M] (hc : ∀ a b : M, a * b = b * a)
    (hodd : Odd (Nat.card M)) {a b : M} (h : a ^ 2 = b ^ 2) : a = b := by
  have h1 : (a * b⁻¹) ^ 2 = 1 := by
    have : (a * b⁻¹) ^ 2 = a ^ 2 * (b ^ 2)⁻¹ := by
      rw [pow_two, pow_two, pow_two]
      calc a * b⁻¹ * (a * b⁻¹) = a * a * (b⁻¹ * b⁻¹) := by
            rw [mul_assoc, ← mul_assoc b⁻¹ a b⁻¹, hc b⁻¹ a, mul_assoc, ← mul_assoc]
        _ = a * a * (b * b)⁻¹ := by rw [mul_inv_rev]
    rw [this, h, mul_inv_cancel]
  have h2 : orderOf (a * b⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (a * b⁻¹) ∣ Nat.card M := orderOf_dvd_natCard _
  have h4 : orderOf (a * b⁻¹) = 1 := by
    have hcop : Nat.Coprime 2 (Nat.card M) := Nat.coprime_two_left.2 hodd
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3
  exact mul_inv_eq_one.1 (orderOf_eq_one_iff.1 h4)

theorem exists_fixed_nq {P X₀ : Subgroup G} (hP : IsPGroup p ↥P) (hp2 : p ≠ 2)
    {x v : G} (hx : x ∈ normalizer (P : Set G)) (hv : v ∈ normalizer (P : Set G))
    (hv2 : v * v = 1) (hxv : x * v = v * x) (hvX : ∀ z ∈ X₀, v * z * v⁻¹ ∈ X₀)
    {z₀ : ↥P} (hz₀X : (z₀ : G) ∈ X₀) (hnq : NQ hP ⟨x, hx⟩ z₀)
    (hfix : fAct P ⟨v, hv⟩ (nuP hP ⟨x, hx⟩ (QuotientGroup.mk z₀)) =
      nuP hP ⟨x, hx⟩ (QuotientGroup.mk z₀)) :
    ∃ z : ↥P, (z : G) ∈ X₀ ∧ v * z * v⁻¹ = z ∧ NQ hP ⟨x, hx⟩ z := by
  classical
  have hMc := FMod.comm hP
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    exact Odd.pow (Nat.Prime.odd_of_ne_two Fact.out hp2)
  have hModd : Odd (Nat.card (FMod P)) := by
    have : Nat.card (FMod P) ∣ Nat.card P :=
      Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (frattini ↥P))
        (QuotientGroup.mk'_surjective _)
    exact Odd.of_dvd_nat hodd this
  obtain ⟨α, hα⟩ : ∃ α : MulAut (FMod P), α = fAct P ⟨v, hv⟩ := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : FMod P →* FMod P, ν = nuP hP ⟨x, hx⟩ := ⟨_, rfl⟩
  rw [← hα, ← hν] at hfix
  have hνα : ∀ m, ν (α m) = α (ν m) := fun m => by
    rw [hν, hα]
    exact nuHom_comm (FMod.comm hP) (fAct P ⟨x, hx⟩) (fAct P ⟨v, hv⟩)
      (fun m => fAct_mul_comm hx hv hxv m) m
  have hαα : ∀ m, α (α m) = m := fun m => by rw [hα]; exact fAct_involutive hv hv2 m
  obtain ⟨zb, hzb⟩ : ∃ zb : ↥P, zb = z₀ * P.normalizerMonoidHom ⟨v, hv⟩ z₀ := ⟨_, rfl⟩
  have hzbX : (zb : G) ∈ X₀ := by
    have : (zb : G) = (z₀ : G) * (v * (z₀ : G) * v⁻¹) := by
      simp [hzb, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this]
    exact X₀.mul_mem hz₀X (hvX _ hz₀X)
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.card P := ⟨_, rfl⟩
  have hodd' : Odd n := hn ▸ hodd
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ↥P, z₁ = zb ^ ((n + 1) / 2) := ⟨_, rfl⟩
  have hz₁X : (z₁ : G) ∈ X₀ := by
    have : (z₁ : G) = (zb : G) ^ ((n + 1) / 2) := by simp [hz₁]
    rw [this]
    exact X₀.pow_mem hzbX _
  have hz₁sq : z₁ ^ 2 = zb := by
    rw [hz₁, ← pow_mul]
    obtain ⟨k, hk⟩ := hodd'
    have h2 : 2 * ((n + 1) / 2) = n + 1 := by omega
    rw [mul_comm, h2, pow_succ, hn, pow_card_eq_one', one_mul]
  have hmzb : (QuotientGroup.mk zb : FMod P) = QuotientGroup.mk z₀ * α (QuotientGroup.mk z₀) := by
    rw [hzb, QuotientGroup.mk_mul, hα, fAct_mk]
  have hαzb : α (QuotientGroup.mk zb : FMod P) = QuotientGroup.mk zb := by
    rw [hmzb, map_mul, hαα, hMc]
  have hαz₁ : α (QuotientGroup.mk z₁ : FMod P) = QuotientGroup.mk z₁ := by
    rw [hz₁, QuotientGroup.mk_pow, map_pow, hαzb]
  have hν₁ : ν (QuotientGroup.mk z₁) = ν (QuotientGroup.mk z₀) := by
    have hsq : ν (QuotientGroup.mk z₁) ^ 2 = ν (QuotientGroup.mk z₀) ^ 2 := by
      have e1 : (QuotientGroup.mk z₁ : FMod P) ^ 2 = QuotientGroup.mk zb := by
        rw [← QuotientGroup.mk_pow, hz₁sq]
      calc ν (QuotientGroup.mk z₁) ^ 2 = ν ((QuotientGroup.mk z₁) ^ 2) := (map_pow ν _ 2).symm
        _ = ν (QuotientGroup.mk zb) := by rw [e1]
        _ = ν (QuotientGroup.mk z₀ * α (QuotientGroup.mk z₀)) := by rw [hmzb]
        _ = ν (QuotientGroup.mk z₀) * α (ν (QuotientGroup.mk z₀)) := by rw [map_mul, hνα]
        _ = ν (QuotientGroup.mk z₀) ^ 2 := by rw [hfix, pow_two]
    exact eq_of_sq_eq_of_odd hMc hModd hsq
  let Φ : Subgroup G := (frattini ↥P).map P.subtype
  let O : Subgroup G := Φ ⊓ X₀
  have hOP : O ≤ P := fun g hg => by
    obtain ⟨g', -, rfl⟩ := hg.1
    exact g'.2
  have hOodd : ¬ 2 ∣ Nat.card O := by
    intro h2
    have h3 : Nat.card O ∣ Nat.card P := Subgroup.card_dvd_of_le hOP
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans h3))
  have hmap := Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (frattini ↥P).Characteristic) (P.normalizerMonoidHom ⟨v, hv⟩)
  have hvΦ : ∀ g ∈ Φ, v * g * v⁻¹ ∈ Φ := by
    rintro _ ⟨g', hg', rfl⟩
    refine ⟨P.normalizerMonoidHom ⟨v, hv⟩ g', ?_, by simp [Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hg'
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvN : v ∈ normalizer (O : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact ⟨hvΦ g hg.1, hvX g hg.2⟩
    · intro hg
      have h1 := hvΦ _ hg.1
      have h2 := hvX _ hg.2
      have e : v * (v * g * v⁻¹) * v⁻¹ = g := by
        rw [hvinv]
        calc v * (v * g * v) * v = (v * v) * g * (v * v) := by group
          _ = g := by rw [hv2]; group
      rw [e] at h1 h2
      exact ⟨h1, h2⟩
  have hFO : ∀ f ∈ Subgroup.zpowers v, ∀ o ∈ O, f * o * f⁻¹ ∈ O := by
    intro f hf o ho
    have hfN : f ∈ normalizer (O : Set G) := (Subgroup.zpowers_le.2 hvN) hf
    exact (Subgroup.mem_normalizer_iff.1 hfN o).1 ho
  have hvfix : (z₁ : G)⁻¹ * (v * (z₁ : G) * v⁻¹) ∈ O := by
    refine ⟨?_, X₀.mul_mem (X₀.inv_mem hz₁X) (hvX _ hz₁X)⟩
    have h1 : (QuotientGroup.mk (P.normalizerMonoidHom ⟨v, hv⟩ z₁) : FMod P) = QuotientGroup.mk z₁ := by
      rw [← fAct_mk, ← hα]; exact hαz₁
    have h2 := (frattini ↥P).inv_mem (QuotientGroup.eq.1 h1)
    refine ⟨z₁⁻¹ * P.normalizerMonoidHom ⟨v, hv⟩ z₁, by simpa using h2, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hk : ∀ f ∈ Subgroup.zpowers v, (z₁ : G)⁻¹ * (f * (z₁ : G) * f⁻¹) ∈ O := by
    intro f hf
    by_cases hv1 : v = 1
    · subst hv1
      have : f = 1 := by simpa using hf
      subst this
      simp only [one_mul, inv_one, mul_one, inv_mul_cancel]
      exact O.one_mem
    · have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
      rcases mem_zpowers_two hvo hf with rfl | rfl
      · simp only [one_mul, inv_one, mul_one, inv_mul_cancel]
        exact O.one_mem
      · exact hvfix
  have hF : IsPGroup 2 ↥(Subgroup.zpowers v) := by
    by_cases hv1 : v = 1
    · subst hv1
      intro g
      refine ⟨0, ?_⟩
      obtain ⟨g, hg⟩ := g
      have : g = 1 := by simpa using hg
      subst this
      exact Subtype.ext (by simp)
    · have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvo]; norm_num)
  obtain ⟨o, ho, hofix⟩ := Th2.L83.exists_fixed_mem_coset hOodd hF hFO hk
  have hoP : o ∈ P := hOP ho
  refine ⟨z₁ * ⟨o, hoP⟩, ?_, ?_, ?_⟩
  · have : ((z₁ * ⟨o, hoP⟩ : ↥P) : G) = (z₁ : G) * o := rfl
    rw [this]
    exact X₀.mul_mem hz₁X ho.2
  · have := hofix v (Subgroup.mem_zpowers v)
    simpa using this
  · intro h1
    apply hnq
    have hmko : (QuotientGroup.mk ⟨o, hoP⟩ : FMod P) = 1 := by
      obtain ⟨o', ho', hoo'⟩ := ho.1
      have : (⟨o, hoP⟩ : ↥P) = o' := Subtype.ext hoo'.symm
      rw [this]
      exact (QuotientGroup.eq_one_iff _).2 ho'
    have e2 : ν (QuotientGroup.mk (z₁ * ⟨o, hoP⟩)) = ν (QuotientGroup.mk z₁) := by
      rw [QuotientGroup.mk_mul, hmko, mul_one]
    rw [hν] at hν₁ e2
    show nuP hP ⟨x, hx⟩ (QuotientGroup.mk z₀) = 1
    rw [← hν₁, ← e2]
    exact h1

end FrattiniModule

end CFSG.GH74.GLS.Th2.Obs
