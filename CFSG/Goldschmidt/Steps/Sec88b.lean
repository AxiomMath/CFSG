module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87a
import CFSG.Goldschmidt.Steps.Sec87b
import CFSG.Goldschmidt.Steps.Sec87f
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem commutator_le_of_invariant {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) {r : G}
    (hrR : r ∈ Subgroup.normalizer (R : Set G))
    (hX : ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) →
      r ∈ Subgroup.normalizer (X : Set G) → X ≤ A ∨ X = R) :
    ⁅R, R⁆ ≤ A := by
  rcases hX ⁅R, R⁆ (commutator_self_le R) (fun y hy => mem_normalizer_commutator
    (Subgroup.le_normalizer hy)) (mem_normalizer_commutator hrR) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsPerfect R := Subgroup.isPerfect_iff.mpr h
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    exact Group.IsPerfect.not_isNilpotent R hR2.isNilpotent

theorem sq_mem_of_invariant {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRA : R ≤ Subgroup.centralizer (A : Set G)) (hRR : ⁅R, R⁆ ≤ A) (hRA' : ¬ R ≤ A) {r : G}
    (hrR : r ∈ Subgroup.normalizer (R : Set G)) (hrA : r ∈ Subgroup.centralizer (A : Set G))
    (hX : ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) →
      r ∈ Subgroup.normalizer (X : Set G) → X ≤ A ∨ X = R) :
    ∀ y ∈ R, y ^ 2 ∈ A := by
  classical
  have hc : ∀ y ∈ R, ∀ z ∈ R, y⁻¹ * z * y * z⁻¹ ∈ A := fun y hy z hz => by
    have := hRR (Subgroup.commutator_mem_commutator (R.inv_mem hy) hz)
    rwa [commutatorElement_def, inv_inv] at this
  let X : Subgroup G :=
    { carrier := {y | y ∈ R ∧ y ^ 2 ∈ A}
      mul_mem' := fun {y z} hy hz => ⟨R.mul_mem hy.1 hz.1, by
        have e : (y * z) ^ 2 = y ^ 2 * (y⁻¹ * z * y * z⁻¹) * z ^ 2 := by
          rw [sq, sq, sq]
          group
        rw [e]
        exact A.mul_mem (A.mul_mem hy.2 (hc y hy.1 z hz.1)) hz.2⟩
      one_mem' := ⟨R.one_mem, by rw [one_pow]; exact A.one_mem⟩
      inv_mem' := fun {y} hy => ⟨R.inv_mem hy.1, by rw [inv_pow]; exact A.inv_mem hy.2⟩ }
  have hconj : ∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.centralizer (A : Set G) →
      g ∈ Subgroup.normalizer (X : Set G) := fun g hgR hgA =>
    mem_normalizer_of_conj_le fun y hy => by
      refine ⟨by simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgR) y).mp hy.1,
        ?_⟩
      have e : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by
        have := conj_pow (a := g⁻¹) (b := y) (i := 2)
        rwa [inv_inv] at this
      have hgy : y ^ 2 * g = g * y ^ 2 := Subgroup.mem_centralizer_iff.mp hgA _ hy.2
      rw [e, mul_assoc, hgy, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hy.2
  rcases hX X (fun y hy => hy.1) (fun g hg => hconj g (Subgroup.le_normalizer hg) (hRA hg))
    (hconj r hrR hrA) with h | h
  · exfalso
    obtain ⟨y, hyR, hyA⟩ := IsConcreteLE.not_le_iff_exists.mp hRA'
    obtain ⟨k, hk⟩ := hR2 ⟨y, hyR⟩
    have hex : ∃ n : ℕ, y ^ (2 ^ n) ∈ A := ⟨k, by
      have := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [this]
      exact A.one_mem⟩
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, pow_one] at this
      exact hyA this
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    apply Nat.find_min hex (show m < Nat.find hex by omega)
    refine h ⟨R.pow_mem hyR _, ?_⟩
    rw [← pow_mul, ← pow_succ, ← hm]
    exact Nat.find_spec hex
  · intro y hy
    have : y ∈ X := h ▸ hy
    exact this.2

theorem card_le_32 (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p P)
    (hbP : ∀ x ∈ P, b⁻¹ * x * b = x⁻¹) (hrank : CFSG.Open.pRank p P = 2) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hAR : A ≤ R) (hRA : R ≤ Subgroup.centralizer (A : Set G))
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hRR : A ≤ ⁅R, R⁆)
    (huniq : ∀ t ∈ R ⊓ Subgroup.centralizer (P : Set G), t ^ 2 = 1 → t = 1 ∨ t = a) {r : G}
    (hrR : r ∈ Subgroup.normalizer (R : Set G)) (hrA : r ∈ Subgroup.centralizer (A : Set G))
    (hrP : r ∈ Subgroup.normalizer (P : Set G))
    (hX : ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) →
      r ∈ Subgroup.normalizer (X : Set G) → X ≤ A ∨ X = R) :
    Nat.card R ≤ 32 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcard
  push Not at hcard
  set C := Subgroup.centralizer (P : Set G) with hC
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => comm_of_inv hbP hx hy
  obtain ⟨V, hVP, hVab, hVp, hVc, hVall⟩ := exists_omega1 hp hPab hrank
  have hNV : ∀ s ∈ Subgroup.normalizer (P : Set G), s ∈ Subgroup.normalizer (V : Set G) :=
    fun s hs => mem_normalizer_of_conj_le fun v hv => by
      have h1 : s⁻¹ * v * s ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) v).mp (hVP hv)
      refine hVall _ h1 ?_
      have h2 := conj_pow (a := s⁻¹) (b := v) (i := p)
      rw [inv_inv, hVp v hv] at h2
      rw [h2]
      group
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := fun y hy => hNV y (hRP hy)
  obtain ⟨δ, hδ⟩ := exists_det hp2 hVab hVp hVc
  have hRA' : ¬ R ≤ A := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  have hR1 : R ≠ ⊥ := fun h => hRA' (h ▸ bot_le)
  have hsq := sq_mem_of_invariant hR2 hRA (commutator_le_of_invariant hR2 hR1 hrR hX) hRA'
    hrR hrA hX
  have hbR : b ∈ R := hAR hb
  have hb2 : b * b = 1 := mul_self_eq_one hA hb
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbC : b ∉ C := by
    intro hbc
    obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hall
      push Not at hall
      have : V = ⊥ := eq_bot_iff.mpr fun v hv => Subgroup.mem_bot.mpr (hall v hv)
      rw [this, Subgroup.card_bot] at hVc
      have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    have hcomm : v * b = b * v := Subgroup.mem_centralizer_iff.mp hbc v (hVP hvV)
    have h1 := hbP v (hVP hvV)
    have h2 : b⁻¹ * v * b = v := by rw [mul_assoc, hcomm]; group
    rw [h2] at h1
    have hv2 : v * v = 1 := (congrArg (v * ·) h1).trans (mul_inv_cancel v)
    exact hv1 (eq_one_of_pow_two_of_odd (K := V) (by rw [hVc]; exact (hp.odd_of_ne_two hp2).pow)
      hvV (k := 1) (by rw [pow_one, sq]; exact hv2))
  have hRC : ∀ t ∈ R ⊓ C, t = 1 ∨ t = a := by
    have hle : R ⊓ C ≤ A := by
      rcases hX (R ⊓ C) inf_le_left (fun y hy => mem_normalizer_inf (Subgroup.le_normalizer hy)
        (normalizer_le_normalizer_centralizer P (hRP hy)))
        (mem_normalizer_inf hrR (normalizer_le_normalizer_centralizer P hrP)) with h | h
      · exact h
      · exfalso
        have : b ∈ R ⊓ C := by rw [h]; exact hbR
        exact hbC this.2
    exact fun t ht => huniq t ht (hA.2 t (hle ht))
  have hδR : ∀ y (hy : y ∈ R), δ ⟨y, hRV hy⟩ = 1 ∨ δ ⟨y, hRV hy⟩ = -1 := by
    intro y hy
    refine mul_self_eq_one_iff.mp ?_
    rw [← map_mul]
    have e : (⟨y, hRV hy⟩ * ⟨y, hRV hy⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨y ^ 2, hRV (hAR (hsq y hy))⟩ := Subtype.ext (sq y).symm
    rw [e]
    exact det_eq_one_of_mem_commutator δ hRV (hRR (hsq y hy)) _
  have hbu : ∀ u ∈ R, b * u = u * b := fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hRA hu) b hb
  have hbV : ∀ v ∈ V, b * v * b⁻¹ = v⁻¹ := fun v hv => by
    have h := hbP v (hVP hv)
    rw [hbi] at h ⊢
    exact h
  have hpm : ∀ y ∈ R, y ^ 2 ∈ C →
      ((∀ v ∈ V, y * v * y⁻¹ = v) ∨ (∀ v ∈ V, y * v * y⁻¹ = v⁻¹)) → y ∈ C ∨ b * y ∈ C := by
    intro y hy hy2 h
    rcases h with h | h
    · exact Or.inl (mem_centralizer_of_forall_eq hp hp2 hPp hVall (hRP hy) hy2 h)
    · refine Or.inr (mem_centralizer_of_forall_eq hp hp2 hPp hVall (hRP (R.mul_mem hbR hy)) ?_
        fun v hv => ?_)
      · have e : (b * y) ^ 2 = y ^ 2 := by
          rw [sq, sq]
          calc b * y * (b * y) = b * (y * b) * y := by group
            _ = b * (b * y) * y := by rw [hbu y hy]
            _ = (b * b) * (y * y) := by group
            _ = y * y := by rw [hb2, one_mul]
        rw [e]
        exact hy2
      · calc b * y * v * (b * y)⁻¹ = b * (y * v * y⁻¹) * b⁻¹ := by group
          _ = (b * v * b⁻¹)⁻¹ := by rw [h v hv]; group
          _ = v := by rw [hbV v hv, inv_inv]
  have hsqV : ∀ y ∈ R, y ^ 2 ∈ C → ∀ v ∈ V, y * (y * v * y⁻¹) * y⁻¹ = v := fun y _ hy2 v hv => by
    have h := Subgroup.mem_centralizer_iff.mp hy2 v (hVP hv)
    calc y * (y * v * y⁻¹) * y⁻¹ = y ^ 2 * v * (y ^ 2)⁻¹ := by rw [sq]; group
      _ = v := by rw [← h]; group
  let φ : R →* (ZMod p)ˣ := (δ.comp (Subgroup.inclusion hRV)).toHomUnits
  have hφ : ∀ y : R, ((φ y : (ZMod p)ˣ) : ZMod p) = δ ⟨y, hRV y.2⟩ := fun y => rfl
  have hrange : Nat.card φ.range ≤ 2 := by
    refine (Subgroup.card_le_of_le (K := rootsOfUnity 2 (ZMod p)) ?_).trans
      (card_rootsOfUnity (ZMod p) 2)
    rintro _ ⟨y, rfl⟩
    rw [mem_rootsOfUnity', hφ]
    rcases hδR y y.2 with h | h
    · rw [h, one_pow]
    · rw [h]
      exact neg_one_sq
  set R₁ := φ.ker.map R.subtype with hR₁
  have hR₁R : R₁ ≤ R := Subgroup.map_subtype_le _
  have hmemR₁ : ∀ y (hy : y ∈ R), δ ⟨y, hRV hy⟩ = 1 → y ∈ R₁ := fun y hy h =>
    ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr (Units.ext (by rw [hφ, Units.val_one]; exact h)), rfl⟩
  have hδR₁ : ∀ y (hy : y ∈ R₁), δ ⟨y, hRV (hR₁R hy)⟩ = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have := congrArg Units.val (MonoidHom.mem_ker.mp hz)
    rw [hφ, Units.val_one] at this
    exact this
  have hcardR : Nat.card R ≤ 2 * Nat.card R₁ := by
    have h3 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h3
    rw [hR₁, Subgroup.card_map_of_injective R.subtype_injective]
    calc Nat.card R = Nat.card φ.ker * Nat.card φ.range := h3.symm
      _ ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ hrange
      _ = 2 * Nat.card φ.ker := mul_comm _ _
  set K := R₁ ⊓ C with hK
  have hKR₁ : K ≤ R₁ := inf_le_left
  have hK2 : Nat.card K ≤ 2 := by
    have hle : K ≤ Subgroup.zpowers a := fun t ht => by
      rcases hRC t ⟨hR₁R ht.1, ht.2⟩ with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (hA.2 a ha)
  have hR₁K : R₁ ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    mem_normalizer_inf (Subgroup.le_normalizer hy)
      (normalizer_le_normalizer_centralizer P (hRP (hR₁R hy)))
  have hnormal : (K.subgroupOf R₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKR₁).mpr hR₁K
  have hbR₁ : b ∈ R₁ := hmemR₁ b hbR (det_eq_one_of_mem_commutator δ hRV (hRR hb) _)
  have hord2 : ∀ {X : Type} [Group X] (y : X), orderOf y = 2 → y ^ 2 = 1 := fun y hy => by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hord1 : ∀ {X : Type} [Group X] (y : X), orderOf y = 2 → y ≠ 1 := fun y hy h => by
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hQ8 : Nat.card (R₁ ⧸ K.subgroupOf R₁) ≤ 8 := by
    have hQinv : ∀ q : R₁ ⧸ K.subgroupOf R₁, orderOf q = 2 →
        q = (QuotientGroup.mk (⟨b, hbR₁⟩ : R₁))⁻¹ := by
      intro q hq
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hy2 : (y : G) ^ 2 ∈ K := by
        have := hord2 _ hq
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
        simpa using this
      have hyK : (y : G) ∉ K := fun h => hord1 _ hq (by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h)
      have hyR : (y : G) ∈ R := hR₁R y.2
      rcases hpm y hyR hy2.2 (hδ ⟨y, hRV hyR⟩ (hsqV y hyR hy2.2) (hδR₁ y y.2)) with h | h
      · exact absurd ⟨y.2, h⟩ hyK
      · rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        show (y : G) * b ∈ K
        rw [← hbu y hyR]
        exact ⟨R₁.mul_mem hbR₁ y.2, h⟩
    refine card_le_eight ((hR2.to_le hR₁R).to_quotient _) (fun q q' hq hq' =>
      (hQinv q hq).trans (hQinv q' hq').symm) fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy4 : y ^ 4 = 1 := Subtype.ext (by
      show (y : G) ^ 4 = 1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact hA.2 _ (hsq y (hR₁R y.2)))
    rw [← QuotientGroup.mk_pow, hy4]
    rfl
  have hR₁card : Nat.card R₁ = Nat.card (R₁ ⧸ K.subgroupOf R₁) * Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf R₁),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR₁).toEquiv]
  have : Nat.card R ≤ 32 := by
    calc Nat.card R ≤ 2 * Nat.card R₁ := hcardR
      _ = 2 * (Nat.card (R₁ ⧸ K.subgroupOf R₁) * Nat.card K) := by rw [hR₁card]
      _ ≤ 2 * (8 * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ8 hK2)
  omega

end CFSG.Goldschmidt.Sec8
