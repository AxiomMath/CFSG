module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Root

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

section NormOne

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem two_le_q : 2 ≤ p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : p ^ f ≤ 1 := by omega
  have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
  omega

omit hF in
theorem unitaryInvolution_of_mem {ν : Fˣ} (hν : ν ∈ rootsOfUnity (p ^ f + 1) F) :
    unitaryInvolution F p f (ν : F) = ((ν⁻¹ : Fˣ) : F) := by
  rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
  congr 1
  have h := (mem_rootsOfUnity _ _).1 hν
  rw [pow_succ] at h
  exact eq_inv_of_mul_eq_one_left h

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem card_rootsOfUnity_q : Nat.card (rootsOfUnity (p ^ f + 1) F) = p ^ f + 1 := by
  have hq := two_le_q hF
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = (p ^ f - 1) * (p ^ f + 1) := by
    rw [Nat.card_units, hF]
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hdvd : p ^ f - 1 ∣ orderOf g := by rw [hg, hcard]; exact dvd_mul_right _ _
  have hne : p ^ f - 1 ≠ 0 := by omega
  have hord : orderOf (g ^ (p ^ f - 1)) = p ^ f + 1 := by
    rw [orderOf_pow_of_dvd hne hdvd, hg, hcard, Nat.mul_div_cancel_left _ (by omega)]
  exact (hord ▸ IsPrimitiveRoot.orderOf (g ^ (p ^ f - 1))).card_rootsOfUnity'

omit hF [Field F] [Finite F] [Fact (Nat.Prime p)] in
theorem coprime_three (hq3 : p ^ f % 3 = 1) : Nat.Coprime 3 (p ^ f + 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
  omega

omit hF [Finite F] [CharP F p] [Fact (Nat.Prime p)] in
theorem exists_cube (hq3 : p ^ f % 3 = 1) {ν : Fˣ} (hν : ν ∈ rootsOfUnity (p ^ f + 1) F) :
    ∃ μ ∈ rootsOfUnity (p ^ f + 1) F, μ ^ 3 = ν := by
  let φ : rootsOfUnity (p ^ f + 1) F →* rootsOfUnity (p ^ f + 1) F := powMonoidHom 3
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h3 : x ^ 3 = 1 := hx
    have hq : x ^ (p ^ f + 1) = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact (mem_rootsOfUnity _ _).1 x.2)
    have := pow_gcd_eq_one.2 ⟨h3, hq⟩
    rw [coprime_three hq3] at this
    simpa using this
  obtain ⟨μ, hμ⟩ := Finite.surjective_of_injective hinj ⟨ν, hν⟩
  exact ⟨μ, μ.2, congrArg Subtype.val hμ⟩

end NormOne

@[expose] noncomputable def multipliers (A : AddSubgroup F) : Subfield F where
  carrier := {r | ∀ a ∈ A, r * a ∈ A}
  zero_mem' := fun a _ => by rw [zero_mul]; exact A.zero_mem
  one_mem' := fun a ha => by rwa [one_mul]
  add_mem' := fun hr hs a ha => by rw [add_mul]; exact A.add_mem (hr a ha) (hs a ha)
  neg_mem' := fun hr a ha => by rw [neg_mul]; exact A.neg_mem (hr a ha)
  mul_mem' := fun hr hs a ha => by rw [mul_assoc]; exact hr _ (hs a ha)
  inv_mem' := by
    intro r hr
    have hpow : ∀ n : ℕ, ∀ a ∈ A, r ^ n * a ∈ A := by
      intro n
      induction n with
      | zero => intro a ha; rwa [pow_zero, one_mul]
      | succ n ih => intro a ha; rw [pow_succ, mul_assoc]; exact ih _ (hr a ha)
    by_cases h0 : r = 0
    · intro a ha; rw [h0, _root_.inv_zero, zero_mul]; exact A.zero_mem
    · have := Fintype.ofFinite F
      have hc : r ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one r h0
      have hc2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have e : r⁻¹ = r ^ (Fintype.card F - 2) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega, hc]
      intro a ha
      rw [e]
      exact hpow _ a ha


variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem ca_tSU_conj_of_mem {μ : Fˣ} (hμ : μ ∈ rootsOfUnity (p ^ f + 1) F)
    {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    ca (tSU hF μ * x * (tSU hF μ)⁻¹) = ((μ ^ 3 : Fˣ) : F) * ca x := by
  rw [ca_tSU_conj hF μ hx]
  have hq := two_le_q hF
  have h := (mem_rootsOfUnity _ _).1 hμ
  have e : (μ ^ (p ^ f - 1))⁻¹ = μ ^ 2 := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_add, ← h]
    congr 1
    omega
  rw [e]
  push_cast
  ring

theorem cb_tSU_conj_of_mem {μ : Fˣ} (hμ : μ ∈ rootsOfUnity (p ^ f + 1) F)
    {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    cb (tSU hF μ * x * (tSU hF μ)⁻¹) = cb x := by
  rw [cb_tSU_conj hF μ hx]
  have h := (mem_rootsOfUnity _ _).1 hμ
  have e : (μ : F) * ((μ ^ (p ^ f) : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, ← pow_succ', h, Units.val_one]
  linear_combination cb x * e

theorem ca_inv {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    ca x⁻¹ = -ca x := by
  have h := ca_mul hF hx ((rootU hF).inv_mem hx)
  rw [mul_inv_cancel, ca_one] at h
  linear_combination -h

theorem cb_inv_of_ca_eq_zero {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF)
    (ha : ca x = 0) : cb x⁻¹ = -cb x := by
  have h := cb_mul hF hx ((rootU hF).inv_mem hx)
  rw [mul_inv_cancel, cb_one, ha, zero_mul, sub_zero] at h
  linear_combination -h

theorem ca_commutator {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF)
    (hy : y ∈ rootU hF) : ca (x * y * x⁻¹ * y⁻¹) = 0 := by
  have hU := rootU hF
  have hxi := (rootU hF).inv_mem hx
  have hyi := (rootU hF).inv_mem hy
  rw [ca_mul hF ((rootU hF).mul_mem ((rootU hF).mul_mem hx hy) hxi) hyi,
    ca_mul hF ((rootU hF).mul_mem hx hy) hxi, ca_mul hF hx hy, ca_inv hF hx, ca_inv hF hy]
  ring

theorem cb_commutator {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF)
    (hy : y ∈ rootU hF) :
    cb (x * y * x⁻¹ * y⁻¹) = ca y * unitaryInvolution F p f (ca x) -
      ca x * unitaryInvolution F p f (ca y) := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcU : c ∈ rootU hF := (rootU hF).mul_mem ((rootU hF).mul_mem ((rootU hF).mul_mem hx hy)
    ((rootU hF).inv_mem hx)) ((rootU hF).inv_mem hy)
  have hyx : c * (y * x) = x * y := by rw [hc]; group
  have h := congrArg cb hyx
  rw [cb_mul hF hcU ((rootU hF).mul_mem hy hx), ca_commutator hF hx hy, zero_mul, sub_zero,
    cb_mul hF hy hx, cb_mul hF hx hy] at h
  linear_combination h

@[expose] noncomputable def zSet (S : Subgroup (SU (unitaryInvolution F p f) 3))
    (hSU : S ≤ rootU hF) : AddSubgroup F where
  carrier := {b | ∃ x ∈ S, ca x = 0 ∧ cb x = b}
  zero_mem' := ⟨1, S.one_mem, ca_one, cb_one⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, hxa, rfl⟩ ⟨y, hy, hya, rfl⟩
    refine ⟨x * y, S.mul_mem hx hy, ?_, ?_⟩
    · rw [ca_mul hF (hSU hx) (hSU hy), hxa, hya, add_zero]
    · rw [cb_mul hF (hSU hx) (hSU hy), hxa, zero_mul, sub_zero]
  neg_mem' := by
    rintro _ ⟨x, hx, hxa, rfl⟩
    refine ⟨x⁻¹, S.inv_mem hx, ?_, ?_⟩
    · rw [ca_inv hF (hSU hx), hxa, neg_zero]
    · exact cb_inv_of_ca_eq_zero hF (hSU hx) hxa

@[expose] noncomputable def aSet (S : Subgroup (SU (unitaryInvolution F p f) 3))
    (hSU : S ≤ rootU hF) : AddSubgroup F where
  carrier := {a | ∃ x ∈ S, ca x = a}
  zero_mem' := ⟨1, S.one_mem, ca_one⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, ca_mul hF (hSU hx) (hSU hy)⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, ca_inv hF (hSU hx)⟩

omit hF in
theorem sub_inv_mem_traceZero {ν : Fˣ} (hν : ν ∈ rootsOfUnity (p ^ f + 1) F) :
    (ν : F) - ((ν⁻¹ : Fˣ) : F) ∈ traceZero (unitaryInvolution F p f) := by
  rw [mem_traceZero, map_sub, unitaryInvolution_of_mem hν,
    unitaryInvolution_of_mem (inv_mem hν), inv_inv]
  ring

omit [Finite F] [Fact p.Prime] [CharP F p] hF in
theorem eq_or_eq_of_sub_inv_eq {ν ν' : F} (hν : ν ≠ 0) (hν' : ν' ≠ 0)
    (h : ν - ν⁻¹ = ν' - ν'⁻¹) : ν' = ν ∨ ν' = -ν⁻¹ := by
  have h1 : (ν - ν') * (ν * ν' + 1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · left; linear_combination -h2
  · right; field_simp; linear_combination h2

theorem eq_traceZero_of_le {V : AddSubgroup F} (hV : V ≤ traceZero (unitaryInvolution F p f))
    (hmem : ∀ ν ∈ rootsOfUnity (p ^ f + 1) F, (ν : F) - ((ν⁻¹ : Fˣ) : F) ∈ V) :
    V = traceZero (unitaryInvolution F p f) := by
  classical
  by_contra hne
  have hlt : V < traceZero (unitaryInvolution F p f) := lt_of_le_of_ne hV hne
  have hcardT : Nat.card (traceZero (unitaryInvolution F p f)) = p ^ f := card_traceZero hF
  have hcard_lt := AddSubgroup.card_lt_of_lt hlt
  have hdvd := AddSubgroup.card_dvd_of_le hV
  rw [hcardT] at hcard_lt hdvd
  obtain ⟨k, hk, hVk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have hkf : k < f := by
    by_contra h
    have : p ^ f ≤ p ^ k := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    omega
  have h2V : 2 * Nat.card V ≤ p ^ f := by
    rw [hVk]
    calc 2 * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right _ (Fact.out : p.Prime).two_le
      _ = p ^ (k + 1) := by ring
      _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (rootsOfUnity (p ^ f + 1) F)
  have := Fintype.ofFinite V
  let φ : rootsOfUnity (p ^ f + 1) F → F := fun ν => ((ν : Fˣ) : F) - (((ν : Fˣ)⁻¹ : Fˣ) : F)
  have hfib : ∀ c ∈ (Finset.univ : Finset (rootsOfUnity (p ^ f + 1) F)).image φ,
      (Finset.univ.filter fun ν => φ ν = c).card ≤ 2 := by
    intro c hc
    obtain ⟨ν₀, -, rfl⟩ := Finset.mem_image.1 hc
    have hsub : ((Finset.univ.filter fun ν => φ ν = φ ν₀).map
        ⟨fun ν : rootsOfUnity (p ^ f + 1) F => ((ν : Fˣ) : F), fun a b h =>
          Subtype.ext (Units.ext h)⟩) ⊆ {((ν₀ : Fˣ) : F), -(((ν₀ : Fˣ) : F))⁻¹} := by
      intro y hy
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_map.1 hy
      have hφ : φ ν = φ ν₀ := (Finset.mem_filter.1 hν).2
      simp only [φ, Units.val_inv_eq_inv_val] at hφ
      show ((ν : Fˣ) : F) ∈ ({((ν₀ : Fˣ) : F), -(((ν₀ : Fˣ) : F))⁻¹} : Finset F)
      rcases eq_or_eq_of_sub_inv_eq (Units.ne_zero _) (Units.ne_zero _) hφ.symm with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    calc (Finset.univ.filter fun ν => φ ν = φ ν₀).card
        = ((Finset.univ.filter fun ν => φ ν = φ ν₀).map ⟨fun ν : rootsOfUnity (p ^ f + 1) F =>
            ((ν : Fˣ) : F), fun a b h => Subtype.ext (Units.ext h)⟩).card := (Finset.card_map _).symm
      _ ≤ ({((ν₀ : Fˣ) : F), -(((ν₀ : Fˣ) : F))⁻¹} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have himg : ((Finset.univ : Finset (rootsOfUnity (p ^ f + 1) F)).image φ).card ≤ Nat.card V := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := V)]
    calc ((Finset.univ : Finset (rootsOfUnity (p ^ f + 1) F)).image φ).card
        ≤ ((Finset.univ : Finset V).map ⟨fun v : V => (v : F), Subtype.val_injective⟩).card := by
          refine Finset.card_le_card ?_
          intro y hy
          obtain ⟨ν, -, rfl⟩ := Finset.mem_image.1 hy
          exact Finset.mem_map.2 ⟨⟨φ ν, hmem ν ν.2⟩, Finset.mem_univ _, rfl⟩
      _ = (Finset.univ : Finset V).card := Finset.card_map _
  have hle := Finset.card_le_mul_card_image (Finset.univ : Finset (rootsOfUnity (p ^ f + 1) F)) 2
    hfib
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_rootsOfUnity_q hF] at hle
  omega

theorem mem_zSet (hq3 : p ^ f % 3 = 1) {S : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hSU : S ≤ rootU hF)
    (hS : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ S, tSU hF μ * x * (tSU hF μ)⁻¹ ∈ S)
    {x₀ : SU (unitaryInvolution F p f) 3} (hx₀ : x₀ ∈ S) (ha₀ : ca x₀ ≠ 0) {d : F}
    (hd : d ∈ traceZero (unitaryInvolution F p f)) : d ∈ zSet hF S hSU := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  set N := unitaryInvolution F p f (ca x₀) * ca x₀ with hN
  have hN0 : N ≠ 0 := mul_ne_zero ((map_ne_zero (unitaryInvolution F p f)).2 ha₀) ha₀
  have hσN : unitaryInvolution F p f N = N := by rw [hN, map_mul, hσ, mul_comm]
  have hcomm : ∀ ν ∈ rootsOfUnity (p ^ f + 1) F,
      N * ((ν : F) - ((ν⁻¹ : Fˣ) : F)) ∈ zSet hF S hSU := by
    intro ν hν
    obtain ⟨μ, hμ, rfl⟩ := exists_cube hq3 hν
    set y := tSU hF μ * x₀ * (tSU hF μ)⁻¹
    have hy : y ∈ S := hS μ hμ x₀ hx₀
    refine ⟨x₀ * y * x₀⁻¹ * y⁻¹, S.mul_mem (S.mul_mem (S.mul_mem hx₀ hy) (S.inv_mem hx₀))
      (S.inv_mem hy), ca_commutator hF (hSU hx₀) (hSU hy), ?_⟩
    rw [cb_commutator hF (hSU hx₀) (hSU hy), ca_tSU_conj_of_mem hF hμ (hSU hx₀), map_mul,
      unitaryInvolution_of_mem (pow_mem hμ 3)]
    ring
  let V : AddSubgroup F :=
    (zSet hF S hSU).comap (AddMonoidHom.mulLeft N) ⊓ traceZero (unitaryInvolution F p f)
  have hV : V = traceZero (unitaryInvolution F p f) := by
    refine eq_traceZero_of_le hF inf_le_right fun ν hν => ⟨hcomm ν hν, sub_inv_mem_traceZero hν⟩
  have hd' : N⁻¹ * d ∈ V := by
    rw [hV, mem_traceZero]
    rw [mem_traceZero] at hd
    rw [map_mul, map_inv₀, hσN]
    linear_combination N⁻¹ * hd
  have h1 : N * (N⁻¹ * d) ∈ zSet hF S hSU := (AddSubgroup.mem_inf.1 hd').1
  rwa [← mul_assoc, mul_inv_cancel₀ hN0, one_mul] at h1

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem eq_top_of_card (R : Subfield F) (hR : p ^ f < Nat.card R) : R = ⊤ := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite R
  have hpow := Module.natCard_eq_pow_finrank (K := R) (V := F)
  rw [hF] at hpow
  have hq := two_le_q hF
  set k := Module.finrank R F
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [pow_zero] at hpow
        have : 2 ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
        omega
      · rfl
    · exfalso
      have h1 : (p ^ f) ^ 2 < Nat.card R ^ 2 := Nat.pow_lt_pow_left hR (by norm_num)
      have h2 : Nat.card R ^ 2 ≤ Nat.card R ^ k :=
        Nat.pow_le_pow_right (by omega) h
      omega
  rw [hk1, pow_one] at hpow
  classical
  refine eq_top_iff.2 fun x _ => ?_
  by_contra hx
  have hlt : Fintype.card {y // y ∈ R} < Fintype.card F := Fintype.card_subtype_lt hx
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF] at hlt
  have : Nat.card {y // y ∈ R} = Nat.card R := rfl
  omega

theorem aSet_eq_top (hq3 : p ^ f % 3 = 1) {S : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hSU : S ≤ rootU hF)
    (hS : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ S, tSU hF μ * x * (tSU hF μ)⁻¹ ∈ S)
    {x₀ : SU (unitaryInvolution F p f) 3} (hx₀ : x₀ ∈ S) (ha₀ : ca x₀ ≠ 0) :
    aSet hF S hSU = ⊤ := by
  classical
  have hνR : ∀ ν ∈ rootsOfUnity (p ^ f + 1) F,
      ((ν : Fˣ) : F) ∈ multipliers (aSet hF S hSU) := by
    intro ν hν a ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨μ, hμ, rfl⟩ := exists_cube hq3 hν
    exact ⟨tSU hF μ * x * (tSU hF μ)⁻¹, hS μ hμ x hx, ca_tSU_conj_of_mem hF hμ (hSU hx)⟩
  have hcardR : p ^ f < Nat.card (multipliers (aSet hF S hSU)) := by
    let g : Option (rootsOfUnity (p ^ f + 1) F) → multipliers (aSet hF S hSU) := fun o =>
      match o with
      | none => 0
      | some ν => ⟨((ν : Fˣ) : F), hνR ν ν.2⟩
    have hg : Function.Injective g := by
      rintro (_ | ν) (_ | ν') h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm (Units.ne_zero _)
      · exact absurd (congrArg Subtype.val h) (Units.ne_zero _)
      · exact congrArg some (Subtype.ext (Units.ext (congrArg Subtype.val h)))
    have hle := Nat.card_le_card_of_injective g hg
    rw [Finite.card_option, card_rootsOfUnity_q hF] at hle
    omega
  have hRtop := eq_top_of_card hF _ hcardR
  rw [eq_top_iff]
  intro t _
  have ha₀A : ca x₀ ∈ aSet hF S hSU := ⟨x₀, hx₀, rfl⟩
  have hr : t * (ca x₀)⁻¹ ∈ multipliers (aSet hF S hSU) := by rw [hRtop]; trivial
  have := hr _ ha₀A
  rwa [mul_assoc, inv_mul_cancel₀ ha₀, mul_one] at this

theorem eq_top_or_ca_eq_zero (hq3 : p ^ f % 3 = 1) {S : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hSU : S ≤ rootU hF)
    (hS : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ S, tSU hF μ * x * (tSU hF μ)⁻¹ ∈ S) :
    S = rootU hF ∨ ∀ x ∈ S, ca x = 0 := by
  by_cases h : ∀ x ∈ S, ca x = 0
  · exact Or.inr h
  push Not at h
  obtain ⟨x₀, hx₀, ha₀⟩ := h
  left
  refine le_antisymm hSU fun x hx => ?_
  have hA := aSet_eq_top hF hq3 hSU hS hx₀ ha₀
  have hxa : ca x ∈ aSet hF S hSU := by rw [hA]; trivial
  obtain ⟨y, hy, hya⟩ := hxa
  have hxy : x * y⁻¹ ∈ rootU hF := (rootU hF).mul_mem hx ((rootU hF).inv_mem (hSU hy))
  have hxya : ca (x * y⁻¹) = 0 := by
    rw [ca_mul hF hx ((rootU hF).inv_mem (hSU hy)), ca_inv hF (hSU hy), hya, add_neg_cancel]
  have hz := mem_zSet hF hq3 hSU hS hx₀ ha₀ (cb_add_of_ca_eq_zero hF hxy hxya)
  obtain ⟨z, hz, hza, hzb⟩ := hz
  have hzx : z = x * y⁻¹ := eq_of_ca_cb hF (hSU hz) hxy (hza.trans hxya.symm) hzb
  have : x = z * y := by rw [hzx]; group
  rw [this]
  exact S.mul_mem hz hy

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
