module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Cited
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMain
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem inf_centralizer_le_of_balance (hbal : Sol78.BalanceTwoComponentInput) {E : Subgroup X}
    (hEel : IsElementaryAbelian 2 E) (hE : E ≠ ⊥) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype ⊓
        centralizer (E : Set X) ≤
      (pPrimeCore 2 (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he2 : e ^ 2 = 1 := by
    have h2 : (⟨e, he⟩ : E) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := hEel.exponent_dvd_p
      rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    have := congrArg Subtype.val h2
    simpa using this
  have hS : zpowers e ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    exact he1 h
  have hSel : IsElementaryAbelian 2 (zpowers e) := IsElementaryAbelian.zpowers_of_pow_eq_one he2
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hST : zpowers e ≤ centralizer (E : Set X) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact hcomm x hx e he
  obtain ⟨-, hbc, hd⟩ := hbal X (zpowers e) E hS hE hSel hEel hST
  have hCS : centralizer ((zpowers e : Subgroup X) : Set X) = centralizer ({e} : Set X) :=
    centralizer_zpowers_eq' e
  by_contra hne
  have hne' : ¬ GH74.GLS.pPrimeCoreOf 2 (centralizer ((zpowers e : Subgroup X) : Set X)) ⊓
      centralizer (E : Set X) ≤ GH74.GLS.pPrimeCoreOf 2 (centralizer (E : Set X)) := by
    rw [hCS]
    exact hne
  obtain ⟨M, hM, hMX⟩ := hd hne'
  obtain ⟨-, hc⟩ := hbc M hM
  obtain ⟨-, -, h3⟩ := hc hMX
  have h4 : ⁅M, zpowers e ⊓ normalizer (M : Set X)⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro m hm g hg
    have hgE : g ∈ E := (zpowers_le.mpr he) (mem_inf.mp hg).1
    have hmg : g * m = m * g := mem_centralizer_iff.mp (hM.1 hm) g hgE
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hmg.symm
  rw [h4, sup_bot_eq] at h3
  have hMO : M ≤ GH74.GLS.pPrimeCoreOf 2 (centralizer (E : Set X)) := h3 ▸ le_sup_right
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hM.1).mp hM.2).2.2
  have hModd : Nat.Coprime 2 (Nat.card M) := by
    have h1 : Nat.card M ∣ Nat.card (GH74.GLS.pPrimeCoreOf 2 (centralizer (E : Set X))) :=
      card_dvd_of_le hMO
    rw [GH74.GLS.pPrimeCoreOf, card_map_of_injective (centralizer (E : Set X)).subtype_injective]
      at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥M = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Nontrivial (↥M ⧸ pPrimeCore 2 ↥M) := LocalCores.isQuasisimple_nontrivial hMq
  have : Subsingleton (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥M ⧸ pPrimeCore 2 ↥M)

theorem thetaFunctor_eq_of_balance (hbal : Sol78.BalanceTwoComponentInput) {E : Subgroup X}
    (hEel : IsElementaryAbelian 2 E) (hE : E ≠ ⊥) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    SolAltLit.thetaFunctor E e =
      (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype := by
  set O := (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype
    with hOdef
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : E ≤ centralizer ({e} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hcomm x hx e he)
  have hEO : E ≤ normalizer (O : Set X) :=
    hEe.trans (Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({e} : Set X))))
  have : IsElementaryAbelian 2 E := hEel
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hcop : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective (centralizer ({e} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  apply le_antisymm
  · refine sup_le ?_ inf_le_left
    rw [commutator_le]
    intro x hx g hg
    have h1 : g * x⁻¹ * g⁻¹ ∈ O := (mem_normalizer_iff.mp (hEO hg) _).mp (inv_mem hx)
    have h2 : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hx h1
  · rw [← SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two
      E O hE2 hEO hcop]
    exact sup_le le_sup_left
      ((le_inf inf_le_left (inf_centralizer_le_of_balance hbal hEel hE he he1)).trans
        le_sup_right)

omit [Finite X] in
theorem isElementaryAbelian_of_klein {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    IsElementaryAbelian 2 E := by
  obtain ⟨φ⟩ := hE
  have hsq : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by decide
  have hcomm : ∀ u v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u * v = v * u := by
    decide
  exact { toIsMulCommutative := ⟨⟨fun a b => φ.injective (by rw [map_mul, map_mul, hcomm])⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
            φ.injective (by rw [map_pow, hsq, map_one]) }

omit [Finite X] in
theorem exists_three_of_klein {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ∃ a₁ a₂ a₃ : X, a₁ ∈ E ∧ a₂ ∈ E ∧ a₃ ∈ E ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₃ ≠ 1 ∧ a₁ ≠ a₂ ∧
      a₁ ≠ a₃ ∧ a₂ ≠ a₃ := by
  classical
  obtain ⟨φ⟩ := hE
  let u₁ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)
  let u₂ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)
  let u₃ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)
  have hu : u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧ u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ := by decide
  refine ⟨φ.symm u₁, φ.symm u₂, φ.symm u₃, (φ.symm u₁).2, (φ.symm u₂).2, (φ.symm u₃).2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : φ.symm u₁ = φ.symm 1 := by rw [map_one]; exact Subtype.ext h
    exact hu.1 (φ.symm.injective h')
  · intro h
    have h' : φ.symm u₂ = φ.symm 1 := by rw [map_one]; exact Subtype.ext h
    exact hu.2.1 (φ.symm.injective h')
  · intro h
    have h' : φ.symm u₃ = φ.symm 1 := by rw [map_one]; exact Subtype.ext h
    exact hu.2.2.1 (φ.symm.injective h')
  · intro h
    exact hu.2.2.2.1 (φ.symm.injective (Subtype.ext h))
  · intro h
    exact hu.2.2.2.2.1 (φ.symm.injective (Subtype.ext h))
  · intro h
    exact hu.2.2.2.2.2 (φ.symm.injective (Subtype.ext h))

theorem completion_le_of_balance (hbal : Sol78.BalanceTwoComponentInput) {E F : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEF : E ≤ centralizer (F : Set X))
    (hst : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ F, f ≠ 1 →
      (pPrimeCore 2 (centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ⊓
          centralizer ({e} : Set X) ≤
        (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype) :
    Sol78.signalizerCompletion F F ≤ Sol78.signalizerCompletion E E := by
  classical
  have hEel := isElementaryAbelian_of_klein hE
  have hFel := isElementaryAbelian_of_klein hF
  have hFne : F ≠ ⊥ := by
    intro h
    obtain ⟨φ⟩ := hF
    have h1 := Nat.card_congr φ.toEquiv
    rw [h, Subgroup.card_bot, Nat.card_prod] at h1
    simp [Nat.card_eq_fintype_card, ZMod.card] at h1
  have hEne : E ≠ ⊥ := by
    intro h
    obtain ⟨φ⟩ := hE
    have h1 := Nat.card_congr φ.toEquiv
    rw [h, Subgroup.card_bot, Nat.card_prod] at h1
    simp [Nat.card_eq_fintype_card, ZMod.card] at h1
  obtain ⟨a₁, a₂, a₃, h₁, h₂, h₃, h₁₁, h₂₁, h₃₁, h₁₂, h₁₃, h₂₃⟩ := exists_three_of_klein hE
  have : IsKleinFour ↥E := by
    obtain ⟨hE4, hE2⟩ := card_sq_of_klein hE
    exact isKleinFour_of_card hE4 fun g => Subtype.ext (by rw [← sq]; exact hE2 g g.2)
  have hle : ∀ a ∈ E, a ≠ 1 → SolAltLit.thetaFunctor E a ≤ Sol78.signalizerCompletion E E :=
    fun a ha ha1 => le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ E) =>
      ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor E c) a ha (le_iSup_of_le ha1 le_rfl)
  refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
  rw [thetaFunctor_eq_of_balance hbal hFel hFne hf hf1]
  set O := (pPrimeCore 2 (centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype
    with hOdef
  have hEf : E ≤ centralizer ({f} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEF hx) f hf).symm)
  have hEO : E ≤ normalizer (O : Set X) :=
    hEf.trans (Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({f} : Set X))))
  have hodd : Odd (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective (centralizer ({f} : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hprod := ABGLocalTools.four_group_odd_eq_mul_centralizers hodd hEO h₁ h₂ h₃ h₁₁ h₂₁ h₃₁
    h₁₂ h₁₃ h₂₃
  have hC : ∀ a ∈ E, a ≠ 1 → O ⊓ centralizer ({a} : Set X) ≤ Sol78.signalizerCompletion E E :=
    fun a ha ha1 => (hst a ha ha1 f hf hf1).trans
      ((thetaFunctor_eq_of_balance hbal hEel hEne ha ha1).symm ▸ hle a ha ha1)
  intro x hx
  have hx' : x ∈ (O : Set X) := hx
  rw [hprod] at hx'
  obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hx'
  exact mul_mem (mul_mem (hC a₁ h₁ h₁₁ hc₁) (hC a₂ h₂ h₂₁ hc₂)) (hC a₃ h₃ h₃₁ hc₃)

end CFSG.ComponentClassification.SolMax
