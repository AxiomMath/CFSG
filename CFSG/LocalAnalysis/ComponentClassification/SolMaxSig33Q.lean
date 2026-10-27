module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig28
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33O

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

abbrev coreAt (a : X) : Subgroup X :=
  (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype

@[expose] def DaggerAt (E : Subgroup X) (a b : X) : Prop :=
  ∀ L : Subgroup X, L ≤ centralizer ({b} : Set X) →
    IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) →
    ¬ ⁅L, coreAt a ⊓ centralizer ({b} : Set X)⁆ ≤ coreAt b →
    E ≤ UnbalancedLayer.coreActionKernel L

theorem le_normalizer_coreAt (g : X) :
    centralizer ({g} : Set X) ≤ normalizer ((coreAt g : Subgroup X) : Set X) :=
  Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥(centralizer ({g} : Set X)))

theorem odd_card_coreAt [Finite X] (g : X) : Odd (Nat.card (coreAt g)) := by
  rw [coreAt, card_map_of_injective (centralizer ({g} : Set X)).subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem commutator_le_core_of_dagger [Finite X] (hbal : Sol78.BalanceTwoComponentInput)
    {E : Subgroup X}
    {a b : X} (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hab : a * b = b * a) (hdag : DaggerAt E a b) {Z : Subgroup X}
    (hZ : Z ≤ coreAt a ⊓ centralizer ({b} : Set X)) (hEZ : E ≤ normalizer (Z : Set X)) :
    ⁅Z, E⁆ ≤ coreAt b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers b ≠ ⊥ := fun h => hb1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hab
  have hSel := IsElementaryAbelian.zpowers_of_pow_eq_one (show a ^ 2 = 1 by rw [sq]; exact ha2)
  have hTel := IsElementaryAbelian.zpowers_of_pow_eq_one (show b ^ 2 = 1 by rw [sq]; exact hb2)
  have hCb' : centralizer ((zpowers b : Subgroup X) : Set X) = centralizer ({b} : Set X) :=
    centralizer_zpowers_eq' b
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) :=
    centralizer_zpowers_eq' a
  have hZE : ⁅Z, E⁆ ≤ Z := commutator_le_left_of_le_normalizer hEZ
  have hgoal := le_core_of_forall_commutator hbal hS hT hSel hTel hST (Y := ⁅Z, E⁆) ?_ ?_
  · rw [hCb'] at hgoal
    exact hgoal
  · rw [hCa', hCb']
    exact hZE.trans hZ
  · intro L hL
    rw [hCb'] at hL ⊢
    obtain ⟨hLC, hLpc⟩ := hL
    by_cases hLX : ⁅L, coreAt a ⊓ centralizer ({b} : Set X)⁆ ≤ coreAt b
    · exact (commutator_mono le_rfl (hZE.trans hZ)).trans hLX
    · have hEL := hdag L hLC hLpc hLX
      obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers b) hS hT hSel hTel hST
      rw [hCb', hCa'] at hbc
      obtain ⟨hXN, -⟩ := hbc L ⟨hLC, hLpc⟩
      have hZL : Z ≤ normalizer (L : Set X) :=
        le_normalizer_of_le_normalizer_sup hLC hLpc (hZ.trans inf_le_right) (hZ.trans hXN)
      exact (commutator_le_of_le_coreActionKernel (commutator_le_coreActionKernel hZL hEL)).trans
        (pPrimeCore_le_of_isPComponent hLC hLpc)

theorem inf_core_le_core_of_dagger [Finite X] (hbal : Sol78.BalanceTwoComponentInput)
    {E : Subgroup X}
    (hEel : IsElementaryAbelian 2 E) (hE : E ≠ ⊥) {a b : X} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hab : a * b = b * a)
    (hEb : E ≤ centralizer ({b} : Set X)) (hdag : DaggerAt E a b) :
    coreAt a ⊓ (pPrimeCore 2 ↥(centralizer (E : Set X))).map (centralizer (E : Set X)).subtype ⊓
        centralizer ({b} : Set X) ≤ coreAt b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers b ≠ ⊥ := fun h => hb1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hab
  have hSel := IsElementaryAbelian.zpowers_of_pow_eq_one (show a ^ 2 = 1 by rw [sq]; exact ha2)
  have hTel := IsElementaryAbelian.zpowers_of_pow_eq_one (show b ^ 2 = 1 by rw [sq]; exact hb2)
  have hCb' : centralizer ((zpowers b : Subgroup X) : Set X) = centralizer ({b} : Set X) :=
    centralizer_zpowers_eq' b
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) :=
    centralizer_zpowers_eq' a
  have hET : E ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by rw [hCb']; exact hEb
  have hgoal := le_core_of_forall_commutator hbal hS hT hSel hTel hST
    (Y := coreAt a ⊓ (pPrimeCore 2 ↥(centralizer (E : Set X))).map
      (centralizer (E : Set X)).subtype ⊓ centralizer ({b} : Set X)) ?_ ?_
  · rw [hCb'] at hgoal
    exact hgoal
  · rw [hCa', hCb']
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · intro L hL
    rw [hCb'] at hL ⊢
    obtain ⟨hLC, hLpc⟩ := hL
    by_cases hLX : ⁅L, coreAt a ⊓ centralizer ({b} : Set X)⁆ ≤ coreAt b
    · exact (commutator_mono le_rfl (le_inf (inf_le_left.trans inf_le_left)
        inf_le_right)).trans hLX
    · have hEL := hdag L hLC hLpc hLX
      obtain ⟨-, hbcE, -⟩ := hbal X E (zpowers b) hE hT hEel hTel hET
      rw [hCb'] at hbcE
      obtain ⟨-, hcE⟩ := hbcE L ⟨hLC, hLpc⟩
      have hXE : ⁅L, GH74.GLS.pPrimeCoreOf 2 (centralizer (E : Set X)) ⊓
          centralizer ({b} : Set X)⁆ ≤ GH74.GLS.pPrimeCoreOf 2 (centralizer ({b} : Set X)) := by
        by_contra hne
        obtain ⟨-, -, hOL⟩ := hcE hne
        have h1 : ⁅L, E ⊓ normalizer (L : Set X)⁆ ≤ coreAt b :=
          (commutator_le_of_le_coreActionKernel (inf_le_left.trans hEL)).trans
            (pPrimeCore_le_of_isPComponent hLC hLpc)
        have h2 : GH74.GLS.pPrimeCoreOf 2 (centralizer ({b} : Set X)) ⊔ L ≤ coreAt b := by
          rw [hOL]
          exact sup_le le_rfl h1
        exact not_le_pPrimeCore_of_isPComponent hLC hLpc (le_sup_right.trans h2)
      refine (commutator_mono le_rfl ?_).trans hXE
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem commutator_inf_centralizer_le_of_dagger [Finite X]
    (hbal : Sol78.BalanceTwoComponentInput)
    {E : Subgroup X} (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {a : X} (ha2 : a * a = 1) (ha1 : a ≠ 1) (hEa : E ≤ centralizer ({a} : Set X))
    (hdag : ∀ e ∈ E, e ≠ 1 → DaggerAt E a e) :
    ⁅coreAt a, E⁆ ⊓ centralizer (E : Set X) ≤
      (pPrimeCore 2 ↥(centralizer (E : Set X))).map (centralizer (E : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEel := isElementaryAbelian_of_klein hE
  have : IsElementaryAbelian 2 E := hEel
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  obtain ⟨hE4, hEsq⟩ := card_sq_of_klein hE
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    omega
  have hcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hEN : E ≤ normalizer ((coreAt a : Subgroup X) : Set X) :=
    hEa.trans (le_normalizer_coreAt a)
  have hcop : Nat.Coprime 2 (Nat.card (coreAt a)) := Nat.coprime_two_left.mpr (odd_card_coreAt a)
  have hX₀le : ⁅coreAt a, E⁆ ≤ coreAt a := commutator_le_left_of_le_normalizer hEN
  have hX₀odd : Odd (Nat.card ↥⁅coreAt a, E⁆) :=
    (odd_card_coreAt a).of_dvd_nat (card_dvd_of_le hX₀le)
  have hEX₀ : E ≤ normalizer ((⁅coreAt a, E⁆ : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hEN hg),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)]
  have hidem : ⁅⁅coreAt a, E⁆, E⁆ = ⁅coreAt a, E⁆ :=
    SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2 Nat.prime_two E
      (coreAt a) hE2 hEN hcop
  have hGen := Sig28.goldschmidtGeneration_klein hE hEX₀ hX₀odd hidem
  rw [hGen]
  refine iSup₂_le fun U₀ hU₀ => iSup_le fun hu => ?_
  obtain ⟨u, huE, hEU⟩ := hu
  obtain ⟨e, heU, he1⟩ : ∃ e ∈ U₀, e ≠ 1 := by
    rcases U₀.bot_or_exists_ne_one with h | h
    · exfalso
      rw [h, bot_sup_eq] at hEU
      have h1 : Nat.card E ∣ Nat.card (zpowers u) := card_dvd_of_le hEU
      rw [Nat.card_zpowers, hE4] at h1
      have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (hEsq u huE)
      have h3 := Nat.le_of_dvd two_pos h2
      have h4 := Nat.le_of_dvd (orderOf_pos u) h1
      omega
    · exact h
  have heE : e ∈ E := hU₀ heU
  have he2 : e * e = 1 := by rw [← sq]; exact hEsq e heE
  have hae : a * e = e * a := (mem_centralizer_singleton_iff.mp (hEa heE)).symm
  have hCU : centralizer (U₀ : Set X) ≤ centralizer ({e} : Set X) :=
    centralizer_le (Set.singleton_subset_iff.mpr heU)
  have hZ : ⁅coreAt a, E⁆ ⊓ centralizer (U₀ : Set X) ≤ coreAt a ⊓ centralizer ({e} : Set X) :=
    inf_le_inf hX₀le hCU
  have hEZ : E ≤ normalizer ((⁅coreAt a, E⁆ ⊓ centralizer (U₀ : Set X) : Subgroup X) : Set X) := by
    intro g hg
    have hgU : g ∈ centralizer (U₀ : Set X) :=
      mem_centralizer_iff.mpr fun z hz => hcomm z (hU₀ hz) g hg
    exact inf_mem_normalizer' (hEX₀ hg) (le_normalizer hgU)
  have hZE := commutator_le_core_of_dagger hbal ha2 ha1 he2 he1 hae (hdag e heE he1) hZ hEZ
  refine le_trans ?_ (inf_centralizer_le_of_balance hbal hEel hEne heE he1)
  exact le_inf (inf_le_right.trans hZE) (inf_le_left.trans inf_le_right)

theorem thetaFunctor_inf_le_of_dagger [Finite X] (hbal : Sol78.BalanceTwoComponentInput)
    {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) {a b : X}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hab : a * b = b * a)
    (hEa : E ≤ centralizer ({a} : Set X)) (hEb : E ≤ centralizer ({b} : Set X))
    (hdag : DaggerAt E a b) (hdagE : ∀ e ∈ E, e ≠ 1 → DaggerAt E a e) :
    SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEel := isElementaryAbelian_of_klein hE
  have : IsElementaryAbelian 2 E := hEel
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  obtain ⟨hE4, -⟩ := card_sq_of_klein hE
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    omega
  have hcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  set OE := (pPrimeCore 2 ↥(centralizer (E : Set X))).map (centralizer (E : Set X)).subtype
    with hOEdef
  have hθb : SolAltLit.thetaFunctor E b = ⁅coreAt b, E⁆ ⊔ (coreAt b ⊓ OE) := rfl
  have hθa : SolAltLit.thetaFunctor E a = ⁅coreAt a, E⁆ ⊔ (coreAt a ⊓ OE) := rfl
  have hEN : E ≤ normalizer ((coreAt a : Subgroup X) : Set X) :=
    hEa.trans (le_normalizer_coreAt a)
  have hX₀le : ⁅coreAt a, E⁆ ≤ coreAt a := commutator_le_left_of_le_normalizer hEN
  have hθle : SolAltLit.thetaFunctor E a ≤ coreAt a := by
    rw [hθa]
    exact sup_le hX₀le inf_le_left
  have hYN : E ≤ normalizer
      ((SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) : Subgroup X) : Set X) := by
    intro g hg
    have h1 : g ∈ normalizer ((SolAltLit.thetaFunctor E a : Subgroup X) : Set X) :=
      mem_normalizer_iff_map_conj_eq.mpr
        (Sol78.map_conj_thetaFunctor (hEa hg) fun z hz => hcomm g hg z hz)
    exact inf_mem_normalizer' h1 (le_normalizer (hEb hg))
  have hYodd : Odd (Nat.card ↥(SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X))) :=
    (odd_card_coreAt a).of_dvd_nat (card_dvd_of_le (inf_le_left.trans hθle))
  refine (GrSLit.le_commutator_sup_inf_centralizer_of_odd hE2 hYN hYodd).trans (sup_le ?_ ?_)
  ·
    have hYZ : SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤
        coreAt a ⊓ centralizer ({b} : Set X) := inf_le_inf_right _ hθle
    have h1 := commutator_le_core_of_dagger hbal ha2 ha1 hb2 hb1 hab hdag hYZ hYN
    rw [← SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2 Nat.prime_two E
      _ hE2 hYN (Nat.coprime_two_left.mpr hYodd), hθb]
    exact (commutator_mono h1 le_rfl).trans le_sup_left
  ·
    have hHN : coreAt a ⊓ OE ≤ normalizer ((⁅coreAt a, E⁆ : Subgroup X) : Set X) := by
      intro g hg
      have hgE : g ∈ centralizer (E : Set X) := map_subtype_le _ (mem_inf.mp hg).2
      rw [mem_normalizer_iff_map_conj_eq, map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer (mem_inf.mp hg).1),
        mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hgE)]
    have hθE : SolAltLit.thetaFunctor E a ⊓ centralizer (E : Set X) ≤ OE := by
      intro x hx
      obtain ⟨hxθ, hxE⟩ := mem_inf.mp hx
      have hx' : x ∈ ((⁅coreAt a, E⁆ ⊔ (coreAt a ⊓ OE) : Subgroup X) : Set X) := by
        rw [← hθa]
        exact hxθ
      rw [coe_mul_of_right_le_normalizer_left _ _ hHN] at hx'
      obtain ⟨m, hm, k, hk, rfl⟩ := hx'
      have hkE : k ∈ centralizer (E : Set X) := map_subtype_le _ (mem_inf.mp hk).2
      have hmE : m ∈ centralizer (E : Set X) := by
        have := mul_mem hxE (inv_mem hkE)
        simpa using this
      exact mul_mem (commutator_inf_centralizer_le_of_dagger hbal hE ha2 ha1 hEa hdagE
        (mem_inf.mpr ⟨hm, hmE⟩)) (mem_inf.mp hk).2
    intro x hx
    obtain ⟨hxY, hxE⟩ := mem_inf.mp hx
    obtain ⟨hxθ, hxb⟩ := mem_inf.mp hxY
    have hxOE : x ∈ OE := hθE (mem_inf.mpr ⟨hxθ, hxE⟩)
    have hxb' : x ∈ coreAt b :=
      inf_core_le_core_of_dagger hbal hEel hEne ha2 ha1 hb2 hb1 hab hEb hdag
        (mem_inf.mpr ⟨mem_inf.mpr ⟨hθle hxθ, hxOE⟩, hxb⟩)
    rw [hθb]
    exact mem_sup_right (mem_inf.mpr ⟨hxb', hxOE⟩)

end CFSG.ComponentClassification.SolMax
