module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR19

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section GroupLevel

@[expose] def OddCommG (C : Type*) [Group C] : Prop :=
  ∀ s : C, Odd (orderOf s) → ∀ w ∈ pPrimeCore 2 C, s * w = w * s

theorem OddCommG.of_mulEquiv {C C' : Type*} [Group C] [Group C'] (φ : C ≃* C') (h : OddCommG C) :
    OddCommG C' := by
  intro s' hs' w' hw'
  have hw : w' ∈ (pPrimeCore 2 C).map φ.toMonoidHom := by rw [pPrimeCore_map_iso]; exact hw'
  obtain ⟨w, hw, rfl⟩ := hw
  have hs : Odd (orderOf (φ.symm s')) := by rwa [MulEquiv.orderOf_eq]
  have := h (φ.symm s') hs w hw
  have h2 := congrArg φ this
  simpa using h2

theorem OddCommG.of_odd_comm {C : Type*} [Group C] [Finite C]
    (h : ∀ a b : C, Odd (orderOf a) → Odd (orderOf b) → a * b = b * a) : OddCommG C := by
  intro s hs w hw
  have hOodd : Odd (Nat.card (pPrimeCore 2 C)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hw' : Odd (orderOf w) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 C) hw
    exact Odd.of_dvd_nat hOodd this
  exact h s w hs hw'

theorem OddCommG.of_pPrimeCore_eq_bot {C : Type*} [Group C] (h : pPrimeCore 2 C = ⊥) :
    OddCommG C := by
  intro s hs w hw
  rw [h, Subgroup.mem_bot] at hw
  rw [hw]; simp

theorem pPrimeCore_eq_bot_of_simple {C : Type*} [Group C] [Finite C] (hs : IsSimpleGroup C)
    (heven : 2 ∣ Nat.card C) : pPrimeCore 2 C = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 C) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (pPrimeCore 2 C)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)

theorem OddCommG.dihedral (k : ℕ) [NeZero k] : OddCommG (DihedralGroup k) := by
  apply OddCommG.of_odd_comm
  intro a b ha hb
  cases a with
  | r i =>
    cases b with
    | r j => simp [DihedralGroup.r_mul_r, add_comm]
    | sr j =>
      exfalso
      rw [DihedralGroup.orderOf_sr] at hb
      exact absurd hb (by decide)
  | sr i =>
    exfalso
    rw [DihedralGroup.orderOf_sr] at ha
    exact absurd ha (by decide)

theorem OddCommG.of_card_eq_24 {C : Type} [Group C] [Finite C] (h : Nat.card C = 24) :
    OddCommG C := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hs w hw
  have key : ∀ n : ℕ, n ≤ 24 → Odd n → n ∣ 24 → n = 1 ∨ n = 3 := by decide
  have hOodd : Odd (Nat.card (pPrimeCore 2 C)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hOdvd : Nat.card (pPrimeCore 2 C) ∣ 24 := h ▸ Subgroup.card_subgroup_dvd_card _
  have hs24 : orderOf s ∣ 24 := h ▸ orderOf_dvd_natCard s
  rcases key _ (Nat.le_of_dvd (by norm_num) hOdvd) hOodd hOdvd with hO1 | hO3
  · have : pPrimeCore 2 C = ⊥ := Subgroup.card_eq_one.1 hO1
    rw [this, Subgroup.mem_bot] at hw
    rw [hw]; simp
  rcases key _ (Nat.le_of_dvd (by norm_num) hs24) hs hs24 with hs1 | hs3
  · rw [orderOf_eq_one_iff.1 hs1]; simp
  set O : Subgroup C := pPrimeCore 2 C with hOdef
  set S : Subgroup C := Subgroup.zpowers s with hSdef
  have hScard : Nat.card S = 3 := by rw [hSdef, Nat.card_zpowers, hs3]
  have hSN : S ≤ normalizer (O : Set C) := by
    intro x _
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hprod := Th2.HY.card_sup_mul_card_inf_of_le_normalizer hSN
  rw [hScard, hO3] at hprod
  have hinfdvd : Nat.card ↥(S ⊓ O) ∣ 3 := by
    rw [← hScard]; exact Subgroup.card_dvd_of_le inf_le_left
  have hsupdvd : Nat.card ↥(S ⊔ O) ∣ 24 := h ▸ Subgroup.card_subgroup_dvd_card _
  have hinf3 : Nat.card ↥(S ⊓ O) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hinfdvd with h1 | h3
    · exfalso
      rw [h1] at hprod
      rw [mul_one] at hprod
      rw [hprod] at hsupdvd
      exact absurd hsupdvd (by norm_num)
    · exact h3
  have hSle : S ≤ O := by
    have : S ⊓ O = S := Subgroup.eq_of_le_of_card_ge (inf_le_left : S ⊓ O ≤ S) (by rw [hScard, hinf3])
    rw [← this]
    exact inf_le_right
  have hsO : s ∈ O := hSle (Subgroup.mem_zpowers s)
  have hOcyc : IsCyclic ↥O := isCyclic_of_prime_card (p := 3) hO3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥O)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (by simpa using hg ⟨s, hsO⟩ : (⟨s, hsO⟩ : ↥O) ∈ Subgroup.zpowers g)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (by simpa using hg ⟨w, hw⟩ : (⟨w, hw⟩ : ↥O) ∈ Subgroup.zpowers g)
  have hs' : s = ((g ^ a : ↥O) : C) := by rw [ha]
  have hw' : w = ((g ^ b : ↥O) : C) := by rw [hb]
  rw [hs', hw']
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← zpow_add, ← zpow_add, add_comm]

theorem pPrimeCore_perm5_eq_bot : pPrimeCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  classical
  set N : Subgroup (Equiv.Perm (Fin 5)) := pPrimeCore 2 (Equiv.Perm (Fin 5)) with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hNA : N.subgroupOf (alternatingGroup (Fin 5)) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with h | h
    · exact h
    · exfalso
      have hle : alternatingGroup (Fin 5) ≤ N := by
        intro a ha
        have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin 5))) ∈ N.subgroupOf (alternatingGroup (Fin 5)) := by
          rw [h]; trivial
        exact this
      have hdvd : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card N := Subgroup.card_dvd_of_le hle
      rw [nat_card_alternatingGroup] at hdvd
      have : 2 ∣ Nat.card N := by
        refine dvd_trans ?_ hdvd
        norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 this)
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have hn2 : n ^ 2 ∈ N := N.pow_mem hn 2
  have hsign : Equiv.Perm.sign (n ^ 2) = 1 := by rw [map_pow]; exact Int.units_sq _
  have hmem : (⟨n ^ 2, Equiv.Perm.mem_alternatingGroup.2 hsign⟩ : ↥(alternatingGroup (Fin 5))) ∈
      N.subgroupOf (alternatingGroup (Fin 5)) := hn2
  rw [hNA, Subgroup.mem_bot] at hmem
  have hsq : n ^ 2 = 1 := congrArg Subtype.val hmem
  have hord : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hodd : Odd (orderOf n) := Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn)
  have h1 : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

end GroupLevel

section A7Case

open Equiv Equiv.Perm

theorem oddComm_of_oddCommG {K : Type} [Group K] [Finite K] {H : Subgroup K} (h : OddCommG ↥H) :
    ∀ s ∈ H, Odd (orderOf s) → ∀ w ∈ pPrimeCoreOf 2 H, s * w = w * s := by
  intro s hs hodd w hw
  obtain ⟨w', hw', rfl⟩ := hw
  have hodd' : Odd (orderOf (⟨s, hs⟩ : ↥H)) := by
    rw [← Subgroup.orderOf_coe]; exact hodd
  have := h ⟨s, hs⟩ hodd' w' hw'
  have h2 := congrArg Subtype.val this
  simpa using h2

theorem oddCommG_fixed_one {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (heven : 2 ∣ Nat.card K) : OddCommG ↥(fixedSubgroup K (1 : MulAut K)) := by
  have hOK : OddCommG K := OddCommG.of_pPrimeCore_eq_bot (pPrimeCore_eq_bot_of_simple hs heven)
  have htop : fixedSubgroup K (1 : MulAut K) = ⊤ := by
    ext k
    simp [fixedSubgroup]
  exact OddCommG.of_mulEquiv (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)) hOK

theorem oddCommG_fixed_A7 {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 7))
    (y : MulAut K) (hy : y ^ 2 = 1) : OddCommG ↥(fixedSubgroup K y) := by
  classical
  have hsimpleA : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimpleK : IsSimpleGroup K := (e.isSimpleGroup_congr).2 hsimpleA
  have hevenK : 2 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  by_cases hy1 : y = 1
  · subst hy1
    exact oddCommG_fixed_one hsimpleK hevenK
  have hbij : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 (MulAut.congr e y)
  have hy'2 : (MulAut.congr e y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, hy'2, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hy1
    have h1 : MulAut.congr e y = 1 := by rw [← hσ, map_one]
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  let ψ : K →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective _).comp e.injective
  have hψy : ∀ k : K, ψ (y k) = σ * ψ k * σ⁻¹ := by
    intro k
    have h1 : e (y k) = MulAut.congr e y (e k) := by simp [MulAut.congr_apply]
    show ((e (y k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ * ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹
    rw [h1, ← hσ, MulAut.conjNormal_apply]
  have hmap : (fixedSubgroup K y).map ψ =
      centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : y k = k := hk
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (e k).2⟩
      have := hψy k
      rw [hk'] at this
      calc ψ k * σ = σ * ψ k * σ⁻¹ * σ := by rw [← this]
        _ = σ * ψ k := by group
    · rintro ⟨hxc, hxA⟩
      refine ⟨e.symm ⟨x, hxA⟩, ?_, by simp [ψ]⟩
      show y (e.symm ⟨x, hxA⟩) = e.symm ⟨x, hxA⟩
      apply hψinj
      rw [hψy]
      have hx : σ * x = x * σ := (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
      have : ψ (e.symm ⟨x, hxA⟩) = x := by simp [ψ]
      rw [this]
      calc σ * x * σ⁻¹ = x * σ * σ⁻¹ := by rw [hx]
        _ = x := by group
  let φ : ↥(fixedSubgroup K y) ≃* ↥(centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    (Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr hmap)
  refine OddCommG.of_mulEquiv φ.symm ?_
  rcases IVK.A7.involution_cycleType σ hσ2 hσ1 with h2 | h22 | h222
  · have hf : σ.IsSwap := Equiv.Perm.isSwap_iff_cycleType.mpr h2
    obtain ⟨e5⟩ := IVK.A7.centralizer_A7_swap_equiv hf
    exact OddCommG.of_mulEquiv e5.symm (OddCommG.of_pPrimeCore_eq_bot pPrimeCore_perm5_eq_bot)
  · exact OddCommG.of_card_eq_24 (IVK.A7.card_centralizer_A7_two_two h22 hσ2 hσ1)
  · exact OddCommG.of_card_eq_24 (IVK.A7.card_centralizer_A7_two_two_two h222 hσ2 hσ1)

end A7Case



section L2Case

open CFSG.GH74.GLS.IVK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_dihedral_fixed (hF : L2Field F) (e : K ≃* L2 F) (x : MulAut K)
    (hx : x ∈ innDiagSub e) (hx2 : orderOf x = 2) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥(fixedSubgroup K x) ≃* DihedralGroup k) := by
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  by_cases hin : x ∈ innAut K
  · obtain ⟨u, rfl⟩ := hin
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_conj_eq e u]
      exact hx2
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu2).2.1
    exact ⟨k, hk2, ⟨(MulEquiv.subgroupCongr (Proofs2.Lemma118.fixedSubgroup_conj u)).trans ψ⟩⟩
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
      ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3b F hF K e ε hε1 hε d hd x hx hin hx2).2.1
    exact ⟨k, hk2, ⟨ψ⟩⟩

theorem oddCommG_fixed_diag (hF : L2Field F) (e : K ≃* L2 F) (y : MulAut K) (hy : y ^ 2 = 1)
    (hyd : y ∈ innDiagSub e) : OddCommG ↥(fixedSubgroup K y) := by
  by_cases hy1 : y = 1
  · subst hy1
    exact oddCommG_fixed_one (Proofs2.isSimpleGroup_of_l2 hF e)
      (even_iff_two_dvd.1 (Proofs2.even_card_of_l2 hF e))
  · have hy2 : orderOf y = 2 := orderOf_eq_prime hy hy1
    obtain ⟨k, hk, ⟨φ⟩⟩ := exists_dihedral_fixed hF e y hyd hy2
    have : NeZero k := ⟨by omega⟩
    exact OddCommG.of_mulEquiv φ.symm (OddCommG.dihedral k)

theorem pPrimeCoreOf_fixed_outer_eq_bot
    (hF : L2Field F) (e : K ≃* L2 F) (y : MulAut K) (hy : y ^ 2 = 1)
    (hout : y ∉ innDiagSub e) : pPrimeCoreOf 2 (fixedSubgroup K y) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 : fieldProj e y ≠ 1 := fun h => hout ((mem_innDiagSub_iff e y).2 h)
  have hy1 : y ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy hy1
  have hord : orderOf (thetaAut e y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord hσ1
  set σ : F ≃+* F := fieldProj e y with hσdef
  set a : MulAut K := innDiagHom e C with hadef
  have hay : a⁻¹ * y * a = fieldAutHom e σ := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, thetaAut_innDiagHom, thetaAut_fieldAutHom]
    exact hC
  have hmap := Proofs2.map_fixedSubgroup_eq (K := K) hay
  by_contra hne
  set H := fixedSubgroup K y with hH
  set O := pPrimeCoreOf 2 H with hO
  let X : Subgroup K := O.map (a⁻¹ : MulAut K).toMonoidHom
  have hXne : X ≠ ⊥ := by
    intro hX
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ (a⁻¹ : MulAut K).injective).1 hX)
  have hXodd : Odd (Nat.card X) := by
    rw [Subgroup.card_map_of_injective (a⁻¹ : MulAut K).injective]
    exact TwoThin.card_pPrimeCoreOf_odd H
  obtain ⟨c, hc, x, hx, hcx⟩ := Proofs2.ivk_1_4e F hF K e σ X hXne hXodd
  rw [← hmap] at hc
  obtain ⟨c₁, hc₁, rfl⟩ := hc
  obtain ⟨o, ho, rfl⟩ := hx
  apply hcx
  have : (a⁻¹ : MulAut K) c₁ * (a⁻¹ : MulAut K) o * ((a⁻¹ : MulAut K) c₁)⁻¹ =
      (a⁻¹ : MulAut K) (c₁ * o * c₁⁻¹) := by simp [map_mul, map_inv]
  show (a⁻¹ : MulAut K) c₁ * (a⁻¹ : MulAut K) o * ((a⁻¹ : MulAut K) c₁)⁻¹ ∈ X
  rw [this]
  exact ⟨_, TwoThin.pPrimeCoreOf_normalized H hc₁ ho, rfl⟩

end L2Case


end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.Th2.Obs

theorem b_ivk_oddcent_proof :
    B_ivk_oddcent := by
  intro K _ _ hK y hy s hs hodd w hw
  rcases hK with ⟨⟨e⟩⟩ | hL2
  · exact oddComm_of_oddCommG (oddCommG_fixed_A7 e y hy) s hs hodd w hw
  · obtain ⟨F, _, _, hF, -, ⟨e⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq) hL2
    by_cases hin : y ∈ IVK.innDiagSub e
    · exact oddComm_of_oddCommG (oddCommG_fixed_diag hF e y hy hin) s hs hodd w hw
    · have := pPrimeCoreOf_fixed_outer_eq_bot hF e y hy hin
      rw [this, Subgroup.mem_bot] at hw
      rw [hw]
      simp

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS

theorem b_thm2_p72c_U2_proof
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) :
    B_thm2_p72c_U2 :=
  u2_of_oddcent hL34 h102 b_ivk_oddcent_proof

end CFSG.GH74.GLS
