module

public import CFSG.GH74.GLS.IVK.L2.Lemma13

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GorensteinWalter

namespace OrdL2

theorem isInvolution_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    BenderSuzuki.PFAppendixIII.IsInvolution x := by
  obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.mp hx
  exact ⟨h2, h1⟩

theorem commutator_le_of_index_eq_two {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) :
    commutator G ≤ H := by
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hcard : Nat.card (G ⧸ H) = 2 := by rw [← Subgroup.index_eq_card]; exact hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  have hker := Abelianization.commutator_subset_ker (QuotientGroup.mk' H)
  rwa [QuotientGroup.ker_mk'] at hker

end OrdL2

theorem L2_involution_facts {I : Type} [Group I] [Finite I] {q : ℕ}
    (hI : CFSG.GH74.GLS.IVK.IsL2 I (fun r => r = q)) (hq5 : 5 ≤ q) (hqodd : Odd q)
    {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1) (hε : (q : ℤ) ≡ ε [ZMOD 4]) {δ : ℕ}
    (hδ : ((2 * δ : ℕ) : ℤ) = q - ε) :
    2 * Nat.card I = q * (q ^ 2 - 1) ∧
    (∀ u v : I, orderOf u = 2 → orderOf v = 2 → ∃ g : I, g * u * g⁻¹ = v) ∧
    (∀ u : I, orderOf u = 2 → Nonempty (↥(centralizer ({u} : Set I)) ≃* DihedralGroup δ)) := by
  obtain ⟨F₀, _, _, hq, ⟨e⟩⟩ := hI
  have hq' : Nat.card F₀ = q := hq
  have hL : IVK.L2Field F₀ := ⟨hq' ▸ hqodd, by omega⟩
  have hpp : IsOddPrimePower (Nat.card F₀) := IVK.isOddPrimePower_of_L2Field hL
  refine ⟨?_, ?_, ?_⟩
  · have hfactorEven : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hqodd.pow (show Odd (1 : ℕ) from odd_one)
    have hdvd : 2 ∣ q * (q ^ 2 - 1) := dvd_mul_of_dvd_right hfactorEven.two_dvd _
    have hcard := IVK.card_eq_of_L2Field e hL
    rw [hq'] at hcard
    rw [hcard]
    exact Nat.mul_div_cancel' hdvd
  · intro u v hu hv
    have hu' : orderOf (IVK.toPSL e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (IVK.toPSL e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F₀ hpp _ _
      (OrdL2.isInvolution_of_orderOf_eq_two hu') (OrdL2.isInvolution_of_orderOf_eq_two hv')
    refine ⟨(IVK.toPSL e).symm g, (IVK.toPSL e).injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  · intro u hu
    have hδ' : ((2 * δ : ℕ) : ℤ) = (Nat.card F₀ : ℤ) - ε := by rw [hq']; exact hδ
    have hε' : (Nat.card F₀ : ℤ) ≡ ε [ZMOD 4] := by rw [hq']; exact hε
    obtain ⟨-, ⟨k, hk, -, ⟨φ⟩⟩, -⟩ := IVK.ivk_1_3a F₀ hL I e ε hε1 hε' (2 * δ) hδ' u hu
    have hkδ : δ = k := by omega
    rw [hkδ]
    exact ⟨φ⟩

theorem pgl2_outer_involution_count {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4])
    {s : ℕ} (hs : (s : ℤ) = Nat.card F + ε) :
    Nat.card (PGL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) ∧
    Nat.card {y : PGL2 F // orderOf y = 2 ∧ y ∉ commutator (PGL2 F)} * (2 * s) =
      Nat.card (PGL2 F) ∧
    (∀ H : Subgroup (PGL2 F), H.index = 2 → H = commutator (PGL2 F)) := by
  have hL : IVK.L2Field F := ⟨hodd, by omega⟩
  have hpp : IsOddPrimePower (Nat.card F) := IVK.isOddPrimePower_of_L2Field hL
  have hq3 : 3 < Nat.card F := by omega
  have hcomm : commutator (PGL2 F) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hpp hq3
  have hidx : (commutator (PGL2 F)).index = 2 := by
    rw [hcomm]
    exact pgl2_psl2Range_index_eq_two F hpp
  refine ⟨pgl2_card_formula F, ?_, ?_⟩
  ·
    obtain ⟨U, y0, w, hU, hcardU, hy0U, hy02, hy01, hwU, hw2, hinv, hC, hUK⟩ :=
      IVK.torus_data hodd (-ε) (by rcases hε1 with rfl | rfl <;> simp)
    have hUc : IsCyclic U := hU
    have h4 : ¬ 4 ∣ Nat.card U := by
      have hmod := hε
      unfold Int.ModEq at hmod
      omega
    have hy0J : y0 ∉ commutator (PGL2 F) := by
      rw [hcomm]
      intro h
      exact h4 ((IVK.DihedralAux.involution_mem_iff _ (hcomm ▸ hidx) U hUK hy0U hy02 hy01).mp h)
    have hy0ord : orderOf y0 = 2 := orderOf_eq_prime (by rwa [← pow_two] at hy02) hy01
    obtain ⟨m, hm, ⟨φ⟩⟩ := (IVK.pgl2_involution_centralizer_dihedral hpp hq3 hε1 hε hy0ord).2
      (by rw [← hcomm]; exact hy0J)
    have hms : m = s := by omega
    have hcent : Nat.card (centralizer ({y0} : Set (PGL2 F))) = 2 * s := by
      rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, hms]
    have horb : Nat.card (MulAction.orbit (ConjAct (PGL2 F)) y0) *
        Nat.card (centralizer ({y0} : Set (PGL2 F))) = Nat.card (PGL2 F) := by
      have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct (PGL2 F)) y0)
      rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
      have h2 : Nat.card (ConjAct (PGL2 F)) = Nat.card (PGL2 F) :=
        Nat.card_congr (ConjAct.toConjAct (G := PGL2 F)).toEquiv.symm
      rw [h2] at h1
      rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, mul_comm]
      exact h1
    have horbit : Nat.card {y : PGL2 F // orderOf y = 2 ∧ y ∉ commutator (PGL2 F)} =
        Nat.card (MulAction.orbit (ConjAct (PGL2 F)) y0) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun y => ?_))
      constructor
      · rintro ⟨hy2, hyJ⟩
        have hconj := pgl2_outer_involutions_conjugate F hpp hq3
          (OrdL2.isInvolution_of_orderOf_eq_two hy0ord)
          (OrdL2.isInvolution_of_orderOf_eq_two hy2) hy0J hyJ
        obtain ⟨c, hc⟩ := isConj_iff.mp hconj
        refine MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct c, ?_⟩
        rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        exact hc
      · intro hy
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
        rw [ConjAct.smul_def]
        refine ⟨?_, ?_⟩
        · have h := orderOf_injective (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom
            (MulAut.conj (ConjAct.ofConjAct g)).injective y0
          rw [hy0ord] at h
          exact h
        · intro hmem
          apply hy0J
          have h := (inferInstance : (commutator (PGL2 F)).Normal).conj_mem _ hmem
            (ConjAct.ofConjAct g)⁻¹
          have h' : (ConjAct.ofConjAct g)⁻¹ * (ConjAct.ofConjAct g * y0 * (ConjAct.ofConjAct g)⁻¹) *
              ((ConjAct.ofConjAct g)⁻¹)⁻¹ = y0 := by group
          rwa [h'] at h
    rw [horbit, ← hcent]
    exact horb
  ·
    intro H hH
    have hle := OrdL2.commutator_le_of_index_eq_two hH
    have h1 := Subgroup.card_mul_index H
    have h2 := Subgroup.card_mul_index (commutator (PGL2 F))
    rw [hH] at h1
    rw [hidx] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

end CFSG.GH74.GLS.SP.Local
