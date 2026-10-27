module

public import CFSG.GH74.GLS.C3.Prop121.GW56
public import CFSG.GH74.GLS.IVK.L2.Involutions

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.GorensteinWalter CFSG.GH74.GLS.IVK

theorem card_centralizer_subgroup_dvd {X : Type*} [Group X] [Finite X] (L : Subgroup X) (a : L) :
    Nat.card (Subgroup.centralizer ({a} : Set L)) ∣
      Nat.card (Subgroup.centralizer ({(a : X)} : Set X)) := by
  classical
  have hle : (Subgroup.centralizer ({a} : Set L)).map L.subtype ≤
      Subgroup.centralizer ({(a : X)} : Set X) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc')
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective L.subtype_injective] at h1

section PGL2

variable {F : Type} [Field F] [Finite F]

theorem exists_outer_pgl2_involution (hF : IsOddPrimePower (Nat.card F)) {ε : ℤ}
    (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) :
    ∃ A : PGL2 F, orderOf A = 2 ∧
      A ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  have hodd : Odd (Nat.card F) := odd_of_isOddPrimePower hF
  have hidx := pgl2_psl2Range_index_eq_two F hF
  have hεmod := hε
  unfold Int.ModEq at hεmod
  obtain ⟨U, s, w, hU, hcard, hsU, hs2, hs1, hwU, hw2, hinv, hC, hUK⟩ :=
    torus_data hodd (-ε) (by rcases hε1 with rfl | rfl <;> simp)
  have hUc : IsCyclic U := hU
  have h4 : ¬ 4 ∣ Nat.card U := by omega
  refine ⟨s, orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1, fun h => h4 ?_⟩
  exact (DihedralAux.involution_mem_iff _ hidx U hUK hsU hs2 hs1).mp h

end PGL2

theorem hone_of_three_free
    {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥)
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (h3 : ∀ w : X, orderOf w = 2 → ¬ 3 ∣ Nat.card (Subgroup.centralizer ({w} : Set X)))
    {z : X} (hz : orderOf z = 2) (hC : Nat.card (Subgroup.centralizer ({z} : Set X)) = 8)
    {K : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 5))) (hzK : z ∈ K) :
    ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := hK
  have hKcard : Nat.card K = 60 := (Nat.card_congr eK.toEquiv).trans gw56_card_alt_five
  have hnot2 : ¬ IsPGroup 2 X :=
    gw56_not_isPGroup_two (K := K) (by rw [hKcard]; norm_num)
  have hdih : HasDihedralSylowTwo X := fun S => by
    obtain ⟨e⟩ := hSyl S
    exact ⟨2, by norm_num, ⟨e⟩⟩
  let eQ : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases gorensteinWalter X hdih with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ | ⟨-, F, hF, L, hLn, hLodd, hLmodel⟩
  · exact absurd (hTwo.of_equiv eQ) hnot2
  · exfalso
    let f : X ≃* alternatingGroup (Fin 7) := eQ.symm.trans h7
    have hfz : orderOf (f z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (f z) a7t
      (CFSG.Quasithin.I4.isInvolution_of_orderOf_eq_two hfz) a7t_involution
    have h24 : Nat.card (Subgroup.centralizer ({z} : Set X)) = 24 := by
      symm
      rw [← a7t_centralizer_card, ← hg]
      change Nat.card (Subgroup.centralizer {(MulAut.conj g) (f z)}) = _
      rw [CFSG.Quasithin.I4.card_centralizer_map, CFSG.Quasithin.I4.card_centralizer_map]
    rw [hC] at h24
    exact absurd h24 (by norm_num)
  · obtain ⟨p, f, hp, hpodd, hf, hFcard⟩ := hF
    have : Fact p.Prime := ⟨hp⟩
    have : L.Normal := hLn
    set L' : Subgroup X := L.map eQ.toMonoidHom with hL'def
    have hL'n : L'.Normal := hLn.map eQ.toMonoidHom eQ.surjective
    have hL'odd : Odd L'.index := by
      rw [hL'def, Subgroup.index_map_of_injective _ eQ.injective,
        MonoidHom.range_eq_top.mpr eQ.surjective, Subgroup.index_top, mul_one]
      exact hLodd
    let eL : L' ≃* L := (L.equivMapOfInjective eQ.toMonoidHom eQ.injective).symm
    have hinvIn : ∀ u : X, orderOf u = 2 → u ∈ L' := fun u hu =>
      CFSG.Quasithin.I4.mem_of_odd_index hL'odd (k := 1) (by rw [pow_one, hu])
    have hzL : z ∈ L' := hinvIn z hz
    rcases hLmodel with hPSL | hPGL
    · obtain ⟨ePSL⟩ := hPSL
      let eL' : L' ≃* PSL2 F := eL.trans ePSL
      intro a b ha hb
      have haL := hinvIn a ha
      have hbL := hinvIn b hb
      have ha' : orderOf (eL' ⟨a, haL⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ha]
      have hb' : orderOf (eL' ⟨b, hbL⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hb]
      have hc := eL'.symm.toMonoidHom.map_isConj
        (CFSG.Walter.psl2_isConj_of_orderOf_eq_two F hFcard hpodd hf ha' hb')
      have hc' : IsConj (⟨a, haL⟩ : L') ⟨b, hbL⟩ := by simpa using hc
      simpa using L'.subtype.map_isConj hc'
    · exfalso
      obtain ⟨ePGL⟩ := hPGL
      let eP : L' ≃* PGL2 F := eL.trans ePGL
      have hFodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, hFcard⟩
      have hqodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
      have hq3' : 3 ≤ Nat.card F := by
        rw [hFcard]
        calc 3 ≤ p := by
              have := hp.two_le
              rcases hpodd with ⟨k, hk⟩
              omega
          _ ≤ p ^ f := Nat.le_self_pow (by omega) p
      have hSimpleA : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hSimpleK : IsSimpleGroup K := eK.isSimpleGroup
      have hKL : K ≤ L' := by
        let φ : K →* X ⧸ L' := (QuotientGroup.mk' L').comp K.subtype
        have hn : φ.ker.Normal := MonoidHom.normal_ker φ
        rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker) with h | h
        · exfalso
          have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
          have hd : Nat.card K ∣ Nat.card (X ⧸ L') := Subgroup.card_dvd_of_injective φ hinj
          rw [← Subgroup.index_eq_card, hKcard] at hd
          obtain ⟨k, hk⟩ := hL'odd
          have : 2 ∣ L'.index := (by norm_num : (2 : ℕ) ∣ 60).trans hd
          omega
        · intro k hk
          have : (⟨k, hk⟩ : K) ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
          exact (QuotientGroup.eq_one_iff k).1 (MonoidHom.mem_ker.1 this)
      have hLcard : Nat.card L' = Nat.card F * (Nat.card F ^ 2 - 1) :=
        (Nat.card_congr eP.toEquiv).trans (pgl2_card_formula F)
      have hKdvd : 60 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [← hLcard, ← hKcard]
        exact Subgroup.card_dvd_of_le hKL
      have hq3 : 3 < Nat.card F := by
        by_contra hcon
        have h3q : Nat.card F = 3 := by omega
        rw [h3q] at hKdvd
        revert hKdvd
        norm_num
      obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
        have h4 := Nat.odd_iff.mp hqodd
        by_cases h : Nat.card F % 4 = 1
        · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
        · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
      have hεmod := hε
      unfold Int.ModEq at hεmod
      have hidx := pgl2_psl2Range_index_eq_two F hFodd
      have hRn : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.Normal :=
        Subgroup.normal_of_index_eq_two hidx
      let ψ : K →* PGL2 F := eP.toMonoidHom.comp (Subgroup.inclusion hKL)
      have hψR : ∀ k : K,
          ψ k ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
        let χ : K →* PGL2 F ⧸
            (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
          (QuotientGroup.mk' _).comp ψ
        have hn : χ.ker.Normal := MonoidHom.normal_ker χ
        rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker) with h | h
        · exfalso
          have hinj : Function.Injective χ := (MonoidHom.ker_eq_bot_iff χ).mp h
          have hd : Nat.card K ∣ Nat.card (PGL2 F ⧸
              (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :=
            Subgroup.card_dvd_of_injective χ hinj
          rw [← Subgroup.index_eq_card, hidx, hKcard] at hd
          revert hd
          norm_num
        · intro k
          have : k ∈ χ.ker := by rw [h]; exact Subgroup.mem_top _
          exact (QuotientGroup.eq_one_iff (ψ k)).1 (MonoidHom.mem_ker.1 this)
      have hA2 : orderOf (eP ⟨z, hzL⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
      have hzR : eP ⟨z, hzL⟩ ∈
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
        hψR ⟨z, hzK⟩
      obtain ⟨m, hm, ⟨eCm⟩⟩ :=
        (pgl2_involution_centralizer_dihedral hFodd hq3 hε1 hε hA2).1 hzR
      have hm0 : 0 < m := by omega
      have : NeZero m := ⟨by omega⟩
      have hcm : Nat.card (Subgroup.centralizer ({eP ⟨z, hzL⟩} : Set (PGL2 F))) = 2 * m := by
        rw [Nat.card_congr eCm.toEquiv, DihedralGroup.nat_card]
      have hdvdz : 2 * m ∣ 8 := by
        have h1 := CFSG.Quasithin.I4.card_centralizer_map eP ⟨z, hzL⟩
        have h2 := card_centralizer_subgroup_dvd L' ⟨z, hzL⟩
        rw [← h1, hcm] at h2
        rwa [hC] at h2
      have hm4 : m ∣ 4 := by
        have h8 : 2 * m ∣ 2 * 4 := by simpa using hdvdz
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h8
      have hm4' : 4 ∣ m := by omega
      have hmeq : m = 4 := Nat.dvd_antisymm hm4 hm4'
      have hq5 : Nat.card F = 5 ∧ ε = 1 := by omega
      obtain ⟨A, hA, hAR⟩ := exists_outer_pgl2_involution hFodd hε1 hε
      obtain ⟨m', hm', ⟨eCm'⟩⟩ :=
        (pgl2_involution_centralizer_dihedral hFodd hq3 hε1 hε hA).2 hAR
      have hm'0 : 0 < m' := by omega
      have : NeZero m' := ⟨by omega⟩
      have hcm' : Nat.card (Subgroup.centralizer ({A} : Set (PGL2 F))) = 2 * m' := by
        rw [Nat.card_congr eCm'.toEquiv, DihedralGroup.nat_card]
      let w : L' := eP.symm A
      have hAw : eP w = A := eP.apply_symm_apply A
      have hw2 : orderOf (w : X) = 2 := by
        have h1 : orderOf (w : X) = orderOf w := Subgroup.orderOf_coe w
        have h2 : orderOf (eP w) = orderOf w := MulEquiv.orderOf_eq eP w
        rw [h1, ← h2, hAw, hA]
      have hwdvd := card_centralizer_subgroup_dvd L' w
      have h1 := CFSG.Quasithin.I4.card_centralizer_map eP w
      rw [hAw, hcm'] at h1
      have hm'6 : m' = 6 := by omega
      rw [← h1, hm'6] at hwdvd
      exact h3 (w : X) hw2 ((by norm_num : (3 : ℕ) ∣ 2 * 6).trans hwdvd)

theorem gw5_of_three_free
    {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥)
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (h3 : ∀ w : X, orderOf w = 2 → ¬ 3 ∣ Nat.card (Subgroup.centralizer ({w} : Set X)))
    {z : X} (hz : orderOf z = 2) (hC : Nat.card (Subgroup.centralizer ({z} : Set X)) = 8)
    {K : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 5))) (hzK : z ∈ K) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) :=
  gw56_five hO hSyl (hone_of_three_free hO hSyl h3 hz hC hK hzK) hz hC hK

end CFSG.GH74.GLS.C3.Prop121
