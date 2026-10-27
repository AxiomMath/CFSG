module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCen
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreGamma
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Mirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoNtwo

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.OddStandard.Solomon75.Sec5Two

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

private theorem odd_card_sup_of_le_normalizer' {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup X)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

private theorem card_sup_mul_card_inf {H N : Subgroup X} (hHN : H ≤ normalizer (N : Set X)) :
    Nat.card (H ⊔ N : Subgroup X) * Nat.card (H ⊓ N : Subgroup X) =
      Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  rw [← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv] at h1
  have h3 : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective (f := _),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h3] at h2
  rw [h1, h2]
  ring

private theorem exists_conj_le_of_le_sup {C O Q : Subgroup X} (hCO : C ≤ normalizer (O : Set X))
    (hodd : Odd (Nat.card O)) (hQ : IsPGroup 2 ↥Q) (hQle : Q ≤ C ⊔ O) :
    ∃ o ∈ O, ∀ x ∈ Q, o * x * o⁻¹ ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 C
  have hPR : IsSylowOf 2 P (C ⊔ O) := isSylowOf_sup hP hCO hodd
  obtain ⟨k, hk, hkQ⟩ := exists_conj_le_sylow' hPR hQle hQ
  obtain ⟨c, hc, o, ho, rfl⟩ := exists_mul_of_mem_sup hCO hk
  refine ⟨o, ho, fun x hx => ?_⟩
  have h1 := hkQ x hx
  have h2 : o * x * o⁻¹ = c⁻¹ * (c * o * x * (c * o)⁻¹) * c := by group
  rw [h2]
  exact C.mul_mem (C.mul_mem (C.inv_mem hc) (hP.le h1)) hc

private theorem exists_conj_mem_of_involution {C O : Subgroup X}
    (hCO : C ≤ normalizer (O : Set X)) (hodd : Odd (Nat.card O)) {w : X} (hw2 : orderOf w = 2)
    (hw : w ∈ C ⊔ O) : ∃ o ∈ O, o * w * o⁻¹ ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2]; norm_num)
  obtain ⟨o, ho, h⟩ := exists_conj_le_of_le_sup hCO hodd hQ (Subgroup.zpowers_le.2 hw)
  exact ⟨o, ho, h w (Subgroup.mem_zpowers w)⟩

private theorem exists_conj_le_of_cover {Q₀ O Xs : Subgroup X} (hQO : Q₀ ≤ normalizer (O : Set X))
    (hodd : Odd (Nat.card O)) (hQ : IsPGroup 2 ↥Q₀)
    (hcov : ∀ q ∈ Q₀, ∃ x ∈ Xs, ∃ o ∈ O, q = x * o) :
    ∃ o ∈ O, ∀ q ∈ Q₀, o * q * o⁻¹ ∈ Xs := by
  set R : Subgroup X := Q₀ ⊔ O with hR
  set Y : Subgroup X := Xs ⊓ R with hY
  have hRn : R ≤ normalizer (O : Set X) := sup_le hQO Subgroup.le_normalizer
  have hYn : Y ≤ normalizer (O : Set X) := inf_le_right.trans hRn
  have hQY : Q₀ ≤ Y ⊔ O := by
    intro q hq
    obtain ⟨x, hx, o, ho, hqx⟩ := hcov q hq
    have hxR : x ∈ R := by
      have : x = q * o⁻¹ := by rw [hqx]; group
      rw [this]
      exact R.mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (O.inv_mem ho))
    rw [hqx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show x ∈ Y from ⟨hx, hxR⟩))
      (Subgroup.mem_sup_right ho)
  obtain ⟨o, ho, h⟩ := exists_conj_le_of_le_sup hYn hodd hQ hQY
  exact ⟨o, ho, fun q hq => (h q hq).1⟩

private theorem inf_le_oddCoreOf_of_normalizes {K O : Subgroup X} (hodd : Odd (Nat.card O))
    (hKO : K ≤ normalizer (O : Set X)) : O ⊓ K ≤ oddCoreOf K := by
  refine le_oddCoreOf_of_normalized inf_le_right ?_
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
  intro k hk
  exact mem_normalizer_inf (hKO hk) (Subgroup.le_normalizer hk)

private theorem oddCoreOf_K0_le {O : Subgroup X}
    (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O) :
    pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ≤ O := by
  rw [core_K0_eq]
  exact inf_le_right.trans hOc

private theorem comm_conj_mem {O : Subgroup X} {a w o : X} (ha : a ∈ normalizer (O : Set X))
    (hw : w ∈ normalizer (O : Set X)) (ho : o ∈ O) (hc : ⁅a, w⁆ ∈ O) :
    ⁅a, o * w * o⁻¹⁆ ∈ O := by
  have hn : ∀ x ∈ normalizer (O : Set X), ∀ y ∈ O, x * y * x⁻¹ ∈ O := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 hx y).1 hy
  have hp : ⁅a, o⁆ ∈ O := by
    have : ⁅a, o⁆ = (a * o * a⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact O.mul_mem (hn a ha o ho) (O.inv_mem ho)
  have e : ⁅a, o * w * o⁻¹⁆ =
      ⁅a, o⁆ * o * ⁅a, w⁆ * (w * (o⁻¹ * ⁅a, o⁆⁻¹ * o) * w⁻¹) * o⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine O.mul_mem (O.mul_mem (O.mul_mem (O.mul_mem hp ho) hc) ?_) (O.inv_mem ho)
  exact hn w hw _ (O.mul_mem (O.mul_mem (O.inv_mem ho) (O.inv_mem hp)) ho)

private theorem exists_conj_eq_of_zpowers {W : Subgroup X} {a b : X} (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (ha : IsSylowTwoIn W (zpowers a)) (hb : IsSylowTwoIn W (zpowers b)) :
    ∃ y ∈ W, b = y * a * y⁻¹ := by
  obtain ⟨y, hy, hyq⟩ := exists_conj_of_isSylowTwoIn ha hb
  refine ⟨y, hy, ?_⟩
  have hmem : b ∈ (zpowers a).map (MulAut.conj y).toMonoidHom := hyq ▸ Subgroup.mem_zpowers b
  rw [MonoidHom.map_zpowers] at hmem
  have hord : orderOf ((MulAut.conj y).toMonoidHom a) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) a
    rw [ha2] at this
    exact this
  rcases zpowers_eq_of_orderOf_two hord b hmem with e | e
  · exfalso
    rw [e, orderOf_one] at hb2
    omega
  · simpa [MulAut.conj_apply] using e

private theorem comm_oddCore_of_comm_hull {O A : Subgroup X} (hodd : Odd (Nat.card O))
    (hCO : centralizer ({z} : Set X) ≤ normalizer (O : Set X))
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {v : X}
    (hvC : v ∈ centralizer ({z} : Set X)) (hcomm : ∀ a ∈ A, ⁅a, v⁆ ∈ O) :
    ∀ a ∈ A, ⁅a, v⁆ ∈ oddCoreOf A := by
  have hnC : ∀ a ∈ A, ⁅a, v⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) := by
    intro a ha
    have hK : ⁅a, v⁆ ∈ K0 X n (centralizer ({z} : Set X)) := by
      have e : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (comp_le_K0 hA ha)
        (conj_mem_K0 n (Subgroup.le_normalizer hvC) (Subgroup.inv_mem _ (comp_le_K0 hA ha)))
    exact inf_le_oddCoreOf_of_normalizes hodd (fun k hk => hCO (K0_le n _ hk)) ⟨hcomm a ha, hK⟩
  exact (normalizes_of_comm hA (Subgroup.le_normalizer hvC) hnC).2

theorem oddHull_sup_core (h : Sec5Data X n z (zpowers z) S) {O : Subgroup X}
    (hO : OddHull X n z O) :
    OddHull X n z (O ⊔ oddCoreOf (centralizer ({z} : Set X))) := by
  obtain ⟨hodd, hCO, hcomp⟩ := hO
  refine ⟨?_, ?_, ?_⟩
  · rw [sup_comm]
    exact odd_card_sup_of_le_normalizer' ((oddCoreOf_le _).trans hCO)
      (odd_card_oddCoreOf _) hodd
  · intro c hc
    exact mem_normalizer_sup (hCO hc) (le_normalizer_oddCoreOf _ hc)
  · intro b hb
    exact (hcomp b hb).trans (sup_le_sup_right le_sup_left _)

private theorem cen_le_hull_of_involution (h : Sec5Data X n z (zpowers z) S) {O : Subgroup X}
    (hO : OddHull X n z O) {A A' : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') (hne : A' ≠ A) {b : X} (hb : b ∈ A)
    (hb2 : orderOf b = 2) :
    centralizer ({b} : Set X) ≤ O ⊔ centralizer ({z} : Set X) := by
  have hbC : b ∈ centralizer ({z} : Set X) := comp_le hA hb
  have hcomm : ∀ a ∈ A', ⁅a, b⁆ ∈ oddCoreOf A' :=
    (normalizes_of_comm hA' (Subgroup.le_normalizer hbC) fun a ha =>
      comm_mem_of_ne hA' hA hne a ha b hb).2
  exact (cen_eq_oddCoreOf_sup_of_comm h hA' hb2 hbC hcomm).le.trans
    (sup_le (hO.2.2 b ⟨A, hA, hb, hb2⟩) (inf_le_left.trans le_sup_right))

theorem cen_le_of_oddHull (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z)
    {O : Subgroup X} (hO : OddHull X n z O) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {w : X} (hw2 : orderOf w = 2)
    (hwC : w ∈ centralizer ({z} : Set X)) (hcomm : ∀ a ∈ A, ⁅a, w⁆ ∈ oddCoreOf A) :
    centralizer ({w} : Set X) ≤ O ⊔ centralizer ({z} : Set X) := by
  obtain ⟨A', hA', hA'ne⟩ := exists_comp_ne A hne
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hAK : IsPCompIn 2 (K0 X n (centralizer ({z} : Set X))) A := comp_isPCompIn_K0 hA
  have hnorm : w ∈ normalizer (A : Set X) :=
    (normalizes_of_comm hA (Subgroup.le_normalizer hwC) fun a ha =>
      oddCoreOf_le_of_isPCompIn hAK (hcomm a ha)).1
  obtain ⟨Q, hQ, hQw⟩ := exists_sylow_le_cen hw2 hnorm hcomm
  obtain ⟨E, hEQ, hE, hE4⟩ := exists_four_le_sylow hn8 hA hQ
  have hEA : E ≤ A := hEQ.trans hQ.le
  have hEw : E ≤ centralizer ({w} : Set X) := hEQ.trans hQw
  have hEN : E ≤ normalizer (oddCoreOf (centralizer ({w} : Set X)) : Set X) :=
    hEw.trans (le_normalizer_oddCoreOf _)
  have hgen := CoreAux.le_iSup_inf_cen_of_four hE hE4 hEN (odd_card_oddCoreOf _)
  have hN : oddCoreOf (centralizer ({w} : Set X)) ≤ O ⊔ centralizer ({z} : Set X) := by
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => inf_le_right.trans ?_)
    have ha2 : a * a = 1 := AhatData.sq_of_isElemAbelian hE a ha
    have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    exact cen_le_hull_of_involution h hO hA hA' hA'ne (hEA ha) hao
  exact (cen_eq_oddCoreOf_sup_of_comm h hA hw2 hwC hcomm).le.trans
    (sup_le hN (inf_le_left.trans le_sup_right))

theorem pPrimeCoreOf_hull_K0 (h : Sec5Data X n z (zpowers z) S) {O : Subgroup X}
    (hO : OddHull X n z O) (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O) :
    pPrimeCoreOf 2 (O ⊔ K0 X n (centralizer ({z} : Set X))) = O := by
  obtain ⟨hodd, hCO, -⟩ := hO
  set C := centralizer ({z} : Set X) with hCdef
  set K := K0 X n C with hK
  have hKO : K ≤ normalizer (O : Set X) := fun k hk => hCO (K0_le n C hk)
  have hDn : O ⊔ K ≤ normalizer (O : Set X) := sup_le Subgroup.le_normalizer hKO
  have hge : O ≤ pPrimeCoreOf 2 (O ⊔ K) := le_oddCoreOf_of_normalized le_sup_left hDn hodd
  refine le_antisymm ?_ hge
  intro x hx
  have hxD : x ∈ K ⊔ O := by
    rw [sup_comm]
    exact oddCoreOf_le (O ⊔ K) hx
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup hKO hxD
  have hkR : k ∈ pPrimeCoreOf 2 (O ⊔ K) := by
    have : k = (k * o) * o⁻¹ := by group
    rw [this]
    exact (pPrimeCoreOf 2 (O ⊔ K)).mul_mem hx ((pPrimeCoreOf 2 (O ⊔ K)).inv_mem (hge ho))
  have hRn : K ≤ normalizer (pPrimeCoreOf 2 (O ⊔ K) : Set X) := fun k' hk' =>
    le_normalizer_oddCoreOf (O ⊔ K) (Subgroup.mem_sup_right hk')
  have hkK : k ∈ oddCoreOf K :=
    inf_le_oddCoreOf_of_normalizes (odd_card_oddCoreOf (O ⊔ K)) hRn ⟨hkR, hk⟩
  exact O.mul_mem (oddCoreOf_K0_le hOc hkK) ho

theorem normalizer_hull_K0 (h : Sec5Data X n z (zpowers z) S) {O : Subgroup X}
    (hO : OddHull X n z O) (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O) :
    normalizer ((O ⊔ K0 X n (centralizer ({z} : Set X)) : Subgroup X) : Set X) =
      O ⊔ centralizer ({z} : Set X) := by
  have hD4 := pPrimeCoreOf_hull_K0 h hO hOc
  obtain ⟨hodd, hCO, -⟩ := hO
  set C := centralizer ({z} : Set X) with hCdef
  set K := K0 X n C with hK
  set D := O ⊔ K with hD
  have hKC : K ≤ C := K0_le n C
  have hKO : K ≤ normalizer (O : Set X) := fun k hk => hCO (hKC hk)
  have hOK : pPrimeCoreOf 2 K ≤ O := oddCoreOf_K0_le hOc
  have hzK : z ∈ zStar K := h.pair.sylow.1 (Subgroup.mem_zpowers z)
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzD : z ∈ D := Subgroup.mem_sup_right hzK.1
  have hCD : C ≤ normalizer (D : Set X) := fun c hc =>
    mem_normalizer_sup (hCO hc) (Sec5Data.le_normalizer_K0 X n C hc)
  apply le_antisymm
  swap
  · exact sup_le (fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_left ho)) hCD
  have hzZ : z ∈ zStar D := by
    refine ⟨hzD, hCD hzC, ?_, ?_⟩
    · rw [hD4]
      exact hCO hzC
    · intro d hd
      rw [hD4]
      have hd' : d ∈ K ⊔ O := by rw [sup_comm]; exact hd
      obtain ⟨k₁, hk₁, o, ho, rfl⟩ := exists_mul_of_mem_sup hKO hd'
      have e : ⁅k₁ * o, z⁆ = (k₁ * ⁅o, z⁆ * k₁⁻¹) * ⁅k₁, z⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have h1 : ⁅o, z⁆ ∈ O := by
        have : ⁅o, z⁆ = o * (z * o⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 (hCO hzC) o⁻¹).1 (O.inv_mem ho))
      have h2 : k₁ * ⁅o, z⁆ * k₁⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.1 (hCO (hKC hk₁)) _).1 h1
      exact O.mul_mem h2 (hOK (hzK.2.2.2 k₁ hk₁))
  have hZD_le : zStar D ≤ O ⊔ zpowers z := by
    intro x hx
    obtain ⟨hxD, -, -, hxc⟩ := hx
    have hxD' : x ∈ K ⊔ O := by rw [sup_comm]; exact hxD
    obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup hKO hxD'
    have hkz : k ∈ zStar K := by
      refine ⟨hk, Subgroup.le_normalizer hk, mem_normalizer_pPrimeCoreOf_of_mem hk, fun d hd => ?_⟩
      have h1 : ⁅d, k * o⁆ ∈ pPrimeCoreOf 2 D := hxc d (Subgroup.mem_sup_right hd)
      rw [hD4] at h1
      have e : ⁅d, k⁆ = ⁅d, k * o⁆ * (k * ⁅d, o⁆ * k⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      have h2 : ⁅d, k⁆ ∈ O := by
        rw [e]
        refine O.mul_mem h1 (O.inv_mem ?_)
        have h3 : ⁅d, o⁆ ∈ O := by
          have : ⁅d, o⁆ = (d * o * d⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
          rw [this]
          exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hCO (hKC hd)) o).1 ho) (O.inv_mem ho)
        exact (Subgroup.mem_normalizer_iff.1 (hCO (hKC hk)) _).1 h3
      have h4 : ⁅d, k⁆ ∈ K := by
        have : ⁅d, k⁆ = d * k * d⁻¹ * k⁻¹ := rfl
        rw [this]
        exact K.mul_mem (K.mul_mem (K.mul_mem hd hk) (K.inv_mem hd)) (K.inv_mem hk)
      exact inf_le_oddCoreOf_of_normalizes hodd hKO ⟨h2, h4⟩
    have h5 := zStar_le_pPrimeCoreOf_sup h.pair.sylow hkz
    exact (O ⊔ zpowers z).mul_mem (sup_le_sup_right hOK _ h5) (Subgroup.mem_sup_left ho)
  have hsyl : IsSylowTwoIn (zStar D) (zpowers z) :=
    isSylowTwoIn_of_le_sup_odd (Subgroup.zpowers_le.2 hzZ) h.isPGroup_Z hodd
      (Subgroup.zpowers_le.2 (hCO hzC)) hZD_le
  intro g hg
  have hgD : D.map (MulAut.conj g).toMonoidHom = D := map_conj_eq_of_mem_normalizer hg
  have hY : (zStar D).map (MulAut.conj g).toMonoidHom = zStar D := by
    have := zStar_map_mulEquiv (MulAut.conj g) D
    rw [hgD] at this
    exact this.symm
  have hQ : IsSylowTwoIn (zStar D) (zpowers (g * z * g⁻¹)) := by
    have := hsyl.map_mulEquiv (MulAut.conj g)
    rw [hY, MonoidHom.map_zpowers] at this
    simpa [MulAut.conj_apply] using this
  have hgz2 : orderOf (g * z * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rw [hz2] at this
    simpa [MulAut.conj_apply] using this
  obtain ⟨y, hy, hyeq⟩ := exists_conj_eq_of_zpowers hz2 hgz2 hsyl hQ
  have hyH : y ∈ O ⊔ C := (sup_le_sup_left (Subgroup.zpowers_le.2 hzC) O) (hZD_le hy)
  have hyg : y⁻¹ * g ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y⁻¹ * g * z = y⁻¹ * (g * z * g⁻¹) * g := by group
      _ = y⁻¹ * (y * z * y⁻¹) * g := by rw [hyeq]
      _ = z * (y⁻¹ * g) := by group
  have : g = y * (y⁻¹ * g) := by group
  rw [this]
  exact (O ⊔ C).mul_mem hyH (Subgroup.mem_sup_right hyg)

private theorem isSylowTwoIn_zStar_K0_map (h : Sec5Data X n z (zpowers z) S) (φ : X ≃* X) :
    IsSylowTwoIn (zStar (K0 X n (centralizer ({φ z} : Set X)))) (zpowers (φ z)) := by
  have hK : K0 X n (centralizer ({φ z} : Set X)) =
      (K0 X n (centralizer ({z} : Set X))).map φ.toMonoidHom := by
    rw [centralizer_singleton_map_mulEquiv, K0_map]
  rw [hK, zStar_map_mulEquiv]
  have := h.pair.sylow.map_mulEquiv φ
  rw [MonoidHom.map_zpowers] at this
  exact this

theorem mem_of_conj_cen_le_hull (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z)
    {O : Subgroup X} (hO : OddHull X n z O) (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O)
    {k : X} (hk : (centralizer ({z} : Set X)).map (MulAut.conj k⁻¹).toMonoidHom ≤
      O ⊔ centralizer ({z} : Set X)) :
    k ∈ O ⊔ centralizer ({z} : Set X) := by
  have hodd := hO.1
  have hCO := hO.2.1
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hHn : O ⊔ centralizer ({z} : Set X) ≤ normalizer (O : Set X) :=
    sup_le Subgroup.le_normalizer hCO
  obtain ⟨A₁, -, hA₁, -, -⟩ := hne
  obtain ⟨w, hwdef⟩ : ∃ w : X, w = k⁻¹ * z * k := ⟨_, rfl⟩
  have hφw : (MulAut.conj k⁻¹) z = w := by rw [hwdef]; simp [MulAut.conj_apply]
  have hw2 : orderOf w = 2 := by
    rw [← hφw, MulEquiv.orderOf_eq]
    exact hz2
  have hCw : centralizer ({w} : Set X) =
      (centralizer ({z} : Set X)).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [← hφw]
    exact centralizer_singleton_map_mulEquiv (MulAut.conj k⁻¹) z
  have hCwH : centralizer ({w} : Set X) ≤ O ⊔ centralizer ({z} : Set X) := hCw.le.trans hk
  have hwH : w ∈ O ⊔ centralizer ({z} : Set X) :=
    hCwH (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hCwn : centralizer ({w} : Set X) ≤ normalizer (O : Set X) := hCwH.trans hHn
  have hcC : Nat.card (centralizer ({w} : Set X)) = Nat.card (centralizer ({z} : Set X)) := by
    rw [hCw]
    exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have hOw : oddCoreOf (centralizer ({w} : Set X)) =
      (oddCoreOf (centralizer ({z} : Set X))).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [hCw]
    exact pPrimeCoreOf_map_mulEquiv (MulAut.conj k⁻¹) (centralizer ({z} : Set X))
  have hcardOw : Nat.card (oddCoreOf (centralizer ({w} : Set X))) =
      Nat.card (oddCoreOf (centralizer ({z} : Set X))) := by
    rw [hOw]
    exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have hinf : Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X) ≤
      Nat.card (centralizer ({z} : Set X) ⊓ O : Subgroup X) := by
    calc Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X)
        ≤ Nat.card (oddCoreOf (centralizer ({w} : Set X))) :=
          Subgroup.card_le_of_le (by rw [inf_comm]; exact inf_le_oddCoreOf_of_normalizes hodd hCwn)
      _ = Nat.card (oddCoreOf (centralizer ({z} : Set X))) := hcardOw
      _ ≤ Nat.card (centralizer ({z} : Set X) ⊓ O : Subgroup X) :=
          Subgroup.card_le_of_le (le_inf (oddCoreOf_le _) hOc)
  have e1 := card_sup_mul_card_inf hCO
  have e2 := card_sup_mul_card_inf hCwn
  have hpos : 0 < Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X) := Nat.card_pos
  have hcard : Nat.card (centralizer ({z} : Set X) ⊔ O : Subgroup X) ≤
      Nat.card (centralizer ({w} : Set X) ⊔ O : Subgroup X) := by
    have : Nat.card (centralizer ({z} : Set X) ⊔ O : Subgroup X) *
        Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X) ≤
        Nat.card (centralizer ({w} : Set X) ⊔ O : Subgroup X) *
          Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X) := by
      calc Nat.card (centralizer ({z} : Set X) ⊔ O : Subgroup X) *
            Nat.card (centralizer ({w} : Set X) ⊓ O : Subgroup X)
          ≤ Nat.card (centralizer ({z} : Set X) ⊔ O : Subgroup X) *
            Nat.card (centralizer ({z} : Set X) ⊓ O : Subgroup X) := Nat.mul_le_mul_left _ hinf
        _ = Nat.card (centralizer ({z} : Set X)) * Nat.card O := e1
        _ = Nat.card (centralizer ({w} : Set X)) * Nat.card O := by rw [hcC]
        _ = _ := e2.symm
    exact Nat.le_of_mul_le_mul_right this hpos
  have hCwO : centralizer ({w} : Set X) ⊔ O = centralizer ({z} : Set X) ⊔ O :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (hCwH.trans (sup_comm O _).le) le_sup_right) hcard
  have hcomm_w : ∀ a ∈ O ⊔ centralizer ({z} : Set X), ⁅a, w⁆ ∈ O := by
    intro a ha
    have ha' : a ∈ centralizer ({w} : Set X) ⊔ O := by
      rw [hCwO, sup_comm]
      exact ha
    obtain ⟨c, hc, o, ho, rfl⟩ := exists_mul_of_mem_sup hCwn ha'
    have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcw' : c⁻¹ * w⁻¹ = w⁻¹ * c⁻¹ := by
      have : (c * w)⁻¹ = (w * c)⁻¹ := by rw [hcw]
      simpa [mul_inv_rev] using this.symm
    have e : ⁅c * o, w⁆ = c * ⁅o, w⁆ * c⁻¹ := by
      calc ⁅c * o, w⁆ = c * o * w * o⁻¹ * (c⁻¹ * w⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = c * o * w * o⁻¹ * (w⁻¹ * c⁻¹) := by rw [hcw']
        _ = c * ⁅o, w⁆ * c⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅o, w⁆ ∈ O := by
      have : ⁅o, w⁆ = o * (w * o⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 (hHn hwH) o⁻¹).1 (O.inv_mem ho))
    exact (Subgroup.mem_normalizer_iff.1 (hCwn hc) _).1 h1
  obtain ⟨o₀, ho₀, hvC⟩ := exists_conj_mem_of_involution hCO hodd hw2 (by
    rw [sup_comm]
    exact hwH)
  have hv2 : orderOf (o₀ * w * o₀⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj o₀) w
    rw [hw2] at this
    simpa [MulAut.conj_apply] using this
  have hvcomm : ∀ a ∈ A₁, ⁅a, o₀ * w * o₀⁻¹⁆ ∈ O := fun a ha =>
    comm_conj_mem (hCO (comp_le hA₁ ha)) (hHn hwH) ho₀
      (hcomm_w a (Subgroup.mem_sup_right (comp_le hA₁ ha)))
  have hvcomm' := comm_oddCore_of_comm_hull hodd hCO hA₁ hvC hvcomm
  have hsylz := isSylowTwoIn_zStar_K0_cen h hA₁ hv2 hvC hvcomm'
  have hvφ : (MulAut.conj (o₀ * k⁻¹)) z = o₀ * w * o₀⁻¹ := by
    rw [hwdef]
    simp only [MulAut.conj_apply]
    group
  have hsylv : IsSylowTwoIn (zStar (K0 X n (centralizer ({o₀ * w * o₀⁻¹} : Set X))))
      (zpowers (o₀ * w * o₀⁻¹)) := by
    have := isSylowTwoIn_zStar_K0_map h (MulAut.conj (o₀ * k⁻¹))
    rw [hvφ] at this
    exact this
  obtain ⟨y, hy, hyeq⟩ := exists_conj_eq_of_zpowers hz2 hv2 hsylz hsylv
  have hyv : y * (o₀ * w * o₀⁻¹) = (o₀ * w * o₀⁻¹) * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (K0_le n _ hy.1)
  have hzv : z = o₀ * w * o₀⁻¹ := by
    have h1 : y⁻¹ * (o₀ * w * o₀⁻¹) * y = z := by
      rw [hyeq]; group
    rw [← h1]
    calc y⁻¹ * (o₀ * w * o₀⁻¹) * y = y⁻¹ * (y * (o₀ * w * o₀⁻¹)) := by rw [hyv]; group
      _ = o₀ * w * o₀⁻¹ := by group
  have hg₀ : o₀ * k⁻¹ ∈ centralizer ({z} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (MulAut.conj (o₀ * k⁻¹)) z = z := by rw [hvφ, ← hzv]
    simp only [MulAut.conj_apply] at h1
    calc o₀ * k⁻¹ * z = (o₀ * k⁻¹ * z * (o₀ * k⁻¹)⁻¹) * (o₀ * k⁻¹) := by group
      _ = z * (o₀ * k⁻¹) := by rw [h1]
  have hk' : k = (o₀ * k⁻¹)⁻¹ * o₀ := by group
  rw [hk']
  exact (O ⊔ centralizer ({z} : Set X)).mul_mem
    (Subgroup.mem_sup_right ((centralizer ({z} : Set X)).inv_mem hg₀)) (Subgroup.mem_sup_left ho₀)

theorem hull_hyp_ii (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z)
    {O : Subgroup X} (hO : OddHull X n z O) (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O)
    {A : Subgroup X} (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {g : X} {Xs : Subgroup X}
    (hX : Xs ≤ (O ⊔ centralizer ({z} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom)
    (hcov : ∀ a ∈ A, ∃ x ∈ Xs, ∃ o ∈ O, a = x * o) :
    g ∈ O ⊔ centralizer ({z} : Set X) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hO.1
  have hCO := hO.2.1
  have hz2 : orderOf z = 2 := h.orderOf_z
  obtain ⟨Q₀, hQ₀⟩ := exists_isSylowOf 2 A
  have hAC : A ≤ centralizer ({z} : Set X) := comp_le hA
  have hQ₀A : Q₀ ≤ A := hQ₀.le
  have hQ₀O : Q₀ ≤ normalizer (O : Set X) := fun q hq => hCO (hAC (hQ₀A hq))
  obtain ⟨o₁, ho₁, hQX⟩ := exists_conj_le_of_cover hQ₀O hodd hQ₀.isPGroup
    (fun q hq => hcov q (hQ₀A hq))
  have hQ₂ : IsPGroup 2 ↥(Q₀.map (MulAut.conj (g * o₁)).toMonoidHom) :=
    hQ₀.isPGroup.of_equiv (Subgroup.equivMapOfInjective Q₀ _ (MulAut.conj (g * o₁)).injective)
  have hQ₂le : Q₀.map (MulAut.conj (g * o₁)).toMonoidHom ≤ centralizer ({z} : Set X) ⊔ O := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hceq⟩ := hX (hQX q hq)
    have hceq' : g⁻¹ * c * g = o₁ * q * o₁⁻¹ := by simpa [MulAut.conj_apply] using hceq
    have : (MulAut.conj (g * o₁)).toMonoidHom q = c := by
      show g * o₁ * q * (g * o₁)⁻¹ = c
      calc g * o₁ * q * (g * o₁)⁻¹ = g * (o₁ * q * o₁⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * c * g) * g⁻¹ := by rw [hceq']
        _ = c := by group
    rw [this, sup_comm]
    exact hc
  obtain ⟨o₂, ho₂, hconj⟩ := exists_conj_le_of_le_sup hCO hodd hQ₂ hQ₂le
  obtain ⟨g', hg'⟩ : ∃ g' : X, g' = o₂ * g * o₁ := ⟨_, rfl⟩
  have hg'Q : ∀ q ∈ Q₀, g' * q * g'⁻¹ ∈ centralizer ({z} : Set X) := by
    intro q hq
    have h1 := hconj _ ⟨q, hq, rfl⟩
    have e : g' * q * g'⁻¹ = o₂ * ((MulAut.conj (g * o₁)).toMonoidHom q) * o₂⁻¹ := by
      show g' * q * g'⁻¹ = o₂ * (g * o₁ * q * (g * o₁)⁻¹) * o₂⁻¹
      rw [hg']; group
    rw [e]
    exact h1
  have hzQ : z ∈ Q₀ := (sylow_center_of h hA hQ₀).1
  obtain ⟨u, hu⟩ : ∃ u : X, u = g'⁻¹ * z * g' := ⟨_, rfl⟩
  have hucomm : ∀ y ∈ Q₀, u * y = y * u := by
    intro y hy
    have h1 : (g' * y * g'⁻¹) * z = z * (g' * y * g'⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hg'Q y hy)
    calc u * y = g'⁻¹ * (z * (g' * y * g'⁻¹)) * g' := by rw [hu]; group
      _ = g'⁻¹ * ((g' * y * g'⁻¹) * z) * g' := by rw [h1]
      _ = y * u := by rw [hu]; group
  have huC : u ∈ centralizer ({z} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hucomm z hzQ)
  have hφu : (MulAut.conj g'⁻¹) z = u := by rw [hu]; simp [MulAut.conj_apply]
  have hu2 : orderOf u = 2 := by
    rw [← hφu, MulEquiv.orderOf_eq]
    exact hz2
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu2, pow_two] at this
    exact this
  have hcommA := comm_of_centralizes_sylow' h.maxdeg.1 hA hQ₀ huC huu hucomm
  have hCu := cen_le_of_oddHull h hne hO hA hu2 huC hcommA
  have hCu' : (centralizer ({z} : Set X)).map (MulAut.conj g'⁻¹).toMonoidHom ≤
      O ⊔ centralizer ({z} : Set X) := by
    have e := centralizer_singleton_map_mulEquiv (MulAut.conj g'⁻¹) z
    rw [hφu] at e
    rw [← e]
    exact hCu
  have hg'H := mem_of_conj_cen_le_hull h hne hO hOc hCu'
  have hgeq : g = o₂⁻¹ * g' * o₁⁻¹ := by rw [hg']; group
  rw [hgeq]
  exact (O ⊔ centralizer ({z} : Set X)).mul_mem
    ((O ⊔ centralizer ({z} : Set X)).mul_mem (Subgroup.mem_sup_left (O.inv_mem ho₂)) hg'H)
    (Subgroup.mem_sup_left (O.inv_mem ho₁))

private theorem mem_hull_of_comm_sylow (h : Sec5Data X n z (zpowers z) S) {O : Subgroup X}
    (hO : OddHull X n z O) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {s : X}
    (hs : ∀ a ∈ A ⊔ O, s⁻¹ * a⁻¹ * s * a ∈ O) : s ∈ O ⊔ centralizer ({z} : Set X) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hO.1
  have hCO := hO.2.1
  set C := centralizer ({z} : Set X) with hCdef
  have hAC : A ≤ C := comp_le hA
  have hAn : A ≤ normalizer (O : Set X) := fun a ha => hCO (hAC ha)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 A
  have hPA' : IsSylowOf 2 P (A ⊔ O) := isSylowOf_sup hP hAn hodd
  have hNP : normalizer (P : Set X) ≤ C := normalizer_le_of h hA hP
  set Q : Subgroup X := P.map (MulAut.conj s⁻¹).toMonoidHom with hQ
  have hQA : Q ≤ A ⊔ O := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ A := hP.le hx
    have e : (MulAut.conj s⁻¹).toMonoidHom x = x * (x⁻¹ * s⁻¹ * x * s) := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    have hu : x⁻¹ * s⁻¹ * x * s ∈ O := by
      have := O.inv_mem (hs x (Subgroup.mem_sup_left hxA))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxA) (Subgroup.mem_sup_right hu)
  have hQcard : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
  have hQ' : IsSylowOf 2 Q (A ⊔ O) :=
    isSylowOf_of_card hQA (by rw [hQcard]; exact hPA'.card_eq)
  obtain ⟨k, hkAO, hk⟩ := hPA'.exists_mem_conj hQ'
  have hkH : k ∈ O ⊔ C := (sup_le (hAC.trans le_sup_right) le_sup_left) hkAO
  have hle : P.map (MulAut.conj (s * k)⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj s⁻¹).toMonoidHom x ∈ Q := Subgroup.mem_map_of_mem _ hx
    have h2 := (hk _).1 h1
    have e : (MulAut.conj (s * k)⁻¹).toMonoidHom x =
        k⁻¹ * ((MulAut.conj s⁻¹).toMonoidHom x) * k := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv,
        mul_inv_rev]
      group
    rw [e]
    exact h2
  have heq : P.map (MulAut.conj (s * k)⁻¹).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj (s * k)⁻¹).injective).symm.le
  have hskn : (s * k)⁻¹ ∈ normalizer (P : Set X) := mem_normalizer_of_map_conj_eq heq
  have hsk : s * k ∈ normalizer (P : Set X) := by simpa using Subgroup.inv_mem _ hskn
  have hskC : s * k ∈ C := hNP hsk
  have : s = (s * k) * k⁻¹ := by group
  rw [this]
  exact (O ⊔ C).mul_mem (Subgroup.mem_sup_right hskC) ((O ⊔ C).inv_mem hkH)

private theorem cen_le_hull_of_comm (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z)
    {O : Subgroup X} (hO : OddHull X n z O) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {s : X}
    (hsH : s ∈ O ⊔ centralizer ({z} : Set X)) (hs1 : s ≠ 1) {k : ℕ} (hk : s ^ 2 ^ k = 1)
    (hs : ∀ a ∈ A ⊔ O, s⁻¹ * a⁻¹ * s * a ∈ O) :
    centralizer ({s} : Set X) ≤ O ⊔ centralizer ({z} : Set X) := by
  have hodd := hO.1
  have hCO := hO.2.1
  have hHn : O ⊔ centralizer ({z} : Set X) ≤ normalizer (O : Set X) :=
    sup_le Subgroup.le_normalizer hCO
  obtain ⟨m, hm⟩ := exists_pow_orderOf_eq_two' hk hs1
  have hsO : s ∈ normalizer (O : Set X) := hHn hsH
  have hcomm : ∀ a ∈ A, ⁅a, s⁆ ∈ O := by
    intro a ha
    have h1 := hs a⁻¹ (Subgroup.mem_sup_left (A.inv_mem ha))
    have e : ⁅a, s⁆ = s * (s⁻¹ * a⁻¹⁻¹ * s * a⁻¹) * s⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 hsO _).1 h1
    simpa using this
  have hpow := commutator_pow_mem' hsO hcomm m
  have hwH : s ^ m ∈ O ⊔ centralizer ({z} : Set X) := Subgroup.pow_mem _ hsH m
  obtain ⟨o₀, ho₀, hvC⟩ := exists_conj_mem_of_involution hCO hodd hm (by
    rw [sup_comm]
    exact hwH)
  have hv2 : orderOf (o₀ * s ^ m * o₀⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj o₀) (s ^ m)
    rw [hm] at this
    simpa [MulAut.conj_apply] using this
  have hvcomm : ∀ a ∈ A, ⁅a, o₀ * s ^ m * o₀⁻¹⁆ ∈ O := fun a ha =>
    comm_conj_mem (hCO (comp_le hA ha)) (hHn hwH) ho₀ (hpow a ha)
  have hCv := cen_le_of_oddHull h hne hO hA hv2 hvC
    (comm_oddCore_of_comm_hull hodd hCO hA hvC hvcomm)
  intro x hx
  have hxw : x * s ^ m = s ^ m * x :=
    (Commute.pow_right (show Commute x s from Subgroup.mem_centralizer_singleton_iff.1 hx) m).eq
  have hxv : o₀ * x * o₀⁻¹ ∈ centralizer ({o₀ * s ^ m * o₀⁻¹} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc o₀ * x * o₀⁻¹ * (o₀ * s ^ m * o₀⁻¹) = o₀ * (x * s ^ m) * o₀⁻¹ := by group
      _ = o₀ * (s ^ m * x) * o₀⁻¹ := by rw [hxw]
      _ = o₀ * s ^ m * o₀⁻¹ * (o₀ * x * o₀⁻¹) := by group
  have h1 := hCv hxv
  have hxeq : x = o₀⁻¹ * (o₀ * x * o₀⁻¹) * o₀ := by group
  rw [hxeq]
  exact (O ⊔ centralizer ({z} : Set X)).mul_mem
    ((O ⊔ centralizer ({z} : Set X)).mul_mem (Subgroup.mem_sup_left (O.inv_mem ho₀)) h1)
    (Subgroup.mem_sup_left ho₀)

theorem hull_hyp_i (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z)
    {O : Subgroup X} (hO : OddHull X n z O) (hOc : oddCoreOf (centralizer ({z} : Set X)) ≤ O)
    {A A' : Subgroup X} (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') {t g : X}
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (ht1 : t ≠ 1)
    (hti : ∀ a ∈ A ⊔ O, t⁻¹ * a⁻¹ * t * a ∈ O)
    (htj : ∀ a ∈ A' ⊔ O, (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ O) :
    g ∈ O ⊔ centralizer ({z} : Set X) := by
  obtain ⟨k, hk⟩ := ht2
  have hodd := hO.1
  have hs_eq : g⁻¹ * t * g = (MulAut.conj g⁻¹) t := by simp
  have hs1 : g⁻¹ * t * g ≠ 1 := by
    rw [hs_eq]
    exact fun e => ht1 ((MulAut.conj g⁻¹).injective (e.trans (map_one _).symm))
  have hsk : (g⁻¹ * t * g) ^ 2 ^ k = 1 := by
    rw [hs_eq, ← map_pow, hk, map_one]
  have hsH : g⁻¹ * t * g ∈ O ⊔ centralizer ({z} : Set X) := mem_hull_of_comm_sylow h hO hA' htj
  have hCs : centralizer ({g⁻¹ * t * g} : Set X) ≤ O ⊔ centralizer ({z} : Set X) :=
    cen_le_hull_of_comm h hne hO hA' hsH hs1 hsk htj
  have hCt : ∀ x ∈ centralizer ({t} : Set X), g⁻¹ * x * g ∈ O ⊔ centralizer ({z} : Set X) := by
    intro x hx
    apply hCs
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
      _ = g⁻¹ * (t * x) * g := by rw [hx]
      _ = (g⁻¹ * t * g) * (g⁻¹ * x * g) := by group
  have htO' : ∀ o ∈ O, t⁻¹ * o * t ∈ O := by
    intro o ho
    have h1 := hti o (Subgroup.mem_sup_right ho)
    have h2 : t⁻¹ * o⁻¹ * t ∈ O := by
      have := O.mul_mem h1 (O.inv_mem ho)
      simpa [mul_assoc] using this
    have := O.inv_mem h2
    simpa [mul_assoc] using this
  have hmapO : O.map (MulAut.conj t⁻¹).toMonoidHom ≤ O := by
    rintro _ ⟨o, ho, rfl⟩
    have e : (MulAut.conj t⁻¹).toMonoidHom o = t⁻¹ * o * t := by simp
    rw [e]
    exact htO' o ho
  have heqO : O.map (MulAut.conj t⁻¹).toMonoidHom = O :=
    Subgroup.eq_of_le_of_card_ge hmapO
      (Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective).symm.le
  have htO : t⁻¹ ∈ normalizer (O : Set X) := mem_normalizer_of_map_conj_eq heqO
  have hk' : (t⁻¹) ^ 2 ^ k = 1 := by rw [inv_pow, hk, inv_one]
  have hcov : ∀ a ∈ A, ∃ x ∈ (A ⊔ O) ⊓ centralizer ({t} : Set X), ∃ o ∈ O, a = x * o := by
    intro a ha
    have hy : a⁻¹ * (t⁻¹ * a * t⁻¹⁻¹) ∈ O := by
      have := O.inv_mem (hti a (Subgroup.mem_sup_left ha))
      simpa [mul_assoc] using this
    obtain ⟨p, hp, hfix⟩ := exists_fixed_mem_coset hodd hk' htO hy
    have hfix' : t⁻¹ * (a * p) * t = a * p := by simpa using hfix
    have hcent : a * p ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * p * t = t * (t⁻¹ * (a * p) * t) := by group
        _ = t * (a * p) := by rw [hfix']
    exact ⟨a * p, Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hp), hcent⟩,
      p⁻¹, O.inv_mem hp, by group⟩
  have hX : (A ⊔ O) ⊓ centralizer ({t} : Set X) ≤
      (O ⊔ centralizer ({z} : Set X)).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hCt x (Subgroup.mem_inf.1 hx).2, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  have hmem := hull_hyp_ii h hne hO hOc hA hX hcov
  simpa using Subgroup.inv_mem _ hmem

private theorem eq_of_le_sup_odd {H A A' O : Subgroup X} (hA : Sec5Comp X n H A)
    (hA' : Sec5Comp X n H A') (hodd : Odd (Nat.card O)) (hHO : H ≤ normalizer (O : Set X))
    (hOK : pPrimeCoreOf 2 (K0 X n H) ≤ O) (hle : A' ≤ A ⊔ O) : A' = A := by
  by_contra hne
  have hAN : A ≤ normalizer (O : Set X) := (comp_le hA).trans hHO
  have hA'N : A' ≤ normalizer (O : Set X) := (comp_le hA').trans hHO
  have hn : ∀ x ∈ normalizer (O : Set X), ∀ y ∈ O, x * y * x⁻¹ ∈ O := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 hx y).1 hy
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', ⁅a, b⁆ ∈ O := fun a ha b hb =>
    hOK (comm_mem_of_ne hA hA' (Ne.symm hne) a ha b hb)
  have hall : ∀ a' ∈ A', ∀ b' ∈ A', ⁅a', b'⁆ ∈ O := by
    intro a' ha' b' hb'
    obtain ⟨a₂, ha₂, o₂, ho₂, rfl⟩ := exists_mul_of_mem_sup hAN (hle hb')
    have e : ⁅a', a₂ * o₂⁆ = ⁅a', a₂⁆ * (a₂ * ⁅a', o₂⁆ * a₂⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h2 : ⁅a', a₂⁆ ∈ O := by
      have : ⁅a', a₂⁆ = (⁅a₂, a'⁆)⁻¹ := by simp only [commutatorElement_def]; group
      rw [this]
      exact O.inv_mem (hcomm a₂ ha₂ a' ha')
    have h3 : ⁅a', o₂⁆ ∈ O := by
      have : ⁅a', o₂⁆ = (a' * o₂ * a'⁻¹) * o₂⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact O.mul_mem (hn a' (hA'N ha') o₂ ho₂) (O.inv_mem ho₂)
    exact O.mul_mem h2 (hn a₂ (hAN ha₂) _ h3)
  refine not_comm_mod_core hA' (fun a ha b hb => ?_)
  refine inf_le_oddCoreOf_of_normalizes hodd hA'N ⟨hall a ha b hb, ?_⟩
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact A'.mul_mem ha (A'.mul_mem (A'.mul_mem hb (A'.inv_mem ha)) (A'.inv_mem hb))

private theorem isQuasisimple_bar_of {H A D : Subgroup X} (hA : Sec5Comp X n H A) (hAD : A ≤ D)
    (h1 : pPrimeCoreOf 2 A ≤ pPrimeCoreOf 2 D) (h2 : A ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 A) :
    CFSG.Open.IsQuasisimple ↥(bar D A) := by
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_bar hAD h1 h2
  have hq : CFSG.IsQuasisimple ↥(bar D A) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hA.2.1
  exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
    ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq)

omit [Finite X] in
private theorem bar_eq_top_of_sup_eq {D K : Subgroup X} (hKD : K ≤ D)
    (h : K ⊔ pPrimeCoreOf 2 D = D) : bar D K = ⊤ := by
  have h1 := preimage_bar hKD
  rw [h] at h1
  have h2 : ((bar D K).comap (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D))).map
      D.subtype = D := h1
  have h3 : (bar D K).comap (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D)) = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [h2, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _) (by rw [h3, Subgroup.comap_top])

theorem false_of_oddHull (h5 : ComponentClassification.GSThmB.AschbacherTheorem5Input)
    (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z) {O : Subgroup X}
    (hO : OddHull X n z O) : False := by
  classical
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hsimple := h.cex.simple
  have hne2 := hne
  set C := centralizer ({z} : Set X) with hCdef
  set K := K0 X n C with hK
  have hO' := oddHull_sup_core h hO
  set O' : Subgroup X := O ⊔ oddCoreOf C with hO'def
  have hOc : oddCoreOf C ≤ O' := le_sup_right
  have hodd := hO'.1
  have hCO := hO'.2.1
  set D := O' ⊔ K with hD
  have hDN : normalizer (D : Set X) = O' ⊔ C := normalizer_hull_K0 h hO' hOc
  have hDO : pPrimeCoreOf 2 D = O' := pPrimeCoreOf_hull_K0 h hO' hOc
  have hOK : pPrimeCoreOf 2 K ≤ O' := oddCoreOf_K0_le hOc
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  let 𝒜 : Set (Subgroup X) := {A | Sec5Comp X n C A}
  have h𝒜 : Finite 𝒜 := inferInstance
  obtain ⟨A₁, A₂, hA₁, hA₂, hA₁₂⟩ := hne
  have hr : 1 < Nat.card 𝒜 := by
    refine Finite.one_lt_card_iff_nontrivial.2 ?_
    exact ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, fun e => hA₁₂ (congrArg Subtype.val e)⟩
  let r := Nat.card 𝒜
  let e : Fin r ≃ 𝒜 := (Finite.equivFin 𝒜).symm
  let Mi : Fin r → Subgroup X := fun i => (e i).1
  have hMi : ∀ i, Sec5Comp X n C (Mi i) := fun i => (e i).2
  have hMiK : ∀ i, Mi i ≤ K := fun i => comp_le_K0 (hMi i)
  have hMiD : ∀ i, Mi i ≤ D := fun i => (hMiK i).trans le_sup_right
  have hMinj : ∀ i j, Mi i = Mi j → i = j := fun i j hij =>
    e.injective (Subtype.ext hij)
  have hKgen : ⨆ i, Mi i = K := by
    rw [hK, K0_eq_sSup_sec5Comp, iSup]
    congr 1
    ext A
    constructor
    · rintro ⟨i, rfl⟩
      exact (hMi i)
    · intro hA
      exact ⟨e.symm ⟨A, hA⟩, by simp [Mi]⟩
  let Abar : Fin r → Subgroup (D ⧸ CFSG.Open.aschbacherThm5OddCore D) := fun i => bar D (Mi i)
  have hpre : ∀ i, CFSG.Open.aschbacherThm5Preimage D (Abar i) = Mi i ⊔ O' := fun i => by
    show CFSG.Open.aschbacherThm5Preimage D (bar D (Mi i)) = _
    rw [preimage_bar (hMiD i), hDO]
  have hinj : Function.Injective Abar := by
    intro i j hij
    by_contra hne'
    have h1 := preimage_bar (hMiD i)
    have h2 := preimage_bar (hMiD j)
    have hbar : bar D (Mi i) = bar D (Mi j) := hij
    rw [hbar, h2, hDO] at h1
    exact hne' (hMinj i j (eq_of_le_sup_odd (hMi i) (hMi j) hodd hCO hOK
      (h1 ▸ le_sup_left)).symm)
  have hss : ∀ i, CFSG.Open.aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, one_pos, fun _ => ⟨le_rfl, isQuasisimple_bar_of (hMi i) (hMiD i)
      (by
        rw [hDO]
        exact (oddCoreOf_le_of_isPCompIn (comp_isPCompIn_K0 (hMi i))).trans hOK)
      (by
        rw [hDO, inf_comm]
        exact inf_le_oddCoreOf_of_normalizes hodd ((comp_le (hMi i)).trans hCO))⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    intro i j hij
    apply bar_commute
    intro a ha b hb
    have h1 := comm_mem_of_ne (hMi i) (hMi j) (fun e' => hij (hMinj i j e')) a ha b hb
    rw [commutatorElement_def] at h1
    rw [hDO]
    exact hOK h1
  have hgen : ⨆ i, Abar i = ⊤ := by
    have h1 : ⨆ i, bar D (Mi i) = bar D (⨆ i, Mi i) := (bar_iSup Mi hMiD).symm
    show ⨆ i, bar D (Mi i) = ⊤
    rw [h1, hKgen]
    exact bar_eq_top_of_sup_eq le_sup_right (by rw [hDO, sup_comm])
  have hperm : ∀ x ∈ normalizer (D : Set X), ∀ i, ∃ j,
      (CFSG.Open.aschbacherThm5Preimage D (Abar i)).map (MulAut.conj x).toMonoidHom =
        CFSG.Open.aschbacherThm5Preimage D (Abar j) := by
    intro x hx i
    rw [hDN] at hx
    have hx' : x ∈ C ⊔ O' := by rw [sup_comm]; exact hx
    obtain ⟨c, hc, o, ho, rfl⟩ := exists_mul_of_mem_sup hCO hx'
    have hA' := Sec5Comp.map_conj (hMi i) (Subgroup.le_normalizer hc)
    refine ⟨e.symm ⟨_, hA'⟩, ?_⟩
    rw [hpre, hpre]
    have hMj : Mi (e.symm ⟨_, hA'⟩) = (Mi i).map (MulAut.conj c).toMonoidHom := by
      simp [Mi]
    rw [hMj]
    have hcomp : (MulAut.conj (c * o)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj o).toMonoidHom := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map]
    have hoG : o ∈ normalizer ((Mi i ⊔ O' : Subgroup X) : Set X) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_right ho)
    rw [map_conj_eq_of_mem_normalizer hoG, Subgroup.map_sup,
      map_conj_eq_of_mem_normalizer (hCO hc)]
  have hi : ∀ (i j : Fin r) (t g : X), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center X →
      CFSG.Open.aschbacherThm5Centralizes (CFSG.Open.aschbacherThm5Core D)
        (CFSG.Open.aschbacherThm5Preimage D (Abar i)) t →
      CFSG.Open.aschbacherThm5Centralizes (CFSG.Open.aschbacherThm5Core D)
        (CFSG.Open.aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set X) := by
    intro i j t g ht2 htZ hti htj
    rw [hDN]
    have ht1 : t ≠ 1 := fun e' => htZ (e' ▸ one_mem _)
    unfold CFSG.Open.aschbacherThm5Centralizes at hti htj
    rw [core_eq, hDO, hpre] at hti htj
    exact hull_hyp_i h hne2 hO' hOc (hMi i) (hMi j) ht2 ht1 hti htj
  have hii : ∀ (i : Fin r) (g : X) (Xs : Subgroup X),
      Xs ≤ (normalizer (D : Set X)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ CFSG.Open.aschbacherThm5Preimage D (Abar i), ∃ x ∈ Xs,
        ∃ o ∈ CFSG.Open.aschbacherThm5Core D, a = x * o) →
      g ∈ normalizer (D : Set X) := by
    intro i g Xs hX hcover
    rw [hDN] at hX ⊢
    rw [core_eq, hDO, hpre] at hcover
    exact hull_hyp_ii h hne2 hO' hOc (hMi i) hX fun a ha => hcover a (Subgroup.mem_sup_left ha)
  have hH : normalizer (D : Set X) ≠ ⊤ := by
    rw [hDN]
    intro htop
    have hsup : O' ⊔ C ≤ normalizer (O' : Set X) := sup_le Subgroup.le_normalizer hCO
    have hnorm : O'.Normal :=
      ⟨fun w hw g => (Subgroup.mem_normalizer_iff.1 (hsup (htop ▸ Subgroup.mem_top g)) w).1 hw⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O' with hbot | htop'
    · rw [hbot, bot_sup_eq] at htop
      exact centralizer_ne_top_of_involution h.cex.nonabelian h.orderOf_z htop
    · have hcard : Nat.card O' = Nat.card X := by
        rw [htop']
        exact Subgroup.card_top
      have h2 : 2 ∣ Nat.card X := by
        have := orderOf_dvd_natCard z
        rwa [h.orderOf_z] at this
      rw [← hcard] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rcases h5 X D r (by omega) Abar hinj hss hcomm hgen hperm hi hii hH with h1 | ⟨h2r, h2⟩
  · omega
  · have hr2 : 1 < r := hr
    obtain ⟨-, hrk, -⟩ := h2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    rw [hpre] at hrk
    have h3 := SectionRank.pRank_mono (p := 2) (by norm_num)
      (le_sup_left : Mi ⟨0, by omega⟩ ≤ Mi ⟨0, by omega⟩ ⊔ O')
    have h4 := two_le_pRank_comp hn8 (hMi ⟨0, by omega⟩)
    omega

end CFSG.OddStandard.Solomon75
