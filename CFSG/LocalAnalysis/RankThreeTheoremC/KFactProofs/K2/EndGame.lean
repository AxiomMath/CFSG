module

public import CFSG.Walter.ReeOrder.JT.PSL2
public import CFSG.Walter.W67.JR.OutPSL
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section EndGame

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem tor_order_three_mem {X : Type*} [Group X] {U : Subgroup X} {w : X}
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (hw : w * w = 1) {c : X}
    (hc : c ∈ U ⊔ Subgroup.zpowers w) (h3 : orderOf c = 3) : c ∈ U := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  let T : Subgroup X :=
    { carrier := {x | x ∈ U ∨ ∃ u ∈ U, x = u * w}
      one_mem' := Or.inl U.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨v, hv, rfl⟩)
        · exact Or.inl (U.mul_mem ha hb)
        · exact Or.inr ⟨a * v, U.mul_mem ha hv, by rw [mul_assoc]⟩
        · refine Or.inr ⟨u * b⁻¹, U.mul_mem hu (U.inv_mem hb), ?_⟩
          have h := hinv b hb
          calc u * w * b = u * (w * b * w⁻¹) * w := by group
            _ = u * b⁻¹ * w := by rw [h]
        · refine Or.inl ?_
          have h := hinv v hv
          have : u * w * (v * w) = u * (w * v * w⁻¹) * (w * w) := by group
          rw [this, h, hw, mul_one]
          exact U.mul_mem hu (U.inv_mem hv)
      inv_mem' := by
        rintro x (hx | ⟨u, hu, rfl⟩)
        · exact Or.inl (U.inv_mem hx)
        · refine Or.inr ⟨u, hu, ?_⟩
          have h := hinv u⁻¹ (U.inv_mem hu)
          rw [inv_inv] at h
          calc (u * w)⁻¹ = w⁻¹ * u⁻¹ := mul_inv_rev _ _
            _ = w * u⁻¹ := by rw [hwinv]
            _ = (w * u⁻¹ * w⁻¹) * w := by group
            _ = u * w := by rw [h] }
  have hUT : U ≤ T := fun x hx => Or.inl hx
  have hwT : Subgroup.zpowers w ≤ T := by
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, U.one_mem, (one_mul w).symm⟩
  have hcT : c ∈ T := sup_le hUT hwT hc
  rcases hcT with h | ⟨u, hu, rfl⟩
  · exact h
  · exfalso
    have h2 : (u * w) ^ 2 = 1 := by
      rw [sq]
      calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
        _ = 1 := by rw [hinv u hu, hw]; group
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    omega

theorem tor_exists_conj {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {R S : Subgroup L} (hR : Nat.card R = p) (hS : Nat.card S = p)
    (hL : ¬ p ^ 2 ∣ Nat.card L) :
    ∃ g : L, ∀ x : L, x ∈ R ↔ g⁻¹ * x * g ∈ S := by
  have hsyl : ∀ P : Subgroup L, Nat.card P = p → ∃ T : Sylow p L, (T : Subgroup L) = P := by
    intro P hP
    have hPg : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
    have hidx : ¬ p ∣ P.index := by
      intro hd
      apply hL
      have h := Subgroup.card_mul_index P
      rw [hP] at h
      rw [← h, sq]
      exact Nat.mul_dvd_mul_left p hd
    exact ⟨hPg.toSylow hidx, rfl⟩
  obtain ⟨TS, hTS⟩ := hsyl S hS
  obtain ⟨TR, hTR⟩ := hsyl R hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L TS TR
  refine ⟨g, fun x => ?_⟩
  rw [← hTR, ← hTS, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem tor_conj_mem_normalizer {L : Type*} [Group L] {R S : Subgroup L} {g : L}
    (hg : ∀ x : L, x ∈ R ↔ g⁻¹ * x * g ∈ S) {c : L} (hc : c ∈ normalizer (R : Set L)) :
    g⁻¹ * c * g ∈ normalizer (S : Set L) := by
  rw [Subgroup.mem_normalizer_iff] at hc ⊢
  intro s
  have h1 := hg (g * s * g⁻¹)
  have h2 := hg (c * (g * s * g⁻¹) * c⁻¹)
  have h3 := hc (g * s * g⁻¹)
  have e1 : g⁻¹ * (g * s * g⁻¹) * g = s := by group
  have e2 : g⁻¹ * (c * (g * s * g⁻¹) * c⁻¹) * g =
      g⁻¹ * c * g * s * (g⁻¹ * c * g)⁻¹ := by group
  rw [e1] at h1
  rw [e2] at h2
  rw [← h2, ← h3, h1]

theorem tor_of_torus {L : Type*} [Group L] [Finite L] {U : Subgroup L} {w : L}
    (hT : CFSG.Walter.JT.TorusData (⊤ : Subgroup L) U w) {p : ℕ} [Fact p.Prime]
    (hpU : p ∣ Nat.card U) (h3U : ¬ 3 ∣ Nat.card U) (hL : ¬ p ^ 2 ∣ Nat.card L)
    {R : Subgroup L} (hR : Nat.card R = p) {c : L} (hc : orderOf c = 3) :
    c ∉ normalizer (R : Set L) := by
  intro hcn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) p hpU
  have hSU : Subgroup.zpowers (x : L) ≤ U := (Subgroup.zpowers_le).mpr x.2
  have hScard : Nat.card (Subgroup.zpowers (x : L)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hSbot : Subgroup.zpowers (x : L) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hScard
    exact (Fact.out : p.Prime).one_lt.ne hScard
  obtain ⟨g, hg⟩ := tor_exists_conj hR hScard hL
  have hc1 := tor_conj_mem_normalizer hg hcn
  have hN := hT.normalizer _ hSU hSbot
  rw [top_inf_eq] at hN
  rw [hN] at hc1
  have hord : orderOf (g⁻¹ * c * g) = 3 := by
    rw [← hc]
    simpa [MulAut.conj_apply] using
      MulEquiv.orderOf_eq (MulAut.conj g⁻¹) c
  have hU := tor_order_three_mem hT.inv hT.w_mul_self hc1 hord
  apply h3U
  rw [← hord, ← Subgroup.orderOf_mk (H := U) (g⁻¹ * c * g) hU]
  exact orderOf_dvd_natCard _

theorem tor_card_psl2_27 : Nat.card PSL(2, GaloisField 3 3) = 9828 := by
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  rw [CFSG.GorensteinWalter.psl2_card_formula _
    ⟨3, 3, Nat.prime_three, ⟨1, by norm_num⟩, by norm_num, hK⟩, hK]
  norm_num

theorem tor_main {R : Subgroup PSL(2, GaloisField 3 3)}
    (hR : Nat.card R = 7 ∨ Nat.card R = 13) {c : PSL(2, GaloisField 3 3)}
    (hc : orderOf c = 3) : c ∉ normalizer (R : Set PSL(2, GaloisField 3 3)) := by
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have hKodd : Odd (Nat.card (GaloisField 3 3)) := by
    rw [hK]
    exact ⟨13, by norm_num⟩
  have hL := tor_card_psl2_27
  rcases hR with hR | hR
  · obtain ⟨U, w, hT, -, hmod⟩ := CFSG.Walter.JT.psl2_even_torus hK hKodd
    have hU : Nat.card U = 14 := by
      rw [hK] at hmod
      omega
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact tor_of_torus hT (p := 7) (by rw [hU]; norm_num) (by rw [hU]; norm_num)
      (by rw [hL]; norm_num) hR hc
  · obtain ⟨U, w, hT, -, hmod⟩ := CFSG.Walter.JT.psl2_odd_torus hK hKodd
    have hU : Nat.card U = 13 := by
      rw [hK] at hmod
      omega
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact tor_of_torus hT (p := 13) (by rw [hU]) (by rw [hU]; norm_num)
      (by rw [hL]; norm_num) hR hc

theorem psl2_27_no_order_three_normalizes {X : Type} [Group X]
    (e : X ≃* PSL(2, GaloisField 3 3)) {R : Subgroup X}
    (hR : Nat.card R = 7 ∨ Nat.card R = 13) {c : X} (hc : orderOf c = 3) :
    c ∉ normalizer (R : Set X) := by
  intro hcn
  refine tor_main (R := R.map e.toMonoidHom) ?_ (c := e c) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hR
  · rw [MulEquiv.orderOf_eq]
    exact hc
  · have h := Subgroup.mem_map_of_mem e.toMonoidHom hcn
    rwa [Subgroup.map_equiv_normalizer_eq] at h

end EndGame

section EndGame

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem exists_index_three_normal (hL : L.Normal)
    (e : Nonempty (L ≃* PSL(2, GaloisField 3 3))) (hc : centralizer (L : Set H) = ⊥)
    (hi : L.index = 3 ∨ L.index = 6) : ∃ N : Subgroup H, N.Normal ∧ N.index = 3 := by
  rcases hi with h3 | h6
  · exact ⟨L, hL, h3⟩
  · haveI := hL
    obtain ⟨e⟩ := e
    have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
      CFSG.Walter.W67.JROut.isCyclic_outer_of_equiv e (p := 3) (n := 3) (by decide) (by decide)
        (by norm_num)
    let ψ : H →* CFSG.ComponentClassification.OuterAutomorphisms.Outer L :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner L)).comp
        MulAut.conjNormal
    have hker : ψ.ker = L := by
      ext h
      constructor
      · intro hh
        rw [MonoidHom.mem_ker] at hh
        have hmem : (MulAut.conjNormal h : MulAut L) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner L :=
          (QuotientGroup.eq_one_iff _).mp hh
        obtain ⟨l, hl⟩ := hmem
        have hz : (l : H)⁻¹ * h ∈ centralizer (L : Set H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          have hlx := congrArg (fun f : MulAut L => ((f ⟨x, hx⟩ : L) : H)) hl
          simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
            Subgroup.coe_inv] at hlx
          calc x * ((l : H)⁻¹ * h) = (l : H)⁻¹ * ((l : H) * x * (l : H)⁻¹) * h := by group
            _ = (l : H)⁻¹ * (h * x * h⁻¹) * h := by rw [hlx]
            _ = ((l : H)⁻¹ * h) * x := by group
        rw [hc, Subgroup.mem_bot, inv_mul_eq_one] at hz
        rw [← hz]
        exact l.2
      · intro hh
        rw [MonoidHom.mem_ker]
        apply (QuotientGroup.eq_one_iff _).mpr
        exact ⟨⟨h, hh⟩, (MulAut.conjNormal_val (h := ⟨h, hh⟩)).symm⟩
    have hrange_card : Nat.card ψ.range = 6 := by
      rw [← Subgroup.index_ker, hker, h6]
    haveI : Finite ψ.range := Nat.finite_of_card_ne_zero (by omega)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ψ.range) 2
      (by rw [hrange_card]; norm_num)
    let T : Subgroup ψ.range := Subgroup.zpowers x
    have hTcard : Nat.card T = 2 := by
      rw [Nat.card_zpowers, hx]
    have hTindex : T.index = 3 := by
      have := T.card_mul_index
      rw [hTcard, hrange_card] at this
      omega
    refine ⟨T.comap ψ.rangeRestrict, inferInstance, ?_⟩
    rw [Subgroup.index_comap_of_surjective T ψ.rangeRestrict_surjective, hTindex]

end EndGame

section EndGame

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem eg_eq_of_card_seven {W : Subgroup H} (hW : Nat.card W = 91) {A B : Subgroup H}
    (hA : A ≤ W) (hB : B ≤ W) (hA7 : Nat.card A = 7) (hB7 : Nat.card B = 7) : A = B := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hS : ∀ {C : Subgroup H}, C ≤ W → Nat.card C = 7 →
      ∃ P : Sylow 7 W, (P : Subgroup W) = C.subgroupOf W ∧ (C.subgroupOf W).index = 13 := by
    intro C hC hC7
    have hcard : Nat.card (C.subgroupOf W) = 7 := by
      rw [← hC7]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
    have hp : IsPGroup 7 (C.subgroupOf W) := IsPGroup.of_card (n := 1) (by rw [hcard]; simp)
    have hidx : (C.subgroupOf W).index = 13 := by
      have := Subgroup.card_mul_index (C.subgroupOf W)
      rw [hcard, hW] at this
      omega
    exact ⟨hp.toSylow (by rw [hidx]; omega), rfl, hidx⟩
  obtain ⟨PA, hPA, hidxA⟩ := hS hA hA7
  obtain ⟨PB, hPB, -⟩ := hS hB hB7
  have hsub : Subsingleton (Sylow 7 W) := by
    have h1 := card_sylow_modEq_one 7 W
    have h2 := Sylow.card_dvd_index PA
    have h3 : (PA : Subgroup W).index = 13 := by rw [hPA, hidxA]
    rw [h3] at h2
    have h4 : Nat.card (Sylow 7 W) = 1 ∨ Nat.card (Sylow 7 W) = 13 :=
      (Nat.dvd_prime (by norm_num)).mp h2
    have h5 : Nat.card (Sylow 7 W) = 1 := by
      rcases h4 with h | h
      · exact h
      · rw [h] at h1
        exact absurd h1 (by decide)
    exact (Nat.card_eq_one_iff_unique.mp h5).1
  have hPAB : PA = PB := Subsingleton.elim PA PB
  have h6 : A.subgroupOf W = B.subgroupOf W := by
    rw [← hPA, ← hPB, hPAB]
  have h7 := (Subgroup.subgroupOf_inj).mp h6
  rwa [inf_of_le_left hA, inf_of_le_left hB] at h7

theorem eq_bot_of_elemAbelian_normalizes (hL : L.Normal)
    (e : Nonempty (L ≃* PSL(2, GaloisField 3 3))) (hc : centralizer (L : Set H) = ⊥)
    (hi : L.index = 3 ∨ L.index = 6) {D W : Subgroup H} (hD : IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hDW : D ≤ normalizer (W : Set H))
    (hW : Nat.Coprime (Nat.card W) 6) : W = ⊥ := by
  haveI := hL
  obtain ⟨e⟩ := e
  have hLcard : Nat.card L = 9828 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.card_psl2_27
  have hWL : W ≤ L := by
    intro w hw
    have h1 : orderOf (QuotientGroup.mk w : H ⧸ L) ∣ Nat.card W :=
      (orderOf_map_dvd (QuotientGroup.mk' L) w).trans (Subgroup.orderOf_dvd_natCard W hw)
    have h2 : orderOf (QuotientGroup.mk w : H ⧸ L) ∣ L.index := orderOf_dvd_natCard _
    have h3 : Nat.Coprime (Nat.card W) L.index := by
      refine Nat.Coprime.coprime_dvd_right ?_ hW
      rcases hi with h | h <;> rw [h] <;> norm_num
    have h4 : orderOf (QuotientGroup.mk w : H ⧸ L) = 1 :=
      Nat.dvd_one.mp (h3.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
    rw [orderOf_eq_one_iff] at h4
    exact (QuotientGroup.eq_one_iff w).mp h4
  by_contra hne
  have hWne : Nat.card W ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hdvd : Nat.card W ∣ 91 := by
    have h1 : Nat.card W ∣ 9828 := hLcard ▸ Subgroup.card_dvd_of_le hWL
    have h2 : Nat.Coprime (Nat.card W) 108 :=
      (Nat.Coprime.pow_right 3 hW).coprime_dvd_right (by norm_num)
    exact h2.dvd_of_dvd_mul_left (by simpa using h1)
  have hcases : Nat.card W = 7 ∨ Nat.card W = 13 ∨ Nat.card W = 91 := by
    have hmem : Nat.card W ∈ Nat.divisors 91 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 91 = {1, 7, 13, 91} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  obtain ⟨R, hRW, hR, hDR⟩ : ∃ R : Subgroup H, R ≤ W ∧
      (Nat.card R = 7 ∨ Nat.card R = 13) ∧ D ≤ normalizer (R : Set H) := by
    rcases hcases with h | h | h
    · exact ⟨W, le_rfl, Or.inl h, hDW⟩
    · exact ⟨W, le_rfl, Or.inr h, hDW⟩
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 7
        (n := 1) (by rw [h]; norm_num)
      have hRcard : Nat.card (K.map W.subtype) = 7 := by
        rw [Subgroup.card_map_of_injective W.subtype_injective, hK]
        norm_num
      refine ⟨K.map W.subtype, Subgroup.map_subtype_le K, Or.inl hRcard, fun d hd => ?_⟩
      have hdW := (mem_normalizer_iff_map_conj_eq.mp (hDW hd))
      rw [mem_normalizer_iff_map_conj_eq]
      refine eg_eq_of_card_seven h ?_ (Subgroup.map_subtype_le K) ?_ hRcard
      · calc (K.map W.subtype).map (MulAut.conj d).toMonoidHom
            ≤ W.map (MulAut.conj d).toMonoidHom :=
              Subgroup.map_mono (Subgroup.map_subtype_le K)
          _ = W := hdW
      · rw [Subgroup.card_map_of_injective (MulAut.conj d).injective, hRcard]
  obtain ⟨c, hcD, hc1, hcL⟩ : ∃ c ∈ D, c ≠ 1 ∧ c ∈ L := by
    have hnotinj : ¬ Function.Injective ((QuotientGroup.mk' L).comp D.subtype) := by
      intro hinj
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [hD9] at h1
      have h2 : Nat.card (H ⧸ L) = L.index := rfl
      omega
    rw [injective_iff_map_eq_one] at hnotinj
    push Not at hnotinj
    obtain ⟨x, hx, hx1⟩ := hnotinj
    refine ⟨(x : H), x.2, fun h => hx1 (Subtype.ext h), ?_⟩
    exact (QuotientGroup.eq_one_iff (x : H)).mp hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf c = 3 := orderOf_eq_prime (hD.2 c hcD) hc1
  have hcR : c ∈ normalizer (R : Set H) := hDR hcD
  have hRL : R ≤ L := hRW.trans hWL
  have hnorm : (⟨c, hcL⟩ : L) ∈ normalizer ((R.subgroupOf L : Subgroup L) : Set L) := by
    rw [mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact mem_normalizer_iff.mp hcR (h : H)
  have hcardR : Nat.card (R.subgroupOf L) = 7 ∨ Nat.card (R.subgroupOf L) = 13 := by
    have : Nat.card (R.subgroupOf L) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
    rwa [this]
  have hordc : orderOf (⟨c, hcL⟩ : L) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hord
  exact psl2_27_no_order_three_normalizes e hcardR hordc hnorm

end EndGame

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
