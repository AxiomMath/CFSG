module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCent
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.Sporadic.Co2Smith.Timmesfeld

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.Blueprint.Chevalley CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.Sporadic.Co2Smith (Sp62 natCard_sp62)
open CFSG.HardMathSupport.Timmesfeld.DefChar (nonempty_mulEquiv_adjoint_of_bridge)

theorem card_mulAut_dvd_outer (S : Type) [Group S] [Finite S] :
    Nat.card (MulAut S) ∣ Nat.card (Outer S) * Nat.card S := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)]
  exact Nat.mul_dvd_mul dvd_rfl (Subgroup.card_range_dvd (MulAut.conj : S →* MulAut S))

theorem coprime_cube_of_dvd_twelve {p n : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hn : n ∣ 12) :
    Nat.Coprime (p ^ 3) n := by
  have hp12 : Nat.Coprime p 12 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> first | omega | norm_num at hp
  exact Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right hn hp12)

theorem cube_dvd_of_outer_dvd {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hO : Nat.card (Outer S) ∣ 12) (h : p ^ 3 ∣ Nat.card (MulAut S)) : p ^ 3 ∣ Nat.card S :=
  Nat.Coprime.dvd_of_dvd_mul_left (coprime_cube_of_dvd_twelve hp h5 hO)
    (h.trans (card_mulAut_dvd_outer S))

theorem cube_ndvd_of_mem {p N : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ N) (hN : N ≠ 0)
    {s : Finset ℕ} (hs : N.primeFactors = s) (hcube : ∀ q ∈ s, 5 ≤ q → ¬ q ^ 3 ∣ N) : False := by
  have hmem : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, hN⟩
  rw [hs] at hmem
  exact hcube p hmem h5 h

theorem cube_ndvd_U4 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 51840) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5}) (by norm_num [Nat.primeFactors, Nat.primeFactorsList])
    (by norm_num)

theorem cube_ndvd_Sp6 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 1451520) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5, 7})
    (by norm_num [Nat.primeFactors, Nat.primeFactorsList]) (by norm_num)

theorem cube_ndvd_Om8 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 174182400) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5, 7})
    (by norm_num [Nat.primeFactors, Nat.primeFactorsList]) (by norm_num)

theorem cube_ndvd_U6 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 9196830720) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5, 7, 11})
    (by norm_num [Nat.primeFactors, Nat.primeFactorsList]) (by norm_num)

theorem cube_ndvd_F4 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 3311126603366400) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5, 7, 13, 17})
    (by norm_num [Nat.primeFactors, Nat.primeFactorsList]) (by norm_num)

theorem cube_ndvd_E6 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ^ 3 ∣ 76532479683774853939200) : False :=
  cube_ndvd_of_mem hp h5 h (by norm_num) (s := {2, 3, 5, 7, 11, 13, 17, 19})
    (by norm_num [Nat.primeFactors, Nat.primeFactorsList]) (by norm_num)

theorem cube_dvd_mulAut_of_centMod {G : Type} [Group G] [Finite G] {p : ℕ} {X L B : Subgroup G}
    (hp : p.Prime) (hL : GLAPComponent p X L) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hcard : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B) :
    p ^ 3 ∣ Nat.card (MulAut (PSimple p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let H : Subgroup N := B.subgroupOf N
  let ψ : H →* MulAut (PSimple p L) := (chevAut p L).comp H.subtype
  have hcardH : Nat.card H = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hmap : ψ.ker.map (N.subtype.comp H.subtype) = B ⊓ centModSubgroup p L := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : chevAut p L x.1 = 1 := hx
      have hcent : CentMod p L (x.1 : G) := (chevAut_eq_one_iff hp hL x.1.2).1 hx'
      exact ⟨Subgroup.mem_subgroupOf.1 x.2, centMod_iff.1 hcent⟩
    · rintro ⟨hgB, hgC⟩
      have hgN : g ∈ N := (mem_centModSubgroup.1 hgC).1
      refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, ?_, rfl⟩
      show chevAut p L ⟨g, hgN⟩ = 1
      exact (chevAut_eq_one_iff hp hL hgN).2 (centMod_iff.2 hgC)
  have hf : Function.Injective (N.subtype.comp H.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(B ⊓ centModSubgroup p L) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
  have hsplitB : Nat.card B = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← hcardH, hsplit]
  have hdvdR : Nat.card ψ.range ∣ p ^ m := by
    rw [← hm, hsplitB]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdR
  have hcpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hRge : p ^ 3 ≤ Nat.card ψ.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [← hsplitB, hkerCard]
    exact hcard
  have hj3 : 3 ≤ j := by
    rw [hj] at hRge
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRge
  have hp3r : p ^ 3 ∣ Nat.card ψ.range := by
    rw [hj]
    exact pow_dvd_pow p hj3
  exact hp3r.trans (Subgroup.card_subgroup_dvd_card ψ.range)

theorem cube_u4two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isU4two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False :=
  cube_ndvd_U4 hp h5 (by rw [← card_mulAut_u4two hS]; exact h)

theorem cube_sp6two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isSp6two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_sp6two hS
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2)).subgroupOf (StatedSp 3 (ZMod 2)) = ⊥ := by
    have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  let eP : Sp62 ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hO0 := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    (r := 3) Nat.prime_two le_rfl le_rfl hK).1
  have hO : Nat.card (Outer S) ∣ 12 := by
    have hc : Nat.card (Outer S) = Nat.card (Outer (StatedProj (StatedSp 3 (ZMod 2)))) :=
      Nat.card_congr (equivalence (eS.trans eP)).toEquiv
    rw [hc]
    exact hO0.trans (by norm_num)
  have hSc : Nat.card S = 1451520 := by
    rw [Nat.card_congr eS.toEquiv]
    exact natCard_sp62
  have h' := cube_dvd_of_outer_dvd hp h5 hO h
  rw [hSc] at h'
  exact cube_ndvd_Sp6 hp h5 h'

theorem card_outer_of_surj_ker {G : Type} [Group G] {R : Type} [Group R] (Θ : MulAut G →* R)
    (hsurj : Function.Surjective Θ) (hker : Θ.ker = (MulAut.conj : G →* MulAut G).range) :
    Nat.card (Outer G) = Nat.card R := by
  show Nat.card (MulAut G ⧸ (MulAut.conj : G →* MulAut G).range) = Nat.card R
  rw [← hker]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj).toEquiv

theorem cube_d4two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isD4two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two hS
  obtain ⟨eO⟩ := CFSG.AGLEmbedding.O8pCent.nonempty_mulEquiv_omegaT_catalog ⟨.D 4 q, hv⟩ q hq rfl
  let eS : S ≃* CFSG.EvenSmallLie.OmegaEight.omegaT := e.trans eO
  have hO : Nat.card (Outer S) ∣ 12 := by
    have hc : Nat.card (Outer S) = Nat.card (Outer CFSG.EvenSmallLie.OmegaEight.omegaT) :=
      Nat.card_congr (equivalence eS).toEquiv
    rw [hc, CFSG.EvenSmallLie.OmegaEight.card_outer_omegaT]
    norm_num
  have hSc : Nat.card S = 174182400 := by
    rw [Nat.card_congr eS.toEquiv, CFSG.EvenSmallLie.OmegaEight.card_omegaT]
  have h' := cube_dvd_of_outer_dvd hp h5 hO h
  rw [hSc] at h'
  exact cube_ndvd_Om8 hp h5 h'

theorem cube_u6two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isU6two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U62RankSound.lieIndex_isU6two hS
  obtain ⟨eT⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.nonempty_equiv_timmesfeldPSU 5 q hv hq e
  have hO6 : Nat.card (Outer S) = Nat.card (Outer (CFSG.Open.timmesfeldPSU 6)) :=
    Nat.card_congr (equivalence eT).toEquiv
  have hO : Nat.card (Outer S) ∣ 12 := by
    rw [hO6, CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU_six]
    norm_num
  have hSc : Nat.card S = 9196830720 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 5 q, hv⟩ S ⟨e⟩]
    show CFSG.Open.orderTwistedA 5 q.card = 9196830720
    rw [hq]
    decide
  have h' := cube_dvd_of_outer_dvd hp h5 hO h
  rw [hSc] at h'
  exact cube_ndvd_U6 hp h5 h'

theorem cube_f4two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isF4two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨d, hv, hP, ⟨e0⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS
  cases d with
  | F4 q =>
    have hq2 : q.card = 2 := hP
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    obtain ⟨eC⟩ :=
      nonempty_mulEquiv_adjoint_of_bridge CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv e0
    obtain ⟨h2, hexp⟩ :=
      primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
    have hKc : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
      GaloisField.card _ _ q.exponent_pos.ne'
    have hK2 : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
      rw [hKc, h2]
    have hchar : CharP (GaloisField q.p q.exponent) ReeTag.F4.prime := by
      have : CharP (GaloisField q.p q.exponent) q.p := inferInstance
      rw [show ReeTag.F4.prime = 2 from rfl, ← h2]
      exact this
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
      even_F4_exact_automorphism_normal_form q.exponent_pos (GaloisField q.p q.exponent) hK2
    have hO2 : Nat.card (Outer S) = 2 := by
      have h1 : Nat.card (Outer S) = Nat.card (Multiplicative (ZMod (2 * q.exponent))) :=
        (Nat.card_congr (equivalence eC).toEquiv).trans (card_outer_of_surj_ker Θ hsurj hker)
      rw [h1, hexp]
      show Nat.card (ZMod (2 * 1)) = 2
      rw [Nat.card_zmod]
    have hS' : Nat.card S = 3311126603366400 := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.F4 q, hv⟩ S ⟨e0⟩]
      show CFSG.Open.orderF4 q.card = 3311126603366400
      rw [hq2]
      norm_num [CFSG.Open.orderF4]
    have h' := cube_dvd_of_outer_dvd hp h5 (by rw [hO2]; norm_num) h
    rw [hS'] at h'
    exact cube_ndvd_F4 hp h5 h'
  | _ => exact (show False from hP).elim

theorem cube_e6two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isTE6two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨d, hv, hP, ⟨e0⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS
  cases d with
  | twistedE6 q =>
    have hq2 : q.card = 2 := hP
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let K := GaloisField q.p (2 * q.exponent)
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
      change Nat.card (GaloisField q.p (2 * q.exponent)) = _
      rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
      change _ = (q.p ^ q.exponent) ^ 2
      rw [← pow_mul, mul_comm]
    obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
    have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, hsurj, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
    have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
    have e : S ≃* twistedE6RootGroup K σ := e0.trans (eB.symm.trans eC)
    obtain ⟨h2, hexp⟩ :=
      primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
    have hK' : Nat.card K = q.p ^ (2 * q.exponent) := by
      rw [hK2, ← pow_mul, mul_comm]
    have hRA : Nat.card (RingAut K) = 2 := by
      rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hK').1, hexp]
    have hinn : (inner (twistedE6RootGroup K σ)).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hψ := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_card_range_diag_outer_le_three hK2 σ hσ
    have hN1 : (Θ.ker).map (QuotientGroup.mk' (inner (twistedE6RootGroup K σ))) ≤
        ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hΘker] at hx
      obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      refine ⟨u, ?_⟩
      change QuotientGroup.mk' (twistedE6Inn K σ) (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) = _
      have hy1 : QuotientGroup.mk' (inner (twistedE6RootGroup K σ)) y = 1 :=
        (QuotientGroup.eq_one_iff y).2 hy
      rw [← hyz, map_mul, hy1, one_mul]
    have hN : Nat.card ((Θ.ker).map (QuotientGroup.mk' (inner (twistedE6RootGroup K σ)))) ≤ 3 :=
      (Subgroup.card_le_of_le hN1).trans hψ
    have hIK : inner (twistedE6RootGroup K σ) ≤ Θ.ker := by
      rw [hΘker]
      exact le_sup_left
    set I := inner (twistedE6RootGroup K σ) with hI
    let φ : Θ.ker →* (MulAut (twistedE6RootGroup K σ) ⧸ I) :=
      (QuotientGroup.mk' I).comp Θ.ker.subtype
    have hφk : φ.ker = I.subgroupOf Θ.ker := by
      ext x
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hm1 : Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) = Nat.card φ.range := by
      rw [← hφk]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hle : φ.range ≤ (Θ.ker).map (QuotientGroup.mk' I) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    have hm3 : Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) ≤ 3 := by
      rw [hm1]
      exact (Subgroup.card_le_of_le hle).trans hN
    have hm0 : 0 < Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) := Nat.card_pos
    have hK1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf Θ.ker)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIK).toEquiv] at hK1
    have hQ1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
    have hquot : Nat.card (MulAut (twistedE6RootGroup K σ) ⧸ Θ.ker) = 2 :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj).toEquiv).trans hRA
    have hQI := Subgroup.card_eq_card_quotient_mul_card_subgroup I
    have hOut : Nat.card (MulAut (twistedE6RootGroup K σ) ⧸ I) =
        2 * Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥I))
      rw [← hQI, hQ1, hquot, hK1]
      ring
    have hOS : Nat.card (Outer S) = Nat.card (MulAut (twistedE6RootGroup K σ) ⧸ I) :=
      Nat.card_congr (equivalence e).toEquiv
    have hO : Nat.card (Outer S) ∣ 12 := by
      rw [hOS, hOut]
      rcases (show Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) = 1 ∨
          Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) = 2 ∨
          Nat.card (Θ.ker ⧸ I.subgroupOf Θ.ker) = 3 by omega) with h1 | h1 | h1 <;>
        rw [h1] <;> norm_num
    have hSc : Nat.card S = 76532479683774853939200 := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedE6 q, hv⟩ S ⟨e0⟩]
      show CFSG.Open.orderTwistedE6 q.card = 76532479683774853939200
      rw [hq2]
      norm_num [CFSG.Open.orderTwistedE6]
    have h' := cube_dvd_of_outer_dvd hp h5 hO h
    rw [hSc] at h'
    exact cube_ndvd_E6 hp h5 h'
  | _ => exact (show False from hP).elim

theorem p_eq_three_of_list67 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isList67) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    p = 3 := by
  by_contra hne
  have h5 : 5 ≤ p := by
    by_contra hlt
    push_neg at hlt
    interval_cases p <;> first | omega | norm_num at hp
  obtain ⟨j, hj, ⟨f⟩⟩ := hS
  rcases hj with hj | hj | hj | hj | hj | hj
  · exact cube_sp6two hp h5 ⟨j, hj, ⟨f⟩⟩ h
  · exact cube_d4two hp h5 ⟨j, hj, ⟨f⟩⟩ h
  · exact cube_f4two hp h5 ⟨j, hj, ⟨f⟩⟩ h
  · exact cube_u4two hp h5 ⟨j, hj, ⟨f⟩⟩ h
  · exact cube_u6two hp h5 ⟨j, hj, ⟨f⟩⟩ h
  · exact cube_e6two hp h5 ⟨j, hj, ⟨f⟩⟩ h

theorem rank3AutAt_holds (G : Type) [Group G] [Finite G] :
    Rank3AutAt G := by
  intro p X L B hp hp2 hL hB hBN hcard hcat
  exact p_eq_three_of_list67 hp hp2 hcat (cube_dvd_mulAut_of_centMod hp hL hB hBN hcard)

end CFSG.LocalAnalysis.GLTheoremA
