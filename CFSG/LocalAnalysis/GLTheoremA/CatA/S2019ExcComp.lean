module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcCompCenterQ
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcL2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcSpecial
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcTen
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsSpecialQHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsOutThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019AmbAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.LieType.Chevalley.G2SectionalTwoRank
import CFSG.GH74.BNPair.Lemma3013
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduce

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieIndexChar)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_centralQuotient_mulEquiv
  isChevSimple_congr)
open CFSG.Monster.Existence.StdOdd.Cert (frattini_quotient_card_eq_pow_of_rank_le)

section GroupTheory

private theorem normal_eq_top_or_le_center' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  haveI := hs
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

variable {G : Type} [Group G] [Finite G]

private noncomputable def frattiniActHom (T L : Subgroup G)
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) : ↥L →* MulAut (↥T ⧸ frattini ↥T) :=
  (CFSG.GH74.BNPair.frattiniAutHom ↥T).comp
    ((Subgroup.normalizerMonoidHom T).comp (Subgroup.inclusion hLT))

private theorem commute_of_frattiniActHom_eq_one {T L : Subgroup G} (hT : IsPGroup 2 T)
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) {m : ℕ} (hm : Odd m) {x : ↥L} (hxm : x ^ m = 1)
    (hx : frattiniActHom T L hLT x = 1) : ∀ t ∈ T, (x : G) * t = t * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : MulAut ↥T := Subgroup.normalizerMonoidHom T (Subgroup.inclusion hLT x) with hc
  have hker : c ∈ (CFSG.GH74.BNPair.frattiniAutHom ↥T).ker := hx
  obtain ⟨k, hk⟩ := CFSG.GH74.BNPair.frattiniAutHom_ker_isPGroup hT ⟨c, hker⟩
  have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcm : c ^ m = 1 := by rw [hc, ← map_pow, ← map_pow, hxm, map_one, map_one]
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hck) (orderOf_dvd_of_pow_eq_one hcm))
  intro t ht
  have h1 := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : G)) hc1
  simp only [hc, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
    MulAut.one_apply] at h1
  calc (x : G) * t = ((x : G) * t * (x : G)⁻¹) * x := by group
    _ = t * x := by rw [h1]

private theorem mem_center_of_commute {T L : Subgroup G} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) (hTL : ⁅T, L⁆ ≠ ⊥) {x : ↥L}
    (hx : ∀ t ∈ T, (x : G) * t = t * x) : x ∈ Subgroup.center ↥L := by
  set N : Subgroup ↥L := (Subgroup.centralizer (T : Set G)).subgroupOf L with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
    intro t ht
    have hg := (Subgroup.mem_normalizer_iff.1 (hLT g.2))
    have ht' : (g : G)⁻¹ * t * g ∈ T := by
      refine (hg ((g : G)⁻¹ * t * g)).2 ?_
      rw [show (g : G) * ((g : G)⁻¹ * t * g) * (g : G)⁻¹ = t by group]
      exact ht
    have h1 := hn _ ht'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc t * ((g : G) * n * (g : G)⁻¹) = g * (((g : G)⁻¹ * t * g) * n) * (g : G)⁻¹ := by group
      _ = g * (n * ((g : G)⁻¹ * t * g)) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * n * (g : G)⁻¹ * t := by group
  rcases normal_eq_top_or_le_center' hLq hNn with h | h
  · exfalso
    apply hTL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlN : (⟨l, hl⟩ : ↥L) ∈ N := h ▸ Subgroup.mem_top _
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hlN
    exact (hlN t ht).symm
  · refine h ?_
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hx t ht).symm

private theorem card_frattini_le (hsec : CFSG.GH74.SectionalTwoRankLE G 17) {T : Subgroup G}
    (hT : IsPGroup 2 T) : Nat.card (↥T ⧸ frattini ↥T) ≤ 2 ^ 17 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, hcard⟩ := frattini_quotient_card_eq_pow_of_rank_le hT
    (CFSG.GH74.SectionalTwoRankLE.rank_le_of_isPGroup hsec hT)
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) hd

end GroupTheory

private theorem not_dvd_card_GL_two (n : ℕ) (hn : n ≤ 17) :
    ¬ 3 ^ 11 ∣ Nat.card (GL (Fin n) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases n <;> decide

private theorem card_le_three_pow_ten {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (hW17 : Nat.card W ≤ 2 ^ 17) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 3 P) (ρ : P →* MulAut W) (hρ : Function.Injective ρ) :
    Nat.card P ≤ 3 ^ 10 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := CFSG.QuasithinUnique.Setup.X1.card_eq_two_pow_W hW (⊤ : Subgroup W)
  rw [Subgroup.card_top] at hn
  have hn17 : n ≤ 17 := by
    by_contra h
    have : 2 ^ 18 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => by rw [pow_two]; exact hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (GL (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  have hdvd : Nat.card P ∣ Nat.card (MulAut W) := Subgroup.card_dvd_of_injective ρ hρ
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  by_contra h
  have hk11 : 11 ≤ k := by
    by_contra hk'
    exact h (hk ▸ Nat.pow_le_pow_right (by norm_num) (by omega))
  exact not_dvd_card_GL_two n hn17 ((pow_dvd_pow 3 hk11).trans (hk ▸ hGL ▸ hdvd))

private theorem center_quotient_center_eq_bot {J : Type*} [Group J]
    (hJq : CFSG.Open.IsQuasisimple J) : Subgroup.center (J ⧸ Subgroup.center J) = ⊥ := by
  haveI := hJq.2
  rcases (Subgroup.center (J ⧸ Subgroup.center J)).normal_of_characteristic.eq_bot_or_eq_top
    with h | h
  · exact h
  · exfalso
    have hab : ∀ a b : J ⧸ Subgroup.center J, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    have hle : commutator J ≤ Subgroup.center J := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        hab (x : J ⧸ Subgroup.center J)]
      group
    rw [hJq.1] at hle
    have hsub : Subsingleton (J ⧸ Subgroup.center J) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (hle (Subgroup.mem_top _))
    exact (IsSimpleGroup.toNontrivial (G := J ⧸ Subgroup.center J)).exists_pair_ne.elim
      fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)

private theorem factorization_three_le_ten {J : Type} [Group J] [Finite J] {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (hW17 : Nat.card W ≤ 2 ^ 17)
    (ρ : J →* MulAut W)
    (hρ : ∀ x : J, ∀ m : ℕ, Odd m → x ^ m = 1 → ρ x = 1 → x ∈ Subgroup.center J) :
    (Nat.card (J ⧸ Subgroup.center J)).factorization 3 ≤ 10 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  set π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set ρP : ↥(P : Subgroup J) →* MulAut W := ρ.comp (P : Subgroup J).subtype with hρP
  set πP : ↥(P : Subgroup J) →* J ⧸ Subgroup.center J := π.comp (P : Subgroup J).subtype
    with hπP
  have hker : ρP.ker ≤ πP.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have hxk : (x : J) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc := hρ x (3 ^ k) (Odd.pow (by decide)) hxk hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 hc
  have hsplitρ : Nat.card ↥(P : Subgroup J) = Nat.card ρP.range * Nat.card ρP.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρP.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρP).toEquiv]
  have hsplitπ : Nat.card ↥(P : Subgroup J) = Nat.card πP.range * Nat.card πP.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πP.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange πP).toEquiv]
  have hkle : Nat.card ρP.ker ≤ Nat.card πP.ker := Subgroup.card_le_of_le hker
  have hrange : Nat.card πP.range ≤ Nat.card ρP.range := by
    have h1 : 0 < Nat.card ρP.ker := Nat.card_pos
    have h2 : 0 < Nat.card πP.range := Nat.card_pos
    nlinarith
  have hR3 : IsPGroup 3 ρP.range :=
    P.isPGroup'.of_surjective ρP.rangeRestrict ρP.rangeRestrict_surjective
  have hR10 := card_le_three_pow_ten hW hW17 hR3 ρP.range.subtype ρP.range.subtype_injective
  have hS := (P.mapSurjective hπs).card_eq_multiplicity
  rw [Sylow.coe_mapSurjective] at hS
  have hmap : (P : Subgroup J).map π = πP.range := by
    rw [hπP, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap] at hS
  have h3 : 3 ^ (Nat.card (J ⧸ Subgroup.center J)).factorization 3 ≤ 3 ^ 10 := by
    rw [← hS]
    exact hrange.trans hR10
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

private theorem lieIndexChar_eq_characteristic' (d : LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

private theorem one_lt_fieldOrder (d : LieTypeIndex) : 1 < d.fieldOrder := by
  have hQ : ∀ Q : PrimePower, 1 < Q.card := fun Q => by
    rw [PrimePower.card_def]
    exact Nat.one_lt_pow Q.exponent_pos.ne' Q.prime_p.one_lt
  cases d with
  | suzuki m =>
    rw [LieTypeIndex.fieldOrder_suzuki]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  | reeG2 m =>
    rw [LieTypeIndex.fieldOrder_reeG2]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  | reeF4 m =>
    rw [LieTypeIndex.fieldOrder_reeF4]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  | tits => rw [LieTypeIndex.fieldOrder_tits]; norm_num
  | _ =>
    simp only [LieTypeIndex.fieldOrder_A, LieTypeIndex.fieldOrder_twistedA,
      LieTypeIndex.fieldOrder_B, LieTypeIndex.fieldOrder_C, LieTypeIndex.fieldOrder_D,
      LieTypeIndex.fieldOrder_twistedD, LieTypeIndex.fieldOrder_E6, LieTypeIndex.fieldOrder_E7,
      LieTypeIndex.fieldOrder_E8, LieTypeIndex.fieldOrder_F4, LieTypeIndex.fieldOrder_G2,
      LieTypeIndex.fieldOrder_twistedE6, LieTypeIndex.fieldOrder_trialityD4]
    exact hQ _

section Comp


private theorem sectionalTwoRankLE_seventeen (hsec : S2019ExcSecRank) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {G : Type} [Group G] [Finite G]
    (hG : catalogIs G (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d)) :
    CFSG.GH74.SectionalTwoRankLE G 17 := by
  obtain ⟨i, hi, ⟨eG⟩⟩ := hG
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hcore⟩ := hi
  by_cases hG2 : ∃ Q, d = .G2 Q
  · obtain ⟨Q, rfl⟩ := hG2
    simp only [LieTypeIndex.characteristic_G2] at hchar
    haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hQ3 : 3 ≤ Q.card := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 Q hv (by rw [hchar]; exact hq2)
      (GaloisField Q.p Q.exponent) (by rw [GaloisField.card _ _ Q.exponent_pos.ne',
        PrimePower.card_def])
    have hM : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 Q.p Q.exponent :=
      ⟨⟨Q.prime_p, Q.exponent_pos, rfl, by rw [← PrimePower.card_def]; exact hQ3⟩,
        GaloisField Q.p Q.exponent, inferInstance, inferInstance,
        GaloisField.card _ _ Q.exponent_pos.ne', ⟨eG.trans b.symm⟩⟩
    have h8 := CFSG.LieType.Chevalley.sectionalTwoRankLE_of_chevalleyExceptionalModel_G2
      (by rw [hchar]; exact hq2) hM
    intro P hP
    obtain ⟨s, hs, hsP⟩ := h8 P hP
    exact ⟨s, hs.trans (by norm_num), hsP⟩
  · push Not at hG2
    exact hsec q hq hq2 G ⟨.lie ⟨d, hv⟩, ⟨hchar, hcore, hG2⟩, ⟨eG⟩⟩

theorem isComponentOf_and_isChevSimple {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hqp : q ≠ p)
    {K : Type} [Group K] [Finite K] (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a)
    {idx : ValidLieTypeIndex} (hchar : idx.1.characteristic = q)
    (eK : K ≃* (CFSGIndex.lie idx).Group) {β : MulAut K} (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup K} (hJ : GLAPComponent p (fixSubgroup β) J) :
    IsComponentOf J (fixSubgroup β) ∧ IsChevSimple q (↥J ⧸ Subgroup.center ↥J) := by
  have hpq : p ≠ idx.1.characteristic := by rw [hchar]; exact Ne.symm hqp
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent K hKs
    hKna idx ⟨eK⟩ p hp hp2 hpq β hβp hβ1
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ (hlayer J hJ.1 hJperf)).1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  have hlc : lieIndexChar idx.1 = q := by rw [lieIndexChar_eq_characteristic', hchar]
  refine ⟨hJcomp, ?_⟩
  rcases eq_three_or_five_le hp hp2 with hp3 | hp5
  · subst hp3
    have hbar : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
    have hO : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J := by
      rcases normal_eq_top_or_le_center' hJq
        (inferInstance : (GLAPPrimeCore 3 ↥J).Normal) with h | h
      · exfalso
        have hsub : Subsingleton (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
          refine ⟨fun a b => ?_⟩
          induction a using QuotientGroup.induction_on with | H a => ?_
          induction b using QuotientGroup.induction_on with | H b => ?_
          exact QuotientGroup.eq.2 (h ▸ Subgroup.mem_top _)
        have := hbar.2.toNontrivial
        obtain ⟨a, b, hab⟩ := exists_pair_ne
          ((↥J ⧸ GLAPPrimeCore 3 ↥J) ⧸ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J))
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        exact hab (congrArg _ (Subsingleton.elim a b))
      · exact h
    have hd := (lieComp_holds K hKs hKna idx ⟨eK⟩ β hβp J hJ).1
    rw [hlc] at hd
    let π : ↥J →* ↥J ⧸ GLAPPrimeCore 3 ↥J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hJq.1 π (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hO)
    exact isChevSimple_congr e.symm hd.chev
  · have hexp := lieCompsOn_holds hp hp5 (CFSG.Yardstones.Md42047359a2a.lieFamily
      idx.1) K hKs hKna idx rfl ⟨eK⟩ β hβp hβ1 (Or.inl (by rw [hlc]; exact hqp))
    obtain ⟨X, _, _, hX, f, hf, hk⟩ := hexp.comps J hJcomp
    rw [hlc] at hX
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hk
    exact isChevSimple_congr e hX.chev

private theorem false_of_gf3 {J : Type} [Group J] [Finite J] (hJq : CFSG.Open.IsQuasisimple J)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (hW17 : Nat.card W ≤ 2 ^ 17)
    (ρ : J →* MulAut W)
    (hρ : ∀ x : J, ∀ m : ℕ, Odd m → x ^ m = 1 → ρ x = 1 → x ∈ Subgroup.center J)
    {d : LieTypeIndex} (hcat : catalogIs (J ⧸ Subgroup.center J) (onLie (· = d)))
    (hchar : d.characteristic = 3) (hfield : d.fieldOrder = 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {A : Subgroup (MulAut (J ⧸ Subgroup.center J))} (hAel : IsElemAbelian p A)
    (hAcard : p ^ 2 ≤ Nat.card A) : False := by
  have hle := card_aut_le_of_three_le_ten s2019ChevOutThree_holds d hcat hchar hfield
    (factorization_three_le_ten hW hW17 ρ hρ) (center_quotient_center_eq_bot hJq) hp hp5 hAel
  nlinarith [hp.two_le]

theorem commutator_eq_bot_of_excComp (hsec : S2019ExcSecRank) (hcen : S2019ExcCompCenterQ)
    (hree : S2019ExcCompNotRee) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {K : Type} [Group K] [Finite K]
    (hK : catalogIs K (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d))
    (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a) {β : MulAut K} (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) {J : Subgroup K} (hJ : GLAPComponent p (fixSubgroup β) J)
    (hA : ∃ A : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)), IsElemAbelian p A ∧
      p ^ 2 ≤ Nat.card A)
    {T : Subgroup K} (hT : IsPGroup 2 T) (hJT : J ≤ Subgroup.normalizer (T : Set K)) :
    ⁅T, J⁆ = ⊥ := by
  classical
  by_contra hTJ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨A, hAel, hAcard⟩ := hA
  have hpA : p < Nat.card A := lt_of_lt_of_le (by nlinarith [hp.two_le]) hAcard
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hp5 : q = 3 → 5 ≤ p := fun h3 => by
    rcases eq_three_or_five_le hp hp2 with h | h
    · exact absurd (h.trans h3.symm) (Ne.symm hqp)
    · exact h
  have hK' := hK
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  rcases i with _ | _ | idx | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hJcomp, hchev⟩ := isComponentOf_and_isChevSimple hp hp2 hqp hKs hKna hi.1 eK hβp hβ1 hJ
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWc, hW2⟩ := CFSG.Walter.Huppert.frattini_quotient_facts (p := 2) hT
  letI : CommGroup (↥T ⧸ frattini ↥T) :=
    { (inferInstance : Group (↥T ⧸ frattini ↥T)) with mul_comm := hWc }
  have hW : ∀ w : ↥T ⧸ frattini ↥T, w * w = 1 := fun w => by rw [← pow_two]; exact hW2 w
  have hW17 : Nat.card (↥T ⧸ frattini ↥T) ≤ 2 ^ 17 :=
    card_frattini_le (sectionalTwoRankLE_seventeen hsec hq hq2 hK') hT
  set ρ := frattiniActHom T J hJT with hρdef
  have hρodd : ∀ x : ↥J, ∀ m : ℕ, Odd m → x ^ m = 1 → ρ x = 1 → x ∈ Subgroup.center ↥J :=
    fun x m hm hxm hx => mem_center_of_commute hJq hJT hTJ
      (commute_of_frattiniActHom_eq_one hT hJT hm hxm hx)
  have hρ : ∀ x : ↥J, x ^ q = 1 → ρ x = 1 → x ∈ Subgroup.center ↥J :=
    fun x hxq hx => hρodd x q hqodd hxq hx
  have hamb : ¬ catalogIs (↥J ⧸ Subgroup.center ↥J) (ambiguousChev q) := fun h =>
    absurd hAcard (not_le.2 (s2019FactAmbAut_holds p q hp hp2 hq hq2 hqp _ h A hAel))
  by_cases hqZ : q ∣ Nat.card (Subgroup.center ↥J)
  · rcases hcen p q hp hp2 hq hq2 hqp K hKs hKna hK' β hβp hβ1 J hJ hqZ with ⟨hq3, hcat3⟩ | h
    · obtain ⟨i3, hi3, ⟨e3⟩⟩ := hcat3
      rcases i3 with _ | _ | ⟨⟨d3, hv3⟩⟩ | _
      · exact absurd hi3 id
      · exact absurd hi3 id
      swap
      · exact absurd hi3 id
      change d3.characteristic = 3 ∧ d3.fieldOrder = 3 at hi3
      exact false_of_gf3 hJq hW hW17 ρ hρodd ⟨.lie ⟨d3, hv3⟩, rfl, ⟨e3⟩⟩ hi3.1 hi3.2 hp (hp5 hq3)
        hAel hAcard
    · exact hamb h
  have hZJ : ¬ q ∣ Nat.card (Subgroup.center ↥J) := hqZ
  rcases hchev with hlie | hamb'
  swap
  · exact hamb hamb'
  obtain ⟨i', hi', ⟨e'⟩⟩ := hlie
  rcases i' with _ | _ | ⟨⟨d', hv'⟩⟩ | _
  · exact absurd hi' id
  · exact absurd hi' id
  swap
  · exact absurd hi' id
  change d'.characteristic = q at hi'
  by_cases hA1 : ∃ Q, d' = .A 1 Q
  ·
    obtain ⟨Q, rfl⟩ := hA1
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_A] at hi'
    obtain ⟨⟨-, -, -, -, hn3⟩, F, hFf, hFfin, hcardF, ⟨e2⟩⟩ :=
      (lieModel_A1 Q hv' e').statedClassicalModel (by decide)
    rw [hQp] at hcardF hn3
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hF : CFSG.GH74.GLS.IVK.L2Field F := by
      refine ⟨by rw [hcardF]; exact hqodd.pow, ?_⟩
      have hge : q ≤ q ^ Q.exponent := Nat.le_self_pow Q.exponent_pos.ne' q
      have hne : q ^ Q.exponent ≠ 3 := fun h => hn3 (by rw [h])
      rw [hcardF]
      omega
    have hdvd := dvd_of_lt_card_aut_L2 hF e2 hp hp2 hq (Ne.symm hqp) hcardF hAel hpA
    have hn : p ≤ Q.exponent := Nat.le_of_dvd Q.exponent_pos hdvd
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact false_of_L2_of_card_le e2 hq2 hcardF (hp3.trans hn) (fun h3 => (hp5 h3).trans hn)
      hZJ hW hW17 ρ hρ
  by_cases hR : ∃ m, d' = .reeG2 m
  · exact hree p q hp hp2 hq hq2 hqp K hK' β hβp J hJ ⟨.lie ⟨d', hv'⟩, hR, ⟨e'⟩⟩
  push Not at hA1 hR
  have hcat' : catalogIs (↥J ⧸ Subgroup.center ↥J) (onLie (· = d')) :=
    ⟨.lie ⟨d', hv'⟩, rfl, ⟨e'⟩⟩
  obtain ⟨R, hRq, hRexp, hRcard, hZR, hext⟩ :=
    s2019ChevSpecialQ_holds q hq hq2 _ d' hcat' hi' hA1 hR
  obtain ⟨hq3, hf3⟩ := eq_three_of_special (MulEquiv.refl _) hq2 hZJ hRq hRexp hRcard hZR
    (one_lt_fieldOrder d') hext hW hW17 ρ hρ
  exact false_of_gf3 hJq hW hW17 ρ hρodd hcat' (hi'.trans hq3) hf3 hp (hp5 hq3) hAel hAcard

end Comp

end CFSG.LocalAnalysis.GLTheoremA.S2019
