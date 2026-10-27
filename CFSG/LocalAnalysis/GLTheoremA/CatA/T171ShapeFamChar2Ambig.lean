module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MAmbig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem chevAut_ne_one_of_setup {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b) {hdN : d ∈ Subgroup.normalizer (L : Set G)} :
    chevAut p L ⟨d, hdN⟩ ≠ 1 := by
  intro h1
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime h.pcomp
  have hJleL : J ≤ L := h.comp.1.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.qs.1
  have hcore : GLAPPrimeCore p ↥L ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hc
    exact h.prime.ne_one (Nat.Coprime.eq_one_of_dvd hc hpL)
  have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple h.qs inferInstance hcore
  have hLself : GLAPComponent p L L := glaPComponent_self_of_dvd_card h.prime h.qs hpL
  have hCent : CentMod p L d := (chevAut_eq_one_iff h.prime hLself hdN).1 h1
  have hcoreG : ∀ y ∈ GLAPPrimeCoreOf p L, ∀ z ∈ L, z * y = y * z := by
    intro y hy z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
    have hZ := hOZ hc
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hZ ⟨z, hz⟩)
  have hfix : ∀ x : ↥L, x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x ∈ Subgroup.center ↥L := by
    intro x
    have hmem : ((x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x : ↥L) : G) ∈ GLAPPrimeCoreOf p L := by
      have hcoe : ((x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x : ↥L) : G) =
          ⁅((x⁻¹ : ↥L) : G), d⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, chev_coe_normalizerMonoidHom,
          commutatorElement_def]
        group
      rw [hcoe]
      exact hCent.2 (Subgroup.commutator_mem_commutator (x⁻¹).2 (Subgroup.mem_zpowers d))
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcoreG _ hmem _ y.2
  have hα : L.normalizerMonoidHom ⟨d, hdN⟩ = MonoidHom.id ↥L :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement _ hfix
  have hcent : d ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 : L.normalizerMonoidHom ⟨d, hdN⟩ ⟨l, hl⟩ = ⟨l, hl⟩ :=
      DFunLike.congr_fun hα ⟨l, hl⟩
    have h3 : d * l * d⁻¹ = l := by
      have := congrArg Subtype.val h2
      rwa [chev_coe_normalizerMonoidHom] at this
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨h.d_mem, hcent⟩
  rw [h.faithful, Subgroup.mem_bot] at hmem
  exact h.d_ne hmem

theorem chevTransfer_perfect_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b) {hdN : d ∈ Subgroup.normalizer (L : Set G)}
    (hdP : IsPGroup p (Subgroup.zpowers d)) :
    ⁅chevTransfer p L J, chevTransfer p L J⁆ = chevTransfer p L J ∧
      chevTransfer p L J ≤ fixSubgroup (chevAut p L ⟨d, hdN⟩) ∧
        chevTransfer p L J ≠ ⊥ := by
  have hJleL : J ≤ L := h.comp.1.1.trans inf_le_left
  have hJsub : ⁅J.subgroupOf L, J.subgroupOf L⁆ = J.subgroupOf L := by
    haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr h.comp.1.2.2.1
    haveI : Group.IsPerfect ↥(J.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := ((Subgroup.subgroupOfEquivOfLe hJleL).symm :
        ↥J →* ↥(J.subgroupOf L))) (Subgroup.subgroupOfEquivOfLe hJleL).symm.surjective
    exact Subgroup.commutator_eq_self
  have hperf : ⁅chevTransfer p L J, chevTransfer p L J⁆ = chevTransfer p L J := by
    rw [chevTransfer, ← Subgroup.map_commutator, hJsub]
  have hcomp : GLAPComponent p (fixSubgroup (chevAut p L ⟨d, hdN⟩)) (chevTransfer p L J) :=
    glaPComponent_chevTransfer h.prime hdN hdP h.pcomp
  refine ⟨hperf, hcomp.1, ?_⟩
  intro hbot
  have hp1 : p ∣ Nat.card ↥(chevTransfer p L J) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime hcomp
  rw [hbot, Subgroup.card_bot] at hp1
  exact h.prime.not_dvd_one hp1

private theorem glaPPrimeCore_ne_top_of_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    {L : Subgroup G} (hp : p.Prime) (hd : p ∣ Nat.card ↥L) : GLAPPrimeCore p ↥L ≠ ⊤ := by
  intro htop
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hc
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hc hd)

theorem pSimpleEquivCenterQuot_of_setup {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (h : Setup p L J A d b) :
    Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* PSimple p L) := by
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.qs.1
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime h.pcomp
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le (h.comp.1.1.trans inf_le_left))
  exact ⟨CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p
    (CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple h.qs inferInstance
      (glaPPrimeCore_ne_top_of_dvd h.prime hpL))⟩

theorem isSimpleGroup_pSimple {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b) : IsSimpleGroup (PSimple p L) := by
  haveI := h.qs.2
  obtain ⟨eP⟩ := pSimpleEquivCenterQuot_of_setup h
  exact eP.symm.isSimpleGroup

theorem exists_ne_comm_pSimple {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b) : ∃ a b : PSimple p L, a * b ≠ b * a := by
  haveI hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.qs.1
  haveI hnt : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := h.qs.2
  obtain ⟨eP⟩ := pSimpleEquivCenterQuot_of_setup h
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : ↥L ⧸ Subgroup.center ↥L, a * b = b * a := by
    intro a b
    refine eP.injective ?_
    rw [map_mul, map_mul]
    exact hcon (eP a) (eP b)
  exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm)

private theorem twistedA_two_three_false
    {S : Type} [Group S] [Finite S] [hS : IsSimpleGroup S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnc : ∃ a b : S, a * b ≠ b * a) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq3 : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group)
    {β : MulAut S} (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {P : Subgroup S}
    (hPfix : P ≤ fixSubgroup β) (hPperf : ⁅P, P⁆ = P) (hPne : P ≠ ⊥) : False := by
  obtain ⟨hcard, hidx, h7⟩ := I142C.u33_data hS hnc q hv hq3 e
  have hz : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc
  have hO : ¬ p ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
    change ¬ p ∣ (MulAut.conj : S →* MulAut S).range.index
    have hne : (MulAut.conj : S →* MulAut S).range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    intro hpd
    have hle : (MulAut.conj : S →* MulAut S).range.index = 1 ∨
        (MulAut.conj : S →* MulAut S).range.index = 2 := by omega
    rcases hle with h1 | h2
    · rw [h1] at hpd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
    · rw [h2] at hpd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd)
  obtain ⟨x, hx⟩ := I142C.exists_conj_of_pow_eq_one hp hO hβp
  have hxp : x ^ p = 1 := by
    refine I142C.conj_injective_of_center hz ?_
    rw [map_pow, hx, hβp, map_one]
  have hx1 : x ≠ 1 := fun hh => hβ1 (by rw [← hx, hh, map_one])
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hKC : P ≤ Subgroup.centralizer ({x} : Set S) := by
    rw [← fixSubgroup_conj_eq_centralizer' x, hx]
    exact hPfix
  have hpd : p ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
    have hh := orderOf_dvd_natCard x
    rw [hord, hcard] at hh
    simpa using hh
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h23 | h7'
  · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      subst hp3
      exact hPne (I142C.perfect_eq_bot_of_not_seven hcard (h7 x hxp hx1) hKC hPperf)
  · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7'
    subst hp7
    exact hPne (I142M.Ambig.perfect_eq_bot_of_order_seven hcard hord hKC hPperf)

theorem setup_ambiguousChev_false
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (h : Setup p L J A d b) (hamb : catalogIs (PSimple p L) (ambiguousChev 2)) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic _ _ => simp [ambiguousChev] at hi
  | sporadic _ => simp [ambiguousChev] at hi
  | alternating n hn =>
    have h5 : 5 ≤ n := by
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
    have hf : n = 5 ∨ n = 6 ∨ n = 8 := by
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
    exact ambiguousAltFalse G p L J A d b n h5 hf h ⟨.alternating n hn, rfl, ⟨e⟩⟩
  | lie dd =>
    obtain ⟨d1, hv⟩ := dd
    have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
      S171.normalizer_of_innerDiagMarking h.idiag h.d_mem
    have hdp : d ^ p = 1 := h.elem.2 d h.d_mem
    have hdP : IsPGroup p (Subgroup.zpowers d) := by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hx : ((x : G) ^ p) = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp,
          one_zpow]
      simpa using hx
    have hβ1 : chevAut p L ⟨d, hdN⟩ ≠ 1 := chevAut_ne_one_of_setup h
    obtain ⟨hJperf, hJle, hJne⟩ := chevTransfer_perfect_ne_bot h hdP
    rcases I142C.chev2_lie_cases d1 hv hi with ⟨q, rfl, hq7⟩ | ⟨q, rfl, hq3⟩
    · haveI : IsSimpleGroup (PSimple p L) := isSimpleGroup_pSimple h
      have hcard : Nat.card (PSimple p L) = 168 := by
        obtain ⟨hq7p, he1⟩ := I142C.primePower_eq_of_card (by norm_num : Nat.Prime 7) hq7
        obtain ⟨-, hSCor⟩ := CFSG.Models.lieModel_A 1 q hv e
        rcases hSCor with hSC | ⟨h0, -⟩
        · rw [hq7p, he1] at hSC
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hSC
        · exact absurd h0 (by norm_num)
      exact hJne (I142M.Ambig.perfect_eq_bot_of_card_168 hcard hβ1 hJle hJperf)
    · haveI : IsSimpleGroup (PSimple p L) := isSimpleGroup_pSimple h
      exact twistedA_two_three_false h.prime h.odd (exists_ne_comm_pSimple h) hv hq3 e
        (chevAut_pow_eq_one p L hdN hdp) hβ1 hJle hJperf hJne

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
