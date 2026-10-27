module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuTc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.SylowExp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier CFSG.AGLEmbeddingD2.Wilson.ThetaSpor Subgroup Equiv

section Sylow


theorem ruSylowSub_exp
    {q : Equiv.Perm (Fin 4060)} (hq : q ∈ ruSylowSub) :
    q ^ 3 = 1 := by
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  obtain ⟨he, hsz, -, hall⟩ := ruSylow_parts
  obtain ⟨i, hi, hiq⟩ := ((enumOK_spec hps he).1 _).1 hq
  have hvalid := (enumOK_spec hps he).2.2 i hi
  have hrep : Rep 4060 (ruSylCert ()).pts[i]! (permOfArr 4060 (ruSylCert ()).pts[i]!) :=
    rep_of_validA hvalid
  rcases hall i hi with hid | ⟨g, hg, hgv, hgs, hgc⟩
  · have := (eqA_iff hrep rep_idA).1 hid
    rw [← hiq, this]; simp
  · have hc := eq_of_eqA (rep_conjA hgv hrep) rep_ruX hgc
    have hq' : q = (permOfArr 4060 g)⁻¹ * ruXperm * permOfArr 4060 g := by
      rw [← hc, ← hiq]; group
    have hcp := conj_pow (a := (permOfArr 4060 g)⁻¹) (b := ruXperm) (i := 3)
    rw [inv_inv] at hcp
    rw [hq', hcp, ruXperm_pow_three]
    group

theorem ruP_pow_three
    {y : ruP} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ruP := inferInstance
  have hQ : Nat.card (ruSylowSub.subgroupOf ruP) = 3 ^ 3 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruSylowSub_le).toEquiv
    rw [e, card_ruSylowSub]
    norm_num
  refine pow_eq_one_of_pPower_of_exp 3 3 (ruSylowSub.subgroupOf ruP) hQ
    (by rw [card_ruP]; norm_num) (fun q hq => ?_) hy
  apply Subtype.ext
  have := ruSylowSub_exp (Subgroup.mem_subgroupOf.1 hq)
  simpa using this

end Sylow

section YLevel


theorem ruTcQ_le_ruP : ruTcQ ≤ ruP := by
  refine ruTc_le.trans ?_
  rw [closure_ruGs_eq]
  exact inf_le_right

@[expose] noncomputable def ruKY : Subgroup ↥ruP := ruTcQ.subgroupOf ruP

theorem ruKY_le : ruKY ≤ Subgroup.centralizer ({ruXp} : Set ruP) := by
  intro y hy
  exact mem_RuC_of_mem_closure (ruTc_le (Subgroup.mem_subgroupOf.1 hy))

theorem ruKY_normal : (ruKY.subgroupOf (Subgroup.centralizer ({ruXp} : Set ruP))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : ruP).1 ∈ ruTcQ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hn)
  have hnC : (n : ruP).1 ∈ closure (permsA 4060 ruGs) := ruTc_le hn'
  have hgC : (g : ruP).1 ∈ closure (permsA 4060 ruGs) := mem_closure_of_mem_RuC g.2
  have := ruTc_normal.conj_mem ⟨(n : ruP).1, hnC⟩ (Subgroup.mem_subgroupOf.2 hn')
    ⟨(g : ruP).1, hgC⟩
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 this))

theorem ruKY_card : Nat.card ruKY = 1080 := by
  rw [ruKY, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruTcQ_le_ruP).toEquiv, card_ruTcQ]

theorem card_centralizer_ruXp :
    Nat.card (Subgroup.centralizer ({ruXp} : Set ruP)) = 2160 := by
  have hmap : (Subgroup.centralizer ({ruXp} : Set ruP)).map ruP.subtype =
      closure (permsA 4060 ruGs) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact mem_closure_of_mem_RuC hc
    · intro hy
      have hyP : y ∈ ruP := by
        rw [closure_ruGs_eq] at hy
        exact hy.2
      exact ⟨⟨y, hyP⟩, mem_RuC_of_mem_closure hy, rfl⟩
  rw [← Subgroup.card_map_of_injective ruP.subtype_injective, hmap]
  exact ruCent_enum.2.1

theorem ruKY_index : (ruKY.subgroupOf (Subgroup.centralizer ({ruXp} : Set ruP))).index = 2 := by
  have h1 := (ruKY.subgroupOf (Subgroup.centralizer ({ruXp} : Set ruP))).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruKY_le).toEquiv, ruKY_card,
    card_centralizer_ruXp] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans (by norm_num))

theorem ruKY_quasisimple : CFSG.IsQuasisimple ↥ruKY :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe ruTcQ_le_ruP).symm
    ruTc_spec.2.1

theorem ruY_layer :
    CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({ruXp} : Set ruP)) = ruKY :=
  Proving.inSubgroup_layer_eq_of_index_two ruKY_le ruKY_normal ruKY_index ruKY_quasisimple

end YLevel

section XLevel

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

theorem exists_pow_eq_one_of_isCentral218 {X : Type} [Group X] {x : X}
    (h : IsCentral218 (⊤ : Subgroup X) x) : ∃ k : ℕ, x ^ 3 ^ k = 1 := by
  obtain ⟨S, ⟨Q, hQ⟩, hxS⟩ := h
  obtain ⟨s, -, rfl⟩ := hxS
  have hs : (s : X) ∈ Subgroup.map (⊤ : Subgroup X).subtype
      (Q : Subgroup ↥(⊤ : Subgroup X)) := by
    rw [hQ]; exact s.2
  obtain ⟨q, hq, hqs⟩ := hs
  obtain ⟨k, hk⟩ := (Q.isPGroup' ⟨q, hq⟩)
  refine ⟨k, ?_⟩
  have h1 : (q : ↥(⊤ : Subgroup X)) ^ 3 ^ k = 1 := by
    simpa using congrArg (fun z : ↥(Q : Subgroup ↥(⊤ : Subgroup X)) => (z : ↥(⊤ : Subgroup X))) hk
  have h2 : ((q : ↥(⊤ : Subgroup X)) : X) ^ 3 ^ k = 1 := by
    simpa using congrArg (fun z : ↥(⊤ : Subgroup X) => (z : X)) h1
  show (s : X) ^ 3 ^ k = 1
  rw [← hqs]
  exact h2


theorem ks219Ru : KS219Ru := by
  intro X _ _ ⟨e⟩ x hx1 hxc
  have hfin : Finite ruP := inferInstance
  let φ0 : X ≃* ruP := e.trans ruEquivP
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isCentral218 hxc
  have hb3 : (φ0 x) ^ 3 = 1 := by
    apply ruP_pow_three (k := k)
    rw [← map_pow, hk, map_one]
  have hb1 : φ0 x ≠ 1 := fun h => hx1 (φ0.injective (h.trans (map_one φ0).symm))
  obtain ⟨g, hg⟩ := exists_conj_ruXp (φ0 x) hb3 hb1
  let φ : X ≃* ruP := φ0.trans (MulAut.conj g)
  have hφx : φ x = ruXp := by
    show g * φ0 x * g⁻¹ = ruXp
    exact hg
  have hmap := Proving.map_inSubgroup_layer_centralizer φ x
  rw [hφx, ruY_layer] at hmap
  set Lx := CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set X)) with hLx
  have hLxe : Lx = ruKY.comap φ.toMonoidHom := by
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective φ.injective Lx).symm
  refine ⟨?_, ?_⟩
  · rw [hLxe]
    show φ x ∈ ruKY
    rw [hφx]
    exact Subgroup.mem_subgroupOf.2 ruTc_spec.1
  · let e1 : ↥Lx ≃* ↥(Lx.map φ.toMonoidHom) := Subgroup.equivMapOfInjective Lx φ.toMonoidHom φ.injective
    let e2 : ↥(Lx.map φ.toMonoidHom) ≃* ↥ruKY := MulEquiv.subgroupCongr hmap
    let e3 : ↥ruKY ≃* ↥ruTcQ := Subgroup.subgroupOfEquivOfLe ruTcQ_le_ruP
    exact isTripleCover_of_mulEquiv (e1.trans (e2.trans e3)).symm ruTc_spec.2.2

end XLevel

end CFSG.AGLEmbeddingD2.Wilson.Census219
