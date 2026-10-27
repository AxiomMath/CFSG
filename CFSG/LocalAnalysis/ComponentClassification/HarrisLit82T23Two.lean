module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieHalf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank GrSLit.L34Facts
open scoped commutatorElement

namespace L35.Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem false_of_lieModel_char (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p w v L K)
    {t : StatedLieTag} {n f : ℕ} (hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n p f) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  obtain ⟨n', k', hn', -, hm, hne⟩ := h.exists_partialCover hL
  rcases (by omega : n' = 1 ∨ 2 ≤ n') with rfl | hn2
  · rw [mul_one] at hm
    rcases hm with hm | hm
    ·
      apply hne
      have hm' := GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm
      have hcardM := GH74.Generic.card_hopfMultiplier_of_griess hGA hm'
      rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv] at hcardM
      have hexc := L35.odd_exceptionalOrders_psl_two (f := k') h.ne_two
      have hgcd : Nat.gcd 2 (p ^ k' - 1) = 2 := by
        obtain ⟨i, hi⟩ : Odd (p ^ k') := (h.prime.odd_of_ne_two h.ne_two).pow
        rw [hi, Nat.add_sub_cancel]
        exact Nat.gcd_eq_left ⟨i, rfl⟩
      have hgen : (Blueprint.Multiplier.genericOrders .PSL 2 p k').1 = 2 := by
        simpa [Blueprint.Multiplier.genericOrders] using hgcd
      have hgen2 : (Blueprint.Multiplier.genericOrders .PSL 2 p k').2 = 1 := by
        simp [Blueprint.Multiplier.genericOrders]
      rw [hgen, hgen2, mul_one] at hcardM
      have hfM : (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))).factorization
          2 = 1 := by
        rw [hcardM, factorization_two_mul_odd two_ne_zero hexc]
        exact Nat.Prime.factorization_self Nat.prime_two
      have hM0 : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) ≠ 0 := by
        rw [hcardM]
        exact Nat.mul_ne_zero two_ne_zero hexc.pos.ne'
      have hz0 : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ≠ 0 := Nat.card_pos.ne'
      have hzdvd : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∣
          Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) := by
        rw [Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
        exact Center47.card_center_dvd_card_griessHopfMultiplier h.quasisimple_quot
      have hle : (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 ≤ 1 := by
        rw [← hfM]
        exact (Nat.factorization_le_iff_dvd hz0 hM0).mpr hzdvd 2
      have hge : 0 < (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hz0
          (even_iff_two_dvd.mp h.even_card_center)
      rw [hfM]
      congr 1
      omega
    ·
      exact absurd (N36.admissible_of_lieModel' hm).2.2.1 (by norm_num)
  · obtain ⟨rfl, -⟩ := h.four_of_partialCover hn2 hm
    rcases hm with hm | hm
    · exact h.false_of_psl4 hGA hm hne
    · exact h.false_of_psu4 hGA hm hne

theorem quotAut_tau_eq_one (h : Config G p w v L K)
    (hc : ∀ k : ↥K, k⁻¹ * h.beta k ∈ pPrimeCore 2 ↥K) : quotAut h.tau = 1 := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [quotAut_mk, MulAut.one_apply]
  congr 1
  change oddAut h.beta (QuotientGroup.mk k) = QuotientGroup.mk k
  rw [oddAut_mk]
  exact (QuotientGroup.eq.mpr (hc k)).symm

end L35.Config

namespace T23

theorem isMTypeSchur_of_mulEquiv {p : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsMTypeSchur p A) : IsMTypeSchur p B := by
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  have hcard : Nat.card ↥(Open.fusionZStar B) = Nat.card ↥(Open.fusionZStar A) := by
    rw [← FooteLit.fusionZStar_map_mulEquiv e,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  rcases h with ⟨hq, ⟨τ, n, f, hm⟩, hev, hc⟩ | ⟨hp3, he⟩
  · refine .inl ⟨isTwoQuasisimple_of_mulEquiv e hq,
      ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩, hcard ▸ hev, fun n' r hn hr hm' => ?_⟩
    rw [hcard, hc n' r hn hr (hm'.imp (GSThmB.OddQuot.lieModel_of_equiv eZ.symm)
      (GSThmB.OddQuot.lieModel_of_equiv eZ.symm)),
      Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
  · obtain ⟨e'⟩ := he
    exact .inr ⟨hp3, ⟨(QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm.trans e'⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_center_ne_one {J : Subgroup G} {z : G} (hz : orderOf z = 2) (hzJ : z ∈ J)
    (hJ : J ≤ centralizer {z}) :
    (QuotientGroup.mk ⟨z, hzJ⟩ : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) ∧
      (QuotientGroup.mk ⟨z, hzJ⟩ : ↥J ⧸ pPrimeCore 2 ↥J) ≠ 1 := by
  refine ⟨mem_center_iff.mpr fun y => ?_, fun h1 => ?_⟩
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJ y.2))
  · have hmem : (⟨z, hzJ⟩ : ↥J) ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff _).mp h1
    have hdvd : orderOf (⟨z, hzJ⟩ : ↥J) ∣ Nat.card ↥(pPrimeCore 2 ↥J) := by
      rw [← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem exists_center_ne_one {J : Subgroup G} {z : G} (hz : orderOf z = 2) (hzJ : z ∈ J)
    (hJ : J ≤ centralizer {z}) : ∃ c ∈ center (↥J ⧸ pPrimeCore 2 ↥J), c ≠ 1 :=
  ⟨_, (mk_mem_center_ne_one hz hzJ hJ).1, (mk_mem_center_ne_one hz hzJ hJ).2⟩

omit [Finite G] in
theorem eq_of_ne_one_of_card_two {H : Type*} [Group H] (hH : Nat.card H = 2) {a b : H}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  classical
  let := Fintype.ofFinite H
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ha.symm, hb.symm]), Finset.card_pair hab]
  have hle := Finset.card_le_univ ({1, a, b} : Finset H)
  rw [h3, Fintype.card_eq_nat_card, hH] at hle
  omega

omit [Finite G] in
theorem map_subtype_map_conj {C : Subgroup G} (K₀ : Subgroup ↥C) (c : ↥C) :
    (K₀.map (MulAut.conj c).toMonoidHom).map C.subtype =
      (K₀.map C.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1

theorem isTwoComponentIn_subgroupOf {w v : G} (hvM : v ∈ centralizer {w}) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v})) :
    IsTwoComponentIn (L.subgroupOf (centralizer {w}))
      (centralizer {(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))}) := by
  set M := centralizer ({w} : Set G)
  set v' : ↥M := ⟨v, hvM⟩
  have hCv : centralizer ({v'} : Set ↥M) =
      (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M := by
    ext x
    rw [mem_subgroupOf, mem_inf]
    constructor
    · intro h
      have h' : x * v' = v' * x := mem_centralizer_singleton_iff.mp h
      exact ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')⟩
    · rintro ⟨-, h⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))
  rw [hCv]
  have hle : L.subgroupOf M ≤ (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M :=
    fun x hx => hL.1 hx
  rw [isTwoComponentIn_iff hle, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
    (inf_le_left : centralizer {w} ⊓ centralizer {v} ≤ M) 2 Nat.prime_two]
  exact (isTwoComponentIn_iff hL.1).mp hL

theorem map_conj_eq_of_mem_twoComponent {H : Type} [Group H] [Finite H] {v : H}
    (hv : orderOf v = 2) {L₂ : Subgroup H} (hL₂ : IsTwoComponentIn L₂ (centralizer {v}))
    (hvL : v ∈ L₂) {K₀ : Subgroup H} (hK₀ : IsTwoComponent K₀) :
    K₀.map (MulAut.conj v).toMonoidHom = K₀ := by
  obtain ⟨hLC, hL2⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hL₂
  have hvE : v ∈ TwoLayer.subgroup H :=
    (GH74.GLS.TwoThin.pumpupY_structure hv hLC hL2).1 hvL
  exact L35.map_conj_eq_of_mem_normalizer
    (L219.twoLayer_le_normalizer ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀) hvE)

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {x y : G} (hx : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  have hk : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem commutator_mem_pPrimeCore {M : Subgroup G} {K₀ K₂ : Subgroup ↥M}
    (hK₀ : IsTwoComponent K₀) (hK₂ : IsTwoComponent K₂) (hne : K₀ ≠ K₂) {z : ↥M} (hz : z ∈ K₂)
    (k : ↥(K₀.map M.subtype)) :
    ∃ o ∈ pPrimeCore 2 ↥(K₀.map M.subtype),
      (o : G) = (k : G)⁻¹ * ((z : G) * (k : G) * (z : G)⁻¹) := by
  obtain ⟨-, -, hcomm⟩ := TwoComponentInteraction.mutual_normalization_core_commutation K₀ K₂
    ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀)
    ((L219.isTwoComponent_iff_twoComponents K₂).mp hK₂) hne
  let e : ↥K₀ ≃* ↥(K₀.map M.subtype) := K₀.equivMapOfInjective M.subtype M.subtype_injective
  obtain ⟨k₀, rfl⟩ := e.surjective k
  have hmem : ⁅(k₀ : ↥M)⁻¹, z⁆ ∈ ⁅K₀, K₂⁆ := commutator_mem_commutator (inv_mem k₀.2) hz
  obtain ⟨o, ho, hoeq⟩ := (hcomm hmem).1
  rw [← CatalogueBAlternating.primeCore_two_eq_oddCore] at ho
  refine ⟨e o, ?_, ?_⟩
  · rw [← pPrimeCore_map_iso 2 e]
    exact ⟨o, ho, rfl⟩
  · have hoeq' : ((o : ↥K₀) : ↥M) = ⁅(k₀ : ↥M)⁻¹, z⁆ := hoeq
    change (((o : ↥K₀) : ↥M) : G) = _
    rw [hoeq', commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    change _ = (((k₀ : ↥M) : G))⁻¹ * ((z : G) * ((k₀ : ↥M) : G) * (z : G)⁻¹)
    group

theorem false_of_not_isMTypeSchur (hGA : TBLit.GriessMultipliersAllModels)
    (hID : Harris81Lemma35IdentFact) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hcat : ¬ Blueprint.Catalog X) {W : Subgroup X} (hW2 : ∀ a ∈ W, a * a = 1)
    (hW4 : Nat.card W = 4) {z₁ z₂ : X} (hz₁W : z₁ ∈ W) (hz₂W : z₂ ∈ W) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hne : z₁ ≠ z₂) {L₁ L₂ : Subgroup X}
    (hL₁ : IsTwoComponentIn L₁ (centralizer (W : Set X)))
    (hL₂ : IsTwoComponentIn L₂ (centralizer (W : Set X))) (hz₁L : z₁ ∈ L₁) (hz₂L : z₂ ∈ L₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM₁ : IsMTypeSchur p ↥L₁)
    (hm₁ : ∃ k : ℕ, Blueprint.LieModel (↥L₁ ⧸ Open.fusionZStar ↥L₁) .PSL 2 p k)
    (hKM : IsTwoComponentIn (GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})))
        (centralizer {z₁}) → z₁ ∈ GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})) →
      ¬ IsMTypeSchur p ↥(GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₂n : z₂ ∉ zpowers z₁ := fun h =>
    (eq_one_or_eq_of_mem_zpowers (hW2 z₁ hz₁W) h).elim hz₂1 hne.symm
  obtain ⟨hz₁2, hz₂2, hz₂M, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hz₁W hz₁1 hz₂W hz₂n
  have hL₁' : IsTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₁
  have hL₂' : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₂
  set M := centralizer ({z₁} : Set X) with hMdef
  set z₂' : ↥M := ⟨z₂, hz₂M⟩
  have hz₂'2 : orderOf z₂' = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂2
  obtain ⟨k, hmk⟩ := hm₁
  have hL₁z : L₁ ≤ centralizer {z₁} := hL₁'.1.trans inf_le_left
  obtain ⟨c, hcZ, hc1⟩ := exists_center_ne_one hz₁2 hz₁L hL₁z
  obtain ⟨hk, h5, hsl⟩ := slTwo_of_lieModel hGA hL₁.2.2 hp hp2 hmk
    ((Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨c, hcZ⟩, fun h => hc1 (congrArg Subtype.val h)⟩)
  obtain ⟨K₀, hK₀, hKeq, hcases⟩ := exists_pumpup hz₂2 hz₂M hL₁'
  have hfix : K₀.map (MulAut.conj z₂').toMonoidHom = K₀ :=
    map_conj_eq_of_mem_twoComponent hz₂'2 (isTwoComponentIn_subgroupOf hz₂M hL₂') hz₂L hK₀
  have hKK₀ : GSThmB.conjClosure L₁ (GSThmB.layerIn M) = K₀.map M.subtype := by
    rw [hKeq, hfix, sup_idem]
  have hKc : IsTwoComponentIn (K₀.map M.subtype) M := isTwoComponentIn_map_subtype hK₀
  have hL₁K : L₁ ≤ K₀.map M.subtype := hKK₀ ▸ GSThmB.B5a.le_conjClosure L₁ _
  have hz₁K : z₁ ∈ K₀.map M.subtype := hL₁K hz₁L
  have hKM : ¬ IsMTypeSchur p ↥(K₀.map M.subtype) := by
    have h := hKM (by rw [hKK₀]; exact hKc) (by rw [hKK₀]; exact hz₁K)
    rwa [hKK₀] at h
  have hKv : (K₀.map M.subtype).map (MulAut.conj z₂).toMonoidHom = K₀.map M.subtype := by
    have h := map_subtype_map_conj K₀ z₂'
    rw [hfix] at h
    exact h.symm
  have hcfg : L35.Config X p z₁ z₂ L₁ (K₀.map M.subtype) :=
    { simple := inferInstance, nonabelian := hnonab, kProper := hK, not_catalog := hcat,
      prime := hp, ne_two := hp2, orderOf_w := hz₁2, v_sq := hW2 z₂ hz₂W, v_not_mem := hz₂n,
      v_mem := hz₂M, compL := hL₁', mTypeL := hM₁, slTwo := ⟨k, hk, h5, hsl⟩, w_mem_L := hz₁L,
      K_eq := hKK₀.symm, L_le := hL₁K, compK := hKc, w_mem_K := hz₁K, not_mType := hKM,
      K_v := hKv }
  obtain ⟨K₂, hK₂, -, -, hL₂K₂⟩ := exists_pumpup_of_mem hz₂2 hz₂M hL₂' hz₂L
  have hz₂K₂ : z₂' ∈ K₂ := (hL₂K₂.1 (show z₂' ∈ L₂.subgroupOf M from hz₂L)).1
  by_cases hK₂K : K₀ = K₂
  ·
    subst hK₂K
    set K := K₀.map M.subtype with hKdef
    have hL₂K : L₂ ≤ K := by
      intro x hx
      exact ⟨⟨x, hL₂'.1 hx |>.1⟩, (hL₂K₂.1 (show (⟨x, _⟩ : ↥M) ∈ L₂.subgroupOf M from hx)).1, rfl⟩
    have hle : K ⊓ centralizer {z₂} ≤ centralizer (W : Set X) :=
      hCW ▸ inf_le_inf_right _ hKc.1
    have hL₂C : L₂ ≤ K ⊓ centralizer {z₂} := le_inf hL₂K (hL₂'.1.trans inf_le_right)
    have hL₂KC : IsTwoComponentIn L₂ (K ⊓ centralizer {z₂}) :=
      ⟨hL₂C, L219.isSubnormal_subgroupOf_of_le hle hL₂.2.1, hL₂.2.2⟩
    obtain ⟨hLeq, -⟩ := hID X hnonab hK hcat p hp hp2 z₁ z₂ hz₁2 (hW2 z₂ hz₂W) hz₂n hz₂M L₁ hL₁'
      hM₁ k hk h5 hsl hz₁L K hKK₀.symm hL₁K hKc hz₁K hKM hKv
    have hL₂L₁ : L₂ ≤ L₁ := by
      rw [hLeq]
      have hpc : IsPComponent 2 (L₂.subgroupOf (K ⊓ centralizer {z₂})) :=
        (isTwoComponentIn_iff hL₂C).mp hL₂KC
      intro x hx
      refine ⟨⟨x, hL₂C hx⟩, ?_, rfl⟩
      exact (le_sSup (s := {J : Subgroup ↥(K ⊓ centralizer {z₂}) | IsPComponent 2 J}) hpc :
        _ ≤ pLayer ↥(K ⊓ centralizer {z₂}) 2) (show (⟨x, hL₂C hx⟩ : ↥(K ⊓ centralizer {z₂})) ∈
          L₂.subgroupOf (K ⊓ centralizer {z₂}) from hx)
    have heq : L₂ = L₁ := by
      obtain ⟨hL₂W, hL₂t⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hL₂
      obtain ⟨hL₁W, hL₁t⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hL₁
      have h1 := TwoComponentSubnormal.eq_of_le _ _ hL₂t hL₁t (fun x hx => hL₂L₁ hx)
      rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hL₂W, inf_eq_left.mpr hL₁W] at h1
      exact h1
    have hz₂L₁ : z₂ ∈ L₁ := heq ▸ hz₂L
    have hL₁c₂ : L₁ ≤ centralizer {z₂} := hL₁'.1.trans inf_le_right
    obtain ⟨-, hZ2, -, -⟩ := Lemma47.sl2_facts hp hp2 hk h5 hsl
    obtain ⟨hc₁, hc₁1⟩ := mk_mem_center_ne_one hz₁2 hz₁L hL₁z
    obtain ⟨hc₂, hc₂1⟩ := mk_mem_center_ne_one hz₂2 hz₂L₁ hL₁c₂
    have h12 := eq_of_ne_one_of_card_two hZ2 (a := ⟨_, hc₁⟩) (b := ⟨_, hc₂⟩)
      (fun h => hc₁1 (congrArg Subtype.val h)) (fun h => hc₂1 (congrArg Subtype.val h))
    have h12' : (QuotientGroup.mk ⟨z₁, hz₁L⟩ : ↥L₁ ⧸ pPrimeCore 2 ↥L₁) =
        QuotientGroup.mk ⟨z₂, hz₂L₁⟩ := congrArg Subtype.val h12
    rw [QuotientGroup.eq] at h12'
    set x : ↥L₁ := (⟨z₁, hz₁L⟩ : ↥L₁)⁻¹ * ⟨z₂, hz₂L₁⟩ with hxdef
    have hxx : x * x = 1 := by
      apply Subtype.ext
      have hinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (hW2 z₁ hz₁W)
      have hc : z₂ * z₁ = z₁ * z₂ := mem_centralizer_singleton_iff.mp hz₂M
      change z₁⁻¹ * z₂ * (z₁⁻¹ * z₂) = 1
      rw [hinv]
      calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
        _ = (z₁ * z₁) * (z₂ * z₂) := by rw [hc]; group
        _ = 1 := by rw [hW2 z₁ hz₁W, hW2 z₂ hz₂W, one_mul]
    have hdvd : orderOf x ∣ Nat.card ↥(pPrimeCore 2 ↥L₁) := by
      rw [← Subgroup.orderOf_mk x h12']
      exact orderOf_dvd_natCard _
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hxx)
    have hx1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 pPrimeCore_coprime_card) hdvd
    rw [orderOf_eq_one_iff, hxdef, inv_mul_eq_one] at hx1
    exact hne (congrArg Subtype.val hx1)
  ·
    apply hcfg.quotAut_tau_ne_one
    refine hcfg.quotAut_tau_eq_one fun k => ?_
    obtain ⟨o, ho, hoeq⟩ := commutator_mem_pPrimeCore hK₀ hK₂ hK₂K hz₂K₂ k
    have : k⁻¹ * hcfg.beta k = o := by
      apply Subtype.ext
      rw [hoeq]
      rfl
    rw [this]
    exact ho

theorem harris82Theorem2SLTwo_holds (hT1 : Harris82Theorem1KProper)
    (hGA : TBLit.GriessMultipliersAllModels) (hID : Harris81Lemma35IdentFact) :
    Harris82Theorem2SLTwo := by
  intro X _ _ _ hnonab hK W hW2 hW4 z₁ hz₁W z₂ hz₂W hz₁1 hz₂1 hne L₁ L₂ hL₁ hL₂ hz₁L hz₂L p hp
    hp2 hM₁ _ hm₁
  by_contra hcat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₁2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 z₁ hz₁W) hz₁1
  exact false_of_not_isMTypeSchur hGA hID hnonab hK hcat hW2 hW4 hz₁W hz₂W hz₁1 hz₂1 hne hL₁ hL₂
    hz₁L hz₂L hp hp2 hM₁ hm₁ fun hKc hz₁K =>
      not_isMTypeSchur_of_kProper hT1 hnonab hK hcat hz₁2 hKc hz₁K hp hp2

end T23

end CFSG.ComponentClassification.HarrisLit
