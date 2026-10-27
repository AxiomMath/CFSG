module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.C25D44
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.D44Centre
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section D44Facts

theorem isD44Index_iff (d : TauCeti.LieTypeIndex) : IsD4FourIndex d ↔ IsD44Index d := by
  cases d <;> simp [IsD4FourIndex, IsD44Index, IsTwoPow]

theorem d44_center
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hQ : IsLieQuot Y IsD4FourIndex) : Subgroup.center Y = ⊥ := by
  obtain ⟨d, hd, e⟩ := hQ
  exact CFSG.HardMathSupport.Dickson.Sec6.up34D44Centre_holds Y hq
    ⟨d, (isD44Index_iff _).1 hd, e⟩

theorem d44_twoLocal
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hQ : IsLieQuot Y IsD4FourIndex) : 4 ≤ GLATwoLocalRank 3 Y := by
  have hZ := d44_center hq hQ
  obtain ⟨d, hd, ⟨e⟩⟩ := hQ
  let eY : Y ≃* (Y ⧸ Subgroup.center Y) :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact input25_4Facts_borel_holds Y ⟨d, (isD44Index_iff _).1 hd, ⟨eY.trans e⟩⟩

end D44Facts

section Inner

variable {X : Type} [Group X] [Finite X]

theorem inducesInnerIn_of_range_le {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : (actK hBN).range ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) : InducesInnerIn B K := by
  intro b hb
  have hbB : b ∈ B := hb.1
  obtain ⟨k, hk⟩ := h ⟨⟨b, hbB⟩, rfl⟩
  refine ⟨(k : X), k.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) hk
  have h2 : (k : X) * y * (k : X)⁻¹ = b * y * b⁻¹ := h1
  calc y * ((k : X)⁻¹ * b) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * b := by group
    _ = (k : X)⁻¹ * (b * y * b⁻¹) * b := by rw [h2]
    _ = ((k : X)⁻¹ * b) * y := by group

end Inner

section TwoLocal

variable {W : Type*} [Group W] [Finite W] {p : ℕ}

theorem twoLocal_pRank_bddAbove (hp : 1 < p) (W : Type*) [Group W] [Finite W] :
    BddAbove {k | ∃ H : Subgroup W, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
  refine ⟨Nat.card W, ?_⟩
  rintro k ⟨H, -, rfl⟩
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
  have h2 : Nat.card E ≤ Nat.card W := Subgroup.card_le_card_group E
  omega

theorem exists_twoLocal_of_le (hp : 1 < p) {n : ℕ} (hn : 0 < n) (h : n ≤ GLATwoLocalRank p W) :
    ∃ P : Subgroup W, P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
      n ≤ CFSG.Open.pRank p (Subgroup.normalizer (P : Set W)) := by
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank at h
  have hne : {k | ∃ H : Subgroup W, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp at h
    omega
  have hmem := Nat.sSup_mem hne (twoLocal_pRank_bddAbove hp W)
  obtain ⟨H, ⟨P, hP, hP2, rfl⟩, hk⟩ := hmem
  exact ⟨P, hP, hP2, h.trans hk.ge⟩

theorem le_twoLocal_of_normalizer (hp : 1 < p) {n : ℕ} {P : Subgroup W} (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 ↥P) (h : n ≤ CFSG.Open.pRank p (Subgroup.normalizer (P : Set W))) :
    n ≤ GLATwoLocalRank p W :=
  h.trans (le_csSup (twoLocal_pRank_bddAbove hp W) ⟨_, ⟨P, hP, hP2, rfl⟩, rfl⟩)

end TwoLocal

section Count

variable {X : Type} [Group X] [Finite X]

theorem le_twoLocalRank_of_central {p : ℕ} (hp : p.Prime) {K C : Subgroup X}
    (hC : IsElemAbelian p C) (hCK : C ≤ Subgroup.centralizer (K : Set X))
    (hZ : Subgroup.center ↥K = ⊥) {n : ℕ} (hn : 0 < n) (h : n ≤ GLATwoLocalRank p ↥K) :
    n + CFSG.Open.pRank p C ≤ GLATwoLocalRank p X := by
  obtain ⟨P, hP, hP2, hrk⟩ := exists_twoLocal_of_le hp.one_lt hn h
  obtain ⟨E, hEN, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (P : Set ↥K))
  obtain ⟨c, hc⟩ := i271_exists_card_eq hp hC
  have hcr : CFSG.Open.pRank p C = c := i271_pRank_eq hp hC hc
  set P' : Subgroup X := P.map K.subtype with hP'
  set E' : Subgroup X := E.map K.subtype with hE'
  have hE'K : E' ≤ K := Subgroup.map_subtype_le E
  have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hE K.subtype
  have hE'card : Nat.card E' = p ^ CFSG.Open.pRank p (Subgroup.normalizer (P : Set ↥K)) := by
    rw [hE', Subgroup.card_map_of_injective K.subtype_injective, hEcard]
  have hcomm : ∀ x ∈ E', ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hCK hy) x (hE'K hx)
  have hdisj : E' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxC⟩
    have hxK : x ∈ K := hE'K hxE
    have hxz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hCK hxC) z z.2))
    rw [hZ, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  have hTel : IsElemAbelian p (E' ⊔ C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx, u, hu, hxu⟩ := i224_mem_sup_of_comm hcomm a.2
      obtain ⟨x', hx', u', hu', hxu'⟩ := i224_mem_sup_of_comm hcomm b.2
      apply Subtype.ext
      change (a : X) * b = b * a
      rw [hxu, hxu']
      have e1 : ∀ s ∈ E', ∀ t ∈ E', s * t = t * s := fun s hs t ht =>
        congrArg Subtype.val (hE'el.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
      have e2 : ∀ s ∈ C, ∀ t ∈ C, s * t = t * s := fun s hs t ht =>
        congrArg Subtype.val (hC.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
      calc x * u * (x' * u') = x * (u * x') * u' := by group
        _ = x * (x' * u) * u' := by rw [← hcomm x' hx' u hu]
        _ = (x * x') * (u * u') := by group
        _ = (x' * x) * (u' * u) := by rw [e1 x hx x' hx', e2 u hu u' hu']
        _ = x' * (x * u') * u := by group
        _ = x' * (u' * x) * u := by rw [hcomm x hx u' hu']
        _ = x' * u' * (x * u) := by group
    · obtain ⟨x, hx, u, hu, rfl⟩ := i224_mem_sup_of_comm hcomm hy
      have hxp : x ^ p = 1 := hE'el.2 x hx
      have hup : u ^ p = 1 := hC.2 u hu
      have e1 : Commute x u := hcomm x hx u hu
      rw [e1.mul_pow, hxp, hup, one_mul]
  have hTcard : Nat.card ↥(E' ⊔ C) = p ^ (CFSG.Open.pRank p (Subgroup.normalizer (P : Set ↥K)) + c) := by
    rw [i224_card_sup hcomm hdisj, hE'card, hc, pow_add]
  have hTN : E' ⊔ C ≤ Subgroup.normalizer (P' : Set X) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact Subgroup.le_normalizer_map K.subtype ⟨e, hEN he, rfl⟩
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hcen : ∀ z : X, z ∈ P' → u * z * u⁻¹ = z := by
        rintro _ ⟨z, -, rfl⟩
        have := Subgroup.mem_centralizer_iff.1 (hCK hu) (z : X) z.2
        calc u * (z : X) * u⁻¹ = (z : X) * u * u⁻¹ := by rw [← this]
          _ = (z : X) := by group
      constructor
      · intro hy
        rw [hcen y hy]
        exact hy
      · intro hy
        have h1 : u * y * u⁻¹ = y := by
          have h := hcen _ hy
          calc u * y * u⁻¹ = u⁻¹ * (u * (u * y * u⁻¹) * u⁻¹) * u := by group
            _ = u⁻¹ * (u * y * u⁻¹) * u := by rw [h]
            _ = y := by group
        rw [h1] at hy
        exact hy
  have hP'ne : P' ≠ ⊥ := by
    intro h0
    apply hP
    exact (Subgroup.map_eq_bot_iff_of_injective P K.subtype_injective).1 h0
  have hP'2 : IsPGroup 2 ↥P' :=
    hP2.of_equiv (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective)
  have hle := le_twoLocal_of_normalizer (n := CFSG.Open.pRank p (Subgroup.normalizer (P : Set ↥K)) + c)
    hp.one_lt hP'ne hP'2 (CFSG.SectionRank.le_pRank hp.one_lt hTN hTel hTcard)
  rw [hcr]
  omega

end Count

section D44

variable {X : Type} [Group X] [Finite X]

theorem false_of_d44_outer
    (hD : D44OuterRank) {K B : Subgroup X} (hH : I271Hyp 3 K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hQ : IsLieQuot ↥K IsD4FourIndex)
    (hout : ¬ InducesInnerIn B K) : False := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hZ : Subgroup.center ↥K = ⊥ := d44_center hq hQ
  have h2loc : 4 ≤ GLATwoLocalRank 3 ↥K := d44_twoLocal hq hQ
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  set C : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC
  have hCel : IsElemAbelian 3 C := i271_isElemAbelian_of_le hBel inf_le_left
  have hA : Nat.card (actK hBN).range ≤ 3 ^ 3 :=
    hD ↥K hq hOK hQ _ (isElemAbelian_range_actK hBel hBN)
      fun hle => hout (inducesInnerIn_of_range_le hBN hle)
  obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hBel
  obtain ⟨c, hc⟩ := i271_exists_card_eq Nat.prime_three hCel
  have hmr := i271_pRank_eq Nat.prime_three hBel hm
  have hcr := i271_pRank_eq Nat.prime_three hCel hc
  have hcard := card_range_actK hBN
  rw [hm, ← hC, hc] at hcard
  have hle : 3 ^ m ≤ 3 ^ (c + 3) := by
    rw [hcard, pow_add]
    exact Nat.mul_le_mul_left _ hA
  have hmc : m ≤ c + 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
  have h4 := le_twoLocalRank_of_central Nat.prime_three hCel inf_le_right hZ (n := 4)
    (by norm_num) h2loc
  have hrk := hH.rank_local
  rw [hmr] at hrk
  rw [hcr] at h4
  omega

end D44

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
