module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016ON
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofON
public import CFSG.RankThree.Native.ONTripleUnique

public section


namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

attribute [local irreducible] dotProduct

open CFSG.Open

variable {H : Type*} [Group H] [Finite H]

theorem map_mk_facts {p : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {E T : Subgroup H} (hE : IsElemAbelian p E) (hT : IsPGroup 2 T)
    (hTN : ¬ T ≤ N) (hET : E ≤ Subgroup.normalizer (T : Set H)) :
    IsElemAbelian p (E.map (QuotientGroup.mk' N)) ∧
      Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E ∧
      IsPGroup 2 (T.map (QuotientGroup.mk' N)) ∧ T.map (QuotientGroup.mk' N) ≠ ⊥ ∧
      E.map (QuotientGroup.mk' N) ≤
        Subgroup.normalizer ((T.map (QuotientGroup.mk' N)) : Set (H ⧸ N)) := by
  set π := QuotientGroup.mk' N
  have hinj : Set.InjOn π (E : Set H) := by
    intro x hx y hy hxy
    have hxyE : x⁻¹ * y ∈ E := E.mul_mem (E.inv_mem hx) hy
    have hxyN : x⁻¹ * y ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      show π (x⁻¹ * y) = 1
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hNpow : (x⁻¹ * y) ^ Nat.card N = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨x⁻¹ * y, hxyN⟩ : N)))
    have hcop : Nat.gcd p (Nat.card N) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
    have h1 := (pow_gcd_eq_one (a := x⁻¹ * y) (m := p) (n := Nat.card N)).2 ⟨hE.2 _ hxyE, hNpow⟩
    rw [hcop, pow_one, inv_mul_eq_one] at h1
    exact h1
  have hcard : Nat.card (E.map π) = Nat.card E := by
    have h := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h
    exact h
  have hTne : T.map π ≠ ⊥ := by
    intro hbot
    apply hTN
    intro t ht
    have : π t ∈ T.map π := Subgroup.mem_map_of_mem π ht
    rw [hbot, Subgroup.mem_bot] at this
    rw [← QuotientGroup.ker_mk' N]
    exact this
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, hcard, hT.map π, hTne, ?_⟩
  · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg π (congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨a', ha', rfl⟩
    rw [← map_pow, hE.2 a' ha', map_one]
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_inv, ← map_mul, ← map_mul]
    constructor
    · rintro ⟨t, ht, htq⟩
      refine ⟨e * t * e⁻¹, (Subgroup.mem_normalizer_iff.mp (hET he) t).mp ht, ?_⟩
      rw [map_mul, map_mul, map_mul, map_mul, htq]
    · rintro ⟨t, ht, htq⟩
      refine ⟨e⁻¹ * t * e, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hET he) (e⁻¹ * t * e)).mpr
        apply this
        rw [show e * (e⁻¹ * t * e) * e⁻¹ = t by group]
        exact ht
      · rw [map_mul, map_mul, map_inv, htq, map_mul, map_mul, map_inv]
        group
        rfl

section PQuot

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem pquot_facts {p : ℕ} (hp : p.Prime) {L E T : Subgroup G} (hEL : E ≤ L)
    (hE : IsElemAbelian p E) (hTL : T ≤ L) (hT : IsPGroup 2 T)
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p L) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    ∃ Eb Tb : Subgroup (PQuot p L), IsElemAbelian p Eb ∧ Nat.card Eb = Nat.card E ∧
      IsPGroup 2 Tb ∧ Tb ≠ ⊥ ∧ Eb ≤ Subgroup.normalizer (Tb : Set (PQuot p L)) := by
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥L) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp L
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
  have hE' : IsElemAbelian p (E.subgroupOf L) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (hE.2 _ hx)⟩
    simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  have hT' : IsPGroup 2 (T.subgroupOf L) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hT'N : ¬ T.subgroupOf L ≤ GLAPPrimeCore p ↥L := by
    intro h
    apply hTO
    intro t ht
    unfold GLAPPrimeCoreOf
    exact ⟨⟨t, hTL ht⟩, h (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hE'T' : E.subgroupOf L ≤ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hET (Subgroup.mem_subgroupOf.mp he))) h
  obtain ⟨h1, h2, h3, h4, h5⟩ := map_mk_facts hp (GLAPPrimeCore p ↥L) hN hE' hT' hT'N hE'T'
  refine ⟨_, _, h1, ?_, h3, h4, h5⟩
  rw [h2]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

end PQuot

section Row

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_pquot_equiv_ON
    {p : ℕ} {L : Subgroup G}
    (hcat : catalogIs (PSimple p L) (sporIs .ONan)) (hZ : Subgroup.center (PQuot p L) = ⊥) :
    Nonempty (PQuot p L ≃* CFSG.Blueprint.NativeSporadic.ON) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    e).trans b.symm⟩

theorem cfsgQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  obtain ⟨a, b, hab⟩ := h2.exists_pair_ne
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) b
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact hZ (Subgroup.mem_top _)

theorem nonempty_psimple_equiv_ON
    {p : ℕ} {L : Subgroup G}
    (hcat : catalogIs (PSimple p L) (sporIs .ONan)) :
    Nonempty (PSimple p L ≃* CFSG.Blueprint.NativeSporadic.ON) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact ⟨e.trans b.symm⟩

theorem card_center_pquot_dvd_three_ON
    {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hcat : catalogIs (PSimple p L) (sporIs .ONan)) :
    Nat.card (Subgroup.center (PQuot p L)) ∣ 3 := by
  obtain ⟨e⟩ := nonempty_psimple_equiv_ON hcat
  have hq := cfsgQuasisimple_of_open (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq
    (X := CFSG.Blueprint.NativeSporadic.Carrier .ONan) e
  rwa [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover.nativeRow_ONan] at h

theorem card_le_27_of_triple_ON
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] (hZ3 : Nat.card (Subgroup.center Y) = 3)
    (eON : Y ⧸ Subgroup.center Y ≃* CFSG.Blueprint.NativeSporadic.ON) {B : Subgroup Y}
    (hB : IsElemAbelian 3 B) : Nat.card B ≤ 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eK : Subgroup.center Y ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq (p := 3) hZ3
      (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  obtain ⟨e⟩ := CFSG.RankThree.Native.ONTriple.nonempty_equiv_FHat (G := Y)
    (Subgroup.center Y) eK eON
  let ψ : Y ≃* CFSG.RankThree.Native.ONTriple.GM := e.trans CFSG.RankThree.Native.ONTriple.modelEquiv
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  have h := CFSG.RankThree.PartTwo.Sec4.Res417Five.card_le_27_of_abelian_model
    (B := B.map ψ.toMonoidHom) (hB3.map _) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))
  rw [Subgroup.card_map_of_injective ψ.injective] at h
  exact h.trans (by norm_num)

theorem i1016ONAt_holds
    (G : Type) [Group G] [Finite G] : I1016ONAt G := by
  intro p hp hp2 X L hL hcat E T hEL hE hTL hT hTO hET
  obtain ⟨Eb, Tb, hEb, hEbcard, hTb, hTb1, hEbTb⟩ := pquot_facts hp hEL hE hTL hT hTO hET
  rw [← hEbcard]
  obtain ⟨eS⟩ := nonempty_psimple_equiv_ON hcat
  rcases (Nat.dvd_prime Nat.prime_three).mp (card_center_pquot_dvd_three_ON hp hL hcat) with
    h1 | h3
  · obtain ⟨e⟩ := nonempty_pquot_equiv_ON hcat (Subgroup.card_eq_one.mp h1)
    exact i1016_ON_native e hp hp2 hEb hTb hTb1 hEbTb
  · have : Fact p.Prime := ⟨hp⟩
    have hp3 : p = 3 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (I2611.isPGroup_center_pQuot' hp L)
      rw [h3] at hk
      have hk0 : k ≠ 0 := by rintro rfl; norm_num at hk
      exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hk ▸ dvd_pow_self p hk0)).symm ▸ rfl
    subst hp3
    have : Group.IsPerfect (PQuot 3 L) := ⟨(isQuasisimple_pQuot_of_glaPComponent hp hL).1⟩
    exact Or.inl ⟨rfl, card_le_27_of_triple_ON h3 eS hEb⟩

end Row

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
