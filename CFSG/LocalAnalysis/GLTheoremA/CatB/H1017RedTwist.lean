module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Row
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_phiC_eq_conj (hOut : SporadicOuterLeTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X L : Subgroup G} (hL : GLAPComponent p X L) (hsp : catalogIs (PSimple p L) isSporIndex)
    (γ : ↥(Subgroup.normalizer (L : Set G))) (hγ : γ ^ p = 1) :
    ∃ s : PSimple p L, L62.phiC p L γ = MulAut.conj s := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI : IsSimpleGroup (PSimple p L) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  obtain ⟨i, hi, ⟨e⟩⟩ := hsp
  cases i with
  | sporadic s =>
    have hout : Nat.card (Outer (PSimple p L)) ≤ 2 := hOut _ ‹_› hnab s ⟨e⟩
    set φ := L62.phiC p L γ with hφ
    have hφp : φ ^ p = 1 := by rw [hφ, ← map_pow, hγ, map_one]
    set ψ : Outer (PSimple p L) := QuotientGroup.mk φ
    have hψ : ψ ^ p = 1 := by rw [← QuotientGroup.mk_pow, hφp, QuotientGroup.mk_one]
    have hord : orderOf ψ ∣ p := orderOf_dvd_of_pow_eq_one hψ
    have hle : orderOf ψ ≤ 2 :=
      (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard ψ)).trans hout
    have h1 : orderOf ψ = 1 := by
      rcases (Nat.dvd_prime hp).1 hord with h1 | h1
      · exact h1
      · have := hp.two_le
        omega
    rw [orderOf_eq_one_iff] at h1
    obtain ⟨s', hs'⟩ := (QuotientGroup.eq_one_iff φ).mp h1
    exact ⟨s', hs'.symm⟩
  | cyclic _ _ => exact absurd hi (by simp [isSporIndex])
  | alternating _ _ => exact absurd hi (by simp [isSporIndex])
  | lie _ => exact absurd hi (by simp [isSporIndex])

private theorem phiC_piL (p : ℕ) (L : Subgroup G) (γ : ↥(Subgroup.normalizer (L : Set G)))
    (l : ↥L) : L62.phiC p L γ (piL p L l) = piL p L (L.normalizerMonoidHom γ l) :=
  L62.phiC_apply_mk p L γ l

private theorem mem_core_of_piL_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    {w : ↥L} {k : ℕ} (hk : w ^ 2 ^ k = 1) (hφ : piL p L w = 1) : w ∈ GLAPPrimeCore p ↥L := by
  have hZp : IsPGroup p (Subgroup.center (PQuot p L)) := I2611.isPGroup_center_pQuot' hp L
  have hcop2 : Nat.Coprime (2 : ℕ) p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hcZ : (QuotientGroup.mk w : PQuot p L) ∈ Subgroup.center (PQuot p L) :=
    (QuotientGroup.eq_one_iff _).1 hφ
  obtain ⟨j, hj⟩ := hZp ⟨_, hcZ⟩
  have hj' : (QuotientGroup.mk w : PQuot p L) ^ p ^ j = 1 := congrArg Subtype.val hj
  have hk' : (QuotientGroup.mk w : PQuot p L) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk w : PQuot p L) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk') (Nat.Coprime.pow k j hcop2))
      (orderOf_dvd_of_pow_eq_one hj')
  exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3)

private theorem conj_injective_of_center {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut S => φ g) hab
    simp only [MulAut.conj_apply] at h
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
      _ = a⁻¹ * b * g := by group
  rw [hcen, Subgroup.mem_bot] at hc
  calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
    _ = b := by group

theorem exists_twist_pSimple (hOut : SporadicOuterLeTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X B L : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hL : GLAPComponent p X L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hsp : catalogIs (PSimple p L) isSporIndex)
    (hcm : ∀ b ∈ B, CentMod p L b ↔ b ∈ Subgroup.zpowers x)
    {T : Subgroup G} (hTL : T ≤ L) (hT : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (htw : ¬ (⁅T, B⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L) :
    ∃ E V : Subgroup (PSimple p L), IsElemAbelian p E ∧ Nat.card E * p = Nat.card B ∧
      IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set (PSimple p L)) ∧
      ¬ ∀ e ∈ E, ∀ v ∈ V, e * v = v * e := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI : IsSimpleGroup (PSimple p L) := hq.2
  have hcen : Subgroup.center (PSimple p L) = ⊥ := center_eq_bot_of_isSimpleGroup
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq)
  have hinj := conj_injective_of_center hcen
  set f : ↥B →* MulAut (PSimple p L) := (L62.phiC p L).comp (Subgroup.inclusion hBN) with hf
  have hfB : ∀ b : ↥B, ∃ s : PSimple p L, f b = MulAut.conj s := fun b =>
    exists_phiC_eq_conj hOut hp hp2 hL hsp _ (Subtype.ext (by simp [hB.2 b.1 b.2]))
  set E : Subgroup (PSimple p L) := f.range.comap MulAut.conj with hE
  have hmemE : ∀ e ∈ E, ∃ b : ↥B, f b = MulAut.conj e := fun e he => he
  have hfE : ∀ b : ↥B, ∃ s ∈ E, f b = MulAut.conj s := fun b => by
    obtain ⟨s, hs⟩ := hfB b
    exact ⟨s, ⟨b, hs⟩, hs⟩
  have hact : ∀ (b : ↥B) (l : ↥L), f b (piL p L l) =
      piL p L ⟨b * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hBN b.2) l).1 l.2⟩ := by
    intro b l
    rw [hf, MonoidHom.comp_apply, phiC_piL]
    rfl
  have hker : Nat.card f.ker = p := by
    have hk : f.ker = (Subgroup.zpowers x).subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hcm b b.2]
      exact L62.phiC_eq_one_iff hp hL (hBN b.2)
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).2 hxB)).toEquiv, Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 x hxB) hx1
  have hcardE : Nat.card E = Nat.card f.range := by
    have hmap : E.map (MulAut.conj : PSimple p L →* MulAut (PSimple p L)) = f.range := by
      rw [hE, Subgroup.map_comap_eq, inf_eq_right]
      rintro _ ⟨b, rfl⟩
      obtain ⟨s, hs⟩ := hfB b
      exact ⟨s, hs.symm⟩
    rw [← Subgroup.card_map_of_injective hinj, hmap]
  have hEcomm : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := by
    intro a ha c hc
    obtain ⟨b, hb⟩ := hmemE a ha
    obtain ⟨d, hd⟩ := hmemE c hc
    have hbd : b * d = d * b := Subtype.ext (isElemAbelian_commute hB b.2 d.2)
    apply hinj
    rw [map_mul, map_mul, ← hb, ← hd, ← map_mul, ← map_mul, hbd]
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a c => Subtype.ext (hEcomm a.1 a.2 c.1 c.2)⟩⟩, fun e he => ?_⟩
    obtain ⟨b, hb⟩ := hmemE e he
    apply hinj
    rw [map_pow, ← hb, ← map_pow, map_one,
      show b ^ p = 1 from Subtype.ext (by simp [hB.2 b.1 b.2]), map_one]
  set V : Subgroup (PSimple p L) := (T.subgroupOf L).map (piL p L) with hV
  have hV2 : IsPGroup 2 V := IsPGroup.map (isPGroup_subgroupOf_of hT) (piL p L)
  have hconj : ∀ e ∈ E, ∀ w ∈ V, e * w * e⁻¹ ∈ V := by
    intro e he w hw
    obtain ⟨b, hb⟩ := hmemE e he
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hw
    have h1 : e * piL p L t * e⁻¹ = f b (piL p L t) := by rw [hb, MulAut.conj_apply]
    rw [h1, hact]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    exact (Subgroup.mem_normalizer_iff.1 (hBT b.2) t).1 (Subgroup.mem_subgroupOf.1 ht)
  have hEV : E ≤ Subgroup.normalizer (V : Set (PSimple p L)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconj e he w, fun h => ?_⟩
    have h2 := hconj e⁻¹ (E.inv_mem he) _ h
    rwa [inv_inv, show e⁻¹ * (e * w * e⁻¹) * e = w by group] at h2
  have htwist : ¬ ∀ e ∈ E, ∀ v ∈ V, e * v = v * e := by
    intro hc
    apply htw
    rw [Subgroup.commutator_le]
    intro t ht b hb
    obtain ⟨s, hsE, hs⟩ := hfE ⟨b, hb⟩
    set tL : ↥L := ⟨t, hTL ht⟩
    set u : ↥L := ⟨b * t * b⁻¹, (Subgroup.mem_normalizer_iff.1 (hBN hb) t).1 (hTL ht)⟩ with hu
    have huT : (u : G) ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
    have h1 : piL p L u = piL p L tL := by
      have h2 := hact ⟨b, hb⟩ tL
      rw [hs, MulAut.conj_apply,
        hc s hsE _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)),
        mul_inv_cancel_right] at h2
      exact h2.symm
    have hwT : ((u * tL⁻¹ : ↥L) : G) ∈ T := T.mul_mem huT (T.inv_mem ht)
    obtain ⟨k, hk⟩ := hT ⟨_, hwT⟩
    have hk' : (u * tL⁻¹) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hw1 : piL p L (u * tL⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hmem := mem_core_of_piL_eq_one hp hp2 hk' hw1
    have hval : ((u * tL⁻¹ : ↥L) : G)⁻¹ = ⁅t, b⁆ := by
      simp only [hu, tL, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [← hval]
    exact (GLAPPrimeCoreOf p L).inv_mem (Subgroup.mem_map.2 ⟨_, hmem, rfl⟩)
  refine ⟨E, V, hEab, ?_, hV2, hEV, htwist⟩
  have hlag := Subgroup.card_ker_mul_card_range f
  rw [hker] at hlag
  rw [hcardE, mul_comm]
  exact hlag

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
