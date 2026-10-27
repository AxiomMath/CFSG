module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Rank

variable {G A : Type*} [Group G] [Group A]

theorem pRank_eq_pRank_top_subtype [Finite G] {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    CFSG.Open.pRank p H = CFSG.Open.pRank p (⊤ : Subgroup ↥H) := by
  apply le_antisymm
  · obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp H
    refine CFSG.SectionRank.le_pRank hp (E := E.subgroupOf H) le_top ?_ ?_
    · have := hE.1
      exact ⟨inferInstance, fun x hx => Subtype.ext (hE.2 x hx)⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hcard]
  · have h := CFSG.SectionRank.pRank_le_map hp H.subtype H.subtype_injective ⊤
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h

theorem pRank_map_eq_of_injective [Finite A] [Finite G] {p : ℕ} (hp : 1 < p) (f : A →* G)
    (hf : Function.Injective f) (H : Subgroup A) :
    CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p H := by
  rw [pRank_eq_pRank_top_subtype hp (H.map f), pRank_eq_pRank_top_subtype hp H]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (H.equivMapOfInjective f hf)).symm

end Rank

section CoprimeQuotient

variable {Z : Type*} [Group Z] [Finite Z] {p : ℕ}

theorem exists_elemAbelian_lift [hp : Fact p.Prime] (N : Subgroup Z) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {Eb : Subgroup (Z ⧸ N)} (hE : IsElemAbelian p Eb) :
    ∃ S : Subgroup Z, IsElemAbelian p S ∧ S.map (QuotientGroup.mk' N) = Eb ∧
      Nat.card S = Nat.card Eb := by
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  have hEp : IsPGroup p Eb := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hcard⟩ := hEp.exists_card_eq
  set P : Subgroup Z := Eb.comap (QuotientGroup.mk' N) with hP
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (Eb : Set (Z ⧸ N))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P))
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* Z := P.subtype.comp (S : Subgroup P).subtype
  set φ : S →* Eb := ((QuotientGroup.mk' N).comp ι).codRestrict Eb fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have := hE.1
  have hsurj : Function.Surjective φ :=
    (hφ.bijective_of_nat_card_le (by rw [hcard, hScard])).2
  refine ⟨ι.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Z) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    apply hφ
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : x ^ p = 1 := by
      apply hφ
      rw [map_pow, map_one]
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ (φ x).2)
    rw [this, map_one]
  · ext e
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact (φ s).2
    · intro he
      obtain ⟨s, hs⟩ := hsurj ⟨e, he⟩
      exact ⟨ι s, ⟨s, rfl⟩, congrArg Subtype.val hs⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, hScard, hcard]

theorem exists_sylow_normalized {r : ℕ} [Fact r.Prime] [Fact p.Prime] {W S : Subgroup Z}
    (hSW : S ≤ Subgroup.normalizer (W : Set Z)) (hS : IsPGroup p S)
    (hW : ¬ p ∣ Nat.card W) :
    ∃ P : Sylow r W, S ≤ Subgroup.normalizer ((P : Subgroup W).map W.subtype : Set Z) := by
  classical
  let _ : MulDistribMulAction S W := Subgroup.conjMulDistribMulActionOfLeNormalizer S W hSW
  have hnot : ¬ p ∣ Nat.card (Sylow r W) := by
    intro hdvd
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r W))
    exact hW (hdvd.trans (Q.card_dvd_index.trans (Q : Subgroup W).index_dvd_card))
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) hnot
  refine ⟨P, fun s hs => ?_⟩
  have hfix : ∀ t : S, t • P = P := fun t => MulAction.mem_fixedPoints.mp hP t
  have key : ∀ t : S, ∀ x : Z, x ∈ (P : Subgroup W).map W.subtype →
      (t : Z) * x * (t : Z)⁻¹ ∈ (P : Subgroup W).map W.subtype := by
    intro t x hx
    obtain ⟨w, hwP, rfl⟩ := hx
    have h1 : t • w ∈ ((t • P : Sylow r W) : Subgroup W) := by
      rw [Sylow.pointwise_smul_def]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, hwP, rfl⟩
    rw [hfix t] at h1
    exact ⟨t • w, h1, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key ⟨_, hs⟩ y
  · intro hy
    have := key ⟨_, S.inv_mem hs⟩ _ hy
    simpa [mul_assoc] using this

theorem glaTwoLocalRank_quotient_le (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup Z) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) : GLATwoLocalRank p (Z ⧸ N) ≤ GLATwoLocalRank p Z := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup Z, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card Z, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card Z := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank p H ≤ Nat.card Z
    omega
  refine csSup_le' fun k hk => ?_
  obtain ⟨H, ⟨T, hT, hT2, rfl⟩, rfl⟩ := hk
  obtain ⟨Eb, hEbH, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (T : Set (Z ⧸ N)))
  obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift N hN hEel
  set W : Subgroup Z := T.comap (QuotientGroup.mk' N) with hW
  have hSW : S ≤ Subgroup.normalizer (W : Set Z) := by
    intro s hs
    have hsb : QuotientGroup.mk' N s ∈ Subgroup.normalizer (T : Set (Z ⧸ N)) :=
      hEbH (hSmap ▸ ⟨s, hs, rfl⟩)
    have h := Subgroup.mem_normalizer_iff.1 hsb
    rw [Subgroup.mem_normalizer_iff]
    intro w
    change QuotientGroup.mk' N w ∈ T ↔ QuotientGroup.mk' N (s * w * s⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact h _
  obtain ⟨j, hj⟩ := hT2.exists_card_eq
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hT (Subgroup.eq_bot_of_card_eq T (by simpa using hj))
  have hWcard : Nat.card W = Nat.card N * 2 ^ j := by
    rw [← hj]
    exact QuotientGroup.card_preimage_mk N (T : Set (Z ⧸ N))
  have hWp : ¬ p ∣ Nat.card W := by
    rw [hWcard]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact hN h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      exact hp2 this
  have hSp : IsPGroup p S := by
    have := hSel.1
    exact fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hSel.2 g.1 g.2)⟩
  obtain ⟨P, hPS⟩ := exists_sylow_normalized (r := 2) hSW hSp hWp
  set P' : Subgroup Z := (P : Subgroup W).map W.subtype with hP'
  have hP'2 : IsPGroup 2 P' := (P.isPGroup').map _
  have hPne : P' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P' = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hP', Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity,
      hWcard] at h1
    have h2 : 0 < (Nat.card N * 2 ^ j).factorization 2 := by
      rw [Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ two_ne_zero), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
      omega
    have := Nat.one_lt_pow h2.ne' (by norm_num : 1 < 2)
    omega
  have hloc : IsTwoLocal (Subgroup.normalizer (P' : Set Z)) := ⟨P', hPne, hP'2, rfl⟩
  have hr : CFSG.Open.pRank p (Subgroup.normalizer (T : Set (Z ⧸ N))) ≤
      CFSG.Open.pRank p (Subgroup.normalizer (P' : Set Z)) := by
    have hcardS : Nat.card S = p ^ CFSG.Open.pRank p (Subgroup.normalizer (T : Set (Z ⧸ N))) := by
      rw [hScard, hEcard]
    exact CFSG.SectionRank.le_pRank hp.one_lt hPS hSel hcardS
  exact hr.trans (le_csSup hbdd ⟨_, hloc, rfl⟩)

theorem normalizer_map_quotient_le [Fact p.Prime] (N : Subgroup Z) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {E : Subgroup Z} (hE : IsPGroup p E) :
    Subgroup.normalizer ((E.map (QuotientGroup.mk' N) : Subgroup (Z ⧸ N)) : Set (Z ⧸ N)) ≤
      (Subgroup.normalizer (E : Set Z)).map (QuotientGroup.mk' N) := by
  classical
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  set Eb : Subgroup (Z ⧸ N) := E.map (QuotientGroup.mk' N) with hEb
  set W : Subgroup Z := Eb.comap (QuotientGroup.mk' N) with hW
  have hEW : E ≤ W := fun e he => ⟨e, he, rfl⟩
  have hxn := Subgroup.mem_normalizer_iff.1 hxb
  have hxW : ∀ z : Z, z ∈ W ↔ x * z * x⁻¹ ∈ W := by
    intro z
    change QuotientGroup.mk' N z ∈ Eb ↔ QuotientGroup.mk' N (x * z * x⁻¹) ∈ Eb
    rw [map_mul, map_mul, map_inv]
    exact hxn _
  set E' : Subgroup Z := E.map (MulAut.conj x).toMonoidHom with hE'
  have hE'W : E' ≤ W := by
    rintro _ ⟨e, he, rfl⟩
    exact (hxW e).1 (hEW he)
  obtain ⟨a, hcard⟩ := hE.exists_card_eq
  have hEcard : Nat.card E = p ^ a := hcard
  have hE'card : Nat.card E' = p ^ a := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj x).injective, hEcard]
  have hdisj : Disjoint E N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hEcard]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN))
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have h1 : (s : Z) ∈ E ⊓ N := ⟨s.2, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hEbcard : Nat.card Eb = p ^ a := by
    have hr : ((QuotientGroup.mk' N).comp E.subtype).range = Eb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hEcard]
  have hWcard : Nat.card W = Nat.card N * p ^ a := by
    rw [← hEbcard]
    exact QuotientGroup.card_preimage_mk N (Eb : Set (Z ⧸ N))
  have hfact : (Nat.card W).factorization p = a := by
    rw [hWcard, Nat.factorization_mul Nat.card_pos.ne'
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow Fact.out,
      Finsupp.single_eq_same, zero_add]
  have hPEcard : Nat.card (E.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [hfact, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv, hEcard]
  have hPE'card : Nat.card (E'.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [hfact, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'W).toEquiv, hE'card]
  let PE : Sylow p W := Sylow.ofCard (E.subgroupOf W) hPEcard
  let PE' : Sylow p W := Sylow.ofCard (E'.subgroupOf W) hPE'card
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W PE PE'
  have hwE : ∀ z ∈ E, (w : Z) * z * (w : Z)⁻¹ ∈ E' := by
    intro z hz
    have hzW : (⟨z, hEW hz⟩ : W) ∈ (PE : Subgroup W) := hz
    have h1 : MulAut.conj w ⟨z, hEW hz⟩ ∈ ((w • PE : Sylow p W) : Subgroup W) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨_, hzW, rfl⟩
    rw [hw] at h1
    exact h1
  set y : Z := x⁻¹ * (w : Z) with hy
  have hyE : ∀ z ∈ E, y * z * y⁻¹ ∈ E := by
    intro z hz
    obtain ⟨e, he, hex⟩ := hwE z hz
    have : y * z * y⁻¹ = e := by
      have h2 : x * e * x⁻¹ = (w : Z) * z * (w : Z)⁻¹ := hex
      calc y * z * y⁻¹ = x⁻¹ * ((w : Z) * z * (w : Z)⁻¹) * x := by rw [hy]; group
        _ = x⁻¹ * (x * e * x⁻¹) * x := by rw [h2]
        _ = e := by group
    rw [this]
    exact he
  have hyN : y ∈ Subgroup.normalizer (E : Set Z) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hyE z hz, fun hz => ?_⟩
    let f : E → E := fun e => ⟨y * e * y⁻¹, hyE e e.2⟩
    have hfi : Function.Injective f := by
      intro a b hab
      have h3 := congrArg Subtype.val hab
      simp only [f] at h3
      exact Subtype.ext (by simpa using h3)
    obtain ⟨e, he⟩ := Finite.injective_iff_surjective.1 hfi ⟨y * z * y⁻¹, hz⟩
    have h3 := congrArg Subtype.val he
    simp only [f] at h3
    have h4 : (e : Z) = z := by simpa using h3
    rw [← h4]
    exact e.2
  have hxy : x = (w : Z) * y⁻¹ := by rw [hy]; group
  have hwb : QuotientGroup.mk' N (w : Z) ∈ (Subgroup.normalizer (E : Set Z)).map
      (QuotientGroup.mk' N) := by
    have : QuotientGroup.mk' N (w : Z) ∈ Eb := w.2
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, Subgroup.le_normalizer he, hee⟩
  have hyb : QuotientGroup.mk' N y⁻¹ ∈ (Subgroup.normalizer (E : Set Z)).map
      (QuotientGroup.mk' N) := ⟨y⁻¹, Subgroup.inv_mem _ hyN, rfl⟩
  have : QuotientGroup.mk' N x ∈ (Subgroup.normalizer (E : Set Z)).map (QuotientGroup.mk' N) := by
    rw [hxy, map_mul]
    exact Subgroup.mul_mem _ hwb hyb
  exact this

end CoprimeQuotient

end CFSG.LocalAnalysis.GLTheoremB
