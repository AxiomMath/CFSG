module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem i76_mem_glaPPrimeCoreOf_iff {p : ℕ} {L : Subgroup G} {x : G} (hx : x ∈ L) :
    x ∈ GLAPPrimeCoreOf p L ↔ (⟨x, hx⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem i76_conj_mem {p : ℕ} {L : Subgroup G} {l y : G} (hl : l ∈ L)
    (hy : y ∈ GLAPPrimeCoreOf p L) : l * y * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
  exact Subgroup.mem_map.2 ⟨⟨l, hl⟩ * z * (⟨l, hl⟩ : ↥L)⁻¹,
    Subgroup.Normal.conj_mem (GLAPPrimeCore.normal p ↥L) z hz ⟨l, hl⟩, rfl⟩

private theorem i76_coe_normalizerMonoidHom {L : Subgroup G}
    (γ : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹ := rfl

private theorem i76_barAut_eq_one_iff {p : ℕ} {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨a, ha⟩ = 1 ↔ ∀ l ∈ L, ⁅l, a⁆ ∈ GLAPPrimeCoreOf p L := by
  constructor
  · intro h l hl
    have h1 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) =>
      φ (QuotientGroup.mk (⟨l, hl⟩ : ↥L))) h
    simp only [MulAut.one_apply] at h1
    rw [barAut_mk, QuotientGroup.eq] at h1
    have h2 := Subgroup.mem_map_of_mem L.subtype h1
    have e : ⁅l, a⁆ =
        l * (((L.normalizerMonoidHom ⟨a, ha⟩ ⟨l, hl⟩)⁻¹ * ⟨l, hl⟩ : ↥L) : G) * l⁻¹ := by
      simp only [commutatorElement_def, i76_coe_normalizerMonoidHom, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    rw [e]
    exact i76_conj_mem hl h2
  · intro h
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq]
      have hc := i76_conj_mem (L.inv_mem x.2) (h (x : G) x.2)
      have key : (((L.normalizerMonoidHom ⟨a, ha⟩ x)⁻¹ * x : ↥L) : G) ∈ GLAPPrimeCoreOf p L := by
        have e : (((L.normalizerMonoidHom ⟨a, ha⟩ x)⁻¹ * x : ↥L) : G) =
            (x : G)⁻¹ * ⁅(x : G), a⁆ * ((x : G)⁻¹)⁻¹ := by
          simp only [commutatorElement_def, i76_coe_normalizerMonoidHom, Subgroup.coe_mul,
            Subgroup.coe_inv]
          group
        rw [e]
        exact hc
      exact (i76_mem_glaPPrimeCoreOf_iff _).1 key

private theorem i76_inducesInnerMod_of_barAut {p : ℕ} {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) {k : ↥L ⧸ GLAPPrimeCore p ↥L}
    (h : barAut p L ⟨a, ha⟩ = MulAut.conj k) : InducesInnerMod p L a := by
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
  have ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ha
  have hinv : barAut p L ⟨a⁻¹, ha'⟩ =
      MulAut.conj (QuotientGroup.mk k'⁻¹ : ↥L ⧸ GLAPPrimeCore p ↥L) := by
    have e : (⟨a⁻¹, ha'⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨a, ha⟩)⁻¹ := rfl
    rw [e, map_inv, h, QuotientGroup.mk_inv, map_inv]
  refine ⟨(k' : G), k'.2, fun y hy => ?_⟩
  have h1 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) =>
    φ (QuotientGroup.mk (⟨y, hy⟩ : ↥L))) hinv
  simp only [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
  rw [QuotientGroup.eq] at h1
  refine Subgroup.mem_map.2 ⟨_, Subgroup.inv_mem _ h1, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, i76_coe_normalizerMonoidHom, Subgroup.coe_mk,
    Subgroup.coe_subtype]
  group

private theorem i76_isElemAbelian_range {p : ℕ} {H M : Type*} [Group H] [Group M]
    (hcomm : ∀ a b : H, a * b = b * a) (hpow : ∀ a : H, a ^ p = 1) (f : H →* M) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    change (a : M) * (b : M) = (b : M) * (a : M)
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm x z]
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
    change y ^ p = 1
    rw [← hx, ← map_pow, hpow x, map_one]

private theorem i76_exists_quot_elemAbelian {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    {p : ℕ} {D : Subgroup (MulAut Q)} (hD : IsElemAbelian p D) (hDI : D ⊓ inner Q = ⊥) :
    ∃ D' : Subgroup (MulAut (Q ⧸ Subgroup.center Q)), IsElemAbelian p D' ∧
      Nat.card D' = Nat.card D ∧ D' ⊓ inner (Q ⧸ Subgroup.center Q) = ⊥ := by
  have hinj : Function.Injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
  refine ⟨D.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q),
    CFSG.SectionRank.isElemAbelian_map hD _, Subgroup.card_map_of_injective hinj, ?_⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨α, hα, rfl⟩, hα'⟩
  have h1 : α ∈ D ⊓ inner Q := ⟨hα, mem_inner_of_centerQuotientHom_mem hα'⟩
  rw [hDI, Subgroup.mem_bot] at h1
  rw [h1, map_one]
  exact Subgroup.one_mem _

private theorem i76_D4_of_isD4 (d : TauCeti.LieTypeIndex) (hd : d.Valid)
    (h : isD4ThreePowThree d) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      d = TauCeti.LieTypeIndex.D 4 q ∧ q.p = 3 ∧ 3 ∣ q.exponent := by
  cases d with
  | D n q =>
    by_cases hn : n = 4
    · subst hn
      exact ⟨q, hd, rfl, h.1, h.2⟩
    · exfalso
      unfold isD4ThreePowThree at h
      split at h <;> simp_all
  | _ => exact (show False from h).elim

private theorem i76_exists_D4_of_onLie (i : TauCeti.CFSGIndex) (hi : onLie isD4ThreePowThree i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ ∧ q.p = 3 ∧ 3 ∣ q.exponent := by
  cases i with
  | lie j =>
    obtain ⟨q, hv, hdq, hq3, hdvd⟩ := i76_D4_of_isD4 j.1 j.2 hi
    exact ⟨q, hv, congrArg TauCeti.CFSGIndex.lie (Subtype.ext hdq), hq3, hdvd⟩
  | _ => exact (show False from hi).elim

theorem i76At_of {G : Type} [Group G] [Finite G] {p : ℕ} (h26 : KD26a) (h76 : KD76c p)
    (hD4 : KDD4TwoLocal) (h65 : I65At G p) : I76At G p := by
  intro hp hp2 X K A hX hK hChev hAel hAN hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hcat : CFSG.Open.IsCatalogGroup (PSimple p K) := by
    rcases hChev with ⟨i, -, e⟩ | ⟨i, -, e⟩ <;> exact ⟨i, e⟩
  have hKhat : IsKHat (PQuot p K) := ⟨hq, hcat⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ↥A →* MulAut (PQuot p K),
      ψ = (barAut p K).comp (Subgroup.inclusion hAN) := ⟨_, rfl⟩
  have hψapp : ∀ x : ↥A, ψ x = barAut p K ⟨(x : G), hAN x.2⟩ := fun x => by
    rw [hψdef]
    rfl
  have hA_comm : ∀ a b : ↥A, a * b = b * a := fun a b => hAel.1.1.comm a b
  have hA_pow : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAel.2 a a.2)
  have hDel : IsElemAbelian p ψ.range := i76_isElemAbelian_range hA_comm hA_pow ψ
  have hker : ∀ x : ↥A, ψ x = 1 ↔ (x : G) ∈ centModSubgroup p K := by
    intro x
    rw [hψapp, i76_barAut_eq_one_iff (hAN x.2), mem_centModSubgroup]
    exact ⟨fun h => ⟨hAN x.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card ψ.ker = Nat.card ↥(A ⊓ centModSubgroup p K) := by
    refine Nat.card_congr
      { toFun := fun x =>
          ⟨(x.1 : G), Subgroup.mem_inf.2 ⟨x.1.2, (hker x.1).1 (MonoidHom.mem_ker.1 x.2)⟩⟩
        invFun := fun y => ⟨⟨(y.1 : G), (Subgroup.mem_inf.1 y.2).1⟩,
          MonoidHom.mem_ker.2 ((hker _).2 (Subgroup.mem_inf.1 y.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hcardA : Nat.card ψ.ker * Nat.card ψ.range = Nat.card ↥A :=
    Subgroup.card_ker_mul_card_range ψ
  have hDinner : ψ.range ⊓ inner (PQuot p K) = ⊥ := by
    rw [eq_bot_iff]
    rintro α ⟨hα, hαi⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hα
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hαi
    have hind : InducesInnerMod p K (x : G) :=
      i76_inducesInnerMod_of_barAut (hAN x.2) ((hψapp x).symm.trans hk.symm)
    have hc : (x : G) ∈ centModSubgroup p K := by
      by_contra hc
      exact hnot (x : G) x.2 (fun hcm => hc (centMod_iff.1 hcm)) hind
    exact Subgroup.mem_bot.2 ((hker x).2 hc)
  have hKD := h26 (PQuot p K) hKhat p hp hp2 ψ.range hDel
  rw [hDinner, Subgroup.card_bot, mul_one] at hKD
  refine ⟨?_, ?_⟩
  · rw [← hcardA, ← hcardker]
    calc Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card ψ.ker * p ^ 2 :=
          Nat.mul_le_mul_left _ hKD
      _ = p ^ 2 * Nat.card ψ.ker := mul_comm _ _
  · intro heq
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    rw [← hcardA, ← hcardker] at heq
    have hrange : Nat.card ψ.range = p ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [heq, mul_comm]
    have hbot : ψ.range ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hrange
      have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    obtain ⟨d, hd, hd1⟩ : ∃ d ∈ ψ.range, d ≠ 1 := by
      by_contra hcon
      exact hbot ((Subgroup.eq_bot_iff_forall _).2 fun d hd => by
        by_contra hd1
        exact hcon ⟨d, hd, hd1⟩)
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    have hxker : (x : G) ∉ centModSubgroup p K := fun hc => hd1 ((hker x).2 hc)
    have hxnc : ¬ CentMod p K (x : G) := fun hc => hxker (centMod_iff.1 hc)
    have hxni : ¬ InducesInnerMod p K (x : G) := hnot (x : G) x.2 hxnc
    have hcenter : Subgroup.center (PQuot p K) = ⊥ :=
      h65 hp hp2 X K hX hK hChev ⟨(x : G), hAN x.2, hAel.2 _ x.2, hxnc, hxni⟩
    haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
    obtain ⟨D', hD'el, hD'card, hD'I⟩ := i76_exists_quot_elemAbelian hDel hDinner
    have hsimple : IsSimpleGroup (PSimple p K) := hq.2
    have hnon : ∃ a b : PSimple p K, a * b ≠ b * a :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
    obtain ⟨hp3, hcatD⟩ := h76 (PSimple p K) hsimple hnon hChev D' hD'el
      (hD'card.trans hrange) hD'I
    have e1 : PQuot p K ≃* PSimple p K :=
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    obtain ⟨i, hi, ⟨e⟩⟩ := hcatD
    obtain ⟨q, hv, rfl, hq3, hdvd⟩ := i76_exists_D4_of_onLie i hi
    subst hp3
    have hR := hD4 (PQuot 3 K) q hv hq3 ⟨e1.trans e⟩
    have hexp : 3 ≤ q.exponent := Nat.le_of_dvd q.exponent_pos hdvd
    exact ⟨rfl, by omega⟩

end CFSG.LocalAnalysis.GLTheoremA
