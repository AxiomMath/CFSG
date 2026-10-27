module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem barAut_eq_one_iff {p : ℕ} {K : Subgroup G}
    (g : ↥(Subgroup.normalizer (K : Set G))) :
    barAut p K g = 1 ↔ (g : G) ∈ centModSubgroup p K := by
  have hmem : ∀ z : ↥K, ((z : G) ∈ GLAPPrimeCoreOf p K ↔ z ∈ GLAPPrimeCore p ↥K) :=
    fun z => Subgroup.mem_map_iff_mem K.subtype_injective
  have key : ∀ x : ↥K, (QuotientGroup.mk (K.normalizerMonoidHom g x) : PQuot p K) =
      QuotientGroup.mk x ↔ ⁅(x : G), (g : G)⁆ ∈ GLAPPrimeCoreOf p K := by
    intro x
    rw [QuotientGroup.eq]
    have hc : ⁅(x : G), (g : G)⁆ =
        ((x * ((K.normalizerMonoidHom g x)⁻¹ * x) * x⁻¹ : ↥K) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      group
    rw [hc, hmem]
    constructor
    · intro h
      exact (GLAPPrimeCore.normal p ↥K).conj_mem _ h x
    · intro h
      have h' := (GLAPPrimeCore.normal p ↥K).conj_mem _ h x⁻¹
      have e : x⁻¹ * (x * ((K.normalizerMonoidHom g x)⁻¹ * x) * x⁻¹) * x⁻¹⁻¹ =
          (K.normalizerMonoidHom g x)⁻¹ * x := by group
      rwa [e] at h'
  constructor
  · intro h
    refine mem_centModSubgroup.2 ⟨g.2, fun l hl => ?_⟩
    have h1 := congrArg (fun ψ : MulAut (PQuot p K) => ψ (QuotientGroup.mk (⟨l, hl⟩ : ↥K))) h
    simp only [barAut_mk, MulAut.one_apply] at h1
    exact (key ⟨l, hl⟩).1 h1
  · intro h
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [barAut_mk, MulAut.one_apply]
    exact (key x).2 ((mem_centModSubgroup.1 h).2 (x : G) x.2)

private theorem inducesInnerMod_of_barAut_mem_inner {p : ℕ} {K : Subgroup G}
    (g : ↥(Subgroup.normalizer (K : Set G))) (h : barAut p K g ∈ inner (PQuot p K)) :
    InducesInnerMod p K (g : G) := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective m
  have hinv : barAut p K g⁻¹ = MulAut.conj (QuotientGroup.mk w⁻¹ : PQuot p K) := by
    rw [map_inv, ← hm, ← map_inv]
    rfl
  refine ⟨(w : G), w.2, fun y hy => ?_⟩
  have h1 : barAut p K g⁻¹ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w⁻¹ * ⟨y, hy⟩ * w⁻¹⁻¹) := by
    rw [hinv, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h3 : (((w⁻¹ * ⟨y, hy⟩ * w⁻¹⁻¹)⁻¹ * K.normalizerMonoidHom g⁻¹ ⟨y, hy⟩ : ↥K) : G) =
      ((w : G)⁻¹ * y * (w : G))⁻¹ * ((g : G)⁻¹ * y * (g : G)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
      inv_inv]
  rw [← h3]
  exact Subgroup.mem_map_of_mem K.subtype (QuotientGroup.eq.1 h1.symm)

private theorem exists_elemAbelian_lift {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal] (hN : ¬ p ∣ Nat.card N) (E : Subgroup (Y ⧸ N))
    (hE : IsElemAbelian p E) :
    ∃ W : Subgroup Y, IsElemAbelian p W ∧ W.map (QuotientGroup.mk' N) = E ∧
      Nat.card W = Nat.card E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmk : ∀ y : Y, QuotientGroup.mk' N y = 1 ↔ y ∈ N := fun y => QuotientGroup.eq_one_iff y
  have hOE : N ≤ E.comap (QuotientGroup.mk' N) := fun n hn => by
    rw [Subgroup.mem_comap, (hmk n).2 hn]
    exact E.one_mem
  have hEN : E.comap (QuotientGroup.mk' N) ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hEp : ∀ e ∈ E.comap (QuotientGroup.mk' N), ∃ k : ℕ, e ^ (p ^ k) ∈ N := fun e he => by
    refine ⟨1, ?_⟩
    rw [pow_one, ← hmk, map_pow]
    exact hE.2 _ (Subgroup.mem_comap.1 he)
  have hNO : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
  have hENO : E.comap (QuotientGroup.mk' N) ≤ (⊤ : Subgroup Y) ⊔ N :=
    le_sup_of_le_left le_top
  obtain ⟨W, -, hWp, -, hWsup⟩ := exists_pGroup_lift hp hN hOE hEN hEp
    IsPGroup.of_bot bot_le bot_le hNO hENO
  have hWN : W ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := hWp.exists_card_eq
    have h1 : Nat.card ↥(W ⊓ N) ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
    have hj0 : j = 0 := by
      by_contra hne
      apply hN
      have h2 : Nat.card ↥(W ⊓ N) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_right
      rw [hj] at h2
      exact (dvd_pow_self p hne).trans h2
    have hcard1 : Nat.card ↥(W ⊓ N) = 1 := by rw [hj, hj0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hkey : ∀ w ∈ W, QuotientGroup.mk' N w = 1 → w = 1 := by
    intro w hw h1
    have hwN : w ∈ W ⊓ N := ⟨hw, (hmk w).1 h1⟩
    rw [hWN, Subgroup.mem_bot] at hwN
    exact hwN
  have hWmap : W.map (QuotientGroup.mk' N) = E := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hWsup
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h
  have hfinj : Function.Injective ((QuotientGroup.mk' N).domRestrict W) := by
    intro a b hab
    have h1 : QuotientGroup.mk' N ((a : Y) * (b : Y)⁻¹) = 1 := by
      have hab' : QuotientGroup.mk' N (a : Y) = QuotientGroup.mk' N (b : Y) := hab
      rw [map_mul, map_inv, hab', mul_inv_cancel]
    have h2 := hkey _ (W.mul_mem a.2 (W.inv_mem b.2)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hcard : Nat.card ↥W = Nat.card ↥E := by
    have h2 : Nat.card ((QuotientGroup.mk' N).domRestrict W).ker *
        Nat.card ((QuotientGroup.mk' N).domRestrict W).range = Nat.card ↥W := by
      rw [← Subgroup.index_ker]
      exact Subgroup.card_mul_index _
    rw [(MonoidHom.ker_eq_bot_iff _).2 hfinj, Subgroup.card_bot, one_mul,
      MonoidHom.domRestrict_range, hWmap] at h2
    exact h2.symm
  have hWel : IsElemAbelian p W := by
    have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
      intro a ha b hb
      have hae : QuotientGroup.mk' N a ∈ E := by
        rw [← hWmap]
        exact Subgroup.mem_map_of_mem _ ha
      have hbe : QuotientGroup.mk' N b ∈ E := by
        rw [← hWmap]
        exact Subgroup.mem_map_of_mem _ hb
      have hcN : ⁅a, b⁆ ∈ N := by
        rw [← hmk, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact isElemAbelian_commute hE hae hbe
      have hcW : ⁅a, b⁆ ∈ W := by
        rw [commutatorElement_def]
        exact W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)
      have hc1 : ⁅a, b⁆ ∈ W ⊓ N := ⟨hcW, hcN⟩
      rw [hWN, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc1
      exact hc1
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    have hxe : QuotientGroup.mk' N x ∈ E := by
      rw [← hWmap]
      exact Subgroup.mem_map_of_mem _ hx
    have hpN : x ^ p ∈ N := (hmk _).1 (by rw [map_pow]; exact hE.2 _ hxe)
    have hpW : x ^ p ∈ W ⊓ N := ⟨W.pow_mem hx p, hpN⟩
    rw [hWN, Subgroup.mem_bot] at hpW
    exact hpW
  exact ⟨W, hWel, hWmap, hcard⟩

private theorem natCard_eq_mul_natCard_map {p : ℕ} {K B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥B = Nat.card ↥(B ⊓ centModSubgroup p K) *
      Nat.card ↥((B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)) := by
  have hker : ∀ b : ↥(B.subgroupOf (Subgroup.normalizer (K : Set G))),
      b ∈ ((barAut p K).domRestrict (B.subgroupOf (Subgroup.normalizer (K : Set G)))).ker ↔
        (((b : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ centModSubgroup p K) := by
    intro b
    rw [MonoidHom.mem_ker]
    exact barAut_eq_one_iff (K := K) (b : ↥(Subgroup.normalizer (K : Set G)))
  have hkercard : Nat.card
      ((barAut p K).domRestrict (B.subgroupOf (Subgroup.normalizer (K : Set G)))).ker =
      Nat.card ↥(B ⊓ centModSubgroup p K) := by
    have hinj : Function.Injective
        ((Subgroup.normalizer (K : Set G)).subtype.comp
          (B.subgroupOf (Subgroup.normalizer (K : Set G))).subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    rw [← Subgroup.card_map_of_injective hinj]
    congr 2
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(Subgroup.mem_subgroupOf.1 b.2), (hker b).1 hb⟩
    · rintro ⟨hgB, hgc⟩
      have hgN : g ∈ Subgroup.normalizer (K : Set G) := (mem_centModSubgroup.1 hgc).1
      exact ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, (hker _).2 hgc, rfl⟩
  have hB'card : Nat.card ↥(B.subgroupOf (Subgroup.normalizer (K : Set G))) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have h1 : Nat.card
      ((barAut p K).domRestrict (B.subgroupOf (Subgroup.normalizer (K : Set G)))).ker *
      Nat.card
      ((barAut p K).domRestrict (B.subgroupOf (Subgroup.normalizer (K : Set G)))).range =
      Nat.card ↥(B.subgroupOf (Subgroup.normalizer (K : Set G))) := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  rw [MonoidHom.domRestrict_range, hkercard, hB'card] at h1
  exact h1.symm

private theorem barAut_image_facts {p : ℕ} {K B T : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hcomm : ⁅T, B⁆ = T) :
    IsPGroup 2 ((T.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)) ∧
    (B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) ≤
      Subgroup.normalizer
        (((T.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) :
          Subgroup (MulAut (PQuot p K))) : Set (MulAut (PQuot p K))) ∧
    ⁅(T.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K),
        (B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)⁆ =
      (T.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) := by
  have hT' : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (K : Set G))) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hcN : ⁅T.subgroupOf (Subgroup.normalizer (K : Set G)),
      B.subgroupOf (Subgroup.normalizer (K : Set G))⁆ =
      T.subgroupOf (Subgroup.normalizer (K : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (K : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hTK, inf_eq_left.2 hBN]
    exact hcomm
  refine ⟨hT'.map (barAut p K), ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
      have hconj : b * t * b⁻¹ ∈ T.subgroupOf (Subgroup.normalizer (K : Set G)) := by
        rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.1 (hBT hbB) (t : G)).1 ht'
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hconj
    · rintro ⟨s, hs, hseq⟩
      have hs' : (s : G) ∈ T := Subgroup.mem_subgroupOf.1 hs
      refine ⟨b⁻¹ * s * b, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have := (Subgroup.mem_normalizer_iff.1 (hBT (B.inv_mem hbB)) (s : G)).1 hs'
        simpa using this
      · rw [map_mul, map_mul, map_inv, hseq]
        group
  · rw [← Subgroup.map_commutator, hcN]

theorem chevRank3At_of {G : Type} [Group G] [Finite G] {p : ℕ} (hR : KDRank3 p)
    (h65 : I65At G p) : ChevRank3At G p := by
  unfold ChevRank3At
  intro hp hp2 X K B hX hK hChev hrank hBel hBN hBcard hout
  obtain ⟨b, hbB, hbC, hbI⟩ := hout
  have hZ : Subgroup.center (PQuot p K) = ⊥ :=
    h65 hp hp2 X K hX hK hChev ⟨b, hBN hbB, hBel.2 b hbB, hbC, hbI⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : IsSimpleGroup (PSimple p K) := hq.2
  let e : PSimple p K ≃* PQuot p K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hsimple : IsSimpleGroup (PQuot p K) := e.symm.isSimpleGroup
  have hchevQ : IsChevSimple p (PQuot p K) := by
    unfold IsChevSimple at hChev ⊢
    rcases hChev with h | h
    · exact Or.inl ((catalogIs_congr e).1 h)
    · exact Or.inr ((catalogIs_congr e).1 h)
  have hnonab : ∃ x y : PQuot p K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
    refine ⟨e x, e y, fun h => hxy (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hEel : IsElemAbelian p
      ((B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBel _) _
  have hEcard : Nat.card ↥((B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)) =
      p ^ 3 := by
    have h := natCard_eq_mul_natCard_map (p := p) hBN
    have hcpos : 0 < Nat.card ↥(B ⊓ centModSubgroup p K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hcpos
    rw [← h, hBcard, mul_comm]
  have hEinner : ¬ ((B.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot p K)) := by
    intro hle
    have hbN : (⟨b, hBN hbB⟩ : ↥(Subgroup.normalizer (K : Set G))) ∈
        B.subgroupOf (Subgroup.normalizer (K : Set G)) :=
      Subgroup.mem_subgroupOf.2 hbB
    exact hbI (inducesInnerMod_of_barAut_mem_inner
      (⟨b, hBN hbB⟩ : ↥(Subgroup.normalizer (K : Set G))) (hle (Subgroup.mem_map_of_mem _ hbN)))
  obtain ⟨⟨Pbar, hPbarel, hPbarcard⟩, hTpart⟩ :=
    hR (PQuot p K) hsimple hnonab hchevQ hrank _ hEel hEcard hEinner
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥K) := by
    have h := CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hp K
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  obtain ⟨W, hWel, -, hWcard⟩ := exists_elemAbelian_lift hp (GLAPPrimeCore p ↥K) hN Pbar hPbarel
  refine ⟨⟨W.map K.subtype, Subgroup.map_subtype_le W, hWel.map K.subtype, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hWcard, hPbarcard]
  intro T hT2 hTK hBT hcomm t ht
  obtain ⟨h1, h2, h3⟩ := barAut_image_facts hBN hTK hT2 hBT hcomm
  have hT0 := hTpart _ h1 h2 h3
  have hmem : barAut p K ⟨t, hTK ht⟩ ∈ (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (barAut p K) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
  rw [hT0, Subgroup.mem_bot] at hmem
  exact centMod_iff.2 ((barAut_eq_one_iff _).1 hmem)

end CFSG.LocalAnalysis.GLTheoremA
