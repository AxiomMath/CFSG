module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Inputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelCentralizerSurjective

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

section OddCore

theorem odd_natCard_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem le_fusionOddCore {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

theorem fusionOddCore_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y]
    (e : X ≃* Y) (h : fusionOddCore Y = ⊥) : fusionOddCore X = ⊥ := by
  have hN : ((fusionOddCore X).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hodd : Odd (Nat.card ((fusionOddCore X).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact odd_natCard_fusionOddCore X
  have hle := le_fusionOddCore (N := (fusionOddCore X).map e.toMonoidHom) hodd
  rw [h, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have h1 : e.toMonoidHom x ∈ (fusionOddCore X).map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [hle, mem_bot] at h1
  exact mem_bot.2 ((MulEquiv.map_eq_one_iff e).1 h1)

theorem even_natCard_alternatingGroup_six : Even (Nat.card (alternatingGroup (Fin 6))) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp only [Fintype.card_fin]
  exact ⟨180, by decide⟩

theorem eq_of_ne_one_zmod_two :
    ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide

theorem natCard_comap_eq_card_ker_mul {E G : Type*} [Group E] [Group G] (f : E →* G)
    (hf : Function.Surjective f) (P : Subgroup G) [Finite E] :
    Nat.card (P.comap f) = Nat.card f.ker * Nat.card P := by
  let g : P.comap f →* P := (f.comp (P.comap f).subtype).codRestrict P (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ P
    rw [hx]
    exact y.2
  have hker : g.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change ((g x : P) = 1) ↔ f x = 1
    exact Subtype.ext_iff
  have h1 := Subgroup.card_ker_mul_card_of_surjective hg
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P.ker_le_comap f)).toEquiv] at h1
  exact h1.symm

theorem fusionOddCore_quotient_eq_bot (X : Type*) [Group X] [Finite X] :
    fusionOddCore (X ⧸ fusionOddCore X) = ⊥ := by
  let π : X →* X ⧸ fusionOddCore X := QuotientGroup.mk' (fusionOddCore X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = fusionOddCore X := QuotientGroup.ker_mk' _
  let N : Subgroup X := (fusionOddCore (X ⧸ fusionOddCore X)).comap π
  have hNnormal : N.Normal :=
    (inferInstance : (fusionOddCore (X ⧸ fusionOddCore X)).Normal).comap π
  have hcard : Nat.card N =
      Nat.card (fusionOddCore X) * Nat.card (fusionOddCore (X ⧸ fusionOddCore X)) := by
    rw [natCard_comap_eq_card_ker_mul π hπ, hker]
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (odd_natCard_fusionOddCore X).mul (odd_natCard_fusionOddCore _)
  have hle : N ≤ fusionOddCore X := le_fusionOddCore hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ x
  have hy : y ∈ fusionOddCore X := hle hx
  have : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [this]
  exact one_mem _

end OddCore

section Centralizer

variable {K : Type*} [Group K] [Finite K] {z : K} {D : Subgroup K}

theorem centralizer_quotient_equiv (hz : orderOf z = 2)
    (hcent : centralizer ({z} : Set K) = zpowers z ⊔ D) (hdisj : Disjoint (zpowers z) D)
    (hDc : fusionOddCoreOf D ≤ center K)
    (eD : D ⧸ fusionOddCore D ≃* alternatingGroup (Fin 6)) :
    Nonempty (centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) := by
  classical
  set O := fusionOddCore K with hO
  have hOodd : Odd (Nat.card O) := odd_natCard_fusionOddCore K
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; omega
  have hDle : D ≤ centralizer ({z} : Set K) := hcent ▸ le_sup_right
  have hcomm : ∀ c ∈ zpowers z, ∀ d ∈ D, c * d = d * c := by
    intro c hc d hd
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have h1 : d * z = z * d := mem_centralizer_singleton_iff.1 (hDle hd)
    exact (Commute.zpow_left (show Commute z d from h1.symm) k).eq
  have hcommS : ∀ (a : zpowers z) (b : D), Commute ((zpowers z).subtype a) (D.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let Φ : zpowers z × D →* K := (zpowers z).subtype.noncommCoprod D.subtype hcommS
  have hΦrange : Φ.range = centralizer ({z} : Set K) := by
    rw [hcent]
    change (MonoidHom.noncommCoprod (zpowers z).subtype D.subtype hcommS).range = _
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  let ψ : zpowers z × D →* K ⧸ O := (QuotientGroup.mk' O).comp Φ
  have hψ : ∀ p : zpowers z × D, ψ p = QuotientGroup.mk ((p.1 : K) * (p.2 : K)) := fun p => rfl
  have hrange : ψ.range = centralizer ({(QuotientGroup.mk z : K ⧸ O)} : Set (K ⧸ O)) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hp : Φ p ∈ centralizer ({z} : Set K) := hΦrange ▸ ⟨p, rfl⟩
      have h1 := mem_centralizer_singleton_iff.1 hp
      rw [hψ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk h1
    · intro hy
      obtain ⟨x, hx, hxy⟩ := CFSG.GorensteinWalter.exists_centralizer_lift_of_odd_kernel O hOodd
        ⟨hz1, hz2⟩ y hy
      rw [← hΦrange] at hx
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p, hxy⟩
  have hmemD : ∀ d : D, (d : K) ∈ O ↔ d ∈ fusionOddCore D := by
    intro d
    constructor
    · intro hd
      have : (O.comap D.subtype).Normal := (inferInstance : O.Normal).comap _
      have hodd : Odd (Nat.card (O.comap D.subtype)) := by
        have hle : (O.comap D.subtype).map D.subtype ≤ O := by
          rintro _ ⟨m, hm, rfl⟩
          exact hm
        have h1 := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective D.subtype_injective] at h1
        exact Odd.of_dvd_nat hOodd h1
      exact le_fusionOddCore hodd hd
    · intro hd
      have hMc : (fusionOddCore D).map D.subtype ≤ center K := hDc
      have : ((fusionOddCore D).map D.subtype).Normal := ⟨fun n hn g => by
        rw [mem_center_iff.1 (hMc hn) g, mul_inv_cancel_right]
        exact hn⟩
      have hodd : Odd (Nat.card ((fusionOddCore D).map D.subtype)) := by
        rw [Subgroup.card_map_of_injective D.subtype_injective]
        exact odd_natCard_fusionOddCore D
      exact le_fusionOddCore hodd ⟨d, hd, rfl⟩
  have hker_le : ∀ p : zpowers z × D, ψ p = 1 → p.1 = 1 ∧ p.2 ∈ fusionOddCore D := by
    rintro ⟨c, d⟩ hp
    have hp' : (QuotientGroup.mk ((c : K) * d) : K ⧸ O) = 1 := hp
    have hg : (c : K) * d ∈ O := (QuotientGroup.eq_one_iff _).1 hp'
    have hord : Odd (orderOf ((c : K) * d)) :=
      Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hg)
    obtain ⟨j, hj⟩ := hord
    have h1 : ((c : K) * d) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have hcd : Commute (c : K) d := hcomm c c.2 d d.2
    rw [hcd.mul_pow] at h1
    have h2 : (c : K) ^ (2 * j + 1) ∈ zpowers z := pow_mem c.2 _
    have h3 : (c : K) ^ (2 * j + 1) = ((d : K) ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h4 : (c : K) ^ (2 * j + 1) ∈ D := by rw [h3]; exact inv_mem (pow_mem d.2 _)
    have h5 : (c : K) ^ (2 * j + 1) = 1 := Subgroup.disjoint_def.1 hdisj h2 h4
    have hc2 : (c : K) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 c.2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
    have hc1 : (c : K) = 1 := by
      calc (c : K) = (c : K) ^ (2 * j + 1) := by
            rw [pow_succ, pow_mul, hc2, one_pow, one_mul]
        _ = 1 := h5
    refine ⟨Subtype.ext hc1, (hmemD d).1 ?_⟩
    rw [hc1, one_mul] at hg
    exact hg
  have hcard2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (zpowers z) := isCyclic_of_prime_card hcard2
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp
  have : IsCyclic (Multiplicative (ZMod 2)) := isCyclic_of_prime_card hcardM
  let e₁ : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [hcard2, hcardM])
  let θ : zpowers z × D →* Multiplicative (ZMod 2) × alternatingGroup (Fin 6) :=
    e₁.toMonoidHom.prodMap (eD.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore D)))
  have hθker : ∀ p : zpowers z × D, θ p = 1 ↔ p.1 = 1 ∧ p.2 ∈ fusionOddCore D := by
    intro p
    show (e₁ p.1, eD (QuotientGroup.mk p.2)) = 1 ↔ _
    rw [Prod.mk_eq_one, map_eq_one_iff _ e₁.injective, map_eq_one_iff _ eD.injective,
      QuotientGroup.eq_one_iff]
  have hθsurj : Function.Surjective θ :=
    e₁.surjective.prodMap (eD.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker = θ.ker := by
    ext p
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθker]
    constructor
    · exact hker_le p
    · rintro ⟨h1, h2⟩
      have h3 : (p.2 : K) ∈ O := (hmemD p.2).2 h2
      rw [hψ, h1, QuotientGroup.eq_one_iff]
      simpa using h3
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)))⟩

end Centralizer

@[expose] def Lemma64Conclusion (K : Type*) [Group K] (zb : K ⧸ fusionOddCore K) : Prop :=
  Nonempty (K ⧸ fusionOddCore K ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) ∨
    ∃ N₁ N₂ : Subgroup (K ⧸ fusionOddCore K),
      Nonempty (N₁ ≃* alternatingGroup (Fin 6)) ∧ Nonempty (N₂ ≃* alternatingGroup (Fin 6)) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧ zb ∉ N₁ ⊔ N₂ ∧ N₁.map (MulAut.conj zb).toMonoidHom = N₂

theorem lemma64_of_solomon (hSol : SolomonZ2A6) {K : Type} [Group K] [Finite K]
    (hKG : CFSG.SectionRank.IsKGroupCat K) {z : K} (hz : orderOf z = 2) {D : Subgroup K}
    (hcent : centralizer ({z} : Set K) = zpowers z ⊔ D)
    (hdisj : Disjoint (zpowers z) D) (hDc : fusionOddCoreOf D ≤ center K)
    (hD : Nonempty (D ⧸ fusionOddCore D ≃* alternatingGroup (Fin 6))) :
    Lemma64Conclusion K (QuotientGroup.mk z) := by
  unfold Lemma64Conclusion
  obtain ⟨eD⟩ := hD
  obtain ⟨e⟩ := centralizer_quotient_equiv hz hcent hdisj hDc eD
  set O := fusionOddCore K with hO
  set zb : K ⧸ O := QuotientGroup.mk z with hzb
  have hOodd : Odd (Nat.card O) := odd_natCard_fusionOddCore K
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzO : z ∉ O := by
    intro h
    have h1 : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O h
    rw [hz] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)
  have hzb1 : zb ≠ 1 := fun h => hzO ((QuotientGroup.eq_one_iff z).1 h)
  have hzb2' : zb ^ 2 = 1 := by rw [hzb, ← QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]
  have hzb2 : orderOf zb = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzb2' hzb1
  by_cases hcen : ∀ y : K ⧸ O, y * zb = zb * y
  · left
    have htop : centralizer ({zb} : Set (K ⧸ O)) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [mem_centralizer_singleton_iff]
      exact hcen y
    exact ⟨((topEquiv (G := K ⧸ O)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩
  · right
    have hbot : fusionOddCore (K ⧸ O) = ⊥ := fusionOddCore_quotient_eq_bot K
    have hcenA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hcentral : ∀ r : Multiplicative (ZMod 2) × alternatingGroup (Fin 6),
        (∀ s, s * r = r * s) → r.2 = 1 := by
      intro r hr
      have hr2 : r.2 ∈ Subgroup.center (alternatingGroup (Fin 6)) :=
        mem_center_iff.2 fun b => by simpa using congrArg Prod.snd (hr (1, b))
      rw [hcenA, mem_bot] at hr2
      exact hr2
    have hzbR : zb ∈ centralizer ({zb} : Set (K ⧸ O)) := mem_centralizer_singleton_iff.2 rfl
    have hrz : ∀ s, s * e ⟨zb, hzbR⟩ = e ⟨zb, hzbR⟩ * s := by
      intro s
      obtain ⟨y, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
    have hrz1 : e ⟨zb, hzbR⟩ ≠ 1 := fun h => hzb1 (congrArg Subtype.val
      (e.injective (h.trans (map_one e).symm)))
    have hZ : fusionZStar (K ⧸ O) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have hg' : QuotientGroup.mk' (fusionOddCore (K ⧸ O)) g ∈
          Subgroup.center ((K ⧸ O) ⧸ fusionOddCore (K ⧸ O)) := hg
      have hgc : ∀ y : K ⧸ O, y * g = g * y := by
        intro y
        have h1 : (QuotientGroup.mk (y * g) : (K ⧸ O) ⧸ fusionOddCore (K ⧸ O)) =
            QuotientGroup.mk (g * y) := mem_center_iff.1 hg' (QuotientGroup.mk' _ y)
        have h2 : (y * g)⁻¹ * (g * y) ∈ fusionOddCore (K ⧸ O) := QuotientGroup.eq.1 h1
        rw [hbot, mem_bot, inv_mul_eq_one] at h2
        exact h2
      have hgR : g ∈ centralizer ({zb} : Set (K ⧸ O)) :=
        mem_centralizer_singleton_iff.2 (hgc zb).symm
      have hrg : ∀ s, s * e ⟨g, hgR⟩ = e ⟨g, hgR⟩ * s := by
        intro s
        obtain ⟨y, rfl⟩ := e.surjective s
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (hgc y))
      have hg2 := hcentral _ hrg
      have hz2' := hcentral _ hrz
      by_cases hg1 : (e ⟨g, hgR⟩).1 = 1
      · have : e ⟨g, hgR⟩ = 1 := Prod.ext hg1 hg2
        have h3 : (⟨g, hgR⟩ : centralizer ({zb} : Set (K ⧸ O))) = 1 :=
          e.injective (this.trans (map_one e).symm)
        exact mem_bot.2 (congrArg Subtype.val h3)
      · exfalso
        have hz1' : (e ⟨zb, hzbR⟩).1 ≠ 1 := fun h => hrz1 (Prod.ext h hz2')
        have h4 : e ⟨g, hgR⟩ = e ⟨zb, hzbR⟩ :=
          Prod.ext (eq_of_ne_one_zmod_two _ _ hg1 hz1') (hg2.trans hz2'.symm)
        have h5 : g = zb := congrArg Subtype.val (e.injective h4)
        rw [h5] at hgc
        exact hcen hgc
    exact hSol (K ⧸ O) (hKG.quotient O) zb hzb2 hZ ⟨e⟩

end CFSG.EvenSporadicStandard.Fin76b
