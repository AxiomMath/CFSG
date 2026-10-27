module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarDichotomy

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open
open CFSG.EvenSporadicStandard.M23Std

@[expose] def NormQuot (A : Type*) [Group A] {G : Type*} [Group G] (N F : Subgroup G) : Prop :=
  ∃ ψ : ↥N →* A, Function.Surjective ψ ∧ ψ.ker = F.subgroupOf N

theorem NormQuot.of_equiv {A : Type*} [Group A] {G : Type*} [Group G] {N F : Subgroup G}
    [(F.subgroupOf N).Normal] (e : ↥N ⧸ F.subgroupOf N ≃* A) : NormQuot A N F := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (F.subgroupOf N)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ x ∈ F.subgroupOf N
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

theorem NormQuot.map {A : Type*} [Group A] {G X : Type*} [Group G] [Group X] {φ : X →* G}
    (hφ : Function.Injective φ) {N F : Subgroup X} (h : NormQuot A N F) :
    NormQuot A (N.map φ) (F.map φ) := by
  obtain ⟨ψ, hψ, hker⟩ := h
  let e : ↥N ≃* ↥(N.map φ) := Subgroup.equivMapOfInjective N φ hφ
  have he : ∀ x : ↥N, ((e x : ↥(N.map φ)) : G) = φ (x : X) := fun x => rfl
  refine ⟨ψ.comp e.symm.toMonoidHom, hψ.comp e.symm.surjective, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, he]
  show ψ (e.symm (e x)) = 1 ↔ _
  rw [MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_map_iff_mem hφ).symm

section Centralizer

variable {X : Type} [Group X] [Finite X] {z : X}

theorem centralizer_quotient_oddCore_equiv_gen {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hAe : Even (Nat.card A)) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (e : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × A) :
    Nonempty (centralizer ({(QuotientGroup.mk z : X ⧸ fusionOddCore X)} :
      Set (X ⧸ fusionOddCore X)) ≃* Multiplicative (ZMod 2) × A) := by
  classical
  set O := fusionOddCore X with hO
  have hOodd : Odd (Nat.card O) := natCard_fusionOddCore_odd X
  have hCbot : fusionOddCore (centralizer ({z} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_equiv e
      (fusionOddCore_prod_eq_bot_of_simple hAe)
  let ι : centralizer ({z} : Set X) →*
      centralizer ({(QuotientGroup.mk z : X ⧸ O)} : Set (X ⧸ O)) :=
    ((QuotientGroup.mk' O).comp (centralizer ({z} : Set X)).subtype).codRestrict _ (fun c => by
      rw [mem_centralizer_singleton_iff]
      show (QuotientGroup.mk (c : X) : X ⧸ O) * QuotientGroup.mk z =
        QuotientGroup.mk z * QuotientGroup.mk (c : X)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (mem_centralizer_singleton_iff.1 c.2))
  have hinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have hcO : (c : X) ∈ O := by
      have : ι c = 1 := hc
      have h2 : (QuotientGroup.mk (c : X) : X ⧸ O) = 1 := congrArg Subtype.val this
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hnormal : (O.comap (centralizer ({z} : Set X)).subtype).Normal :=
      (inferInstance : O.Normal).comap _
    have hodd : Odd (Nat.card (O.comap (centralizer ({z} : Set X)).subtype)) := by
      have hle : (O.comap (centralizer ({z} : Set X)).subtype).map
          (centralizer ({z} : Set X)).subtype ≤ O := by
        rintro _ ⟨m, hm, rfl⟩
        exact hm
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective (centralizer ({z} : Set X)).subtype_injective] at h1
      exact Odd.of_dvd_nat hOodd h1
    have hle := le_fusionOddCore_of_odd hodd
    rw [hCbot, le_bot_iff] at hle
    have hc' : c ∈ O.comap (centralizer ({z} : Set X)).subtype := hcO
    rw [hle, mem_bot] at hc'
    exact mem_bot.2 hc'
  have hsurj : Function.Surjective ι := by
    intro y
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx, hxy⟩ := CFSG.GorensteinWalter.exists_centralizer_lift_of_odd_kernel O hOodd
      ⟨hz1, by rw [pow_two]; exact hz2⟩ (y : X ⧸ O) y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨(MulEquiv.ofBijective ι ⟨hinj, hsurj⟩).symm.trans e⟩

end Centralizer

section Dichotomy

theorem xbar_dichotomy_of_solomon_gen {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hAe : Even (Nat.card A)) (hcenA : Subgroup.center A = ⊥) (hSol : SolomonGen A)
    {X : Type} [Group X] [Finite X] (hKX : CFSG.SectionRank.IsKGroupCat X) {z : X}
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (eX : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × A) :
    (∀ y : X ⧸ fusionOddCore X,
        y * (QuotientGroup.mk z : X ⧸ fusionOddCore X) = QuotientGroup.mk z * y) ∨
    ∃ N₁ N₂ : Subgroup (X ⧸ fusionOddCore X),
      Nonempty (N₁ ≃* A) ∧ Nonempty (N₂ ≃* A) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧ (QuotientGroup.mk z : X ⧸ fusionOddCore X) ∉ N₁ ⊔ N₂ ∧
      N₁.map (MulAut.conj (QuotientGroup.mk z : X ⧸ fusionOddCore X)).toMonoidHom = N₂ := by
  classical
  obtain ⟨e⟩ := centralizer_quotient_oddCore_equiv_gen hAe hz2 hz1 eX
  set O := fusionOddCore X with hO
  set zb : X ⧸ O := QuotientGroup.mk z with hzb
  have hOodd : Odd (Nat.card O) := natCard_fusionOddCore_odd X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzO : z ∉ O := by
    intro h
    have h1 : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O h
    rw [hz] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)
  have hzb1 : zb ≠ 1 := fun h => hzO ((QuotientGroup.eq_one_iff z).1 h)
  have hzb2' : zb ^ 2 = 1 := by
    rw [hzb, ← QuotientGroup.mk_pow, pow_two, hz2, QuotientGroup.mk_one]
  have hzb2 : orderOf zb = 2 := orderOf_eq_prime hzb2' hzb1
  by_cases hcen : ∀ y : X ⧸ O, y * zb = zb * y
  · exact Or.inl hcen
  · right
    have hbot : fusionOddCore (X ⧸ O) = ⊥ := fusionOddCore_quotient_oddCore_eq_bot X
    have hcentral : ∀ r : Multiplicative (ZMod 2) × A,
        (∀ s, s * r = r * s) → r.2 = 1 := by
      intro r hr
      have hr2 : r.2 ∈ Subgroup.center (A) :=
        mem_center_iff.2 fun b => by simpa using congrArg Prod.snd (hr (1, b))
      rw [hcenA, mem_bot] at hr2
      exact hr2
    have hzbR : zb ∈ centralizer ({zb} : Set (X ⧸ O)) := mem_centralizer_singleton_iff.2 rfl
    have hrz : ∀ s, s * e ⟨zb, hzbR⟩ = e ⟨zb, hzbR⟩ * s := by
      intro s
      obtain ⟨y, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
    have hrz1 : e ⟨zb, hzbR⟩ ≠ 1 := fun h => hzb1 (congrArg Subtype.val
      (e.injective (h.trans (map_one e).symm)))
    have hZ : fusionZStar (X ⧸ O) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have hg' : QuotientGroup.mk' (fusionOddCore (X ⧸ O)) g ∈
          Subgroup.center ((X ⧸ O) ⧸ fusionOddCore (X ⧸ O)) := hg
      have hgc : ∀ y : X ⧸ O, y * g = g * y := by
        intro y
        have h1 : (QuotientGroup.mk (y * g) : (X ⧸ O) ⧸ fusionOddCore (X ⧸ O)) =
            QuotientGroup.mk (g * y) := mem_center_iff.1 hg' (QuotientGroup.mk' _ y)
        have h2 : (y * g)⁻¹ * (g * y) ∈ fusionOddCore (X ⧸ O) := QuotientGroup.eq.1 h1
        rw [hbot, mem_bot, inv_mul_eq_one] at h2
        exact h2
      have hgR : g ∈ centralizer ({zb} : Set (X ⧸ O)) :=
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
        have h3 : (⟨g, hgR⟩ : centralizer ({zb} : Set (X ⧸ O))) = 1 :=
          e.injective (this.trans (map_one e).symm)
        exact mem_bot.2 (congrArg Subtype.val h3)
      · exfalso
        have hz1' : (e ⟨zb, hzbR⟩).1 ≠ 1 := fun h => hrz1 (Prod.ext h hz2')
        have h4 : e ⟨g, hgR⟩ = e ⟨zb, hzbR⟩ :=
          Prod.ext (eq_of_ne_one_zmod_two' _ _ hg1 hz1') (hg2.trans hz2'.symm)
        have h5 : g = zb := congrArg Subtype.val (e.injective h4)
        rw [h5] at hgc
        exact hcen hgc
    exact hSol (X ⧸ O) (hKX.quotient O) zb hzb2 hZ ⟨e⟩

end Dichotomy

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}
  (S : Setup L z t F L1 N)

include S

theorem centralizer_zbar_equiv_gen {A : Type} [Group A]
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) :
    Nonempty (centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) ≃*
      Multiplicative (ZMod 2) × A) := by
  classical
  set D : Subgroup G := normalizer (F : Set G) ⊓ L with hD
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := hA
  have hDL : D ≤ L := inf_le_right
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hDc : D ≤ centralizer (zpowers z : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute z d from S.one.z_comm d (hDL hd)) k).eq
  have hdisj : Disjoint (zpowers z) D := (disjoint_zpowers S.one hDL).symm
  let e := internalProdEquiv hDc hdisj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) S.one.z_ne_one
  have hcard2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have : IsCyclic (zpowers z) := isCyclic_of_prime_card hcard2
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp
  have : IsCyclic (Multiplicative (ZMod 2)) := isCyclic_of_prime_card hcardM
  let e₁ : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [hcard2, hcardM])
  let θ : ↥(zpowers z ⊔ D) →* Multiplicative (ZMod 2) × A :=
    (e₁.toMonoidHom.prodMap ψ₀).comp e.symm.toMonoidHom
  have hθsurj : Function.Surjective θ :=
    (e₁.surjective.prodMap hψ₀).comp e.symm.surjective
  have hθker : θ.ker = F.subgroupOf (zpowers z ⊔ D) := by
    ext q
    obtain ⟨⟨c, d⟩, rfl⟩ := e.surjective q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (e₁ (e.symm (e (c, d))).1, ψ₀ (e.symm (e (c, d))).2) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, Prod.mk_eq_one, map_eq_one_iff _ e₁.injective]
    show c = 1 ∧ ψ₀ d = 1 ↔ (c : G) * d ∈ F
    constructor
    · rintro ⟨hc, hd⟩
      have hd' : (d : G) ∈ F := by
        have : d ∈ ψ₀.ker := hd
        rw [hker₀] at this
        exact this
      rw [hc]
      simpa using hd'
    · intro h
      have hcL : (c : G) ∈ L := by
        have : (c : G) = (c * d) * (d : G)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (S.nd.F_le h) (Subgroup.inv_mem _ (hDL d.2))
      have hc1 : (c : G) = 1 :=
        Subgroup.disjoint_def.1 (disjoint_zpowers S.one le_rfl) hcL c.2
      have hc : c = 1 := Subtype.ext hc1
      refine ⟨hc, ?_⟩
      have hdF : (d : G) ∈ F := by
        rw [hc1, one_mul] at h
        exact h
      have : d ∈ ψ₀.ker := by
        rw [hker₀]
        exact hdF
      exact this
  have hker : S.PiQ.ker = θ.ker := by rw [S.ker_PiQ, hθker]
  exact ⟨(MulEquiv.subgroupCongr S.range_PiQ.symm).trans
    ((QuotientGroup.quotientKerEquivRange S.PiQ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)))⟩


theorem xbar_dichotomy_gen {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hAe : Even (Nat.card A)) (hcenA : Subgroup.center A = ⊥) (hSol : SolomonGen A)
    (hKX : CFSG.SectionRank.IsKGroupCat (Xbar L1))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) :
    (∀ y : Xbar L1 ⧸ fusionOddCore (Xbar L1), y * (QuotientGroup.mk
        (QuotientGroup.mk S.zX : Xbar L1) : Xbar L1 ⧸ fusionOddCore (Xbar L1)) =
      QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) * y) ∨
    ∃ N₁ N₂ : Subgroup (Xbar L1 ⧸ fusionOddCore (Xbar L1)),
      Nonempty (N₁ ≃* A) ∧ Nonempty (N₂ ≃* A) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧
      (QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) :
        Xbar L1 ⧸ fusionOddCore (Xbar L1)) ∉ N₁ ⊔ N₂ ∧
      N₁.map (MulAut.conj (QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) :
        Xbar L1 ⧸ fusionOddCore (Xbar L1))).toMonoidHom = N₂ := by
  obtain ⟨e⟩ := centralizer_zbar_equiv_gen S hA
  have hz2 : (QuotientGroup.mk S.zX : Xbar L1) * QuotientGroup.mk S.zX = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
    rw [this, QuotientGroup.mk_one]
  have hz1 : (QuotientGroup.mk S.zX : Xbar L1) ≠ 1 := by
    intro h
    have := S.orderOf_zbar
    rw [h, orderOf_one] at this
    omega
  exact xbar_dichotomy_of_solomon_gen hAe hcenA hSol hKX hz2 hz1 e

end Setup

end CFSG.EvenSporadicStandard.M22Std
