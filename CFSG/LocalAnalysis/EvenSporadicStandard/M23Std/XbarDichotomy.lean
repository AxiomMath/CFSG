module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarWreath
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelCentralizerSurjective
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.SolomonA7Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open

section OddCoreQuotient

theorem natCard_comap_of_surjective {E H : Type*} [Group E] [Group H] (f : E →* H)
    (hf : Function.Surjective f) (P : Subgroup H) [Finite E] :
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

theorem fusionOddCore_quotient_oddCore_eq_bot (X : Type*) [Group X] [Finite X] :
    fusionOddCore (X ⧸ fusionOddCore X) = ⊥ := by
  let π : X →* X ⧸ fusionOddCore X := QuotientGroup.mk' (fusionOddCore X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = fusionOddCore X := QuotientGroup.ker_mk' _
  let N : Subgroup X := (fusionOddCore (X ⧸ fusionOddCore X)).comap π
  have hNnormal : N.Normal :=
    (inferInstance : (fusionOddCore (X ⧸ fusionOddCore X)).Normal).comap π
  have hcard : Nat.card N =
      Nat.card (fusionOddCore X) * Nat.card (fusionOddCore (X ⧸ fusionOddCore X)) := by
    rw [natCard_comap_of_surjective π hπ, hker]
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (natCard_fusionOddCore_odd X).mul (natCard_fusionOddCore_odd _)
  have hle : N ≤ fusionOddCore X := le_fusionOddCore_of_odd hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ x
  have hy : y ∈ fusionOddCore X := hle hx
  have : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [this]
  exact one_mem _

end OddCoreQuotient

section Centralizer

variable {X : Type} [Group X] [Finite X] {z : X}

theorem centralizer_quotient_oddCore_equiv (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (e : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) :
    Nonempty (centralizer ({(QuotientGroup.mk z : X ⧸ fusionOddCore X)} :
      Set (X ⧸ fusionOddCore X)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) := by
  classical
  set O := fusionOddCore X with hO
  have hOodd : Odd (Nat.card O) := natCard_fusionOddCore_odd X
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hCbot : fusionOddCore (centralizer ({z} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_equiv e
      (fusionOddCore_prod_eq_bot_of_simple even_natCard_alternatingGroup_seven)
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

theorem eq_of_ne_one_zmod_two' :
    ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide

theorem xbar_dichotomy_of_solomon (hSol : SolomonZ2A7) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.SectionRank.IsKGroupCat X) {z : X} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (eX : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) :
    (∀ y : X ⧸ fusionOddCore X,
        y * (QuotientGroup.mk z : X ⧸ fusionOddCore X) = QuotientGroup.mk z * y) ∨
    ∃ N₁ N₂ : Subgroup (X ⧸ fusionOddCore X),
      Nonempty (N₁ ≃* alternatingGroup (Fin 7)) ∧ Nonempty (N₂ ≃* alternatingGroup (Fin 7)) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧ (QuotientGroup.mk z : X ⧸ fusionOddCore X) ∉ N₁ ⊔ N₂ ∧
      N₁.map (MulAut.conj (QuotientGroup.mk z : X ⧸ fusionOddCore X)).toMonoidHom = N₂ := by
  classical
  obtain ⟨e⟩ := centralizer_quotient_oddCore_equiv hz2 hz1 eX
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
    have hcenA : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hcentral : ∀ r : Multiplicative (ZMod 2) × alternatingGroup (Fin 7),
        (∀ s, s * r = r * s) → r.2 = 1 := by
      intro r hr
      have hr2 : r.2 ∈ Subgroup.center (alternatingGroup (Fin 7)) :=
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

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}
  (S : Setup L z t F L1 N)

include S

theorem xbar_dichotomy (hSol : SolomonZ2A7) (hKX : CFSG.SectionRank.IsKGroupCat (Xbar L1))
    (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F) :
    (∀ y : Xbar L1 ⧸ fusionOddCore (Xbar L1), y * (QuotientGroup.mk
        (QuotientGroup.mk S.zX : Xbar L1) : Xbar L1 ⧸ fusionOddCore (Xbar L1)) =
      QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) * y) ∨
    ∃ N₁ N₂ : Subgroup (Xbar L1 ⧸ fusionOddCore (Xbar L1)),
      Nonempty (N₁ ≃* alternatingGroup (Fin 7)) ∧ Nonempty (N₂ ≃* alternatingGroup (Fin 7)) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧
      (QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) :
        Xbar L1 ⧸ fusionOddCore (Xbar L1)) ∉ N₁ ⊔ N₂ ∧
      N₁.map (MulAut.conj (QuotientGroup.mk (QuotientGroup.mk S.zX : Xbar L1) :
        Xbar L1 ⧸ fusionOddCore (Xbar L1))).toMonoidHom = N₂ := by
  obtain ⟨e⟩ := S.centralizer_zbar_equiv hA7
  have hz2 : (QuotientGroup.mk S.zX : Xbar L1) * QuotientGroup.mk S.zX = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
    rw [this, QuotientGroup.mk_one]
  have hz1 : (QuotientGroup.mk S.zX : Xbar L1) ≠ 1 := by
    intro h
    have := S.orderOf_zbar
    rw [h, orderOf_one] at this
    omega
  exact xbar_dichotomy_of_solomon hSol hKX hz2 hz1 e

end Setup

end CFSG.EvenSporadicStandard.M23Std
