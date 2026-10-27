module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Aut
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] {z r : G}

@[expose] def rElem (hzr : r ∈ centralizer ({z} : Set G)) : ↥(centralizer ({z} : Set G)) :=
  ⟨r, hzr⟩

@[expose] def rBar (hzr : r ∈ centralizer ({z} : Set G)) : OuterSection z :=
  QuotientGroup.mk (rElem hzr)

theorem sectionMk_mem_centralizer (hzr : r ∈ centralizer ({z} : Set G))
    (q : ↥(centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G))) :
    (QuotientGroup.mk (⟨q.1, (mem_inf.1 q.2).1⟩ : ↥(centralizer ({z} : Set G))) :
      OuterSection z) ∈ centralizer ({rBar hzr} : Set (OuterSection z)) := by
  rw [mem_centralizer_singleton_iff]
  have hq : q.1 * r = r * q.1 := mem_centralizer_singleton_iff.1 (mem_inf.1 q.2).2
  change (QuotientGroup.mk _ : OuterSection z) * QuotientGroup.mk (rElem hzr) =
    QuotientGroup.mk (rElem hzr) * QuotientGroup.mk _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hq

@[expose] noncomputable def sectionHom (hzr : r ∈ centralizer ({z} : Set G)) :
    ↥(centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G)) →*
      ↥(centralizer ({rBar hzr} : Set (OuterSection z))) :=
  ((QuotientGroup.mk' (vSub z)).comp
    (Subgroup.inclusion (inf_le_left : centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G) ≤
      centralizer ({z} : Set G)))).codRestrict _ (sectionMk_mem_centralizer hzr)

theorem sectionHom_apply (hzr : r ∈ centralizer ({z} : Set G))
    (q : ↥(centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G))) :
    ((sectionHom hzr q : ↥(centralizer ({rBar hzr} : Set (OuterSection z)))) : OuterSection z) =
      QuotientGroup.mk (⟨q.1, (mem_inf.1 q.2).1⟩ : ↥(centralizer ({z} : Set G))) := rfl

theorem sectionHom_eq_one_iff (hzr : r ∈ centralizer ({z} : Set G))
    (q : ↥(centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G))) :
    sectionHom hzr q = 1 ↔ q.1 ∈ zpowers z := by
  rw [← Subtype.coe_inj, sectionHom_apply, Subgroup.coe_one, ← QuotientGroup.mk_one,
    QuotientGroup.eq, mul_one, inv_mem_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    exact mem_zpowers_iff.2 ⟨k, by simpa [vElem] using congrArg Subtype.val hk⟩
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [vElem] using hk)⟩

theorem sectionHom_surjective [Finite G] (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzr : r ∈ centralizer ({z} : Set G)) (hr5 : orderOf r = 5) :
    Function.Surjective (sectionHom hzr) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN : ¬ 5 ∣ Nat.card (vSub z) := by
    rw [card_vSub hz2 hz1]
    norm_num
  set Q : Subgroup ↥(centralizer ({z} : Set G)) := zpowers (rElem hzr) with hQ
  have hQp : IsPGroup 5 Q := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hQ, Nat.card_zpowers, show orderOf (rElem hzr) = 5 from
      (Subgroup.orderOf_mk r hzr).trans hr5]
    norm_num
  have hlift := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN hQp
  intro y
  have hy : (y : OuterSection z) ∈ centralizer
      ((Q.map (QuotientGroup.mk' (vSub z)) : Subgroup (OuterSection z)) :
        Set (OuterSection z)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hyr : (y : OuterSection z) * rBar hzr = rBar hzr * y :=
      mem_centralizer_singleton_iff.1 y.2
    have h2 : (y : OuterSection z) * (QuotientGroup.mk' (vSub z) (rElem hzr)) ^ k =
        (QuotientGroup.mk' (vSub z) (rElem hzr)) ^ k * y :=
      ((Commute.zpow_right (show Commute (y : OuterSection z) (rBar hzr) from hyr) k).eq)
    simpa [map_zpow] using h2.symm
  rw [hlift] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hcr : (c : G) * r = r * c := by
    have := mem_centralizer_iff.1 hc (rElem hzr) (mem_zpowers _)
    exact congrArg Subtype.val this.symm
  refine ⟨⟨c.1, mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2 hcr⟩⟩, ?_⟩
  apply Subtype.ext
  rw [sectionHom_apply]
  exact hcy

theorem exists_psi_of_section [Finite G] (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzr : r ∈ centralizer ({z} : Set G)) (hr5 : orderOf r = 5)
    (e : ↥(centralizer ({rBar hzr} : Set (OuterSection z))) ≃*
      Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    ∃ ψ : ↥(centralizer ({z} : Set G) ⊓ centralizer ({r} : Set G)) →*
        Multiplicative (ZMod 5) × Equiv.Perm (Fin 5),
      Function.Surjective ψ ∧ ∀ q, ψ q = 1 ↔ q.1 ∈ zpowers z :=
  ⟨e.toMonoidHom.comp (sectionHom hzr),
    e.surjective.comp (sectionHom_surjective hz2 hz1 hzr hr5), fun q => by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        sectionHom_eq_one_iff]⟩

@[expose] def centralizerSingletonEquiv {X Y : Type*} [Group X] [Group Y] (θ : X ≃* Y) (x : X) :
    ↥(centralizer ({x} : Set X)) ≃* ↥(centralizer ({θ x} : Set Y)) where
  toFun c := ⟨θ c.1, by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg θ (mem_centralizer_singleton_iff.1 c.2)⟩
  invFun c := ⟨θ.symm c.1, by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 c.2
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h⟩
  left_inv c := Subtype.ext (θ.symm_apply_apply _)
  right_inv c := Subtype.ext (θ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul θ _ _)

theorem orderOf_sectionMk (hz2 : z * z = 1) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {g : G}
    (hg : g ∈ centralizer ({z} : Set G)) (hgp : orderOf g = p) :
    orderOf (QuotientGroup.mk (⟨g, hg⟩ : ↥(centralizer ({z} : Set G))) : OuterSection z) = p := by
  have hpow : (QuotientGroup.mk (⟨g, hg⟩ : ↥(centralizer ({z} : Set G))) : OuterSection z) ^ p =
      1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hgpow : g ^ p = 1 := hgp ▸ pow_orderOf_eq_one g
    have : (⟨g, hg⟩ : ↥(centralizer ({z} : Set G))) ^ p = 1 := Subtype.ext (by simpa using hgpow)
    rw [this]
    exact one_mem _
  refine orderOf_eq_prime hpow ?_
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
  have hgz : g ∈ zpowers z := mem_zpowers_iff.2 ⟨k, by simpa [vElem] using congrArg Subtype.val hk⟩
  have hsq : g * g = 1 := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hgz
    rcases zpow_eq_one_or_self hz2 j with h | h <;> rw [h]
    · simp
    · exact hz2
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rw [hgp] at this
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)

end CFSG.EvenSporadicStandard.HSStd

