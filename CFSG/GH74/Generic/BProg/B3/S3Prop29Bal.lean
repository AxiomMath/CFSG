module

public import CFSG.GH74.Generic.BProg.B3.LocBalL3
public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Basic
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Prop29Bal

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement

section Rho

variable {X : Type} [Group X]

theorem rhoL_eq_conj {L : Subgroup X} (m : ↥(normalizer (L : Set X))) (hm : (m : X) ∈ L) :
    rhoL L m = MulAut.conj (QuotientGroup.mk (⟨(m : X), hm⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  show (QuotientGroup.mk' (center ↥L)) (((CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L m)
    l : ↥L)) = _
  rw [MulAut.conj_apply]
  rfl

theorem rhoL_eq_one_of_centralizes {L : Subgroup X} (m : ↥(normalizer (L : Set X)))
    (hm : ∀ l ∈ L, (m : X) * l = l * (m : X)) : rhoL L m = 1 := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  show (QuotientGroup.mk' (center ↥L)) (((CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L m)
    l : ↥L)) = QuotientGroup.mk l
  have : ((CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L m) l : ↥L) = l := by
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply, hm l l.2]
    group
  rw [this]
  rfl

theorem rhoL_mul_of_centralizes {L : Subgroup X} (m m' : ↥(normalizer (L : Set X)))
    (hm' : ∀ l ∈ L, (m' : X) * l = l * (m' : X)) : rhoL L (m * m') = rhoL L m := by
  rw [map_mul, rhoL_eq_one_of_centralizes m' hm', mul_one]

end Rho

section Transport

variable {X Kt : Type} [Group X] [Group Kt]

theorem locBal32_of_equiv' (L : Subgroup X) (e : Kt ≃* ↥L)
    (φ : (Kt ⧸ center Kt) ≃* (↥L ⧸ center ↥L))
    (hφ : ∀ k : Kt, φ (QuotientGroup.mk k) = QuotientGroup.mk (e k)) {Ab : Subgroup Kt}
    (h : ∀ B₀ : Subgroup (MulAut (Kt ⧸ center Kt)),
      B₀ ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
        (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)) →
      IsLocBal32 (Kt ⧸ center Kt) B₀)
    {B : Subgroup X}
    (hB : ∀ m : ↥(normalizer (L : Set X)), (m : X) ∈ B → ∃ k ∈ Ab,
      rhoL L m = MulAut.conj (φ (QuotientGroup.mk k))) :
    IsLocBal32 (↥L ⧸ center ↥L) ((B.subgroupOf (normalizer (L : Set X))).map (rhoL L)) := by
  classical
  have _hφ := hφ
  set B₁ : Subgroup (MulAut (↥L ⧸ center ↥L)) :=
    (B.subgroupOf (normalizer (L : Set X))).map (rhoL L) with hB₁
  set B₀ : Subgroup (MulAut (Kt ⧸ center Kt)) :=
    B₁.map (MulAut.congr φ.symm).toMonoidHom with hB₀
  have hB₀le : B₀ ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
      (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)) := by
    rintro _ ⟨t, ⟨m, hm, rfl⟩, rfl⟩
    have hmB : (m : X) ∈ B := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨k, hk, hkm⟩ := hB m hmB
    refine ⟨QuotientGroup.mk' (center Kt) k, ⟨k, hk, rfl⟩, ?_⟩
    show MulAut.conj (QuotientGroup.mk' (center Kt) k) = (MulAut.congr φ.symm) (rhoL L m)
    rw [hkm, LocBalSL4Basic.congr_conj, MulEquiv.symm_apply_apply]
    rfl
  have h2 := isLocBal32_of_mulEquiv φ (h B₀ hB₀le)
  have hBB : B₀.map (MulAut.congr φ).toMonoidHom = B₁ := by
    rw [hB₀, Subgroup.map_map]
    have : (MulAut.congr φ).toMonoidHom.comp (MulAut.congr φ.symm).toMonoidHom =
        MonoidHom.id _ := by
      ext y z
      simp [MulAut.congr_apply]
    rw [this, Subgroup.map_id]
  rwa [hBB] at h2

end Transport

section Canonical

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem exists_canonical_equiv (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    ∃ e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(PumpCalc.bar x K),
      ∀ (k : G) (hk : k ∈ K), ((e (QuotientGroup.mk ⟨k, hk⟩) : ↥(PumpCalc.bar x K)) :
        barQ ↥(centralizer ({x} : Set G))) = barMk ↥(centralizer ({x} : Set G)) ⟨k, hK.1 hk⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let f : ↥K →* ↥(PumpCalc.bar x K) :=
    ((barMk ↥C).comp (Subgroup.inclusion hKC)).codRestrict (PumpCalc.bar x K)
      (fun k => ⟨⟨(k : G), hKC k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩)
  have hfs : Function.Surjective f := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩
  have hker : f.ker = pPrimeCore 2 ↥K := by
    have h0 : f.ker = ((barMk ↥C).comp (Subgroup.inclusion hKC)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [h0]
    have hsub : (K.subgroupOf C).IsSubnormal := B1.isSubnormal_of_isPCompIn hK
    have hker2 := ker_restrict_eq_pPrimeCore hsub
    let ε : ↥K ≃* ↥(K.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hKC).symm
    ext k
    constructor
    · intro hk
      have hk' : ε k ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥C)).comp (K.subgroupOf C).subtype).ker := by
        rw [MonoidHom.mem_ker] at hk ⊢
        exact hk
      rw [hker2, ← pPrimeCore_map_iso 2 ε] at hk'
      obtain ⟨k', hk', hk'e⟩ := hk'
      have : k' = k := ε.injective hk'e
      rwa [this] at hk'
    · intro hk
      have hmem : ε k ∈ pPrimeCore 2 ↥(K.subgroupOf C) := by
        rw [← pPrimeCore_map_iso 2 ε]
        exact ⟨k, hk, rfl⟩
      rw [← hker2] at hmem
      rw [MonoidHom.mem_ker] at hmem ⊢
      exact hmem
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun k hk => rfl⟩

end Canonical

section Shape3

theorem locBal32_of_le_range {Kt : Type} [Group Kt] [Finite Kt] (h3 : QShape3 Kt)
    (hZ : ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) {Ab : Subgroup Kt}
    (hAb : CFSG.IsElementaryAbelian 2 ↥Ab) (B₀ : Subgroup (MulAut (Kt ⧸ center Kt)))
    (hB₀ : B₀ ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
      (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt))) :
    IsLocBal32 (Kt ⧸ center Kt) B₀ := by
  classical
  have hinj : Function.Injective (QuotientGroup.mk' (center Kt)) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    exact hZ k (Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff k).1 hk))
  let φ₀ : Kt ≃* (Kt ⧸ center Kt) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center Kt)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let f : Kt →* MulAut (Kt ⧸ center Kt) :=
    (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)).comp (QuotientGroup.mk' (center Kt))
  set Bk : Subgroup Kt := Ab ⊓ B₀.comap f with hBk
  have hsq : ∀ b ∈ Bk, b * b = 1 := by
    intro b hb
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ab) b (Subgroup.mem_inf.1 hb).1
    rwa [sq] at h2
  have h1 := locBal32_L3_gen h3 Bk hsq
  have h2 := isLocBal32_of_mulEquiv φ₀ h1
  have hcomp : (MulAut.congr φ₀).toMonoidHom.comp (MulAut.conj : Kt →* MulAut Kt) = f := by
    ext k y
    simp [f, φ₀]
    rfl
  have hmap : (Bk.map (MulAut.conj : Kt →* MulAut Kt)).map (MulAut.congr φ₀).toMonoidHom = B₀ := by
    rw [Subgroup.map_map, hcomp]
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (Subgroup.mem_inf.1 hb).2
    · intro hz
      have hz' := hB₀ hz
      rw [Subgroup.map_map] at hz'
      obtain ⟨a, ha, haz⟩ := hz'
      refine ⟨a, Subgroup.mem_inf.2 ⟨ha, ?_⟩, haz⟩
      show f a ∈ B₀
      have : f a = z := haz
      rw [this]
      exact hz
  rwa [hmap] at h2

end Shape3

end S3Prop29Bal

end CFSG.GH74.Generic.BProg.B3
