module

public import CFSG.GH74.Generic.BProg.B3.S1Split
public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Basic
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Lemma282Bal

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement

section Transport

variable {X Kt : Type} [Group X] [Group Kt]

theorem rhoL_eq_conj {L : Subgroup X} (m : ↥(normalizer (L : Set X))) (hm : (m : X) ∈ L) :
    rhoL L m = MulAut.conj (QuotientGroup.mk (⟨(m : X), hm⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  show (QuotientGroup.mk' (center ↥L)) (((CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L m)
    l : ↥L)) = _
  rw [MulAut.conj_apply]
  rfl

theorem locBal32_of_equiv (L : Subgroup X) (e : Kt ≃* ↥L) {Ab : Subgroup Kt}
    (h : ∀ B₀ : Subgroup (MulAut (Kt ⧸ center Kt)),
      B₀ ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
        (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)) →
      IsLocBal32 (Kt ⧸ center Kt) B₀)
    {B : Subgroup X} (hBL : B ≤ L) (hBAb : ∀ b ∈ B, ∃ k ∈ Ab, ((e k : ↥L) : X) = b) :
    IsLocBal32 (↥L ⧸ center ↥L) ((B.subgroupOf (normalizer (L : Set X))).map (rhoL L)) := by
  classical
  let φ : Kt ⧸ center Kt ≃* ↥L ⧸ center ↥L :=
    QuotientGroup.congr (center Kt) (center ↥L) e
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)
  set B₁ : Subgroup (MulAut (↥L ⧸ center ↥L)) :=
    (B.subgroupOf (normalizer (L : Set X))).map (rhoL L) with hB₁
  set B₀ : Subgroup (MulAut (Kt ⧸ center Kt)) :=
    B₁.map (MulAut.congr φ.symm).toMonoidHom with hB₀
  have hB₀le : B₀ ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
      (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)) := by
    rintro _ ⟨t, ⟨m, hm, rfl⟩, rfl⟩
    have hmB : (m : X) ∈ B := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨k, hk, hkb⟩ := hBAb (m : X) hmB
    have hmL : (m : X) ∈ L := hBL hmB
    have hek : e k = ⟨(m : X), hmL⟩ := Subtype.ext hkb
    refine ⟨QuotientGroup.mk' (center Kt) k, ⟨k, hk, rfl⟩, ?_⟩
    have h1 : rhoL L m = MulAut.conj (φ (QuotientGroup.mk' (center Kt) k)) := by
      rw [rhoL_eq_conj m hmL]
      congr 1
      show _ = QuotientGroup.mk (e k)
      rw [hek]
    show MulAut.conj (QuotientGroup.mk' (center Kt) k) = (MulAut.congr φ.symm) (rhoL L m)
    rw [h1, LocBalSL4Basic.congr_conj, MulEquiv.symm_apply_apply]
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
    apply le_antisymm
    · exact S1Split.ker_fK_le x hKC
    · intro k hk
      have hsub : (K.subgroupOf C).IsSubnormal := B1.isSubnormal_of_isPCompIn hK
      have hker2 := ker_restrict_eq_pPrimeCore hsub
      let ε : ↥K ≃* ↥(K.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hKC).symm
      have hmem : ε k ∈ pPrimeCore 2 ↥(K.subgroupOf C) := by
        rw [← pPrimeCore_map_iso 2 ε]
        exact ⟨k, hk, rfl⟩
      rw [← hker2] at hmem
      exact hmem
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun k hk => rfl⟩

end Canonical

section Bar

variable {G : Type} [Group G] [Finite G]

@[expose] def LocBalAll (Kt : Type) [Group Kt] : Prop :=
  ∀ {Ab : Subgroup Kt}, CFSG.IsElementaryAbelian 2 ↥Ab → Nat.card ↥Ab = 8 →
    ∀ B : Subgroup (MulAut (Kt ⧸ center Kt)),
      B ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
        (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt)) →
      IsLocBal32 (Kt ⧸ center Kt) B

theorem locBal32_bar {x : G} {K A B' : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hAK : A ≤ K)
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) (hB'A : B' ≤ A)
    (hLoc : LocBalAll (↥K ⧸ pPrimeCore 2 ↥K)) :
    IsLocBal32 (↥(PumpCalc.bar x K) ⧸ center ↥(PumpCalc.bar x K))
      (((PumpCalc.bar x B').subgroupOf
        (normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) :
          Set (barQ ↥(centralizer ({x} : Set G)))))).map (rhoL (PumpCalc.bar x K))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨e, he⟩ := exists_canonical_equiv hK
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  let ψ : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  set AK : Subgroup ↥K := A.subgroupOf K with hAKdef
  set Ab : Subgroup (↥K ⧸ N) := AK.map ψ with hAb
  have : CFSG.IsElementaryAbelian 2 ↥A := hAe
  have : CFSG.IsElementaryAbelian 2 ↥AK := IsElementaryAbelian.subgroupOf hAK
  have hAbe : CFSG.IsElementaryAbelian 2 ↥Ab := IsElementaryAbelian.map ψ
  have hsqAK : ∀ c ∈ AK, c * c = 1 := fun c hc => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (c : G)
      (Subgroup.mem_subgroupOf.mp hc)
    exact Subtype.ext (by rw [← pow_two]; exact h1)
  have hinjOn : Set.InjOn ψ (AK : Set ↥K) := by
    intro a ha b hb hab
    have hab' : a⁻¹ * b ∈ N := by
      have : ψ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hsq := hsqAK (a⁻¹ * b) (AK.mul_mem (AK.inv_mem ha) hb)
    exact inv_mul_eq_one.1 (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore hsq hab')
  have hAb8 : Nat.card ↥Ab = 8 := by
    have h1 : Nat.card ↥Ab = Nat.card ↥AK := by
      exact Nat.card_image_of_injOn hinjOn
    have h2 : Nat.card ↥AK = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
    rw [h1, h2, hA8]
  refine locBal32_of_equiv (PumpCalc.bar x K) e (Ab := Ab)
    (fun B₀ hB₀ => hLoc hAbe hAb8 B₀ hB₀) ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Subgroup.mem_subgroupOf.2 (hAK (hB'A (Subgroup.mem_subgroupOf.1 hz))), rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzB : (z : G) ∈ B' := Subgroup.mem_subgroupOf.1 hz
    have hzK : (z : G) ∈ K := hAK (hB'A hzB)
    refine ⟨ψ ⟨(z : G), hzK⟩, ⟨⟨(z : G), hzK⟩, Subgroup.mem_subgroupOf.2 (hB'A hzB), rfl⟩, ?_⟩
    exact he (z : G) hzK

end Bar

end S1Lemma282Bal

end CFSG.GH74.Generic.BProg.B3
