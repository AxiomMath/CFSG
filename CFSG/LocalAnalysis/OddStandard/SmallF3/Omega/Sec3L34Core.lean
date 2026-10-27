module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem aux_card_comap_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (H : Subgroup Q') : Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
  have h := Subgroup.card_map_of_injective (K := H.comap e.toMonoidHom)
    (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_comap_eq_self_of_surjective e.surjective H] at h
  exact h.symm

private theorem map_oddCore_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (oddCore Q).map e.toMonoidHom = oddCore Q' := by
  unfold oddCore
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup_eq_sSup_image]
  congr 1
  ext N'
  constructor
  · rintro ⟨N, ⟨hNnorm, hNodd⟩, rfl⟩
    exact ⟨hNnorm.map e.toMonoidHom e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact hNodd⟩
  · intro hN'
    exact ⟨N'.comap e.toMonoidHom,
      ⟨hN'.1.comap e.toMonoidHom,
        by rw [aux_card_comap_mulEquiv e N']; exact hN'.2⟩,
      Subgroup.map_comap_eq_self_of_surjective e.surjective N'⟩

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem oddCore_le_center_of_pocket [Finite G] {X : Subgroup G} (hX : CFSG.IsQuasisimple X)
    {y : G} (hyX : y ∈ X) (hy : orderOf y = 2)
    (hG2 : oddCore ↥(Subgroup.centralizer
      ({(QuotientGroup.mk (⟨y, hyX⟩ : ↥X) : ↥X ⧸ oddCore ↥X)} : Set (↥X ⧸ oddCore ↥X))) = ⊥)
    {M K : Subgroup G} (hM : X ⊓ centralizer ({y} : Set G) ≤ M) (hKX : K ≤ X)
    (hKy : K ≤ centralizer ({y} : Set G)) (hsub : (K.subgroupOf M).IsSubnormal) :
    oddCore ↥K ≤ Subgroup.center ↥K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : ↥X := ⟨y, hyX⟩
  let N : Subgroup ↥X := oddCore ↥X
  let C : Subgroup ↥X := Subgroup.centralizer ({a} : Set ↥X)
  let K₁ : Subgroup ↥X := K.subgroupOf X
  let q : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  let Cbar : Subgroup (↥X ⧸ N) := Subgroup.centralizer ({q a} : Set (↥X ⧸ N))
  have hN_normal : N.Normal := CFSG.oddCore_normal (G := ↥X)
  have hG2' : oddCore ↥Cbar = ⊥ := hG2
  have ha : a * a = 1 := by
    apply Subtype.ext
    show y * y = 1
    rw [← pow_two, ← hy, pow_orderOf_eq_one]
  have hK₁C : K₁ ≤ C := by
    intro c hc
    change c ∈ Subgroup.centralizer ({a} : Set ↥X)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hKy hc) y (Set.mem_singleton y)
  have hCmap_eq : C.map X.subtype = X ⊓ centralizer ({y} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      change X.subtype c ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hc a (Set.mem_singleton a))
    · rintro ⟨hgX, hgc⟩
      refine ⟨⟨g, hgX⟩, ?_, rfl⟩
      change (⟨g, hgX⟩ : ↥X) ∈ Subgroup.centralizer ({a} : Set ↥X)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hgc y (Set.mem_singleton y)
  have hCM : C.map X.subtype ≤ M := hCmap_eq ▸ hM
  let fCM : ↥C →* ↥M :=
    { toFun := fun c => ⟨(c : G), hCM (Subgroup.mem_map_of_mem X.subtype c.2)⟩
      map_one' := by ext; rfl
      map_mul' := by intro x z; ext; rfl }
  have hsub_KC : (K₁.subgroupOf C).IsSubnormal := by
    have h1 : ((K.subgroupOf M).comap fCM).IsSubnormal := hsub.comap fCM
    have h_eq : (K.subgroupOf M).comap fCM = K₁.subgroupOf C := by
      ext c
      exact Iff.rfl
    rwa [h_eq] at h1
  have hTp : IsPGroup 2 (Subgroup.zpowers a) := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  haveI : Fact (IsPGroup 2 ↥(Subgroup.zpowers a)) := ⟨hTp⟩
  have hNodd : Odd (Nat.card N) := odd_card_oddCore' ↥X
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hNodd
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers a : Set ↥X) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcent_zpq : Subgroup.centralizer (Subgroup.zpowers (q a) : Set (↥X ⧸ N)) = Cbar := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcent_map : Subgroup.centralizer
        (((Subgroup.zpowers a).map (QuotientGroup.mk' N)) : Set (↥X ⧸ N)) =
      (Subgroup.centralizer (Subgroup.zpowers a : Set ↥X)).map (QuotientGroup.mk' N) :=
    CFSG.centralizer_map_quotient_eq_map_centralizer (G := ↥X) 2 (Subgroup.zpowers a) N
      hN_normal hcop
  rw [MonoidHom.map_zpowers, hcent_zp, hcent_zpq] at hcent_map
  have hCmap : C.map q = Cbar := hcent_map.symm
  let ψ : ↥C →* ↥Cbar :=
    { toFun := fun c => ⟨q c, by
        change q c ∈ Subgroup.centralizer ({q a} : Set (↥X ⧸ N))
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hc := Subgroup.mem_centralizer_iff.mp c.2 a (Set.mem_singleton a)
        simpa using congrArg (fun z : ↥X => q z) hc⟩
      map_one' := by ext; simp
      map_mul' := by intro x z; ext; simp }
  have hψ_surj : Function.Surjective ψ := by
    intro d
    have hd : (d : ↥X ⧸ N) ∈ C.map q := by
      rw [hCmap]
      exact d.2
    obtain ⟨c, hc, hcq⟩ := hd
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  have hψ_le : (oddCore ↥C).map ψ ≤ oddCore ↥Cbar :=
    CFSG.ComponentClassification.OddCore.maximal ↥Cbar ((oddCore ↥C).map ψ)
      (Subgroup.Normal.map (CFSG.oddCore_normal (G := ↥C)) ψ hψ_surj)
      ((odd_card_oddCore' ↥C).of_dvd_nat (Subgroup.card_map_dvd _ _))
  have hψ_bot : (oddCore ↥C).map ψ = ⊥ :=
    le_bot_iff.mp (hψ_le.trans (le_of_eq hG2'))
  have hOC_le_N : (oddCore ↥C).map C.subtype ≤ N := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hψc : ψ c = 1 := by
      have hm : ψ c ∈ (oddCore ↥C).map ψ := Subgroup.mem_map_of_mem ψ hc
      rw [hψ_bot] at hm
      simpa using hm
    have hq1 : q (c : ↥X) = 1 := by
      have := congrArg (fun z : ↥Cbar => (z : ↥X ⧸ N)) hψc
      simpa [ψ] using this
    rw [← QuotientGroup.ker_mk' N]
    exact MonoidHom.mem_ker.mpr hq1
  have hK₁_le_N : (oddCore ↥K₁).map K₁.subtype ≤ N :=
    (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hK₁C).2 hsub_KC)).trans hOC_le_N
  have hK_le_N : (oddCore ↥K).map K.subtype ≤ N.map X.subtype := by
    let e : ↥K ≃* ↥K₁ := (Subgroup.subgroupOfEquivOfLe hKX).symm
    have hcomp : K.subtype = X.subtype.comp (K₁.subtype.comp e.toMonoidHom) := by
      ext k
      rfl
    have hmap_e : (oddCore ↥K).map e.toMonoidHom = oddCore ↥K₁ := map_oddCore_mulEquiv e
    have h1 : (oddCore ↥K).map (X.subtype.comp (K₁.subtype.comp e.toMonoidHom)) =
        ((oddCore ↥K).map (K₁.subtype.comp e.toMonoidHom)).map X.subtype :=
      (Subgroup.map_map (oddCore ↥K) X.subtype (K₁.subtype.comp e.toMonoidHom)).symm
    have h2 : (oddCore ↥K).map (K₁.subtype.comp e.toMonoidHom) =
        ((oddCore ↥K).map e.toMonoidHom).map K₁.subtype :=
      (Subgroup.map_map (oddCore ↥K) K₁.subtype e.toMonoidHom).symm
    calc (oddCore ↥K).map K.subtype
        = (oddCore ↥K).map (X.subtype.comp (K₁.subtype.comp e.toMonoidHom)) := by rw [hcomp]
      _ = ((oddCore ↥K).map (K₁.subtype.comp e.toMonoidHom)).map X.subtype := h1
      _ = (((oddCore ↥K).map e.toMonoidHom).map K₁.subtype).map X.subtype := by rw [h2]
      _ = ((oddCore ↥K₁).map K₁.subtype).map X.subtype := by rw [hmap_e]
      _ ≤ N.map X.subtype := Subgroup.map_mono hK₁_le_N
  have hXopen : CFSG.Open.IsQuasisimple ↥X := ⟨hX.1.commutator_eq_top, hX.2.1⟩
  have hN_center : N ≤ Subgroup.center ↥X :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hXopen
  have hcent : (oddCore ↥K).map K.subtype ≤ Subgroup.centralizer (K : Set G) := by
    intro g hg
    obtain ⟨n, hnN, hneq⟩ := hK_le_N hg
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hn_center : n ∈ Subgroup.center ↥X := hN_center hnN
    have hcomm := Subgroup.mem_center_iff.mp hn_center (⟨j, hKX hj⟩ : ↥X)
    have hval := congrArg Subtype.val hcomm
    rw [← hneq]
    simpa using hval
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro j
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hcent ⟨k, hk, rfl⟩) (j : G) j.2

end CFSG.OddStandard.SmallF3.Omega
