module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FLift
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaZ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def isU9two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 8 q => q.card = 2 | _ => False

@[expose] def I141U9Lemma : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K J : Subgroup Γ) (x a : Γ),
    IsCatalogGroup (PSimple 3 K) → x ^ 3 = 1 → a ^ 3 = 1 → x * a = a * x → x ∉ Subgroup.zpowers a →
    S10.InnDiagOn 3 (Subgroup.zpowers x) K → S10.InnDiagOn 3 (Subgroup.zpowers a) K →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    catalogIs (PSimple 3 J) S9.isU3eight → Subgroup.center (PQuot 3 J) ≠ ⊥ → S10.FieldOn 3 a J →
    catalogIs (PSimple 3 K) isU9two

@[expose] def I141U9Rank : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    catalogIs (H ⧸ Subgroup.center H) isU9two →
    ∃ M : Subgroup H, CFSG.Open.IsTwoLocal M ∧ 5 ≤ CFSG.Open.pRank 3 M

theorem isSimpleGroup_of_mulEquiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : IsSimpleGroup A) : IsSimpleGroup B := by
  haveI : Nontrivial A := hA.toNontrivial
  haveI : Nontrivial B := e.symm.surjective.nontrivial
  refine { eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  rcases hA.eq_bot_or_eq_top_of_normal (H.comap e.toMonoidHom) with h | h
  · left
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective H, h,
      Subgroup.map_bot]
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective H, h,
      Subgroup.map_top_of_surjective _ e.surjective]

theorem exists_noncomm_of_quasisimple {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
  by_contra hcon
  have hcon' : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  obtain ⟨hcomm, hsimp⟩ := hq
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimp.toNontrivial
  have hcomm' : ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q) := hcomm
  have hbot : ⁅(⊤ : Subgroup (Q ⧸ Subgroup.center Q)), (⊤ : Subgroup (Q ⧸ Subgroup.center Q))⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    exact Subgroup.mem_centralizer_iff.2 (fun h _ => hcon' h a)
  have hmap : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ := by
    have hc := Subgroup.map_commutator (QuotientGroup.mk' (Subgroup.center Q)) (H₁ := (⊤ : Subgroup Q)) (H₂ := (⊤ : Subgroup Q))
    rw [hcomm', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), hbot] at hc
    exact hc
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hxtop : x ∈ (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := Subgroup.mem_top x
  rw [hmap, Subgroup.mem_bot] at hxtop
  exact hx hxtop

theorem mem_map_subtype_iff {G : Type} [Group G] {K : Subgroup G} (M : Subgroup ↥K) (y : ↥K) :
    (y : G) ∈ M.map K.subtype ↔ y ∈ M := by
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 h
    have : z = y := Subtype.ext hzy
    rwa [this] at hz
  · intro h
    exact Subgroup.mem_map.2 ⟨y, h, rfl⟩

theorem catalog_of_component {G : Type} [Group G] [Finite G] {C K : Subgroup G}
    (hKG : CFSG.Open.IsKGroup ↥C) (hK : GLAPComponent 3 C K) : IsCatalogGroup (PSimple 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKC : K ≤ C :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
      Nat.prime_three).1 hK).1
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  haveI hNn : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hN
  set Z : Subgroup (↥K ⧸ N) := Subgroup.center (↥K ⧸ N) with hZ
  haveI hZn : Z.Normal := inferInstance
  set MK : Subgroup ↥K := Z.comap (QuotientGroup.mk' N) with hMK
  haveI hMKn : MK.Normal := inferInstance
  have hNMK : N ≤ MK := by
    intro n hn
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [hMK, Subgroup.mem_comap, h1]
    exact Z.one_mem
  set MG : Subgroup G := MK.map K.subtype with hMG
  have hMGK : MG ≤ K := Subgroup.map_subtype_le MK
  set K' : Subgroup ↥C := K.subgroupOf C with hK'
  set L' : Subgroup ↥C := MG.subgroupOf C with hL'
  have hL'K' : L' ≤ K' := by
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hMGK (Subgroup.mem_subgroupOf.1 hx))
  have hMGn : ∀ g ∈ K, ∀ m ∈ MG, g * m * g⁻¹ ∈ MG := by
    intro g hg m hm
    obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.1 hm
    have hg' : (⟨g, hg⟩ : ↥K) * m' * (⟨g, hg⟩ : ↥K)⁻¹ ∈ MK := hMKn.conj_mem m' hm' _
    exact Subgroup.mem_map_of_mem K.subtype hg'
  haveI hL'n : (L'.subgroupOf K').Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf, hL'] at hn ⊢
    rw [Subgroup.mem_subgroupOf]
    have hgK : ((g : ↥C) : G) ∈ K := g.2
    have key := hMGn _ hgK _ hn
    simpa using key
  let e₁ : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hmapL : (L'.subgroupOf K').map e₁.toMonoidHom = MK := by
    ext k
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (((x : ↥C)) : G) ∈ MG := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hx)
      have hx'' : e₁ x ∈ MK := (mem_map_subtype_iff MK (e₁ x)).1 (by
        have : ((e₁ x : ↥K) : G) = ((x : ↥C) : G) := rfl
        rw [this]
        exact hx')
      exact hx''
    · intro hk
      refine ⟨e₁.symm k, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ?_), by simp⟩
      have hval : (((e₁.symm k : ↥K') : ↥C) : G) = (k : G) := by
        have h1 : e₁ (e₁.symm k) = k := e₁.apply_symm_apply k
        have h2 : (((e₁ (e₁.symm k)) : ↥K) : G) = (((e₁.symm k : ↥K') : ↥C) : G) := rfl
        rw [← h2, h1]
      rw [hval]
      exact (mem_map_subtype_iff MK k).2 hk
  have e₂ : ↥K' ⧸ L'.subgroupOf K' ≃* ↥K ⧸ MK := QuotientGroup.congr (L'.subgroupOf K') MK e₁ hmapL
  haveI hMKmap : (MK.map (QuotientGroup.mk' N)).Normal := hMKn.map _ (QuotientGroup.mk'_surjective N)
  have hmapMK : MK.map (QuotientGroup.mk' N) = Z :=
    Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) Z
  let e₃ : (↥K ⧸ N) ⧸ MK.map (QuotientGroup.mk' N) ≃* ↥K ⧸ MK :=
    QuotientGroup.quotientQuotientEquivQuotient N MK hNMK
  let e₄ : (↥K ⧸ N) ⧸ Z ≃* ↥K ⧸ MK := (QuotientGroup.quotientMulEquivOfEq hmapMK).symm.trans e₃
  let e : ↥K' ⧸ L'.subgroupOf K' ≃* PSimple 3 K := e₂.trans e₄.symm
  haveI hsimp : IsSimpleGroup (↥K' ⧸ L'.subgroupOf K') := isSimpleGroup_of_mulEquiv' e.symm hq.2
  have hnc : ∃ a b : ↥K' ⧸ L'.subgroupOf K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple hq
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨f⟩⟩ := hKG K' L' hL'K' hsimp hnc
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem i141RankAtK_of_facts (hA : I141U9Lemma) (hB : I141U9Rank) (G : Type) [Group G] [Finite G] :
    CFSG.LocalAnalysis.GLTheoremA.I141RankAtK G := by
  intro Ky Kxy Kay x a y hKG hKy hx3 ha3 hxa hxna _hxC _haC hKxy hKxyT hKxyZ hKay _hKayT hFa _hFx hIx hIa
  have hKC : Ky ≤ Subgroup.centralizer ({y} : Set G) :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
      Nat.prime_three).1 hKy).1
  have hcat : IsCatalogGroup (PSimple 3 Ky) := catalog_of_component hKG hKy
  have hsimple : catalogIs (PSimple 3 Ky) isU9two :=
    hA G Ky Kxy x a hcat hx3 ha3 hxa hxna hIx hIa hKxy hKxyT hKxyZ hFa
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 Ky) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hKy
  obtain ⟨M, hM, h5⟩ := hB (PQuot 3 Ky) hq hsimple
  exact lift_twoLocal_rank hKC M hM h5

end CFSG.LocalAnalysis.GLTheoremA.I141F
