module

public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

theorem le_normalizer_of_input11_6 (i11 : Input11_6) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C B X L : Subgroup G}
    (hCtop : C ≠ ⊤) (hBC : B ≤ C) (hXC : X ≤ C) (hSC : IsSCp p ⊤ B)
    (hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C)) (hX2 : IsPGroup 2 X)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hL : GLAPComponent p C L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have hKC : CFSG.Open.IsKGroup ↥C := isKGroup_of_isKProper hK hCtop
  have hSC' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf hSC hBC
  have hcop : Nat.Coprime p (Nat.card (X.subgroupOf C)) := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hnorm : B.subgroupOf C ≤ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 (hBX ((Subgroup.mem_subgroupOf).1 hb)) (x : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hmain := i11 ↥C hKC p hp hp2 (B.subgroupOf C) hSC' hrank (X.subgroupOf C) hcop hnorm
    (L.subgroupOf C) (glaPComponent_top hL)
  intro x hx
  have hxX : (⟨x, hXC hx⟩ : ↥C) ∈ X.subgroupOf C := (Subgroup.mem_subgroupOf).2 hx
  have hxn := Subgroup.mem_normalizer_iff.1 (hmain hxX)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := (hxn ⟨y, hL.1 hy⟩).1 ((Subgroup.mem_subgroupOf).2 hy)
    exact (Subgroup.mem_subgroupOf).1 (by simpa using h1)
  · intro hy
    have hyC : y ∈ C := by
      have : x * y * x⁻¹ ∈ C := hL.1 hy
      have := C.mul_mem (C.mul_mem (C.inv_mem (hXC hx)) this) (hXC hx)
      simpa [mul_assoc] using this
    have h1 := (hxn ⟨y, hyC⟩).2 ((Subgroup.mem_subgroupOf).2 (by simpa using hy))
    exact (Subgroup.mem_subgroupOf).1 h1

theorem coprime_card_of_isPGroup_two {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup G} (hX : IsPGroup 2 X) : Nat.Coprime p (Nat.card X) := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem lemma91ii_of_inputs (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23) : Lemma91ii := by
  intro G _ _ m p hS B M hB hM b hb hb1
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.simple
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := pCoreOf 2 (M ⊓ C) with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB hM
  have hBC : B ≤ C := fun b' hb' =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB.1.1 hb' hb)
  have hXC : X ≤ C := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hX2 : IsPGroup 2 X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hBX : B ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hBM hBC).trans (le_normalizer_pCoreOf 2 _)
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hcenter : b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ C := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have hcbot : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, c, hac⟩ := hS.nonabelian
        exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) a)
          hac
    rw [hcbot, Subgroup.mem_bot] at hcenter
    exact hb1 hcenter
  have hK0M : GLAPPrimeCoreOf p C ≤ M := lemma91_i hS hB hM hb
  have hlam : lambdaOf p B b ≤ M :=
    ((le_sup_left.trans le_sup_left : lambdaOf p B b ≤ lambdaStar p B b).trans
      (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl) : lambdaStar p B b ≤
        lambdaStarGroup p B)).trans hM.2.1
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (l23 G m p hS B hB) hBC
  have hBbar : IsSCp p ⊤ (barX p C B) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥C)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hB'
  have hXb2 : IsPGroup 2 (barX p C X) :=
    IsPGroup.map (hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXC).symm)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
  have hBXb : barX p C B ≤ Subgroup.normalizer (barX p C X : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_le_normalizer hBX
  have h1 := centralizes_pCore_of_isSCp i20 hp hp2 hBbar hXb2 hBXb
  have hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
    rw [hS.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hS.card_eq hB]
  have h2 : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C X ≤ Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK
    by_cases hbal : IsStronglyLocallyOneBalanced p B b L
    · have hXL : X ≤ Subgroup.normalizer (L : Set G) :=
        le_normalizer_of_input11_6 i11 hS.kProper hp hp2 hCtop hBC hXC (l23 G m p hS B hB)
          hrank hX2 hBX hL
      have hcomm : ⁅L, X⁆ ≤ GLAPPrimeCoreOf p L :=
        hbal X (le_inf hXL hXC) (coprime_card_of_isPGroup_two hp hp2 hX2)
          (fun g hg => hBX hg.1)
      refine barX_le_centralizer fun s hs t ht _ _ => ?_
      have h3 : s * t * s⁻¹ * t⁻¹ ∈ ⁅X, L⁆ := Subgroup.commutator_mem_commutator hs ht
      rw [Subgroup.commutator_comm] at h3
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcomm h3)
    · have hLM : L ≤ M := (le_sSup ⟨hL, hbal⟩ : L ≤ lambdaOf p B b).trans hlam
      have hLX : L ≤ Subgroup.normalizer (X : Set G) :=
        (le_inf hLM hL.1).trans (le_normalizer_pCoreOf 2 _)
      have hKX := barX_le_normalizer (p := p) (C := C) hLX
      have hcomm := commutator_eq_bot_of_normalizes hK hXb2 hKX
      exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
  have hXb : barX p C X = ⊥ :=
    eq_bot_of_centralizes_pCore_components hp hQcore (coprime_card_of_isPGroup_two hp hp2 hXb2)
      h1 h2
  have hXK : X ≤ GLAPPrimeCoreOf p C := by
    intro x hx
    have hxC : x ∈ C := hXC hx
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨x, hxC⟩ ∈ barX p C X :=
      ⟨⟨x, hxC⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
    rw [hXb, Subgroup.mem_bot] at hmem
    exact ⟨⟨x, hxC⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  have hK₀C : GLAPPrimeCoreOf p C ≤ C := Subgroup.map_subtype_le _
  have hK₀n : GLAPPrimeCoreOf p C ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hK0M hK₀C).trans (le_normalizer_pCoreOf 2 _)
  have hXO : X ≤ pCoreOf 2 (GLAPPrimeCoreOf p C) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXK hK₀n hX2
  have hCn : C ≤ Subgroup.normalizer (pCoreOf 2 (GLAPPrimeCoreOf p C) : Set G) := by
    intro c hc
    have h1 := le_normalizer_glaPPrimeCoreOf p C hc
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [← pCoreOf_gLBConj, h1]
  exact hXO.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hK₀C) hCn
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))

theorem lemma91_of_inputs (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23) : Lemma91 :=
  lemma91_iff.2 (lemma91ii_of_inputs i20 i11 l23)

end CFSG.LocalAnalysis.GLTheoremB
