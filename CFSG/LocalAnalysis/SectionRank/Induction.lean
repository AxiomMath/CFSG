module

public import CFSG.LocalAnalysis.SectionRank.CatalogStep
public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.LocalAnalysis.SectionRank.Framework.CentralProductQuotient

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.LocalCores

variable {G : Type} [Group G]

theorem pRank_quotient_two_group [Finite G] (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (G ⧸ P)) = CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  refine pRank_quotient_eq P fun h => ?_
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hk] at h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))

theorem isStronglyQuasithin_quotient_two_group_iff [Finite G] (P : Subgroup G) [P.Normal]
    (hP : IsPGroup 2 P) : IsStronglyQuasithin (G ⧸ P) ↔ IsStronglyQuasithin G := by
  rw [isStronglyQuasithin_iff, isStronglyQuasithin_iff]
  exact forall₃_congr fun q hq hq2 => by rw [pRank_quotient_two_group P hP hq hq2]

theorem layer_eq_top_of_mulEquiv {H : Type} [Group H] [Finite G] (e : G ≃* H)
    (hG : layer G = ⊤) : layer H = ⊤ :=
  layer_eq_top_of_surjective hG e.toMonoidHom e.surjective

@[expose] def OddKernelCentralization : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → ∀ (C : Subgroup X) [C.Normal],
    Group.IsNilpotent C → Odd (Nat.card C) →
    (∀ (N : Subgroup (X ⧸ C)) [N.Normal], Subgroup.center ((X ⧸ C) ⧸ N) = ⊥) →
    (∀ r : ℕ, r.Prime → r ∣ Nat.card C → CFSG.Open.pRank r C ≤ 2) → C ≤ Subgroup.center X

@[expose] def CatalogStepHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsSQTKCat L →
    Odd (Nat.card (Subgroup.center L)) → CatalogStepConclusion L

theorem exists_orderOf_not_mem_center_of_card_center {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] (hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) :
    ∃ g : L, orderOf g = p ∧ g ∉ Subgroup.center L := by
  have : Fact p.Prime := ⟨hp⟩
  refine (perfect_cyclic_center_odd_elements hp2 hpL).1 ?_
  rw [pRank_eq_open_pRank_top]
  refine pRank_le hp.one_lt fun E _ _ => ?_
  have h1 : Nat.card E ≤ Nat.card (Subgroup.center L) := Subgroup.card_le_card_group E
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  rcases hZ with h | h <;> rw [h] at h1 <;> simp only [pow_one] <;> omega

theorem sqt_quotient_of_catalog_aux (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (n : ℕ) : ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → IsSQTKCat G →
      ∀ (V : Subgroup G) [V.Normal], layer (G ⧸ V) = ⊤ → IsStronglyQuasithin (G ⧸ V) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hG V _ hE
  by_contra hfail
  set S := G ⧸ V
  set π : G →* S := QuotientGroup.mk' V
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective V
  have hIH : ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → IsSQTKCat X →
      ∀ (W : Subgroup X) [W.Normal], layer (X ⧸ W) = ⊤ → IsStronglyQuasithin (X ⧸ W) :=
    fun X _ _ hX => ih _ hX X rfl
  have hmin : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤ := by
    intro Y hY hYmap
    let φ : Y →* S := π.comp Y.subtype
    have hφ : Function.Surjective φ := by
      intro s
      have hs : s ∈ Y.map π := hYmap ▸ Subgroup.mem_top s
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
      exact ⟨⟨y, hy⟩, rfl⟩
    let e : Y ⧸ φ.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    have hlt : Nat.card Y < n :=
      hn ▸ (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hY)).trans_eq Subgroup.card_top
    have h := hIH Y hlt (hG.subgroup Y) φ.ker (layer_eq_top_of_mulEquiv e.symm hE)
    exact hfail (isStronglyQuasithin_of_mulEquiv e.symm h)
  obtain ⟨hXperf, hCnormal, hCnil, hCsyl, ⟨eC, heC⟩, hZS, hES, hZX, hEX⟩ :=
    minimal_semisimple_cover hE π hπ hmin
  set C : Subgroup G := (Subgroup.center S).comap π with hCdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : ∀ Q : Sylow 2 C, (Q : Subgroup C) = ⊥ := by
    intro Q
    set P2 : Subgroup G := (Q : Subgroup C).map C.subtype with hP2def
    have : P2.Normal := hCsyl 2 Q
    have hP2 : IsPGroup 2 P2 := Q.isPGroup'.map C.subtype
    by_contra hne
    have hP2ne : P2 ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ P2 := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have hlt : Nat.card (G ⧸ P2) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup P2]
      have h1 := (Subgroup.one_lt_card_iff_ne_bot P2).2 hP2ne
      have h0 : 0 < Nat.card (G ⧸ P2) := Nat.card_pos
      nlinarith
    have hG' : IsSQTKCat (G ⧸ P2) :=
      ⟨(isStronglyQuasithin_quotient_two_group_iff P2 hP2).2 hG.1, hG.2.quotient P2⟩
    set M : Subgroup G := V ⊔ P2 with hMdef
    have : M.Normal := Subgroup.sup_normal V P2
    let e₁ : (G ⧸ P2) ⧸ M.map (QuotientGroup.mk' P2) ≃* G ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient P2 M le_sup_right
    let e₂ : S ⧸ M.map π ≃* G ⧸ M := QuotientGroup.quotientQuotientEquivQuotient V M le_sup_left
    have hMmap : M.map π = P2.map π := by
      rw [hMdef, Subgroup.map_sup]
      have : V.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [this, bot_sup_eq]
    have hP2S : IsPGroup 2 (M.map π) := hMmap ▸ hP2.map π
    have hsolv : Group.IsSolvable (M.map π) := by
      have := hP2S.isNilpotent
      infer_instance
    have hES' : layer (S ⧸ M.map π) = ⊤ := (semisimple_solvable_quotient hE (M.map π) hsolv).2
    have hEM : layer ((G ⧸ P2) ⧸ M.map (QuotientGroup.mk' P2)) = ⊤ :=
      layer_eq_top_of_mulEquiv (e₂.trans e₁.symm) hES'
    have hSQT' := hIH (G ⧸ P2) hlt hG' (M.map (QuotientGroup.mk' P2)) hEM
    have hSM : IsStronglyQuasithin (S ⧸ M.map π) :=
      isStronglyQuasithin_of_mulEquiv (e₂.trans e₁.symm) hSQT'
    exact hfail ((isStronglyQuasithin_quotient_two_group_iff (M.map π) hP2S).1 hSM)
  have hCodd : Odd (Nat.card C) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 C))
    exact Sylow.ne_bot_of_dvd_card Q h2 (hC2 Q)
  have hGSQT := isStronglyQuasithin_iff.1 hG.1
  have hCZ : C ≤ Subgroup.center G := by
    refine hcent G hXperf C hCnil hCodd (fun N _ => ?_) fun r hr hrC => ?_
    · exact (centerless_semisimple_quotient hEX hZX (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)).2
    · have hr2 : r ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 hCodd) (even_iff_two_dvd.2 hrC)
      exact (pRank_mono hr.one_lt le_top).trans (hGSQT r hr hr2)
  have hEG : layer G = ⊤ := perfect_central_semisimple_extension hXperf C hCZ hEX
  have hVC : V ≤ C := fun v hv => by
    have h1 : π v = 1 := (QuotientGroup.eq_one_iff v).2 hv
    change π v ∈ Subgroup.center S
    rw [h1]
    exact one_mem _
  have hVZ : V ≤ Subgroup.center G := hVC.trans hCZ
  have hZC : Subgroup.center G ≤ C := fun z hz =>
    Subgroup.mem_center_iff.2 fun s => by
      obtain ⟨g, rfl⟩ := hπ s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
  have hZodd : Odd (Nat.card (Subgroup.center G)) := by
    rw [le_antisymm hZC hCZ]
    exact hCodd
  have hcomp : ∀ L : Subgroup G, IsComponent L → CatalogStepConclusion L := by
    intro L hL
    refine hcat L hL.1 (hG.subgroup L) ?_
    have hle : (Subgroup.center L).map L.subtype ≤ Subgroup.center G := by
      intro z hz
      have h1 := center_component_le_center_layer hL hz
      rw [mem_map_center_iff] at h1
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ (layer G : Set G) := by rw [hEG]; trivial
      exact (Subgroup.mem_centralizer_iff.1 h1.2 g hg)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hZodd hdvd
  refine hfail (central_product_quotient_criterion hEG hG.1 (fun L hL p hp hp2 hpL => ?_)
    (fun L hL => (hcomp L hL).2) V hVZ)
  have : Group.IsPerfect L := hL.1.1
  exact exists_orderOf_not_mem_center_of_card_center (hcomp L hL).1 hp hp2 hpL

theorem sqt_quotient_of_catalog (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    {G : Type} [Group G] [Finite G] (hG : IsSQTKCat G) (V : Subgroup G) [V.Normal]
    (hE : layer (G ⧸ V) = ⊤) : IsStronglyQuasithin (G ⧸ V) :=
  sqt_quotient_of_catalog_aux hcent hcat _ G rfl hG V hE

theorem sqtk_semisimple_section_rank_of_catalog (hcent : OddKernelCentralization)
    (hcat : CatalogStepHyp) {G : Type} [Group G] [Finite G] (hG : IsSQTKCat G) (H : Subgroup G)
    (N : Subgroup H) [N.Normal] (hE : layer (H ⧸ N) = ⊤) : IsStronglyQuasithin (H ⧸ N) :=
  sqt_quotient_of_catalog hcent hcat (hG.subgroup H) N hE

end CFSG.SectionRank
