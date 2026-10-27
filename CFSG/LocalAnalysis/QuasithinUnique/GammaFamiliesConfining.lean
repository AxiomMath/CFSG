module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

section Elementary

variable {G : Type*} [Group G]

theorem pCoreOf_eq_of_isPGroup {p : ℕ} {U : Subgroup G} (hU : IsPGroup p U) : pCoreOf p U = U :=
  le_antisymm (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p U)
    (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf p U U le_rfl
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).mpr Subgroup.le_normalizer) hU)

theorem charTwo_of_isPGroup {U : Subgroup G} (hU : IsPGroup 2 U) : CharTwo U := by
  unfold CharTwo
  rw [pCoreOf_eq_of_isPGroup hU]
  exact inf_le_left

theorem inf_centralizer_ne_bot {P : Subgroup G} [Finite G] (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    P ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have hnt : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center P)
  have hzc : (z : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  intro hbot
  have hmem : (z : G) ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨z.2, hzc⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 (Subtype.ext (Subtype.ext hmem))

theorem IsSylowTwoOf.pCoreOf_le {M S : Subgroup G} (hS : IsSylowTwoOf S M) : pCoreOf 2 M ≤ S :=
  hS.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)

end Elementary

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace UniqueSetting

variable (h : UniqueSetting G T M)
include h

theorem twoPart_top : twoPart (⊤ : Subgroup G) = Nat.card T :=
  (isSylowTwoOf_iff.mp h.sylow).2.2.symm

theorem card_le_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 X) : Nat.card X ≤ Nat.card T :=
  h.twoPart_top ▸ card_le_twoPart le_top hX

theorem isSylowTwoOf_M : IsSylowTwoOf T M :=
  isSylowTwoOf_of_card_eq h.le h.isPGroup
    (le_antisymm (card_le_twoPart h.le h.isPGroup) (h.twoPart_top ▸ twoPart_mono le_top))

theorem twoPart_M : twoPart M = Nat.card T := h.isSylowTwoOf_M.card_eq.symm

theorem card_eq_of_isSylowTwoOf_M {S : Subgroup G} (hS : IsSylowTwoOf S M) :
    Nat.card S = Nat.card T := by
  rw [hS.card_eq, ← h.isSylowTwoOf_M.card_eq]

theorem isSylowTwoOf_top_of_isSylowTwoOf_M {S : Subgroup G} (hS : IsSylowTwoOf S M) :
    IsSylowTwoOf S ⊤ :=
  isSylowTwoOf_of_card_eq le_top hS.isPGroup (by rw [h.twoPart_top, h.card_eq_of_isSylowTwoOf_M hS])

theorem unique_of_isSylowTwoOf_M {S : Subgroup G} (hS : IsSylowTwoOf S M) :
    ∀ M' : Subgroup G, CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M' → S ≤ M' → M' = M := by
  intro M' hM' hSM'
  obtain ⟨g, hgM, hgS⟩ := h.isSylowTwoOf_M.exists_conj hS
  set f : G ≃* G := MulAut.conj g⁻¹ with hf
  have hmax : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal (M'.map f.toMonoidHom) :=
    quasithinIsMaxTwoLocal_map_equiv hM' f
  have hTle : T ≤ M'.map f.toMonoidHom := by
    have h1 := Subgroup.map_mono (f := f.toMonoidHom) hSM'
    have h2 : S.map f.toMonoidHom = T := by
      rw [hgS, Subgroup.map_map]
      have : f.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [hf, MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    rwa [h2] at h1
  have hEq := h.unique _ hmax hTle
  have : M' = (M'.map f.toMonoidHom).map f.symm.toMonoidHom := (map_equiv_symm_map_equiv f M').symm
  rw [this, hEq]
  have hsymm : f.symm = MulAut.conj g := by
    ext x
    simp [hf, MulAut.conj_apply, mul_assoc]
  rw [hsymm]
  exact map_conj_eq_self_of_mem hgM

theorem le_of_isTwoLocal_of_isSylowTwoOf_M {S K : Subgroup G} (hS : IsSylowTwoOf S M)
    (hK : IsTwoLocal K) (hSK : S ≤ K) : K ≤ M := by
  obtain ⟨M', hM'max, hKM'⟩ := exists_quasithinIsMaxTwoLocal_ge hK
  have := h.unique_of_isSylowTwoOf_M hS M' hM'max (hSK.trans hKM')
  exact this ▸ hKM'

theorem center_le_pCoreOf_M {T' : Subgroup G} (hT' : IsSylowTwoOf T' M) :
    T' ⊓ Subgroup.centralizer (T' : Set G) ≤ pCoreOf 2 M := by
  intro z hz
  have hcore : (pCoreOf 2 M : Set G) ⊆ T' := hT'.pCoreOf_le
  exact h.charTwo ⟨hT'.le hz.1, Subgroup.centralizer_le hcore hz.2⟩

theorem center_le_center_of_isConfining {T' S : Subgroup G} (hT' : IsSylowTwoOf T' M)
    (hST : S ≤ T') (hS : IsConfining M S) :
    T' ⊓ Subgroup.centralizer (T' : Set G) ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
  intro z hz
  have hzS : z ∈ S := hS.2.2.2.2 ⟨h.center_le_pCoreOf_M hT' hz,
    Subgroup.centralizer_le (by exact_mod_cast hST) hz.2⟩
  exact ⟨hzS, Subgroup.centralizer_le (by exact_mod_cast hST) hz.2⟩

end UniqueSetting

end Setting

section Confining

variable {G : Type*} [Group G] [Finite G]

theorem IsConfining.of_le {M U V : Subgroup G} (hU : IsConfining M U) (hV : IsPGroup 2 V)
    (hUV : U ≤ V) : IsConfining M V := by
  obtain ⟨hUM, hU1, -, hUN, hUC⟩ := hU
  have hconf := normalizer_overgroup_confinement (p := 2) hUM hUN V hV hUV
  refine ⟨hconf.1, ne_bot_of_le_ne_bot hU1 hUV, hV, hconf.2, ?_⟩
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (by exact_mod_cast hUV))).trans (hUC.trans hUV)

theorem IsConfining.twoPart_eq_inf {M U H : Subgroup G} (hU : IsConfining M U) (hUH : U ≤ H) :
    twoPart H = twoPart (H ⊓ M) :=
  pow_factorization_card_eq_inf_of_confinement (p := 2) hU.1 hU.2.2.1 hU.2.2.2.1 H hUH

theorem IsConfining.sylow_le_and_isConfining {M U H S : Subgroup G} (hU : IsConfining M U)
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) : S ≤ M ∧ IsConfining M S :=
  have hSc : IsConfining M S := hU.of_le hS.isPGroup hUS
  ⟨hSc.1, hSc⟩

end Confining

section ConfiningLocal

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsConfining.charTwo_normalizer_core (h : UniqueSetting G T M) {U H : Subgroup G}
    (hU : IsConfining M U) (hUH : U ≤ H) (hH : CharTwo H) :
    pCoreOf 2 H ≠ ⊥ ∧ CharTwo (Subgroup.normalizer (pCoreOf 2 H : Set G)) := by
  obtain ⟨S, hUS, hS⟩ := exists_isSylowTwoOf_of_le hUH hU.2.2.1
  have hSc : IsConfining M S := hU.of_le hS.isPGroup hUS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hQS : pCoreOf 2 H ≤ S :=
    hS.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H) hQ2
  have hZT : T' ⊓ Subgroup.centralizer (T' : Set G) ≤ S ⊓ Subgroup.centralizer (S : Set G) :=
    h.center_le_center_of_isConfining hT' hST' hSc
  have hZS : S ⊓ Subgroup.centralizer (S : Set G) ≤ pCoreOf 2 H := fun z hz =>
    hH ⟨hS.le hz.1, Subgroup.centralizer_le (by exact_mod_cast hQS) hz.2⟩
  have hTne : T' ≠ ⊥ := ne_bot_of_le_ne_bot hU.2.1 (hUS.trans hST')
  have hZne : T' ⊓ Subgroup.centralizer (T' : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot hT'.isPGroup hTne
  have hQne : pCoreOf 2 H ⊓ (T' ⊓ Subgroup.centralizer (T' : Set G)) ≠ ⊥ := by
    rwa [inf_eq_right.mpr (hZT.trans hZS)]
  refine ⟨fun h0 => hQne (by rw [h0]; exact bot_inf_eq _), ?_⟩
  exact charTwo_normalizer_of_inf_center h.qtke.2.1 (h.isSylowTwoOf_top_of_isSylowTwoOf_M hT') hQ2
    hQne

theorem IsConfining.charTwo_normalizer (h : UniqueSetting G T M) {U : Subgroup G}
    (hU : IsConfining M U) : CharTwo (Subgroup.normalizer (U : Set G)) := by
  have := (hU.charTwo_normalizer_core h le_rfl (charTwo_of_isPGroup hU.2.2.1)).2
  rwa [pCoreOf_eq_of_isPGroup hU.2.2.1] at this

end ConfiningLocal

section MaximalEscaping

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem maximal_escaping_normalizer_witness (h : UniqueSetting G T M) {D S : Subgroup G}
    (hD : Maximal (IsEscaping M) D)
    (hS : IsSylowTwoOf S (M ⊓ Subgroup.normalizer (D : Set G))) :
    pCoreOf 2 (Subgroup.normalizer (D : Set G)) = D ∧
      pCoreOf 2 M ⊓ Subgroup.centralizer (D : Set G) ≤ D ∧ D < S ∧
      Nat.card S < Nat.card T ∧ IsConfining M S ∧
      IsSylowTwoOf S (Subgroup.normalizer (D : Set G)) ∧
      ∀ U : Subgroup G, IsPGroup 2 U → D < U → U ≤ M → IsConfining M U := by
  obtain ⟨hDe, hDmax⟩ := hD
  obtain ⟨hDM, hD1, hD2, hDchar, hDnot⟩ := hDe
  have hDle : D ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer
  have hconf : ∀ V : Subgroup G, IsPGroup 2 V → D < V → V ≤ M →
      Subgroup.normalizer (V : Set G) ≤ M := by
    intro V hV hDV hVM
    by_contra hnot
    have hesc : IsEscaping M V := ⟨hVM, ne_bot_of_le_ne_bot hD1 hDV.le, hV,
      charTwo_normalizer_of_le hV hDV.le hDchar, hnot⟩
    exact hDV.not_ge (hDmax hesc hDV.le)
  have hSle : S ≤ M ⊓ Subgroup.normalizer (D : Set G) := hS.le
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hDS : D ≤ S := hS.le_of_normalizes (le_inf hDM hDle) inf_le_right hD2
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le (hSle.trans inf_le_left) hS2
  have hSne : S ≠ T' := by
    intro hEq
    exact hDnot (h.le_of_isTwoLocal_of_isSylowTwoOf_M hT' ⟨D, hD1, hD2, rfl⟩
      (hEq ▸ hSle.trans inf_le_right))
  have hSlt : S < T' := lt_of_le_of_ne hST' hSne
  have hc : T' ⊓ Subgroup.normalizer (D : Set G) = S :=
    hS.eq_of_le (le_inf hST' (hSle.trans inf_le_right))
      (le_inf (inf_le_left.trans hT'.le) inf_le_right) (hT'.isPGroup.to_le inf_le_left)
  have hDlt : D < S := by
    refine lt_of_le_of_ne hDS fun hDeq => ?_
    have hne : D ≠ T' := hDeq ▸ hSne
    obtain ⟨x, hx, hxD⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT'.isPGroup
      (hDS.trans hST') hne
    have hxS : x ∈ S := hc ▸ hx
    exact hxD (by rw [hDeq]; exact hxS)
  have hnorm : ∀ V : Subgroup G, IsPGroup 2 V → S ≤ V → V ≤ M →
      Subgroup.normalizer (V : Set G) ≤ M := fun V hV hSV hVM =>
    hconf V hV (hDlt.trans_le hSV) hVM
  have hSsyl : IsSylowTwoOf S (Subgroup.normalizer (D : Set G)) := by
    obtain ⟨R, hSR, hR⟩ := exists_isSylowTwoOf_of_le (hSle.trans inf_le_right) hS2
    have hRM : R ≤ M :=
      (normalizer_overgroup_confinement (p := 2) (hSle.trans inf_le_left) hnorm R hR.isPGroup
        hSR).1
    have hReq : R = S := hS.eq_of_le hSR (le_inf hRM hR.le) hR.isPGroup
    rwa [hReq] at hR
  have hE : pCoreOf 2 (Subgroup.normalizer (D : Set G)) = D := by
    have hDE : D ≤ pCoreOf 2 (Subgroup.normalizer (D : Set G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 D _ hDle
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDle).mpr le_rfl) hD2
    have hES : pCoreOf 2 (Subgroup.normalizer (D : Set G)) ≤ S :=
      hSsyl.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    refine le_antisymm ?_ hDE
    by_contra hnot
    have hlt : D < pCoreOf 2 (Subgroup.normalizer (D : Set G)) :=
      lt_of_le_of_ne hDE fun hh => hnot hh.ge
    have h1 := hconf _ (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) hlt
      (hES.trans (hSle.trans inf_le_left))
    exact hDnot
      ((CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _).trans h1)
  have hCD : pCoreOf 2 M ⊓ Subgroup.centralizer (D : Set G) ≤ D := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (D : Set G) := Subgroup.centralizer_le_normalizer _ hy.2
    have hmem : y ∈ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (D : Set G)) : Set G) :=
      ⟨hyN, by rw [hE]; exact hy.2⟩
    have := hDchar hmem
    rwa [hE] at this
  have hbeta : ∀ U : Subgroup G, IsPGroup 2 U → D < U → U ≤ M → IsConfining M U := by
    intro U hU hDU hUM
    refine ⟨hUM, ne_bot_of_le_ne_bot hD1 hDU.le, hU,
      fun V hV hUV hVM => hconf V hV (hDU.trans_le hUV) hVM, ?_⟩
    exact (inf_le_inf_left _ (Subgroup.centralizer_le (by exact_mod_cast hDU.le))).trans
      (hCD.trans hDU.le)
  refine ⟨hE, hCD, hDlt, ?_, hbeta S hS2 hDlt (hSle.trans inf_le_left), hSsyl, hbeta⟩
  calc Nat.card S < Nat.card T' := Subgroup.card_lt_of_lt hSlt
    _ = Nat.card T := h.card_eq_of_isSylowTwoOf_M hT'

end MaximalEscaping

end CFSG.QuasithinUnique
