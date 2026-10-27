module

public import CFSG.LocalAnalysis.AGLEmbedding.G28PieceOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section PieceGeneric

variable {G : Type} [Group G] [Finite G]

theorem not_mem_glbPrimeCore_of_three {H : Subgroup G} {y : G}
    (hy3 : IsPGroup 3 (Subgroup.zpowers y)) (hy1 : y ≠ 1) : y ∉ GLBPrimeCore 3 H := by
  intro hyN
  obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hya : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hcop : Nat.Coprime (3 ^ a) (Nat.card (GLBPrimeCore 3 H)) :=
    Nat.Coprime.pow_left a (glbPrimeCore_coprime 3 H)
  exact hy1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hya) (Subgroup.orderOf_dvd_natCard _ hyN)))

theorem D1PhaseThree.mem_Pi' {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (hB3 : StmtBlockThree) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    H ⊓ M ≤ Subgroup.normalizer (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L : Subgroup G) : Set G) ∧
    ∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧
      (∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M) ∧ y ∈ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L := by
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  refine ⟨(le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
    Subgroup.inf_normalizer_le_normalizer_inf, ?_⟩
  obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB3 h3 hL
  have hyK : y ∈ H ⊓ M := hKeq ▸ ⟨hL.le hyL, hyS⟩
  have hyE : y ∈ blockClosure M (H ⊓ M) L :=
    Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨y, hyL, by simp⟩))
  exact ⟨y, hyL, hy3, ⟨l, hl, hlQ⟩, hyK, hyE⟩

end PieceGeneric

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section PieceCommutator

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.commutator_le_of_piece {P : Sylow 3 G} {M H R : Subgroup G}
    (h3 : D1PhaseThree 3 P M H R) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {V : Subgroup G} (hVV : ⁅V, V⁆ = V) (hVK : V ≤ H ⊓ M) (hVN : ¬ V ≤ GLBPrimeCore 3 H)
    (hKVN : H ⊓ M ≤ Subgroup.normalizer ((V ⊔ GLBPrimeCore 3 H : Subgroup G) : Set G))
    (hdich : ∀ W : Subgroup G, W ≤ H ⊓ M → V ≤ Subgroup.normalizer (W : Set G) →
      V ≤ W ⊔ GLBPrimeCore 3 H ∨ ⁅W, V⁆ ≤ GLBPrimeCore 3 H)
    (hVE : V ≤ blockClosure M (H ⊓ M) L) {k : G} (hk : k ∈ H ⊓ M)
    (hne : barM M (L.map (MulAut.conj k).toMonoidHom) ≠ barM M L) :
    ⁅(H ⊓ M) ⊓ preM M (barM M L), V⁆ ≤ GLBPrimeCore 3 H :=
  (h3.commutator_le_of_piece_and_conj hL hVV hVK hVN hKVN hdich hVE hk hne).1

end PieceCommutator

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section OrbitOneSp62

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.barM_Pi_le' {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hb : StmtBlockInnerNormalizer) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (horb : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L) :
    barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) ≤ blockParabolic M (pCoreOf 2 H) L := by
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hBC : blockClosure M (H ⊓ M) L ≤ preM M (barM M L) := by
    refine sup_le (fun q hq => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
    · refine (mem_preM ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hq)).mpr ?_
      rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
      exact Subgroup.one_mem _
    · exact le_preM (hL.toIsTwoPrimeComponent.map_conj hk.2).le (horb k hk).le
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hx' := Subgroup.mem_subgroupOf.mp hx
  have hxL := (mem_preM hxM).mp (hBC hx'.2)
  have hxS : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hx'.1).2
  have hxN := mem_normalizer_barM hxM hxS
  refine hb h3 h84 h86 hD2 hL _ hxL fun s hs => ⟨_ * s * _⁻¹,
    (Subgroup.mem_normalizer_iff.mp hxN s).mp hs, fun w hw => rfl⟩

variable {P : Sylow 3 G} {M H R V : Subgroup G}

theorem D1Sp62Data.le_Pi (h : D1Sp62Data P M H R V) (hB3 : StmtBlockThree) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : V ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L := by
  obtain ⟨hN, y, -, hy3, ⟨l, -, hyl⟩, hyPi⟩ := h.surv.ph3.mem_Pi' hB3 hL
  refine (h.dichotomy _ inf_le_left hN).resolve_left fun hPiN => ?_
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hyl
    simp
  exact not_mem_glbPrimeCore_of_three hy3 hy1 (hPiN hyPi)

theorem D1Sp62Data.barM_conj_eq (h : D1Sp62Data P M H R V) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {k : G} (hk : k ∈ H ⊓ M) :
    barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L := by
  have h3 := h.surv.ph3
  obtain ⟨hVV, hVK, hVN, hKVN, -, -, hdich, hcent⟩ := h.piece
  obtain ⟨-, y, hyL, hy3, ⟨l, -, hyl⟩, hyPi⟩ := h3.mem_Pi' hB3 hL
  by_contra hne
  have hc := h3.commutator_le_of_piece hL.toIsTwoPrimeComponent hVV hVK hVN hKVN hdich
    ((h.le_Pi hB3 hL).trans inf_le_right) hk hne
  have hyW : y ∈ (H ⊓ M) ⊓ preM M (barM M L) := ⟨hyPi.1, le_preM hL.le le_rfl hyL⟩
  have hyN : y ∈ GLBPrimeCore 3 H := hcent y hyPi.1 fun v hv => by
    have := Subgroup.commutator_mem_commutator hyW hv
    simpa [commutatorElement_def] using hc this
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hyl
    simp
  exact not_mem_glbPrimeCore_of_three hy3 hy1 hyN

end OrbitOneSp62

end CFSG.AGLEmbedding
