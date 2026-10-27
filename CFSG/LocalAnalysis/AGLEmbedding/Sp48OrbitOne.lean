module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Gen
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Pkg

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_zpowers {M : Subgroup G} {u : G} (hu : u ∈ M) :
    barM M (Subgroup.zpowers u) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hu⟩) := by
  have e1 : (Subgroup.zpowers u).subgroupOf M = Subgroup.zpowers (⟨u, hu⟩ : M) := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hu), MonoidHom.map_zpowers]
    rfl
  rw [barM, e1, MonoidHom.map_zpowers]

omit [Finite G] in
theorem barM_inf_of_isPGroup {M A Z W : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : IsPGroup p A) (hZA : Z ≤ A) (hWA : W ≤ A) :
    barM M (Z ⊓ W) = barM M Z ⊓ barM M W := by
  refine le_antisymm (le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
    (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))) ?_
  rintro _ ⟨⟨z, hz, rfl⟩, ⟨w, hw, hwz⟩⟩
  have hzA : (z : G) ∈ A := hZA (Subgroup.mem_subgroupOf.mp hz)
  have hwA : (w : G) ∈ A := hWA (Subgroup.mem_subgroupOf.mp hw)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (w⁻¹ * z) = 1 := by
    rw [map_mul, map_inv, hwz, inv_mul_cancel]
  have hx : ((w⁻¹ * z : M) : G) ∈ A := by simpa using A.mul_mem (A.inv_mem hwA) hzA
  have h2 := eq_one_of_mem_pCoreOf_two hp hp2 hA hx (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have h3 : w = z := by
    have : w⁻¹ * z = 1 := Subtype.ext h2
    exact inv_mul_eq_one.mp this
  refine ⟨z, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hz, ?_⟩, rfl⟩
  rw [← h3]
  exact Subgroup.mem_subgroupOf.mp hw

theorem D1PhaseThree.le_normalizer_of_orbit {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (hL : IsTwoPrimeComponent M L)
    (horb : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  refine hL.le_normalizer ?_ h3.le_M
  rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
  have heq := horb r (h3.le_inf (Subgroup.mem_subgroupOf.mp hr))
  rw [barM_map_conj hrM] at heq
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

variable {P : Sylow 3 G} {M H R X U A : Subgroup G}

theorem D1Sp48Data₂.inf_blockCentralizer_eq_bot (h : D1Sp48Data₂ P M H R X U A)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hXL : barM M X ≤ barM M L) : R ⊓ blockCentralizer M L = ⊥ := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨w, hwC, hwZ, hw1⟩ := exists_mem_inf_centerOf h3.isPGroup_R
    (inf_le_left : R ⊓ blockCentralizer M L ≤ R) (fun r hr =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr,
        mem_normalizer_blockCentralizer (h3.le_M hr) (hRL hr)⟩) hne
  have hwX : w ∈ X := h.center_le hwZ
  have hwM : w ∈ M := h3.le_M hwC.1
  have hwL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ ∈ barM M L :=
    hXL (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwX))
  have hwCb := (mem_blockCentralizer_iff ⟨w, hwM⟩).mp hwC.2
  have hw3 : IsPGroup 3 (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩)) := by
    obtain ⟨a, ha⟩ := h3.isPGroup_R ⟨w, hwC.1⟩
    have hwa : (⟨w, hwM⟩ : M) ^ 3 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
    exact isPGroup_zpowers_of_pow_prime_pow_eq_one (by rw [← map_pow, hwa, map_one])
  have h1 := eq_one_of_mem_center_component hO hL.component hwL hwCb hw3
  exact hw1 (eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) h3.isPGroup_R hwC.1
    (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))

end Helpers

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section OrbitOne

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A : Subgroup G}

theorem D1Sp48Data₂.false_of_orbit_one (h : D1Sp48Data₂ P M H R X U A)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut)
    (hNine : KFactBlockThreeOrderNine) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (horb : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L) : False := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Pi := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hPi
  have hPiM : Pi ≤ M := inf_le_left.trans inf_le_right
  have hPiPL : barM M Pi ≤ blockParabolic M S L := h3.barM_Pi_le' h84 h86 hD2 hb hL horb
  have hPLPi := blockParabolic_le_barM hKeq hL.le (le_rfl : Pi ≤ Pi)
  have hPLK : blockParabolic M S L ≤ barM M (H ⊓ M) :=
    hPLPi.trans (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
  have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockParabolic M S L →
      ⁅W, W⁆ = W → Nat.Coprime 3 (Nat.card W) := fun W hW hWW =>
    h.coprime_of_perfect (hW.trans hPLK) hWW
  have hRL := h3.le_normalizer_of_orbit hL.toIsTwoPrimeComponent horb
  obtain ⟨hXPi, hcases⟩ := h.Pi_cases hB3 hL
  have hXL : barM M X ≤ Lb := ((Subgroup.map_mono (Subgroup.comap_mono hXPi)).trans
    hPiPL).trans (blockParabolic_le_barM' _ _ _)
  have hC := h.inf_blockCentralizer_eq_bot hO hL.toIsTwoPrimeComponent hRL hXL
  have hRM : R ≤ M := h3.le_M
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  have hUS : barM M R ≤ barM M (Subgroup.normalizer (S : Set G)) :=
    Subgroup.map_mono (Subgroup.comap_mono ((hKeq ▸ h3.le_inf).trans inf_le_right))
  have hUN : barM M R ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hL' : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRL (Subgroup.mem_subgroupOf.mp hx))
    have hLbar : (barM M L).map (MulAut.conj (mk x)).toMonoidHom = barM M L := by
      rw [← barM_map_conj x.2, hL']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar
  have hU3 : IsPGroup 3 (barM M R) := (hR3.comap_subtype (K := M)).map _
  have hγ := hOut G M S L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL) hperf
    (barM M R) hUS hUN hU3
  set I := barM M R ⊓ (Lb ⊔ Cb) with hI
  have hIC : I ⊓ Cb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨⟨r, hrM⟩, hr, rfl⟩, -⟩, hrC⟩
    have hrC' : r ∈ R ⊓ blockCentralizer M L :=
      ⟨Subgroup.mem_subgroupOf.mp hr, (mem_blockCentralizer_iff ⟨r, hrM⟩).mpr hrC⟩
    rw [hC, Subgroup.mem_bot] at hrC'
    subst hrC'
    exact Subgroup.mem_bot.mpr (map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
  have hLbN : Lb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := Subgroup.le_normalizer
  have hIdvd : Nat.card I ∣ Nat.card (blockParabolic M S L) :=
    card_dvd_of_faithful_inner (inf_le_left.trans hUN)
      ((blockParabolic_le_barM' M S L).trans hLbN) hIC fun x hx =>
      h3.exists_mem_blockParabolic h84 h86 hD2 hb hL (hUS hx.1) hx.2
  have hcardU : Nat.card (barM M R) = 3 ^ 5 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hRM hR3, h.card_R]
  have hmul := (I.subgroupOf (barM M R)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : I ≤ barM M R)).toEquiv,
    hcardU] at hmul
  have hidx : (I.subgroupOf (barM M R)).index ≤ 3 := hγ
  obtain ⟨a, ha⟩ := (hU3.to_le (inf_le_left : I ≤ barM M R)).exists_card_eq
  have ha4 : 4 ≤ a := by
    by_contra hlt
    have hle : 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha] at hmul
    have := Nat.mul_le_mul hle hidx
    rw [hmul] at this
    norm_num at this
  have h81I : 3 ^ 4 ∣ Nat.card I := ha ▸ pow_dvd_pow 3 ha4
  have h81 : 3 ^ 4 ∣ Nat.card (R ⊓ Pi : Subgroup G) :=
    pow_dvd_card_of_isSylowOf (h.isSylowOf_Pi hB3 hL) (h81I.trans (hIdvd.trans
      ((Subgroup.card_dvd_of_le hPLPi).trans (card_barM_dvd hPiM))))
  have hUPi : U ≤ Pi := by
    rcases hcases with h1 | h1 | h1 | h1
    · rw [h1, h.card_X] at h81
      norm_num at h81
    · rw [h1, h.card_A] at h81
      norm_num at h81
    · exact h1 ▸ inf_le_right
    · exact h.U_le.trans (h1 ▸ inf_le_right)
  obtain ⟨u, v, huU, hvU, hu9, hv9, huv, hbot⟩ := h.homocyclic
  have hUM : U ≤ M := h.U_le.trans hRM
  have hU3' : IsPGroup 3 U := hR3.to_le h.U_le
  have hLV := (hNine G M S L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    (fun l hl hcond => hb h3 h84 h86 hD2 hL l hl hcond) hperf).2
  refine hLV (mk ⟨u, hUM huU⟩)
    (hPiPL (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hUPi huU))))
    (mk ⟨v, hUM hvU⟩)
    (hPiPL (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hUPi hvU))))
    (by rw [orderOf_mk_of_isPGroup Nat.prime_three (by norm_num) hUM hU3' huU]; exact hu9)
    (by rw [orderOf_mk_of_isPGroup Nat.prime_three (by norm_num) hUM hU3' hvU]; exact hv9)
    (by rw [← map_mul, ← map_mul]; exact congrArg mk (Subtype.ext huv)) ?_
  rw [← barM_zpowers (hUM huU), ← barM_zpowers (hUM hvU),
    ← barM_inf_of_isPGroup Nat.prime_three (by norm_num) hU3'
      (Subgroup.zpowers_le.mpr huU) (Subgroup.zpowers_le.mpr hvU), hbot]
  rw [barM, Subgroup.bot_subgroupOf, Subgroup.map_bot]

end OrbitOne

end CFSG.AGLEmbedding
