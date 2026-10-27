module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

namespace TwoLocalPair

variable {G : Type} [Group G] [Finite G] {M H : Subgroup G}

theorem exists_weakSBlock_or_le_inf (h : TwoLocalPair M H)
    {Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hL : IsComponentOf Lbar ⊤) :
    ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧ barM M L = Lbar ∧
      (IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ H ⊓ M) := by
  obtain ⟨L, hL2, hbar⟩ := exists_isTwoPrimeComponent hL
  refine ⟨L, hL2, hbar, ?_⟩
  by_cases hLS : L ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)
  · exact Or.inr (h.inf_eq_inf_normalizer_twoCore ▸ le_inf hL2.le hLS)
  · exact Or.inl ⟨hL2, hLS⟩

theorem card_le_pRank_three_of_blocks_of_le (h : TwoLocalPair M H)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {A : Subgroup G} (hAM : A ≤ M) {ι : Type} [Finite ι] (L : ι → Subgroup G)
    (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i)) (hinj : Function.Injective L)
    (hA : ∀ i, H ⊓ M ⊓ L i ≤ A) : Nat.card ι ≤ Open.pRank 3 A := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  let Lbar : ι → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun j => barM M (L j)
  have hLbarinj : Function.Injective Lbar := fun i j hij =>
    hinj ((hL i).toIsTwoPrimeComponent.eq_of_barM_eq (hL j).toIsTwoPrimeComponent hij)
  choose y hy using fun j => hB3 (L j) (hL j)
  have hyM : ∀ j, y j ∈ M := fun j => (hL j).le (hy j).1.2
  let ybar : ι → ↥M ⧸ CFSG.pCore 2 ↥M := fun j => mk ⟨y j, hyM j⟩
  have hyA : ∀ j, ybar j ∈ barM M A := fun j =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (hA j ⟨hKeq ▸ ⟨hyM j, (hy j).1.1⟩, (hy j).1.2⟩))
  have hyL : ∀ j, ybar j ∈ Lbar j := fun j =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hy j).1.2)
  have hyq : ∀ j, IsPGroup 3 (Subgroup.zpowers (ybar j)) := by
    intro j
    obtain ⟨k, hk⟩ := (hy j).2.1 ⟨y j, Subgroup.mem_zpowers _⟩
    have hk' : y j ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
    have : (⟨y j, hyM j⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
    simp only [ybar, ← map_pow, this, map_one]
  have hyZ : ∀ j, ∃ l ∈ Lbar j, ybar j * l ≠ l * ybar j := by
    intro j
    obtain ⟨l, hl, hlQ⟩ := (hy j).2.2
    have hlM : l ∈ M := (hL j).le hl
    refine ⟨mk ⟨l, hlM⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl), fun he => ?_⟩
    apply hlQ
    have h1 : mk (⟨y j, hyM j⟩ * ⟨l, hlM⟩ * (⟨y j, hyM j⟩)⁻¹ * (⟨l, hlM⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change ybar j * mk ⟨l, hlM⟩ * (ybar j)⁻¹ * (mk ⟨l, hlM⟩)⁻¹ = 1
      rw [he]
      group
    simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  exact (le_pRank_of_components Nat.prime_three Lbar (fun j => (hL j).component) hLbarinj
    (barM M A) ybar hyA hyL hyq hyZ).trans
    (pRank_barM_le Nat.prime_three (by decide) M A hAM)

theorem card_le_pRank_three_of_blocks (h : TwoLocalPair M H)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {ι : Type} [Finite ι] (L : ι → Subgroup G) (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i))
    (hinj : Function.Injective L) : Nat.card ι ≤ Open.pRank 3 (H ⊓ M) :=
  h.card_le_pRank_three_of_blocks_of_le hB3 inf_le_right L hL hinj fun _ => inf_le_left

theorem le_pRank_three_of_injective_conj (h : TwoLocalPair M H)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {m : ℕ} (g : Fin m → G)
    (hgK : ∀ j, g j ∈ H ⊓ M)
    (hinj : Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank 3 (H ⊓ M) := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have h1 := h.card_le_pRank_three_of_blocks hB3
    (fun j => L.map (MulAut.conj (g j)).toMonoidHom)
    (fun j => hL.map_conj (hgK j).2 (hKeq ▸ hgK j).2) hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h1

theorem relIndex_le_pRank_three (h : TwoLocalPair M H)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {A : Subgroup G} (hAK : A ≤ H ⊓ M) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A ≤ Open.pRank 3 (H ⊓ M) := by
  set NA := (A ⊓ Subgroup.normalizer (L : Set G)).subgroupOf A with hNA
  have hidx : (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A = Nat.card (↥A ⧸ NA) := by
    rw [Subgroup.relIndex, Subgroup.index]
  rw [hidx]
  have : Finite (↥A ⧸ NA) := inferInstance
  set m := Nat.card (↥A ⧸ NA)
  let e : Fin m ≃ (↥A ⧸ NA) := (Finite.equivFin _).symm
  let g : Fin m → G := fun j => ((Quotient.out (e j) : A) : G)
  have hgK : ∀ j, g j ∈ H ⊓ M := fun j => hAK (Quotient.out (e j)).2
  refine h.le_pRank_three_of_injective_conj hB3 hL g hgK ?_
  intro i j hij
  simp only at hij
  have hn : (g j)⁻¹ * g i ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj ((g j)⁻¹ * g i)).toMonoidHom = L
    rw [map_conj_mul_eq, hij, ← map_conj_mul_eq, inv_mul_cancel]
    ext x
    simp
  have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ NA := by
    refine Subgroup.mem_subgroupOf.mpr ⟨A.mul_mem (A.inv_mem (Quotient.out (e j)).2)
      (Quotient.out (e i)).2, ?_⟩
    simpa [g] using hn
  have heq : (e j) = (e i) := by
    rw [← Quotient.out_eq (e j), ← Quotient.out_eq (e i)]
    exact QuotientGroup.eq.mpr hmem
  exact e.injective heq.symm

theorem le_pRank_three_of_not_mem_normalizer (h : TwoLocalPair M H)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {r : ℕ} [Fact r.Prime] {g : G} (hgK : g ∈ H ⊓ M) (hg : IsPGroup r (Subgroup.zpowers g))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hgL : g ∉ Subgroup.normalizer (L : Set G)) : r ≤ Open.pRank 3 (H ⊓ M) := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hgM : g ∈ M := hgK.2
  have hgS : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hgK).2
  have h1 := h.card_le_pRank_three_of_blocks hB3
    (fun j : Fin r => L.map (MulAut.conj (g ^ (j : ℕ))).toMonoidHom)
    (fun j => hL.map_conj (M.pow_mem hgM _) (Subgroup.pow_mem _ hgS _))
    (injective_conj_pow_of_not_mem_normalizer hg hgL)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h1

omit [Finite G] in
theorem card_blockPL_map_conj (h : TwoLocalPair M H) {L : Subgroup G} {k : G} (hk : k ∈ H ⊓ M) :
    Nat.card (blockPL M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom)) =
      Nat.card (blockPL M (pCoreOf 2 H) L) := by
  have hkS : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h.inf_eq_inf_normalizer_twoCore ▸ hk).2
  have hN : (Subgroup.normalizer (pCoreOf 2 H : Set G)).map (MulAut.conj k).toMonoidHom =
      Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkS)
  have he : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L.map (MulAut.conj k).toMonoidHom =
      (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L).map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective, hN]
  rw [blockPL, he, barM_map_conj hk.2,
    Subgroup.card_map_of_injective (MulAut.conj _).injective]

end TwoLocalPair

variable {G : Type} [Group G] [Finite G]

theorem TwoLocalPhaseThree.mk_mem_blockPL_sup {M H : Subgroup G} (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h86 : Asc81bEightSix) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hb : ∀ l ∈ barM M L,
      (∀ s ∈ barM M (pCoreOf 2 H), ∃ s' ∈ barM M (pCoreOf 2 H), ∀ y ∈ barM M L,
        (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
      l ∈ blockPL M (pCoreOf 2 H) L) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hC : C ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) {x : M}
    (hxK : (x : G) ∈ H ⊓ M) (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ barM M L ⊔ C) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ blockPL M (pCoreOf 2 H) L ⊔ C := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  have hxS : (x : G) ∈ Subgroup.normalizer (S : Set G) := (hKeq ▸ hxK).2
  have hx' : mk x ∈ ((Lb ⊔ C : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Lb C
    (hC.trans (Subgroup.centralizer_le_normalizer _))] at hx'
  obtain ⟨_, ⟨l, hl, rfl⟩, c, hc, hlc⟩ := hx'
  have hlb : mk l ∈ Lb := Subgroup.mem_map_of_mem _ hl
  have hSL : barM M S ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M S hK h.asc81bHyp _ hL.component
  have act : ∀ y ∈ Lb, mk x * y * (mk x)⁻¹ = mk l * y * (mk l)⁻¹ := by
    intro y hy
    have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.mp (hC hc) y hy
    rw [← hlc]
    calc mk l * c * y * (mk l * c)⁻¹ = mk l * (c * y) * c⁻¹ * (mk l)⁻¹ := by group
      _ = mk l * (y * c) * c⁻¹ * (mk l)⁻¹ := by rw [hcy]
      _ = mk l * y * (mk l)⁻¹ := by group
  have hlP : mk l ∈ blockPL M S L := by
    refine hb _ hlb fun s hs => ?_
    obtain ⟨σ, hσ, rfl⟩ := hs
    have hσS : (σ : G) ∈ S := Subgroup.mem_subgroupOf.mp hσ
    have hσ' : (x : G) * σ * (x : G)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS σ).mp hσS
    refine ⟨mk x * mk σ * (mk x)⁻¹, ⟨x * σ * x⁻¹, Subgroup.mem_subgroupOf.mpr hσ', by
      simp only [map_mul, map_inv]; rfl⟩, fun y hy => ?_⟩
    have hsb : mk σ ∈ barM M S := Subgroup.mem_map_of_mem _ hσ
    have hy1 : (mk l)⁻¹ * y * mk l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hlb) hy) hlb
    have hy2 : mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹ ∈ Lb :=
      (Subgroup.mem_normalizer_iff.mp (hSL hsb) _).mp hy1
    have hy3 : (mk x)⁻¹ * y * mk x = (mk l)⁻¹ * y * mk l := by
      calc (mk x)⁻¹ * y * mk x
          = (mk x)⁻¹ * (mk l * ((mk l)⁻¹ * y * mk l) * (mk l)⁻¹) * mk x := by group
        _ = (mk x)⁻¹ * (mk x * ((mk l)⁻¹ * y * mk l) * (mk x)⁻¹) * mk x := by rw [act _ hy1]
        _ = (mk l)⁻¹ * y * mk l := by group
    calc mk l * mk σ * (mk l)⁻¹ * y * (mk l * mk σ * (mk l)⁻¹)⁻¹
        = mk l * (mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹) * (mk l)⁻¹ := by group
      _ = mk x * (mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹) * (mk x)⁻¹ := (act _ hy2).symm
      _ = mk x * (mk σ * ((mk x)⁻¹ * y * mk x) * (mk σ)⁻¹) * (mk x)⁻¹ := by rw [hy3]
      _ = mk x * mk σ * (mk x)⁻¹ * y * (mk x * mk σ * (mk x)⁻¹)⁻¹ := by group
  rw [← hlc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlP) (Subgroup.mem_sup_right hc)

end CFSG.AGLEmbedding
