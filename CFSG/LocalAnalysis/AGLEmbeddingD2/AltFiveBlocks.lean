module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveResidue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockInnerAt
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.QuasithinUnique

@[expose] def KFactBlockAltFiveSection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) ∨
      ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M S L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        ¬ E ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockAltFiveSquare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    3 ≤ Open.pRank 3 (blockPL M S L)

@[expose] def KFactBlockAltFiveSectionInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) ∨
      ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M S L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        ¬ E ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockAltFiveSquareInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    3 ≤ Open.pRank 3 (blockPL M S L)

theorem KFactBlockAltFiveSection.inner (h : KFactBlockAltFiveSection) :
    KFactBlockAltFiveSectionInner :=
  fun G _ _ M S L U hK hA hL hX hS _ => h G M S L U hK hA hL hX hS

theorem KFactBlockAltFiveSquare.inner (h : KFactBlockAltFiveSquare) :
    KFactBlockAltFiveSquareInner :=
  fun G _ _ M S L U hK hA hL hX hS _ => h G M S L U hK hA hL hX hS

instance : Coe KFactBlockAltFiveSection KFactBlockAltFiveSectionInner :=
  ⟨KFactBlockAltFiveSection.inner⟩

instance : Coe KFactBlockAltFiveSquare KFactBlockAltFiveSquareInner :=
  ⟨KFactBlockAltFiveSquare.inner⟩

theorem four_le_pRank_of_commute_of_inf_eq_bot {Y : Type*} [Group Y] [Finite Y]
    {E F : Subgroup Y} (hE : IsElemAbelian 3 E) (hF : IsElemAbelian 3 F) (hEc : Nat.card E = 3 ^ 2)
    (hFc : Nat.card F = 3 ^ 2) (hcomm : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) (hdisj : E ⊓ F = ⊥) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  have := hE.1
  have := hF.1
  let f : E × F →* Y := MonoidHom.noncommCoprod E.subtype F.subtype
    fun a b => hcomm a a.2 b b.2
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Y) * (b : Y) = 1 := hab
    have ha : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have haF : (a : Y) ∈ F := ha ▸ F.inv_mem b.2
    have ha1 : (a : Y) = 1 := by
      have : (a : Y) ∈ E ⊓ F := ⟨a.2, haF⟩
      rwa [hdisj, Subgroup.mem_bot] at this
    have hb1 : (b : Y) = 1 := by
      rw [ha1, one_mul] at hab'
      exact hab'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  refine SectionRank.le_pRank_of_injective (by norm_num) (A := E × F) ?_ ?_ ?_ f hf le_top
  · rintro ⟨a, b⟩ ⟨a', b'⟩
    exact Prod.ext (mul_comm' a a') (mul_comm' b b')
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE.2 a a.2)) (Subtype.ext (hF.2 b b.2))
  · rw [Nat.card_prod, hEc, hFc]
    norm_num

theorem three_le_pRank_of_commute_of_not_mem {Y : Type*} [Group Y] [Finite Y]
    {A E : Subgroup Y} (hEA : E ≤ A) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) {u : Y}
    (huA : u ∈ A) (hu3 : u ^ 3 = 1) (hcomm : ∀ a ∈ E, a * u = u * a) (huE : u ∉ E) :
    3 ≤ Open.pRank 3 A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu1 : u ≠ 1 := fun h => huE (h ▸ E.one_mem)
  have huC : u ∈ Subgroup.centralizer (E : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha
  have hdisj : Subgroup.zpowers u ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxu, hxE⟩
    by_contra hx1
    rw [Subgroup.mem_bot] at hx1
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers u := Subgroup.zpowers_le.mpr hxu
    have heq : Subgroup.zpowers x = Subgroup.zpowers u := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hu3 hu1,
        orderOf_eq_prime hx3 hx1]
    apply huE
    have : u ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers u
    exact (Subgroup.zpowers_le.mpr hxE) this
  have h1 := pRank_succ_le_sup_zpowers E hu3 hu1 huC hdisj
  have h2 : 2 ≤ Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three hE hEc
  exact (by omega : 3 ≤ Open.pRank 3 (E ⊔ Subgroup.zpowers u)).trans
    (SectionRank.pRank_mono (by norm_num) (sup_le hEA (Subgroup.zpowers_le.mpr huA)))

namespace D2AltData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

omit [Fact p.Prime] in
theorem orderOf_coprime_of_psi_eq_one {W : Subgroup G} {Q : Type*} [Group Q] {ψ : W →* Q}
    (hker : ψ.ker = (GLBPrimeCore p H).subgroupOf W) (n : W) (hn : ψ n = 1) :
    (orderOf n).Coprime p := by
  have hnN : (n : G) ∈ GLBPrimeCore p H := by
    have hn' : n ∈ ψ.ker := hn
    rw [hker] at hn'
    exact hn'
  have hdvd : orderOf n ∣ Nat.card (GLBPrimeCore p H) := by
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hnN
  exact Nat.Coprime.coprime_dvd_left hdvd (glbPrimeCore_coprime p H).symm

theorem psi_fst_eq_one_of_not_mem (h : D2AltData p M H R X) {c₀ c₁ s : G} {g : ℕ}
    {W : Subgroup G} {ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)}
    (hsc : AltScalar p (H ⊓ M) X c₀ c₁ s g) (hWM : W ≤ M) (hXW : X ≤ W)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker = (GLBPrimeCore p H).subgroupOf W)
    (hc₀ : ∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hnormL : barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hw₀ : (⟨c₀, hXW hsc.mem_zero⟩ : W) ∉ centralizerBar M hWM Lb) :
    ∀ w ∈ centralizerBar M hWM Lb, (ψ w).1 = 1 := by
  have hp5 := h.five_le
  have : IsSimpleGroup (alternatingGroup (Fin p)) :=
    alternatingGroup.isSimpleGroup (by simpa using hp5)
  have hZ : Subgroup.center (alternatingGroup (Fin p)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  set w₀ : W := ⟨c₀, hXW hsc.mem_zero⟩ with hw₀def
  have hw₀p : w₀ ^ p = 1 := Subtype.ext (h.elem.2 c₀ hsc.mem_zero)
  have := normal_centralizerBar hWM hnormL
  have hnormψ : ((centralizerBar M hWM Lb).map ψ).Normal :=
    Subgroup.Normal.map inferInstance ψ hsurj
  intro w hw
  refine fst_eq_one_of_normal hZ (a := (ψ w₀).1) (fun hmem => hw₀ (mem_centralizerBar_of_psi_mem
    hWM hnormL (orderOf_coprime_of_psi_eq_one hker) hw₀p ?_)) (Subgroup.mem_map_of_mem ψ hw)
  rwa [show ψ w₀ = ((ψ w₀).1, 1) from Prod.ext rfl (hc₀ w₀ rfl)]

theorem psi_snd_eq_one_of_not_mem (h : D2AltData p M H R X) {c₀ c₁ s : G} {g : ℕ}
    {W : Subgroup G} {ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)}
    (hsc : AltScalar p (H ⊓ M) X c₀ c₁ s g) (hWM : W ≤ M) (hXW : X ≤ W)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker = (GLBPrimeCore p H).subgroupOf W)
    (hc₁ : ∀ w : W, (w : G) = c₁ → (ψ w).1 = 1) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hnormL : barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hw₁ : (⟨c₁, hXW hsc.mem_one⟩ : W) ∉ centralizerBar M hWM Lb) :
    ∀ w ∈ centralizerBar M hWM Lb, (ψ w).2 = 1 := by
  have hp5 := h.five_le
  have : IsSimpleGroup (alternatingGroup (Fin p)) :=
    alternatingGroup.isSimpleGroup (by simpa using hp5)
  have hZ : Subgroup.center (alternatingGroup (Fin p)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  set w₁ : W := ⟨c₁, hXW hsc.mem_one⟩ with hw₁def
  have hw₁p : w₁ ^ p = 1 := Subtype.ext (h.elem.2 c₁ hsc.mem_one)
  have := normal_centralizerBar hWM hnormL
  have hnormψ : ((centralizerBar M hWM Lb).map ψ).Normal :=
    Subgroup.Normal.map inferInstance ψ hsurj
  intro w hw
  refine snd_eq_one_of_normal hZ (b := (ψ w₁).2) (fun hmem => hw₁ (mem_centralizerBar_of_psi_mem
    hWM hnormL (orderOf_coprime_of_psi_eq_one hker) hw₁p ?_)) (Subgroup.mem_map_of_mem ψ hw)
  rwa [show ψ w₁ = (1, (ψ w₁).2) from Prod.ext (hc₁ w₁ rfl) rfl]

end D2AltData

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem mul_comm_of_components_ne {Y : Type*} [Group Y] [Finite Y] {L L' : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hne : L ≠ L') {a b : Y} (ha : a ∈ L)
    (hb : b ∈ L') : a * b = b * a := by
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL hL' hne
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h ha
  exact (Subgroup.mem_centralizer_iff.mp hle b hb).symm

theorem AGLPair.false_of_block_conj_ne {p : ℕ} {M H R : Subgroup G} (hpair : AGLPair p M H R)
    (h2K : Open.pRank 3 (H ⊓ M) ≤ 2) (hM3 : Open.pRank 3 M ≤ 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {s : G} (hs : s ∈ H ⊓ M)
    (hne : barM M (L.map (MulAut.conj s).toMonoidHom) ≠ barM M L)
    (halt : (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) ∨
      ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M (pCoreOf 2 H) L ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
        ¬ E ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  have hsM : s ∈ M := hs.2
  have hKeq := hpair.inf_eq_inf_normalizer_twoCore
  have hsS : s ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hs).2
  set σ := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩) with hσ
  have hL' : IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj s).toMonoidHom) :=
    hL.map_conj hsM hsS
  have hbar : barM M (L.map (MulAut.conj s).toMonoidHom) = (barM M L).map σ.toMonoidHom :=
    barM_map_conj hsM L
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  have hLb' : IsComponentOf (barM M (L.map (MulAut.conj s).toMonoidHom)) ⊤ := hL'.component
  have hcomm : ∀ {a b}, a ∈ barM M L → b ∈ barM M (L.map (MulAut.conj s).toMonoidHom) →
      a * b = b * a := fun ha hb => mul_comm_of_components_ne hLb hLb' hne.symm ha hb
  have hσL : ∀ {a}, a ∈ barM M L → σ a ∈ barM M (L.map (MulAut.conj s).toMonoidHom) :=
    fun ha => hbar ▸ ⟨_, ha, rfl⟩
  have hsK : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ ∈ barM M (H ⊓ M) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hPK : blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
    barM_mono (by rw [hKeq]; exact le_inf (inf_le_right.trans hL.le) inf_le_left)
  rcases halt with ⟨E, hEL, hE, hEc, hEZ⟩ | ⟨E, hEP, hE, hEc, hEZ⟩
  ·
    have hE' : IsElemAbelian 3 (E.map σ.toMonoidHom) := SectionRank.isElemAbelian_map hE _
    have hE'c : Nat.card (E.map σ.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective σ.injective, hEc]
    have h4 := four_le_pRank_of_commute_of_inf_eq_bot hE hE' hEc hE'c
      (fun a ha b hb => by
        obtain ⟨b', hb', rfl⟩ := hb
        exact hcomm (hEL ha) (hσL (hEL hb')))
      (by
        rw [eq_bot_iff]
        rintro x ⟨hxE, ⟨y, hy, rfl⟩⟩
        have hxC : σ.toMonoidHom y ∈ Subgroup.centralizer (barM M L : Set _) :=
          Subgroup.mem_centralizer_iff.mpr fun l hl => hcomm hl (hσL (hEL hy))
        have : σ.toMonoidHom y ∈ E ⊓ Subgroup.centralizer (barM M L : Set _) := ⟨hxE, hxC⟩
        rwa [hEZ] at this)
    have hMbar : barM M M = ⊤ := by
      rw [barM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        QuotientGroup.range_mk']
    have h4M : 4 ≤ Open.pRank 3 M := by
      have := pRank_barM_le Nat.prime_three (by decide) M M le_rfl
      rw [hMbar] at this
      omega
    omega
  ·
    obtain ⟨u, huE, huC⟩ := Set.not_subset.mp hEZ
    have huL : u ∈ barM M L := (hEP.trans (barM_mono inf_le_right)) huE
    have hu3 : u ^ 3 = 1 := hE.2 u huE
    have hσuK : σ u ∈ barM M (H ⊓ M) := by
      rw [hσ, MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsK (hPK (hEP huE))) (Subgroup.inv_mem _ hsK)
    have hσu3 : σ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
    have hσuE : σ u ∉ E := by
      intro hσu
      apply huC
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : σ u * σ l = σ l * σ u :=
        (hcomm ((hEP.trans (barM_mono inf_le_right)) hσu) (hσL hl)).symm ▸ rfl
      have h2 : σ (l * u) = σ (u * l) := by
        rw [map_mul, map_mul]
        exact (hcomm ((hEP.trans (barM_mono inf_le_right)) hσu) (hσL hl)).symm
      exact σ.injective h2
    have h3 := three_le_pRank_of_commute_of_not_mem (hEP.trans hPK) hE hEc hσuK hσu3
      (fun a ha => hcomm ((hEP.trans (barM_mono inf_le_right)) ha) (hσL huL)) hσuE
    have := h3.trans (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
    omega

end Assembly

theorem false_of_altFiveBlock {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner) (hglob : AGLGlobal G) (hD1 : D1For G)
    (hNX : NoXBlockFor G) {P : Sylow 5 G} {M A H : Subgroup G} (hesc : D2Escape 5 P M A H A)
    {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 5)}
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
    (hK : D2AlmostSimple 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K)
    (e : K ≃* alternatingGroup (Fin (2 * 5))) (hM3 : Open.pRank 3 M ≤ 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hA : ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    False := by
  have hdata : D2AltData 5 M H A A := hesc.altData_of_alt hglob hRbar hK e le_rfl
  have hpair := hdata.pair
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L :=
    fun L hL => hpair.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  obtain ⟨hnot1, -⟩ := hpair.nineThree_not_one h85 hNX hL
  have hsyl := hpair.not_isSylowTwoOf_inf h85 hNX hL
  have hbL := hpair.blockInnerNormalizerAt h84 h86 hNX hL
  obtain ⟨c₀, c₁, s, g, W, ψ, hsc, hWK, hW, hXW, -, hsurj, hker, hc₀, hc₁, -⟩ := hdata.perfect
  have hWM : W ≤ M := hWK.trans inf_le_right
  have hKeq := hpair.inf_eq_inf_normalizer_twoCore
  have hWS : W ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hWK).trans inf_le_right
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  have hinner := hpair.le_sup_centralizer_component hD1 hα hSch hB3 hWK hW hLb
  have hnormL := hpair.le_normalizer_component hD1 hα hB3 hWK hW hLb
  have h2K := hesc.pRank_three_inf_le_two_of_alt_five hglob hD1 hRbar hK e rfl
  have hPK : blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
    barM_mono (by rw [hKeq]; exact le_inf (inf_le_right.trans hL.le) inf_le_left)
  set w₀ : W := ⟨c₀, hXW hsc.mem_zero⟩ with hw₀
  set w₁ : W := ⟨c₁, hXW hsc.mem_one⟩ with hw₁
  have hs : s ∈ H ⊓ M := hsc.mem
  set σ := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hs.2⟩) with hσ
  have hσc : σ (barElt M hWM w₀) = barElt M hWM w₁ := by
    rw [hσ, MulAut.conj_apply]
    simp only [barElt, MonoidHom.coe_comp, Function.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [w₀, w₁, hsc.conj_zero]
  have hPK3 : ∀ B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), B ≤ barM M (H ⊓ M) →
      3 ≤ Open.pRank 3 B → False := fun B hB h3 => by
    have := (h3.trans (SectionRank.pRank_mono (by norm_num) hB)).trans
      (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
    omega
  by_cases h0 : w₀ ∈ centralizerBar M hWM (barM M L)
  · by_cases h1 : w₁ ∈ centralizerBar M hWM (barM M L)
    ·
      apply hA
      rintro _ ⟨m, hmA, rfl⟩
      have hmA' : (m : G) ∈ A := Subgroup.mem_subgroupOf.mp hmA
      obtain ⟨i, j, hij⟩ := hsc.exists_zpow_eq hdata.elem.1 hmA'
      have hm : m = Subgroup.inclusion hWM (w₀ ^ i * w₁ ^ j) :=
        Subtype.ext (by simp [w₀, w₁, hij])
      have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m =
          barElt M hWM w₀ ^ i * barElt M hWM w₁ ^ j := by
        rw [hm, ← map_zpow, ← map_zpow, ← map_mul]
        rfl
      rw [hmk]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h0 _) (Subgroup.zpow_mem _ h1 _)
    ·
      have hφC : ∀ w ∈ centralizerBar M hWM (barM M L), ((MonoidHom.snd _ _).comp ψ) w = 1 :=
        fun w hw => hdata.psi_snd_eq_one_of_not_mem hsc hWM hXW hsurj hker hc₁ hnormL h1 w hw
      have halt := hKB G M (pCoreOf 2 H) L W hpair.isKGroup.1 hpair.asc81bHyp hL hnot1 hsyl hbL
        hWM hWS hinner _ (Prod.snd_surjective.comp hsurj) hφC
      refine hpair.false_of_block_conj_ne h2K hM3 hL hs (fun heq => h1 ?_) halt
      have h0' : barElt M hWM w₀ ∈ Subgroup.centralizer (barM M L : Set _) := h0
      change barElt M hWM w₁ ∈ Subgroup.centralizer (barM M L : Set _)
      rw [← hσc, ← heq, barM_map_conj hs.2 L, Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp h0' l hl
      change σ l * σ (barElt M hWM w₀) = σ (barElt M hWM w₀) * σ l
      rw [← map_mul, ← map_mul, hcomm]
  · by_cases h1 : w₁ ∈ centralizerBar M hWM (barM M L)
    ·
      have hφC : ∀ w ∈ centralizerBar M hWM (barM M L), ((MonoidHom.fst _ _).comp ψ) w = 1 :=
        fun w hw => hdata.psi_fst_eq_one_of_not_mem hsc hWM hXW hsurj hker hc₀ hnormL h0 w hw
      have halt := hKB G M (pCoreOf 2 H) L W hpair.isKGroup.1 hpair.asc81bHyp hL hnot1 hsyl hbL
        hWM hWS hinner _ (Prod.fst_surjective.comp hsurj) hφC
      refine hpair.false_of_block_conj_ne h2K hM3 hL hs (fun heq => h0 ?_) halt
      have h1' : barElt M hWM w₁ ∈ Subgroup.centralizer (barM M L : Set _) := h1
      rw [← heq, barM_map_conj hs.2 L, ← hσc] at h1'
      change barElt M hWM w₀ ∈ Subgroup.centralizer (barM M L : Set _)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcomm := Subgroup.mem_centralizer_iff.mp h1' (σ l) ⟨l, hl, rfl⟩
      change σ l * σ (barElt M hWM w₀) = σ (barElt M hWM w₀) * σ l at hcomm
      rw [← map_mul, ← map_mul] at hcomm
      exact σ.injective hcomm
    ·
      have hψ1 : ∀ w ∈ centralizerBar M hWM (barM M L), ψ w = 1 := fun w hw =>
        Prod.ext (hdata.psi_fst_eq_one_of_not_mem hsc hWM hXW hsurj hker hc₀ hnormL h0 w hw)
          (hdata.psi_snd_eq_one_of_not_mem hsc hWM hXW hsurj hker hc₁ hnormL h1 w hw)
      exact hPK3 _ hPK (hKS G M (pCoreOf 2 H) L W hpair.isKGroup.1 hpair.asc81bHyp hL hnot1 hsyl
        hbL hWM hWS hinner ψ hsurj hψ1)

theorem d2AltFiveBlock_of (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner) : D2AltFiveBlock := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩ L hL hA
  subst hp5
  have hM3 : Open.pRank 3 M ≤ 3 := by
    by_cases h3 : 3 ∈ GLBBetaFour G
    · have := hesc.pRank_three_M_le_two_of_alt hglob.toAGLGlobal hD1 hK e le_rfl hβ h3
      omega
    · by_contra hlt
      exact h3 ⟨Nat.prime_three, by norm_num,
        prime_dvd_card_of_positive_rank 3 Nat.prime_three M (by omega),
        (by omega : 4 ≤ Open.pRank 3 M).trans
          (le_csSup (twoLocalRank_bddAbove 3 Nat.prime_three) ⟨M, hesc.maxTwoLocal_M.1, rfl⟩)⟩
  exact false_of_altFiveBlock hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKB hKS hglob.toAGLGlobal hD1
    (hD2.noXBlockFor hglob.toD1Global) hesc hRbar hK e hM3 hL hA

end CFSG.AGLEmbeddingD2
