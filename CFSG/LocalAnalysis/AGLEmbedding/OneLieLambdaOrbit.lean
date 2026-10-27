module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThreeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZClose
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockGlue

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Orbit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.le_normalizer_of_mem [Fact p.Prime] {n e : ℕ} {Z : Subgroup G}
    (hd : D1OneLieData p P M H R Rbar K)
    (hMD : D1OneLieMData p n e P M H R (d1PlusCore p H K) Z) (hWK : d1MapPCore p M H ≤ K)
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hzL : z ∈ L) :
    H ⊓ M ≤ Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨hNle, hHN, -⟩ := hd.d1PlusCore_facts
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set L₂ := L.map (MulAut.conj k).toMonoidHom with hL₂def
  have hL₂ : IsTwoPrimeComponent M L₂ := hL.map_conj hk.2
  have hbar : barM M L ≠ barM M L₂ := fun h => hne (hL.eq_of_barM_eq hL₂ h).symm
  have hzM : z ∈ M := hL.le hzL
  have hkzM : k * z * k⁻¹ ∈ M := M.mul_mem (M.mul_mem hk.2 hzM) (M.inv_mem hk.2)
  have hkzL : k * z * k⁻¹ ∈ L₂ := ⟨z, hzL, by simp⟩
  have hkzN : k * z * k⁻¹ ∈ d1PlusCore p H K :=
    (Subgroup.mem_normalizer_iff.mp (hHN hk.1) z).mp hzN
  set kb := mk ⟨k, hk.2⟩ with hkb
  set y₁ := mk ⟨z, hzM⟩ with hy₁
  set y₂ := mk ⟨k * z * k⁻¹, hkzM⟩ with hy₂
  have hy₂eq : y₂ = kb * y₁ * kb⁻¹ := by
    rw [hy₂, hkb, hy₁, ← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨l, hl, hl₁⟩ := hd.exists_mul_ne_of_mem hWK hzR hzN hzp hL hzL
  have hl₂ : kb * l * kb⁻¹ ∈ barM M L₂ := by
    rw [hL₂def, barM_map_conj hk.2]
    exact ⟨l, hl, rfl⟩
  have hne₂ : y₂ * (kb * l * kb⁻¹) ≠ kb * l * kb⁻¹ * y₂ := by
    intro he
    apply hl₁
    rw [hy₂eq] at he
    have he' : kb * (y₁ * l) * kb⁻¹ = kb * (l * y₁) * kb⁻¹ := by
      calc kb * (y₁ * l) * kb⁻¹ = kb * y₁ * kb⁻¹ * (kb * l * kb⁻¹) := by group
        _ = kb * l * kb⁻¹ * (kb * y₁ * kb⁻¹) := he
        _ = kb * (l * y₁) * kb⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel he')
  have hy₁N : y₁ ∈ barM M (d1PlusCore p H K) := ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzN, rfl⟩
  have hy₂N : y₂ ∈ barM M (d1PlusCore p H K) :=
    ⟨⟨k * z * k⁻¹, hkzM⟩, Subgroup.mem_subgroupOf.mpr hkzN, rfl⟩
  have hzp1 : z ^ p ^ 1 = 1 := by rw [pow_one, ← hzp]; exact pow_orderOf_eq_one z
  have hy₁p : y₁ ^ p ^ 1 = 1 := by
    rw [hy₁, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ p ^ 1 = 1 := Subtype.ext (by simpa using hzp1)
    rw [this, map_one]
  have hy₂p : y₂ ^ p ^ 1 = 1 := by
    rw [hy₂eq, conj_pow, hy₁p, mul_one, mul_inv_cancel]
  have h2 := stmtComponentRank hp (ι := Fin 2) ![barM M L, barM M L₂]
    (fun i => by fin_cases i <;> simp [hL.component, hL₂.component])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp_all)
    (barM M (d1PlusCore p H K)) ![y₁, y₂]
    (fun i => by fin_cases i <;> simp [hy₁N, hy₂N])
    (fun i => by
      fin_cases i
      · exact ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
      · exact ⟨⟨k * z * k⁻¹, hkzM⟩, Subgroup.mem_subgroupOf.mpr hkzL, rfl⟩)
    (fun i => by
      fin_cases i
      · exact isPGroup_zpowers_of_pow_eq_one hy₁p
      · exact isPGroup_zpowers_of_pow_eq_one hy₂p)
    (fun i => by
      fin_cases i
      · exact ⟨l, hl, hl₁⟩
      · exact ⟨kb * l * kb⁻¹, hl₂, hne₂⟩)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h3 := pRank_barM_le hp hp2 M (d1PlusCore p H K) (hNle.trans inf_le_right)
  have h4 := hMD.pRank_plus_le_one
  omega

theorem D1OneLieData.le_pCorePreimage [Fact p.Prime] {n e : ℕ} {Z : Subgroup G}
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneLieData p P M H R Rbar K)
    (hMD : D1OneLieMData p n e P M H R (d1PlusCore p H K) Z)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) : Z ≤ pCorePreimage p M := by
  have h3 := hd.toPhaseThree hK
  rcases hMD.dichotomy _ (h3.pCorePreimage_le_inf h84 hD2)
    (inf_le_right.trans (le_normalizer_pCorePreimage p M)) with hZY | hYN
  · exact hZY
  · exfalso
    apply (hd.d1MapPCore_facts hK h84 hD2).2.2.2.2.mp hY
    rw [eq_bot_iff]
    rintro w ⟨hwY, -, hwK⟩
    obtain ⟨y, hy, rfl⟩ := hwY
    obtain ⟨y', hy', hyy'⟩ := hYN (Subgroup.mem_subgroupOf.mp hy)
    have hyy : y' = y := Subtype.ext hyy'
    subst hyy
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) p) y' ∈
        K ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := ⟨hwK, hy'⟩
    rwa [hd.inf_centralizer_eq_bot] at hmem

theorem D1OneLieData.inf_le_d1PlusCore [Fact p.Prime] {n e : ℕ} {Z : Subgroup G}
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneLieData p P M H R Rbar K)
    (hMD : D1OneLieMData p n e P M H R (d1PlusCore p H K) Z)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hLK : H ⊓ M ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ barM M L →
      A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup p A →
        IsCyclic A) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ d1PlusCore p H K := by
  have hp : p.Prime := Fact.out
  have h3 := hd.toPhaseThree hK
  set Y := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hYdef
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases hMD.dichotomy Y inf_le_left hYn with hZY | hYN
  · exfalso
    have hLk : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) ≤ barM M L :=
      fun k hk => by
        have h : L.map (MulAut.conj k).toMonoidHom = L :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLK hk)
        rw [h]
    have hZL : barM M Z ≤ barM M L := barM_le_of_le_preimage
      ((hZY.trans inf_le_right).trans (blockClosure_le_preimage inf_le_right hL hLk))
    have hZO : barM M Z ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
      (barM_mono (hd.le_pCorePreimage hK h84 hD2 hMD hY)).trans (barM_preimage _).le
    have hZC := hZO.trans (pCore_le_centralizer_component p hL.component)
    have hZel := hMD.isElemAbelian_barM'
    have hZp : IsPGroup p (barM M Z) := fun x => ⟨1, Subtype.ext (by simpa using hZel.2 x x.2)⟩
    exact not_isCyclic_of_isElemAbelian hp hZel hMD.two_le
      (by rw [hMD.card_barM', hMD.card_eq]) (hcyc _ hZL hZC hZp)
  · rintro x ⟨hxS, hxL⟩
    refine hYN ⟨⟨h3.normalizer_twoCore_H ▸ hxS, hL.le hxL⟩, ?_⟩
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨x, hxL, by simp⟩))

theorem D1OneLieData.exists_weakSBlock_map_conj (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K) {z : G}
    (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hzL : z ∈ L) :
    ∃ m ∈ M, IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj m).toMonoidHom) := by
  have h3 := hd.toPhaseThree hK
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  by_contra hno
  push Not at hno
  have hS2 : IsPGroup 2 (barM M S) :=
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype).map _
  have hNS : barM M (Subgroup.normalizer (S : Set G)) ≤
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.map_mono (Subgroup.le_normalizer_comap M.subtype)).trans
      (Subgroup.le_normalizer_map _)
  have hcent : ∀ m ∈ M, barM M S ≤
      Subgroup.centralizer (barM M (L.map (MulAut.conj m).toMonoidHom) : Set _) := by
    intro m hm
    have hLm := hL.map_conj hm
    have hle : L.map (MulAut.conj m).toMonoidHom ≤ Subgroup.normalizer (S : Set G) := by
      by_contra hn
      exact hno m hm ⟨hLm, hn⟩
    refine le_centralizer_of_forall_commutator_mem hLm.component (barM_mono hle) hS2 hNS ?_
    intro a ha x hx
    have hx' : x * a⁻¹ * x⁻¹ ∈ barM M S :=
      (Subgroup.mem_normalizer_iff.mp (hNS hx) a⁻¹).mp ((barM M S).inv_mem ha)
    have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact (barM M S).mul_mem ha hx'
  set T := (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).normalCore with hT
  have hST : barM M S ≤ T := by
    intro s hs b
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) b
    have hs' := hcent m⁻¹ (M.inv_mem hm) hs
    rw [barM_map_conj (M.inv_mem hm)] at hs'
    have hinv : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m⁻¹, M.inv_mem hm⟩ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [hinv] at hs'
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.mp hs' _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    generalize QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩ = b at h1 ⊢
    calc l * (b * s * b⁻¹) = b * (b⁻¹ * l * b * s) * b⁻¹ := by group
      _ = b * (s * (b⁻¹ * l * b)) * b⁻¹ := by rw [h1]
      _ = b * s * b⁻¹ * l := by group
  have hzM : z ∈ M := hL.le hzL
  have hzT : mk ⟨z, hzM⟩ ∈ T := barM_nclIn_le h3.twoCore_le hST
    ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr (hd.mem_nclIn_twoCore hK h84 hD2 hY hzJ), rfl⟩
  have hzC := Subgroup.normalCore_le _ hzT
  obtain ⟨l, hl, hne⟩ := hd.exists_mul_ne_of_mem hWK hzR hzN hzp hL hzL
  exact hne (Subgroup.mem_centralizer_iff.mp hzC l hl).symm

end Orbit

end CFSG.AGLEmbedding
