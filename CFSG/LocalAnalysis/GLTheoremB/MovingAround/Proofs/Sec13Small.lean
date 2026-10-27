module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_pGroup_aux {p : ℕ} [Fact p.Prime] {M A B : Subgroup G}
    (hAM : A ≤ M) (hA : IsPGroup p ↥A) (hBM : B ≤ M) (hB : IsPGroup p ↥B) :
    ∃ y ∈ M, IsPGroup p ↥(A ⊔ GLBConj y B) := by
  have hAm : IsPGroup p ↥(A.subgroupOf M) := hA.comap_of_injective M.subtype Subtype.val_injective
  have hBm : IsPGroup p ↥(B.subgroupOf M) := hB.comap_of_injective M.subtype Subtype.val_injective
  obtain ⟨QB, hQB⟩ := IsPGroup.exists_le_sylow hBm
  obtain ⟨QA, hQA⟩ := IsPGroup.exists_le_sylow hAm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M QB QA
  have key : ∀ b ∈ (QB : Subgroup M), MulAut.conj g b ∈ (QA : Subgroup M) := by
    intro b hb
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hb
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, ?_⟩
  have hsub : A ⊔ GLBConj (g : G)⁻¹ B ≤ (QA : Subgroup M).map M.subtype := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨⟨a, hAM ha⟩, hQA (Subgroup.mem_subgroupOf.2 ha), rfl⟩
    · intro x hx
      have hb : (g : G)⁻¹ * x * (g : G) ∈ B := by
        have := (mem_gLBConj (g := (g : G)⁻¹) (y := x) (H := B)).1 hx
        simpa using this
      have hxM : x ∈ M := by
        have h1 : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
        rw [h1]
        exact M.mul_mem (M.mul_mem g.2 (hBM hb)) (M.inv_mem g.2)
      have hmem : (⟨(g : G)⁻¹ * x * (g : G), hBM hb⟩ : M) ∈ (QB : Subgroup M) :=
        hQB (Subgroup.mem_subgroupOf.2 hb)
      have hk := key _ hmem
      have heq : MulAut.conj g ⟨(g : G)⁻¹ * x * (g : G), hBM hb⟩ = ⟨x, hxM⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply]
        group
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      rw [← heq]
      exact hk
  have hQG : IsPGroup p ↥((QA : Subgroup M).map M.subtype) :=
    QA.isPGroup'.map M.subtype
  exact IsPGroup.to_le hQG hsub

theorem exists_conj_pGroup_holds : Exists_conj_pGroupStatement := by
  intro G _ _ m p B M h A hA hAM
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hB : IsBOneMax p B := h.bOne
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hBp : IsPGroup p ↥B := IsPGroup.iff_card.2 ⟨m, hS.card_eq hB⟩
  have hAp : IsPGroup p ↥A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 (g : G) g.2)⟩
  exact exists_conj_pGroup_aux hAM hAp hBM hBp

end Sylow

section Prop121

variable {G : Type} [Group G] [Finite G]

private theorem le_pCoreOf_two_of_normal {C N : Subgroup G} (hNC : N ≤ C)
    (hn : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hN : IsPGroup 2 ↥N) : N ≤ pCoreOf 2 C := by
  have hN'n : (N.subgroupOf C).Normal := ⟨fun n hn' g => Subgroup.mem_subgroupOf.2 (by
    have := hn (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.1 hn')
    simpa using this)⟩
  have hN'p : IsPGroup 2 ↥(N.subgroupOf C) := fun x => by
    obtain ⟨k, hk⟩ := hN ⟨x.1, Subgroup.mem_subgroupOf.1 x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hle : N.subgroupOf C ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hN'n, hN'p⟩
  intro x hx
  exact ⟨⟨x, hNC hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

private theorem conj_mem_centralizer_singleton {a c x : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G))
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) :
    c * x * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc hx ⊢
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hc]
      _ = a * c⁻¹ := by group
  calc c * x * c⁻¹ * a = c * x * (c⁻¹ * a) := by group
    _ = c * x * (a * c⁻¹) := by rw [hc']
    _ = c * (x * a) * c⁻¹ := by group
    _ = c * (a * x) * c⁻¹ := by rw [hx]
    _ = c * a * x * c⁻¹ := by group
    _ = a * c * x * c⁻¹ := by rw [hc]
    _ = a * (c * x * c⁻¹) := by group

theorem prop121_cor_of (hc : Prop121_of_cexStatement) : Prop121_corStatement := by
  intro G _ _ m p B M E A h a ha ha1
  have h121 : pCoreOf 2 (alphaOf p M ⊓ Cg a) ≤ pCoreOf 2 (Cg a) := by
    by_contra hcon
    exact hc (⟨h, ⟨ha, ha1⟩, hcon⟩ : Cex121 G m p B M E A a)
  have hαM : alphaOf p M ≤ M :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      (iSup_le fun J => iSup_le fun hJ => hJ.2.1)
  have hpM : pCoreOf 2 M ≤ alphaOf p M := le_sup_left
  have hNH : pCoreOf 2 M ⊓ Cg a ≤ alphaOf p M ⊓ Cg a :=
    inf_le_inf_right _ hpM
  have hNp : IsPGroup 2 ↥(pCoreOf 2 M ⊓ Cg a) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hcN : ∀ c ∈ alphaOf p M ⊓ Cg a, ∀ x ∈ pCoreOf 2 M ⊓ Cg a,
      c * x * c⁻¹ ∈ pCoreOf 2 M ⊓ Cg a := by
    intro c hc' x hx
    have hcM : c ∈ M := hαM hc'.1
    have hnorm : c ∈ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
      le_normalizer_pCoreOf 2 M hcM
    refine ⟨?_, conj_mem_centralizer_singleton hc'.2 hx.2⟩
    exact (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx.1
  have hcore : pCoreOf 2 M ⊓ Cg a ≤ pCoreOf 2 (alphaOf p M ⊓ Cg a) :=
    le_pCoreOf_two_of_normal hNH hcN hNp
  exact hcore.trans h121

end Prop121

section Conj

variable {G : Type} [Group G] [Finite G]

private theorem card_gLBConj' (y : G) (H : Subgroup G) : Nat.card (GLBConj y H) = Nat.card H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective

private theorem gLBConj_fix_of_mem' {M : Subgroup G} {y : G} (hy : y ∈ M) : GLBConj y M = M :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)

private theorem gLBConj_le_iff' (g : G) {X Y : Subgroup G} :
    GLBConj g X ≤ Y ↔ X ≤ GLBConj g⁻¹ Y := by
  constructor
  · intro h
    have h' := gLBConj_mono g⁻¹ h
    rwa [gLBConj_inv_gLBConj] at h'
  · intro h
    have h' := gLBConj_mono g h
    rwa [gLBConj_gLBConj_inv] at h'

private theorem centralizer_singleton_gLBConj' (g b : G) :
    Subgroup.centralizer ({g⁻¹ * b * g} : Set G) =
      GLBConj g (Subgroup.centralizer ({b} : Set G)) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc (g * y * g⁻¹) * b = g * (y * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * y) * g⁻¹ := by rw [h]
      _ = b * (g * y * g⁻¹) := by group
  · intro h
    calc y * (g⁻¹ * b * g) = g⁻¹ * ((g * y * g⁻¹) * b) * g := by group
      _ = g⁻¹ * (b * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * b * g) * y := by group

private theorem gLBConj_inv_centralizer_singleton (g b : G) :
    GLBConj g⁻¹ (Subgroup.centralizer ({g⁻¹ * b * g} : Set G)) =
      Subgroup.centralizer ({b} : Set G) := by
  rw [centralizer_singleton_gLBConj', gLBConj_inv_gLBConj]

private theorem sl_gLBConj {p : ℕ} {B L : Subgroup G} {b : G}
    (h : IsStronglyLocallyOneBalanced p B b L) (g : G) :
    IsStronglyLocallyOneBalanced p (GLBConj g B) (g⁻¹ * b * g) (GLBConj g L) := by
  intro S hS hcop hBS
  have hSS : S = GLBConj g (GLBConj g⁻¹ S) := (gLBConj_gLBConj_inv g S).symm
  have hcard : Nat.card (GLBConj g⁻¹ S) = Nat.card S := card_gLBConj' g⁻¹ S
  have hN : GLBConj g⁻¹ (Subgroup.normalizer (GLBConj g L : Set G)) =
      Subgroup.normalizer (L : Set G) := by
    rw [gLBConj_normalizer g⁻¹ (GLBConj g L), gLBConj_inv_gLBConj]
  have hS0N : GLBConj g⁻¹ S ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hN]
    exact gLBConj_mono g⁻¹ (le_inf_iff.1 hS).1
  have hS0C : GLBConj g⁻¹ S ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [← gLBConj_inv_centralizer_singleton g b]
    exact gLBConj_mono g⁻¹ (le_inf_iff.1 hS).2
  have hB0 : B ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((GLBConj g⁻¹ S : Subgroup G) : Set G) := by
    rw [← gLBConj_normalizer g⁻¹ S, ← gLBConj_le_iff' g]
    exact (le_inf (gLBConj_mono g inf_le_left)
      ((gLBConj_mono g inf_le_right).trans (gLBConj_normalizer g L).le)).trans hBS
  have hL := h (GLBConj g⁻¹ S) (le_inf hS0N hS0C) (by rw [hcard]; exact hcop) hB0
  rw [hSS, glaPPrimeCoreOf_gLBConj]
  have hcomm : GLBConj g ⁅L, GLBConj g⁻¹ S⁆ = ⁅GLBConj g L, GLBConj g (GLBConj g⁻¹ S)⁆ :=
    Subgroup.map_commutator (f := (MulAut.conj g⁻¹).toMonoidHom) (H₁ := L) (H₂ := GLBConj g⁻¹ S)
  calc ⁅GLBConj g L, GLBConj g (GLBConj g⁻¹ S)⁆ = GLBConj g ⁅L, GLBConj g⁻¹ S⁆ := hcomm.symm
    _ ≤ GLBConj g (GLAPPrimeCoreOf p L) := gLBConj_mono g hL

private theorem lambdaOf_gLBConj_le {p : ℕ} (B : Subgroup G) (b g : G) :
    lambdaOf p (GLBConj g B) (g⁻¹ * b * g) ≤ GLBConj g (lambdaOf p B b) := by
  unfold lambdaOf
  apply sSup_le
  rintro L' ⟨hL'comp, hL'nb⟩
  have hcomp : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) (GLBConj g⁻¹ L') := by
    have h := glaPComponent_gLBConj hL'comp g⁻¹
    rwa [gLBConj_inv_centralizer_singleton g b] at h
  have hnot : ¬ IsStronglyLocallyOneBalanced p B b (GLBConj g⁻¹ L') := fun hsl =>
    hL'nb (by
      have h := sl_gLBConj hsl g
      rwa [gLBConj_gLBConj_inv] at h)
  calc L' = GLBConj g (GLBConj g⁻¹ L') := (gLBConj_gLBConj_inv g L').symm
    _ ≤ GLBConj g (sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
          ¬ IsStronglyLocallyOneBalanced p B b L}) :=
        gLBConj_mono g (le_sSup ⟨hcomp, hnot⟩)

private theorem lambdaStar_gLBConj_le {p : ℕ} (B : Subgroup G) (b g : G) :
    lambdaStar p (GLBConj g B) (g⁻¹ * b * g) ≤ GLBConj g (lambdaStar p B b) := by
  unfold lambdaStar
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (lambdaOf_gLBConj_le B b g).trans (gLBConj_mono g (le_sup_of_le_left le_sup_left))
  · calc GLAPPrimeCoreOf p (Subgroup.centralizer ({g⁻¹ * b * g} : Set G))
        = GLBConj g (GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) := by
          rw [centralizer_singleton_gLBConj', glaPPrimeCoreOf_gLBConj]
      _ ≤ _ := gLBConj_mono g (le_sup_of_le_left le_sup_right)
  · calc GLAPPrimeCoreOf p (Subgroup.centralizer (GLBConj g B : Set G))
        = GLBConj g (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set G))) := by
          rw [← gLBConj_centralizer, glaPPrimeCoreOf_gLBConj]
      _ ≤ _ := gLBConj_mono g le_sup_right

private theorem lambdaStarGroup_gLBConj_le {p : ℕ} {B M : Subgroup G} {y : G} (hy : y ∈ M)
    (hB : lambdaStarGroup p B ≤ M) : lambdaStarGroup p (GLBConj y B) ≤ M := by
  unfold lambdaStarGroup
  refine iSup_le fun b' => iSup_le fun hb' => iSup_le fun hne => ?_
  have hb : y * b' * y⁻¹ ∈ B := mem_gLBConj.1 hb'
  have hne' : y * b' * y⁻¹ ≠ 1 := fun h => hne (by
    have : b' = y⁻¹ * (y * b' * y⁻¹) * y := by group
    rw [this, h]; group)
  have heq : b' = y⁻¹ * (y * b' * y⁻¹) * y := by group
  rw [heq]
  calc lambdaStar p (GLBConj y B) (y⁻¹ * (y * b' * y⁻¹) * y)
      ≤ GLBConj y (lambdaStar p B (y * b' * y⁻¹)) := lambdaStar_gLBConj_le B _ y
    _ ≤ GLBConj y (lambdaStarGroup p B) := by
        refine gLBConj_mono y ?_
        unfold lambdaStarGroup
        exact le_iSup₂_of_le (f := fun c _ => ⨆ (_ : c ≠ 1), lambdaStar p B c) (y * b' * y⁻¹) hb
          (le_iSup_of_le hne' le_rfl)
    _ ≤ GLBConj y M := gLBConj_mono y hB
    _ = M := gLBConj_fix_of_mem' hy

private theorem glbCore_gLBConj_le {p : ℕ} (hp : 1 < p) (k : ℕ) (H : Subgroup G) (g : G) :
    GLBCore p k (GLBConj g H) ≤ GLBConj g (GLBCore p k H) := by
  unfold GLBCore
  apply sSup_le
  rintro N ⟨Q, hQH, hkQ, rfl⟩
  have hQ' : GLBConj g⁻¹ Q ≤ H := by
    have h := gLBConj_mono g⁻¹ hQH
    rwa [gLBConj_inv_gLBConj] at h
  have hmap : GLBConj g⁻¹ Q = Q.map (MulAut.conj g).toMonoidHom := by
    unfold GLBConj
    rw [inv_inv]
  have hrank : k ≤ CFSG.Open.pRank p (GLBConj g⁻¹ Q) := by
    rw [hmap]
    exact hkQ.trans (CFSG.SectionRank.pRank_le_map hp _ (MulAut.conj g).injective Q)
  have hle : Subgroup.normalizer ((GLBConj g⁻¹ Q : Subgroup G) : Set G) ≤ GLBCore p k H :=
    le_sSup ⟨GLBConj g⁻¹ Q, hQ', hrank, rfl⟩
  calc Subgroup.normalizer (Q : Set G)
      = Subgroup.normalizer ((GLBConj g (GLBConj g⁻¹ Q) : Subgroup G) : Set G) := by
        rw [gLBConj_gLBConj_inv]
    _ = GLBConj g (Subgroup.normalizer ((GLBConj g⁻¹ Q : Subgroup G) : Set G)) :=
        (gLBConj_normalizer g _).symm
    _ ≤ GLBConj g (GLBCore p k H) := gLBConj_mono g hle

private theorem gladelta_gLBConj_le {p : ℕ} (g : G) (D : Subgroup G) :
    GLADelta p (GLBConj g D) ≤ GLBConj g (GLADelta p D) := by
  intro x hx
  rw [mem_gLBConj]
  unfold GLADelta at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro d hd hd1
  have hd' : g⁻¹ * d * g ∈ GLBConj g D :=
    mem_gLBConj.2 (by rw [show g * (g⁻¹ * d * g) * g⁻¹ = d by group]; exact hd)
  have hd'1 : g⁻¹ * d * g ≠ 1 := fun h => hd1 (by
    have : d = g * (g⁻¹ * d * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hx' := hx (g⁻¹ * d * g) hd' hd'1
  rw [centralizer_singleton_gLBConj', glaPPrimeCoreOf_gLBConj] at hx'
  exact mem_gLBConj.1 hx'

private theorem gladelta_gLBConj {p : ℕ} (g : G) (D : Subgroup G) :
    GLADelta p (GLBConj g D) = GLBConj g (GLADelta p D) :=
  gLBConj_eq_of_forall_le (F := GLADelta p) (fun g' H => gladelta_gLBConj_le g' H) g D

private theorem isBmax_gLBConj {p : ℕ} {B : Subgroup G} (g : G) (hB : GLAIsBmax p B) :
    GLAIsBmax p (GLBConj g B) := by
  unfold GLAIsBmax at hB ⊢
  obtain ⟨hE, hcard, U, hU, hUp, hBN⟩ := hB
  refine ⟨CFSG.SectionRank.isElemAbelian_map hE _, ?_, GLBConj g U,
    fun h => hU ((gLBConj_eq_bot_iff g U).1 h), ?_, ?_⟩
  · rw [card_gLBConj']
    exact hcard
  · unfold GLBConj
    exact hUp.map (MulAut.conj g⁻¹).toMonoidHom
  · rw [← gLBConj_normalizer g U]
    exact gLBConj_mono g hBN

private theorem isBOneMax_gLBConj' {p : ℕ} {B : Subgroup G} (g : G) (hB : IsBOneMax p B) :
    IsBOneMax p (GLBConj g B) := by
  obtain ⟨hBmax, D, hDB, hD, hev⟩ := hB
  refine ⟨isBmax_gLBConj g hBmax, GLBConj g D, gLBConj_mono g hDB, isPPlane_gLBConj g hD, ?_⟩
  rw [gladelta_gLBConj, card_gLBConj']
  exact hev

end Conj

theorem sec10Fails_conj_of (hconj : IsUniquenessTwoLocal_conjStatement) : Sec10Fails_conjStatement := by
  intro G _ _ m p B M h y hy
  have hp1 : 1 < p := h.standing.prime.one_lt
  refine ⟨⟨h.standing, isBOneMax_gLBConj' y h.bOne, ⟨h.pre.1, ?_, ?_⟩, hconj h.uniq hy⟩,
    h.notB, h.notStar⟩
  · exact lambdaStarGroup_gLBConj_le hy h.pre.2.1
  · exact (glbCore_gLBConj_le hp1 3 B y).trans ((gLBConj_mono y h.pre.2.2).trans
      (gLBConj_fix_of_mem' hy).le)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
