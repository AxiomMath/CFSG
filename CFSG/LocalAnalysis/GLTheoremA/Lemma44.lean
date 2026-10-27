module

public import CFSG.LocalAnalysis.GLTheoremA.Exc
public import CFSG.LocalAnalysis.GLTheoremA.PCompJoin
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_mono {g : G} {H K : Subgroup G} (h : H ≤ K) : GLBConj g H ≤ GLBConj g K :=
  fun _ hy => mem_gLBConj.2 (h (mem_gLBConj.1 hy))

private theorem le_gLBConj_glaPLayer {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    GLAPLayer p X ≤ GLBConj g (GLAPLayer p X) := by
  refine sSup_le fun L hL => ?_
  have hX : GLBConj g⁻¹ X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ hg)
  have h1 : GLAPComponent p X (GLBConj g⁻¹ L) := by
    have := glaPComponent_gLBConj hL g⁻¹
    rwa [hX] at this
  have e : L = GLBConj g (GLBConj g⁻¹ L) := by
    rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
  rw [e]
  exact gLBConj_mono (le_sSup h1)

theorem mem_normalizer_glaPLayer {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ (le_gLBConj_glaPLayer hg)
  have h := gLBConj_mono (g := g) (le_gLBConj_glaPLayer (p := p) (Subgroup.inv_mem _ hg))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

private theorem le_gLBConj_closureIn {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    closureIn I H ≤ GLBConj g (closureIn I H) := by
  have hIg : GLBConj g I = I := mem_normalizer_iff_gLBConj_eq.1 hI
  conv_lhs => rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun h hh => ?_
  have hc : g * h * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hH h).1 hh
  have e : GLBConj h I = GLBConj g (GLBConj (g * h * g⁻¹) I) := by
    rw [gLBConj_gLBConj, show g * h * g⁻¹ * g = g * h by group, ← gLBConj_gLBConj, hIg]
  rw [e]
  refine gLBConj_mono ?_
  rw [closureIn_eq_iSup_gLBConj]
  exact le_biSup (fun h => GLBConj h I) hc

theorem mem_normalizer_closureIn {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (closureIn I H : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ (le_gLBConj_closureIn hI hH)
  have h := gLBConj_mono (g := g)
    (le_gLBConj_closureIn (Subgroup.inv_mem _ hI) (Subgroup.inv_mem _ hH))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

theorem isGoodComp_of_le_MxB {p : ℕ} (hp : p.Prime) {Club : Subgroup G → Prop}
    {B K : Subgroup G} {x : G} (hK : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K)
    (h : K ≤ MxB p Club B x) : IsGoodComp p Club B x K :=
  mem_of_le_sSup_glaPComponent hp _ (fun _ hL => hL.1) hK h

theorem le_closureIn_self (I H : Subgroup G) : I ≤ closureIn I H := by
  rw [closureIn_eq_iSup_gLBConj]
  have := le_biSup (fun g => GLBConj g I) (Subgroup.one_mem H)
  simpa [gLBConj_one] using this

theorem lemma44b_closure {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B' L : Subgroup G} {x x' : G}
    (hB' : GLAIsBmax p B') (hx' : IsEssential p B' x') (hxB' : x ∈ B')
    (hB'L : B' ≤ Subgroup.normalizer (L : Set G))
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hx'L : CentMod p L x')
    (hnc : ¬ Club L) :
    IsGoodComp p Club B' x' (closureIn (GLAPLayer p (L ⊓ Subgroup.centralizer ({x'} : Set G)))
      (GLAPLayer p (Subgroup.centralizer ({x'} : Set G)))) ∧
    ∀ L' : Subgroup G, GLAPComponent p (closureIn (GLAPLayer p
      (L ⊓ Subgroup.centralizer ({x'} : Set G))) (GLAPLayer p (Subgroup.centralizer ({x'} : Set G))))
      L' → L' = closureIn (GLAPLayer p (L ⊓ Subgroup.centralizer ({x'} : Set G)))
        (GLAPLayer p (Subgroup.centralizer ({x'} : Set G))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Cx := Subgroup.centralizer ({x} : Set G)
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hx'B' : x' ∈ B' := hx'.1
  have hB'Cx' : B' ≤ Cx' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := GLAPLayer p (L ⊓ Cx')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Cx' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf Cx') hIc
  have hKx' : CFSG.Open.IsKGroup ↥Cx' :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1)
  have hxCx' : Subgroup.zpowers x ≤ Cx' := Subgroup.zpowers_le.2 (hB'Cx' hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Cx' hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'.1 hxB') I hI2
  set J := closureIn I (GLAPLayer p Cx')
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Cx' := hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p J K := fun K hK =>
    glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hmem : ∀ L', GLAPComponent p J L' → L' ∈ 𝒞 := fun L' hL' => by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL' ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'.1
  obtain ⟨L₀, hL₀𝒞⟩ : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : J = ⊥ := by
      rw [hJ, h]
      simp
    exact glaPComponent_ne_bot' hIc (eq_bot_iff.2 (hbot ▸ hIJ))
  have hL₀C : GLAPComponent p Cx' L₀ := h𝒞c L₀ hL₀𝒞
  have hB'J : ∀ b ∈ B', b ∈ Subgroup.normalizer (J : Set G) := by
    intro b hb
    have hbCx' : b ∈ Subgroup.normalizer (Cx' : Set G) := Subgroup.le_normalizer (hB'Cx' hb)
    have hbLCx' : b ∈ Subgroup.normalizer ((L ⊓ Cx' : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_gLBConj_eq] at hbCx' ⊢
      rw [gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 (hB'L hb), hbCx']
    exact mem_normalizer_closureIn (mem_normalizer_glaPLayer hbLCx')
      (mem_normalizer_glaPLayer hbCx')
  have huniq : ∀ K ∈ 𝒞, K = L₀ := by
    by_contra hne
    push Not at hne
    obtain ⟨K, hK𝒞, hKL₀⟩ := hne
    have hxL₀ : x ∉ Subgroup.normalizer (L₀ : Set G) := by
      intro hxN
      obtain ⟨e, he, hee⟩ := h𝒞tr L₀ hL₀𝒞 K hK𝒞
      have heN : e ∈ Subgroup.normalizer (L₀ : Set G) := Subgroup.zpowers_le.2 hxN he
      exact hKL₀ (by rw [← hee, mem_normalizer_iff_gLBConj_eq.1 heN])
    have hcl : closureIn L₀ B' = J := by
      apply le_antisymm
      · rw [closureIn_eq_iSup_gLBConj]
        refine iSup₂_le fun b hb => ?_
        rw [← mem_normalizer_iff_gLBConj_eq.1 (hB'J b hb)]
        exact gLBConj_mono (hKJ L₀ hL₀𝒞)
      · rw [hJ]
        refine iSup₂_le fun K hK => ?_
        obtain ⟨e, he, rfl⟩ := h𝒞tr L₀ hL₀𝒞 K hK
        rw [closureIn_eq_iSup_gLBConj]
        exact le_biSup (fun b => GLBConj b L₀) (Subgroup.zpowers_le.2 hxB' he)
    have hIdiag : GLAPComponent p (closureIn L₀ B' ⊓ Cx) I := by
      rw [hcl]
      refine glaPComponent_of_le hp hI2 (le_inf hIJ (hIL.trans hL.1)) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hJCx'
    exact hnc ((hEC.club_congr I L ⟨eIL⟩).1
      (hEC.club_diag B' x' L₀ x hB' hx' hL₀C hxB' hxL₀ I hIdiag))
  have hJL₀ : J = L₀ := by
    rw [hJ]
    exact le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_biSup (fun K => K) hL₀𝒞)
  have hB'L₀ : B' ≤ Subgroup.normalizer (L₀ : Set G) := fun b hb => hJL₀ ▸ hB'J b hb
  refine ⟨hJL₀ ▸ ⟨hL₀C, hB'L₀, fun hclub => hnc ?_⟩,
    fun L' hL' => (huniq L' (hmem L' hL')).trans hJL₀.symm⟩
  have hIL₀x : GLAPComponent p (L₀ ⊓ Cx) I := by
    refine glaPComponent_of_le hp hI2 (le_inf (hJL₀ ▸ hIJ) (hIL.trans hL.1)) ?_
    rw [hCzx]
    exact inf_le_inf_right _ hL₀C.1
  exact (hEC.club_congr I L ⟨eIL⟩).1
    (hEC.club_down Cx' L₀ x hL₀C (hB'.1.2 x hxB') (hB'L₀ hxB') I hIL₀x hclub)

theorem lemma44b {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B' L L' : Subgroup G} {x x' : G}
    (hB' : GLAIsBmax p B') (hx' : IsEssential p B' x') (hxB' : x ∈ B')
    (hB'L : B' ≤ Subgroup.normalizer (L : Set G))
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hx'L : CentMod p L x')
    (hL' : GLAPComponent p (closureIn (GLAPLayer p (L ⊓ Subgroup.centralizer ({x'} : Set G)))
      (GLAPLayer p (Subgroup.centralizer ({x'} : Set G)))) L')
    (hnc : ¬ Club L) :
    IsGoodComp p Club B' x' L' := by
  obtain ⟨hgood, huniq⟩ :=
    lemma44b_closure hp hEC h183 hKP hsimple hnonab hB' hx' hxB' hB'L hL hx'L hnc
  rw [huniq L' hL']
  exact hgood

theorem isGoodComp_of_pumpRel {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {t t' : Triple G} (hrel : PumpRel p t t') (hL : IsGoodComp p Club t.1 t.2.1 t.2.2) :
    IsGoodComp p Club t'.1 t'.2.1 t'.2.2 := by
  obtain ⟨-, ⟨hB', hx', -⟩, hxB', hdec, -, hx'L, hL'⟩ := hrel
  refine lemma44b hp hEC h183 hKP hsimple hnonab hB' hx' hxB' ?_ hL.1 hx'L hL' hL.2.2
  intro b hb
  obtain ⟨u, hu, v, -, hv, rfl⟩ := hdec b hb
  exact Subgroup.mul_mem _ (hL.2.1 hu.1) hv.1

theorem lemma44a {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B B' L L' : Subgroup G} {x x' : G} (hS : IsSTriple p B x L)
    (hrel : Relation.ReflTransGen (PumpRel p) (B, x, L) (B', x', L'))
    (hL : L ≤ MxB p Club B x) :
    L' ≤ MxB p Club B' x' := by
  have key : ∀ t' : Triple G, Relation.ReflTransGen (PumpRel p) (B, x, L) t' →
      IsGoodComp p Club t'.1 t'.2.1 t'.2.2 := by
    intro t' h
    induction h with
    | refl => exact isGoodComp_of_le_MxB hp hS.2.2 hL
    | tail _ hstep ih => exact isGoodComp_of_pumpRel hp hEC h183 hKP hsimple hnonab hstep ih
  exact le_MxB (key _ hrel)

end CFSG.LocalAnalysis.GLTheoremA
