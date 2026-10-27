module

public import CFSG.ClassicalInvolution.Q3.TL3T39

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem swap : CHyp 3 IH Ω J K where
  toCHypG := hS.toCHypG
  adj := hS.graphFam'.graph.symm hS.adj
  max := orbOf_mem_maxOrbs hS.graphFam' hS.adj hS.max

theorem orb_swap_eq {g : G} (hg : conjSub g K = J) :
    conjSub g '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
  rw [hS.conj_orb_eq (by rw [hg]; exact mem_orbOf_self K J), hg]

theorem nonempty_aeIdent_swap {n : ℕ} (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    Nonempty (AEIdent (orbOf (TC.nbrAdj Ω) J K) n) := by
  obtain ⟨g, hg⟩ := hS.trans K hS.adj.1 J (hS.orb_subset_omega (mem_orbOf_self K J))
  exact ⟨AEIdent.ofEq (hS.orb_swap_eq hg) (I.conj g)⟩

theorem exists_twin_at_J {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    ∃ Js ∈ orbOf (TC.nbrAdj Ω) K J, Js ≠ J ∧ (∀ a ∈ J, ∀ b ∈ Js, a * b = b * a) ∧
      ∀ z zs : G, IsUniqueInvolution J z → IsUniqueInvolution Js zs → zs = z := by
  obtain ⟨I'⟩ := hS.nonempty_aeIdent_swap I
  obtain ⟨g, Ks, y, hD, -, -, -, -, hz⟩ := hS.swap.exists_twin hn I'
  have hKs : Ks ∈ orbOf (TC.nbrAdj Ω) K J := by
    have h1 := hD.Ks_mem
    rwa [hS.swap.orb_swap_eq hD.hg] at h1
  exact ⟨Ks, hKs, hD.Ks_ne, hD.comm, hz⟩

theorem twin_z_eq {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar γ hγ c)
    {J' : Subgroup G} (hJ' : J' ∈ orbOf (TC.nbrAdj Ω) K J)
    (hlab' : (J'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar γ hγ (!c)) :
    ∀ z z' : G, IsUniqueInvolution J z → IsUniqueInvolution J' z' → z' = z := by
  intro z z' hz hz'
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hPΩ := hS.orb_subset_omega
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  obtain ⟨Js, hJs, hJsJ, -, hzs⟩ := hS.exists_twin_at_J hn I
  obtain ⟨β, hβ, c', hlabJs⟩ := I.label Js hJs
  obtain ⟨⟨zs, hzs'⟩, -⟩ := hS.hyp.omega1 Js (hPΩ hJs)
  have hzz : zs = z := hzs z zs hz hzs'
  have e1 := I.map_eq_zBar hn hJs (h8 Js (hPΩ hJs)) hlabJs hzs'
  have e2 := I.map_eq_zBar hn hJπ (h8 J (hPΩ hJπ)) hlabJ hz
  have hβγ : β = γ := by
    apply AE.eq_of_zBar_eq hn8
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext hzz
  subst hβγ
  have hcc : c' = c ∨ c' = !c := by cases c <;> cases c' <;> simp
  rcases hcc with rfl | rfl
  · exact absurd (aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hJs hJπ
      (hlabJs.trans hlabJ.symm)) hJsJ
  · have hJsJ' : Js = J' := aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hJs hJ'
      (hlabJs.trans hlab'.symm)
    subst hJsJ'
    rw [hz'.eq hzs', hzz]

theorem z_eq_of_label {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {L L' : Subgroup G}
    (hL : L ∈ orbOf (TC.nbrAdj Ω) K J) (hL' : L' ∈ orbOf (TC.nbrAdj Ω) K J)
    {δ : Finset (Fin n)} {hδ hδ' : δ.card = 4} {d d' : Bool}
    (hlab : (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar δ hδ d)
    (hlab' : (L'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar δ hδ' d') :
    ∀ z z' : G, IsUniqueInvolution L z → IsUniqueInvolution L' z' → z' = z := by
  intro z z' hz hz'
  have hPΩ := hS.orb_subset_omega
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hinv : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      conjSub x M ∈ orbOf (TC.nbrAdj Ω) K J :=
    fun M hM x hx => CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hx) hM
  have heq : ∀ {M M' : Subgroup G}, M ∈ orbOf (TC.nbrAdj Ω) K J →
      M' ∈ orbOf (TC.nbrAdj Ω) K J →
      (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
        (M'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ → M = M' :=
    fun hM hM' h => aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hM hM' h
  obtain ⟨γ, hγ, c, hlabJ⟩ := I.label J hJπ
  obtain ⟨J', hJ', hlabJ'⟩ := I.label_surj γ hγ (!c)
  have hJJ' : J' ≠ J := fun e => by
    rw [e] at hlabJ'
    rw [hlabJ'] at hlabJ
    cases c
    · exact AE.memBar_true_ne_false hn γ hγ hlabJ
    · exact AE.memBar_true_ne_false hn γ hγ hlabJ.symm
  have hzbar : ∀ {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) {ε : Finset (Fin n)}
      {hε : ε.card = 4} {e : Bool}
      (_ : (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar ε hε e)
      {w : G} (hw : IsUniqueInvolution M w), I.φ ⟨w, le_pSpan hM hw.mem⟩ = AE.zBar ε hε :=
    fun hM _ _ _ hlabM _ hw => I.map_eq_zBar hn hM (h8 _ (hPΩ hM)) hlabM hw
  obtain ⟨a, ha, haJ⟩ := orbOf_subset_gen hS.graphFam'.graph hS.adj hL
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hS.hyp.omega1 J (hPΩ hJπ)
  obtain ⟨⟨zJ', hzJ'⟩, -⟩ := hS.hyp.omega1 J' (hPΩ hJ')
  have hJ'z : zJ' = zJ := hS.twin_z_eq hn hn8 I hlabJ hJ' hlabJ' zJ zJ' hzJ hzJ'
  set M := conjSub a J' with hM
  have hMπ : M ∈ orbOf (TC.nbrAdj Ω) K J := hinv J' hJ' a ha
  have hzM : IsUniqueInvolution M (a * zJ * a⁻¹) := by
    have := hzJ'.conj a
    rwa [hJ'z] at this
  have hzL : IsUniqueInvolution L (a * zJ * a⁻¹) := haJ ▸ hzJ.conj a
  have hzz : z = a * zJ * a⁻¹ := hz.eq hzL
  obtain ⟨ε, hε, e, hlabM⟩ := I.label M hMπ
  have hεδ : ε = δ := by
    apply AE.eq_of_zBar_eq hn8
    rw [← hzbar hMπ hlabM hzM, ← hzbar hL hlab hzL]
  subst hεδ
  have hML : M ≠ L := by
    intro h
    apply hJJ'
    apply conjSub_injective a
    rw [← hM, h, haJ]
  have hed : e ≠ d := by
    intro h
    subst h
    exact hML (heq hMπ hL (hlabM.trans hlab.symm))
  have hd' : d' = d ∨ d' = e := by
    cases d <;> cases e <;> cases d' <;> simp_all
  rcases hd' with rfl | rfl
  · have : L' = L := heq hL' hL (hlab'.trans hlab.symm)
    subst this
    exact hz'.eq hz
  · have : L' = M := heq hL' hMπ (hlab'.trans hlabM.symm)
    subst this
    rw [hz'.eq hzM, hzz]

theorem z_comm {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {L L' : Subgroup G} (hL : L ∈ orbOf (TC.nbrAdj Ω) K J) (hL' : L' ∈ orbOf (TC.nbrAdj Ω) K J)
    {z z' : G} (hz : IsUniqueInvolution L z) (hz' : IsUniqueInvolution L' z') :
    z * z' = z' * z := by
  have hPΩ := hS.orb_subset_omega
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hK : K ∈ Ω := hS.adj.1
  have hzX : z ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := le_pSpan hL hz.mem
  have hz'X : z' ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := le_pSpan hL' hz'.mem
  set M := conjSub z L' with hM
  have hMπ : M ∈ orbOf (TC.nbrAdj Ω) K J :=
    CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hzX) hL'
  have hzM : IsUniqueInvolution M (z * z' * z⁻¹) := hz'.conj z
  obtain ⟨δ, hδ, d, hlab⟩ := I.label L hL
  obtain ⟨δ', hδ', d', hlab'⟩ := I.label L' hL'
  obtain ⟨ε, hε, e, hlabM⟩ := I.label M hMπ
  have e1 := I.map_eq_zBar hn hL (h8 L (hPΩ hL)) hlab hz
  have e2 := I.map_eq_zBar hn hL' (h8 L' (hPΩ hL')) hlab' hz'
  have e3 := I.map_eq_zBar hn hMπ (h8 M (hPΩ hMπ)) hlabM hzM
  have hεδ : ε = δ' := by
    apply AE.eq_of_zBar_eq hn8
    rw [← e3, ← e2]
    have h1 : (⟨z * z' * z⁻¹, le_pSpan hMπ hzM.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) =
        ⟨z, hzX⟩ * ⟨z', hz'X⟩ * ⟨z, hzX⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    have hc : I.φ ⟨z, hzX⟩ * I.φ ⟨z', hz'X⟩ = I.φ ⟨z', hz'X⟩ * I.φ ⟨z, hzX⟩ := by
      have h2 : I.φ ⟨z, le_pSpan hL hz.mem⟩ = AE.zBar δ hδ := e1
      have h3 : I.φ ⟨z', le_pSpan hL' hz'.mem⟩ = AE.zBar δ' hδ' := e2
      rw [h2, h3]
      exact comm_of_mem_ker_permQ (by rw [AE.zBar, permQ_mkQ, AE.zOf_perm])
        (by rw [AE.zBar, permQ_mkQ, AE.zOf_perm])
    rw [hc, mul_inv_cancel_right]
  subst hεδ
  have := hS.z_eq_of_label hn hn8 I hMπ hL' hlabM hlab' _ _ hzM hz'
  calc z * z' = z * z' * z⁻¹ * z := by group
    _ = z' * z := by rw [← this]

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
