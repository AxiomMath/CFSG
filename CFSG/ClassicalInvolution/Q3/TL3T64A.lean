module

public import CFSG.ClassicalInvolution.Q3.TL3T72F
public import CFSG.ClassicalInvolution.Q3.TL3T72G
public import CFSG.ClassicalInvolution.Q3.TL3T80
public import CFSG.ClassicalInvolution.Q3.TL3T62

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

theorem exists_pairInv_of_five_le {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {R : Subgroup G} (hRn : R.Normal) (hR : ∀ L ∈ Ω, ∀ v : G, IsUniqueInvolution L v → v ∈ R) :
    ∃ t u : G, conjSub t K = J ∧ conjSub t J = K ∧
      (∃ k ∈ K, ∃ k' ∈ Ks, u = k * k') ∧ u ∈ R ∧ u ≠ 1 ∧
      (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x) ∧
      (¬ ∀ k ∈ K, k * u = u * k) ∧ (¬ ∀ k ∈ Ks, k * u = u * k) ∧
      (∃ (hw : t * u * t⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) (a c : Fin n), a ≠ c ∧
        I.φ ⟨t * u * t⁻¹, hw⟩ = mkQ n (ofVec (TL4.pairVec a c)) ∧
        ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (b : Bool),
          (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b →
            a ∈ γ ∧ c ∈ γ) ∧
      (∃ (hw : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) (a c : Fin n), a ≠ c ∧
        I.φ ⟨t⁻¹ * u * t, hw⟩ = mkQ n (ofVec (TL4.pairVec a c)) ∧
        ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (b : Bool),
          (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b →
            a ∈ γ ∧ c ∈ γ) := by
  by_cases hn8 : n = 8
  · subst hn8
    exact hS.exists_pairInv_eight I hKs hKsK hz hKsX hRn hR
  · exact hS.toCHyp.exists_pairInv' (by omega) I hKs hKsK hz hKsX hRn hR

theorem conjSub_twin_label_of_five_le {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {δ : Finset (Fin n)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ b)
    {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z) :
    ((conjSub s Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      memBar δ hδ (!b) := by
  by_cases hn8 : n = 8
  · subst hn8
    exact hS.conjSub_twin_label_eight I hlabJ hs hs' hKs hKsK hz
  · exact hS.toCHyp.conjSub_twin_label hn hn8 I hlabJ hs hs' hKs hKsK hz

theorem nonempty_pairChart {n : ℕ} (hn : 5 ≤ n) (hM : Model117At n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) : Nonempty (PairChart Ω K J I) := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hn5 : 5 ≤ n := hn
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hH := hC.aeCoverHyp_orb' hn5 I
  obtain ⟨g, Ks, y, hDg, -, -, hKsπ, hKsX, hz⟩ := hC.exists_twin hn5 I
  have hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K := by
    have h1 := hDg.Ks_mem
    rwa [hC.orb_swap_eq hDg.hg] at h1
  have hKsK : Ks ≠ K := hDg.Ks_ne
  obtain ⟨⟨z, hzK⟩, -⟩ := hD.hyp.omega1 K hK
  obtain ⟨R, hRn, hR2, hzR⟩ := hD.inO2 K hK z hzK
  have hR : ∀ L ∈ Ω, ∀ v : G, IsUniqueInvolution L v → v ∈ R := by
    intro L hL v hv
    obtain ⟨x, hx⟩ := hD.trans K hK L hL
    have h1 : IsUniqueInvolution L (x * z * x⁻¹) := hx ▸ hzK.conj x
    rw [hv.eq h1]
    exact hRn.conj_mem z hzR x
  obtain ⟨t, u, ht, ht', ⟨k₀, hk₀, k₀', hk₀', hu⟩, huR, hu1, hXu, hKu, hKsu,
    ⟨hw, a, c, hac, hwI, hγac⟩, ⟨hw', a', c', hac', hwI', hγac'⟩⟩ :=
    hS.exists_pairInv_of_five_le hn5 I hKs hKsK hz hKsX hRn hR
  obtain ⟨hti, hti'⟩ := CHyp.swap_inv ht ht'
  obtain ⟨γ, hγ, b, hlabJ⟩ := I.label J hJπ
  have hJs := hC.conjSub_twin_mem ht ht' hKs
  have hlabJs := hS.conjSub_twin_label_of_five_le hn5 I hlabJ ht ht' hKs hKsK hz
  have hJs' : conjSub t⁻¹ Ks = conjSub t Ks := by
    have h1 := hS.conjSub_twin_label_of_five_le hn5 I hlabJ hti hti' hKs hKsK hz
    exact hH.label_inj _ (hC.conjSub_twin_mem hti hti' hKs) _ hJs (h1.trans hlabJs.symm)
  obtain ⟨ha, hc⟩ := hγac γ hγ b hlabJ
  obtain ⟨ha', hc'⟩ := hγac' γ hγ b hlabJ
  obtain ⟨m, hm5, ⟨IY⟩⟩ :=
    hS.exists_aeIdent_centMembers' hn5 I hKs hKsK hKsπ hz hKsX hu1 hXu hKu hKsu
  have hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u := fun M hM =>
    ⟨hC.orb_subset_omega hM, fun m hm => hXu m (le_pSpan hM hm)⟩
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hodd := hS.oddCore_centMembers_eq_bot hRn hR2 huR
  have hkY : IsPGroup 2 IY.φ.ker := IY.toLabel.isPGroup_ker hodd
  have hinjY : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two hPΩ hm5 IY hkY hL hL' h
  have htrans := hS.trans_centMembers' hn5 I hKs hKsK hKsπ hz hKsX hu1 hXu hKu hKsu
  have huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) := by
    rw [hu]
    exact mul_mem (le_pSpan (mem_orbOf_self J K) hk₀) (le_pSpan hKs hk₀')
  have hmn : m = n + 2 := by
    by_cases hn5e : n = 5
    · subst hn5e
      have h7 := hS.degree_centMembers_five I ht ht' huX' hac' hw' hwI' (fun h => hγac' _ _ _ h)
        IY hm5 hkY hπY
      omega
    · exact hS.degree_centMembers' (by omega) I ht ht' huX' hac' hw' hwI' IY hm5 hkY hπY
  subst hmn
  obtain ⟨ι, hι⟩ : ∃ ι : Fin n ↪ Fin (n + 2), ∀ L ∈ orbOf (TC.nbrAdj Ω) K J,
      ∀ (α : Finset (Fin n)) (hα : α.card = 4) (e : Bool),
      (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar α hα e →
      ∃ (hα' : (α.map ι).card = 4) (e' : Bool),
        (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ = memBar (α.map ι) hα' e' :=
    exists_emb_of_aeIdent_small_eq hπY hn5 I IY hH
      (fun L hL => (hD.hyp.omega1 L (hC.orb_subset_omega hL)).1)
  have hmiss : ∃ x, x ∉ Set.range ι := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective ι fun x => hcon x
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨L₁, hL₁, hl₁⟩ := I.label_surj γ hγ true
  obtain ⟨L₂, hL₂, hl₂⟩ := I.label_surj γ hγ false
  have hL₁₂ : L₁ ≠ L₂ := fun e => memBar_true_ne_false hn5 γ hγ (by rw [← hl₁, ← hl₂, e])
  have hz₁₂ := hH.twin_z γ hγ L₁ hL₁ L₂ hL₂ hl₁ hl₂
  have hHY : TL4.AECoverHyp IY := by
    by_cases hn6 : n = 6
    ·
      obtain ⟨hγ₁, b₁, hl₁Y⟩ := hι L₁ hL₁ γ hγ true hl₁
      obtain ⟨hγ₂, b₂, hl₂Y⟩ := hι L₂ hL₂ γ hγ false hl₂
      have hb : b₂ = !b₁ := by
        cases b₁ <;> cases b₂
        · exact absurd (hinjY L₁ (hπY hL₁) L₂ (hπY hL₂) (hl₁Y.trans hl₂Y.symm)) hL₁₂
        · rfl
        · rfl
        · exact absurd (hinjY L₁ (hπY hL₁) L₂ (hπY hL₂) (hl₁Y.trans hl₂Y.symm)) hL₁₂
      subst hb
      exact hS.aeCoverHyp_centMembers_of_twin hm5 IY hodd htrans (hπY hL₁) (hπY hL₂) hl₁Y hl₂Y
        hz₁₂
    · exact hS.aeCoverHyp_centMembers' hm5 (by omega) IY hodd htrans (hπY hL₁) (hπY hL₂) hL₁₂
        hz₁₂
  have hsub : SubHyp IY (orbOf (TC.nbrAdj Ω) K J) ι :=
    subHyp_of_labels I IY hπY hn5 ι hmiss hH.card hH.conj_mem hHY.label_inj hι
  have hl : t * k₀ * t⁻¹ ∈ J := ht ▸ conj_mem_conjSub hk₀
  have hl' : t * k₀' * t⁻¹ ∈ conjSub t Ks := conj_mem_conjSub hk₀'
  have hm : t⁻¹ * k₀ * t ∈ J := by
    have := conj_mem_conjSub (n := t⁻¹) hk₀
    rwa [hti, inv_inv] at this
  have hm' : t⁻¹ * k₀' * t ∈ conjSub t Ks := by
    have := conj_mem_conjSub (n := t⁻¹) hk₀'
    rwa [hJs', inv_inv] at this
  have he1 : t * u * t⁻¹ = (t * k₀ * t⁻¹) * (t * k₀' * t⁻¹) := by rw [hu]; group
  have he2 : t⁻¹ * u * t = (t⁻¹ * k₀ * t) * (t⁻¹ * k₀' * t) := by rw [hu]; group
  have hI1 : I.φ ⟨(t * k₀ * t⁻¹) * (t * k₀' * t⁻¹), mul_mem (le_pSpan hJπ hl) (le_pSpan hJs hl')⟩ =
      mkQ n (ofVec (TL4.pairVec a c)) := by
    rw [← hwI]
    exact congrArg I.φ (Subtype.ext he1.symm)
  have hI2 : I.φ ⟨(t⁻¹ * k₀ * t) * (t⁻¹ * k₀' * t), mul_mem (le_pSpan hJπ hm) (le_pSpan hJs hm')⟩ =
      mkQ n (ofVec (TL4.pairVec a' c')) := by
    rw [← hwI']
    exact congrArg I.φ (Subtype.ext he2.symm)
  have hp1 := hsub.map_pairVec' hM hn5 I hι hJπ hJs hlabJ hlabJs hl hl' ha hc hI1
  have hp2 := hsub.map_pairVec' hM hn5 I hι hJπ hJs hlabJ hlabJs hm hm' ha' hc' hI2
  exact ⟨{
    t := t, u := u, Ks := Ks, Js := conjSub t Ks, IY := IY, ι := ι, γ := γ, hγ := hγ,
    b := b, a := a, c := c, a' := a', c' := c', k₀ := k₀, k₀' := k₀', ht := ht, ht' := ht',
    hKs := hKs, hKsK := hKsK, hKsπ := hKsπ, hz := hz, hKsX := hKsX, hJs := hJs, htKs := rfl,
    htKs' := hJs', hlabJ := hlabJ, hlabJs := hlabJs, hk₀ := hk₀, hk₀' := hk₀', hu := hu,
    hu1 := hu1, hXu := hXu, hKu := hKu, hKsu := hKsu, hac := hac, ha := ha, hc := hc,
    hac' := hac', ha' := ha', hc' := hc', hw := hw, hwI := hwI, hw' := hw', hwI' := hwI',
    hHY := hHY, hπY := hπY, hsub := hsub, hlabι := hι,
    hpair := (congrArg IY.φ (Subtype.ext he1)).trans hp1,
    hpair' := (congrArg IY.φ (Subtype.ext he2)).trans hp2 }⟩

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
