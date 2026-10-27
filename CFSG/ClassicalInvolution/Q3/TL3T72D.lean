module

public import CFSG.ClassicalInvolution.Q3.TL3T59
public import CFSG.ClassicalInvolution.Q3.TL3T53
public import CFSG.ClassicalInvolution.Q3.TL3T57
public import CFSG.ClassicalInvolution.Q3.TL3T58

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem vbar_pairVec_ne_zBar_of_mem {δ : Finset (Fin n)} (hδ : δ.card = 4) {a c : Fin n}
    (ha : a ∈ δ) (hc : c ∈ δ) (hac : a ≠ c) :
    mkQ n (ofVec (TL4.pairVec a c)) ≠ zBar δ hδ := by
  classical
  intro h
  rw [zBar, mkQ_eq_iff] at h
  obtain ⟨d, hdδ, hda, hdc⟩ : ∃ d ∈ δ, d ≠ a ∧ d ≠ c := by
    by_contra hne
    push Not at hne
    have hsub : δ ⊆ {a, c} := fun d hd => by
      by_cases hda : d = a
      · simp [hda]
      · simp [hne d hd hda]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le a ({c} : Finset (Fin n))
    rw [Finset.card_singleton] at h3
    omega
  have hdr : d ∈ Set.range (emb δ hδ) := by rw [range_emb]; exact_mod_cast hdδ
  have har : a ∈ Set.range (emb δ hδ) := by rw [range_emb]; exact_mod_cast ha
  have hd : (zOf (emb δ hδ)).vec d = 1 := by
    rw [zOf_vec_apply]
    simp [hdr]
  have ha' : (zOf (emb δ hδ)).vec a = 1 := by
    rw [zOf_vec_apply]
    simp [har]
  rcases h with h1 | h1
  · have h2 : ofVec (TL4.pairVec a c) = zOf (emb δ hδ) := inv_mul_eq_one.mp h1
    have := congrFun (congrArg Wr.vec h2) d
    rw [hd] at this
    change TL4.pairVec a c d = (1 : ZMod 2) at this
    rw [TL4.pairVec_apply] at this
    simp [hda, hdc] at this
  · have h2 : zOf (emb δ hδ) = ofVec (TL4.pairVec a c) * allOnes n :=
      inv_mul_eq_iff_eq_mul.mp h1
    have := congrFun (congrArg Wr.vec h2) a
    rw [ha', mul_vec] at this
    change (1 : ZMod 2) = TL4.pairVec a c a + 1 at this
    rw [TL4.pairVec_apply, if_pos rfl, if_neg hac] at this
    revert this
    decide

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

private theorem exists_exact_over {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    (hH : TL4.AECoverHyp I) (hn : 5 ≤ n) {δ : Finset (Fin n)} (hδ : δ.card = 4) :
    ∃ Γ : Finset (Fin n), δ ⊆ Γ ∧ ∀ {x y : G} (hx : x ∈ pSpan (I.over Γ))
      (hy : y ∈ pSpan (I.over Γ)),
      I.φ ⟨x, I.pSpan_over_le Γ hx⟩ = I.φ ⟨y, I.pSpan_over_le Γ hy⟩ → x = y := by
  classical
  by_cases h5 : n = 5
  · have hodd : Odd n := by rw [h5]; decide
    have hinj : Function.Injective I.φ :=
      (MonoidHom.ker_eq_bot_iff _).mp (TL4.aeCoverOddKer_proved G P n I hn hodd hH)
    exact ⟨Finset.univ, Finset.subset_univ _, fun {x y} _ _ hxy =>
      congrArg Subtype.val (hinj hxy)⟩
  · obtain ⟨p, hp⟩ := AE.Block4.exists_not_mem (s := δ) (by omega)
    set Γ := insert p δ with hΓ
    have hΓc : Γ.card = 5 := by rw [Finset.card_insert_of_notMem hp, hδ]
    obtain ⟨q, hq⟩ := AE.Block4.exists_not_mem (s := Γ) (by omega)
    have hodd : Odd Γ.card := by rw [hΓc]; decide
    exact ⟨Γ, Finset.subset_insert p δ, fun {x y} hx hy hxy =>
      I.eq_of_map_eq_over hH (by omega) hodd hq hx hy hxy⟩

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem exists_pairInv' {n : ℕ} (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
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
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn5 : 5 ≤ m + 2 := by omega
  have hH := hS.aeCoverHyp_orb hn5 (by omega) I
  have hJπ : J ∈ (orbOf (TC.nbrAdj Ω) K J) := mem_orbOf_self K J
  obtain ⟨t, ht, ht'⟩ := hS.exists_swap
  obtain ⟨hti, hti'⟩ := swap_inv ht ht'
  obtain ⟨δ, hδ, b, hlabJ⟩ := I.label J hJπ
  have hδmem : ∀ {x y : Fin (m + 2)}, x ∈ δ → y ∈ δ →
      ∀ (γ : Finset (Fin (m + 2))) (hγ : γ.card = 4) (b' : Bool),
        (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b' →
          x ∈ γ ∧ y ∈ γ := by
    intro x y hx hy γ hγ b' h
    obtain rfl := eq_of_memBar_eq hn5 (by omega) (hlabJ.symm.trans h)
    exact ⟨hx, hy⟩
  set Js := conjSub t Ks with hJs
  have hJsπ : Js ∈ (orbOf (TC.nbrAdj Ω) K J) := hS.conjSub_twin_mem ht ht' hKs
  have hlabJs := hS.conjSub_twin_label hn5 (by omega) I hlabJ ht ht' hKs hKsK hz
  have hJs' : conjSub t⁻¹ Ks = Js := by
    have h1 := hS.conjSub_twin_label hn5 (by omega) I hlabJ hti hti' hKs hKsK hz
    exact hH.label_inj _ (hS.conjSub_twin_mem hti hti' hKs) _ hJsπ (h1.trans hlabJs.symm)
  obtain ⟨j, hj, j', hj', a, ha, c, hc, hac, hjj, hI⟩ :=
    I.exists_mul_eq_pairVec hJπ hJsπ hlabJ hlabJs
  obtain ⟨u, hu⟩ : ∃ u : G, u = t⁻¹ * (j * j') * t := ⟨_, rfl⟩
  have htu : t * u * t⁻¹ = j * j' := by rw [hu]; group
  have hk : t⁻¹ * j * t ∈ K := by
    have := conj_mem_conjSub (n := t⁻¹) hj
    rwa [hti', inv_inv] at this
  have hk' : t⁻¹ * j' * t ∈ Ks := by
    have := conj_mem_conjSub (n := t⁻¹) hj'
    rwa [hJs, conjSub_inv_conjSub, inv_inv] at this
  have hufac : u = (t⁻¹ * j * t) * (t⁻¹ * j' * t) := by rw [hu]; group
  have hjjker : (⟨j * j', hjj⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) ∈
      (TL4.AECov.permHom I).ker := by
    rw [TL4.AECov.mem_ker_permHom, hI]
    rfl
  have hzle : ∀ x ∈ TL4.AECov.zSpan (orbOf (TC.nbrAdj Ω) K J), (x : G) ∈ R := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨L, hL, hgL⟩ := hg
      exact hR L (hS.orb_subset_omega hL) _ hgL
    | one => exact R.one_mem
    | mul a b _ _ iha ihb => exact R.mul_mem iha ihb
    | inv a _ ih => exact R.inv_mem ih
  have hW := TL4.AECov.zSpan_elem fun L hL L' hL' v v' hv hv' =>
    TL4.AECov.comm_of_isUniqueInvolution I hn5 hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL'
      hv hv'
  have hjjR : j * j' ∈ R := hzle _ (TL4.AECov.ker_permHom_le_zSpan I (by omega) hH.card
    hH.conj_mem hH.label_inj hH.ker_two (TL4.AECov.zSpan_normal hH.conj_mem) hW hjjker)
  have huR : u ∈ R := by
    have := hRn.conj_mem _ hjjR t⁻¹
    rw [hu]
    rwa [inv_inv] at this
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : j * j' = 1 := by rw [← htu, h1]; group
    apply vbar_pairVec_ne_one (by omega) hac
    rw [← hI]
    exact (congrArg I.φ (Subtype.ext h2 :
      (⟨j * j', hjj⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) = 1)).trans (map_one I.φ)
  have hXu : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x := by
    intro x hx
    rw [hufac]
    calc x * ((t⁻¹ * j * t) * (t⁻¹ * j' * t))
        = (x * (t⁻¹ * j * t)) * (t⁻¹ * j' * t) := by group
      _ = ((t⁻¹ * j * t) * x) * (t⁻¹ * j' * t) := by rw [hS.comm_orb_K hx hk]
      _ = (t⁻¹ * j * t) * (x * (t⁻¹ * j' * t)) := by group
      _ = (t⁻¹ * j * t) * ((t⁻¹ * j' * t) * x) := by rw [hKsX x hx _ hk']
      _ = ((t⁻¹ * j * t) * (t⁻¹ * j' * t)) * x := by group
  have hnc : ∀ {M L : Subgroup G} (_ : conjSub t M = L)
      (hL : L ∈ (orbOf (TC.nbrAdj Ω) K J)) {e : Bool}
      (_ : (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ e),
      ¬ ∀ k ∈ M, k * u = u * k := by
    intro M L hML hL e hlab hc'
    refine not_comm_memBar_pairVec hn5 hδ e ha hc hac fun x hx => ?_
    rw [← hlab] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
    have hlM : t⁻¹ * l * t ∈ M := by
      have := conj_mem_conjSub (n := t⁻¹) (hML ▸ hl : l ∈ conjSub t M)
      rwa [conjSub_inv_conjSub, inv_inv] at this
    have e1 := hc' _ hlM
    have e2 : l * (j * j') = (j * j') * l := by
      calc l * (j * j') = t * ((t⁻¹ * l * t) * u) * t⁻¹ := by rw [hu]; group
        _ = t * (u * (t⁻¹ * l * t)) * t⁻¹ := by rw [e1]
        _ = (j * j') * l := by rw [hu]; group
    rw [← hI, ← map_mul, ← map_mul]
    exact congrArg I.φ (Subtype.ext e2)
  have hw1 : t * u * t⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by rw [htu]; exact hjj
  have hI1 : I.φ ⟨t * u * t⁻¹, hw1⟩ = mkQ (m + 2) (ofVec (TL4.pairVec a c)) := by
    rw [← hI]
    exact congrArg I.φ (Subtype.ext htu)
  refine ⟨t, u, ht, ht', ⟨_, hk, _, hk', hufac⟩, huR, hu1, hXu, hnc ht hJπ hlabJ,
    hnc (M := Ks) rfl hJsπ hlabJs, ⟨hw1, a, c, hac, hI1, hδmem ha hc⟩, ?_⟩
  have hnorm : t⁻¹ * t⁻¹ ∈
      Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) :=
    hS.mem_normalizer_orb_of_conjSub (by rw [conjSub_mul, hti, hti'])
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = conjSpan hnorm ⟨j * j', hjj⟩ := ⟨_, rfl⟩
  have hx₀e : (x₀ : G) = t⁻¹ * u * t := by
    rw [hx₀, conjSpan_apply]
    show t⁻¹ * t⁻¹ * (j * j') * (t⁻¹ * t⁻¹)⁻¹ = t⁻¹ * u * t
    rw [hu]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hker := I.conj_mem_ker_permHom (by omega) hH hnorm hjjker
  rw [← hx₀, TL4.AECov.mem_ker_permHom] at hker
  have hl1 : t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹ ∈ J := by
    have := conj_mem_conjSub (n := t⁻¹ * t⁻¹) hj
    rwa [conjSub_mul, hti', hti] at this
  have hl2 : t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹ ∈ Js := by
    have := conj_mem_conjSub (n := t⁻¹ * t⁻¹) hj'
    rwa [conjSub_mul, hJs, conjSub_inv_conjSub, hJs'] at this
  have hfac : t⁻¹ * u * t = (t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹) * (t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹) := by
    rw [hu]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hx₀m : (x₀ : G) ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := x₀.2
  have hx₀' : x₀ = ⟨_, mul_mem (le_pSpan hJπ hl1) (le_pSpan hJsπ hl2)⟩ :=
    Subtype.ext (hx₀e.trans hfac)
  rw [hx₀'] at hker
  obtain ⟨Γ, hδΓ, hex⟩ := exists_exact_over I hH hn5 hδ
  have hJΓ : J ∈ I.over Γ := ⟨hJπ, δ, hδ, b, hδΓ, hlabJ⟩
  have hJsΓ : Js ∈ I.over Γ := ⟨hJsπ, δ, hδ, !b, hδΓ, hlabJs⟩
  have hxΓ : (t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹) * (t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹) ∈
      pSpan (I.over Γ) := mul_mem (le_pSpan hJΓ hl1) (le_pSpan hJsΓ hl2)
  rcases I.map_mul_twins hJπ hJsπ hlabJ hlabJs hl1 hl2 hker with
    h1 | h1 | ⟨a', ha', c', hc', hac', h1⟩
  · exfalso
    have he := hex hxΓ (pSpan (I.over Γ)).one_mem (by
      rw [show (⟨1, I.pSpan_over_le Γ (pSpan (I.over Γ)).one_mem⟩ :
        ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) = 1 from rfl, map_one]
      exact h1)
    apply hu1
    have : t⁻¹ * u * t = 1 := hfac.trans he
    calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
      _ = 1 := by rw [this]; group
  · exfalso
    obtain ⟨⟨zJ, hzJ⟩, -⟩ := hS.hyp.omega1 J (hS.orb_subset_omega hJπ)
    have hzJe := I.map_eq_zBar hn5 hJπ (hH.card J hJπ) hlabJ hzJ
    have he := hex hxΓ (le_pSpan hJΓ hzJ.mem) (h1.trans hzJe.symm)
    have hut : t⁻¹ * u * t = zJ := hfac.trans he
    have hz2 : IsUniqueInvolution J (t * t * zJ * (t * t)⁻¹) := by
      have := hzJ.conj (t * t)
      rwa [conjSub_mul, ht', ht] at this
    have hzz : t * t * zJ * (t * t)⁻¹ = zJ := hz2.eq hzJ
    have hjz : j * j' = zJ := by
      calc j * j' = t * u * t⁻¹ := htu.symm
        _ = t * t * (t⁻¹ * u * t) * (t * t)⁻¹ := by group
        _ = zJ := by rw [hut, hzz]
    apply vbar_pairVec_ne_zBar_of_mem hδ ha hc hac
    rw [← hI, ← hzJe]
    exact congrArg I.φ (Subtype.ext hjz)
  · have hw2 : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by rw [← hx₀e]; exact hx₀m
    refine ⟨hw2, a', c', hac', ?_, hδmem ha' hc'⟩
    rw [← h1]
    apply congrArg I.φ
    exact Subtype.ext hfac

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
