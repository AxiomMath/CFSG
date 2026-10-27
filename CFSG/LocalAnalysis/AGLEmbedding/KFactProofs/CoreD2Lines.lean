
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase
public import Certificates.Data.CoreD2Lines

public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

@[expose] def CoreGenerationVOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ E : Subgroup G, IsPGroup p E ∧ Nat.card E = p ^ 3 ∧
    ∀ A : Subgroup G, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set G, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        (∃ Y : Subgroup G, Y ≤ E ∧ 2 ≤ Open.pRank p Y ∧
          g ∈ Subgroup.normalizer (Y : Set G)) ∨
        ∃ Q : Subgroup G, Q ≤ A ∧ 1 ≤ Open.pRank p Q ∧ g ∈ Subgroup.normalizer (Q : Set G)

section Abstract

variable {X : Type*} [Group X]

theorem wordVal_mem_of (S : List X) (H : Subgroup X) :
    ∀ w : List ℤ, (∀ l ∈ w, S.getD (l.natAbs - 1) 1 ∈ H) → wordVal S w ∈ H
  | [], _ => H.one_mem
  | l :: w, h => by
    rw [wordVal]
    refine H.mul_mem ?_ (wordVal_mem_of S H w fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    split_ifs with hpos
    · rwa [show l.toNat = l.natAbs by omega]
    · exact H.inv_mem (by rwa [show (-l).toNat = l.natAbs by omega])

theorem card_closure_pair_of_pow [Finite X] {p : ℕ} (hp : p.Prime) {u v : X} (hu : u ^ p = 1)
    (hv : v ^ p = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hvu : ∀ j < p, v ≠ u ^ j) :
    Nat.card ↥(Subgroup.closure ({u, v} : Set X)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hou : orderOf u = p := orderOf_eq_prime hu hu1
  have hv1 : v ≠ 1 := by simpa using hvu 0 hp.pos
  have hov : orderOf v = p := orderOf_eq_prime hv hv1
  have hind : v ∉ Subgroup.zpowers u := by
    intro hmem
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
    obtain ⟨m, hm⟩ := hmem
    refine hvu (m % p) (Nat.mod_lt m hp.pos) ?_
    rw [← hou, pow_mod_orderOf, hm]
  exact card_closure_pair hp huv hou hov hind

theorem coreGenerationVOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime) {S : Set X}
    (hS : G = Subgroup.closure S) {E : Subgroup X} (hEp : IsPGroup p E)
    (hEc : Nat.card E = p ^ 3) (hEG : E ≤ G)
    (hΓ : ∀ A : Subgroup X, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set X, Γ ⊆ G ∧ S ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
        (∃ u v : X, u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧
          (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
            g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
        (∃ y ∈ A, y ≠ 1 ∧ y ^ p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g)) :
    CoreGenerationVOf ↥G p := by
  refine ⟨E.subgroupOf G, hEp.comap_subtype, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  · intro A' hA'E hA'e hA'c
    set A : Subgroup X := A'.map G.subtype with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hA'E hx)
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective G.subtype_injective, hA'c]
    obtain ⟨Γ, hΓG, hgen, hnorm⟩ := hΓ A hAE hAe hAc
    refine ⟨{g : ↥G | (g : X) ∈ Γ}, ?_, ?_⟩
    · rw [eq_top_iff]
      intro h _
      have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype =
          Subgroup.closure Γ := by
        rw [MonoidHom.map_closure]
        congr 1
        ext z
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact hg
        · intro hz
          exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
      have hle : G ≤ (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype := by
        rw [hmap, hS, Subgroup.closure_le]
        exact hgen
      obtain ⟨k, hk, hkh⟩ := hle h.2
      have : k = h := Subtype.ext hkh
      rwa [← this]
    · intro g hg
      rcases hnorm _ hg with ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ |
        ⟨y, hyA, hy1, hy, α, h1⟩
      · left
        set u' : ↥G := ⟨u, hEG huE⟩ with hu'
        set v' : ↥G := ⟨v, hEG hvE⟩ with hv'
        refine ⟨Subgroup.closure ({u', v'} : Set ↥G), ?_, ?_, ?_⟩
        · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
          exact ⟨Subgroup.mem_subgroupOf.2 huE, Subgroup.mem_subgroupOf.2 hvE⟩
        · refine two_le_pRank_closure_pair hp ?_ ?_ ?_ ?_ ?_
          · exact Subtype.ext (by simpa [hu'] using hu)
          · exact Subtype.ext (by simpa [hv'] using hv)
          · exact Subtype.ext (by simpa [hu', hv'] using huv)
          · exact fun h => hu1 (congrArg Subtype.val h)
          · intro j hj h
            exact hvu j hj (by simpa [hu', hv'] using congrArg Subtype.val h)
        · exact mem_normalizer_closure_pair (α := α) (β := β) (γ := γ) (δ := δ)
            (Subtype.ext (by simpa [hu', hv'] using h1))
            (Subtype.ext (by simpa [hu', hv'] using h2))
      · right
        obtain ⟨y', hy'A, rfl⟩ := Subgroup.mem_map.1 hyA
        have hy'p : y' ^ p = 1 := Subtype.ext (by simpa using hy)
        have hy'1 : y' ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
        have : Fact p.Prime := ⟨hp⟩
        have hord : orderOf y' = p := orderOf_eq_prime hy'p hy'1
        refine ⟨Subgroup.zpowers y', Subgroup.zpowers_le.2 hy'A, ?_,
          mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
        exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hy'p)
          (by rw [Nat.card_zpowers, hord, pow_one])

theorem glbCore_sup_of_coreGenerationVOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : CoreGenerationVOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) (hAe : IsElemAbelian p A)
    (hA : Nat.card A = p ^ 2) :
    GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEp, hEc, hall⟩ := h
  obtain ⟨T₀, hET⟩ := hEp.exists_le_sylow
  have hET0 : (T₀ : Subgroup G) = E :=
    (Subgroup.eq_of_le_of_card_ge hET (by rw [hEc, hS T₀])).symm
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (S : Subgroup G) ≤ ⊤) le_top S.isPGroup' T₀.isPGroup'
    (by
      change ¬ p ∣ (S : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity T₀, Sylow.card_eq_multiplicity S])
  have hA' : A.map (MulAut.conj l).toMonoidHom ≤ E := by
    rw [← hET0, ← hl]
    exact Subgroup.map_mono hAS
  have hAe' : IsElemAbelian p (A.map (MulAut.conj l).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hAe _
  have hAc' : Nat.card (A.map (MulAut.conj l).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hA]
  obtain ⟨Γ, hΓ, hnorm⟩ := hall _ hA' hAe' hAc'
  have hle : (⊤ : Subgroup G) ≤ GLBCore p 2 (T₀ : Subgroup G) ⊔
      GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
    rw [← hΓ, Subgroup.closure_le]
    intro g hg
    rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨Q, hQA, hrank, hgQ⟩
    · exact Subgroup.mem_sup_left (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2
        (hYE.trans hET0.symm.le) hrank hgY)
    · exact Subgroup.mem_sup_right (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQA hrank hgQ)
  have hTS : (T₀ : Subgroup G).map (MulAut.conj l⁻¹).toMonoidHom = S := by
    rw [← hl, map_conj_inv_map_conj]
  have hAA : (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = A :=
    map_conj_inv_map_conj A l
  have h2 := glbCore_le_comap_conj p 2 hp l⁻¹ hTS
  have h1 := glbCore_le_comap_conj p 1 hp l⁻¹ hAA
  have hle' : (⊤ : Subgroup G) ≤ (GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A).comap
      (MulAut.conj l⁻¹).toMonoidHom :=
    hle.trans (sup_le (h2.trans (Subgroup.comap_mono le_sup_left))
      (h1.trans (Subgroup.comap_mono le_sup_right)))
  rw [eq_top_iff]
  intro x _
  have hx := hle' (Subgroup.mem_top (l * x * l⁻¹))
  rw [Subgroup.mem_comap] at hx
  simpa [MulAut.conj_apply, mul_assoc] using hx

theorem coreGenerationVOf_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (h : CoreGenerationVOf G p) :
    CoreGenerationVOf H p := by
  obtain ⟨E, hEp, hEc, hall⟩ := h
  refine ⟨E.map e.toMonoidHom, hEp.map e.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEc]
  · intro A' hA'E hA'e hA'c
    set A : Subgroup G := A'.map e.symm.toMonoidHom with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (hA'E hy)
      have : e.symm.toMonoidHom y = x := by
        rw [← hxy]
        exact e.symm_apply_apply x
      rwa [this]
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective e.symm.injective, hA'c]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall A hAE hAe hAc
    refine ⟨e.toMonoidHom '' Γ, ?_, ?_⟩
    · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro _ ⟨g, hg, rfl⟩
      rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨Q, hQA, hrank, hgQ⟩
      · left
        refine ⟨Y.map e.toMonoidHom, Subgroup.map_mono hYE, ?_, ?_⟩
        · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Y)
        · rw [← Subgroup.map_equiv_normalizer_eq]
          exact Subgroup.mem_map_of_mem _ hgY
      · right
        refine ⟨Q.map e.toMonoidHom, ?_, ?_, ?_⟩
        · rintro _ ⟨q, hq, rfl⟩
          obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 (hQA hq)
          have : e.toMonoidHom q = x := by
            rw [← hxq]
            exact e.apply_symm_apply x
          rwa [this]
        · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Q)
        · rw [← Subgroup.map_equiv_normalizer_eq]
          exact Subgroup.mem_map_of_mem _ hgQ

end Abstract

section Perm

theorem coreGenerationVOf_of_check {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {a, b}) {V : VData} (hn : V.base.n = n)
    (hp : V.base.p.Prime) (ha : TabRep V.base.aT a) (hb : TabRep V.base.bT b)
    (h : checkV V = true) : CoreGenerationVOf ↥G V.base.p := by
  rcases V with ⟨D, ys, gk, wAs, wBs⟩
  dsimp only at hn hp ha hb ⊢
  subst hn
  simp only [checkV, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, anyBelow_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨heK, hncT⟩, hinv⟩, hinvg⟩, henum⟩, hsz⟩, hz⟩, hys⟩, hcov⟩, hgklen⟩, hkind⟩,
    hwAlen⟩, hwBlen⟩, hwords⟩ := h
  set S : List (Equiv.Perm (Fin D.n)) := [a, b] with hSdef
  obtain ⟨hgs, hgi⟩ := gs_rep ha hb hinv
  have haS : a ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hbS : b ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [haS, hbS]
  set S' : List (Equiv.Perm (Fin D.n)) := D.gWs.map (wordVal S) with hS'def
  have hgT : ∀ j, TabRep ((gT D).getD j (idTab D.n)) (S'.getD j 1) :=
    rep_map_words S _ _ hgs hgi D.gWs
  have hsize : (gT D).size = D.gWs.length := by simp [gT]
  have hgTi : ∀ j, TabRep ((gTi D).getD j (idTab D.n)) (S'.getD j 1)⁻¹ := by
    intro j
    by_cases hj : j < D.gWs.length
    · obtain ⟨h1, h2⟩ := hinvg j (by rw [hsize]; exact hj)
      rw [show (gTi D).getD j (idTab D.n) = (gTi D)[j]! by simp [gTi, gT, hj]]
      have := hgT j
      rw [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hj]] at this
      exact this.inv h1 h2
    · have hn : D.gWs[j]? = none := List.getElem?_eq_none (by omega)
      rw [show (gTi D).getD j (idTab D.n) = idTab D.n by simp [gTi, gT, hn],
        show S'.getD j 1 = 1 by simp [hS'def, hn]]
      simpa using TabRep.idTab (n := D.n)
  have hS'len : S'.length = D.gWs.length := by simp [hS'def]
  have hS'G : ∀ g ∈ S', g ∈ G := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG w
  set L : List (Equiv.Perm (Fin D.n)) := D.eW.map (wordVal S) with hLdef
  have heG : ∀ j, TabRep ((eGens D).getD j (idTab D.n)) (L.getD j 1) :=
    rep_map_words S _ _ hgs hgi D.eW
  have hEsz : (eGens D).size = D.eW.length := by simp [eGens]
  have hLlen : L.length = D.eW.length := by simp [hLdef]
  have heG' : ∀ j (hj : j < D.eW.length), TabRep (eGens D)[j]! (L.getD j 1) := by
    intro j hj
    have := heG j
    rwa [show (eGens D).getD j (idTab D.n) = (eGens D)[j]! by simp [eGens, hj]] at this
  have hLmem : ∀ j, j < D.eW.length → L.getD j 1 ∈ L := by
    intro j hj
    rw [show L.getD j 1 = L[j]'(by omega) by simp [List.getD_eq_getElem?_getD, hLlen, hj]]
    exact List.getElem_mem _
  have hA : ∀ g ∈ {g | g ∈ L}, ∃ j < (eGens D).size, TabRep (eGens D)[j]! g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < D.eW.length := by omega
    refine ⟨j, by rw [hEsz]; exact hj', ?_⟩
    have := heG' j hj'
    rwa [show L.getD j 1 = L[j] by simp [hj]] at this
  have hgensE : ∀ j < (eGens D).size, ∃ g ∈ {g | g ∈ L}, TabRep (eGens D)[j]! g := by
    intro j hj
    have hj' : j < D.eW.length := by rwa [hEsz] at hj
    exact ⟨L.getD j 1, hLmem j hj', heG' j hj'⟩
  have hE := enumerates_closure (A := {g | g ∈ L}) hA hgensE henum
  have hEcard : Nat.card (Subgroup.closure {g | g ∈ L}) = D.p ^ 3 := by
    rw [hE.card, Array.length_toList, hsz, heK]
  have hEp : IsPGroup D.p (Subgroup.closure {g | g ∈ L}) := IsPGroup.of_card hEcard
  have hEG : Subgroup.closure {g | g ∈ L} ≤ G := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG w
  have hnc : ∃ x ∈ Subgroup.closure {g | g ∈ L}, ∃ y ∈ Subgroup.closure {g | g ∈ L},
      x * y ≠ y * x := by
    obtain ⟨i, hi, j, hj, hij⟩ := hncT
    have hx : TabRep (eT D i) (L.getD i 1) := heG i
    have hy : TabRep (eT D j) (L.getD j 1) := heG j
    exact ⟨L.getD i 1, Subgroup.subset_closure (hLmem _ hi), L.getD j 1,
      Subgroup.subset_closure (hLmem _ hj),
      fun h1 => hij (((hx.comp hy).eq_iff (hy.comp hx)).2 h1)⟩
  simp only [zOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, allBelow_eq_true] at hz
  obtain ⟨⟨⟨hz0, hzp⟩, hz1⟩, hzc⟩ := hz
  set z : Equiv.Perm (Fin D.n) := L.getD 0 1 with hzdef
  have hzt : TabRep (eT D 0) z := heG 0
  have hzE : z ∈ Subgroup.closure {g | g ∈ L} := Subgroup.subset_closure (hLmem 0 hz0)
  have hzp' : z ^ D.p = 1 := ((powT_rep hzt D.p).eq_iff TabRep.idTab).1 hzp
  have hz1' : z ≠ 1 := fun h1 => hz1 ((hzt.eq_iff TabRep.idTab).2 h1)
  have hzcent : ∀ x ∈ Subgroup.closure {g | g ∈ L}, x * z = z * x := by
    have hcl : Subgroup.closure {g | g ∈ L} ≤
        Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin D.n))) := by
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hk' : k < D.eW.length := by omega
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hc := hzc k hk'
      have hgk : TabRep (eT D k) L[k] := by
        have := heG k
        rwa [show L.getD k 1 = L[k] by simp [hk]] at this
      exact (((hzt.comp hgk).eq_iff (hgk.comp hzt)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  have hys' : ∀ i < ys.length, vOK D (ys.getD i 0) = true := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.1 hys _ (List.getElem_mem hi)
  set vv : ℕ → Equiv.Perm (Fin D.n) := fun i => L.getD (ys.getD i 0) 1 with hvvdef
  have hvt : ∀ i, TabRep (eT D (ys.getD i 0)) (vv i) := fun i => heG _
  have hvfacts : ∀ i < ys.length, vv i ∈ Subgroup.closure {g | g ∈ L} ∧ (vv i) ^ D.p = 1 ∧
      (∀ k < D.p, vv i ≠ z ^ k) ∧ z * vv i = vv i * z := by
    intro i hi
    have h1 := hys' i hi
    simp only [vOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h1
    obtain ⟨⟨hj, hvp⟩, hvz⟩ := h1
    have hvE : vv i ∈ Subgroup.closure {g | g ∈ L} :=
      Subgroup.subset_closure (hLmem _ hj)
    exact ⟨hvE, ((powT_rep (hvt i) D.p).eq_iff TabRep.idTab).1 hvp,
      fun k hk h1 => hvz k hk (((hvt i).eq_iff (powT_rep hzt k)).2 h1), (hzcent _ hvE).symm⟩
  have hcover : ∀ t ∈ Subgroup.closure {g | g ∈ L}, ∃ i < ys.length, ∃ a' b' : ℕ,
      t = z ^ a' * (vv i) ^ b' := by
    intro t ht
    obtain ⟨tab, htab, hrep⟩ := hE.complete t ht
    have hc := (Array.all_eq_true'.1 (by simpa only [coverYOK] using hcov)) tab
      (Array.mem_toList_iff.1 htab)
    simp only [anyBelow_eq_true, beq_iff_eq] at hc
    obtain ⟨i, hi, a', -, b', -, he⟩ := hc
    exact ⟨i, hi, a', b', ((hrep.eq_iff ((powT_rep hzt a').comp (powT_rep (hvt i) b'))).1 he)⟩
  have hoz : orderOf z = D.p := by
    have : Fact D.p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hzp' hz1'
  refine coreGenerationVOf_of_gens hp hG (S := {a, b}) hEp hEcard hEG ?_
  intro A hAE hAe hAc
  have hzA : z ∈ A := mem_of_central hp hEcard hnc hAE hAe hAc hzE hzcent
  obtain ⟨t, htA, htz⟩ : ∃ t ∈ A, t ∉ Subgroup.zpowers z := by
    by_contra hcon
    have hle : A ≤ Subgroup.zpowers z := fun t ht => by
      by_contra h1
      exact hcon ⟨t, ht, h1⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hAc, Nat.card_zpowers, hoz] at h1
    have h2 := hp.two_le
    have : D.p ^ 2 ≤ D.p := h1
    nlinarith
  have htE : t ∈ Subgroup.closure {g | g ∈ L} := hAE htA
  obtain ⟨i, hi, a', b', hteq⟩ := hcover t htE
  obtain ⟨hvE, hvp, hvz, hzv⟩ := hvfacts i hi
  have hYcard : Nat.card (Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n)))) =
      D.p ^ 2 := card_closure_pair_of_pow hp hzp' hvp hzv hz1' hvz
  have htp : t ^ D.p = 1 := hAe.2 t htA
  have hzt' : z * t = t * z := (hzcent t htE).symm
  have htzk : ∀ k < D.p, t ≠ z ^ k := fun k hk h1 =>
    htz (h1 ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers z) k)
  have hZTcard : Nat.card (Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n)))) =
      D.p ^ 2 := card_closure_pair_of_pow hp hzp' htp hzt' hz1' htzk
  have hZTA : Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n))) ≤ A := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzA, htA⟩
  have hZTY : Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n))) ≤
      Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n))) := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Subgroup.subset_closure (by simp), ?_⟩
    rw [hteq]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hAY : Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n))) = A :=
    (Subgroup.eq_of_le_of_card_ge hZTY (by rw [hYcard, hZTcard])).symm.trans
      (Subgroup.eq_of_le_of_card_ge hZTA (by rw [hAc, hZTcard]))
  set Γ : Set (Equiv.Perm (Fin D.n)) := {g | ∃ j < D.gWs.length,
    (((gk.getD j default).kind = 0 ∨ (gk.getD j default).idx = i) ∨ (gk.getD j default).f2 = 0) ∧
      g = S'.getD j 1} with hΓdef
  have hall : ∀ w : List ℤ, (∀ l ∈ w, (((gk.getD (l.natAbs - 1) default).kind = 0 ∨
      (gk.getD (l.natAbs - 1) default).idx = i) ∨ (gk.getD (l.natAbs - 1) default).f2 = 0)) →
      wordVal S' w ∈ Subgroup.closure Γ := by
    intro w hw
    refine wordVal_mem_of S' _ w fun l hl => ?_
    by_cases hlt : l.natAbs - 1 < D.gWs.length
    · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
    · rw [List.getD_eq_default _ _ (by rw [hS'len]; omega)]
      exact Subgroup.one_mem _
  obtain ⟨⟨⟨hwA, hwB⟩, hoA⟩, hoB⟩ := hwords i hi
  simp only [wordOK, allowed, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hoA hoB
  have hA' : wordVal S' (wAs.getD i []) = a := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi (wAs.getD i [])
    rw [hwA] at h1
    exact h1.perm_eq ha
  have hB' : wordVal S' (wBs.getD i []) = b := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi (wBs.getD i [])
    rw [hwB] at h1
    exact h1.perm_eq hb
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rintro g ⟨j, hj, -, rfl⟩
    refine hS'G _ ?_
    rw [List.getD_eq_getElem _ _ (by rw [hS'len]; exact hj)]
    exact List.getElem_mem _
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact hall _ hoA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact hall _ hoB
  · rintro g ⟨j, hj, hok, rfl⟩
    have hj' : j < (gT D).size := by rw [hsize]; exact hj
    have hgj : TabRep (gT D)[j]! (S'.getD j 1) := by
      have := hgT j
      rwa [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hj]] at this
    have hk := hkind j hj'
    simp only [kindOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
    generalize gk.getD j default = f at hk hok
    obtain ⟨hidx, hk⟩ := hk
    by_cases hk0 : f.kind = 0
    · simp only [hk0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨e1, e2⟩ := hk
      obtain ⟨hvE', hvp', hvz', hzv'⟩ := hvfacts f.idx hidx
      left
      exact ⟨z, vv f.idx, hzE, hvE', hzp', hvp', hzv', hz1', hvz', f.f1, f.f2, f.f3, f.f4,
        ((hgj.comp hzt).eq_iff
          (((powT_rep hzt f.f1).comp (powT_rep (hvt f.idx) f.f2)).comp hgj)).1 e1,
        ((hgj.comp (hvt f.idx)).eq_iff
          (((powT_rep hzt f.f3).comp (powT_rep (hvt f.idx) f.f4)).comp hgj)).1 e2⟩
    · simp only [hk0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq] at hk
      obtain ⟨⟨e0, e1⟩, e2⟩ := hk
      right
      have hyt : TabRep (comp D.n (powT D.n (eT D 0) f.f1)
          (powT D.n (eT D (ys.getD f.idx 0)) f.f2)) (z ^ f.f1 * vv f.idx ^ f.f2) :=
        (powT_rep hzt f.f1).comp (powT_rep (hvt f.idx) f.f2)
      refine ⟨z ^ f.f1 * vv f.idx ^ f.f2, ?_, fun h1 => e0 ((hyt.eq_iff TabRep.idTab).2 h1),
        ((powT_rep hyt D.p).eq_iff TabRep.idTab).1 e1, f.f3,
        ((hgj.comp hyt).eq_iff ((powT_rep hyt f.f3).comp hgj)).1 e2⟩
      rcases hok with (hk0' | hidx') | hf2
      · exact absurd hk0' hk0
      · rw [hidx', ← hAY]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      · rw [hf2, pow_zero, mul_one]
        exact Subgroup.pow_mem _ hzA _

end Perm

end CFSG.AGLEmbedding.CoreD2
