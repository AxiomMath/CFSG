
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2PermSound
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Data.CoreD2Mathieu
import CFSG.GroupTheory.ElementaryAbelianTransport

@[expose] public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

@[expose] def CoreGenerationZOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ (E : Subgroup G) (Γ : Set G), IsPGroup p E ∧ Nat.card E = p ^ 3 ∧
    (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧ Subgroup.closure Γ = ⊤ ∧
    ∀ g ∈ Γ, (∃ Y : Subgroup G, Y ≤ E ∧ 2 ≤ Open.pRank p Y ∧
        g ∈ Subgroup.normalizer (Y : Set G)) ∨
      ∃ u ∈ E, u ≠ 1 ∧ u ^ p = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧
        g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G)

section Abstract

variable {X : Type*} [Group X]

theorem mem_normalizer_zpowers_of_mul_eq [Finite X] {u g : X} {α : ℕ} (h : g * u = u ^ α * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup X) : Set X) := by
  have hcu : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
    rw [mul_inv_eq_iff_eq_mul.2 h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  have hle : Subgroup.zpowers u ≤ (Subgroup.zpowers u).comap (MulAut.conj g).toMonoidHom :=
    Subgroup.zpowers_le.2 hcu
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem isElemAbelian_zpowers {p : ℕ} {u : X} (hu : u ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers u) := CFSG.Open.isElemAbelian_zpowers hu

theorem mem_of_central [Finite X] {p : ℕ} (hp : p.Prime) {E A : Subgroup X}
    (hEc : Nat.card E = p ^ 3) (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hAE : A ≤ E)
    (hAe : IsElemAbelian p A) (hA : Nat.card A = p ^ 2) {u : X} (huE : u ∈ E)
    (hu : ∀ x ∈ E, x * u = u * x) : u ∈ A := by
  by_contra huA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hrc : ((A : Set X) ∪ {u}).Pairwise Commute := by
    rintro x (hx | hx) y (hy | hy) hxy
    · exact hcomm x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hu x (hAE hx)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hu y (hAE hy)).symm
    · rw [Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  have hBcomm := Subgroup.isMulCommutative_closure hrc
  set B := Subgroup.closure ((A : Set X) ∪ {u}) with hB
  have hAB : A ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have huB : u ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hBE : B ≤ E := by
    rw [hB, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hAE hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact huE
  have hd1 : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hd2 : Nat.card B ∣ p ^ 3 := hEc ▸ Subgroup.card_dvd_of_le hBE
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow hp).1 hd2
  rw [hA, hm] at hd1
  have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd1
  have hm' : m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl
  · have : A = B := Subgroup.eq_of_le_of_card_ge hAB (by rw [hA, hm])
    exact huA (this ▸ huB)
  · have : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEc, hm])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    rw [← this] at hx hy
    exact hxy (congrArg Subtype.val (hBcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem glbCore_le_comap_conj [Finite X] (p k : ℕ) (hp : p.Prime) {P P' : Subgroup X} (l : X)
    (h : P.map (MulAut.conj l).toMonoidHom = P') :
    GLBCore p k P ≤ (GLBCore p k P').comap (MulAut.conj l).toMonoidHom := by
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p k _ _).mpr fun Q hQ hrank => ?_
  intro n hn
  rw [Subgroup.mem_comap]
  refine CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k (Q := Q.map (MulAut.conj l).toMonoidHom)
    (by rw [← h]; exact Subgroup.map_mono hQ) ?_ ?_
  · rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _
      (MulAut.conj l).injective Q]
  · exact Subgroup.le_normalizer_map (MulAut.conj l).toMonoidHom ⟨n, hn, rfl⟩

theorem map_conj_inv_map_conj (P : Subgroup X) (l : X) :
    (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = P := by
  rw [Subgroup.map_map]
  have : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem coreGenerationZOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime) {S : Set X}
    (hS : G = Subgroup.closure S) {E : Subgroup X} (hEp : IsPGroup p E)
    (hEc : Nat.card E = p ^ 3) (hEG : E ≤ G) (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x)
    {Γ : Set X} (hΓG : Γ ⊆ G) (hgen : S ⊆ Subgroup.closure Γ)
    (hΓ : ∀ g ∈ Γ,
      (∃ u v : X, u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧
        (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
          g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
      (∃ u ∈ E, u ≠ 1 ∧ u ^ p = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧ ∃ α : ℕ, g * u = u ^ α * g)) :
    CoreGenerationZOf ↥G p := by
  refine ⟨E.subgroupOf G, {g : ↥G | (g : X) ∈ Γ}, hEp.comap_subtype, ?_, ?_, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hEG hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨y, hEG hy⟩, Subgroup.mem_subgroupOf.2 hy,
      fun h => hxy (congrArg Subtype.val h)⟩
  · rw [eq_top_iff]
    intro h _
    have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype = Subgroup.closure Γ := by
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
    rcases hΓ _ hg with ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ |
      ⟨u, huE, hu1, hu, hcent, α, h1⟩
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
      refine ⟨⟨u, hEG huE⟩, Subgroup.mem_subgroupOf.2 huE,
        fun h => hu1 (congrArg Subtype.val h), Subtype.ext (by simpa using hu), ?_,
        mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
      intro x hx
      exact Subtype.ext (by simpa using hcent x (Subgroup.mem_subgroupOf.1 hx))

theorem glbCore_sup_of_coreGenerationZOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : CoreGenerationZOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) (hAe : IsElemAbelian p A)
    (hA : Nat.card A = p ^ 2) :
    GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, Γ, hEp, hEc, hnc, hΓ, hnorm⟩ := h
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
  have hle : (⊤ : Subgroup G) ≤ GLBCore p 2 (T₀ : Subgroup G) ⊔
      GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
    rw [← hΓ, Subgroup.closure_le]
    intro g hg
    rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨u, huE, hu1, hu, hcent, hgu⟩
    · exact Subgroup.mem_sup_left (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2
        (hYE.trans hET0.symm.le) hrank hgY)
    · have huA := mem_of_central hp hEc hnc hA' hAe' hAc' huE hcent
      have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf u = p := orderOf_eq_prime hu hu1
      have hr : 1 ≤ Open.pRank p (Subgroup.zpowers u) :=
        CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hu)
          (by rw [Nat.card_zpowers, hord, pow_one])
      exact Subgroup.mem_sup_right (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1
        (Subgroup.zpowers_le.2 huA) hr hgu)
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

end Abstract

section Perm

theorem coreGenerationZOf_of_check {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {a, b}) {D : Data} (hn : D.n = n)
    (hp : D.p.Prime) (ha : TabRep D.aT a) (hb : TabRep D.bT b) (h : checkZ D = true) :
    CoreGenerationZOf ↥G D.p := by
  subst hn
  simp only [checkZ, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, anyBelow_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨heK, hncT⟩, hinv⟩, hinvg⟩, henum⟩, hsz⟩, hpairs⟩, hlen⟩, hfus⟩, hwA⟩, hwB⟩ := h
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
  have hpairs' : ∀ q ∈ D.pairs, pairOKZ D q = true := List.all_eq_true.1 hpairs
  have hpair : ∀ q ∈ D.pairs,
      (∃ u v : Equiv.Perm (Fin D.n),
        u ∈ Subgroup.closure {g | g ∈ L} ∧ v ∈ Subgroup.closure {g | g ∈ L} ∧ u ^ D.p = 1 ∧
        v ^ D.p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ (∀ j < D.p, v ≠ u ^ j) ∧
        TabRep (eT D q.1) u ∧ TabRep (eT D q.2) v) ∨
      (∃ u : Equiv.Perm (Fin D.n), u ∈ Subgroup.closure {g | g ∈ L} ∧ u ≠ 1 ∧ u ^ D.p = 1 ∧
        (∀ x ∈ Subgroup.closure {g | g ∈ L}, x * u = u * x) ∧ q.1 = q.2 ∧
        TabRep (eT D q.1) u ∧ TabRep (eT D q.2) u) := by
    intro q hq
    have h1 := hpairs' q hq
    by_cases hq12 : q.1 = q.2
    · right
      simp only [pairOKZ, beq_iff_eq, hq12, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        allBelow_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h1
      obtain ⟨⟨⟨hq2, hxp⟩, hx1⟩, hcent⟩ := h1
      have hu : TabRep (eT D q.2) (L.getD q.2 1) := heG q.2
      refine ⟨L.getD q.2 1, Subgroup.subset_closure (hLmem _ hq2),
        fun h1 => hx1 ((hu.eq_iff TabRep.idTab).2 h1),
        ((powT_rep hu D.p).eq_iff TabRep.idTab).1 hxp, ?_, hq12, hq12 ▸ hu, hu⟩
      have hcl : Subgroup.closure {g | g ∈ L} ≤
          Subgroup.centralizer ({L.getD q.2 1} : Set (Equiv.Perm (Fin D.n))) := by
        rw [Subgroup.closure_le]
        intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        have hk' : k < D.eW.length := by omega
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hc := hcent k hk'
        have hgk : TabRep (eT D k) L[k] := by
          have := heG k
          rwa [show L.getD k 1 = L[k] by simp [hk]] at this
        exact (((hu.comp hgk).eq_iff (hgk.comp hu)).1 hc).symm
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
    · left
      simp only [pairOKZ, beq_iff_eq, hq12, ↓reduceIte, pairOK, Bool.and_eq_true,
        decide_eq_true_eq, allBelow_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h1
      obtain ⟨⟨⟨⟨⟨⟨hq1, hq2⟩, hxp⟩, hyp⟩, hcomm⟩, hx1⟩, hne⟩ := h1
      have hu : TabRep (eT D q.1) (L.getD q.1 1) := heG q.1
      have hv : TabRep (eT D q.2) (L.getD q.2 1) := heG q.2
      refine ⟨L.getD q.1 1, L.getD q.2 1, Subgroup.subset_closure (hLmem _ hq1),
        Subgroup.subset_closure (hLmem _ hq2), ((powT_rep hu D.p).eq_iff TabRep.idTab).1 hxp,
        ((powT_rep hv D.p).eq_iff TabRep.idTab).1 hyp, ((hu.comp hv).eq_iff (hv.comp hu)).1 hcomm,
        fun h1 => hx1 ((hu.eq_iff TabRep.idTab).2 h1), fun j hj h1 => hne j hj
          ((hv.eq_iff (powT_rep hu j)).2 h1), hu, hv⟩
  have hfus' : ∀ g ∈ {g | g ∈ S'},
      (∃ u v : Equiv.Perm (Fin D.n),
        u ∈ Subgroup.closure {g | g ∈ L} ∧ v ∈ Subgroup.closure {g | g ∈ L} ∧ u ^ D.p = 1 ∧
        v ^ D.p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ (∀ j < D.p, v ≠ u ^ j) ∧
        ∃ α β γ δ : ℕ, g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
      (∃ u ∈ Subgroup.closure {g | g ∈ L}, u ≠ 1 ∧ u ^ D.p = 1 ∧
        (∀ x ∈ Subgroup.closure {g | g ∈ L}, x * u = u * x) ∧ ∃ α : ℕ, g * u = u ^ α * g) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < (gT D).size := by rw [hsize]; simpa [hS'def] using hj
    have hjl : j < D.gWs.length := by rw [← hsize]; exact hj'
    have hf := hfus
    unfold fusOK at hf
    simp only [allBelow_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
    have hf := hf j hj'
    generalize hF : D.fd.getD j default = f at hf
    obtain ⟨⟨hfp, e1⟩, e2⟩ := hf
    have hqmem : D.pairs.getD f.pair (0, 0) ∈ D.pairs := by
      rw [show D.pairs.getD f.pair (0, 0) = D.pairs[f.pair] by simp [hfp]]
      exact List.getElem_mem _
    have hgj : TabRep (gT D)[j]! S'[j] := by
      have := hgT j
      rwa [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hjl],
        show S'.getD j 1 = S'[j] by simp [hS'def, hjl]] at this
    rcases hpair _ hqmem with ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, hut, hvt⟩ |
      ⟨u, huE, hu1, hu, hcent, -, hut, hvt⟩
    · left
      refine ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, f.α, f.β, f.γ, f.δ, ?_, ?_⟩
      · exact ((hgj.comp hut).eq_iff (((powT_rep hut f.α).comp (powT_rep hvt f.β)).comp hgj)).1 e1
      · exact ((hgj.comp hvt).eq_iff (((powT_rep hut f.γ).comp (powT_rep hvt f.δ)).comp hgj)).1 e2
    · right
      refine ⟨u, huE, hu1, hu, hcent, f.α + f.β, ?_⟩
      have := ((hgj.comp hut).eq_iff (((powT_rep hut f.α).comp (powT_rep hvt f.β)).comp hgj)).1 e1
      rwa [← pow_add] at this
  have hA' : wordVal S' D.wA = a := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi D.wA
    rw [hwA] at h1
    exact h1.perm_eq ha
  have hB' : wordVal S' D.wB = b := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi D.wB
    rw [hwB] at h1
    exact h1.perm_eq hb
  refine coreGenerationZOf_of_gens hp hG (S := {a, b}) hEp hEcard hEG hnc (Γ := {g | g ∈ S'})
    (fun g hg => hS'G g hg) ?_ hfus'
  intro z hz
  rcases hz with rfl | rfl
  · rw [← hA']
    exact wordVal_mem S' (Subgroup.closure {g | g ∈ S'}) (fun g hg => Subgroup.subset_closure hg) _
  · rw [← hB']
    exact wordVal_mem S' (Subgroup.closure {g | g ∈ S'}) (fun g hg => Subgroup.subset_closure hg) _

end Perm

end CFSG.AGLEmbedding.CoreD2

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open

instance finite_carrier_M12 : Finite (NativeSporadic.Carrier .M12) :=
  inferInstanceAs (Finite NativeSporadic.M12)

abbrev m12CoreA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12CoreB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem m12_core_tab_a : TabRep m12CoreData.aT m12CoreA := ⟨rfl, by decide⟩

theorem m12_core_tab_b : TabRep m12CoreData.bT m12CoreB := ⟨rfl, by decide⟩

instance finite_carrier_M24 : Finite (NativeSporadic.Carrier .M24) :=
  inferInstanceAs (Finite NativeSporadic.M24)

theorem m24_core_tab_a : TabRep m24CoreData.aT CFSG.Sporadic.Mathieu.m24gA := ⟨rfl, by decide⟩

theorem m24_core_tab_b : TabRep m24CoreData.bT CFSG.Sporadic.Mathieu.m24gB := ⟨rfl, by decide⟩

theorem card_sylow_M24_three :
    ∀ T : Sylow 3 (NativeSporadic.Carrier .M24), Nat.card T = 3 ^ 3 := by
  intro T
  have hcard : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  have h0 : (244823040 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 3 ^ 3 ∣ 244823040)
  have h2 : ¬ 4 ≤ (244823040 : ℕ).factorization 3 := fun h => by
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hcard, show (244823040 : ℕ).factorization 3 = 3 by omega]

end CFSG.AGLEmbedding
