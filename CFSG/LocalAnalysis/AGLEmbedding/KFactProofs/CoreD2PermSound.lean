module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.FusionCase
public import Certificates.Data.CoreD2Perm
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

@[expose] def CoreGenerationOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ (E : Subgroup G) (Γ : Set G), IsPGroup p E ∧ Subgroup.closure Γ = ⊤ ∧
    ∀ g ∈ Γ, ∃ Y : Subgroup G, Y ≤ E ∧ 2 ≤ Open.pRank p Y ∧ g ∈ Subgroup.normalizer (Y : Set G)

section Abstract

variable {X : Type*} [Group X]

theorem isElemAbelian_closure_pair {p : ℕ} {u v : X} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (huv : u * v = v * u) : IsElemAbelian p (Subgroup.closure ({u, v} : Set X)) := by
  have hrc : ({u, v} : Set X).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact huv
    · exact huv.symm
    · exact absurd rfl hab
  have := Subgroup.isMulCommutative_closure hrc
  refine ⟨this, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    exacts [hu, hv]
  | one => exact one_pow p
  | mul x y hx hy hx' hy' =>
    rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, hx', hy', one_mul]
  | inv x hx hx' => rw [inv_pow, hx', inv_one]

theorem card_closure_pair {p : ℕ} (hp : p.Prime) {a b : X} (hab : Commute a b)
    (ha : orderOf a = p) (hb : orderOf b = p) (hind : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set X)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* X :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : X) * y = 1 := hxy
    have hx : (x : X) = (y : X)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : X) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : X) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set X) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

theorem two_le_pRank_closure_pair [Finite X] {p : ℕ} (hp : p.Prime) {u v : X} (hu : u ^ p = 1)
    (hv : v ^ p = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hvu : ∀ j < p, v ≠ u ^ j) :
    2 ≤ Open.pRank p (Subgroup.closure ({u, v} : Set X)) := by
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
  exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_closure_pair hu hv huv)
    (card_closure_pair hp huv hou hov hind)

theorem mem_normalizer_closure_pair [Finite X] {u v g : X} {α β γ δ : ℕ}
    (h1 : g * u = (u ^ α * v ^ β) * g) (h2 : g * v = (u ^ γ * v ^ δ) * g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({u, v} : Set X) : Subgroup X) : Set X) := by
  have hu : u ∈ Subgroup.closure ({u, v} : Set X) := Subgroup.subset_closure (by simp)
  have hv : v ∈ Subgroup.closure ({u, v} : Set X) := Subgroup.subset_closure (by simp)
  have hcu : g * u * g⁻¹ ∈ Subgroup.closure ({u, v} : Set X) := by
    rw [mul_inv_eq_iff_eq_mul.2 h1]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _) (Subgroup.pow_mem _ hv _)
  have hcv : g * v * g⁻¹ ∈ Subgroup.closure ({u, v} : Set X) := by
    rw [mul_inv_eq_iff_eq_mul.2 h2]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _) (Subgroup.pow_mem _ hv _)
  have hle : Subgroup.closure ({u, v} : Set X) ≤
      (Subgroup.closure ({u, v} : Set X)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hcu, hcv⟩
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem coreGenerationOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime) {S : Set X}
    (hS : G = Subgroup.closure S) {E : Subgroup X} (hEp : IsPGroup p E) (hEG : E ≤ G)
    {Γ : Set X} (hΓG : Γ ⊆ G) (hgen : S ⊆ Subgroup.closure Γ)
    (hΓ : ∀ g ∈ Γ, ∃ u v : X, u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧
      u ≠ 1 ∧ (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
        g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) :
    CoreGenerationOf ↥G p := by
  refine ⟨E.subgroupOf G, {g : ↥G | (g : X) ∈ Γ}, hEp.comap_subtype, ?_, ?_⟩
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
    obtain ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ := hΓ _ hg
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
        (Subtype.ext (by simpa [hu', hv'] using h1)) (Subtype.ext (by simpa [hu', hv'] using h2))

theorem glbCore_two_eq_top_of_coreGenerationOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (h : CoreGenerationOf G p) (T : Sylow p G) :
    GLBCore p 2 (T : Subgroup G) = ⊤ := by
  obtain ⟨E, Γ, hEp, hΓ, hnorm⟩ := h
  obtain ⟨T₀, hET⟩ := hEp.exists_le_sylow
  have h0 : GLBCore p 2 (T₀ : Subgroup G) = ⊤ := by
    rw [eq_top_iff, ← hΓ, Subgroup.closure_le]
    intro g hg
    obtain ⟨Y, hYE, hrank, hgY⟩ := hnorm g hg
    exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2 (hYE.trans hET) hrank hgY
  exact CFSG.AGLEmbeddingD2.glbCore_two_eq_top_of_sylow T₀ h0 T

theorem coreGenerationOf_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (h : CoreGenerationOf G p) : CoreGenerationOf H p := by
  obtain ⟨E, Γ, hEp, hΓ, hnorm⟩ := h
  refine ⟨E.map e.toMonoidHom, e.toMonoidHom '' Γ, hEp.map e.toMonoidHom, ?_, ?_⟩
  · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨Y, hYE, hrank, hgY⟩ := hnorm g hg
    refine ⟨Y.map e.toMonoidHom, Subgroup.map_mono hYE, ?_, ?_⟩
    · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Y)
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.mem_map_of_mem _ hgY

end Abstract

section Perm

theorem gs_rep {D : Data} {a b : Equiv.Perm (Fin D.n)} (ha : TabRep D.aT a) (hb : TabRep D.bT b)
    (hinv : ∀ k < 2, (giT D)[k]!.size = D.n ∧ comp D.n (giT D)[k]! (gsT D)[k]! = idTab D.n) :
    (∀ j, TabRep ((gsT D).getD j (idTab D.n)) ([a, b].getD j 1)) ∧
      ∀ j, TabRep ((giT D).getD j (idTab D.n)) ([a, b].getD j 1)⁻¹ := by
  constructor
  · intro j
    match j with
    | 0 =>
      rw [show (gsT D).getD 0 (idTab D.n) = D.aT by simp [gsT]]
      exact ha
    | 1 =>
      rw [show (gsT D).getD 1 (idTab D.n) = D.bT by simp [gsT]]
      exact hb
    | j + 2 =>
      rw [show (gsT D).getD (j + 2) (idTab D.n) = idTab D.n by simp [gsT]]
      simpa using TabRep.idTab (n := D.n)
  · intro j
    match j with
    | 0 =>
      obtain ⟨h1, h2⟩ := hinv 0 (by norm_num)
      rw [show (giT D).getD 0 (idTab D.n) = (giT D)[0]! by simp [giT, gsT]]
      exact ha.inv h1 (by simpa [gsT] using h2)
    | 1 =>
      obtain ⟨h1, h2⟩ := hinv 1 (by norm_num)
      rw [show (giT D).getD 1 (idTab D.n) = (giT D)[1]! by simp [giT, gsT]]
      exact hb.inv h1 (by simpa [gsT] using h2)
    | j + 2 =>
      rw [show (giT D).getD (j + 2) (idTab D.n) = idTab D.n by simp [giT, gsT]]
      simpa using TabRep.idTab (n := D.n)

theorem rep_map_words {n : ℕ} (S : List (Equiv.Perm (Fin n))) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹) (ws : List (List ℤ)) (j : ℕ) :
    TabRep ((ws.map (wordT n gs gi)).toArray.getD j (idTab n)) ((ws.map (wordVal S)).getD j 1) := by
  by_cases hj : j < ws.length
  · rw [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) = wordT n gs gi ws[j] by simp [hj],
      show (ws.map (wordVal S)).getD j 1 = wordVal S ws[j] by simp [hj]]
    exact wordT_rep S gs gi hgs hgi _
  · have hn : ws[j]? = none := List.getElem?_eq_none (by omega)
    rw [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) = idTab n by simp [hn],
      show (ws.map (wordVal S)).getD j 1 = 1 by simp [hn]]
    exact TabRep.idTab

end Perm

end CFSG.AGLEmbedding.CoreD2
