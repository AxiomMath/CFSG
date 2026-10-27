module

public import CFSG.ClassicalInvolution.Q3.Sec13End16J
public import CFSG.ClassicalInvolution.Q3.Sec13End15H

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

private theorem e16k_zmod2_eq : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide

private theorem e16k_sum_six (w : Fin 6 → ZMod 2) :
    ∑ i ∈ ({2, 3, 4, 5} : Finset (Fin 6)), w i + ∑ i ∈ ({0, 3, 4, 5} : Finset (Fin 6)), w i +
      ∑ i ∈ ({1, 3, 4, 5} : Finset (Fin 6)), w i = ∑ i, w i := by
  rw [Fin.sum_univ_six]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (w 3 + w 4 + w 5) * h2

private theorem e16k_key : ∀ i : Fin 6,
    (if i ∈ ({2, 3, 4, 5} : Finset (Fin 6)) then (1 : ZMod 2) else 0) +
      (if i ∈ ({0, 3, 4, 5} : Finset (Fin 6)) then 1 else 0) +
      (if i ∈ ({1, 3, 4, 5} : Finset (Fin 6)) then 1 else 0) = 1 := by
  decide

private theorem e16k_zOf_vec_eq {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) (i : Fin n) :
    (AE.zOf (AE.emb α h)).vec i = if i ∈ α then 1 else 0 := by
  have hr : i ∈ Set.range (AE.emb α h) ↔ i ∈ α := by
    rw [AE.range_emb, Finset.mem_coe]
  rw [AE.zOf_vec_apply]
  by_cases hi : i ∈ α
  · simp [hi, hr]
  · simp [hi, hr]

private theorem e16k_mul_vec {n : ℕ} {a b : AE.Wr n} (ha : a.perm = 1) (i : Fin n) :
    (a * b).vec i = a.vec i + b.vec i := by
  rw [AE.Wr.mul_vec, ha] <;> rfl

private theorem e16k_zOf_sq {n : ℕ} (ι : Fin 4 ↪ Fin n) : AE.zOf ι * AE.zOf ι = 1 := by
  have h := mul_inv_cancel (AE.zOf ι)
  rwa [AE.zOf_inv] at h

private theorem e16k_zOf_prod (h₁ : ({2, 3, 4, 5} : Finset (Fin 6)).card = 4)
    (h₂ : ({0, 3, 4, 5} : Finset (Fin 6)).card = 4)
    (h₃ : ({1, 3, 4, 5} : Finset (Fin 6)).card = 4) :
    AE.zOf (AE.emb _ h₁) * AE.zOf (AE.emb _ h₂) * AE.zOf (AE.emb _ h₃) =
      AE.Wr.allOnes 6 := by
  have hab : (AE.zOf (AE.emb _ h₁) * AE.zOf (AE.emb _ h₂)).perm = 1 := by
    rw [AE.Wr.mul_perm, AE.zOf_perm, AE.zOf_perm, mul_one]
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · rw [e16k_mul_vec hab, e16k_mul_vec (AE.zOf_perm _), e16k_zOf_vec_eq, e16k_zOf_vec_eq,
      e16k_zOf_vec_eq]
    exact e16k_key i
  · simp [AE.Wr.mul_perm, AE.zOf_perm, AE.Wr.allOnes]

private theorem e16k_mem_normalizer {e : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({e} : Set G)) : e ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hL hl) e (Set.mem_singleton e)).symm)

private theorem e16k_mem_zGroup {Ω : Set (Subgroup G)} {L : Subgroup G} (hL : L ∈ Ω) {r : G}
    (hr : IsUniqueInvolution L r) : r ∈ zGroup Ω := by
  unfold zGroup
  apply Subgroup.subset_closure
  show ∃ K ∈ Ω, IsUniqueInvolution K r
  exact ⟨L, hL, hr⟩

private theorem e16k_mem_zPoints {Ω : Set (Subgroup G)} {L : Subgroup G} (hL : L ∈ Ω)
    {q : zGroup Ω} (hq : IsUniqueInvolution L (q : G)) : q ∈ zPoints Ω := by
  show ∃ K ∈ Ω, IsUniqueInvolution K (q : G)
  exact ⟨L, hL, hq⟩

private theorem e16k_conj_mem {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {d e : G}
    (hde : d * e = e * d) {L : Subgroup G} (hL : L ∈ centMembers Ω e) :
    conjSub d L ∈ centMembers Ω e := by
  refine ⟨hΩ.conjInvariant d L hL.1, fun y hy => ?_⟩
  have hdinv : d⁻¹ * e = e * d⁻¹ := by
    calc d⁻¹ * e = d⁻¹ * (e * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * e) * d⁻¹ := by rw [hde]
      _ = e * d⁻¹ := by group
  have ht : (d⁻¹ * y * d) * e = e * (d⁻¹ * y * d) :=
    (Subgroup.mem_centralizer_iff.mp (hL.2 (mem_conjSub_iff.mp hy)) e
      (Set.mem_singleton e)).symm
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  calc e * y = e * d * (d⁻¹ * y * d) * d⁻¹ := by group
    _ = d * e * (d⁻¹ * y * d) * d⁻¹ := by rw [← hde]
    _ = d * (e * (d⁻¹ * y * d)) * d⁻¹ := by group
    _ = d * ((d⁻¹ * y * d) * e) * d⁻¹ := by rw [ht]
    _ = d * (d⁻¹ * y * d) * (e * d⁻¹) := by group
    _ = d * (d⁻¹ * y * d) * (d⁻¹ * e) := by rw [hdinv]
    _ = y * e := by group

private theorem e16k_psi_mem {Ω : Set (Subgroup G)} {e : G}
    {ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)} {L : Subgroup G}
    {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hψ : ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α hα b)
    (y : ↥(pSpan (centMembers Ω e))) (hy : (y : G) ∈ L) :
    ((ψ y : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α hα b := by
  rw [← hψ]
  exact ⟨ψ y, ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩

private theorem e16k_psi_surj {Ω : Set (Subgroup G)} {e : G}
    {ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)} {L : Subgroup G}
    {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hψ : ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α hα b)
    {w : AE.Wr 6} (hw : w ∈ AE.memAt α hα b) :
    ∃ y : ↥(pSpan (centMembers Ω e)), (y : G) ∈ L ∧
      ((ψ y : ↥(AE.aeSub 6)) : AE.Wr 6) = w := by
  rw [← hψ] at hw
  obtain ⟨x', hx', hxw⟩ := Subgroup.mem_map.mp hw
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
  rw [← hxw, ← hyx]
  rfl

private theorem e16k_psi_sq {Ω : Set (Subgroup G)} {e : G}
    {ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)} (q : ↥(pSpan (centMembers Ω e)))
    (hq : q * q = 1) :
    ((ψ q : ↥(AE.aeSub 6)) : AE.Wr 6) * ((ψ q : ↥(AE.aeSub 6)) : AE.Wr 6) = 1 := by
  have h1 : ψ q * ψ q = 1 := by rw [← map_mul, hq, map_one]
  have h2 := congrArg Subtype.val h1
  simpa using h2

private noncomputable def e16k_pt {Ω : Set (Subgroup G)} {e : G}
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)) (α : Finset (Fin 6)) (hα : α.card = 4) :
    ↥(pSpan (centMembers Ω e)) :=
  ψ.symm ⟨AE.zOf (AE.emb α hα), AE.memK_le_aeSub (AE.emb α hα) (AE.zOf_mem_memK (AE.emb α hα))⟩

private theorem e16k_psi_pt {Ω : Set (Subgroup G)} {e : G}
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)) (α : Finset (Fin 6)) (hα : α.card = 4) :
    ((ψ (e16k_pt ψ α hα) : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  unfold e16k_pt
  rw [MulEquiv.apply_symm_apply]

private theorem e16k_eq_pt {Ω : Set (Subgroup G)} {e : G}
    {ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)} {L : Subgroup G}
    (hL : L ∈ centMembers Ω e) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hψ : ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α hα b)
    {y : G} (hy : y ∈ L) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y = (e16k_pt ψ α hα : G) := by
  have hX : y ∈ pSpan (centMembers Ω e) := le_pSpan hL hy
  have hq2 : (⟨y, hX⟩ : ↥(pSpan (centMembers Ω e))) * ⟨y, hX⟩ = 1 := Subtype.ext hy2
  have hmem := e16k_psi_mem hψ ⟨y, hX⟩ hy
  have hsq := e16k_psi_sq (ψ := ψ) ⟨y, hX⟩ hq2
  rcases AE.eq_of_mem_memAt_mul_self hmem hsq with h3 | h3
  · exfalso
    apply hy1
    have hq1 : (⟨y, hX⟩ : ↥(pSpan (centMembers Ω e))) = 1 :=
      ψ.injective (by rw [map_one]; exact Subtype.ext h3)
    exact congrArg Subtype.val hq1
  · have hq3 : (⟨y, hX⟩ : ↥(pSpan (centMembers Ω e))) = e16k_pt ψ α hα :=
      ψ.injective (Subtype.ext (h3.trans (e16k_psi_pt ψ α hα).symm))
    exact congrArg Subtype.val hq3

private theorem e16k_isUnique {Ω : Set (Subgroup G)} {e : G}
    {ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)} {L : Subgroup G}
    (hL : L ∈ centMembers Ω e) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hψ : ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α hα b) :
    IsUniqueInvolution L (e16k_pt ψ α hα : G) := by
  obtain ⟨y, hyL, hy⟩ := e16k_psi_surj hψ (AE.zOf_mem_memAt α hα b)
  have hyp : y = e16k_pt ψ α hα :=
    ψ.injective (Subtype.ext (hy.trans (e16k_psi_pt ψ α hα).symm))
  have hptL : (e16k_pt ψ α hα : G) ∈ L := by
    rw [← hyp]
    exact hyL
  have hsq : (e16k_pt ψ α hα : G) * (e16k_pt ψ α hα : G) = 1 := by
    have h1 : ((ψ (e16k_pt ψ α hα) : ↥(AE.aeSub 6)) : AE.Wr 6) *
        ((ψ (e16k_pt ψ α hα) : ↥(AE.aeSub 6)) : AE.Wr 6) = 1 := by
      rw [e16k_psi_pt]
      exact e16k_zOf_sq _
    have h2 : ψ (e16k_pt ψ α hα) * ψ (e16k_pt ψ α hα) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, h1, Subgroup.coe_one])
    have h3 : e16k_pt ψ α hα * e16k_pt ψ α hα = 1 :=
      ψ.injective (by rw [map_mul, map_one]; exact h2)
    exact congrArg Subtype.val h3
  refine ⟨hptL, ?_, hsq, ?_⟩
  · intro h1
    have hpt1 : e16k_pt ψ α hα = 1 := Subtype.ext h1
    have h2 := e16k_psi_pt ψ α hα
    rw [hpt1, map_one, Subgroup.coe_one] at h2
    exact AE.zOf_ne_one (AE.emb α hα) h2.symm
  · intro y' hy'L hy'2
    by_cases hy'1 : y' = 1
    · exact Or.inl hy'1
    · exact Or.inr (e16k_eq_pt hL hψ hy'L hy'2 hy'1)

private theorem e16k_pt_inj {Ω : Set (Subgroup G)} {e : G}
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)) {α β : Finset (Fin 6)}
    {hα : α.card = 4} {hβ : β.card = 4}
    (h : (e16k_pt ψ α hα : G) = e16k_pt ψ β hβ) : α = β := by
  have h1 : e16k_pt ψ α hα = e16k_pt ψ β hβ := Subtype.ext h
  have h2 : AE.zOf (AE.emb α hα) = AE.zOf (AE.emb β hβ) := by
    rw [← e16k_psi_pt ψ α hα, ← e16k_psi_pt ψ β hβ, h1]
  have h3 := AE.range_eq_of_zOf_eq h2
  rw [AE.range_emb, AE.range_emb] at h3
  exact Finset.coe_injective h3

private theorem e16k_prod {Ω : Set (Subgroup G)} {e : G}
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)) (he : e ∈ pSpan (centMembers Ω e))
    (hψe : ((ψ ⟨e, he⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.Wr.allOnes 6)
    (h₁ : ({2, 3, 4, 5} : Finset (Fin 6)).card = 4)
    (h₂ : ({0, 3, 4, 5} : Finset (Fin 6)).card = 4)
    (h₃ : ({1, 3, 4, 5} : Finset (Fin 6)).card = 4) :
    e16k_pt ψ _ h₁ * e16k_pt ψ _ h₂ * e16k_pt ψ _ h₃ = ⟨e, he⟩ := by
  apply ψ.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, e16k_psi_pt, e16k_psi_pt, e16k_psi_pt, hψe]
  exact e16k_zOf_prod h₁ h₂ h₃

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem exists_three_element_of_frame (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ x : G, x ∈ pSpan (centMembers Ω e) ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      (∃ a : ℕ, x ^ 3 ^ a = 1) ∧ (∃ k ∈ K, x * k ≠ k * x) := by
  obtain ⟨I, ψ, -, hψI, -, -, -⟩ := exists_equiv_X c h h9 h13
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp (e_mem_centralizer c h).1 k hk).symm
  have hKP : K ∈ centMembers Ω e := ⟨c.twin.mem, hKe⟩
  have hX : pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hinv : ∀ L ∈ centMembers Ω e, ∀ x ∈ pSpan (centMembers Ω e),
      conjSub x L ∈ centMembers Ω e := by
    intro L hL x hx
    have hxe : x * e = e * x :=
      (Subgroup.mem_centralizer_iff.mp (hX hx) e (Set.mem_singleton e)).symm
    have hxinv : x⁻¹ * e = e * x⁻¹ := by
      calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hxe]
        _ = e * x⁻¹ := by group
    refine ⟨h.thmD.hyp.conjInvariant x L hL.1, fun y hy => ?_⟩
    have ht : (x⁻¹ * y * x) * e = e * (x⁻¹ * y * x) :=
      (Subgroup.mem_centralizer_iff.mp (hL.2 (mem_conjSub_iff.mp hy)) e
        (Set.mem_singleton e)).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    calc e * y = e * x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = x * e * (x⁻¹ * y * x) * x⁻¹ := by rw [← hxe]
      _ = x * (e * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * e) * x⁻¹ := by rw [ht]
      _ = x * (x⁻¹ * y * x) * (e * x⁻¹) := by group
      _ = x * (x⁻¹ * y * x) * (x⁻¹ * e) := by rw [hxinv]
      _ = y * e := by group
  have hk : IsPGroup 2 I.φ.ker := by
    intro g
    refine ⟨1, ?_⟩
    have hg : I.φ (g : pSpan (centMembers Ω e)) = 1 := g.2
    have h1 : AE.mkQ 6 ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) = 1 := by
      rw [hψI]
      exact hg
    have h2 : ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) ∈ AE.piSub 6 :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) *
        ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) = 1 := by
      rcases AE.mem_piSub.mp h2 with h4 | h4 <;> rw [h4]
      · exact mul_one 1
      · exact AE.allOnes_mul_self 6
    have h5 : ψ (g : pSpan (centMembers Ω e)) * ψ (g : pSpan (centMembers Ω e)) = 1 :=
      Subtype.ext (by simpa using h3)
    have h6 : (g : pSpan (centMembers Ω e)) * (g : pSpan (centMembers Ω e)) = 1 := by
      apply ψ.injective
      rw [map_mul, map_one]
      exact h5
    have h8 : g * g = 1 := Subtype.ext (by simpa using h6)
    rw [pow_one, sq]
    exact h8
  obtain ⟨y, hy3, hyK, hyc⟩ := AEIdent.exists_pow_three_norm h.thmD.hyp
    (fun L hL => h.thmD.two L hL) (fun L hL => hL.1) hinv (by norm_num) I hk hKP
  have hnorm : (y : G) ∈ Subgroup.normalizer (K : Set G) := by
    have hK' : ∀ s : G, s ∈ K ↔ (y : G)⁻¹ * s * (y : G) ∈ K := fun s => by
      rw [← mem_conjSub_iff, hyK]
    have hK'' : ∀ s : G, s ∈ K ↔ (y : G) * s * (y : G)⁻¹ ∈ K := fun s => by
      rw [hK' ((y : G) * s * (y : G)⁻¹)]
      simp [mul_assoc]
    rw [Subgroup.mem_normalizer_iff]
    exact hK''
  refine ⟨(y : G), y.2, hnorm, ⟨1, ?_⟩, ?_⟩
  · rw [pow_one]
    have := congrArg Subtype.val hy3
    simpa using this
  · push_neg at hyc
    exact hyc

theorem commutator_eq_top_of_frame (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) : commutator G = ⊤ := by
  obtain ⟨x, -, hxN, hx3, hxK⟩ := exists_three_element_of_frame c h h9 h13
  have hK : K ≤ commutator G := h.le_commutator_of_three_element c.twin hxN hx3 hxK
  have hall : pSpan Ω ≤ commutator G := by
    refine pSpan_le fun L hL => ?_
    obtain ⟨g', hg'⟩ := h.thmD.trans K c.twin.mem L hL
    rw [← hg']
    intro y hy
    have h1 : g'⁻¹ * y * g' ∈ K := mem_conjSub_iff.mp hy
    have h2 : g' * (g'⁻¹ * y * g') * g'⁻¹ ∈ commutator G :=
      Subgroup.Normal.conj_mem inferInstance _ (hK h1) g'
    have e' : g' * (g'⁻¹ * y * g') * g'⁻¹ = y := by group
    rw [e'] at h2
    exact h2
  rw [h.thmD.gen] at hall
  exact top_le_iff.mp hall

private theorem e16k_sympForm [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) : Polar.SympForm bf :=
  { sq_eq_one := fun a => Subtype.ext (hh.out.zGroup_mul_self h9.out a.1 a.2)
    mul_left := hbf.mul_left
    mul_right := hbf.mul_right
    alt := hbf.alt
    nondeg := hbf.nondeg }

theorem hmodel_frame (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (ce : zGroup Ω) (hce : ce.1 = e)
    (x : zGroup Ω) (hx1 : x ≠ 1) (hxce : x ≠ ce) :
    5 ≤ (Polar.sigma bf (zPoints Ω) ce ∩ {p | bf x p = 0}).ncard ∧
      ((Polar.sigma bf (zPoints Ω) ce ∩ {p | bf x p = 0}).ncard = 5 → bf ce x = 1) := by
  obtain ⟨I, ψ, -, hψI, hψL, ⟨he, hψe⟩, -⟩ := exists_equiv_X c h h9 h13
  have heD : e ∈ zGroup Ω := by
    rw [← hce]
    exact ce.2
  have hcomm : ∀ d ∈ zGroup Ω, d * e = e * d := fun d hd => h.zGroup_comm h9 d hd e heD
  have hX : pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hinv : ∀ L ∈ centMembers Ω e, ∀ d ∈ pSpan (centMembers Ω e),
      conjSub d L ∈ centMembers Ω e := fun L hL d hd =>
    e16k_conj_mem h.thmD.hyp (Subgroup.mem_centralizer_iff.mp (hX hd) e
      (Set.mem_singleton e)).symm hL
  have hk : IsPGroup 2 I.φ.ker := by
    intro g
    refine ⟨1, ?_⟩
    have hg : I.φ (g : pSpan (centMembers Ω e)) = 1 := g.2
    have h1 : AE.mkQ 6 ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) = 1 := by
      rw [hψI]
      exact hg
    have h2 : ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) ∈ AE.piSub 6 :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) *
        ((ψ (g : pSpan (centMembers Ω e)) : AE.aeSub 6) : AE.Wr 6) = 1 := by
      rcases AE.mem_piSub.mp h2 with h4 | h4 <;> rw [h4]
      · exact mul_one 1
      · exact AE.allOnes_mul_self 6
    have h5 : ψ (g : pSpan (centMembers Ω e)) * ψ (g : pSpan (centMembers Ω e)) = 1 :=
      Subtype.ext (by simpa using h3)
    have h6 : (g : pSpan (centMembers Ω e)) * (g : pSpan (centMembers Ω e)) = 1 := by
      apply ψ.injective
      rw [map_mul, map_one]
      exact h5
    have h8 : g * g = 1 := Subtype.ext (by simpa using h6)
    rw [pow_one, sq]
    exact h8
  have hd : ∀ L ∈ centMembers Ω e, conjSub x.1 L ∈ centMembers Ω e := fun L hL =>
    e16k_conj_mem h.thmD.hyp (hcomm x.1 x.2) hL
  have hdz : ∀ L ∈ centMembers Ω e, ∀ r : G, IsUniqueInvolution L r → x.1 * r = r * x.1 :=
    fun L hL r hr => h.zGroup_comm h9 x.1 x.2 r (e16k_mem_zGroup hL.1 hr)
  obtain ⟨v, hv⟩ := exists_vec_of_aeIdent h.thmD.hyp (fun L hL => h.thmD.two L hL)
    (fun L hL => hL.1) hinv (by norm_num) (by norm_num) I hk hd hdz
  have hxq : ∀ (L : Subgroup G), L ∈ centMembers Ω e → ∀ (α : Finset (Fin 6)) (hα : α.card = 4)
      (b : Bool), (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b →
      ∀ q : zGroup Ω, IsUniqueInvolution L (q : G) → (bf x q = 0 ↔ ∑ i ∈ α, v i = 0) := by
    intro L hL α hα b hlab q hq
    rw [hbf.spec L hL.1 q hq x, mem_normalizer_iff_conjSub_eq]
    exact (hv L hL α hα b hlab).1
  have hceq : ∀ (L : Subgroup G), L ∈ centMembers Ω e → ∀ q : zGroup Ω,
      IsUniqueInvolution L (q : G) → bf ce q = 0 := by
    intro L hL q hq
    rw [hbf.spec L hL.1 q hq ce, hce]
    exact e16k_mem_normalizer hL.2
  have hmemF : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), (e16k_pt ψ α hα : G) ∈ zGroup Ω := by
    intro α hα
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα true
    exact e16k_mem_zGroup hL.1 (e16k_isUnique hL (hψL L hL α hα true hlab))
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 6) → zGroup Ω, ∀ (α : Finset (Fin 6)) (hα : α.card = 4),
      (F α : G) = (e16k_pt ψ α hα : G) :=
    ⟨fun α => if hα : α.card = 4 then ⟨_, hmemF α hα⟩ else 1, fun α hα => by simp [hα]⟩
  have hFinj : Set.InjOn F ↑(Finset.univ.filter fun α : Finset (Fin 6) =>
      α.card = 4 ∧ ∑ i ∈ α, v i = 0) := by
    intro α hα β hβ hFαβ
    rw [Finset.mem_coe, Finset.mem_filter] at hα hβ
    have h1 : (F α : G) = F β := congrArg Subtype.val hFαβ
    rw [hF α hα.2.1, hF β hβ.2.1] at h1
    exact e16k_pt_inj ψ h1
  have hS : Polar.sigma bf (zPoints Ω) ce ∩ {p | bf x p = 0} =
      F '' ↑(Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ ∑ i ∈ α, v i = 0) := by
    ext p
    constructor
    · rintro ⟨⟨hpz, hpce⟩, hpx⟩
      obtain ⟨M, hM, hUI⟩ := hpz
      have heM : e ∈ Subgroup.normalizer (M : Set G) := by
        have h1 := (hbf.spec M hM p hUI ce).mp hpce
        rwa [hce] at h1
      have hMP : M ∈ centMembers Ω e :=
        ⟨hM, Sit16.le_centralizer_of_mem_normalizer c h h9 h13 hM heM⟩
      obtain ⟨α', hα', b', hlab'⟩ := I.label M hMP
      have hpt : (p : G) = e16k_pt ψ α' hα' :=
        e16k_eq_pt hMP (hψL M hMP α' hα' b' hlab') hUI.mem hUI.sq hUI.ne_one
      refine ⟨α', ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hα', (hxq M hMP α' hα' b' hlab' p hUI).mp hpx⟩
      · exact Subtype.ext ((hF α' hα').trans hpt.symm)
    · rintro ⟨α, hα, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hα
      obtain ⟨L, hL, hlab⟩ := I.label_surj α hα.2.1 true
      have hUI : IsUniqueInvolution L (F α : G) := by
        rw [hF α hα.2.1]
        exact e16k_isUnique hL (hψL L hL α hα.2.1 true hlab)
      exact ⟨⟨e16k_mem_zPoints hL.1 hUI, hceq L hL (F α) hUI⟩,
        (hxq L hL α hα.2.1 true hlab (F α) hUI).mpr hα.2.2⟩
  have hbfF : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), bf x (F α) = ∑ i ∈ α, v i := by
    intro α hα
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα true
    have hUI : IsUniqueInvolution L (F α : G) := by
      rw [hF α hα]
      exact e16k_isUnique hL (hψL L hL α hα true hlab)
    exact e16k_zmod2_eq _ _ (hxq L hL α hα true hlab (F α) hUI)
  have hc₁ : ({2, 3, 4, 5} : Finset (Fin 6)).card = 4 := by decide
  have hc₂ : ({0, 3, 4, 5} : Finset (Fin 6)).card = 4 := by decide
  have hc₃ : ({1, 3, 4, 5} : Finset (Fin 6)).card = 4 := by decide
  have hprod : F ({2, 3, 4, 5} : Finset (Fin 6)) * F ({0, 3, 4, 5} : Finset (Fin 6)) *
      F ({1, 3, 4, 5} : Finset (Fin 6)) = ce := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hF _ hc₁, hF _ hc₂, hF _ hc₃, hce]
    exact congrArg Subtype.val (e16k_prod ψ he hψe hc₁ hc₂ hc₃)
  have hsum3 : bf x ce = ∑ i ∈ ({2, 3, 4, 5} : Finset (Fin 6)), v i +
      ∑ i ∈ ({0, 3, 4, 5} : Finset (Fin 6)), v i + ∑ i ∈ ({1, 3, 4, 5} : Finset (Fin 6)), v i := by
    rw [← hprod, hbf.mul_right, hbf.mul_right, hbfF _ hc₁, hbfF _ hc₂, hbfF _ hc₃]
  have hsum_ce : bf ce x = ∑ i, v i := by
    rw [hbf.symm ce x, hsum3, e16k_sum_six v]
  have hcount := AE.count_weight4 v
  rw [hS, hFinj.ncard_image, Set.ncard_coe_finset]
  rcases hcount with ⟨-, h15⟩ | ⟨-, h579, h5⟩
  · rw [h15]
    exact ⟨by norm_num, fun h => by norm_num at h⟩
  · refine ⟨?_, fun h => ?_⟩
    · rcases h579 with h | h | h <;> omega
    · rw [hsum_ce]
      exact h5 h

private theorem e16k_hmodel (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) :
    ∀ ce : zGroup Ω, (∃ y : G, ce.1 = y * e * y⁻¹) → ∀ x : zGroup Ω, x ≠ 1 → x ≠ ce →
      5 ≤ (Polar.sigma bf (zPoints Ω) ce ∩ {p | bf x p = 0}).ncard ∧
        ((Polar.sigma bf (zPoints Ω) ce ∩ {p | bf x p = 0}).ncard = 5 → bf ce x = 1) := by
  intro ce hce x hx1 hxce
  obtain ⟨y, hy⟩ := hce
  exact hmodel_frame (c.conjG h y) h h9 (EndHyp.zGroup_ne_eGroup_conj h c.twin.mem h13 y) hbf
    ce hy x hx1 hxce

private theorem e16kc_three_cycle (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    {pt : Fin 7 → G} {σK : G →* Equiv.Perm (Fin 7)}
    (hinj : Function.Injective pt) (hpt0 : pt 0 = e)
    (hconj : ∀ (x : G) (i : Fin 7), x * pt i * x⁻¹ = pt (σK x i))
    (hker : σK.ker = Subgroup.centralizer (zGroup Ω : Set G))
    (hle : σK.range ≤ alternatingGroup (Fin 7)) :
    ∃ x ∈ pSpan (centMembers Ω e), (σK x).IsThreeCycle := by
  obtain ⟨-, ψ, -, -, -, -, hiff⟩ := exists_equiv_X c h h9 h13
  have hXC0 : pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
    pSpan_le fun L hL => hL.2
  generalize hX : pSpan (centMembers Ω e) = X at ψ hiff hXC0 ⊢
  have hXC : X ≤ Subgroup.centralizer ({e} : Set G) := hXC0
  have hfix : ∀ x ∈ X, σK x 0 = 0 := by
    intro x hx
    have hxe : e * x = x * e :=
      Subgroup.mem_centralizer_iff.mp (hXC hx) e (Set.mem_singleton e)
    apply hinj
    rw [← hconj x 0, hpt0, ← hxe, mul_inv_cancel_right]
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥X →* Equiv.Perm (Fin 6),
      ∀ x : ↥X, θ x = (ψ x : AE.Wr 6).perm :=
    ⟨(AE.permHom 6).comp ((AE.aeSub 6).subtype.comp ψ.toMonoidHom), fun x => rfl⟩
  have hθ_alt : ∀ x : ↥X, θ x ∈ alternatingGroup (Fin 6) := fun x => by
    rw [Equiv.Perm.mem_alternatingGroup, hθ]
    exact (AE.mem_aeSub.mp (ψ x).2).2
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ↥X →* alternatingGroup (Fin 6),
      ∀ x : ↥X, (θ' x : Equiv.Perm (Fin 6)) = θ x :=
    ⟨{ toFun := fun x => ⟨θ x, hθ_alt x⟩
       map_one' := Subtype.ext (map_one θ)
       map_mul' := fun x y => Subtype.ext (map_mul θ x y) }, fun x => rfl⟩
  have hθ'_surj : Function.Surjective θ' := by
    rintro ⟨σ, hσ⟩
    have hσ' : AE.Wr.ofPerm σ ∈ AE.aeSub 6 :=
      AE.mem_aeSub.mpr ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm],
        Equiv.Perm.mem_alternatingGroup.mp hσ⟩
    refine ⟨ψ.symm ⟨AE.Wr.ofPerm σ, hσ'⟩, Subtype.ext ?_⟩
    rw [hθ', hθ]
    simp [AE.Wr.ofPerm]
  have hθ_iff : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ zGroup Ω := fun x => by
    rw [hθ]
    exact (hiff x).symm
  have hθ'_one : ∀ y : ↥X, θ' y = 1 → σK (y : G) = 1 := by
    intro y hy
    have hy' : θ y = 1 := by
      rw [← hθ' y]
      exact congrArg Subtype.val hy
    have hzy : (y : G) ∈ zGroup Ω := (hθ_iff y).mp hy'
    have hcm : (y : G) ∈ σK.ker := by
      rw [hker, Subgroup.mem_centralizer_iff]
      intro d hd
      exact h.zGroup_comm h9 d hd (y : G) hzy
    exact MonoidHom.mem_ker.mp hcm
  obtain ⟨f, hf⟩ : ∃ f : ↥X →* Equiv.Perm (Fin 7), ∀ x : ↥X, f x = σK (x : G) :=
    ⟨σK.comp X.subtype, fun x => rfl⟩
  have hkey : ∀ x : ↥X, f x = 1 → θ' x = 1 := by
    have h5 : 5 ≤ Nat.card (Fin 6) := by simp
    haveI hN : ((f.ker).map θ').Normal := Subgroup.Normal.map inferInstance θ' hθ'_surj
    rcases (alternatingGroup.isSimpleGroup h5).eq_bot_or_eq_top_of_normal
      ((f.ker).map θ') with hbot | htop
    · intro x hx
      have hm : θ' x ∈ (f.ker).map θ' := Subgroup.mem_map_of_mem θ' (MonoidHom.mem_ker.mpr hx)
      rw [hbot] at hm
      exact Subgroup.mem_bot.mp hm
    · exfalso
      have hall : ∀ x : ↥X, σK (x : G) = 1 := by
        intro x
        have hx : θ' x ∈ (f.ker).map θ' := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
        have h1 : θ' (n⁻¹ * x) = 1 := by
          rw [map_mul, map_inv, hnx, inv_mul_cancel]
        have h2 : σK ((n⁻¹ * x : ↥X) : G) = 1 := hθ'_one _ h1
        have h3 : σK (n : G) = 1 := by
          rw [← hf n]
          exact MonoidHom.mem_ker.mp hn
        have h4 : (x : G) = (n : G) * ((n⁻¹ * x : ↥X) : G) := by simp
        rw [h4, map_mul, h3, h2, one_mul]
      have hC : zGroup Ω ≤ Subgroup.centralizer ((X : Subgroup G) : Set G) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : y ∈ σK.ker := MonoidHom.mem_ker.mpr (hall ⟨y, hy⟩)
        rw [hker] at h1
        exact (Subgroup.mem_centralizer_iff.mp h1 d hd).symm
      have hlam : lambdaW Ω W = zGroup Ω := by
        rw [lambdaW_eq_centralizer c h h9 h13, hX]
        exact inf_eq_left.mpr hC
      have h2 := natCard_lambdaW_eq_two c h h9 h13
      have h64 := (natCard_zGroup_eq_sixtyFour_of_frame c h h9 h13).1
      rw [hlam, h64] at h2
      norm_num at h2
  have hker_eq : f.ker = θ'.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    refine ⟨hkey x, fun hx => ?_⟩
    rw [hf]
    exact hθ'_one x hx
  have hcard_alt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcard_f : Nat.card f.range = 360 := by
    have e1 : Nat.card f.range = Nat.card (↥X ⧸ f.ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
    have e2 : Nat.card (↥X ⧸ f.ker) = Nat.card (↥X ⧸ θ'.ker) := by
      rw [hker_eq]
    have e3 : Nat.card (↥X ⧸ θ'.ker) = Nat.card θ'.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ').toEquiv
    have e4 : θ'.range = ⊤ := MonoidHom.range_eq_top.mpr hθ'_surj
    rw [e1, e2, e3, e4, Subgroup.card_top, hcard_alt]
  obtain ⟨e6⟩ : Nonempty (Fin 6 ≃ {x : Fin 7 // x ≠ 0}) :=
    ⟨Fintype.equivOfCardEq (by decide)⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 7),
      ∀ p : Equiv.Perm (Fin 6), Φ p = Equiv.Perm.ofSubtype (e6.permCongr p) :=
    ⟨(Equiv.Perm.ofSubtype (p := fun x : Fin 7 => x ≠ 0)).comp e6.permCongrHom.toMonoidHom,
      fun p => rfl⟩
  have hΦsign : ∀ p, Equiv.Perm.sign (Φ p) = Equiv.Perm.sign p := fun p => by
    rw [hΦ, Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    rw [hΦ, hΦ] at hpq
    exact e6.permCongr.injective (Equiv.Perm.ofSubtype_injective hpq)
  have hΦsurj : ∀ τ : Equiv.Perm (Fin 7), τ 0 = 0 → Equiv.Perm.sign τ = 1 →
      ∃ p ∈ alternatingGroup (Fin 6), Φ p = τ := by
    intro τ hτ0 hτs
    have hτ : ∀ x : Fin 7, τ x ≠ 0 ↔ x ≠ 0 := fun x => by
      have hx : τ x ≠ τ 0 ↔ x ≠ 0 := τ.injective.ne_iff
      rwa [hτ0] at hx
    have hτf : ∀ x : Fin 7, τ x ≠ x → x ≠ 0 := fun x hx h0 => hx (by rw [h0, hτ0])
    have hΦp : Φ (e6.permCongr.symm (τ.subtypePerm hτ)) = τ := by
      rw [hΦ, Equiv.apply_symm_apply]
      exact Equiv.Perm.ofSubtype_subtypePerm hτ hτf
    refine ⟨e6.permCongr.symm (τ.subtypePerm hτ), ?_, hΦp⟩
    rw [Equiv.Perm.mem_alternatingGroup, ← hΦsign, hΦp]
    exact hτs
  have hcardW : Nat.card ((alternatingGroup (Fin 6)).map Φ) = 360 :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6))
      Φ hΦinj).toEquiv).symm.trans hcard_alt
  have hY_le : f.range ≤ (alternatingGroup (Fin 6)).map Φ := by
    intro y hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    have hsx : σK (x : G) ∈ alternatingGroup (Fin 7) :=
      hle (MonoidHom.mem_range.mpr ⟨(x : G), rfl⟩)
    obtain ⟨p, hp, hpy⟩ :=
      hΦsurj (σK (x : G)) (hfix (x : G) x.2) (Equiv.Perm.mem_alternatingGroup.mp hsx)
    refine Subgroup.mem_map.mpr ⟨p, hp, ?_⟩
    rw [hpy, ← hf x]
    exact hx
  have hY : f.range = (alternatingGroup (Fin 6)).map Φ :=
    Subgroup.eq_of_le_of_card_ge hY_le (le_of_eq (by rw [hcardW, hcard_f]))
  have hc3 : (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 1 3).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨p, hp, hpc3⟩ := hΦsurj _ (by decide) hc3.sign
  have hmem : (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 1 3) ∈ f.range := by
    rw [hY]
    exact Subgroup.mem_map.mpr ⟨p, hp, hpc3⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨(x : G), x.2, ?_⟩
  rw [← hf x, hx]
  exact hc3

theorem exists_points_sigma (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ (pt : Fin 7 → G) (σ : G →* Equiv.Perm (Fin 7)),
      Function.Injective pt ∧ (∀ i, pt i ∈ zGroup Ω) ∧ pt 0 = e ∧
      (∀ i, ∃ x : G, pt i = x * e * x⁻¹) ∧ (List.ofFn pt).prod = 1 ∧
      Subgroup.closure (Set.range pt) = zGroup Ω ∧
      (∀ (x : G) (i : Fin 7), x * pt i * x⁻¹ = pt (σ x i)) ∧
      σ.ker = Subgroup.centralizer (zGroup Ω : Set G) ∧ σ.range = alternatingGroup (Fin 7) ∧
      (∀ M ∈ Ω, ∀ b : G, IsUniqueInvolution M b →
        ∃ i j k : Fin 7, i < j ∧ j < k ∧ b = pt i * pt j * pt k ∧
          ∀ l : Fin 7, (l = i ∨ l = j ∨ l = k) ↔ M ≤ Subgroup.centralizer ({pt l} : Set G)) := by
  classical
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 c.twin h13
  have hsymp : Polar.SympForm bf := e16k_sympForm hbf
  have hsec := sections_of_frame c h13 hbf
  obtain ⟨a, hS⟩ := EndHyp.exists_pointSet c.twin h13 hbf
  have hcard64 : Nat.card (zGroup Ω) = 64 :=
    (natCard_zGroup_eq_sixtyFour_of_frame c h h9 h13).1
  have hspan : Subgroup.closure (zPoints Ω : Set (zGroup Ω)) = ⊤ := EndHyp.closure_zPoints Ω
  obtain ⟨p₀, hp₀, x₁, x₂, hx₁, hx₂, hx12, hpx₁, hpx₂⟩ := exists_two_sections c h13 hbf
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  set 𝓔 : Set (zGroup Ω) := {x | ∃ y : G, x.1 = y * e * y⁻¹} with h𝓔
  have hmem : ∃ p ∈ zPoints Ω, ∃ x ∈ 𝓔, ∃ x' ∈ 𝓔, x ≠ x' ∧
      p ∈ Polar.sigma bf (zPoints Ω) x ∧ p ∈ Polar.sigma bf (zPoints Ω) x' :=
    ⟨p₀, hp₀, x₁, hx₁, x₂, hx₂, hx12, hpx₁, hpx₂⟩
  have hcard7 : 𝓔.ncard = 7 := Polar.Sections.card_centres_eq hsymp hS hsec hcard64 hmem
  have hB : ∀ x ∈ 𝓔, ∀ x' ∈ 𝓔, x ≠ x' → bf x x' = 1 := fun x hx x' hx' hne =>
    Polar.Sections.B_eq_one hsymp hS hsec hcard64 hmem (e16k_hmodel c h h9 h13 hbf) hx hx' hne
  have hfin : 𝓔.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard7]; norm_num)
  have hNat : Nat.card 𝓔 = 7 := by rw [Nat.card_coe_set_eq, hcard7]
  have he : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have heZ : (⟨e, he⟩ : zGroup Ω) ∈ 𝓔 := ⟨1, by simp⟩
  let ε0 : 𝓔 ≃ Fin 7 := (Finite.equivFin 𝓔).trans (finCongr hNat)
  let ε : 𝓔 ≃ Fin 7 := ε0.trans (Equiv.swap (ε0 ⟨⟨e, he⟩, heZ⟩) 0)
  have hε : ε ⟨⟨e, he⟩, heZ⟩ = 0 := by simp [ε]
  let pZ : Fin 7 → zGroup Ω := fun i => (ε.symm i).1
  have hpZ𝓔 : ∀ i, pZ i ∈ 𝓔 := fun i => (ε.symm i).2
  have hpZ0 : pZ 0 = ⟨e, he⟩ := by
    have h0 : ε.symm 0 = ⟨⟨e, he⟩, heZ⟩ := by rw [Equiv.symm_apply_eq, hε]
    simp [pZ, h0]
  have hpZinj : Function.Injective pZ := fun i j hij => ε.symm.injective (Subtype.ext hij)
  have hpZsurj : ∀ x ∈ 𝓔, ∃ i, pZ i = x := fun x hx => ⟨ε ⟨x, hx⟩, by simp [pZ]⟩
  let pt : Fin 7 → G := fun i => (pZ i).1
  let cj : G → zGroup Ω → zGroup Ω := fun x a =>
    ⟨x * a.1 * x⁻¹, Subgroup.Normal.conj_mem hD a.1 a.2 x⟩
  have hcjE : ∀ (x : G) (a : zGroup Ω), a ∈ 𝓔 → cj x a ∈ 𝓔 := by
    rintro x a ⟨y, hy⟩
    exact ⟨x * y, by show x * a.1 * x⁻¹ = x * y * e * (x * y)⁻¹; rw [hy]; group⟩
  let pe : G → Equiv.Perm 𝓔 := fun x =>
    { toFun := fun a => ⟨cj x a.1, hcjE x a.1 a.2⟩
      invFun := fun a => ⟨cj x⁻¹ a.1, hcjE x⁻¹ a.1 a.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext (by
        show x⁻¹ * (x * a.1.1 * x⁻¹) * x⁻¹⁻¹ = a.1.1
        group))
      right_inv := fun a => Subtype.ext (Subtype.ext (by
        show x * (x⁻¹ * a.1.1 * x⁻¹⁻¹) * x⁻¹ = a.1.1
        group)) }
  let σ𝓔 : G →* Equiv.Perm 𝓔 :=
    { toFun := pe
      map_one' := Equiv.ext fun a => Subtype.ext (Subtype.ext (by
        show 1 * a.1.1 * 1⁻¹ = a.1.1
        group))
      map_mul' := fun x y => Equiv.ext fun a => Subtype.ext (Subtype.ext (by
        show x * y * a.1.1 * (x * y)⁻¹ = x * (y * a.1.1 * y⁻¹) * x⁻¹
        group)) }
  let σK : G →* Equiv.Perm (Fin 7) := (Equiv.permCongrHom ε).toMonoidHom.comp σ𝓔
  have hσK : ∀ x i, σK x i = ε (pe x (ε.symm i)) := fun x i => rfl
  have hpZσ : ∀ x i, pZ (σK x i) = cj x (pZ i) := fun x i => by
    show (ε.symm (σK x i)).1 = cj x (ε.symm i).1
    rw [hσK, Equiv.symm_apply_apply]
    rfl
  have hconj : ∀ (x : G) (i : Fin 7), x * pt i * x⁻¹ = pt (σK x i) := fun x i => by
    show x * (pZ i).1 * x⁻¹ = (pZ (σK x i)).1
    rw [hpZσ]
  have hpt0 : pt 0 = e := by
    show (pZ 0).1 = e
    rw [hpZ0]
  have hinj : Function.Injective pt := fun i j hij => hpZinj (Subtype.ext hij)
  have hpt𝓔 : ∀ i, ∃ x : G, pt i = x * e * x⁻¹ := fun i => by
    obtain ⟨y, hy⟩ := hpZ𝓔 i
    exact ⟨y, hy⟩
  have hpt_mem : ∀ i, pt i ∈ zGroup Ω := fun i => (pZ i).2
  have hE𝓔 : ∀ x ∈ 𝓔, x.1 ∈ Subgroup.closure (Set.range pt) := fun x hx => by
    obtain ⟨i, rfl⟩ := hpZsurj x hx
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hzP : ∀ p ∈ zPoints Ω, p.1 ∈ Subgroup.closure (Set.range pt) := fun p hp => by
    have hT := Polar.Sections.eq_prod_of_mem hsymp hS hspan hsec hcard64 hmem hB hp
      (hfin.toFinset.filter (fun x => bf x p = 0)) (fun x => by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Polar.sigma, Set.mem_setOf_eq,
          hp, true_and])
    have hmemT : ∀ x ∈ hfin.toFinset.filter (fun x => bf x p = 0),
        x ∈ (Subgroup.closure (Set.range pt)).subgroupOf (zGroup Ω) := fun x hx =>
      Subgroup.mem_subgroupOf.mpr
        (hE𝓔 x ((Set.Finite.mem_toFinset hfin).mp (Finset.mem_filter.mp hx).1))
    have hM := Subgroup.prod_mem _ hmemT
    rw [← hT] at hM
    exact Subgroup.mem_subgroupOf.mp hM
  have hclos : Subgroup.closure (Set.range pt) = zGroup Ω := by
    apply le_antisymm
    · exact Subgroup.closure_le _ |>.mpr (Set.range_subset_iff.mpr hpt_mem)
    · intro b hb
      have hM : (zPoints Ω : Set (zGroup Ω)) ⊆
          ((Subgroup.closure (Set.range pt)).subgroupOf (zGroup Ω) : Set (zGroup Ω)) :=
        fun p hp => Subgroup.mem_subgroupOf.mpr (hzP p hp)
      have htop : (⟨b, hb⟩ : zGroup Ω) ∈ Subgroup.closure (zPoints Ω : Set (zGroup Ω)) := by
        rw [hspan]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.closure_le _ |>.mpr hM) htop)
  have hker : σK.ker = Subgroup.centralizer (zGroup Ω : Set G) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx d hd
      have hC : Set.range pt ⊆ (Subgroup.centralizer ({x} : Set G) : Set G) := by
        rintro _ ⟨i, rfl⟩
        have hi : σK x i = i := by simp [hx]
        have h1 : x * pt i * x⁻¹ = pt i := by rw [hconj, hi]
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact mul_inv_eq_iff_eq_mul.mp h1
      have hcl : zGroup Ω ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← hclos]
        exact (Subgroup.closure_le _).mpr hC
      exact (Subgroup.mem_centralizer_iff.mp (hcl hd) x (Set.mem_singleton x)).symm
    · intro hx
      refine Equiv.ext fun i => ?_
      rw [Equiv.Perm.one_apply]
      refine hinj ?_
      rw [← hconj]
      have hc := hx (pt i) (hpt_mem i)
      rw [← hc]
      group
  have hle : σK.range ≤ alternatingGroup (Fin 7) := by
    have hcomm : commutator G ≤ (Equiv.Perm.sign.comp σK : G →* ℤˣ).ker := by
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [commutator_eq_top_of_frame c h h9 h13] at hcomm
    rintro _ ⟨x, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have hx := hcomm (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hx
    simpa using hx
  have hsurj : ∀ i j : Fin 7, ∃ x : G, σK x i = j := fun i j => by
    obtain ⟨yi, hyi⟩ := hpt𝓔 i
    obtain ⟨yj, hyj⟩ := hpt𝓔 j
    refine ⟨yj * yi⁻¹, hinj ?_⟩
    rw [← hconj, hyi, hyj]
    group
  haveI : MulAction.IsPretransitive σK.range (Fin 7) :=
    ⟨fun i j => by
      obtain ⟨x, hx⟩ := hsurj i j
      exact ⟨⟨σK x, x, rfl⟩, hx⟩⟩
  have hprim : MulAction.IsPreprimitive σK.range (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num)
  obtain ⟨x3, -, hx3⟩ := e16kc_three_cycle c h h9 h13 hinj hpt0 hconj hker hle
  have hJ : alternatingGroup (Fin 7) ≤ σK.range :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hx3 ⟨x3, rfl⟩
  have hrange : σK.range = alternatingGroup (Fin 7) := le_antisymm hle hJ
  have hprod : (List.ofFn pt).prod = 1 := by
    have hl : (List.ofFn pZ).prod = 1 := by
      refine Polar.Sections.prod_eq_one hsymp hS hspan hsec hcard64 hmem hB (List.ofFn pZ)
        (List.nodup_ofFn.mpr hpZinj) (fun x => ?_)
      rw [List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact hpZ𝓔 i
      · intro hx
        obtain ⟨i, hi⟩ := hpZsurj x hx
        exact ⟨i, hi⟩
    have hmap : List.ofFn pt = (List.ofFn pZ).map (zGroup Ω).subtype := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, ← map_list_prod, hl, map_one]
  have htrip : ∀ M ∈ Ω, ∀ b : G, IsUniqueInvolution M b → ∃ i j k : Fin 7, i < j ∧ j < k ∧
      b = pt i * pt j * pt k ∧ ∀ l : Fin 7, (l = i ∨ l = j ∨ l = k) ↔
        M ≤ Subgroup.centralizer ({pt l} : Set G) := by
    intro M hM b hb
    have hbZ : b ∈ zGroup Ω := Subgroup.subset_closure ⟨M, hM, hb⟩
    have hbP : (⟨b, hbZ⟩ : zGroup Ω) ∈ zPoints Ω := ⟨M, hM, hb⟩
    set bZ : zGroup Ω := ⟨b, hbZ⟩ with hbZdef
    set Tidx : Finset (Fin 7) := Finset.univ.filter (fun i : Fin 7 => bf (pZ i) bZ = 0)
      with hTidx
    have ha9 : a = 9 := by
      have h1 := Polar.Sections.card_centres_of_mem hsymp hS hsec hbP
      have h2 := hS.card_nbr bZ hbP
      have h3 := card_nbr_eq_eighteen c h13 hbf hbP
      omega
    have hset : {x | x ∈ 𝓔 ∧ bZ ∈ Polar.sigma bf (zPoints Ω) x} = pZ '' (Tidx : Set (Fin 7)) := by
      ext x
      constructor
      · rintro ⟨hx𝓔, hxσ⟩
        obtain ⟨i, rfl⟩ := hpZsurj x hx𝓔
        refine ⟨i, ?_, rfl⟩
        rw [Finset.mem_coe, hTidx, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hxσ.2⟩
      · rintro ⟨i, hi, rfl⟩
        rw [Finset.mem_coe, hTidx, Finset.mem_filter] at hi
        exact ⟨hpZ𝓔 i, hbP, hi.2⟩
    have hcardT : Tidx.card = 3 := by
      have h1 := Polar.Sections.card_centres_of_mem hsymp hS hsec hbP
      have h2 : {x | x ∈ 𝓔 ∧ bZ ∈ Polar.sigma bf (zPoints Ω) x}.ncard = 3 := by omega
      rw [hset, Set.ncard_image_of_injective _ hpZinj, Set.ncard_coe_finset] at h2
      exact h2
    have hcard3 : Tidx.card = 3 := hcardT
    set ord : Fin 3 ↪o Fin 7 := Tidx.orderEmbOfFin hcard3 with hord
    have hrangeT : Set.range ord = (Tidx : Set (Fin 7)) := Finset.range_orderEmbOfFin Tidx hcard3
    have hTeq : Tidx = {ord 0, ord 1, ord 2} := by
      ext l
      rw [← Finset.mem_coe, ← hrangeT]
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp
      · intro hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    have hd01 : ord 0 ≠ ord 1 := ord.injective.ne (by decide)
    have hd02 : ord 0 ≠ ord 2 := ord.injective.ne (by decide)
    have hd12 : ord 1 ≠ ord 2 := ord.injective.ne (by decide)
    have hTmem : ∀ x : zGroup Ω, x ∈ Tidx.image pZ ↔ x ∈ 𝓔 ∧ bZ ∈ Polar.sigma bf (zPoints Ω) x := by
      intro x
      have h1 := Set.ext_iff.mp hset x
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe] at h1
      rw [Finset.mem_image]
      exact h1.symm
    have hprod3 : bZ = pZ (ord 0) * pZ (ord 1) * pZ (ord 2) := by
      rw [Polar.Sections.eq_prod_of_mem hsymp hS hspan hsec hcard64 hmem hB hbP (Tidx.image pZ)
        hTmem, Finset.prod_image (fun x _ y _ hxy => hpZinj hxy), hTeq,
        Finset.prod_insert (by simp [hd01, hd02]), Finset.prod_insert (by simp [hd12]),
        Finset.prod_singleton, mul_assoc]
      rfl
    refine ⟨ord 0, ord 1, ord 2, ord.strictMono (by decide), ord.strictMono (by decide), ?_, ?_⟩
    · have h := congrArg Subtype.val hprod3
      simpa using h
    intro l
    have hiff : l ∈ Tidx ↔ bf (pZ l) bZ = 0 := by
      rw [hTidx, Finset.mem_filter]
      simp
    have hl : (l = ord 0 ∨ l = ord 1 ∨ l = ord 2) ↔ bf (pZ l) bZ = 0 := by
      rw [← hiff, hTeq]
      simp
    rw [hl, hbf.spec M hM bZ hb (pZ l)]
    constructor
    · intro hN
      obtain ⟨y, hy⟩ := hpZ𝓔 l
      have hN' : y * e * y⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
        rw [← hy]
        exact hN
      have hcen := le_centralizer_of_mem_normalizer (c.conjG h y) h h9
        (h.zGroup_ne_eGroup_conj c.twin.mem h13 y) hM hN'
      rw [← hy] at hcen
      exact hcen
    · intro hC
      have hcomm : ∀ m ∈ M, (pZ l).1 * m = m * (pZ l).1 := fun m hm =>
        Subgroup.mem_centralizer_iff.mp (hC hm) (pZ l).1 (Set.mem_singleton _)
      have hconjeq : ∀ m ∈ M, (pZ l).1 * m * (pZ l).1⁻¹ = m := fun m hm => by
        rw [hcomm m hm]
        group
      have hconjeq' : ∀ m ∈ M, (pZ l).1⁻¹ * m * (pZ l).1 = m := fun m hm => by
        rw [mul_assoc, ← hcomm m hm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hconjeq x hx]
        exact hx
      · intro hx
        have h1 := hconjeq' _ hx
        have h2 : (pZ l).1⁻¹ * ((pZ l).1 * x * (pZ l).1⁻¹) * (pZ l).1 = x := by group
        rw [h2] at h1
        rw [h1]
        exact hx
  refine ⟨pt, σK, hinj, hpt_mem, hpt0, hpt𝓔, hprod, hclos, hconj, hker, hrange, htrip⟩


theorem nonempty_mulEquiv_quotient_pCore
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nonempty (G ⧸ pCore 2 G ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨pt, σK, -, -, -, -, -, -, -, hker, hrange, -⟩ := exists_points_sigma c h h9 h13
  have hc : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G :=
    h.centralizer_zGroup_eq_pCore h9 c.twin h13
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have hkeq : σK.ker = pCore 2 G := hker.trans hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkeq).symm.trans
    ((QuotientGroup.quotientKerEquivRange σK).trans (MulEquiv.subgroupCongr hrange))⟩

theorem pCore_eq_zGroup (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    pCore 2 G = zGroup Ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := nonempty_mulEquiv_quotient_pCore c h h9 h13
  have hcard : Nat.card (G ⧸ pCore 2 G) = 2520 := by
    rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  refine h.pCore_eq_zGroup_of_perfect h9 c.twin h13 (commutator_eq_top_of_frame c h h9 h13)
    (fun P => ?_)
  have hv : padicValNat 2 2520 = 3 := by
    have h1 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_def _ Nat.prime_two, hv]
  norm_num

theorem natCard_eq_of_frame (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) : Nat.card G = 161280 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := nonempty_mulEquiv_quotient_pCore c h h9 h13
  have hcard : Nat.card (G ⧸ pCore 2 G) = 2520 := by
    rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
  rw [hcard, pCore_eq_zGroup c h h9 h13, (natCard_zGroup_eq_sixtyFour_of_frame c h h9 h13).1]
    at hmul
  rw [hmul]

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
