module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8B
public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8G
public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar8
public import CFSG.ClassicalInvolution.Q3.Sec13End18C

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

@[expose] def wt {n : ℕ} (w : Fin n → ZMod 2) : ℕ := (Finset.univ.filter fun i => w i ≠ 0).card

theorem ae8c_e2_wr4_K : ∀ w : Fin 4 → ZMod 2, ∀ a ∈ AE.kList,
    (Even (Finset.univ.filter fun j => w j ≠ 0).card →
      AE.Wr.ofVec (fun j => w j + w (a.perm.symm j)) * a ∈ AE.kList) ∧
    (¬Even (Finset.univ.filter fun j => w j ≠ 0).card →
      AE.Wr.ofVec (fun j => w j + w (a.perm.symm j)) * a ∈ AE.kStarList) := by
  decide +kernel

theorem ae8c_e2_wr4_Kstar : ∀ w : Fin 4 → ZMod 2, ∀ a ∈ AE.kStarList,
    (Even (Finset.univ.filter fun j => w j ≠ 0).card →
      AE.Wr.ofVec (fun j => w j + w (a.perm.symm j)) * a ∈ AE.kStarList) ∧
    (¬Even (Finset.univ.filter fun j => w j ≠ 0).card →
      AE.Wr.ofVec (fun j => w j + w (a.perm.symm j)) * a ∈ AE.kList) := by
  decide +kernel

theorem ae8c_e2_ofVec_inv {n : ℕ} (v : Fin n → ZMod 2) :
    (AE.Wr.ofVec v)⁻¹ = AE.Wr.ofVec v := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · rfl
  · rw [AE.Wr.inv_perm]; rfl

theorem ae8c_e2_ofVec_mul_vec {n : ℕ} (v : Fin n → ZMod 2) (X : AE.Wr n) :
    (AE.Wr.ofVec v * X).vec = fun x => v x + X.vec x := rfl

theorem ae8c_e2_mul_ofVec_vec {n : ℕ} (v : Fin n → ZMod 2) (X : AE.Wr n) (x : Fin n) :
    (X * AE.Wr.ofVec v).vec x = X.vec x + v (X.perm.symm x) := rfl

theorem ae8c_e2_ofVec_mul_perm {n : ℕ} (v : Fin n → ZMod 2) (X : AE.Wr n) :
    (AE.Wr.ofVec v * X).perm = X.perm := by
  rw [AE.Wr.mul_perm]; exact one_mul _

theorem ae8c_e2_mul_ofVec_perm {n : ℕ} (v : Fin n → ZMod 2) (X : AE.Wr n) :
    (X * AE.Wr.ofVec v).perm = X.perm := by
  rw [AE.Wr.mul_perm]; exact mul_one _

theorem ae8c_e2_conj_embed {n : ℕ} (ι : Fin 4 ↪ Fin n) (v : Fin n → ZMod 2) (a : AE.Wr 4) :
    AE.Wr.ofVec v * AE.embed ι a * (AE.Wr.ofVec v)⁻¹ =
      AE.embed ι (AE.Wr.ofVec (fun j => v (ι j) + v (ι (a.perm.symm j))) * a) := by
  rw [ae8c_e2_ofVec_inv]
  refine AE.Wr.ext (funext fun x => ?_) ?_
  · rw [ae8c_e2_mul_ofVec_vec, ae8c_e2_ofVec_mul_perm, ae8c_e2_ofVec_mul_vec, AE.embed_vec,
      AE.embed_vec, ae8c_e2_ofVec_mul_vec, AE.embed_perm]
    dsimp only
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      simp only [AE.embedVec_apply, AE.embedPerm_symm_apply]
      ring
    · rw [AE.embedPerm_symm_of_not_mem ι _ hx, AE.embedVec_of_not_mem ι _ hx,
        AE.embedVec_of_not_mem ι _ hx, add_zero, AE.Wr.zmod_two_add_self]
  · rw [ae8c_e2_mul_ofVec_perm, ae8c_e2_ofVec_mul_perm, AE.embed_perm, AE.embed_perm,
      AE.Wr.mul_perm]
    show AE.embedPerm ι a.perm = AE.embedPerm ι (1 * a.perm)
    rw [one_mul]

theorem ae8c_e2_card_eq {α : Finset (Fin 6)} (h : α.card = 4) (v : Fin 6 → ZMod 2) :
    (Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0).card =
      (Finset.univ.filter fun j : Fin 4 => v (AE.emb α h j) ≠ 0).card := by
  have hmem : ∀ i : Fin 6, i ∈ α ↔ ∃ j, AE.emb α h j = i := by
    intro i
    rw [← Finset.mem_coe, ← AE.range_emb α h, Set.mem_range]
  have key : (Finset.univ.filter fun j : Fin 4 => v (AE.emb α h j) ≠ 0).map (AE.emb α h) =
      Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0 := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hv, rfl⟩
      exact ⟨(hmem _).mpr ⟨j, rfl⟩, hv⟩
    · rintro ⟨hi, hv⟩
      obtain ⟨j, rfl⟩ := (hmem i).mp hi
      exact ⟨j, hv, rfl⟩
  rw [← key, Finset.card_map]

theorem ae8c_e2_memAt_conj {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool} (v : Fin 6 → ZMod 2)
    {a : AE.Wr 6} (ha : a ∈ AE.memAt α h b) :
    AE.Wr.ofVec v * a * (AE.Wr.ofVec v)⁻¹ ∈
      AE.memAt α h
        (if Even (Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0).card then b else !b) := by
  rw [ae8c_e2_card_eq h v]
  cases b
  · have ha' : a ∈ AE.kQStar.map (AE.embed (AE.emb α h)) := ha
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [ae8c_e2_conj_embed]
    by_cases hev : Even (Finset.univ.filter fun j : Fin 4 => v (AE.emb α h j) ≠ 0).card
    · rw [if_pos hev]
      exact Subgroup.mem_map_of_mem _
        (AE.mem_kQStar.mpr ((ae8c_e2_wr4_Kstar (fun j => v (AE.emb α h j)) a0
          (AE.mem_kQStar.mp ha0)).1 hev))
    · rw [if_neg hev]
      exact Subgroup.mem_map_of_mem _
        (AE.mem_kQ.mpr ((ae8c_e2_wr4_Kstar (fun j => v (AE.emb α h j)) a0
          (AE.mem_kQStar.mp ha0)).2 hev))
  · have ha' : a ∈ AE.kQ.map (AE.embed (AE.emb α h)) := ha
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [ae8c_e2_conj_embed]
    by_cases hev : Even (Finset.univ.filter fun j : Fin 4 => v (AE.emb α h j) ≠ 0).card
    · rw [if_pos hev]
      exact Subgroup.mem_map_of_mem _
        (AE.mem_kQ.mpr ((ae8c_e2_wr4_K (fun j => v (AE.emb α h j)) a0
          (AE.mem_kQ.mp ha0)).1 hev))
    · rw [if_neg hev]
      exact Subgroup.mem_map_of_mem _
        (AE.mem_kQStar.mpr ((ae8c_e2_wr4_K (fun j => v (AE.emb α h j)) a0
          (AE.mem_kQ.mp ha0)).2 hev))

theorem ae8c_e2_memBar_inj {α α' : Finset (Fin 6)} {h : α.card = 4} {h' : α'.card = 4}
    {b b' : Bool} (he : AE.memBar α h b = AE.memBar α' h' b') : α = α' ∧ b = b' := by
  have hz : AE.zBar α h ∈ AE.memBar α' h' b' := by
    rw [← he]; exact AE.zBar_mem_memBar α h b
  rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hz (AE.zBar_mul_self α h) with h1 | h1
  · exact absurd h1 (AE.zBar_ne_one (by norm_num) α h)
  · have hα : α = α' := AE.eq_of_zBar_eq (by norm_num) h1
    refine ⟨hα, ?_⟩
    subst hα
    cases b <;> cases b' <;> first
      | rfl
      | exact absurd he (AE.memBar_true_ne_false (by norm_num) _ _)
      | exact absurd he.symm (AE.memBar_true_ne_false (by norm_num) _ _)

theorem ae8c_e2_normalizer_iff (g : G) (L : Subgroup G) :
    g ∈ Subgroup.normalizer (L : Set G) ↔ conjSub g L = L := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    ext x
    rw [mem_conjSub_iff]
    have hx := hg (g⁻¹ * x * g)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hx
    exact hx
  · intro hg k
    have hh := mem_conjSub_iff (n := g) (K := L) (x := g * k * g⁻¹)
    rw [hg, show g⁻¹ * (g * k * g⁻¹) * g = k by group] at hh
    exact hh.symm

theorem ae8c_conj_zGroup (hΩ : ConjInvariant Ω) (g : G) {x : G} (hx : x ∈ zGroup Ω) :
    g * x * g⁻¹ ∈ zGroup Ω := by
  have hx' : x ∈ Subgroup.closure {v | ∃ L ∈ Ω, IsUniqueInvolution L v} := hx
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ zGroup Ω) ?_ ?_ ?_ ?_ hx'
  · intro x hx
    obtain ⟨L, hL, hz⟩ := hx
    exact Subgroup.subset_closure ⟨conjSub g L, hΩ g L hL, hz.conj g⟩
  · simp
  · intro a b _ _ ha hb
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (zGroup Ω).mul_mem ha hb
  · intro a _ ha
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact (zGroup Ω).inv_mem ha

theorem ae8c_mem_zGroup {L : Subgroup G} {z : G} (hL : L ∈ Ω) (hz : IsUniqueInvolution L z) :
    z ∈ zGroup Ω :=
  Subgroup.subset_closure ⟨L, hL, hz⟩

theorem ae8c_central (H : End18.Hyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) : ∀ m ∈ L, m * z = z * m :=
  fun m hm => H.endHyp.commute_z_of_le H.perp9 hL hz (H.endHyp.thmD.two L hL) le_rfl hm

theorem ae8c_zpowers_invol {z g : G} (hz : z * z = 1) (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, hz2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hz2, one_zpow, one_mul]

theorem ae8c_eq_indicator (v : Fin 6 → ZMod 2) :
    v = fun i => if i ∈ Finset.univ.filter (fun j => v j ≠ 0) then 1 else 0 := by
  funext i
  have hv : v i = 0 ∨ v i = 1 := by
    generalize v i = a
    revert a
    decide
  rcases hv with hv | hv <;> simp [hv]

theorem ae8c_wt_le (v : Fin 6 → ZMod 2) : wt v ≤ 6 := by
  unfold wt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem ae8c_conj_Z (hΩ : ConjInvariant Ω) {x : G} {g : G} (hx : ∃ L ∈ Ω, IsUniqueInvolution L x) :
    ∃ L ∈ Ω, IsUniqueInvolution L (g * x * g⁻¹) := by
  obtain ⟨L, hL, hz⟩ := hx
  exact ⟨conjSub g L, hΩ g L hL, hz.conj g⟩

theorem ae8c_mem_iff {L : Subgroup G} (c : Chart Ω u) {α : Finset (Fin 6)} {h : α.card = 4}
    {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    (y : G) ∈ L ↔ ((c.ψ y : AE.aeSub 6) : AE.Wr 6) ∈ AE.memAt α h b := by
  rw [← hlab]
  constructor
  · intro hy
    exact Subgroup.mem_map.mpr
      ⟨c.ψ y, Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  · intro hy
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hz
    have hyy : y' = y := c.ψ.injective (Subtype.ext hzeq)
    subst hyy
    exact Subgroup.mem_subgroupOf.mp hy'

theorem ae8c_memAt_invol {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool} {a : AE.Wr 6}
    (ha : a ∈ AE.memAt α h b) (h2 : a * a = 1) :
    a = 1 ∨ a = AE.zOf (AE.emb α h) := by
  cases b
  · exact AE.eq_of_mem_memKStar_mul_self _ a ha h2
  · exact AE.eq_of_mem_memK_mul_self _ a ha h2

theorem ae8c_exists_inv {L : Subgroup G} (hL : L ∈ Ω) (hLP : L ∈ Generic.centMembers Ω u)
    (c : Chart Ω u) {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b) :
    ∃ w : G, IsUniqueInvolution L w ∧
      ∃ hw : w ∈ pSpan (Generic.centMembers Ω u),
        ((c.ψ ⟨w, hw⟩ : AE.aeSub 6) : AE.Wr 6) = AE.zOf (AE.emb α h) := by
  have hz : AE.zOf (AE.emb α h) ∈ AE.memAt α h b := AE.zOf_mem_memAt α h b
  rw [← hlab] at hz
  obtain ⟨z, hzmem, hzeq⟩ := Subgroup.mem_map.mp hz
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hzmem
  have hψ : ((c.ψ y : AE.aeSub 6) : AE.Wr 6) = AE.zOf (AE.emb α h) := hzeq
  have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
  have hsq : ((c.ψ y : AE.aeSub 6) : AE.Wr 6) * ((c.ψ y : AE.aeSub 6) : AE.Wr 6) = 1 := by
    rw [hψ]
    have hi := AE.zOf_inv (AE.emb α h)
    calc AE.zOf (AE.emb α h) * AE.zOf (AE.emb α h)
        = AE.zOf (AE.emb α h) * (AE.zOf (AE.emb α h))⁻¹ := by rw [hi]
      _ = 1 := mul_inv_cancel _
  refine ⟨(y : G), ⟨hyL, ?_, ?_, ?_⟩, y.2, hψ⟩
  · intro h1
    have hy1 : y = 1 := Subtype.ext h1
    rw [hy1, map_one] at hψ
    exact AE.zOf_ne_one _ hψ.symm
  · have h2 : ((c.ψ (y * y) : AE.aeSub 6) : AE.Wr 6) = 1 := by
      rw [map_mul, Subgroup.coe_mul, hsq]
    have h3 : y * y = 1 :=
      c.ψ.injective (Subtype.ext (by rw [map_one, Subgroup.coe_one]; exact h2))
    exact congrArg Subtype.val h3
  · intro x hx hx2
    have hxY : x ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hLP hx
    have hxsq : ((c.ψ ⟨x, hxY⟩ : AE.aeSub 6) : AE.Wr 6) * ((c.ψ ⟨x, hxY⟩ : AE.aeSub 6) : AE.Wr 6)
        = 1 := by
      have h2 : ((c.ψ (⟨x, hxY⟩ * ⟨x, hxY⟩) : AE.aeSub 6) : AE.Wr 6) = 1 := by
        have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
          Subtype.ext hx2
        rw [this, map_one]
        rfl
      rw [map_mul, Subgroup.coe_mul] at h2
      exact h2
    have hxmem := (ae8c_mem_iff c hlab ⟨x, hxY⟩).mp hx
    rcases ae8c_memAt_invol hxmem hxsq with h1 | h1
    · left
      have : (⟨x, hxY⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
        c.ψ.injective (Subtype.ext (by rw [map_one, Subgroup.coe_one]; exact h1))
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hxY⟩ : ↥(pSpan (Generic.centMembers Ω u))) = y :=
        c.ψ.injective (Subtype.ext (h1.trans hψ.symm))
      exact congrArg Subtype.val this

theorem ae8c_not_mem_Z (H : End18.Hyp Ω) (c : Chart Ω u) :
    ¬ ∃ M ∈ Ω, IsUniqueInvolution M u := by
  rintro ⟨M, hM, hMu⟩
  have hP : M ∈ Generic.centMembers Ω u :=
    Generic.mem_centMembers_iff_commute.mpr ⟨hM, ae8c_central H hM hMu⟩
  obtain ⟨α, h, b, hlab⟩ := c.label M hP
  have hmem := (ae8c_mem_iff c hlab ⟨u, c.mem⟩).mp hMu.mem
  exact AE.ne_allOnes_of_supportedOn (by norm_num) (AE.supportedOn_of_mem_memAt hmem) c.u_eq

theorem ae8c_conj_u_not_Z (H : End18.Hyp Ω) (c : Chart Ω u) (g : G)
    (hg : ∃ L ∈ Ω, IsUniqueInvolution L (g * u * g⁻¹)) : False := by
  obtain ⟨L, hL, hz⟩ := ae8c_conj_Z H.endHyp.thmD.hyp.conjInvariant (g := g⁻¹) hg
  have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rw [e] at hz
  exact ae8c_not_mem_Z H c ⟨L, hL, hz⟩

section FrameCert


theorem ae8i_mem_normalizer_of_comm {R : Subgroup G} {v : G}
    (h : ∀ r ∈ R, v * r = r * v) : v ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hv : ∀ r ∈ R, v * r * v⁻¹ = r := fun r hr => by
    rw [h r hr, mul_assoc, mul_inv_cancel, mul_one]
  have hv' : ∀ r ∈ R, v⁻¹ * r * v = r := fun r hr => by
    rw [mul_assoc, ← h r hr, inv_mul_cancel_left]
  constructor
  · intro hx
    rw [hv x hx]
    exact hx
  · intro hx
    have e2 : x = v * x * v⁻¹ := by
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = v * x * v⁻¹ := hv' _ hx
    rw [e2]
    exact hx

theorem ae8i_zSet_conj (hΩ : ConjInvariant Ω) (g x : G) (hx : x ∈ zSet Ω) :
    g * x * g⁻¹ ∈ zSet Ω := by
  obtain ⟨K, hK, hKx⟩ := hx
  exact ⟨conjSub g K, hΩ g K hK, hKx.conj g⟩

theorem ae8i_zSet_conj_iff (hΩ : ConjInvariant Ω) (g x : G) :
    g * x * g⁻¹ ∈ zSet Ω ↔ x ∈ zSet Ω := by
  refine ⟨fun h => ?_, fun h => ae8i_zSet_conj hΩ g x h⟩
  have h2 := ae8i_zSet_conj hΩ g⁻¹ _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem ae8i_conj_preimage_ncard (hN : (zGroup Ω).Normal) (g : G) (S : Set (zGroup Ω)) :
    ((fun r : zGroup Ω => (⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩ : zGroup Ω)) ⁻¹' S).ncard =
      S.ncard := by
  have hinj : Function.Injective
      (fun r : zGroup Ω => (⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩ : zGroup Ω)) := by
    intro r s hrs
    apply Subtype.ext
    have h1 : g * r.1 * g⁻¹ = g * s.1 * g⁻¹ := congrArg Subtype.val hrs
    calc r.1 = g⁻¹ * (g * r.1 * g⁻¹) * g := by group
      _ = g⁻¹ * (g * s.1 * g⁻¹) * g := by rw [h1]
      _ = s.1 := by group
  have hsub : S ⊆ Set.range
      (fun r : zGroup Ω => (⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩ : zGroup Ω)) := by
    intro r' _
    refine ⟨⟨g⁻¹ * r'.1 * g⁻¹⁻¹, hN.conj_mem r'.1 r'.2 g⁻¹⟩, ?_⟩
    apply Subtype.ext
    show g * (g⁻¹ * r'.1 * g⁻¹⁻¹) * g⁻¹ = r'.1
    group
  exact Set.ncard_preimage_of_injective_subset_range hinj hsub

namespace SectFrame

theorem perp_iff (H : End18.Hyp Ω) (hu : SectFrame Ω u)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (p : zGroup Ω)
    (hp : p ∈ zPoints Ω) :
    bf ⟨u, hu.mem⟩ p = 0 ↔ ∃ R ∈ Generic.centMembers Ω u, IsUniqueInvolution R p.1 := by
  obtain ⟨K, hK, hKp⟩ := hp
  constructor
  · intro h
    have hN : u ∈ Subgroup.normalizer (K : Set G) := (hbf.spec K hK p hKp ⟨u, hu.mem⟩).mp h
    obtain ⟨R, hR, hRtw⟩ := hu.cent K hK hN
    obtain ⟨-, z, hKz, hRz⟩ := hRtw
    exact ⟨R, hR, by rw [← hKz.eq hKp]; exact hRz⟩
  · rintro ⟨R, hR, hRp⟩
    have hN : u ∈ Subgroup.normalizer (R : Set G) :=
      ae8i_mem_normalizer_of_comm (fun r hr => (Subgroup.mem_centralizer_singleton_iff.mp
        (hR.2 hr)).symm)
    exact (hbf.spec R hR.1 p hRp ⟨u, hu.mem⟩).mpr hN

theorem exists_conj_mul (H : End18.Hyp Ω) (hu : SectFrame Ω u) {L : Subgroup G}
    (hL : L ∈ Generic.centMembers Ω u) {a : G} (ha : IsUniqueInvolution L a) :
    ∃ g : G, g * u * g⁻¹ = u * a := by
  obtain ⟨L', hL'V, hL'P⟩ : ∃ L' ∈ twinSet Ω L, L' ∉ Generic.centMembers Ω u := by
    by_contra hcon
    push Not at hcon
    have h1 : twinSet Ω L ∩ Generic.centMembers Ω u = twinSet Ω L :=
      Set.inter_eq_left.mpr hcon
    have h2 := SectData.ncard_twin H hu.toSectData L hL
    rw [h1, H.ncard_twinSet hL.1] at h2
    norm_num at h2
  have hL'Ω : L' ∈ Ω := hL'V.1
  obtain ⟨z, hLz, hL'z⟩ := hL'V.2
  have hL'a : IsUniqueInvolution L' a := by
    rw [← hLz.eq ha]
    exact hL'z
  have huL : u ∈ Subgroup.normalizer (L : Set G) :=
    ae8i_mem_normalizer_of_comm (fun r hr => (Subgroup.mem_centralizer_singleton_iff.mp
      (hL.2 hr)).symm)
  have huL' : u ∈ Subgroup.normalizer (L' : Set G) := by
    have hz0 := H.zGroup_inf_normalizer_eq hL.1 hL'V
    have hmem : u ∈ zGroup Ω ⊓ Subgroup.normalizer (L : Set G) := ⟨hu.mem, huL⟩
    rw [hz0] at hmem
    exact hmem.2
  obtain ⟨t, htL', htu⟩ : ∃ t ∈ L', t * u ≠ u * t := by
    by_contra hcon
    push Not at hcon
    exact hL'P ⟨hL'Ω, fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hcon t ht)⟩
  have hN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant H.endHyp.thmD.hyp.conjInvariant
  have ha_mem : a ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, ha⟩
  have hcD : t * u * t⁻¹ * u⁻¹ ∈ zGroup Ω :=
    mul_mem (hN.conj_mem u hu.mem t) (inv_mem hu.mem)
  have hcL' : t * u * t⁻¹ * u⁻¹ ∈ L' := by
    have h2 : u * t⁻¹ * u⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.mp huL' t⁻¹).mp
      (inv_mem htL')
    have h3 := mul_mem htL' h2
    simpa [mul_assoc] using h3
  have hc2 : t * u * t⁻¹ * u⁻¹ * (t * u * t⁻¹ * u⁻¹) = 1 :=
    H.endHyp.zGroup_mul_self H.perp9 _ hcD
  have hc1 : t * u * t⁻¹ * u⁻¹ ≠ 1 := by
    intro h
    apply htu
    have h4 : t * u * t⁻¹ = u := by
      calc t * u * t⁻¹ = t * u * t⁻¹ * u⁻¹ * u := by group
        _ = u := by rw [h, one_mul]
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [h4]
  have hca : t * u * t⁻¹ * u⁻¹ = a := (hL'a.unique _ hcL' hc2).resolve_left hc1
  refine ⟨t, ?_⟩
  have h3 : t * u * t⁻¹ = a * u := by
    rw [← hca]
    group
  rw [h3, H.endHyp.zGroup_comm H.perp9 a ha_mem u hu.mem]

end SectFrame

theorem card_nbr_eq (H : End18.Hyp Ω) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) (p q : zGroup Ω) (hp : p ∈ zPoints Ω) (hq : q ∈ zPoints Ω) :
    {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p ∧ bf p r = 0}.ncard =
      {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ q ∧ bf q r = 0}.ncard := by
  obtain ⟨Kp, hKp, hpK⟩ := hp
  obtain ⟨Kq, hKq, hqK⟩ := hq
  obtain ⟨g, hg⟩ := H.endHyp.thmD.trans Kp hKp Kq hKq
  have hΩ := H.endHyp.thmD.hyp.conjInvariant
  have hN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩ
  let f : zGroup Ω → zGroup Ω := fun r => ⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩
  have hf1 : ∀ r : zGroup Ω, (f r).1 = g * r.1 * g⁻¹ := fun r => rfl
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    have h1 : g * r.1 * g⁻¹ = g * s.1 * g⁻¹ := congrArg Subtype.val hrs
    calc r.1 = g⁻¹ * (g * r.1 * g⁻¹) * g := by group
      _ = g⁻¹ * (g * s.1 * g⁻¹) * g := by rw [h1]
      _ = s.1 := by group
  have hfp : f p = q := by
    apply Subtype.ext
    have h1 : IsUniqueInvolution Kq (g * p.1 * g⁻¹) := by
      rw [← hg]
      exact hpK.conj g
    rw [hf1]
    exact h1.eq hqK
  have hpt : ∀ r : zGroup Ω, r ∈ zPoints Ω ↔ f r ∈ zPoints Ω := fun r => by
    show r.1 ∈ zSet Ω ↔ g * r.1 * g⁻¹ ∈ zSet Ω
    exact (ae8i_zSet_conj_iff hΩ g r.1).symm
  have hsurj : ∀ r' : zGroup Ω, ∃ r : zGroup Ω, f r = r' := fun r' =>
    ⟨⟨g⁻¹ * r'.1 * g⁻¹⁻¹, hN.conj_mem r'.1 r'.2 g⁻¹⟩, by
      apply Subtype.ext
      rw [hf1]
      show g * (g⁻¹ * r'.1 * g⁻¹⁻¹) * g⁻¹ = r'.1
      group⟩
  have hpre : f ⁻¹' {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ q ∧ bf q r = 0} =
      {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p ∧ bf p r = 0} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hfp, ← hpt r]
    have hb : bf (f p) (f r) = bf p r := hbf.conj g p r (f p) (f r) rfl rfl
    rw [hb]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun h => h2 (by rw [h]), h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun h => h2 (hinj h), h3⟩
  have hsub : {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ q ∧ bf q r = 0} ⊆ Set.range f := by
    intro r' _
    obtain ⟨r, hr⟩ := hsurj r'
    exact ⟨r, hr⟩
  rw [← hpre, Set.ncard_preimage_of_injective_subset_range hinj hsub]

theorem ae8i_q8_rel {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    z * i = i * z ∧ z * j = j * z ∧ j * (z * i) = i * j ∧ i⁻¹ * j * i * j⁻¹ = z ∧
      j⁻¹ * i * j * i⁻¹ = z := by
  have hzi : z * i = i * z := by
    rw [← hQ.sq_i]
    group
  have hzj : z * j = j * z := by
    rw [← hQ.sq_j]
    group
  have h2 : j * (z * i) = i * j := by
    calc j * (z * i) = j * z * i := by group
      _ = j * (j * j) * i := by rw [hQ.sq_j]
      _ = (j * j) * (j * i) := by group
      _ = z * (z * (i * j)) := by rw [hQ.sq_j, hQ.comm]
      _ = (z * z) * (i * j) := by group
      _ = i * j := by rw [hQ.inv.sq, one_mul]
  have hzi' : i⁻¹ * z * i = z := by
    rw [← hQ.sq_i]
    group
  have h3 : i⁻¹ * j * i * j⁻¹ = z := by
    calc i⁻¹ * j * i * j⁻¹ = i⁻¹ * (j * i) * j⁻¹ := by group
      _ = i⁻¹ * (z * (i * j)) * j⁻¹ := by rw [hQ.comm]
      _ = (i⁻¹ * z * i) * j * j⁻¹ := by group
      _ = z := by rw [hzi']; group
  have h4 : j⁻¹ * i * j * i⁻¹ = z := by
    calc j⁻¹ * i * j * i⁻¹ = j⁻¹ * (i * j) * i⁻¹ := by group
      _ = j⁻¹ * (j * (z * i)) * i⁻¹ := by rw [h2]
      _ = z := by group
  exact ⟨hzi, hzj, h2, h3, h4⟩

theorem ae8i_q8_center {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) (hc : ∀ y ∈ K, y * x = x * y) : x = 1 ∨ x = z := by
  obtain ⟨hzi, -, h2, -, -⟩ := ae8i_q8_rel hQ
  have hzz := hQ.inv.sq
  have hnot : ∀ w : G, z * w = w → False := fun w hw =>
    hQ.inv.ne_one (mul_right_cancel (hw.trans (one_mul w).symm))
  have e3 : i * (i * j) = z * j := by
    rw [← mul_assoc, hQ.sq_i]
  have h5 : i * j * i = j := by
    calc i * j * i = i * (j * i) := by group
      _ = i * (z * (i * j)) := by rw [hQ.comm]
      _ = z * (i * (i * j)) := by rw [← mul_assoc, ← hzi, mul_assoc]
      _ = z * (z * j) := by rw [e3]
      _ = j := by rw [← mul_assoc, hzz, one_mul]
  have e4 : i * (z * (i * j)) = z * (z * j) := by
    rw [← mul_assoc, ← hzi, mul_assoc, e3]
  have e5 : z * (i * j) * i = z * j := by
    rw [mul_assoc, h5]
  have e6a : i * (z * j) = z * (i * j) := by
    rw [← mul_assoc i z j, ← hzi, mul_assoc z i j]
  have e6b : z * j * i = i * j := by
    rw [mul_assoc z j i, hQ.comm, ← mul_assoc z z (i * j), hzz, one_mul]
  rcases hQ.nf x hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, hQ.comm] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, h2, mul_assoc z i j] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, hQ.comm] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e6a, e6b] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, h5, e3] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e4, e5] at h6
    have h7 : z * j = j := by
      calc z * j = z * (z * j) := h6.symm
        _ = (z * z) * j := by group
        _ = j := by rw [hzz, one_mul]
    exact hnot _ h7

theorem ae8i_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

theorem ae8i_z_central {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) {m : G}
    (hm : m ∈ K) : z * m = m * z := by
  have hc : m * z * m⁻¹ = z := by
    have hmem : m * z * m⁻¹ ∈ K := K.mul_mem (K.mul_mem hm hz.mem) (K.inv_mem hm)
    have hsq : m * z * m⁻¹ * (m * z * m⁻¹) = 1 := by
      calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
        _ = 1 := by rw [hz.sq, mul_one, mul_inv_cancel]
    rcases hz.unique _ hmem hsq with h | h
    · exfalso
      apply hz.ne_one
      calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group
    · exact h
  calc z * m = m * z * m⁻¹ * m := by rw [hc]
    _ = m * z := by group

theorem ae8i_D0_centralizer (H : End18.Hyp Ω) {K K' : Subgroup G} {z i j : G} (hK : K ∈ Ω)
    (hQ : Q8Data K z i j) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {d : G}
    (hd : d ∈ zGroup Ω ⊓ (K ⊔ K')) (hdK : ∀ m ∈ K, d * m = m * d) :
    d ∈ Subgroup.zpowers z := by
  have hself : K ∈ twinSet Ω K := ⟨hK, z, hQ.inv, hQ.inv⟩
  have hcomm : Commutes K K' := (H.sup_twin hQ.inv hself hK' hne.symm).1
  have hK'Ω : K' ∈ Ω := hK'.1
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hKz', hK'z'⟩ := hK'
    rw [hQ.inv.eq hKz']
    exact hK'z'
  have hdD := hd.1
  obtain ⟨k, hk, k', hk', rfl⟩ := ae8i_sup_decomp hcomm hd.2
  have hkc : ∀ m ∈ K, k * m = m * k := by
    intro m hm
    have h1 := hdK m hm
    have h3 : k * m * k' = m * k * k' := by
      calc k * m * k' = k * (m * k') := by group
        _ = k * (k' * m) := by rw [hcomm m hm k' hk']
        _ = k * k' * m := by group
        _ = m * (k * k') := h1
        _ = m * k * k' := by group
    exact mul_right_cancel h3
  have hk1 : k ∈ Subgroup.zpowers z := by
    rcases ae8i_q8_center hQ hk (fun y hy => (hkc y hy).symm) with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers z
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hQ.inv⟩
  have hkD : k ∈ zGroup Ω := Subgroup.zpowers_le.mpr hzD hk1
  have hk'D : k' ∈ zGroup Ω := by
    have e : k' = k⁻¹ * (k * k') := by group
    rw [e]
    exact mul_mem (inv_mem hkD) hdD
  have hk'pC : k' ∈ K' ⊓ pCore 2 G := ⟨hk', H.endHyp.zGroup_le_pCore hk'D⟩
  rw [H.inf_pCore hK'Ω hz'] at hk'pC
  exact mul_mem hk1 hk'pC

theorem ae8i_claimF (H : End18.Hyp Ω) {K K' : Subgroup G} {z i j : G} (hK : K ∈ Ω)
    (hQ : Q8Data K z i j) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {y : G}
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hyK' : y ∈ Subgroup.normalizer (K' : Set G))
    (hyc : ∀ m ∈ K, y * m * y⁻¹ = m) {d : G} (hd : d ∈ zGroup Ω ⊓ (K ⊔ K')) :
    y * d * y⁻¹ * d⁻¹ ∈ Subgroup.zpowers z := by
  have hcomm : Commutes K K' := (H.sup_twin hQ.inv ⟨hK, z, hQ.inv, hQ.inv⟩ hK' hne.symm).1
  have hN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant H.endHyp.thmD.hyp.conjInvariant
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hQ.inv⟩
  have hdD := hd.1
  have hdS := hd.2
  obtain ⟨k₁, hk₁, k₁', hk₁', hk₁eq⟩ := ae8i_sup_decomp hcomm hdS
  have hcS : y * d * y⁻¹ ∈ K ⊔ K' := by
    rw [hk₁eq]
    have h1 : y * (k₁ * k₁') * y⁻¹ = (y * k₁ * y⁻¹) * (y * k₁' * y⁻¹) := by group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hyK k₁).mp hk₁))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hyK' k₁').mp hk₁'))
  have hcD : y * d * y⁻¹ ∈ zGroup Ω := hN.conj_mem d hdD y
  have ht : d⁻¹ * (y * d * y⁻¹) ∈ zGroup Ω ⊓ (K ⊔ K') :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hdD) hcD,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hdS) hcS⟩
  have hcent : ∀ m ∈ K, d⁻¹ * (y * d * y⁻¹) * m = m * (d⁻¹ * (y * d * y⁻¹)) := by
    intro m hm
    have hdm : d * m * d⁻¹ = k₁ * m * k₁⁻¹ := by
      have e : d = k₁ * k₁' := hk₁eq
      rw [e]
      have hc' : k₁' * m = m * k₁' := (hcomm m hm k₁' hk₁').symm
      calc k₁ * k₁' * m * (k₁ * k₁')⁻¹ = k₁ * (k₁' * m * k₁'⁻¹) * k₁⁻¹ := by group
        _ = k₁ * (m * k₁' * k₁'⁻¹) * k₁⁻¹ := by rw [hc']
        _ = k₁ * m * k₁⁻¹ := by group
    have hym : y * m = m * y := by
      have := hyc m hm
      calc y * m = y * m * y⁻¹ * y := by group
        _ = m * y := by rw [this]
    have hyk : y * k₁ * y⁻¹ = k₁ := hyc k₁ hk₁
    have hyk1 : y * k₁⁻¹ * y⁻¹ = k₁⁻¹ := by
      calc y * k₁⁻¹ * y⁻¹ = (y * k₁ * y⁻¹)⁻¹ := by group
        _ = k₁⁻¹ := by rw [hyk]
    have hcm : y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹ = d * m * d⁻¹ := by
      have hy'm : y⁻¹ * m * y = m := by
        calc y⁻¹ * m * y = y⁻¹ * (m * y) := by group
          _ = y⁻¹ * (y * m) := by rw [hym]
          _ = m := by group
      calc y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹ = y * d * (y⁻¹ * m * y) * d⁻¹ * y⁻¹ := by group
        _ = y * (d * m * d⁻¹) * y⁻¹ := by rw [hy'm]; group
        _ = y * (k₁ * m * k₁⁻¹) * y⁻¹ := by rw [hdm]
        _ = (y * k₁ * y⁻¹) * (y * m * y⁻¹) * (y * k₁⁻¹ * y⁻¹) := by group
        _ = k₁ * m * k₁⁻¹ := by
          rw [hyk, hyc m hm, hyk1]
        _ = d * m * d⁻¹ := hdm.symm
    have hdc : d⁻¹ * (y * d * y⁻¹) * m = m * (d⁻¹ * (y * d * y⁻¹)) := by
      have e1 : y * d * y⁻¹ * m = (d * m * d⁻¹) * (y * d * y⁻¹) := by
        rw [← hcm]
        group
      calc d⁻¹ * (y * d * y⁻¹) * m = d⁻¹ * ((d * m * d⁻¹) * (y * d * y⁻¹)) := by
            rw [← e1]; group
        _ = m * (d⁻¹ * (y * d * y⁻¹)) := by
            have e2 : d⁻¹ * ((d * m * d⁻¹) * (y * d * y⁻¹)) =
                (d⁻¹ * (d * m * d⁻¹)) * (y * d * y⁻¹) := by group
            rw [e2]
            have e3 : d⁻¹ * (d * m * d⁻¹) = m * d⁻¹ := by group
            rw [e3]
            group
    exact hdc
  have hmem := ae8i_D0_centralizer H hK hQ hK' hne ht hcent
  have hdc' : d * (y * d * y⁻¹) = (y * d * y⁻¹) * d :=
    H.endHyp.zGroup_comm H.perp9 d hdD _ hcD
  have e : y * d * y⁻¹ * d⁻¹ = d⁻¹ * (y * d * y⁻¹) := by
    calc y * d * y⁻¹ * d⁻¹ = d⁻¹ * (d * (y * d * y⁻¹)) * d⁻¹ := by group
      _ = d⁻¹ * ((y * d * y⁻¹) * d) * d⁻¹ := by rw [hdc']
      _ = d⁻¹ * (y * d * y⁻¹) := by group
  rw [e]
  exact hmem

theorem ae8i_claimG (H : End18.Hyp Ω) {K₃ K₄ : Subgroup G} {z i j : G} (hK₃ : K₃ ∈ Ω)
    (hQ : Q8Data K₃ z i j) (hK₄ : K₄ ∈ twinSet Ω K₃) (hne : K₄ ≠ K₃) {y : G}
    (hy₃ : y ∈ Subgroup.normalizer (K₃ : Set G)) (hodd : Odd (orderOf y))
    (hnc : ∃ m ∈ K₃, y * m ≠ m * y) {d : G} (hd : d ∈ zGroup Ω ⊓ (K₃ ⊔ K₄))
    (hdz : d ∉ Subgroup.zpowers z) :
    y * d * y⁻¹ * d⁻¹ ∉ Subgroup.zpowers z := by
  intro hw
  have hcomm : Commutes K₃ K₄ := (H.sup_twin hQ.inv ⟨hK₃, z, hQ.inv, hQ.inv⟩ hK₄ hne.symm).1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz₄ : IsUniqueInvolution K₄ z := by
    obtain ⟨-, z', hK₃z', hK₄z'⟩ := hK₄
    rw [hQ.inv.eq hK₃z']
    exact hK₄z'
  have hdD := hd.1
  obtain ⟨k₃, hk₃, k₄, hk₄, hdeq⟩ := ae8i_sup_decomp hcomm hd.2
  have hzK₄ : Subgroup.zpowers z ≤ K₄ := Subgroup.zpowers_le.mpr hz₄.mem
  have hk₃z : k₃ ∉ Subgroup.zpowers z := by
    intro h
    apply hdz
    have hdK₄ : d ∈ K₄ := by
      rw [hdeq]
      exact K₄.mul_mem (hzK₄ h) hk₄
    have hdpC : d ∈ K₄ ⊓ pCore 2 G := ⟨hdK₄, H.endHyp.zGroup_le_pCore hdD⟩
    rw [H.inf_pCore hK₄Ω hz₄] at hdpC
    exact hdpC
  have hdK₃ : ∀ x ∈ K₃, d * x * d⁻¹ = k₃ * x * k₃⁻¹ := by
    intro x hx
    have hc : x * k₄ = k₄ * x := hcomm x hx k₄ hk₄
    rw [hdeq]
    calc k₃ * k₄ * x * (k₃ * k₄)⁻¹ = k₃ * (k₄ * x * k₄⁻¹) * k₃⁻¹ := by group
      _ = k₃ * x * k₃⁻¹ := by rw [← hc]; group
  have hdK₃mem : ∀ x ∈ K₃, d * x * d⁻¹ ∈ K₃ := fun x hx => by
    rw [hdK₃ x hx]
    exact K₃.mul_mem (K₃.mul_mem hk₃ hx) (K₃.inv_mem hk₃)
  have hwK : ∀ x ∈ K₃, (y * d * y⁻¹ * d⁻¹) * x = x * (y * d * y⁻¹ * d⁻¹) := by
    intro x hx
    rcases ae8c_zpowers_invol hQ.inv.sq hw with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact ae8i_z_central hQ.inv hx
  have hstar : ∀ m ∈ K₃, (y * k₃ * y⁻¹) * m * (y * k₃ * y⁻¹)⁻¹ = k₃ * m * k₃⁻¹ := by
    intro m hm
    have hy' : y⁻¹ ∈ Subgroup.normalizer (K₃ : Set G) := inv_mem hy₃
    have hm' : y⁻¹ * m * y ∈ K₃ := by
      have := (Subgroup.mem_normalizer_iff.mp hy' m).mp hm
      rwa [inv_inv] at this
    have hc1 : y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹ = d * m * d⁻¹ := by
      calc y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹
          = ((y * d * y⁻¹ * d⁻¹) * d) * m * (d⁻¹ * (y * d * y⁻¹ * d⁻¹)⁻¹ ) := by group
        _ = ((y * d * y⁻¹ * d⁻¹) * (d * m * d⁻¹)) * (y * d * y⁻¹ * d⁻¹)⁻¹ := by group
        _ = (d * m * d⁻¹) := by
          rw [hwK _ (hdK₃mem m hm)]
          group
    have hc2 : y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹ =
        (y * k₃ * y⁻¹) * m * (y * k₃ * y⁻¹)⁻¹ := by
      calc y * d * y⁻¹ * m * (y * d * y⁻¹)⁻¹ = y * (d * (y⁻¹ * m * y) * d⁻¹) * y⁻¹ := by group
        _ = y * (k₃ * (y⁻¹ * m * y) * k₃⁻¹) * y⁻¹ := by rw [hdK₃ _ hm']
        _ = (y * k₃ * y⁻¹) * (y * (y⁻¹ * m * y) * y⁻¹) * (y * k₃ * y⁻¹)⁻¹ := by group
        _ = (y * k₃ * y⁻¹) * m * (y * k₃ * y⁻¹)⁻¹ := by
          rw [show y * (y⁻¹ * m * y) * y⁻¹ = m by group]
    rw [← hc2, hc1, hdK₃ m hm]
  have hgK₃ : (y * k₃ * y⁻¹) ∈ K₃ := (Subgroup.mem_normalizer_iff.mp hy₃ k₃).mp hk₃
  have hhK₃ : k₃⁻¹ * (y * k₃ * y⁻¹) ∈ K₃ := K₃.mul_mem (K₃.inv_mem hk₃) hgK₃
  have hhc : ∀ m ∈ K₃, m * (k₃⁻¹ * (y * k₃ * y⁻¹)) = (k₃⁻¹ * (y * k₃ * y⁻¹)) * m := by
    intro m hm
    calc m * (k₃⁻¹ * (y * k₃ * y⁻¹)) = k₃⁻¹ * (k₃ * m * k₃⁻¹) * (y * k₃ * y⁻¹) := by group
      _ = k₃⁻¹ * ((y * k₃ * y⁻¹) * m * (y * k₃ * y⁻¹)⁻¹) * (y * k₃ * y⁻¹) := by
        rw [hstar m hm]
      _ = (k₃⁻¹ * (y * k₃ * y⁻¹)) * m := by group
  have hcen := ae8i_q8_center hQ hhK₃ (fun m hm => hhc m hm)
  have hfix : y * k₃ * y⁻¹ = k₃ ∨ y * k₃ * y⁻¹ = k₃ * z := by
    have hsplit : y * k₃ * y⁻¹ = k₃ * (k₃⁻¹ * (y * k₃ * y⁻¹)) := by group
    rcases hcen with h | h
    · left
      rw [hsplit, h, mul_one]
    · right
      rw [hsplit, h]
  have hcent := q8_centralizes_of_odd_fixes hQ hy₃ hodd hk₃ hk₃z hfix
  obtain ⟨m, hm, hmne⟩ := hnc
  apply hmne
  calc y * m = y * m * y⁻¹ * y := by group
    _ = m * y := by rw [hcent m hm]

theorem ae8i_normalizer_of_cube {L : Subgroup G} {y : G} (hy3 : y * y * y = 1)
    (hN : ∀ g ∈ L, y * g * y⁻¹ ∈ L) : y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact hN g
  · intro hg
    have h2 := hN _ (hN _ hg)
    have e : y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = g := by
      calc y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * g * (y * y * y)⁻¹ := by group
        _ = g := by rw [hy3]; group
    rw [← e]
    exact h2

theorem ae8i_yOf_conj (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) :
    ∀ a ∈ AE.memAt α h b, AE.yOf (AE.emb α h) * a * (AE.yOf (AE.emb α h))⁻¹ ∈ AE.memAt α h b := by
  cases b
  · exact AE.yOf_conj_mem_memKStar _
  · exact AE.yOf_conj_mem_memK _

theorem ae8i_dvd_of_fpf {X : Type} [Finite X] (p : ℕ) [Fact p.Prime] (f : X → X)
    (hf : ∀ x, f^[p] x = x) (hfix : ∀ x, f x ≠ x) : p ∣ Nat.card X := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  let F : Function.End X := f
  have hF : F ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    exact hf x
  have h := Equiv.Perm.card_fixedPoints_modEq hF
  have h0 : Fintype.card F.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hfix x.1 x.2⟩
  have key : Fintype.card X ≡ 0 [MOD p] := by
    convert h using 2
    exact h0.symm
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd).mp key

theorem ae8i_psi_conj (c : Chart Ω u) {y g : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (hg : g ∈ pSpan (Generic.centMembers Ω u))
    (hyg : y * g * y⁻¹ ∈ pSpan (Generic.centMembers Ω u)) :
    (c.ψ ⟨y * g * y⁻¹, hyg⟩ : AE.Wr 6) =
      (c.ψ ⟨y, hy⟩ : AE.Wr 6) * (c.ψ ⟨g, hg⟩ : AE.Wr 6) * (c.ψ ⟨y, hy⟩ : AE.Wr 6)⁻¹ := by
  have e : (⟨y * g * y⁻¹, hyg⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
      ⟨y, hy⟩ * ⟨g, hg⟩ * (⟨y, hy⟩)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem ae8i_exists_y (c : Chart Ω u) {α : Finset (Fin 6)} (h : α.card = 4) :
    ∃ y : ↥(pSpan (Generic.centMembers Ω u)),
      (c.ψ y : AE.Wr 6) = AE.yOf (AE.emb α h) :=
  ⟨c.ψ.symm ⟨AE.yOf (AE.emb α h), AE.yOf_mem_aeSub _⟩, by simp⟩

theorem ae8i_normalizes_of_label (c : Chart Ω u) {L : Subgroup G}
    (hL : L ∈ Generic.centMembers Ω u) {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b)
    {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (hψy : (c.ψ ⟨y, hy⟩ : AE.Wr 6) = AE.yOf (AE.emb α h))
    (hy3 : y * y * y = 1) : y ∈ Subgroup.normalizer (L : Set G) := by
  apply ae8i_normalizer_of_cube hy3
  intro g hg
  have hgY : g ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hL hg
  have hygY : y * g * y⁻¹ ∈ pSpan (Generic.centMembers Ω u) :=
    mul_mem (mul_mem hy hgY) (inv_mem hy)
  refine (ae8c_mem_iff c hlab ⟨y * g * y⁻¹, hygY⟩).mpr ?_
  have hmemg : (c.ψ ⟨g, hgY⟩ : AE.Wr 6) ∈ AE.memAt α h b :=
    (ae8c_mem_iff c hlab ⟨g, hgY⟩).mp hg
  rw [ae8i_psi_conj c hy hgY hygY, hψy]
  exact ae8i_yOf_conj α h b _ hmemg

theorem ae8i_ind_inj {α β : Finset (Fin 6)} (h : Chart.ae8b2_ind α = Chart.ae8b2_ind β) :
    α = β := by
  ext i
  have hi := congrFun h i
  unfold Chart.ae8b2_ind at hi
  by_cases hα : i ∈ α <;> by_cases hβ : i ∈ β <;> simp_all

theorem ae8i_twin_label_eq (H : End18.Hyp Ω) (c : Chart Ω u) {L₁ L₂ : Subgroup G} {z : G}
    (hL₁ : L₁ ∈ Generic.centMembers Ω u) (hL₂ : L₂ ∈ Generic.centMembers Ω u)
    (hz₁ : IsUniqueInvolution L₁ z) (hz₂ : IsUniqueInvolution L₂ z)
    {α₁ α₂ : Finset (Fin 6)} {h₁ : α₁.card = 4} {h₂ : α₂.card = 4} {b₁ b₂ : Bool}
    (hlab₁ : ((L₁.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α₁ h₁ b₁)
    (hlab₂ : ((L₂.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α₂ h₂ b₂) : α₁ = α₂ := by
  obtain ⟨w₁, hw₁, hw₁P, hψ₁⟩ := ae8c_exists_inv hL₁.1 hL₁ c hlab₁
  obtain ⟨w₂, hw₂, hw₂P, hψ₂⟩ := ae8c_exists_inv hL₂.1 hL₂ c hlab₂
  have e₁ : w₁ = z := hw₁.eq hz₁
  have e₂ : w₂ = z := hw₂.eq hz₂
  subst e₁
  subst e₂
  have hv := congrArg AE.Wr.vec (hψ₁.symm.trans hψ₂)
  rw [Chart.ae8b2_zOf_eq h₁, Chart.ae8b2_zOf_eq h₂] at hv
  exact ae8i_ind_inj hv

theorem ae8i_exists_noncomm (c : Chart Ω u) {L : Subgroup G}
    {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b)
    {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (hψy : (c.ψ ⟨y, hy⟩ : AE.Wr 6) = AE.yOf (AE.emb α h)) :
    ∃ m ∈ L, y * m ≠ m * y := by
  obtain ⟨a, ha, hna⟩ : ∃ a ∈ AE.memAt α h b,
      AE.yOf (AE.emb α h) * a ≠ a * AE.yOf (AE.emb α h) := by
    cases b
    · exact AE.yOf_not_comm_memKStar _
    · exact AE.yOf_not_comm_memK _
  rw [← hlab] at ha
  obtain ⟨z', hz', hza⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz'
  refine ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, fun hc => hna ?_⟩
  have hYc : (⟨y, hy⟩ : ↥(pSpan (Generic.centMembers Ω u))) * w = w * ⟨y, hy⟩ :=
    Subtype.ext hc
  have hk := congrArg (fun t => (c.ψ t : AE.Wr 6)) hYc
  simp only [map_mul, Subgroup.coe_mul] at hk
  have hwa : (c.ψ w : AE.Wr 6) = a := by
    rw [← hza, ← hwz]
    rfl
  rw [hψy, hwa] at hk
  exact hk

theorem ae8i_six_dvd_main (H : End18.Hyp Ω) (hu : SectFrame Ω u) (c : Chart Ω u)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (p₀ : zGroup Ω)
    (hp₀ : p₀ ∈ zPoints Ω) (K : Subgroup G) (hK : K ∈ Ω) (hz₀ : IsUniqueInvolution K p₀.1)
    (s : G) (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) (huK : u ∈ K ⊔ conjSub s K) :
    6 ∣ {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p₀ ∧ bf p₀ r = 0}.ncard := by
  classical
  have hNz : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant H.endHyp.thmD.hyp.conjInvariant
  have hz₀D : p₀.1 ∈ zGroup Ω := p₀.2
  have hKT : K ∈ twinSet Ω K := ⟨hK, p₀.1, hz₀, hz₀⟩
  have hK'T : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hK'Ω : conjSub s K ∈ Ω := hK'T.1
  have hz'K : IsUniqueInvolution (conjSub s K) p₀.1 := by
    obtain ⟨-, z', hKz', hK'z'⟩ := hK'T
    rw [hz₀.eq hKz']
    exact hK'z'
  have hcommKK' : Commutes K (conjSub s K) := (H.sup_twin hz₀ hKT hK'T hsK.symm).1
  have hinfKK' : K ⊓ conjSub s K = Subgroup.zpowers p₀.1 :=
    (H.sup_twin hz₀ hKT hK'T hsK.symm).2.1
  obtain ⟨K₃, hK₃T, hK₃K, hK₃K', hK₃s, hK₃sK, hK₃sK', htw⟩ := H.exists_twin_frame hK hs hsK
  have hK₃Ω : K₃ ∈ Ω := hK₃T.1
  set K₄ := conjSub s K₃ with hK₄def
  have hK₄Ω : K₄ ∈ Ω := H.endHyp.thmD.hyp.conjInvariant s K₃ hK₃Ω
  have hK₄T : K₄ ∈ twinSet Ω K := by
    rw [htw]
    simp
  have hz₃ : IsUniqueInvolution K₃ p₀.1 := by
    obtain ⟨-, z', hKz', hK₃z'⟩ := hK₃T
    rw [hz₀.eq hKz']
    exact hK₃z'
  have hz₄ : IsUniqueInvolution K₄ p₀.1 := by
    obtain ⟨-, z', hKz', hK₄z'⟩ := hK₄T
    rw [hz₀.eq hKz']
    exact hK₄z'
  have hK₃K₁ : Commutes K₃ K := (H.sup_twin hz₀ hK₃T hKT hK₃K).1
  have hK₃K₂ : Commutes K₃ (conjSub s K) := (H.sup_twin hz₀ hK₃T hK'T hK₃K').1
  have hK₄K₁ : Commutes K₄ K := (H.sup_twin hz₀ hK₄T hKT hK₃sK).1
  have hK₄K₂ : Commutes K₄ (conjSub s K) := (H.sup_twin hz₀ hK₄T hK'T hK₃sK').1
  have hK₃K₄ : Commutes K₃ K₄ := (H.sup_twin hz₀ hK₃T hK₄T hK₃s.symm).1
  obtain ⟨k₀, hk₀, k₀', hk₀', hku⟩ := ae8i_sup_decomp hcommKK' huK
  have hcomm_u : ∀ M : Subgroup G, Commutes M K → Commutes M (conjSub s K) →
      ∀ x ∈ M, x * u = u * x := by
    intro M hMK hMK' x hx
    rw [hku]
    calc x * (k₀ * k₀') = (x * k₀) * k₀' := by group
      _ = (k₀ * x) * k₀' := by rw [hMK x hx k₀ hk₀]
      _ = k₀ * (x * k₀') := by group
      _ = k₀ * (k₀' * x) := by rw [hMK' x hx k₀' hk₀']
      _ = k₀ * k₀' * x := by group
  have hK₃P : K₃ ∈ Generic.centMembers Ω u :=
    ⟨hK₃Ω, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_u K₃ hK₃K₁ hK₃K₂ x hx)⟩
  have hK₄P : K₄ ∈ Generic.centMembers Ω u :=
    ⟨hK₄Ω, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_u K₄ hK₄K₁ hK₄K₂ x hx)⟩
  obtain ⟨α, hα, b, hlab₃⟩ := c.label K₃ hK₃P
  obtain ⟨α₄, h₄, b₄, hlab₄⟩ := c.label K₄ hK₄P
  have hαeq : α = α₄ := ae8i_twin_label_eq H c hK₃P hK₄P hz₃ hz₄ hlab₃ hlab₄
  subst hαeq
  obtain ⟨y, hψy⟩ := ae8i_exists_y c hα
  have hy3' : y * y * y = 1 := by
    apply c.ψ.injective
    rw [map_mul, map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one, hψy]
    exact AE.yOf_pow_three _
  have hyG3 : y.1 * y.1 * y.1 = 1 := congrArg Subtype.val hy3'
  have hyN3 : y.1 ∈ Subgroup.normalizer (K₃ : Set G) :=
    ae8i_normalizes_of_label c hK₃P hlab₃ y.2 hψy hyG3
  have hyN4 : y.1 ∈ Subgroup.normalizer (K₄ : Set G) :=
    ae8i_normalizes_of_label c hK₄P hlab₄ y.2 hψy hyG3
  have hyC : y.1 * u = u * y.1 :=
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun L hL => hL.2) y.2)
  have hyz : y.1 * p₀.1 * y.1⁻¹ = p₀.1 := by
    have h1 : IsUniqueInvolution K₃ (y.1 * p₀.1 * y.1⁻¹) := by
      have := hz₃.conj y.1
      rwa [mem_normalizer_iff_conjSub_eq.mp hyN3] at this
    exact (hz₃.eq h1).symm
  have hconjtw : ∀ M : Subgroup G, IsUniqueInvolution M p₀.1 →
      IsUniqueInvolution (conjSub y.1 M) p₀.1 := by
    intro M hM
    have := hM.conj y.1
    rwa [hyz] at this
  have hyK3 : conjSub y.1 K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp hyN3
  have hyK4 : conjSub y.1 K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp hyN4
  have hyK : y.1 ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    have hA : conjSub y.1 K ∈ twinSet Ω K :=
      ⟨H.endHyp.thmD.hyp.conjInvariant y.1 K hK, p₀.1, hz₀, hconjtw K hz₀⟩
    rw [htw] at hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with h | h | h | h
    · exact h
    · exfalso
      have hB : conjSub y.1 (conjSub s K) ∈ twinSet Ω K :=
        ⟨H.endHyp.thmD.hyp.conjInvariant y.1 _ hK'Ω, p₀.1, hz₀, hconjtw _ hz'K⟩
      rw [htw] at hB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
      rcases hB with h' | h' | h' | h'
      · apply hsK
        have hKK : K = conjSub s K := by
          calc K = conjSub (y.1 * y.1 * y.1) K := by rw [hyG3, conjSub_one]
            _ = conjSub y.1 (conjSub y.1 (conjSub y.1 K)) := by rw [conjSub_mul, conjSub_mul]
            _ = conjSub y.1 (conjSub y.1 (conjSub s K)) := by rw [h]
            _ = conjSub y.1 K := by rw [h']
            _ = conjSub s K := h
        exact hKK.symm
      · exact hsK (conjSub_injective y.1 (h.trans h'.symm)).symm
      · exact hK₃K' (conjSub_injective y.1 (h'.trans hyK3.symm)).symm
      · exact hK₃sK' (conjSub_injective y.1 (h'.trans hyK4.symm)).symm
    · exact absurd (conjSub_injective y.1 (h.trans hyK3.symm)) hK₃K.symm
    · exact absurd (conjSub_injective y.1 (h.trans hyK4.symm)) hK₃sK.symm
  have hyK' : y.1 ∈ Subgroup.normalizer ((conjSub s K : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    have hB : conjSub y.1 (conjSub s K) ∈ twinSet Ω K :=
      ⟨H.endHyp.thmD.hyp.conjInvariant y.1 _ hK'Ω, p₀.1, hz₀, hconjtw _ hz'K⟩
    rw [htw] at hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    have hKfix : conjSub y.1 K = K := mem_normalizer_iff_conjSub_eq.mp hyK
    rcases hB with h' | h' | h' | h'
    · exact absurd (conjSub_injective y.1 (h'.trans hKfix.symm)) hsK
    · exact h'
    · exact absurd (conjSub_injective y.1 (h'.trans hyK3.symm)) hK₃K'.symm
    · exact absurd (conjSub_injective y.1 (h'.trans hyK4.symm)) hK₃sK'.symm
  obtain ⟨zq, i, j, hQ0⟩ := H.endHyp.exists_q8Data hK
  rw [hQ0.inv.eq hz₀] at hQ0
  have hk₀nz : k₀ ∉ Subgroup.zpowers p₀.1 := by
    intro hmem
    have hu' : u ∈ conjSub s K := by
      rw [hku]
      exact (conjSub s K).mul_mem ((Subgroup.zpowers_le.mpr hz'K.mem) hmem) hk₀'
    have hupC : u ∈ conjSub s K ⊓ pCore 2 G := ⟨hu', H.endHyp.zGroup_le_pCore hu.mem⟩
    rw [H.inf_pCore hK'Ω hz'K] at hupC
    rcases ae8c_zpowers_invol hQ0.inv.sq hupC with h1 | h1
    · exact hu.ne_one h1
    · exact ae8c_not_mem_Z H c ⟨K, hK, by rw [h1]; exact hz₀⟩
  have hyk₀ : y.1 * k₀ * y.1⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyK k₀).mp hk₀
  have hyk₀' : y.1 * k₀' * y.1⁻¹ ∈ conjSub s K :=
    (Subgroup.mem_normalizer_iff.mp hyK' k₀').mp hk₀'
  have hyuu : y.1 * u * y.1⁻¹ = u := by
    rw [hyC]
    group
  have hprod0 : (y.1 * k₀ * y.1⁻¹) * (y.1 * k₀' * y.1⁻¹) = k₀ * k₀' := by
    calc (y.1 * k₀ * y.1⁻¹) * (y.1 * k₀' * y.1⁻¹) = y.1 * (k₀ * k₀') * y.1⁻¹ := by group
      _ = y.1 * u * y.1⁻¹ := by rw [← hku]
      _ = u := hyuu
      _ = k₀ * k₀' := hku
  have hm : k₀⁻¹ * (y.1 * k₀ * y.1⁻¹) = k₀' * (y.1 * k₀' * y.1⁻¹)⁻¹ := by
    calc k₀⁻¹ * (y.1 * k₀ * y.1⁻¹)
        = k₀⁻¹ * ((y.1 * k₀ * y.1⁻¹) * (y.1 * k₀' * y.1⁻¹)) * (y.1 * k₀' * y.1⁻¹)⁻¹ := by
          group
      _ = k₀⁻¹ * (k₀ * k₀') * (y.1 * k₀' * y.1⁻¹)⁻¹ := by rw [hprod0]
      _ = k₀' * (y.1 * k₀' * y.1⁻¹)⁻¹ := by group
  have hm_mem : k₀⁻¹ * (y.1 * k₀ * y.1⁻¹) ∈ K ⊓ conjSub s K := by
    refine ⟨K.mul_mem (K.inv_mem hk₀) hyk₀, ?_⟩
    rw [hm]
    exact (conjSub s K).mul_mem hk₀' ((conjSub s K).inv_mem hyk₀')
  rw [hinfKK'] at hm_mem
  have hfixk : y.1 * k₀ * y.1⁻¹ = k₀ ∨ y.1 * k₀ * y.1⁻¹ = k₀ * p₀.1 := by
    rcases ae8c_zpowers_invol hQ0.inv.sq hm_mem with h1 | h1
    · left
      calc y.1 * k₀ * y.1⁻¹ = k₀ * (k₀⁻¹ * (y.1 * k₀ * y.1⁻¹)) := by group
        _ = k₀ := by rw [h1, mul_one]
    · right
      calc y.1 * k₀ * y.1⁻¹ = k₀ * (k₀⁻¹ * (y.1 * k₀ * y.1⁻¹)) := by group
        _ = k₀ * p₀.1 := by rw [h1]
  have hodd : Odd (orderOf y.1) := by
    have hpow : y.1 ^ 3 = 1 := by
      rw [pow_three, ← mul_assoc]
      exact hyG3
    have hd3 : orderOf y.1 ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact ⟨1, by norm_num⟩
  have hyc : ∀ m ∈ K, y.1 * m * y.1⁻¹ = m :=
    fun m hm' => q8_centralizes_of_odd_fixes hQ0 hyK hodd hk₀ hk₀nz hfixk m hm'
  have hnc : ∃ m ∈ K₃, y.1 * m ≠ m * y.1 := ae8i_exists_noncomm c hlab₃ y.2 hψy
  obtain ⟨zq3, i3, j3, hQ3⟩ := H.endHyp.exists_q8Data hK₃Ω
  rw [hQ3.inv.eq hz₃] at hQ3
  have hK₄T3 : K₄ ∈ twinSet Ω K₃ := ⟨hK₄Ω, p₀.1, hz₃, hz₄⟩
  set N : Set (zGroup Ω) := {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p₀ ∧ bf p₀ r = 0} with hN
  have hspan := H.zGroup_inf_span_twin_eq hK hs hsK hK₃T hK₃K hK₃K'
  have hcomD : Commutes (zGroup Ω ⊓ (K ⊔ conjSub s K)) (zGroup Ω ⊓ (K₃ ⊔ K₄)) :=
    fun x hx y' hy' => H.endHyp.zGroup_comm H.perp9 x hx.1 y' hy'.1
  have hdecomp : ∀ r ∈ N, ∃ d d' : G, d ∈ zGroup Ω ⊓ (K ⊔ conjSub s K) ∧
      d' ∈ zGroup Ω ⊓ (K₃ ⊔ K₄) ∧ r.1 = d * d' ∧ d ∉ Subgroup.zpowers p₀.1 ∧
      d' ∉ Subgroup.zpowers p₀.1 := by
    intro r hr
    obtain ⟨hrP, hrne, hrb⟩ := hr
    obtain ⟨J, hJ, hJr⟩ := hrP
    have hrK : r.1 ∈ Subgroup.normalizer (K : Set G) :=
      (hbf.spec K hK p₀ hz₀ r).mp ((hbf.symm r p₀).trans hrb)
    have hrspan : r.1 ∈ zGroup Ω ⊓ pSpan (twinSet Ω K) :=
      ⟨r.2, H.eGroup_le_span hK ((H.mem_eGroup_iff_normalizes hK hJ hJr).mpr hrK)⟩
    rw [hspan] at hrspan
    obtain ⟨d, hd, d', hd', hdd⟩ := ae8i_sup_decomp hcomD hrspan
    have hr1 : r.1 ∉ Subgroup.zpowers p₀.1 := by
      intro h
      rcases ae8c_zpowers_invol hQ0.inv.sq h with h1 | h1
      · exact hJr.ne_one h1
      · exact hrne (Subtype.ext h1)
    have hzD₃ : Subgroup.zpowers p₀.1 ≤ zGroup Ω ⊓ (K₃ ⊔ K₄) :=
      Subgroup.zpowers_le.mpr ⟨hz₀D, Subgroup.mem_sup_left hz₃.mem⟩
    have hzD₀ : Subgroup.zpowers p₀.1 ≤ zGroup Ω ⊓ (K ⊔ conjSub s K) :=
      Subgroup.zpowers_le.mpr ⟨hz₀D, Subgroup.mem_sup_left hz₀.mem⟩
    have hdnz : d ∉ Subgroup.zpowers p₀.1 := by
      intro hdz
      have hrD₃ : r.1 ∈ zGroup Ω ⊓ (K₃ ⊔ K₄) := by
        rw [hdd]
        exact Subgroup.mul_mem _ (hzD₃ hdz) hd'
      exact H.not_point_of_mem_dZero hK₃Ω hz₃ hs hK₃s hrD₃ hr1 ⟨J, hJ, hJr⟩
    have hd'nz : d' ∉ Subgroup.zpowers p₀.1 := by
      intro hd'z
      have hrD₀ : r.1 ∈ zGroup Ω ⊓ (K ⊔ conjSub s K) := by
        rw [hdd]
        exact Subgroup.mul_mem _ hd (hzD₀ hd'z)
      exact H.not_point_of_mem_dZero hK hz₀ hs hsK hrD₀ hr1 ⟨J, hJ, hJr⟩
    exact ⟨d, d', hd, hd', hdd, hdnz, hd'nz⟩
  have hfix3 : ∀ r ∈ N, y.1 * r.1 * y.1⁻¹ ≠ r.1 := by
    intro r hr hcon
    obtain ⟨d, d', hd, hd', hdd, hdnz, hd'nz⟩ := hdecomp r hr
    have ht := ae8i_claimF H hK hQ0 hK'T hsK hyK hyK' hyc hd
    have ht' := ae8i_claimG H hK₃Ω hQ3 hK₄T3 hK₃s hyN3 hodd hnc hd' hd'nz
    obtain ⟨T, hT⟩ : ∃ T : G, T = y.1 * d * y.1⁻¹ * d⁻¹ := ⟨_, rfl⟩
    obtain ⟨T', hT'⟩ : ∃ T' : G, T' = y.1 * d' * y.1⁻¹ * d'⁻¹ := ⟨_, rfl⟩
    rw [← hT] at ht
    rw [← hT'] at ht'
    have hyd : y.1 * d * y.1⁻¹ = T * d := by
      rw [hT]
      group
    have hyd' : y.1 * d' * y.1⁻¹ = T' * d' := by
      rw [hT']
      group
    have hdD : d ∈ zGroup Ω := hd.1
    have hd'D : d' ∈ zGroup Ω := hd'.1
    have hT'G : T' ∈ zGroup Ω := by
      rw [hT']
      exact Subgroup.mul_mem _ (hNz.conj_mem d' hd'D y.1) (Subgroup.inv_mem _ hd'D)
    have hcomm : d * T' = T' * d := H.endHyp.zGroup_comm H.perp9 d hdD T' hT'G
    have hprod : (y.1 * d * y.1⁻¹) * (y.1 * d' * y.1⁻¹) = d * d' := by
      calc (y.1 * d * y.1⁻¹) * (y.1 * d' * y.1⁻¹) = y.1 * (d * d') * y.1⁻¹ := by group
        _ = y.1 * r.1 * y.1⁻¹ := by rw [hdd]
        _ = r.1 := hcon
        _ = d * d' := hdd
    have hTT : (T * T') * (d * d') = 1 * (d * d') := by
      calc (T * T') * (d * d') = T * (T' * d) * d' := by group
        _ = T * (d * T') * d' := by rw [hcomm]
        _ = (T * d) * (T' * d') := by group
        _ = (y.1 * d * y.1⁻¹) * (y.1 * d' * y.1⁻¹) := by rw [hyd, hyd']
        _ = d * d' := hprod
        _ = 1 * (d * d') := (one_mul _).symm
    have hTT1 : T * T' = 1 := mul_right_cancel hTT
    have hT'eq : T' = T⁻¹ := eq_inv_of_mul_eq_one_right hTT1
    exact ht' (by rw [hT'eq]; exact Subgroup.inv_mem _ ht)
  have hcjN : ∀ r ∈ N, (⟨y.1 * r.1 * y.1⁻¹, hNz.conj_mem r.1 r.2 y.1⟩ : zGroup Ω) ∈ N := by
    intro r hr
    obtain ⟨hrP, hrne, hrb⟩ := hr
    obtain ⟨J, hJ, hJr⟩ := hrP
    have hinvz : y.1⁻¹ * p₀.1 * y.1 = p₀.1 := by
      calc y.1⁻¹ * p₀.1 * y.1 = y.1⁻¹ * (y.1 * p₀.1 * y.1⁻¹) * y.1 := by rw [hyz]
        _ = p₀.1 := by group
    refine ⟨⟨conjSub y.1 J, H.endHyp.thmD.hyp.conjInvariant y.1 J hJ, hJr.conj y.1⟩, ?_, ?_⟩
    · intro h
      apply hrne
      apply Subtype.ext
      have h' : y.1 * r.1 * y.1⁻¹ = p₀.1 := congrArg Subtype.val h
      calc r.1 = y.1⁻¹ * (y.1 * r.1 * y.1⁻¹) * y.1 := by group
        _ = y.1⁻¹ * p₀.1 * y.1 := by rw [h']
        _ = p₀.1 := hinvz
    · have h5 := hbf.conj y.1 p₀ r p₀ ⟨y.1 * r.1 * y.1⁻¹, hNz.conj_mem r.1 r.2 y.1⟩ hyz.symm rfl
      rw [h5]
      exact hrb
  have hpN : ∀ r ∈ N, p₀ * r ∈ N := by
    intro r hr
    obtain ⟨hrP, hrne, hrb⟩ := hr
    obtain ⟨J, hJ, hJr⟩ := hrP
    have hrK : r.1 ∈ Subgroup.normalizer (K : Set G) :=
      (hbf.spec K hK p₀ hz₀ r).mp ((hbf.symm r p₀).trans hrb)
    have hJK : J ∉ twinSet Ω K := by
      rintro ⟨-, z', hz1, hz2⟩
      apply hrne
      apply Subtype.ext
      exact (hz2.eq hJr).symm.trans (hz₀.eq hz1).symm
    obtain ⟨M, hM, hMinv⟩ := H.exists_member_mul_of_normalizes hK hJ hz₀ hJr hJK hrK
    refine ⟨⟨M, hM, hMinv⟩, ?_, ?_⟩
    · intro h
      have h1 : r = 1 := mul_left_cancel (h.trans (mul_one p₀).symm)
      exact hJr.ne_one (by rw [h1]; rfl)
    · rw [hbf.mul_right, hbf.alt, hrb, add_zero]
  let f3 : ↥N → ↥N := fun r =>
    ⟨⟨y.1 * r.1.1 * y.1⁻¹, hNz.conj_mem r.1.1 r.1.2 y.1⟩, hcjN r.1 r.2⟩
  have hf3 : ∀ x : ↥N, f3^[3] x = x := by
    intro x
    show f3 (f3 (f3 x)) = x
    apply Subtype.ext
    apply Subtype.ext
    show y.1 * (y.1 * (y.1 * x.1.1 * y.1⁻¹) * y.1⁻¹) * y.1⁻¹ = x.1.1
    calc y.1 * (y.1 * (y.1 * x.1.1 * y.1⁻¹) * y.1⁻¹) * y.1⁻¹
        = (y.1 * y.1 * y.1) * x.1.1 * (y.1 * y.1 * y.1)⁻¹ := by group
      _ = x.1.1 := by rw [hyG3]; group
  have hfix3' : ∀ x : ↥N, f3 x ≠ x := by
    intro x hx
    apply hfix3 x.1 x.2
    exact congrArg (fun t : ↥N => t.1.1) hx
  let f2 : ↥N → ↥N := fun r => ⟨p₀ * r.1, hpN r.1 r.2⟩
  have hp₀sq : p₀ * p₀ = 1 := Subtype.ext (H.endHyp.zGroup_mul_self H.perp9 p₀.1 p₀.2)
  have hf2 : ∀ x : ↥N, f2^[2] x = x := by
    intro x
    show f2 (f2 x) = x
    apply Subtype.ext
    show p₀ * (p₀ * x.1) = x.1
    rw [← mul_assoc, hp₀sq, one_mul]
  have hfix2 : ∀ x : ↥N, f2 x ≠ x := by
    intro x hx
    have h1 : p₀ * x.1 = x.1 := congrArg Subtype.val hx
    have h2 : p₀ = 1 := mul_eq_right.mp h1
    exact hz₀.ne_one (congrArg Subtype.val h2)
  have h2 : 2 ∣ Nat.card ↥N := ae8i_dvd_of_fpf 2 f2 hf2 hfix2
  have h3 : 3 ∣ Nat.card ↥N := ae8i_dvd_of_fpf 3 f3 hf3 hfix3'
  rw [Nat.card_coe_set_eq] at h2 h3
  omega

namespace SectFrame

theorem card_perp_mul (H : End18.Hyp Ω) (hu : SectFrame Ω u) (c : Chart Ω u)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) {L : Subgroup G}
    (hL : L ∈ Generic.centMembers Ω u) (x : zGroup Ω) (hx : IsUniqueInvolution L x.1) :
    {p : zGroup Ω | p ∈ zPoints Ω ∧ bf (⟨u, hu.mem⟩ * x) p = 0}.ncard = 15 := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_mul H hu hL hx
  have hΩ := H.endHyp.thmD.hyp.conjInvariant
  have hN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩ
  have hpre : (fun r : zGroup Ω => (⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩ : zGroup Ω)) ⁻¹'
      {p : zGroup Ω | p ∈ zPoints Ω ∧ bf (⟨u, hu.mem⟩ * x) p = 0} =
      {r : zGroup Ω | r ∈ zPoints Ω ∧ bf ⟨u, hu.mem⟩ r = 0} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hb := hbf.conj g ⟨u, hu.mem⟩ r (⟨u, hu.mem⟩ * x)
      (⟨g * r.1 * g⁻¹, hN.conj_mem r.1 r.2 g⟩) hg.symm rfl
    rw [hb]
    exact and_congr (ae8i_zSet_conj_iff hΩ g r.1) Iff.rfl
  rw [← ae8i_conj_preimage_ncard hN g, hpre]
  have hPfin : (Generic.centMembers Ω u).Finite := Set.toFinite _
  have hTfin : {r : zGroup Ω | r ∈ zPoints Ω ∧ bf ⟨u, hu.mem⟩ r = 0}.Finite := Set.toFinite _
  have hPT : ∀ r : zGroup Ω, (r ∈ zPoints Ω ∧ bf ⟨u, hu.mem⟩ r = 0) ↔
      (r ∈ zPoints Ω ∧ ∃ R ∈ Generic.centMembers Ω u, IsUniqueInvolution R r.1) := by
    intro r
    constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr, (perp_iff H hu hbf r hr).mp h⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, (perp_iff H hu hbf r hr).mpr h⟩
  have hm : ∀ R ∈ hPfin.toFinset,
      (hTfin.toFinset.filter (fun p => IsUniqueInvolution R p.1)).card = 1 := by
    intro R hRmem
    have hR : R ∈ Generic.centMembers Ω u := (Set.Finite.mem_toFinset hPfin).mp hRmem
    obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hR.1
    have hzmem : z ∈ zGroup Ω := Subgroup.subset_closure ⟨R, hR.1, hz⟩
    rw [Finset.card_eq_one]
    refine ⟨⟨z, hzmem⟩, ?_⟩
    ext p
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hpT, hpR⟩
      apply Subtype.ext
      exact hpR.eq hz
    · rintro rfl
      refine ⟨?_, hz⟩
      exact (hPT _).mpr ⟨⟨R, hR.1, hz⟩, R, hR, hz⟩
  have hn : ∀ p ∈ hTfin.toFinset,
      (hPfin.toFinset.filter (fun R => IsUniqueInvolution R p.1)).card = 2 := by
    intro p hpmem
    have hpT : p ∈ {r : zGroup Ω | r ∈ zPoints Ω ∧ bf ⟨u, hu.mem⟩ r = 0} :=
      (Set.Finite.mem_toFinset hTfin).mp hpmem
    obtain ⟨-, R₀, hR₀P, hR₀p⟩ := (hPT p).mp hpT
    have hset : hPfin.toFinset.filter (fun R => IsUniqueInvolution R p.1) =
        (Set.toFinite (twinSet Ω R₀ ∩ Generic.centMembers Ω u)).toFinset := by
      ext R
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff]
      constructor
      · rintro ⟨hRP, hRp⟩
        exact ⟨⟨hRP.1, p.1, hR₀p, hRp⟩, hRP⟩
      · rintro ⟨⟨-, z, hR₀z, hRz⟩, hRP⟩
        refine ⟨hRP, ?_⟩
        rw [hR₀p.eq hR₀z]
        exact hRz
    rw [hset, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact SectData.ncard_twin H hu.toSectData R₀ hR₀P
  have hcard := Finset.card_mul_eq_card_mul
    (r := fun (R : Subgroup G) (p : zGroup Ω) => IsUniqueInvolution R p.1) hm hn
  have hPc : (Generic.centMembers Ω u).ncard = 30 := Chart.ncard_centMembers c
  rw [Set.ncard_eq_toFinset_card _ hPfin] at hPc
  rw [Set.ncard_eq_toFinset_card _ hTfin]
  omega

theorem six_dvd_card_nbr (H : End18.Hyp Ω) (hu : SectFrame Ω u) (c : Chart Ω u)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (z : zGroup Ω)
    (hz : z ∈ zPoints Ω) :
    6 ∣ {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ z ∧ bf z r = 0}.ncard := by
  obtain ⟨K, hK, s, hs, hsK, huK⟩ := hu.inD0
  obtain ⟨z₀, hz₀⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hz₀D : z₀ ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hz₀⟩
  obtain ⟨p₀, hp₀def⟩ : ∃ p₀ : zGroup Ω, p₀.1 = z₀ := ⟨⟨z₀, hz₀D⟩, rfl⟩
  have hp₀ : p₀ ∈ zPoints Ω := by
    show p₀.1 ∈ zSet Ω
    rw [hp₀def]
    exact ⟨K, hK, hz₀⟩
  rw [card_nbr_eq H hbf z p₀ hz hp₀]
  exact ae8i_six_dvd_main H hu c hbf p₀ hp₀ K hK (by rw [hp₀def]; exact hz₀) s hs hsK huK

end SectFrame

theorem ae8i_normalizer_iff (c : Chart Ω u) (H : End18.Hyp Ω) {L : Subgroup G}
    (hL : L ∈ Generic.centMembers Ω u) {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b)
    {d : G} (hdY : d ∈ pSpan (Generic.centMembers Ω u))
    (hperm : (c.ψ ⟨d, hdY⟩ : AE.Wr 6).perm = 1) :
    d ∈ Subgroup.normalizer (L : Set G) ↔
      Even (Finset.univ.filter fun i => i ∈ α ∧ (c.ψ ⟨d, hdY⟩ : AE.Wr 6).vec i ≠ 0).card := by
  classical
  have hLY : L ≤ pSpan (Generic.centMembers Ω u) := le_pSpan hL
  have hmemL : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      (y : G) ∈ L ↔ ((c.ψ y : AE.aeSub 6) : AE.Wr 6) ∈ AE.memAt α h b :=
    fun y => ae8c_mem_iff c hlab y
  set ψd : AE.Wr 6 := (c.ψ ⟨d, hdY⟩ : AE.Wr 6) with hψd
  set v : Fin 6 → ZMod 2 := ψd.vec with hv
  have hofv : AE.Wr.ofVec v = ψd := AE.Wr.ext rfl hperm.symm
  have hinv : ψd⁻¹ = ψd := by
    rw [← hofv]
    exact Chart.ae8b2_ofVec_inv v
  have hconjψ : ∀ (y : ↥(pSpan (Generic.centMembers Ω u)))
      (hy : d * (y : G) * d⁻¹ ∈ pSpan (Generic.centMembers Ω u)),
      (c.ψ ⟨d * (y : G) * d⁻¹, hy⟩ : AE.Wr 6) = ψd * (c.ψ y : AE.Wr 6) * ψd⁻¹ := by
    intro y hy
    have e : (⟨d * (y : G) * d⁻¹, hy⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
        ⟨d, hdY⟩ * y * (⟨d, hdY⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hE : ∀ a ∈ AE.memAt α h b, ψd * a * ψd⁻¹ ∈
      AE.memAt α h (if Even (Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0).card then b else !b) := by
    intro a ha
    have := ae8c_e2_memAt_conj v ha
    rwa [hofv] at this
  have hsq : ψd * ψd = 1 := by
    have h0 := mul_inv_cancel ψd
    rwa [hinv] at h0
  have hinvol : ∀ X : AE.Wr 6, ψd * (ψd * X * ψd⁻¹) * ψd⁻¹ = X := by
    intro X
    rw [hinv]
    calc ψd * (ψd * X * ψd) * ψd = (ψd * ψd) * X * (ψd * ψd) := by group
      _ = X := by rw [hsq, one_mul, mul_one]
  have hsurjL : ∀ a ∈ AE.memAt α h b,
      ∃ y : ↥(pSpan (Generic.centMembers Ω u)), (y : G) ∈ L ∧ (c.ψ y : AE.Wr 6) = a := by
    intro a ha
    rw [← hlab] at ha
    obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hza⟩
  constructor
  · intro hnorm
    have hpres : ∀ a ∈ AE.memAt α h b, ψd * a * ψd⁻¹ ∈ AE.memAt α h b := by
      intro a ha
      obtain ⟨y, hyL, hya⟩ := hsurjL a ha
      have hdy : d * (y : G) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hnorm (y : G)).mp hyL
      have hdyY : d * (y : G) * d⁻¹ ∈ pSpan (Generic.centMembers Ω u) := hLY hdy
      have h3 := (hmemL ⟨d * (y : G) * d⁻¹, hdyY⟩).mp hdy
      rw [hconjψ y hdyY, hya] at h3
      exact h3
    by_contra hodd
    have hpar : (if Even (Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0).card then b else !b) = !b :=
      if_neg hodd
    have hsub : AE.memAt α h b ≤ AE.memAt α h (!b) := by
      intro t ht
      have h4 := hE _ (hpres t ht)
      rw [hpar, hinvol] at h4
      exact h4
    have heq : AE.memAt α h b = AE.memAt α h (!b) :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (by rw [AE.natCard_memAt, AE.natCard_memAt]))
    have heq' : AE.memAt α h true = AE.memAt α h false := by
      cases b
      · exact heq.symm
      · exact heq
    exact AE.memBar_true_ne_false (by norm_num) α h (by unfold AE.memBar; rw [heq'])
  · intro heven
    have hpres : ∀ a ∈ AE.memAt α h b, ψd * a * ψd⁻¹ ∈ AE.memAt α h b := by
      intro a ha
      have h5 := hE a ha
      rwa [if_pos heven] at h5
    rw [Subgroup.mem_normalizer_iff]
    intro g'
    by_cases hg : g' ∈ pSpan (Generic.centMembers Ω u)
    · have hdg : d * g' * d⁻¹ ∈ pSpan (Generic.centMembers Ω u) :=
        mul_mem (mul_mem hdY hg) (inv_mem hdY)
      have h1 := hmemL ⟨g', hg⟩
      have h2 := hmemL ⟨d * g' * d⁻¹, hdg⟩
      rw [hconjψ ⟨g', hg⟩ hdg] at h2
      have hiff : (c.ψ ⟨g', hg⟩ : AE.Wr 6) ∈ AE.memAt α h b ↔
          ψd * (c.ψ ⟨g', hg⟩ : AE.Wr 6) * ψd⁻¹ ∈ AE.memAt α h b := by
        constructor
        · exact hpres _
        · intro hx
          have h6 := hpres _ hx
          rwa [hinvol] at h6
      exact h1.trans (hiff.trans h2.symm)
    · constructor
      · intro hgL
        exact absurd (hLY hgL) hg
      · intro hdgL
        exfalso
        apply hg
        have h7 := hLY hdgL
        have e : g' = d⁻¹ * (d * g' * d⁻¹) * d := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hdY) h7) hdY

theorem ae8i_basis_decide : ∀ v : Fin 6 → ZMod 2, (∑ i, v i = 0) →
    ∃ s0 s1 s2 s3 s4 : ZMod 2,
      v = s0 • Chart.ae8b2_ind {0, 1, 2, 3} + s1 • Chart.ae8b2_ind {0, 1, 2, 4} +
        s2 • Chart.ae8b2_ind {0, 1, 2, 5} + s3 • Chart.ae8b2_ind {0, 1, 3, 4} +
        s4 • Chart.ae8b2_ind {0, 2, 3, 4} := by
  decide +kernel

theorem ae8i_zmod2_eq : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide

theorem ae8i_zmod2_self : ∀ a : ZMod 2, a = a + a → a = 0 := by decide

theorem ae8i_zmod2_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

theorem ae8i_zmod2_cases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide

theorem ae8i_dot6_ind (v : Fin 6 → ZMod 2) (α : Finset (Fin 6)) :
    Polar.dot6 v (Chart.ae8b2_ind α) =
      ((Finset.univ.filter fun i => i ∈ α ∧ v i ≠ 0).card : ZMod 2) := by
  unfold Polar.dot6 Chart.ae8b2_ind
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ α
  · by_cases hv : v i = 0
    · simp [hi, hv]
    · simp [hi, hv, ae8i_zmod2_ne_zero (v i) hv]
  · simp [hi]

theorem ae8i_dot6_add (a b c : Fin 6 → ZMod 2) :
    Polar.dot6 a (b + c) = Polar.dot6 a b + Polar.dot6 a c := by
  unfold Polar.dot6
  simp [mul_add, Finset.sum_add_distrib]

theorem ae8i_dot6_zero (a : Fin 6 → ZMod 2) : Polar.dot6 a 0 = 0 := by
  unfold Polar.dot6
  simp

theorem ae8i_dot6_ones (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) :
    Polar.dot6 (fun _ => 1) v = 0 := by
  unfold Polar.dot6
  simpa using hv

theorem ae8i_mul_vec_of_perm (a b : AE.Wr 6) (ha : a.perm = 1) :
    (a * b).vec = a.vec + b.vec := by
  funext i
  rw [AE.Wr.mul_vec, ha]
  rfl

theorem ae8i_wt6_ind (α : Finset (Fin 6)) : Polar.wt6 (Chart.ae8b2_ind α) = α.card := by
  unfold Polar.wt6 Chart.ae8b2_ind
  congr 1
  ext i
  by_cases hi : i ∈ α <;> simp [hi]

theorem ae8i_exists_w (c : Chart Ω u) (H : End18.Hyp Ω) {α : Finset (Fin 6)}
    (hα : α.card = 4) :
    ∃ L ∈ Generic.centMembers Ω u,
      ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
        (AE.aeSub 6).subtype = AE.memAt α hα true ∧
      ∃ w : zGroup Ω, IsUniqueInvolution L w.1 ∧
        ∃ hw : (w : G) ∈ pSpan (Generic.centMembers Ω u),
          (c.ψ ⟨w.1, hw⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  obtain ⟨L, hL, hlab⟩ := c.label_surj α hα true
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hL.1
  have hzP : z ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hL hz.mem
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, hz⟩
  have hmem : (c.ψ ⟨z, hzP⟩ : AE.Wr 6) ∈ AE.memAt α hα true :=
    (ae8c_mem_iff c hlab ⟨z, hzP⟩).mp hz.mem
  have hsq : (c.ψ ⟨z, hzP⟩ : AE.Wr 6) * (c.ψ ⟨z, hzP⟩ : AE.Wr 6) = 1 := by
    have h1 : c.ψ (⟨z, hzP⟩ * ⟨z, hzP⟩) = 1 := by
      rw [show (⟨z, hzP⟩ : ↥(pSpan (Generic.centMembers Ω u))) * ⟨z, hzP⟩ = 1 from
        Subtype.ext hz.sq, map_one]
    rw [map_mul] at h1
    exact congrArg Subtype.val h1
  have hne : (c.ψ ⟨z, hzP⟩ : AE.Wr 6) ≠ 1 := by
    intro h
    have h1 : c.ψ ⟨z, hzP⟩ = 1 := Subtype.ext h
    have h2 : (⟨z, hzP⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 := by
      apply c.ψ.injective
      rw [h1, map_one]
    exact hz.ne_one (congrArg Subtype.val h2)
  rcases ae8c_memAt_invol hmem hsq with h1 | h1
  · exact absurd h1 hne
  · exact ⟨L, hL, hlab, ⟨z, hzD⟩, hz, hzP, h1⟩

theorem ae8i_bf_eq_dot (c : Chart Ω u) (H : End18.Hyp Ω) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) {L : Subgroup G} (hL : L ∈ Generic.centMembers Ω u)
    {α : Finset (Fin 6)} {h : α.card = 4}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h true)
    {w : zGroup Ω} (hw : IsUniqueInvolution L w.1)
    (x : zGroup Ω) (hxA : (x : G) ∈ pSpan (Generic.centMembers Ω u))
    (hperm : (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).perm = 1) :
    bf x w = Polar.dot6 (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).vec (Chart.ae8b2_ind α) := by
  have h1 := ae8i_normalizer_iff c H hL hlab hxA hperm
  rw [ae8i_dot6_ind]
  apply ae8i_zmod2_eq
  rw [hbf.spec L hL.1 w hw x, h1, ZMod.natCast_eq_zero_iff_even]

theorem ae8i_point_of_wt4 (c : Chart Ω u) (H : End18.Hyp Ω) (x : zGroup Ω)
    (hxA : (x : G) ∈ pSpan (Generic.centMembers Ω u))
    (hwt : Polar.wt6 (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).vec = 4) :
    ∃ L ∈ Generic.centMembers Ω u, IsUniqueInvolution L x.1 := by
  classical
  have hxD : (x : G) ∈ zGroup Ω := x.2
  have hperm : (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).perm = 1 :=
    (Chart.mem_zGroup_iff c H ⟨x.1, hxA⟩).mp hxD
  have hαcard : (Finset.univ.filter fun i => (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).vec i ≠ 0).card = 4 :=
    hwt
  obtain ⟨L, hL, -, w, hw, hwP, hψw⟩ := ae8i_exists_w c H hαcard
  have hvind : (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).vec = Chart.ae8b2_ind
      (Finset.univ.filter fun i => (c.ψ ⟨x.1, hxA⟩ : AE.Wr 6).vec i ≠ 0) :=
    ae8c_eq_indicator _
  have hwD : (w : G) ∈ zGroup Ω := w.2
  have hwperm : (c.ψ ⟨w.1, hwP⟩ : AE.Wr 6).perm = 1 :=
    (Chart.mem_zGroup_iff c H ⟨w.1, hwP⟩).mp hwD
  have hx_eq : c.ψ ⟨x.1, hxA⟩ = c.ψ ⟨w.1, hwP⟩ := by
    apply Subtype.ext
    apply AE.Wr.ext
    · rw [hψw]
      exact hvind.trans (congrArg AE.Wr.vec (Chart.ae8b2_zOf_eq hαcard)).symm
    · rw [hperm, hwperm]
  have hxw2 : (⟨x.1, hxA⟩ : ↥(pSpan (Generic.centMembers Ω u))) = ⟨w.1, hwP⟩ :=
    c.ψ.injective hx_eq
  have hxw : x.1 = w.1 := Subtype.mk.inj hxw2
  exact ⟨L, hL, by rw [hxw]; exact hw⟩

@[expose] def ae8iA (Ω : Set (Subgroup G)) (u : G) : Subgroup (zGroup Ω) :=
  (pSpan (Generic.centMembers Ω u)).comap (zGroup Ω).subtype

theorem ae8iA_mem {x : zGroup Ω} : x ∈ ae8iA Ω u ↔ (x : G) ∈ pSpan (Generic.centMembers Ω u) :=
  Iff.rfl

@[expose] def ae8iPt (x : ↥(ae8iA Ω u)) : ↥(pSpan (Generic.centMembers Ω u)) :=
  ⟨((x : zGroup Ω) : G), ae8iA_mem.mp x.2⟩

@[expose] def ae8iVec (c : Chart Ω u) (x : ↥(ae8iA Ω u)) : Fin 6 → ZMod 2 :=
  (c.ψ (ae8iPt x) : AE.Wr 6).vec

theorem ae8iPt_perm (H : End18.Hyp Ω) (c : Chart Ω u) (x : ↥(ae8iA Ω u)) :
    (c.ψ (ae8iPt x) : AE.Wr 6).perm = 1 :=
  (Chart.mem_zGroup_iff c H (ae8iPt x)).mp (x : zGroup Ω).2

theorem ae8iVec_mul (H : End18.Hyp Ω) (c : Chart Ω u) (x y : ↥(ae8iA Ω u)) :
    ae8iVec c (x * y) = ae8iVec c x + ae8iVec c y := by
  have e1 : ae8iPt (x * y) = ae8iPt x * ae8iPt y := Subtype.ext rfl
  unfold ae8iVec
  rw [e1, map_mul]
  exact ae8i_mul_vec_of_perm _ _ (ae8iPt_perm H c x)

theorem ae8iVec_one (c : Chart Ω u) : ae8iVec c 1 = 0 := by
  unfold ae8iVec
  rw [show ae8iPt (1 : ↥(ae8iA Ω u)) = 1 from Subtype.ext rfl, map_one]
  rfl

theorem ae8iVec_inj (H : End18.Hyp Ω) (c : Chart Ω u) {x y : ↥(ae8iA Ω u)}
    (h : ae8iVec c x = ae8iVec c y) : x = y := by
  have h1 : c.ψ (ae8iPt x) = c.ψ (ae8iPt y) :=
    Subtype.ext (AE.Wr.ext h ((ae8iPt_perm H c x).trans (ae8iPt_perm H c y).symm))
  have h2 : ae8iPt x = ae8iPt y := c.ψ.injective h1
  apply Subtype.ext
  apply Subtype.ext
  have h3 : ((ae8iPt x : ↥(pSpan (Generic.centMembers Ω u))) : G) =
      ((ae8iPt y : ↥(pSpan (Generic.centMembers Ω u))) : G) := congrArg Subtype.val h2
  exact h3

theorem ae8iVec_wsum (c : Chart Ω u) (x : ↥(ae8iA Ω u)) : ∑ i, ae8iVec c x i = 0 := by
  have := (AE.mem_aeSub.mp (c.ψ (ae8iPt x)).2).1
  unfold AE.Wr.wsum at this
  exact this

theorem ae8iVec_surj (H : End18.Hyp Ω) (c : Chart Ω u) (v : Fin 6 → ZMod 2)
    (hv : ∑ i, v i = 0) : ∃ x : ↥(ae8iA Ω u), ae8iVec c x = v := by
  obtain ⟨y, hyD, hyv⟩ := Chart.ae8b2_even c H v hv
  refine ⟨⟨⟨y.1, hyD⟩, ae8iA_mem.mpr y.2⟩, ?_⟩
  have e2 : ae8iPt (⟨⟨y.1, hyD⟩, ae8iA_mem.mpr y.2⟩ : ↥(ae8iA Ω u)) = y := Subtype.ext rfl
  unfold ae8iVec
  rw [e2, hyv]
  rfl

theorem ae8i_forall_A (H : End18.Hyp Ω) (c : Chart Ω u) (Q : ↥(ae8iA Ω u) → Prop)
    (hQ1 : Q 1) (hQmul : ∀ p q, Q p → Q q → Q (p * q))
    (hQw : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), ∃ w : ↥(ae8iA Ω u),
      Q w ∧ ae8iVec c w = Chart.ae8b2_ind α) (y : ↥(ae8iA Ω u)) : Q y := by
  obtain ⟨w0, hQ0, hv0⟩ := hQw {0, 1, 2, 3} (by decide)
  obtain ⟨w1, hQ1', hv1⟩ := hQw {0, 1, 2, 4} (by decide)
  obtain ⟨w2, hQ2, hv2⟩ := hQw {0, 1, 2, 5} (by decide)
  obtain ⟨w3, hQ3, hv3⟩ := hQw {0, 1, 3, 4} (by decide)
  obtain ⟨w4, hQ4, hv4⟩ := hQw {0, 2, 3, 4} (by decide)
  obtain ⟨s0, s1, s2, s3, s4, hdec⟩ := ae8i_basis_decide (ae8iVec c y) (ae8iVec_wsum c y)
  have hfac : ∀ (s : ZMod 2) (w : ↥(ae8iA Ω u)), Q w →
      ∃ f : ↥(ae8iA Ω u), ae8iVec c f = s • ae8iVec c w ∧ Q f := by
    intro s w hw
    rcases ae8i_zmod2_cases s with rfl | rfl
    · exact ⟨1, by rw [ae8iVec_one c, zero_smul], hQ1⟩
    · exact ⟨w, by rw [one_smul], hw⟩
  obtain ⟨f0, hf0v, hf0Q⟩ := hfac s0 w0 hQ0
  obtain ⟨f1, hf1v, hf1Q⟩ := hfac s1 w1 hQ1'
  obtain ⟨f2, hf2v, hf2Q⟩ := hfac s2 w2 hQ2
  obtain ⟨f3, hf3v, hf3Q⟩ := hfac s3 w3 hQ3
  obtain ⟨f4, hf4v, hf4Q⟩ := hfac s4 w4 hQ4
  have hty : ae8iVec c (f0 * f1 * f2 * f3 * f4) = ae8iVec c y := by
    rw [ae8iVec_mul H c, ae8iVec_mul H c, ae8iVec_mul H c, ae8iVec_mul H c, hf0v, hf1v, hf2v,
      hf3v, hf4v, hv0, hv1, hv2, hv3, hv4, hdec]
  have ht := ae8iVec_inj H c hty
  rw [← ht]
  exact hQmul _ _ (hQmul _ _ (hQmul _ _ (hQmul _ _ hf0Q hf1Q) hf2Q) hf3Q) hf4Q

theorem ae8i_witness (H : End18.Hyp Ω) (c : Chart Ω u) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) (x : ↥(ae8iA Ω u)) {α : Finset (Fin 6)} (hα : α.card = 4) :
    ∃ w : ↥(ae8iA Ω u), ae8iVec c w = Chart.ae8b2_ind α ∧
      bf (x : zGroup Ω) (w : zGroup Ω) = Polar.dot6 (ae8iVec c x) (Chart.ae8b2_ind α) := by
  obtain ⟨L, hL, hlab, w, hw, hwP, hψw⟩ := ae8i_exists_w c H hα
  refine ⟨⟨w, ae8iA_mem.mpr hwP⟩, ?_, ?_⟩
  · show (c.ψ ⟨w.1, hwP⟩ : AE.Wr 6).vec = _
    rw [hψw]
    exact congrArg AE.Wr.vec (Chart.ae8b2_zOf_eq hα)
  · exact ae8i_bf_eq_dot c H hbf hL hlab hw (x : zGroup Ω) (ae8iA_mem.mp x.2)
      (ae8iPt_perm H c x)

namespace Chart

theorem exists_cfg9 [Fact (EndHyp Ω)] [Fact (Perp9 Ω)] (H : End18.Hyp Ω) (hu : SectFrame Ω u)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    ∃ (a : ℕ) (A : Subgroup ↥(zGroup Ω)) (e : A →* Multiplicative (Fin 6 → ZMod 2))
      (hu' : u ∈ zGroup Ω),
      (∀ x : zGroup Ω, x ∈ A ↔ (x : G) ∈ pSpan (Generic.centMembers Ω u)) ∧
      Polar.Cfg9 bf (zPoints Ω) A e ⟨u, hu'⟩ a := by
  classical
  obtain ⟨c⟩ := exists_chart H hu.toSectData
  obtain ⟨K₀, hK₀, -⟩ := hu.inD0
  obtain ⟨z₀, hz₀⟩ := H.endHyp.exists_isUniqueInvolution hK₀
  have hz₀D : z₀ ∈ zGroup Ω := Subgroup.subset_closure ⟨K₀, hK₀, hz₀⟩
  obtain ⟨p₀, hp₀def⟩ : ∃ p₀ : zGroup Ω, p₀.1 = z₀ := ⟨⟨z₀, hz₀D⟩, rfl⟩
  have hp₀ : p₀ ∈ zPoints Ω := by
    show p₀.1 ∈ zSet Ω
    rw [hp₀def]
    exact ⟨K₀, hK₀, hz₀⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ,
      N = {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p₀ ∧ bf p₀ r = 0}.ncard := ⟨_, rfl⟩
  have hsix : 6 ∣ N₀ := by
    rw [hN₀]
    exact SectFrame.six_dvd_card_nbr H hu c hbf p₀ hp₀
  let e : ↥(ae8iA Ω u) →* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (ae8iVec c x)
      map_one' := by
        show Multiplicative.ofAdd (ae8iVec c 1) = 1
        rw [ae8iVec_one c]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (ae8iVec c (x * y)) =
          Multiplicative.ofAdd (ae8iVec c x) * Multiplicative.ofAdd (ae8iVec c y)
        rw [ae8iVec_mul H c]
        rfl }
  have e_inj : Function.Injective e := fun x y hxy =>
    ae8iVec_inj H c (congrArg Multiplicative.toAdd hxy)
  have e_range : ∀ x : Multiplicative (Fin 6 → ZMod 2), x ∈ e.range ↔ ∑ i, x.toAdd i = 0 := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ae8iVec_wsum c a
    · intro hx
      obtain ⟨a, ha⟩ := ae8iVec_surj H c x.toAdd hx
      refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
      show Multiplicative.ofAdd (ae8iVec c a) = x
      rw [ha]
      rfl
  have e_form : ∀ x y : ↥(ae8iA Ω u), bf (x : zGroup Ω) (y : zGroup Ω) =
      Polar.dot6 (e x).toAdd (e y).toAdd := by
    intro x y
    refine ae8i_forall_A H c (fun y => bf (x : zGroup Ω) (y : zGroup Ω) =
      Polar.dot6 (ae8iVec c x) (ae8iVec c y)) ?_ ?_ ?_ y
    · show bf (x : zGroup Ω) 1 = Polar.dot6 (ae8iVec c x) (ae8iVec c 1)
      rw [ae8iVec_one c, ae8i_dot6_zero]
      have h1 := hbf.mul_right (x : zGroup Ω) 1 1
      rw [mul_one] at h1
      exact ae8i_zmod2_self _ h1
    · intro p q hp hq
      have hp' : bf (x : zGroup Ω) (p : zGroup Ω) = Polar.dot6 (ae8iVec c x) (ae8iVec c p) := hp
      have hq' : bf (x : zGroup Ω) (q : zGroup Ω) = Polar.dot6 (ae8iVec c x) (ae8iVec c q) := hq
      show bf (x : zGroup Ω) ((p : zGroup Ω) * (q : zGroup Ω)) =
        Polar.dot6 (ae8iVec c x) (ae8iVec c (p * q))
      rw [hbf.mul_right, ae8iVec_mul H c, ae8i_dot6_add, hp', hq']
    · intro α hα
      obtain ⟨w, hwv, hwb⟩ := ae8i_witness H c hbf x hα
      refine ⟨w, ?_, hwv⟩
      show bf (x : zGroup Ω) (w : zGroup Ω) = Polar.dot6 (ae8iVec c x) (ae8iVec c w)
      rw [hwv]
      exact hwb
  have hsymp : Polar.SympForm bf :=
    { sq_eq_one := fun a => Subtype.ext (H.endHyp.zGroup_mul_self H.perp9 a.1 a.2)
      mul_left := hbf.mul_left
      mul_right := hbf.mul_right
      alt := hbf.alt
      nondeg := hbf.nondeg }
  let uA : ↥(ae8iA Ω u) := ⟨⟨u, hu.mem⟩, ae8iA_mem.mpr c.mem⟩
  have he_u : e uA = Multiplicative.ofAdd (fun _ => 1) := by
    show Multiplicative.ofAdd (ae8iVec c uA) = _
    have hpt : ae8iPt uA = ⟨u, c.mem⟩ := Subtype.ext rfl
    unfold ae8iVec
    rw [hpt, c.u_eq]
    rfl
  have perp_u : ∀ p : zGroup Ω, (p ∈ zPoints Ω ∧ bf ⟨u, hu.mem⟩ p = 0) ↔
      ∃ x : ↥(ae8iA Ω u), (x : zGroup Ω) = p ∧ Polar.wt6 (e x).toAdd = 4 := by
    intro p
    constructor
    · rintro ⟨hp, hb⟩
      obtain ⟨R, hR, hRp⟩ := (SectFrame.perp_iff H hu hbf p hp).mp hb
      have hpA : (p : G) ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hR hRp.mem
      refine ⟨⟨p, ae8iA_mem.mpr hpA⟩, rfl, ?_⟩
      obtain ⟨α, hα, b, hlab⟩ := c.label R hR
      obtain ⟨w, hwR, hwP, hψw⟩ := ae8c_exists_inv hR.1 hR c hlab
      have hwp : w = p.1 := hwR.eq hRp
      have hvec : ae8iVec c ⟨p, ae8iA_mem.mpr hpA⟩ = Chart.ae8b2_ind α := by
        unfold ae8iVec
        have e3 : ae8iPt (⟨p, ae8iA_mem.mpr hpA⟩ : ↥(ae8iA Ω u)) = ⟨w, hwP⟩ :=
          Subtype.ext hwp.symm
        rw [e3, hψw]
        exact congrArg AE.Wr.vec (Chart.ae8b2_zOf_eq hα)
      show Polar.wt6 (ae8iVec c ⟨p, ae8iA_mem.mpr hpA⟩) = 4
      rw [hvec, ae8i_wt6_ind, hα]
    · rintro ⟨x, rfl, hwt⟩
      have hwt' : Polar.wt6 (ae8iVec c x) = 4 := hwt
      obtain ⟨L, hL, hinv⟩ := ae8i_point_of_wt4 c H (x : zGroup Ω) (ae8iA_mem.mp x.2) hwt'
      have hpt : (x : zGroup Ω) ∈ zPoints Ω := ⟨L, hL.1, hinv⟩
      exact ⟨hpt, (SectFrame.perp_iff H hu hbf _ hpt).mpr ⟨L, hL, hinv⟩⟩
  have count_perp : ∀ x : ↥(ae8iA Ω u), (x : zGroup Ω) ∈ zPoints Ω →
      {p : zGroup Ω | p ∈ zPoints Ω ∧ bf (⟨u, hu.mem⟩ * (x : zGroup Ω)) p = 0}.ncard = 15 := by
    intro x hxS
    have hb : bf ⟨u, hu.mem⟩ (x : zGroup Ω) = 0 := by
      have h1 : bf ⟨u, hu.mem⟩ (x : zGroup Ω) = Polar.dot6 (fun _ => 1) (ae8iVec c x) := by
        have h2 := e_form uA x
        rw [he_u] at h2
        exact h2
      rw [h1, ae8i_dot6_ones _ (ae8iVec_wsum c x)]
    obtain ⟨x', hx', hw'⟩ := (perp_u _).mp ⟨hxS, hb⟩
    have hx'x : x' = x := Subtype.ext hx'
    have hwt : Polar.wt6 (ae8iVec c x) = 4 := by
      rw [← hx'x]
      exact hw'
    obtain ⟨L, hL, hinv⟩ := ae8i_point_of_wt4 c H (x : zGroup Ω) (ae8iA_mem.mp x.2) hwt
    exact SectFrame.card_perp_mul H hu c hbf hL (x : zGroup Ω) hinv
  have hpS : Polar.PointSet bf (zPoints Ω) (N₀ / 2) := by
    refine { one_notMem := ?_, mul_mem_of_orth := ?_, card_nbr := ?_ }
    · rintro ⟨K, hK, hK1⟩
      exact hK1.ne_one rfl
    · intro x hx y hy hxy hbxy
      obtain ⟨Kx, hKx, hKxx⟩ := hx
      obtain ⟨Ky, hKy, hKyy⟩ := hy
      have hyx : bf y x = 0 := (hbf.symm y x).trans hbxy
      have hbN : y.1 ∈ Subgroup.normalizer (Kx : Set G) := (hbf.spec Kx hKx x hKxx y).mp hyx
      have hJK : Ky ∉ twinSet Ω Kx := by
        rintro ⟨-, z, hz1, hz2⟩
        apply hxy
        apply Subtype.ext
        exact (hKxx.eq hz1).trans (hKyy.eq hz2).symm
      obtain ⟨M, hM, hMinv⟩ := H.exists_member_mul_of_normalizes hKx hKy hKxx hKyy hJK hbN
      exact ⟨M, hM, hMinv⟩
    · intro p hp
      have h1 := card_nbr_eq H hbf p p₀ hp hp₀
      rw [← hN₀] at h1
      have h2 : (Polar.nbr bf (zPoints Ω) p).ncard =
          {r : zGroup Ω | r ∈ zPoints Ω ∧ r ≠ p ∧ bf p r = 0}.ncard := rfl
      rw [h2, h1]
      omega
  refine ⟨N₀ / 2, ae8iA Ω u, e, hu.mem, fun x => ae8iA_mem, ?_⟩
  refine
    { symp := hsymp
      pointSet := hpS
      three_dvd := by omega
      gen := Subgroup.closure_closure_coe_preimage (k := zSet Ω)
      e_inj := e_inj
      e_range := e_range
      e_form := e_form
      mem := ae8iA_mem.mpr c.mem
      e_u := he_u
      perp_u := perp_u
      count_perp := count_perp }

theorem zGroup_inf_centralizer_eq (H : End18.Hyp Ω) (hu : SectFrame Ω u) :
    zGroup Ω ⊓ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) =
      Subgroup.zpowers u := by
  classical
  haveI : Fact (EndHyp Ω) := ⟨H.endHyp⟩
  haveI : Fact (Perp9 Ω) := ⟨H.perp9⟩
  obtain ⟨bf, hbf⟩ := H.exists_endForm
  obtain ⟨c⟩ := exists_chart H hu.toSectData
  obtain ⟨a, A, e, hu', hA, hcfg⟩ := exists_cfg9 H hu hbf
  obtain rfl : A = ae8iA Ω u := by
    ext x
    exact (hA x).trans ae8iA_mem.symm
  apply le_antisymm
  · rintro d ⟨hdD, hdC⟩
    have hx : ∀ L ∈ Generic.centMembers Ω u,
        (⟨d, hdD⟩ : zGroup Ω).1 ∈ Subgroup.normalizer (L : Set G) := by
      intro L hL
      apply ae8i_mem_normalizer_of_comm
      intro r hr
      exact ((Subgroup.mem_centralizer_iff.mp hdC) r (le_pSpan hL hr)).symm
    have hperp : ∀ y : ↥(ae8iA Ω u), bf ⟨d, hdD⟩ (y : zGroup Ω) = 0 := by
      intro y
      refine ae8i_forall_A H c (fun y => bf ⟨d, hdD⟩ (y : zGroup Ω) = 0) ?_ ?_ ?_ y
      · show bf ⟨d, hdD⟩ 1 = 0
        have h1 := hbf.mul_right (⟨d, hdD⟩ : zGroup Ω) 1 1
        rw [mul_one] at h1
        exact ae8i_zmod2_self _ h1
      · intro p q hp hq
        have hp' : bf ⟨d, hdD⟩ (p : zGroup Ω) = 0 := hp
        have hq' : bf ⟨d, hdD⟩ (q : zGroup Ω) = 0 := hq
        show bf ⟨d, hdD⟩ ((p : zGroup Ω) * (q : zGroup Ω)) = 0
        rw [hbf.mul_right, hp', hq', add_zero]
      · intro α hα
        obtain ⟨L, hL, hlab, w, hw, hwP, hψw⟩ := ae8i_exists_w c H hα
        refine ⟨⟨w, ae8iA_mem.mpr hwP⟩, ?_, ?_⟩
        · exact (hbf.spec L hL.1 w hw _).mpr (hx L hL)
        · show (c.ψ ⟨w.1, hwP⟩ : AE.Wr 6).vec = _
          rw [hψw]
          exact congrArg AE.Wr.vec (Chart.ae8b2_zOf_eq hα)
    rcases Polar.Cfg9.ker_le hcfg ⟨d, hdD⟩ hperp with h | h
    · rw [show d = 1 from congrArg Subtype.val h]
      exact Subgroup.one_mem _
    · rw [show d = u from congrArg Subtype.val h]
      exact Subgroup.mem_zpowers u
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hu.mem, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun L hL => hL.2) hh)

theorem card_zGroup_eq_64 (H : End18.Hyp Ω) : Nat.card ↥(zGroup Ω) = 64 := by
  obtain ⟨u₀, hu₀⟩ := exists_sectFrame H
  obtain ⟨c⟩ := exists_chart H hu₀.toSectData
  obtain ⟨θ, hθv, hθc⟩ := exists_vecAct c H
  have hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u₀) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u₀ := fun d hd hcd => by
    have h1 : d ∈ zGroup Ω ⊓
        Subgroup.centralizer ((pSpan (Generic.centMembers Ω u₀) : Subgroup G) : Set G) :=
      ⟨hd, hcd⟩
    rw [zGroup_inf_centralizer_eq H hu₀] at h1
    exact h1
  apply le_antisymm
  · exact ae8b2_card_le c H θ hθv (fun d hd => ae8b2_ker_sub c H hC θ hθc d hd)
  · exact ae8b2_card_ge H

end Chart

end FrameCert

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
