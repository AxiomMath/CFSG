module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8B

public section

namespace CFSG.KC.O8Quat

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution

variable {G : Type} [Group G]

theorem starRel_symm {H K A B : Subgroup G} (h : Vtx.StarRel H K A B) : Vtx.StarRel H K B A := by
  obtain ⟨hA, hB, hne, h⟩ := h
  exact ⟨hB, hA, Ne.symm hne, h.symm⟩

theorem exists_conj_of_norm {A B : Subgroup G} (g : G)
    (h : ∃ u ∈ B, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (A : Set G)) :
    ∃ u ∈ conjSub g B, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (conjSub g A : Set G) := by
  obtain ⟨u, hu, ho, hn⟩ := h
  refine ⟨g * u * g⁻¹, conj_mem_conjSub hu, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho]
  · rw [Asc77.mem_normalizer_iff_conjSub_eq] at hn ⊢
    rw [← conjSub_mul, inv_mul_cancel_right, conjSub_mul, hn]

theorem starRel_conj {H K A B : Subgroup G} {g : G} (hg : g ∈ H) (h : Vtx.StarRel H K A B) :
    Vtx.StarRel H K (conjSub g A) (conjSub g B) := by
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne, h⟩ := h
  refine ⟨⟨g * a, H.mul_mem hg ha, (conjSub_mul g a K).symm⟩,
    ⟨g * b, H.mul_mem hg hb, (conjSub_mul g b K).symm⟩,
    fun e => hne (conjSub_injective g e), ?_⟩
  rcases h with h | h
  · exact Or.inl (exists_conj_of_norm g h)
  · exact Or.inr (exists_conj_of_norm g h)

theorem reflTransGen_conj {H K A B : Subgroup G} {g : G} (hg : g ∈ H)
    (h : Relation.ReflTransGen (Vtx.StarRel H K) A B) :
    Relation.ReflTransGen (Vtx.StarRel H K) (conjSub g A) (conjSub g B) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (starRel_conj hg hbc)

theorem reflTransGen_symm {H K A B : Subgroup G}
    (h : Relation.ReflTransGen (Vtx.StarRel H K) A B) :
    Relation.ReflTransGen (Vtx.StarRel H K) B A := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (starRel_symm hbc) ih

theorem reflTransGen_of_closure {H K : Subgroup G} {S : Set G} (hS : Subgroup.closure S = H)
    (h : ∀ s ∈ S, Relation.ReflTransGen (Vtx.StarRel H K) K (conjSub s K)) {g : G} (hg : g ∈ H) :
    Relation.ReflTransGen (Vtx.StarRel H K) K (conjSub g K) := by
  rw [← hS] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rw [conjSub_one]
  | mul x y hx hy ihx ihy =>
    rw [conjSub_mul]
    exact ihx.trans (reflTransGen_conj (hS ▸ hx) ihy)
  | inv x hx ih =>
    have e := reflTransGen_conj (H.inv_mem (hS ▸ hx)) ih
    rw [conjSub_inv_conjSub] at e
    exact reflTransGen_symm e

theorem reflTransGen_of_norm {H K : Subgroup G} {g : G} (hg : g ∈ H)
    (h : g ∈ Subgroup.normalizer (K : Set G) ∨
      ∃ v ∈ K, orderOf v = 4 ∧ g * v * g⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    Relation.ReflTransGen (Vtx.StarRel H K) K (conjSub g K) := by
  by_cases he : conjSub g K = K
  · rw [he]
  rcases h with hn | ⟨v, hv, ho, hn⟩
  · exact absurd (Asc77.mem_normalizer_iff_conjSub_eq.1 hn) he
  · refine .single ⟨⟨1, H.one_mem, (conjSub_one K).symm⟩, ⟨g, hg, rfl⟩, fun e => he e.symm,
      Or.inl ⟨g * v * g⁻¹, conj_mem_conjSub hv, ?_, hn⟩⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho]

theorem mem_normalizer_closure_pair [Finite G] {i j h : G}
    (hi : h * i * h⁻¹ ∈ Subgroup.closure ({i, j} : Set G))
    (hj : h * j * h⁻¹ ∈ Subgroup.closure ({i, j} : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.closure ({i, j} : Set G) : Set G) := by
  rw [Asc77.mem_normalizer_iff_conjSub_eq]
  have hle : conjSub h (Subgroup.closure ({i, j} : Set G)) ≤ Subgroup.closure ({i, j} : Set G) := by
    unfold conjSub
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact hi
    · exact hj
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Vtx.natCard_conjSub])

theorem isPGroup_biSup {ι : Type*} [DecidableEq ι] {p : ℕ} [Fact p.Prime] (F : ι → Subgroup G) :
    ∀ s : Finset ι, (∀ i ∈ s, IsPGroup p (F i)) →
    (∀ i ∈ s, ∀ j ∈ s, F i = F j ∨ ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x) →
    IsPGroup p ↥(⨆ i ∈ s, F i) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    have e : (⨆ i ∈ (∅ : Finset ι), F i) = ⊥ := by simp
    rw [e]
    exact IsPGroup.of_bot
  | insert a s _ ih =>
    intro hp hc
    rw [Finset.iSup_insert]
    have ih' := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    by_cases he : ∃ j ∈ s, F a = F j
    · obtain ⟨j, hj, e⟩ := he
      rw [sup_eq_right.2 (e ▸ le_iSup₂ (f := fun i (_ : i ∈ s) => F i) j hj)]
      exact ih'
    · simp only [not_exists, not_and] at he
      refine (hp a (Finset.mem_insert_self a s)).to_sup_of_normal_right' ih' fun x hx => ?_
      have hle : (⨆ i ∈ s, F i) ≤ Subgroup.centralizer (F a : Set G) := by
        refine iSup₂_le fun j hj y hy => Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        rcases hc a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) with h | h
        · exact absurd h (he j hj)
        · exact h z hz y hy
      have hcen : ∀ m ∈ ⨆ i ∈ s, F i, x * m = m * x := fun m hm =>
        Subgroup.mem_centralizer_iff.1 (hle hm) x hx
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · intro hm
        have e : x * m * x⁻¹ = m := by rw [hcen m hm, mul_inv_cancel_right]
        rw [e]
        exact hm
      · intro hm
        have e := hcen _ hm
        rw [inv_mul_cancel_right] at e
        have e' : x * m * x⁻¹ = m := mul_left_cancel e
        rw [e'] at hm
        exact hm

theorem datum_conj_of_normalizes {H K : Subgroup G} {s : G} (hd : Vtx.AmbientQuatDatum H K s)
    {g : G} (hg : ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H) :
    Vtx.AmbientQuatDatum H (conjSub g K) (g * s * g⁻¹) := by
  obtain ⟨e⟩ := hd.q8
  refine ⟨fun x hx => ?_, ⟨(K.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩, hd.inv.conj g, fun c hc hcs => ?_⟩
  · rw [mem_conjSub_iff] at hx
    have h1 := (hg _).1 (hd.le hx)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  · have hc' : g⁻¹ * c * g ∈ H := by
      rw [hg]
      rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group]
    have hcs' : g⁻¹ * c * g * s = s * (g⁻¹ * c * g) := by
      calc g⁻¹ * c * g * s = g⁻¹ * (c * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * c) * g := by rw [hcs]
        _ = s * (g⁻¹ * c * g) := by group
    have he : conjSub c (conjSub g K) = conjSub g (conjSub (g⁻¹ * c * g) K) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [he]
    rcases hd.twins _ hc' hcs' with h | h
    · left
      rw [h]
    · right
      intro x hx y hy
      rw [mem_conjSub_iff] at hx hy
      have h2 := h _ hx _ hy
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
        _ = y * x := by group

theorem datum_le_centralizer {H K : Subgroup G} {s : G} (hd : Vtx.AmbientQuatDatum H K s) :
    K ≤ Subgroup.centralizer {s} := fun x hx => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : x * s * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hx hd.inv.mem) (K.inv_mem hx)
  have hsq : x * s * x⁻¹ * (x * s * x⁻¹) = 1 := by
    calc x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [hd.inv.sq]; group
  rcases hd.inv.unique _ hmem hsq with h1 | h1
  · exfalso
    apply hd.inv.ne_one
    calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · calc x * s = (x * s * x⁻¹) * x := by group
      _ = s * x := by rw [h1]

theorem datum_isPGroup {H K : Subgroup G} {s : G} (hd : Vtx.AmbientQuatDatum H K s) :
    IsPGroup 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hd.q8
  refine IsPGroup.of_card (n := 3) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] <;> decide

theorem le_of_twins [Finite G] {H K S : Subgroup G} {s : G} (hd : Vtx.AmbientQuatDatum H K s)
    (hS : S ≤ H ⊓ Subgroup.centralizer {s}) (hSp : IsPGroup 2 S)
    (hQ : ∀ Q : Subgroup G, S ≤ Q → IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer {s} →
      Nat.card Q ≤ Nat.card S) :
    K ≤ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ := Fintype.ofFinite G
  set T : Finset G := Finset.univ.filter (· ∈ S) with hTdef
  have hT : ∀ c, c ∈ T ↔ c ∈ S := fun c => by simp [hTdef]
  set N : Subgroup G := ⨆ c ∈ T, conjSub c K with hN
  have hKs := datum_le_centralizer hd
  have hF : ∀ c ∈ S, conjSub c K ≤ H ⊓ Subgroup.centralizer {s} := by
    intro c hc x hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨hcH, hcs⟩ := Subgroup.mem_inf.1 (hS hc)
    rw [Subgroup.mem_centralizer_singleton_iff] at hcs
    have hy := Subgroup.mem_centralizer_singleton_iff.1 (hKs hx)
    have hcs2 : c * s * c⁻¹ = s := by rw [hcs]; group
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [show x = c * (c⁻¹ * x * c) * c⁻¹ by group]
      exact H.mul_mem (H.mul_mem hcH (hd.le hx)) (H.inv_mem hcH)
    · calc x * s = c * (c⁻¹ * x * c) * c⁻¹ * (c * s * c⁻¹) := by rw [hcs2]; group
        _ = c * ((c⁻¹ * x * c) * s) * c⁻¹ := by group
        _ = c * (s * (c⁻¹ * x * c)) * c⁻¹ := by rw [hy]
        _ = (c * s * c⁻¹) * x := by group
        _ = s * x := by rw [hcs2]
  have hpair : ∀ a ∈ T, ∀ b ∈ T, conjSub a K = conjSub b K ∨
      ∀ x ∈ conjSub a K, ∀ y ∈ conjSub b K, x * y = y * x := by
    intro a ha b hb
    rw [hT] at ha hb
    have hab : a⁻¹ * b ∈ S := S.mul_mem (S.inv_mem ha) hb
    obtain ⟨hH, hc⟩ := Subgroup.mem_inf.1 (hS hab)
    rcases hd.twins _ hH (Subgroup.mem_centralizer_singleton_iff.1 hc) with h | h
    · left
      rw [show b = a * (a⁻¹ * b) by group, conjSub_mul, h]
    · right
      intro x hx y hy
      rw [mem_conjSub_iff] at hx hy
      have hy' : a⁻¹ * y * a ∈ conjSub (a⁻¹ * b) K := by
        rw [mem_conjSub_iff]
        rwa [show (a⁻¹ * b)⁻¹ * (a⁻¹ * y * a) * (a⁻¹ * b) = b⁻¹ * y * b by group]
      have e := h _ hx _ hy'
      calc x * y = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by rw [e]
        _ = y * x := by group
  have hKp := datum_isPGroup hd
  have hNp : IsPGroup 2 N := isPGroup_biSup _ T (fun c _ => by unfold conjSub; exact hKp.map _)
    hpair
  have hNle : N ≤ H ⊓ Subgroup.centralizer {s} := iSup₂_le fun c hc => hF c ((hT c).1 hc)
  have hconj : ∀ c ∈ S, ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
    intro c hc x hx
    have hle : N ≤ N.comap (MulAut.conj c).toMonoidHom := by
      refine iSup₂_le fun d hd' y hy => ?_
      rw [Subgroup.mem_comap]
      have hy' : (MulAut.conj c).toMonoidHom y ∈ conjSub (c * d) K := by
        rw [conjSub_mul]
        exact Subgroup.mem_map_of_mem _ hy
      exact le_iSup₂ (f := fun i (_ : i ∈ T) => conjSub i K) (c * d)
        ((hT _).2 (S.mul_mem hc ((hT d).1 hd'))) hy'
    have h1 := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hSn : S ≤ Subgroup.normalizer (N : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj c hc x hx, fun hx => ?_⟩
    have h1 := hconj c⁻¹ (S.inv_mem hc) _ hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h1
  have hQp : IsPGroup 2 ↥(S ⊔ N) := hSp.to_sup_of_normal_right' hNp hSn
  have heq : S = S ⊔ N :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hQ _ le_sup_left hQp (sup_le hS hNle))
  have hKN : K ≤ N := by
    have h1 := le_iSup₂ (f := fun i (_ : i ∈ T) => conjSub i K) 1 ((hT 1).2 S.one_mem)
    rwa [conjSub_one] at h1
  exact hKN.trans (le_sup_right.trans heq.symm.le)

theorem conj_mem_inv {Ls : List (Subgroup G)} {g : G} (hg : ∀ L ∈ Ls, conjSub g L ∈ Ls) :
    ∀ L ∈ Ls, conjSub g⁻¹ L ∈ Ls := by
  classical
  intro L hL
  have hsub : Ls.toFinset.image (conjSub g) ⊆ Ls.toFinset := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact List.mem_toFinset.2 (hg y (List.mem_toFinset.1 hy))
  have heq : Ls.toFinset.image (conjSub g) = Ls.toFinset :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ (conjSub_injective g)])
  have hL' : L ∈ Ls.toFinset.image (conjSub g) := by
    rw [heq]
    exact List.mem_toFinset.2 hL
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hL'
  rw [conjSub_inv_conjSub]
  exact List.mem_toFinset.1 hy

theorem conj_mem_of_closure {S : Set G} {Ls : List (Subgroup G)}
    (hS : ∀ s ∈ S, ∀ L ∈ Ls, conjSub s L ∈ Ls) {h : G} (hh : h ∈ Subgroup.closure S) :
    ∀ L ∈ Ls, conjSub h L ∈ Ls := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    intro L hL
    rw [conjSub_one]
    exact hL
  | mul x y _ _ hx hy =>
    intro L hL
    rw [conjSub_mul]
    exact hx _ (hy L hL)
  | inv x _ hx => exact conj_mem_inv hx

theorem card_le_of_conj_mem [Finite G] {H N K : Subgroup G} (Ls : List (Subgroup G))
    (hL : ∀ h ∈ H, conjSub h K ∈ Ls) (hN : ∀ h ∈ H, conjSub h K = K → h ∈ N) :
    Nat.card H ≤ Ls.length * Nat.card N := by
  classical
  let rep : Subgroup G → G := fun L => if hL : ∃ h ∈ H, conjSub h K = L then hL.choose else 1
  have hrep : ∀ h ∈ H, rep (conjSub h K) ∈ H ∧ conjSub (rep (conjSub h K)) K = conjSub h K := by
    intro h hh
    have hex : ∃ h' ∈ H, conjSub h' K = conjSub h K := ⟨h, hh, rfl⟩
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  have hmem : ∀ h : H, (rep (conjSub h.1 K))⁻¹ * h.1 ∈ N := fun h => by
    obtain ⟨hr, e⟩ := hrep _ h.2
    set r := rep (conjSub h.1 K)
    exact hN _ (H.mul_mem (H.inv_mem hr) h.2) (by rw [conjSub_mul, ← e, conjSub_inv_conjSub])
  let f : H → Fin Ls.length × N := fun h =>
    (⟨Ls.idxOf (conjSub h.1 K), List.idxOf_lt_length_iff.2 (hL _ h.2)⟩, ⟨_, hmem h⟩)
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have e1 : Ls.idxOf (conjSub a K) = Ls.idxOf (conjSub b K) :=
      congrArg (fun p : Fin Ls.length × N => (p.1 : ℕ)) e
    have e2 : (rep (conjSub a K))⁻¹ * a = (rep (conjSub b K))⁻¹ * b :=
      congrArg (fun p : Fin Ls.length × N => (p.2 : G)) e
    have e3 : conjSub a K = conjSub b K := (List.idxOf_inj (hL _ ha)).1 e1
    rw [e3] at e2
    exact Subtype.ext (mul_left_cancel e2)
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1

theorem exists_conj_eq_of_card [Finite G] {H N K : Subgroup G} {m : ℕ} (w : ℕ → G)
    (hw : ∀ k < m, w k ∈ H)
    (hinj : ∀ i < m, ∀ j < m, conjSub (w i) K = conjSub (w j) K → i = j)
    (hNH : N ≤ H) (hNK : ∀ n ∈ N, conjSub n K = K) (hcard : Nat.card H ≤ m * Nat.card N)
    {g : G} (hg : g ∈ H) : ∃ k < m, conjSub g K = conjSub (w k) K := by
  classical
  by_contra hne
  push Not at hne
  let c : Fin (m + 1) → G := fun i => if (i : ℕ) < m then w i else g
  have hc : ∀ i, c i ∈ H := fun i => by
    by_cases hi : (i : ℕ) < m
    · simp only [c, if_pos hi]
      exact hw _ hi
    · simp only [c, if_neg hi]
      exact hg
  let f : Fin (m + 1) × N → H := fun p => ⟨c p.1 * p.2, H.mul_mem (hc _) (hNH p.2.2)⟩
  have key : ∀ (i : Fin (m + 1)) (n : N), conjSub (c i * n) K = conjSub (c i) K := fun i n => by
    rw [conjSub_mul, hNK n n.2]
  have hf : Function.Injective f := by
    rintro ⟨i, n⟩ ⟨j, n'⟩ e
    have e1 : c i * n = c j * n' := congrArg Subtype.val e
    have e2 : conjSub (c i) K = conjSub (c j) K := by rw [← key i n, ← key j n', e1]
    have hij : i = j := by
      by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m
      · simp only [c, if_pos hi, if_pos hj] at e2
        exact Fin.ext (hinj _ hi _ hj e2)
      · simp only [c, if_pos hi, if_neg hj] at e2
        exact absurd e2.symm (hne _ hi)
      · simp only [c, if_neg hi, if_pos hj] at e2
        exact absurd e2 (hne _ hj)
      · exact Fin.ext (by omega)
    subst hij
    have hn : n = n' := Subtype.ext (mul_left_cancel e1)
    rw [hn]
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1
  have hpos : 0 < Nat.card N := Nat.card_pos
  nlinarith

end CFSG.KC.O8Quat

end
