module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
public import Certificates.Certificate550843

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Solomon73 Certificates.AE117
  Certificates.WsubMembersE64
open scoped Pointwise

section Lists

variable {n : ℕ}

private theorem indL_nil : indL ([] : List (Fin n)) = 0 := funext fun i => by simp [indL]

private theorem embedVec_vec4 (ι : Fin 4 ↪ Fin n) (s : List (Fin 4)) :
    embedVec ι (vec4 s) = indL (s.map ι) := by
  classical
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply]
    simp only [vec4, indL, List.mem_map, ι.injective.eq_iff, exists_eq_right]
  · rw [embedVec_of_not_mem ι _ hx]
    simp only [indL, List.mem_map]
    split_ifs with h2
    · obtain ⟨i, -, rfl⟩ := h2
      exact absurd ⟨i, rfl⟩ hx
    · rfl

private theorem embedPerm_swap (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    embedPerm ι (swap i j) = swap (ι i) (ι j) := by
  classical
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨k, rfl⟩ := hx
    rw [embedPerm_apply, ι.injective.map_swap]
  · rw [embedPerm_of_not_mem ι _ hx, swap_apply_of_ne_of_ne] <;> rintro rfl <;>
      exact hx ⟨_, rfl⟩

private theorem embed_mk (ι : Fin 4 ↪ Fin n) (s : List (Fin 4)) (σ : Perm (Fin 4)) :
    embed ι ⟨vec4 s, σ⟩ = ⟨indL (s.map ι), embedPerm ι σ⟩ :=
  Wr.ext (embedVec_vec4 ι s) rfl

private theorem embedPerm_d₁ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₁ = swap (ι 0) (ι 1) * swap (ι 2) (ι 3) := by
  rw [d₁, embedPerm_mul, embedPerm_swap, embedPerm_swap]

private theorem embedPerm_d₂ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₂ = swap (ι 0) (ι 2) * swap (ι 1) (ι 3) := by
  rw [d₂, embedPerm_mul, embedPerm_swap, embedPerm_swap]

private theorem embedPerm_d₃ (ι : Fin 4 ↪ Fin n) :
    embedPerm ι d₃ = swap (ι 0) (ι 3) * swap (ι 1) (ι 2) := by
  rw [d₃, embedPerm_mul, embedPerm_swap, embedPerm_swap]

private theorem memLC_eq (ι : Fin 4 ↪ Fin n) (b : Bool) :
    memLC (ι 0) (ι 1) (ι 2) (ι 3) b = (if b then kList else kStarList).map (embed ι) := by
  have h1 : embed ι 1 = ⟨indL [], 1⟩ := by rw [map_one, indL_nil]; rfl
  cases b <;>
    simp only [memLC, kList, kStarList, zQ, List.map_cons, List.map_nil, h1, embed_mk,
      embedPerm_d₁, embedPerm_d₂, embedPerm_d₃, embedPerm_one, Bool.false_eq_true, ↓reduceIte]

private theorem sort_eq (α : Finset (Fin n)) (h : α.card = 4) :
    α.sort (· ≤ ·) = [emb α h 0, emb α h 1, emb α h 2, emb α h 3] := by
  have hl : (α.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h]
  apply List.ext_getElem (by rw [hl]; rfl)
  intro i h1 _
  have hi : i < 4 := by rw [hl] at h1; exact h1
  interval_cases i <;> simp [emb, Finset.orderEmbOfFin_apply]

private theorem memAtL_eq (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memAtL α b = (if b then kList else kStarList).map (embed (emb α h)) := by
  rw [← memLC_eq, memAtL, sort_eq α h]

theorem mem_memAt_iff_mem_memAtL (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) (x : Wr n) :
    x ∈ memAt α h b ↔ x ∈ memAtL α b := by
  rw [memAtL_eq α h b]
  cases b <;> simp [memAt, memK, memKStar, mem_kQ, mem_kQStar]

end Lists

theorem memAt_le_Wsub (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) : memAt α h b ≤ Wsub := by
  cases b
  · exact (memKStar_le_aeSub _).trans aeSub_le_Wsub
  · exact (memK_le_aeSub _).trans aeSub_le_Wsub

private theorem isE64_map {K L : Type} [Group K] [Group L] {f : K →* L}
    (hf : Function.Injective f) {A : Subgroup K} (hA : IsE64 A) : IsE64 (A.map f) := by
  obtain ⟨hcomm, hsq, hcard⟩ := hA
  refine ⟨?_, ?_, by rw [Subgroup.card_map_of_injective hf, hcard]⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]

theorem conj_mem_normalizer {G : Type*} [Group G] {B B' : Subgroup G} {g y : G}
    (hB : ∀ x, x ∈ B' ↔ g⁻¹ * x * g ∈ B) (hy : y ∈ Subgroup.normalizer (B' : Set G)) :
    g⁻¹ * y * g ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro k
  have h := hy (g * k * g⁻¹)
  rw [hB, hB] at h
  have e1 : g⁻¹ * (g * k * g⁻¹) * g = k := by group
  have e2 : g⁻¹ * (y * (g * k * g⁻¹) * y⁻¹) * g = g⁻¹ * y * g * k * (g⁻¹ * y * g)⁻¹ := by group
  rwa [e1, e2] at h

section Cert


theorem checkWith_spec : e64B (a0List ()) = true ∧
    (∀ v : Fin 6 → ZMod 2, wsum (⟨v, 1⟩ : Wr 6) = 0 → permB ⟨v, 1⟩ = true) ∧
    (∀ i : Fin 5, permB ⟨0, swap i.castSucc i.succ⟩ = true) ∧ distinctB () = true ∧
    countB (a0List ()) = true := by
  have h := Certificates.certificate550843
  unfold wsubCheck checkWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem a0List_spec : (a0List ()).length = 64 ∧ (a0List ()).Nodup ∧
    (∀ a ∈ a0List (), ∀ b ∈ a0List (), a * b ∈ a0List () ∧ a * b = b * a) ∧
    ∀ a ∈ a0List (), a * a = 1 ∧ wsum a = 0 := by
  have h := checkWith_spec.1
  simp only [e64B, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem eq_of_forall_mem_iff {L₁ L₂ : Finset (Fin 6) × Bool} (h₁ : L₁.1.card = 4)
    (h₂ : L₂.1.card = 4) (h : ∀ z, z ∈ memAtL L₁.1 L₁.2 ↔ z ∈ memAtL L₂.1 L₂.2) : L₁ = L₂ := by
  have hd := checkWith_spec.2.2.2.1
  unfold distinctB at hd
  refine @of_decide_eq_true _ _ hd L₁ L₂ h₁ h₂ ?_
  rw [List.all_eq_true]
  exact fun x hx => decide_eq_true ((h x).mp hx)

end Cert

@[expose] def subOfList (A : List (Wr 6)) : Subgroup ↥Wsub :=
  Subgroup.closure {x | (x : Wr 6) ∈ A}

theorem mem_subOfList {A : List (Wr 6)} (hA : A ≠ []) (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    (hsq : ∀ a ∈ A, a * a = 1) {x : ↥Wsub} : x ∈ subOfList A ↔ (x : Wr 6) ∈ A := by
  refine ⟨fun hx => ?_, fun hx => Subgroup.subset_closure hx⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil A hA
    have h := hmul a ha a ha
    rw [hsq a ha] at h
    exact h
  | mul y z _ _ hy hz => exact hmul _ hy _ hz
  | inv y _ hy =>
    show (y : Wr 6)⁻¹ ∈ A
    rw [inv_eq_of_mul_eq_one_right (hsq _ hy)]
    exact hy

@[expose] def ahat0 : Subgroup ↥Wsub := subOfList (a0List ())

theorem normB_iff (A : List (Wr 6)) (L : Finset (Fin 6) × Bool) :
    normB A L = true ↔ ∀ x ∈ memAtL L.1 L.2, ∀ a ∈ A, x * a * x⁻¹ ∈ A ∧ x⁻¹ * a * x ∈ A := by
  simp only [normB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]

section Cert


theorem mem_ahat0 {x : ↥Wsub} : x ∈ ahat0 ↔ (x : Wr 6) ∈ a0List () := by
  obtain ⟨hlen, -, hmc, hsq⟩ := a0List_spec
  exact mem_subOfList (List.ne_nil_of_length_pos (by omega)) (fun a ha b hb => (hmc a ha b hb).1)
    (fun a ha => (hsq a ha).1)

theorem card_ahat0 : Nat.card ahat0 = 64 := by
  obtain ⟨hlen, hnd, -, hsq⟩ := a0List_spec
  have e : ↥ahat0 ≃ {a : Wr 6 // a ∈ a0List ()} :=
    { toFun := fun x => ⟨((x : ↥Wsub) : Wr 6), mem_ahat0.mp x.2⟩
      invFun := fun a => ⟨⟨a.1, mem_Wsub.mpr (hsq a.1 a.2).2⟩, mem_ahat0.mpr a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (a0List ()).toFinset (fun _ => List.mem_toFinset),
    List.toFinset_card_of_nodup hnd, hlen]

theorem isE64_ahat0 : IsE64 ahat0 := by
  obtain ⟨-, -, hmc, hsq⟩ := a0List_spec
  exact ⟨fun a ha b hb => Subtype.ext ((hmc _ (mem_ahat0.mp ha) _ (mem_ahat0.mp hb)).2),
    fun a ha => Subtype.ext (hsq _ (mem_ahat0.mp ha)).1, card_ahat0⟩

theorem le_normalizer_ahat0_iff {L : Finset (Fin 6) × Bool} (h : L.1.card = 4) :
    (memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (ahat0 : Set ↥Wsub) ↔
      normB (a0List ()) L = true := by
  obtain ⟨-, -, -, hsq⟩ := a0List_spec
  rw [normB_iff]
  constructor
  · intro hle x hx a ha
    have hxM : x ∈ memAt L.1 h L.2 := (mem_memAt_iff_mem_memAtL _ h _ x).mpr hx
    have hxN : (⟨x, memAt_le_Wsub _ h _ hxM⟩ : ↥Wsub) ∈ Subgroup.normalizer (ahat0 : Set ↥Wsub) :=
      hle (Subgroup.mem_subgroupOf.mpr hxM)
    have haA : (⟨a, mem_Wsub.mpr (hsq a ha).2⟩ : ↥Wsub) ∈ ahat0 := mem_ahat0.mpr ha
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp haA
    have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) _).mp haA
    rw [inv_inv] at h2
    exact ⟨mem_ahat0.mp h1, mem_ahat0.mp h2⟩
  · intro hN y hy
    rw [Subgroup.mem_subgroupOf, mem_memAt_iff_mem_memAtL] at hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => mem_ahat0.mpr (hN _ hy _ (mem_ahat0.mp ha)).1, fun ha => ?_⟩
    have h1 := (hN _ hy _ (mem_ahat0.mp ha)).2
    have e : (y : Wr 6)⁻¹ * ((y * a * y⁻¹ : ↥Wsub) : Wr 6) * (y : Wr 6) = (a : Wr 6) := by
      push_cast
      group
    rw [e] at h1
    exact mem_ahat0.mpr h1

theorem ncard_ahat0 :
    {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
      (memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (ahat0 : Set ↥Wsub)}.ncard = 6 := by
  have hset : {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
      (memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (ahat0 : Set ↥Wsub)} =
      ↑(Finset.univ.filter fun L : Finset (Fin 6) × Bool =>
        L.1.card = 4 ∧ normB (a0List ()) L = true) := by
    ext L
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h, hle⟩ => ⟨h, (le_normalizer_ahat0_iff h).mp hle⟩,
      fun ⟨h, hN⟩ => ⟨h, (le_normalizer_ahat0_iff h).mpr hN⟩⟩
  rw [hset, Set.ncard_coe_finset]
  have hc := checkWith_spec.2.2.2.2
  unfold countB at hc
  exact @of_decide_eq_true _ _ hc

end Cert

@[expose] def PermMem (g : Wr 6) : Prop :=
  ∀ L : Finset (Fin 6) × Bool, L.1.card = 4 → ∃ L' : Finset (Fin 6) × Bool, L'.1.card = 4 ∧
    ∀ z : Wr 6, z ∈ memAtL L'.1 L'.2 ↔ g * z * g⁻¹ ∈ memAtL L.1 L.2

theorem permMem_one : PermMem 1 := fun L hL => ⟨L, hL, fun z => by simp⟩

theorem PermMem.mul {g h : Wr 6} (hg : PermMem g) (hh : PermMem h) : PermMem (g * h) := by
  intro L hL
  obtain ⟨L₁, hL₁, h₁⟩ := hg L hL
  obtain ⟨L₂, hL₂, h₂⟩ := hh L₁ hL₁
  refine ⟨L₂, hL₂, fun z => ?_⟩
  rw [h₂ z, h₁ (h * z * h⁻¹), mul_inv_rev]
  simp only [mul_assoc]

theorem permMem_of_permB {s : Wr 6} (hs : permB s = true) : PermMem s := by
  unfold permB at hs
  have h0 : ∀ L : Finset (Fin 6) × Bool, L.1.card = 4 →
      ∃ L' : Finset (Fin 6) × Bool, L'.1.card = 4 ∧ conjToB s L L' = true :=
    @of_decide_eq_true _ _ hs
  intro L hL
  obtain ⟨L', hL', h⟩ := h0 L hL
  simp only [conjToB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨L', hL', fun z => ⟨h1 z, fun hz => ?_⟩⟩
  have h3 := h2 _ hz
  rwa [show s⁻¹ * (s * z * s⁻¹) * s = z by group] at h3

section Cert


theorem permMem_perm (σ : Perm (Fin 6)) : PermMem ⟨0, σ⟩ := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact permMem_of_permB (checkWith_spec.2.2.1 i)
  | one => exact permMem_one
  | mul x y _ _ hx hy =>
    have e : (⟨0, x * y⟩ : Wr 6) = ⟨0, x⟩ * ⟨0, y⟩ :=
      Wr.ext (funext fun i => by simp [mul_vec]) rfl
    rw [e]
    exact hx.mul hy

theorem permMem_of_mem_Wsub {g : Wr 6} (hg : g ∈ Wsub) : PermMem g := by
  have e : g = ⟨g.vec, 1⟩ * ⟨0, g.perm⟩ :=
    Wr.ext (funext fun i => by simp [mul_vec]) (by simp [mul_perm])
  rw [e]
  exact (permMem_of_permB (checkWith_spec.2.1 g.vec hg)).mul (permMem_perm g.perm)

theorem ncard_le_of_conj (g : ↥Wsub) {B B' : Subgroup ↥Wsub}
    (hB : ∀ x, x ∈ B' ↔ g⁻¹ * x * g ∈ B) :
    {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
        (memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (B' : Set ↥Wsub)}.ncard ≤
      {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
        (memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (B : Set ↥Wsub)}.ncard := by
  have hg : ∀ L : Finset (Fin 6) × Bool, L.1.card = 4 →
      ∃ L' : Finset (Fin 6) × Bool, L'.1.card = 4 ∧ ∀ z : Wr 6,
        z ∈ memAtL L'.1 L'.2 ↔ (g : Wr 6) * z * (g : Wr 6)⁻¹ ∈ memAtL L.1 L.2 :=
    permMem_of_mem_Wsub g.2
  choose! f hfL hfz using hg
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_
  · rintro L ⟨h, hle⟩
    refine ⟨hfL L h, fun y hy => ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_memAt_iff_mem_memAtL] at hy
    have h1 : g * y * g⁻¹ ∈ (memAt L.1 h L.2).subgroupOf Wsub := by
      rw [Subgroup.mem_subgroupOf, mem_memAt_iff_mem_memAtL]
      exact (hfz L h _).mp hy
    have h2 := conj_mem_normalizer hB (hle h1)
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h2
  · rintro L₁ ⟨h₁, -⟩ L₂ ⟨h₂, -⟩ he
    refine eq_of_forall_mem_iff h₁ h₂ fun y => ?_
    have e : (g : Wr 6) * ((g : Wr 6)⁻¹ * y * (g : Wr 6)) * (g : Wr 6)⁻¹ = y := by group
    rw [← e, ← hfz L₁ h₁, ← hfz L₂ h₂, he]

theorem exists_conj_ahat0 (P A : Subgroup ↥Wsub) (hP : Nat.card P = 512)
    (huniq : ∀ A' ≤ P, IsE64 A' → A' = A) :
    ∃ g : ↥Wsub, ∀ x, x ∈ A ↔ g⁻¹ * x * g ∈ ahat0 := by
  have hE := isE64_ahat0
  have hidx : ¬ 2 ∣ P.index := by
    intro h2
    have h := Subgroup.card_mul_index P
    rw [hP, card_Wsub] at h
    omega
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 9) (by rw [hP]; norm_num)
  have hA02 : IsPGroup 2 ahat0 := IsPGroup.of_card (n := 6) (by rw [hE.2.2]; norm_num)
  obtain ⟨Q, hQ⟩ := hA02.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Wsub Q (hP2.toSylow hidx)
  have hPeq : P = MulAut.conj g • (Q : Subgroup ↥Wsub) := by
    have := congrArg (fun R : Sylow 2 ↥Wsub => (R : Subgroup ↥Wsub)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this.symm
  have hle : ahat0.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hPeq, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨a, hQ ha, rfl⟩
  have heq := huniq _ hle (isE64_map (MulAut.conj g).injective hE)
  refine ⟨g, fun x => ?_⟩
  rw [← heq, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem card_members_normalizing_e64 (P A : Subgroup ↥Wsub)
    (hP : Nat.card P = 512) (_hAP : A ≤ P) (_hA : Solomon73.IsE64 A)
    (huniq : ∀ A' ≤ P, Solomon73.IsE64 A' → A' = A) :
    {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
      (AE.memAt L.1 h L.2).subgroupOf Wsub ≤ Subgroup.normalizer (A : Set ↥Wsub)}.ncard = 6 := by
  obtain ⟨g, hg⟩ := exists_conj_ahat0 P A hP huniq
  have h1 := ncard_le_of_conj g hg
  have h2 := ncard_le_of_conj g⁻¹ (B := A) (B' := ahat0) fun x => by
    rw [hg, inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  rw [ncard_ahat0] at h1 h2
  omega

end Cert

end CFSG.ClassicalInvolution.Sp62Rec.I1
