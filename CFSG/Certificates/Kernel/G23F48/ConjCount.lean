module

public import CFSG.Certificates.Kernel.G23F48.ConjOrb
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

section Group

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_conj {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact y.2

theorem card_mul_le_of_conj {P K : Subgroup G} {N : ℕ} (g : Fin N → G) (hg : ∀ i, g i ∈ P)
    (hd : ∀ i j, (g i)⁻¹ * g j ∈ Subgroup.normalizer (K : Set G) → i = j) :
    N * Nat.card ↥(P ⊓ Subgroup.normalizer (K : Set G)) ≤ Nat.card P := by
  set M := P ⊓ Subgroup.normalizer (K : Set G)
  have hMP : M ≤ P := inf_le_left
  let f : Fin N → P ⧸ M.subgroupOf P := fun i => ((⟨g i, hg i⟩ : P) : P ⧸ M.subgroupOf P)
  have hf : Function.Injective f := by
    intro i j hij
    have h1 := QuotientGroup.eq.1 hij
    rw [Subgroup.mem_subgroupOf] at h1
    exact hd i j (Subgroup.mem_inf.1 h1).2
  have h1 : N ≤ (M.subgroupOf P).index := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_fin] at this
  have h2 := (M.subgroupOf P).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMP).toEquiv] at h2
  calc N * Nat.card M ≤ (M.subgroupOf P).index * Nat.card M := Nat.mul_le_mul_right _ h1
    _ = Nat.card P := h2

theorem inv_mul_mem_of_card {P K : Subgroup G} {x y : G} (hKP : K ≤ P) (hK : Nat.card K = 4)
    (hM : Nat.card ↥(P ⊓ Subgroup.normalizer (K : Set G)) ≤ 8) (hx : x ∈ P)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hxK : x ∉ K) (hy : y ∈ P)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyK : y ∉ K) : x⁻¹ * y ∈ K := by
  set M := P ⊓ Subgroup.normalizer (K : Set G)
  have hKM : K ≤ M := le_inf hKP Subgroup.le_normalizer
  set L := K.subgroupOf M
  have hL : Nat.card L = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hK]
  have h2 := L.index_mul_card
  rw [hL] at h2
  have h0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : L.index ≠ 1 := fun h => by
    rw [Subgroup.index_eq_one] at h
    have : (⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩ : M) ∈ L := h ▸ Subgroup.mem_top _
    exact hxK (Subgroup.mem_subgroupOf.1 this)
  have hi : L.index = 2 := by omega
  have e := Subgroup.mul_mem_iff_of_index_two hi (a := (⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩ : M)⁻¹)
    (b := ⟨y, Subgroup.mem_inf.2 ⟨hy, hyN⟩⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_mem_iff] at e
  exact e.2 (iff_of_false hxK hyK)

theorem eq_of_card_four {H : Subgroup G} (hH : Nat.card H = 4) {a b c d : G} (ha : a ∈ H)
    (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {x : G} (hx : x ∈ H) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hne
  have := Fintype.ofFinite H
  let T : Finset H := {⟨x, hx⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩}
  have hT : T.card = 5 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem (by simp [hxa, hxb, hxc, hxd]),
      Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hle := Finset.card_le_univ T
  rw [hT, ← Nat.card_eq_fintype_card, hH] at hle
  omega

end Group

section Pack

variable {m n w : ℕ}

@[expose] def RelOm (om : Fin n → Fin m) (c : Equiv.Perm (Fin m)) (r : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ i, c (om i) = om (r i)

theorem RelOm.mul {om : Fin n → Fin m} {c c' : Equiv.Perm (Fin m)} {r r' : Equiv.Perm (Fin n)}
    (h : RelOm om c r) (h' : RelOm om c' r') : RelOm om (c * c') (r * r') := fun i => by
  rw [Equiv.Perm.mul_apply, h', h, Equiv.Perm.mul_apply]

theorem RelOm.inv {om : Fin n → Fin m} {c : Equiv.Perm (Fin m)} {r : Equiv.Perm (Fin n)}
    (h : RelOm om c r) : RelOm om c⁻¹ r⁻¹ := fun i => by
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  simp

@[expose] def RecOm (n w : ℕ) (om : Fin n → Fin m) (N : ℕ) (c : Equiv.Perm (Fin m)) : Prop :=
  ∃ r, PRep n w N r ∧ RelOm om c r

@[expose] def Enc (n w : ℕ) (om : Fin n → Fin m) (N : ℕ) (c : Equiv.Perm (Fin m)) : Prop :=
  N >>> (n * w) = 0 ∧ RecOm n w om N c

theorem RecOm.pcomp {om : Fin n → Fin m} (hn : n < 2 ^ 32) {N N' : ℕ}
    {c c' : Equiv.Perm (Fin m)} (h : RecOm n w om N c) (h' : RecOm n w om N' c') :
    RecOm n w om (pcomp n w (mask w) N N') (c * c') := by
  obtain ⟨r, hr, hc⟩ := h
  obtain ⟨r', hr', hc'⟩ := h'
  exact ⟨r * r', prep_pcomp hn hr hr', hc.mul hc'⟩

theorem Enc.unique {om : Fin n → Fin m} (hom : Function.Injective om) (hw : 0 < w)
    {N N' : ℕ} {c : Equiv.Perm (Fin m)} (h : Enc n w om N c) (h' : Enc n w om N' c) : N = N' := by
  obtain ⟨h0, r, hr, hc⟩ := h
  obtain ⟨h0', r', hr', hc'⟩ := h'
  have e : r = r' := Equiv.ext fun i => hom ((hc i).symm.trans (hc' i))
  subst e
  exact PF.eq_of_fields hw h0 h0' fun i hi => (hr ⟨i, hi⟩).trans (hr' ⟨i, hi⟩).symm

theorem Enc.pcomp {om : Fin n → Fin m} (hn : n < 2 ^ 32) (hw : 0 < w) {N N' : ℕ}
    {c c' : Equiv.Perm (Fin m)} (h : RecOm n w om N c) (h' : RecOm n w om N' c') :
    Enc n w om (pcomp n w (mask w) N N') (c * c') :=
  ⟨PF.pcomp_shr _ _ hn hw, h.pcomp hn h'⟩

@[expose] noncomputable def encOf (n w : ℕ) (om : Fin n → Fin m) (c : Equiv.Perm (Fin m)) : ℕ :=
  open Classical in if h : ∃ N, Enc n w om N c then Classical.choose h else 0

theorem encOf_eq {om : Fin n → Fin m} (hom : Function.Injective om) (hw : 0 < w) {N : ℕ}
    {c : Equiv.Perm (Fin m)} (h : Enc n w om N c) : encOf n w om c = N := by
  have he : ∃ N, Enc n w om N c := ⟨N, h⟩
  rw [encOf, dif_pos he]
  exact Enc.unique hom hw (Classical.choose_spec he) h

@[expose] def wd {H : Type*} [Group H] (σ : ℕ → H) : List ℕ → H
  | [] => 1
  | s :: ws => σ s * wd σ ws

theorem wd_mem {H : Type*} [Group H] {σ : ℕ → H} {P : Subgroup H} {k : ℕ}
    (hσ : ∀ s < k, σ s ∈ P) : ∀ ws : List ℕ, (∀ s ∈ ws, s < k) → wd σ ws ∈ P
  | [], _ => P.one_mem
  | s :: ws, h => P.mul_mem (hσ s (h s List.mem_cons_self))
      (wd_mem hσ ws fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem enc_pconjW {om : Fin n → Fin m} (hn : n < 2 ^ 32) (hw : 0 < w) {G GI : List ℕ}
    {σ : ℕ → Equiv.Perm (Fin m)} {ρ : ℕ → Equiv.Perm (Fin n)}
    (hG : ∀ s < G.length, PRep n w (G.getD s 0) (ρ s) ∧ PRep n w (GI.getD s 0) (ρ s)⁻¹ ∧
      RelOm om (σ s) (ρ s))
    {x : ℕ} {k : Equiv.Perm (Fin m)} (hx : Enc n w om x k) :
    ∀ ws : List ℕ, (∀ s ∈ ws, s < G.length) →
      Enc n w om (pconjW n w G GI ws x) (wd σ ws * k * (wd σ ws)⁻¹)
  | [], _ => by simpa [pconjW, wd] using hx
  | s :: ws, h => by
    have ih := enc_pconjW hn hw hG hx ws fun t ht => h t (List.mem_cons_of_mem _ ht)
    obtain ⟨h1, h2, h3⟩ := hG s (h s List.mem_cons_self)
    have eg : RecOm n w om (G.getD s 0) (σ s) := ⟨ρ s, h1, h3⟩
    have egi : RecOm n w om (GI.getD s 0) (σ s)⁻¹ := ⟨(ρ s)⁻¹, h2, h3.inv⟩
    have e := Enc.pcomp hn hw (eg.pcomp hn ih.2) egi
    have hc : σ s * (wd σ ws * k * (wd σ ws)⁻¹) * (σ s)⁻¹ =
        wd σ (s :: ws) * k * (wd σ (s :: ws))⁻¹ := by
      simp only [wd, mul_inv_rev, mul_assoc]
    rw [hc] at e
    exact e

theorem conj_eq_iff {H : Type*} [Group H] {x c k : H} : x⁻¹ * c * x = k ↔ c = x * k * x⁻¹ := by
  constructor
  · rintro rfl
    group
  · rintro rfl
    group

theorem conj_conj {H : Type*} [Group H] (x k : H) : x⁻¹ * (x * k * x⁻¹) * x = k := by
  group

theorem conj_ne_one {H : Type*} [Group H] {x k : H} (h : k ≠ 1) : x * k * x⁻¹ ≠ 1 := fun e =>
  h (by rw [← conj_conj x k, e, mul_one, inv_mul_cancel])

@[expose] def conj3 (k₀ k₁ x : Equiv.Perm (Fin m)) : Finset (Equiv.Perm (Fin m)) :=
  {x * k₀ * x⁻¹, x * k₁ * x⁻¹, x * (k₀ * k₁) * x⁻¹}

theorem conj_distinct {om : Fin n → Fin m} (hom : Function.Injective om) (hn : n < 2 ^ 32)
    (hw : 0 < w) {md : ℕ} {G GI : List ℕ} {a b N : ℕ} {C : List (List ℕ)}
    (hc : conjQ n w md G GI a b C N = true)
    {σ : ℕ → Equiv.Perm (Fin m)} {ρ : ℕ → Equiv.Perm (Fin n)} {P K : Subgroup (Equiv.Perm (Fin m))}
    (hG : ∀ s < G.length, PRep n w (G.getD s 0) (ρ s) ∧ PRep n w (GI.getD s 0) (ρ s)⁻¹ ∧
      RelOm om (σ s) (ρ s))
    (hσ : ∀ s < G.length, σ s ∈ P)
    {k₀ k₁ : Equiv.Perm (Fin m)} (ha : Enc n w om a k₀) (hb : Enc n w om b k₁)
    (hK : ∀ c ∈ K, c = 1 ∨ c = k₀ ∨ c = k₁ ∨ c = k₀ * k₁) (hk₀ : k₀ ∈ K) (hk₁ : k₁ ∈ K)
    (h0 : k₀ ≠ 1) (h1 : k₁ ≠ 1) (h01 : k₀ * k₁ ≠ 1) (h0_1 : k₀ ≠ k₁) (h0_01 : k₀ ≠ k₀ * k₁)
    (h1_01 : k₁ ≠ k₀ * k₁) :
    ∃ g : Fin N → Equiv.Perm (Fin m), (∀ i, g i ∈ P) ∧
      ∀ i j, (g i)⁻¹ * g j ∈ Subgroup.normalizer (K : Set (Equiv.Perm (Fin m))) → i = j := by
  classical
  obtain ⟨V, hVl, hV, hVp⟩ := conjQ_spec hc
  choose W hWl hWv using hV
  have hidx : ∀ i : Fin N, (i : ℕ) < V.length := fun i => hVl ▸ i.2
  let g : Fin N → Equiv.Perm (Fin m) := fun i => wd σ (W (V[i.1]'(hidx i)) (List.getElem_mem (hidx i)))
  have hmem : ∀ x c, c ∈ conj3 k₀ k₁ x ↔ x⁻¹ * c * x ∈ K ∧ c ≠ 1 := by
    intro x c
    simp only [conj3, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨by rw [conj_conj]; exact hk₀, conj_ne_one h0⟩
      · exact ⟨by rw [conj_conj]; exact hk₁, conj_ne_one h1⟩
      · exact ⟨by rw [conj_conj]; exact K.mul_mem hk₀ hk₁, conj_ne_one h01⟩
    · rintro ⟨hc, hc1⟩
      rcases hK _ hc with e | e | e | e
      · exact (hc1 (by rw [conj_eq_iff.1 e, mul_one, mul_inv_cancel])).elim
      · exact Or.inl (conj_eq_iff.1 e)
      · exact Or.inr (Or.inl (conj_eq_iff.1 e))
      · exact Or.inr (Or.inr (conj_eq_iff.1 e))
  have hkey : ∀ i : Fin N, ckey n w (V[i.1]'(hidx i)) =
      ∑ c ∈ conj3 k₀ k₁ (g i), encOf n w om c := by
    intro i
    have hv := hWv _ (List.getElem_mem (hidx i))
    have hl := hWl _ (List.getElem_mem (hidx i))
    have hx : g i = wd σ (W _ (List.getElem_mem (hidx i))) := rfl
    rw [hx]
    generalize W _ (List.getElem_mem (hidx i)) = ws at hv hl ⊢
    have ea := enc_pconjW hn hw hG ha _ hl
    have eb := enc_pconjW hn hw hG hb _ hl
    have eab := Enc.pcomp hn hw ea.2 eb.2
    set x := wd σ ws with hxw
    have e3 : x * k₀ * x⁻¹ * (x * k₁ * x⁻¹) = x * (k₀ * k₁) * x⁻¹ := by
      group
    rw [e3] at eab
    have hA : x * k₀ * x⁻¹ ∉ ({x * k₁ * x⁻¹, x * (k₀ * k₁) * x⁻¹} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, mul_left_inj, mul_right_inj]
      exact not_or.2 ⟨h0_1, h0_01⟩
    have hB : x * k₁ * x⁻¹ ∉ ({x * (k₀ * k₁) * x⁻¹} : Finset _) := by
      simp only [Finset.mem_singleton, mul_left_inj, mul_right_inj]
      exact h1_01
    rw [conj3, Finset.sum_insert hA, Finset.sum_insert hB, Finset.sum_singleton,
      encOf_eq hom hw ea, encOf_eq hom hw eb, encOf_eq hom hw eab]
    simp only [ckey, hv, add_assoc]
  refine ⟨g, fun i => wd_mem hσ _ (hWl _ _), fun i j hij => ?_⟩
  have hS : conj3 k₀ k₁ (g i) = conj3 k₀ k₁ (g j) := by
    ext c
    rw [hmem, hmem]
    have e : ((g i)⁻¹ * g j)⁻¹ * ((g i)⁻¹ * c * g i) * ((g i)⁻¹ * g j) = (g j)⁻¹ * c * g j := by
      group
    rw [Subgroup.mem_normalizer_iff''.1 hij, e]
  have hk : ckey n w (V[i.1]'(hidx i)) = ckey n w (V[j.1]'(hidx j)) := by
    rw [hkey i, hkey j, hS]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
  · exact List.pairwise_iff_getElem.1 hVp _ _ (hidx i) (hidx j) hlt (by rw [hk])
  · exact List.pairwise_iff_getElem.1 hVp _ _ (hidx j) (hidx i) hlt (by rw [hk])

end Pack

end CFSG.KC.G23F48

end
