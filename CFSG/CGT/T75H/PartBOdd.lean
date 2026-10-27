module

public import CFSG.CGT.T75H.PartBFrattini
public import CFSG.CGT.T75H.CoprimeFour
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.CGT.T75H

open CFSG.OddInversion

variable {G : Type} [Group G]

structure OddAct (N : Subgroup G) (ℓ α β : G) : Prop where
  pgroup : IsPGroup 3 N
  ℓℓ : ℓ * ℓ = 1
  ℓ1 : ℓ ≠ 1
  αα : α * α = 1
  ββ : β * β = 1
  comm_ℓα : ℓ * α = α * ℓ
  comm_ℓβ : ℓ * β = β * ℓ
  comm_αβ : α * β = β * α
  α1 : α ≠ 1
  β1 : β ≠ 1
  αβ : α ≠ β
  normℓ : ∀ n ∈ N, ℓ * n * ℓ⁻¹ ∈ N
  normα : ∀ n ∈ N, α * n * α⁻¹ ∈ N
  normβ : ∀ n ∈ N, β * n * β⁻¹ ∈ N

@[expose] def Jc (N : Subgroup G) (ℓ γ : G) : Set G :=
  {j | j ∈ invertedSet N ℓ ∧ γ * j = j * γ}

theorem conj_mem_closure_of {S : Set G} {x : G} (hS : ∀ s ∈ S, x * s * x⁻¹ ∈ Subgroup.closure S)
    {m : G} (hm : m ∈ Subgroup.closure S) : x * m * x⁻¹ ∈ Subgroup.closure S := by
  induction hm using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul a b _ _ ha hb =>
    have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

section Bridge

variable [Finite G]

theorem le_of_closure_fixed {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M X : Subgroup G}
    (hM : IsPGroup p M) {ℓ : G} (hℓℓ : ℓ * ℓ = 1) (hMℓ : ∀ m ∈ M, ℓ * m * ℓ⁻¹ ∈ M)
    (hgen : M ≤ Subgroup.closure {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m⁻¹}) (hXM : X ≤ M)
    (hXℓ : ∀ x ∈ X, ℓ * x * ℓ⁻¹ ∈ X)
    (hsup : M ≤ Subgroup.closure ((X : Set G) ∪ {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m})) :
    M ≤ X := by
  classical
  have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓℓ
  let φ : M ≃* M :=
    { toFun := fun m => ⟨ℓ * m * ℓ⁻¹, hMℓ m m.2⟩
      invFun := fun m => ⟨ℓ * m * ℓ⁻¹, hMℓ m m.2⟩
      left_inv := fun m => by
        apply Subtype.ext
        show ℓ * (ℓ * (m : G) * ℓ⁻¹) * ℓ⁻¹ = m
        calc ℓ * (ℓ * (m : G) * ℓ⁻¹) * ℓ⁻¹ = (ℓ * ℓ) * (m : G) * (ℓ * ℓ)⁻¹ := by group
          _ = m := by rw [hℓℓ]; group
      right_inv := fun m => by
        apply Subtype.ext
        show ℓ * (ℓ * (m : G) * ℓ⁻¹) * ℓ⁻¹ = m
        calc ℓ * (ℓ * (m : G) * ℓ⁻¹) * ℓ⁻¹ = (ℓ * ℓ) * (m : G) * (ℓ * ℓ)⁻¹ := by group
          _ = m := by rw [hℓℓ]; group
      map_mul' := fun a b => by
        apply Subtype.ext
        show ℓ * ((a : G) * b) * ℓ⁻¹ = (ℓ * (a : G) * ℓ⁻¹) * (ℓ * (b : G) * ℓ⁻¹)
        group }
  have hφ : ∀ m : M, ((φ m : M) : G) = ℓ * (m : G) * ℓ⁻¹ := fun m => rfl
  have hMp : IsPGroup p M := hM
  have hfin : Finite M := inferInstance
  have hgen' : Subgroup.closure {m : M | φ m = m⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have key : ∀ g (hg : g ∈ Subgroup.closure {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m⁻¹}),
        ∃ hgM : g ∈ M, (⟨g, hgM⟩ : M) ∈ Subgroup.closure {m : M | φ m = m⁻¹} := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem s hs =>
        refine ⟨hs.1, Subgroup.subset_closure ?_⟩
        apply Subtype.ext
        simp only [Subgroup.coe_inv]
        rw [hφ]
        exact hs.2
      | one => exact ⟨M.one_mem, Subgroup.one_mem _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨haM, ha'⟩ := ha
        obtain ⟨hbM, hb'⟩ := hb
        exact ⟨M.mul_mem haM hbM, Subgroup.mul_mem _ ha' hb'⟩
      | inv a _ ha =>
        obtain ⟨haM, ha'⟩ := ha
        exact ⟨M.inv_mem haM, Subgroup.inv_mem _ ha'⟩
    obtain ⟨_, h⟩ := key m (hgen m.2)
    exact h
  have hX' : ∀ x ∈ X.subgroupOf M, φ x ∈ X.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hφ]
    exact hXℓ _ hx
  have hsup' : Subgroup.closure (((X.subgroupOf M : Subgroup M) : Set M) ∪ {m : M | φ m = m}) =
      ⊤ := by
    rw [eq_top_iff]
    intro m _
    have key : ∀ g (hg : g ∈ Subgroup.closure ((X : Set G) ∪
        {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m})), ∃ hgM : g ∈ M, (⟨g, hgM⟩ : M) ∈
        Subgroup.closure (((X.subgroupOf M : Subgroup M) : Set M) ∪ {m : M | φ m = m}) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem s hs =>
        rcases hs with hs | hs
        · exact ⟨hXM hs, Subgroup.subset_closure (Or.inl (Subgroup.mem_subgroupOf.2 hs))⟩
        · refine ⟨hs.1, Subgroup.subset_closure (Or.inr ?_)⟩
          apply Subtype.ext
          rw [hφ]
          exact hs.2
      | one => exact ⟨M.one_mem, Subgroup.one_mem _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨haM, ha'⟩ := ha
        obtain ⟨hbM, hb'⟩ := hb
        exact ⟨M.mul_mem haM hbM, Subgroup.mul_mem _ ha' hb'⟩
      | inv a _ ha =>
        obtain ⟨haM, ha'⟩ := ha
        exact ⟨M.inv_mem haM, Subgroup.inv_mem _ ha'⟩
    obtain ⟨_, h⟩ := key m (hsup m.2)
    exact h
  have htop := eq_top_of_closure_fixed hp2 hMp φ hgen' (X.subgroupOf M) hX' hsup'
  intro m hm
  have : (⟨m, hm⟩ : M) ∈ X.subgroupOf M := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

end Bridge

theorem conj_mem_invertedSet {N : Subgroup G} {ℓ x j : G} (hxℓ : ℓ * x = x * ℓ)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hj : j ∈ invertedSet N ℓ) :
    x * j * x⁻¹ ∈ invertedSet N ℓ := by
  refine ⟨hxN j hj.1, ?_⟩
  have hinv : x⁻¹ * ℓ⁻¹ = ℓ⁻¹ * x⁻¹ := by rw [← mul_inv_rev, hxℓ, mul_inv_rev]
  calc ℓ * (x * j * x⁻¹) * ℓ⁻¹ = (ℓ * x) * j * (x⁻¹ * ℓ⁻¹) := by group
    _ = (x * ℓ) * j * (ℓ⁻¹ * x⁻¹) := by rw [hxℓ, hinv]
    _ = x * (ℓ * j * ℓ⁻¹) * x⁻¹ := by group
    _ = (x * j * x⁻¹)⁻¹ := by rw [hj.2]; group

theorem mem_normalizer_of_invol {K : Subgroup G} {t : G} (htt : t * t = 1)
    (h : ∀ k ∈ K, t * k * t⁻¹ ∈ K) : t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h k, fun hk => ?_⟩
  have := h _ hk
  have e : t * (t * k * t⁻¹) * t⁻¹ = k := by
    calc t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ := by group
      _ = k := by rw [htt]; group
  rwa [e] at this

theorem Jc_inv {N : Subgroup G} {ℓ γ j : G} (hj : j ∈ Jc N ℓ γ) : j⁻¹ ∈ Jc N ℓ γ := by
  refine ⟨invertedSet_inv hj.1, ?_⟩
  have h1 : γ * j = j * γ := hj.2
  calc γ * j⁻¹ = (j * γ⁻¹)⁻¹ := by group
    _ = (γ⁻¹ * j)⁻¹ := by
        congr 1
        calc j * γ⁻¹ = γ⁻¹ * (γ * j) * γ⁻¹ := by group
          _ = γ⁻¹ * (j * γ) * γ⁻¹ := by rw [h1]
          _ = γ⁻¹ * j := by group
    _ = j⁻¹ * γ := by group

namespace OddAct

variable {N : Subgroup G} {ℓ α β : G}

theorem odd_card_of_le [Finite G] (h : OddAct N ℓ α β) {M : Subgroup G} (hM : M ≤ N) :
    Odd (Nat.card M) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 h.pgroup)
  have hodd : Odd (Nat.card N) := by rw [hk]; exact Odd.pow (by decide)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hM)

theorem orderOf_ℓ (h : OddAct N ℓ α β) : orderOf ℓ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.ℓℓ) h.ℓ1

end OddAct

section Star

variable [Finite G] {N : Subgroup G} {ℓ α β : G}

theorem closure_inverted_eq (h : OddAct N ℓ α β) :
    Subgroup.closure (invertedSet N ℓ) =
      Subgroup.closure (Jc N ℓ α ∪ Jc N ℓ β ∪ Jc N ℓ (α * β)) := by
  classical
  apply le_antisymm
  · set M := Subgroup.closure (invertedSet N ℓ) with hMdef
    set X := Subgroup.closure (Jc N ℓ α ∪ Jc N ℓ β ∪ Jc N ℓ (α * β)) with hXdef
    have hJN : invertedSet N ℓ ⊆ N := fun j hj => hj.1
    have hMN : M ≤ N := (Subgroup.closure_le N).2 hJN
    have hMp : IsPGroup 3 M := h.pgroup.to_le hMN
    have hModd : Odd (Nat.card M) := h.odd_card_of_le hMN
    have hJM : invertedSet N ℓ ⊆ M := Subgroup.subset_closure
    have hMℓ : ∀ m ∈ M, ℓ * m * ℓ⁻¹ ∈ M := fun m hm =>
      conj_mem_closure_of (fun j hj => by
        have hinv : ℓ * j * ℓ⁻¹ = j⁻¹ := hj.2
        rw [hinv]
        exact Subgroup.inv_mem _ (hJM hj)) hm
    have hMα : ∀ m ∈ M, α * m * α⁻¹ ∈ M := fun m hm =>
      conj_mem_closure_of (fun j hj =>
        hJM (conj_mem_invertedSet h.comm_ℓα h.normα hj)) hm
    have hMβ : ∀ m ∈ M, β * m * β⁻¹ ∈ M := fun m hm =>
      conj_mem_closure_of (fun j hj =>
        hJM (conj_mem_invertedSet h.comm_ℓβ h.normβ hj)) hm
    have hBW := le_sup_fixed_of_commuting_involutions hModd h.αα h.ββ h.comm_αβ h.α1 h.β1
      h.αβ hMα hMβ
    have hJcX : ∀ γ : G, Jc N ℓ γ ⊆ invertedSet N ℓ := fun γ j hj => hj.1
    have hXM : X ≤ M := by
      rw [hXdef, Subgroup.closure_le]
      intro j hj
      rcases hj with (hj | hj) | hj
      · exact hJM (hJcX _ hj)
      · exact hJM (hJcX _ hj)
      · exact hJM (hJcX _ hj)
    have hXℓ : ∀ x ∈ X, ℓ * x * ℓ⁻¹ ∈ X := fun x hx =>
      conj_mem_closure_of (fun j hj => by
        have hinv : ℓ * j * ℓ⁻¹ = j⁻¹ := by
          rcases hj with (hj | hj) | hj <;> exact hj.1.2
        rw [hinv]
        rcases hj with (hj | hj) | hj
        · exact Subgroup.subset_closure (Or.inl (Or.inl (Jc_inv hj)))
        · exact Subgroup.subset_closure (Or.inl (Or.inr (Jc_inv hj)))
        · exact Subgroup.subset_closure (Or.inr (Jc_inv hj))) hx
    set F : Set G := {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m} with hF
    have key : ∀ γ : G, ℓ * γ = γ * ℓ → Jc N ℓ γ ⊆ (X : Set G) →
        M ⊓ Subgroup.centralizer ({γ} : Set G) ≤
          Subgroup.closure ((X : Set G) ∪ F) := by
      intro γ hγℓ hγX c hc
      set K : Subgroup G := M ⊓ Subgroup.centralizer ({γ} : Set G) with hK
      have hKN : K ≤ N := inf_le_left.trans hMN
      have hKodd : Odd (Nat.card K) := h.odd_card_of_le hKN
      have hKℓ : ∀ k ∈ K, ℓ * k * ℓ⁻¹ ∈ K := by
        intro k hk
        refine ⟨hMℓ k hk.1, ?_⟩
        have hkγ : k * γ = γ * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
        show ℓ * k * ℓ⁻¹ ∈ Subgroup.centralizer ({γ} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hinv : ℓ⁻¹ * γ = γ * ℓ⁻¹ := by
          have := congrArg (fun z => ℓ⁻¹ * z * ℓ⁻¹) hγℓ
          simpa [mul_assoc] using this.symm
        calc ℓ * k * ℓ⁻¹ * γ = ℓ * k * (ℓ⁻¹ * γ) := by group
          _ = ℓ * k * (γ * ℓ⁻¹) := by rw [hinv]
          _ = ℓ * (k * γ) * ℓ⁻¹ := by group
          _ = ℓ * (γ * k) * ℓ⁻¹ := by rw [hkγ]
          _ = (ℓ * γ) * k * ℓ⁻¹ := by group
          _ = (γ * ℓ) * k * ℓ⁻¹ := by rw [hγℓ]
          _ = γ * (ℓ * k * ℓ⁻¹) := by group
      have hnorm : ℓ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_invol h.ℓℓ hKℓ
      have hdec := (CFSG.ABGLocalTools.odd_fixed_mul_inverted hKodd h.orderOf_ℓ hnorm).1
      have hcmem : c ∈ (K : Set G) := hc
      rw [hdec] at hcmem
      obtain ⟨f, hf, i, hi, rfl⟩ := Set.mem_mul.1 hcmem
      have hfK : f ∈ K ⊓ Subgroup.centralizer ({ℓ} : Set G) := hf
      have hfℓ : f * ℓ = ℓ * f := Subgroup.mem_centralizer_singleton_iff.1 hfK.2
      have hfF : f ∈ F := by
        refine ⟨hfK.1.1, ?_⟩
        calc ℓ * f * ℓ⁻¹ = f * ℓ * ℓ⁻¹ := by rw [← hfℓ]
          _ = f := by group
      have hiJc : i ∈ Jc N ℓ γ := by
        have hiK : i ∈ K := hi.1
        refine ⟨⟨hKN hiK, hi.2⟩, ?_⟩
        exact (Subgroup.mem_centralizer_singleton_iff.1 hiK.2).symm
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hfF))
        (Subgroup.subset_closure (Or.inl (hγX hiJc)))
    have hXsub : ∀ γ, (γ = α ∨ γ = β ∨ γ = α * β) → Jc N ℓ γ ⊆ (X : Set G) := by
      intro γ hγ j hj
      rcases hγ with rfl | rfl | rfl
      · exact Subgroup.subset_closure (Or.inl (Or.inl hj))
      · exact Subgroup.subset_closure (Or.inl (Or.inr hj))
      · exact Subgroup.subset_closure (Or.inr hj)
    have hℓαβ : ℓ * (α * β) = (α * β) * ℓ := by
      rw [← mul_assoc, h.comm_ℓα, mul_assoc, h.comm_ℓβ, mul_assoc]
    have hsup : M ≤ Subgroup.closure ((X : Set G) ∪ F) := by
      refine hBW.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact key α h.comm_ℓα (hXsub α (Or.inl rfl))
      · exact key β h.comm_ℓβ (hXsub β (Or.inr (Or.inl rfl)))
      · exact key (α * β) hℓαβ (hXsub (α * β) (Or.inr (Or.inr rfl)))
    have hgen : M ≤ Subgroup.closure {m : G | m ∈ M ∧ ℓ * m * ℓ⁻¹ = m⁻¹} :=
      Subgroup.closure_mono fun j hj => ⟨hJM hj, hj.2⟩
    exact le_of_closure_fixed (p := 3) (by norm_num) hMp h.ℓℓ hMℓ hgen hXM hXℓ hsup
  · rw [Subgroup.closure_le]
    rintro j ((hj | hj) | hj)
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1

end Star

@[expose] def PP (N : Subgroup G) (ℓ x y : G) : Set G :=
  {j | j ∈ invertedSet N ℓ ∧ x * j = j * x ∧ y * j = j * y}

@[expose] def PM (N : Subgroup G) (ℓ x y : G) : Set G :=
  {j | j ∈ invertedSet N ℓ ∧ x * j = j * x ∧ y * j * y⁻¹ = j⁻¹}

@[expose] def MP (N : Subgroup G) (ℓ x y : G) : Set G :=
  {j | j ∈ invertedSet N ℓ ∧ x * j * x⁻¹ = j⁻¹ ∧ y * j = j * y}

@[expose] def MM (N : Subgroup G) (ℓ x y : G) : Set G :=
  {j | j ∈ invertedSet N ℓ ∧ x * j * x⁻¹ = j⁻¹ ∧ y * j * y⁻¹ = j⁻¹}

theorem inverted_commute_iff {ℓ j x : G} (hj : ℓ * j * ℓ⁻¹ = j⁻¹) :
    (x * ℓ) * j = j * (x * ℓ) ↔ x * j * x⁻¹ = j⁻¹ := by
  rw [← mul_inv_eq_iff_eq_mul]
  have e : (x * ℓ) * j * (x * ℓ)⁻¹ = x * (ℓ * j * ℓ⁻¹) * x⁻¹ := by group
  rw [e, hj]
  have e2 : x * j⁻¹ * x⁻¹ = (x * j * x⁻¹)⁻¹ := by group
  rw [e2, inv_eq_iff_eq_inv]

theorem eq_one_of_mul_self_eq_one_of_pGroup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {N : Subgroup G} (hN : IsPGroup p N) {c : G} (hc : c ∈ N) (h : c * c = 1) : c = 1 := by
  have : (⟨c, hc⟩ : N) ∈ (⊥ : Subgroup N) :=
    mem_of_sq_mem hp2 hN (K := ⊥) (c := ⟨c, hc⟩) (by
      rw [sq, Subgroup.mem_bot]
      exact Subtype.ext h)
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 this)

section Split

variable [Finite G] {N : Subgroup G} {ℓ : G}

theorem closure_Jc_split (hN : IsPGroup 3 N) (hℓℓ : ℓ * ℓ = 1) (hℓ1 : ℓ ≠ 1) {e f : G}
    (hff : f * f = 1) (hef : e * f = f * e) (hfℓ : ℓ * f = f * ℓ) (hf1 : f ≠ 1) (hfℓ' : f ≠ ℓ)
    (hNf : ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    Subgroup.closure (Jc N ℓ e) =
      Subgroup.closure ({j | j ∈ Jc N ℓ e ∧ f * j = j * f} ∪
        {j | j ∈ Jc N ℓ e ∧ (f * ℓ) * j = j * (f * ℓ)}) := by
  classical
  set N' : Subgroup G := Subgroup.closure (Jc N ℓ e) with hN'
  have hJcN : Jc N ℓ e ⊆ (N : Set G) := fun j hj => hj.1.1
  have hN'N : N' ≤ N := (Subgroup.closure_le N).2 hJcN
  have hN'ℓ : ∀ n ∈ N', ℓ * n * ℓ⁻¹ ∈ N' := fun n hn =>
    conj_mem_closure_of (fun j hj => by
      have : ℓ * j * ℓ⁻¹ = j⁻¹ := hj.1.2
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure hj)) hn
  have hN'f : ∀ n ∈ N', f * n * f⁻¹ ∈ N' := fun n hn =>
    conj_mem_closure_of (fun j hj => by
      refine Subgroup.subset_closure ⟨conj_mem_invertedSet hfℓ hNf hj.1, ?_⟩
      have hej : e * j = j * e := hj.2
      have hfe : f * e = e * f := hef.symm
      calc e * (f * j * f⁻¹) = (e * f) * j * f⁻¹ := by group
        _ = (f * e) * j * f⁻¹ := by rw [hef]
        _ = f * (e * j) * f⁻¹ := by group
        _ = f * (j * e) * f⁻¹ := by rw [hej]
        _ = (f * j * f⁻¹) * (f * e * f⁻¹) := by group
        _ = (f * j * f⁻¹) * e := by rw [hfe]; group) hn
  have hact : OddAct N' ℓ f ℓ :=
    { pgroup := hN.to_le hN'N, ℓℓ := hℓℓ, ℓ1 := hℓ1, αα := hff, ββ := hℓℓ, comm_ℓα := hfℓ,
      comm_ℓβ := rfl, comm_αβ := hfℓ.symm, α1 := hf1, β1 := hℓ1, αβ := hfℓ',
      normℓ := hN'ℓ, normα := hN'f, normβ := hN'ℓ }
  have key := closure_inverted_eq hact
  have hcentr : N' ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [hN', Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2 hx.2.symm
  have hinv : invertedSet N' ℓ = Jc N ℓ e := by
    ext j
    constructor
    · rintro ⟨hjN', hjℓ⟩
      refine ⟨⟨hN'N hjN', hjℓ⟩, ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hcentr hjN')).symm
    · intro hj
      exact ⟨Subgroup.subset_closure hj, hj.1.2⟩
  have hodd3 : (3 : ℕ) ≠ 2 := by norm_num
  have hmid : Jc N' ℓ ℓ ⊆ {1} := by
    intro j hj
    have hjℓ : ℓ * j * ℓ⁻¹ = j⁻¹ := hj.1.2
    have hcomm : ℓ * j = j * ℓ := hj.2
    have e1 : ℓ * j * ℓ⁻¹ = j := by rw [hcomm]; group
    have : j * j = 1 := mul_eq_one_iff_eq_inv.2 (e1.symm.trans hjℓ)
    exact eq_one_of_mul_self_eq_one_of_pGroup hodd3 (hN.to_le hN'N) hj.1.1 this
  apply le_antisymm
  · calc Subgroup.closure (Jc N ℓ e) = Subgroup.closure (invertedSet N' ℓ) := by rw [hinv]
      _ = Subgroup.closure (Jc N' ℓ f ∪ Jc N' ℓ ℓ ∪ Jc N' ℓ (f * ℓ)) := key
      _ ≤ _ := by
        rw [Subgroup.closure_le]
        rintro j ((hj | hj) | hj)
        · obtain ⟨hj1, hj2⟩ := hj
          rw [hinv] at hj1
          exact Subgroup.subset_closure (Or.inl ⟨hj1, hj2⟩)
        · rw [Set.mem_singleton_iff.1 (hmid hj)]
          exact Subgroup.one_mem _
        · obtain ⟨hj1, hj2⟩ := hj
          rw [hinv] at hj1
          exact Subgroup.subset_closure (Or.inr ⟨hj1, hj2⟩)
  · rw [Subgroup.closure_le]
    rintro j (hj | hj)
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1

theorem closure_inverted_eq_four {α β : G} (h : OddAct N ℓ α β) (hαℓ : α ≠ ℓ)
    (hβℓ : β ≠ ℓ) :
    Subgroup.closure (invertedSet N ℓ) =
      Subgroup.closure (PP N ℓ α β ∪ PM N ℓ α β ∪ MP N ℓ α β ∪ MM N ℓ α β) := by
  classical
  have h1 := closure_inverted_eq h
  have hS1 := closure_Jc_split (N := N) (ℓ := ℓ) (e := α) (f := β) h.pgroup h.ℓℓ h.ℓ1 h.ββ
    h.comm_αβ h.comm_ℓβ h.β1 hβℓ (fun n hn => h.normβ n hn)
  have hS2 := closure_Jc_split (N := N) (ℓ := ℓ) (e := β) (f := α) h.pgroup h.ℓℓ h.ℓ1 h.αα
    h.comm_αβ.symm h.comm_ℓα h.α1 hαℓ (fun n hn => h.normα n hn)
  have hαβ1 : α * β ≠ 1 := fun h' => h.αβ (by
    have : α = β⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [this]
    exact inv_eq_of_mul_eq_one_right h.ββ)
  have hS3 := closure_Jc_split (N := N) (ℓ := ℓ) (e := α * β) (f := α) h.pgroup h.ℓℓ h.ℓ1 h.αα
    (by rw [mul_assoc, ← h.comm_αβ])
    h.comm_ℓα h.α1 hαℓ (fun n hn => h.normα n hn)
  apply le_antisymm
  · rw [h1, Subgroup.closure_le]
    rintro j ((hj | hj) | hj)
    · have hj' : j ∈ Subgroup.closure (Jc N ℓ α) := Subgroup.subset_closure hj
      rw [hS1] at hj'
      refine (Subgroup.closure_mono ?_) hj'
      rintro k (hk | hk)
      · exact Or.inl (Or.inl (Or.inl ⟨hk.1.1, hk.1.2, hk.2⟩))
      · refine Or.inl (Or.inl (Or.inr ⟨hk.1.1, hk.1.2, ?_⟩))
        exact (inverted_commute_iff hk.1.1.2).1 hk.2
    · have hj' : j ∈ Subgroup.closure (Jc N ℓ β) := Subgroup.subset_closure hj
      rw [hS2] at hj'
      refine (Subgroup.closure_mono ?_) hj'
      rintro k (hk | hk)
      · exact Or.inl (Or.inl (Or.inl ⟨hk.1.1, hk.2, hk.1.2⟩))
      · refine Or.inl (Or.inr ⟨hk.1.1, ?_, hk.1.2⟩)
        exact (inverted_commute_iff hk.1.1.2).1 hk.2
    · have hj' : j ∈ Subgroup.closure (Jc N ℓ (α * β)) := Subgroup.subset_closure hj
      rw [hS3] at hj'
      refine (Subgroup.closure_mono ?_) hj'
      rintro k (hk | hk)
      ·
        refine Or.inl (Or.inl (Or.inl ⟨hk.1.1, hk.2, ?_⟩))
        have hαk : α * k = k * α := hk.2
        have hαβk : (α * β) * k = k * (α * β) := hk.1.2
        calc β * k = α * ((α * β) * k) := by
              rw [← mul_assoc, ← mul_assoc, h.αα, one_mul]
          _ = α * (k * (α * β)) := by rw [hαβk]
          _ = (α * k) * (α * β) := by group
          _ = (k * α) * (α * β) := by rw [hαk]
          _ = k * (α * α) * β := by group
          _ = k * β := by rw [h.αα, mul_one]
      ·
        refine Or.inr ⟨hk.1.1, (inverted_commute_iff hk.1.1.2).1 hk.2, ?_⟩
        have hαk : α * k * α⁻¹ = k⁻¹ := (inverted_commute_iff hk.1.1.2).1 hk.2
        have hαβk : (α * β) * k = k * (α * β) := hk.1.2
        have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right h.αα
        have hββinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right h.ββ
        rw [hββinv]
        rw [hαinv] at hαk
        calc β * k * β = α * ((α * β) * k) * β := by
              rw [← mul_assoc, ← mul_assoc, h.αα, one_mul]
          _ = α * (k * (α * β)) * β := by rw [hαβk]
          _ = (α * k * α) * (β * β) := by group
          _ = k⁻¹ := by rw [hαk, h.ββ, mul_one]
  · rw [Subgroup.closure_le]
    rintro j (((hj | hj) | hj) | hj)
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1
    · exact Subgroup.subset_closure hj.1

theorem centralizes_of_pure {α β e : G} (h : OddAct N ℓ α β) (hαℓ : α ≠ ℓ) (hβℓ : β ≠ ℓ)
    (hP : ∀ j ∈ PP N ℓ α β ∪ PM N ℓ α β ∪ MP N ℓ α β ∪ MM N ℓ α β, e * j = j * e) :
    ∀ j ∈ invertedSet N ℓ, e * j = j * e := by
  intro j hj
  have : Subgroup.closure (invertedSet N ℓ) ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [closure_inverted_eq_four h hαℓ hβℓ, Subgroup.closure_le]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 (hP k hk).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this (Subgroup.subset_closure hj))).symm

theorem exists_two_pure {α β : G} (h : OddAct N ℓ α β) (hαℓ : α ≠ ℓ) (hβℓ : β ≠ ℓ)
    (hα : ¬ ∀ j ∈ invertedSet N ℓ, α * j = j * α)
    (hβ : ¬ ∀ j ∈ invertedSet N ℓ, β * j = j * β)
    (hαβ : ¬ ∀ j ∈ invertedSet N ℓ, (α * β) * j = j * (α * β)) :
    ((∃ m ∈ PM N ℓ α β, m ≠ 1) ∧ ∃ m ∈ MP N ℓ α β, m ≠ 1) ∨
      ((∃ m ∈ PM N ℓ α β, m ≠ 1) ∧ ∃ m ∈ MM N ℓ α β, m ≠ 1) ∨
      ((∃ m ∈ MP N ℓ α β, m ≠ 1) ∧ ∃ m ∈ MM N ℓ α β, m ≠ 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  by_cases hA : ∃ m ∈ PM N ℓ α β, m ≠ 1
  ·
    refine hα (centralizes_of_pure h hαℓ hβℓ fun j hj => ?_)
    rcases hj with ((hj | hj) | hj) | hj
    · exact hj.2.1
    · exact hj.2.1
    · rw [h1 hA j hj]; simp
    · rw [h2 hA j hj]; simp
  · have hA' : ∀ m ∈ PM N ℓ α β, m = 1 := fun m hm => by
      by_contra hm1
      exact hA ⟨m, hm, hm1⟩
    by_cases hB : ∃ m ∈ MP N ℓ α β, m ≠ 1
    ·
      refine hβ (centralizes_of_pure h hαℓ hβℓ fun j hj => ?_)
      rcases hj with ((hj | hj) | hj) | hj
      · exact hj.2.2
      · rw [hA' j hj]; simp
      · exact hj.2.2
      · rw [h3 hB j hj]; simp
    ·
      have hB' : ∀ m ∈ MP N ℓ α β, m = 1 := fun m hm => by
        by_contra hm1
        exact hB ⟨m, hm, hm1⟩
      refine hαβ (centralizes_of_pure h hαℓ hβℓ fun j hj => ?_)
      rcases hj with ((hj | hj) | hj) | hj
      · calc (α * β) * j = α * (β * j) := by group
          _ = α * (j * β) := by rw [hj.2.2]
          _ = (α * j) * β := by group
          _ = (j * α) * β := by rw [hj.2.1]
          _ = j * (α * β) := by group
      · rw [hA' j hj]; simp
      · rw [hB' j hj]; simp
      ·
        obtain ⟨-, hjα, hjβ⟩ := hj
        have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right h.αα
        have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right h.ββ
        rw [hαinv] at hjα
        rw [hβinv] at hjβ
        have e : (α * β) * j * (α * β)⁻¹ = j := by
          calc (α * β) * j * (α * β)⁻¹ = α * (β * j * β) * α := by
                rw [mul_inv_rev, hαinv, hβinv]; group
            _ = α * j⁻¹ * α := by rw [hjβ]
            _ = (α * j * α)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hαinv]; group
            _ = j := by rw [hjα, inv_inv]
        exact mul_inv_eq_iff_eq_mul.1 e

end Split

end CFSG.CGT.T75H
