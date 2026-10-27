module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Walk

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Sporadic.Bridge

variable {M W N N₀ : Type*} [Group M] [CommGroup W] [Group N] [Group N₀] {ρ : M →* MulAut W}

@[expose] def kOf (q : M → ℕ) (tr : ℕ → M) (h : M) : M := h * (tr (q h))⁻¹

@[expose] def secOf {G : Type*} [Group G] (β : M → G) (σ : ℕ → G) (q : M → ℕ) (tr : ℕ → M)
    (h : M) : G :=
  β (kOf q tr h) * σ (q h)

section OneSided

variable {K : Subgroup M} {q : M → ℕ} {tr : ℕ → M}
  (hq : ∀ k ∈ K, ∀ h, q (k * h) = q h) (htr : ∀ h, kOf q tr h ∈ K)

include hq htr

theorem q_tr (h : M) : q (tr (q h)) = q h := by
  have h1 : h = kOf q tr h * tr (q h) := by simp [kOf]
  have := hq _ (htr h) (tr (q h))
  rw [← h1] at this
  exact this.symm

theorem kOf_tr (h : M) : kOf q tr (tr (q h)) = 1 := by
  rw [kOf, q_tr hq htr h, mul_inv_cancel]

theorem q_mul_gen (h t : M) (ht : t = tr (q h)) (a : M) : q (h * a) = q (t * a) := by
  have h1 : h * a = kOf q tr h * (t * a) := by simp [kOf, ht, mul_assoc]
  rw [h1, hq _ (htr h)]

theorem kOf_mul_gen (h t : M) (ht : t = tr (q h)) (a : M) :
    kOf q tr (h * a) = kOf q tr h * kOf q tr (t * a) := by
  have h1 : h * a = kOf q tr h * (t * a) := by simp [kOf, ht, mul_assoc]
  have h2 := q_mul_gen hq htr h t ht a
  simp only [kOf] at h1 h2 ⊢
  rw [h2]
  rw [ht]
  simp only [mul_assoc]
  rw [← ht]
  simp [ht]

end OneSided

section Sections

variable {K : Subgroup M} {q : M → ℕ} {tr : ℕ → M}
  (hq : ∀ k ∈ K, ∀ h, q (k * h) = q h) (htr : ∀ h, kOf q tr h ∈ K)

include hq htr

theorem secOf_tr {G : Type*} [Group G] (β : M → G) (σ : ℕ → G) (hβ1 : β 1 = 1) (h : M) :
    secOf β σ q tr (tr (q h)) = σ (q h) := by
  rw [secOf, kOf_tr hq htr h, hβ1, q_tr hq htr h, one_mul]

theorem edgeElt_secOf_decomp {G : Type*} [Group G] (β : M → G) (σ : ℕ → G) (hβ1 : β 1 = 1)
    (x : ℕ → G) (g : ℕ → M) (h : M) (i : ℕ) :
    edgeElt (secOf β σ q tr) x g h i =
      (β (kOf q tr h) * edgeElt (secOf β σ q tr) x g (tr (q h)) i * (β (kOf q tr h))⁻¹) *
        (β (kOf q tr h) * β (kOf q tr (tr (q h) * g i)) *
          (β (kOf q tr h * kOf q tr (tr (q h) * g i)))⁻¹) := by
  obtain ⟨t, ht⟩ : ∃ t, t = tr (q h) := ⟨_, rfl⟩
  have h1 : secOf β σ q tr h = β (kOf q tr h) * σ (q h) := rfl
  have h2 : secOf β σ q tr t = σ (q h) := by rw [ht]; exact secOf_tr hq htr β σ hβ1 h
  have h3 : secOf β σ q tr (h * g i) =
      β (kOf q tr h * kOf q tr (t * g i)) * σ (q (t * g i)) := by
    rw [secOf, kOf_mul_gen hq htr h t ht (g i), q_mul_gen hq htr h t ht (g i)]
  have h4 : secOf β σ q tr (t * g i) = β (kOf q tr (t * g i)) * σ (q (t * g i)) := rfl
  rw [← ht]
  simp only [edgeElt]
  rw [h1, h2, h3, h4]
  group

variable {G : Type*} [Group G]

omit hq htr in
theorem π_secOf (X : ExtData ρ N) (β : M → N) (σ : ℕ → N) (hβπ : ∀ k ∈ K, X.π (β k) = k)
    (hσ : ∀ c, X.π (σ c) = tr c) (htr : ∀ h, kOf q tr h ∈ K) (h : M) :
    X.π (secOf β σ q tr h) = h := by
  rw [secOf, map_mul, hβπ _ (htr h), hσ, kOf]
  group

omit hq htr in
theorem π_edgeElt (X : ExtData ρ N) {s : M → N} (hs : ∀ h, X.π (s h) = h) {x : ℕ → N}
    {g : ℕ → M} (hx : ∀ i, X.π (x i) = g i) (h : M) (i : ℕ) : X.π (edgeElt s x g h i) = 1 := by
  rw [edgeElt, map_mul, map_mul, map_inv, hs, hs, hx]
  group

theorem eT_edgeElt_secOf (X : ExtData ρ N) (β : M → N) (σ : ℕ → N)
    (hβπ : ∀ k ∈ K, X.π (β k) = k) (hβ1 : β 1 = 1) (hσ : ∀ c, X.π (σ c) = tr c)
    {x : ℕ → N} {g : ℕ → M} (hx : ∀ i, X.π (x i) = g i) (h : M) (i : ℕ) :
    X.eT (edgeElt (secOf β σ q tr) x g h i) =
      ρ (kOf q tr h) (X.eT (edgeElt (secOf β σ q tr) x g (tr (q h)) i)) *
        X.eT (β (kOf q tr h) * β (kOf q tr (tr (q h) * g i)) *
          (β (kOf q tr h * kOf q tr (tr (q h) * g i)))⁻¹) := by
  have hs := π_secOf X β σ hβπ hσ htr
  have hφ := π_edgeElt X hs hx (tr (q h)) i
  have hε : X.π (β (kOf q tr h) * β (kOf q tr (tr (q h) * g i)) *
      (β (kOf q tr h * kOf q tr (tr (q h) * g i)))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hβπ _ (htr _), hβπ _ (htr _),
      hβπ _ (K.mul_mem (htr _) (htr _))]
    group
  have hconj : X.π (β (kOf q tr h) * edgeElt (secOf β σ q tr) x g (tr (q h)) i *
      (β (kOf q tr h))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hφ, mul_one, mul_inv_cancel]
  rw [edgeElt_secOf_decomp hq htr β σ hβ1 x g h i, X.eT_mul _ _ hconj hε,
    X.eT_conj _ _ hφ, hβπ _ (htr h)]

end Sections

structure DefectData (X : ExtData ρ N) (X₀ : ExtData ρ N₀) (K : Subgroup M) (g : ℕ → M) where
  θ : N → N₀
  θ_mul : ∀ b b', X.π b ∈ K → X.π b' ∈ K → θ (b * b') = θ b * θ b'
  θ_π : ∀ b, X.π b ∈ K → X₀.π (θ b) = X.π b
  θ_eT : ∀ x, X.π x = 1 → X₀.eT (θ x) = X.eT x
  β : M → N
  β_π : ∀ k ∈ K, X.π (β k) = k
  β_one : β 1 = 1
  q : M → ℕ
  tr : ℕ → M
  q_mul : ∀ k ∈ K, ∀ h, q (k * h) = q h
  tr_mem : ∀ h, kOf q tr h ∈ K
  σ : ℕ → N
  σ_π : ∀ c, X.π (σ c) = tr c
  σ₀ : ℕ → N₀
  σ₀_π : ∀ c, X₀.π (σ₀ c) = tr c
  xt : ℕ → N
  xt_π : ∀ i, X.π (xt i) = g i
  xt₀ : ℕ → N₀
  xt₀_π : ∀ i, X₀.π (xt₀ i) = g i

namespace DefectData

variable {X : ExtData ρ N} {X₀ : ExtData ρ N₀} {K : Subgroup M} {g : ℕ → M}
  (D : DefectData X X₀ K g)

@[expose] def s : M → N := secOf D.β D.σ D.q D.tr

@[expose] def s₀ : M → N₀ := secOf (fun k => D.θ (D.β k)) D.σ₀ D.q D.tr

@[expose] def psi (c i : ℕ) : W :=
  X.eT (edgeElt D.s D.xt g (D.tr c) i) * X₀.eT (edgeElt D.s₀ D.xt₀ g (D.tr c) i)

@[expose] def defect (w : List (ℕ × Bool)) : W :=
  X.eT (wordProd D.xt w) * X₀.eT (wordProd D.xt₀ w)

theorem θ_one : D.θ 1 = 1 := by
  have h := D.θ_mul 1 1 (by rw [map_one]; exact K.one_mem) (by rw [map_one]; exact K.one_mem)
  rw [mul_one] at h
  exact left_eq_mul.1 h

theorem θ_inv {b : N} (hb : X.π b ∈ K) : D.θ b⁻¹ = (D.θ b)⁻¹ := by
  have hb' : X.π b⁻¹ ∈ K := by rw [map_inv]; exact K.inv_mem hb
  have h := D.θ_mul b b⁻¹ hb hb'
  rw [mul_inv_cancel, D.θ_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem π_s (h : M) : X.π (D.s h) = h :=
  π_secOf X D.β D.σ D.β_π D.σ_π D.tr_mem h

theorem θβ_π {k : M} (hk : k ∈ K) : X₀.π (D.θ (D.β k)) = k := by
  rw [D.θ_π _ (by rw [D.β_π k hk]; exact hk), D.β_π k hk]

theorem θβ_one : D.θ (D.β 1) = 1 := by rw [D.β_one, D.θ_one]

theorem π₀_s₀ (h : M) : X₀.π (D.s₀ h) = h :=
  π_secOf X₀ (fun k => D.θ (D.β k)) D.σ₀ (fun _ hk => D.θβ_π hk) D.σ₀_π D.tr_mem h

theorem edge_equivariant (hW : ∀ w : W, w * w = 1) (h : M) (i : ℕ) :
    X.eT (edgeElt D.s D.xt g h i) * X₀.eT (edgeElt D.s₀ D.xt₀ g h i) =
      ρ (kOf D.q D.tr h) (D.psi (D.q h) i) := by
  have e1 : X.eT (edgeElt D.s D.xt g h i) =
      ρ (kOf D.q D.tr h) (X.eT (edgeElt D.s D.xt g (D.tr (D.q h)) i)) *
        X.eT (D.β (kOf D.q D.tr h) * D.β (kOf D.q D.tr (D.tr (D.q h) * g i)) *
          (D.β (kOf D.q D.tr h * kOf D.q D.tr (D.tr (D.q h) * g i)))⁻¹) :=
    eT_edgeElt_secOf D.q_mul D.tr_mem X D.β D.σ D.β_π D.β_one D.σ_π D.xt_π h i
  have e2 : X₀.eT (edgeElt D.s₀ D.xt₀ g h i) =
      ρ (kOf D.q D.tr h) (X₀.eT (edgeElt D.s₀ D.xt₀ g (D.tr (D.q h)) i)) *
        X₀.eT (D.θ (D.β (kOf D.q D.tr h)) * D.θ (D.β (kOf D.q D.tr (D.tr (D.q h) * g i))) *
          (D.θ (D.β (kOf D.q D.tr h * kOf D.q D.tr (D.tr (D.q h) * g i))))⁻¹) :=
    eT_edgeElt_secOf D.q_mul D.tr_mem X₀ (fun k => D.θ (D.β k)) D.σ₀
      (fun _ hk => D.θβ_π hk) D.θβ_one D.σ₀_π D.xt₀_π h i
  set k := kOf D.q D.tr h with hk
  set k' := kOf D.q D.tr (D.tr (D.q h) * g i) with hk'
  have hkK : k ∈ K := D.tr_mem h
  have hk'K : k' ∈ K := D.tr_mem _
  have hB : ∀ a ∈ K, X.π (D.β a) ∈ K := fun a ha => by rw [D.β_π a ha]; exact ha
  have hε : X.π (D.β k * D.β k' * (D.β (k * k'))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, D.β_π _ hkK, D.β_π _ hk'K, D.β_π _ (K.mul_mem hkK hk'K)]
    group
  have hθε : D.θ (D.β k * D.β k' * (D.β (k * k'))⁻¹) =
      D.θ (D.β k) * D.θ (D.β k') * (D.θ (D.β (k * k')))⁻¹ := by
    have hkk : X.π (D.β k * D.β k') ∈ K := by
      rw [map_mul]; exact K.mul_mem (hB k hkK) (hB k' hk'K)
    rw [D.θ_mul _ _ hkk (by rw [map_inv]; exact K.inv_mem (hB _ (K.mul_mem hkK hk'K))),
      D.θ_mul _ _ (hB k hkK) (hB k' hk'K), D.θ_inv (hB _ (K.mul_mem hkK hk'K))]
  rw [e1, e2, ← hθε, D.θ_eT _ hε, psi, map_mul]
  have := hW (X.eT (D.β k * D.β k' * (D.β (k * k'))⁻¹))
  calc _ = (ρ k (X.eT (edgeElt D.s D.xt g (D.tr (D.q h)) i)) *
        ρ k (X₀.eT (edgeElt D.s₀ D.xt₀ g (D.tr (D.q h)) i))) *
        (X.eT (D.β k * D.β k' * (D.β (k * k'))⁻¹) *
          X.eT (D.β k * D.β k' * (D.β (k * k'))⁻¹)) := by
        rw [mul_mul_mul_comm]
    _ = _ := by rw [this, mul_one]

theorem walk_eq (hW : ∀ w : W, w * w = 1) (w : List (ℕ × Bool)) (hw : wordProd g w = 1)
    (h₀ : M) :
    ρ h₀ (D.defect w) =
      ((walkEdges g w h₀).map fun e =>
        ρ (kOf D.q D.tr e.1) (D.psi (D.q e.1) e.2)).prod := by
  obtain ⟨-, hN⟩ := eT_walk X hW D.xt_π D.π_s w h₀
  obtain ⟨-, hN₀⟩ := eT_walk X₀ hW D.xt₀_π D.π₀_s₀ w h₀
  rw [hw, mul_one] at hN hN₀
  have hR : X.π (wordProd D.xt w) = 1 := by rw [X.π_wordProd D.xt_π, hw]
  have hR₀ : X₀.π (wordProd D.xt₀ w) = 1 := by rw [X₀.π_wordProd D.xt₀_π, hw]
  have hc : X.eT (D.s h₀ * wordProd D.xt w * (D.s h₀)⁻¹) = ρ h₀ (X.eT (wordProd D.xt w)) := by
    rw [X.eT_conj _ _ hR, D.π_s]
  have hc₀ : X₀.eT (D.s₀ h₀ * wordProd D.xt₀ w * (D.s₀ h₀)⁻¹) =
      ρ h₀ (X₀.eT (wordProd D.xt₀ w)) := by
    rw [X₀.eT_conj _ _ hR₀, D.π₀_s₀]
  rw [defect, map_mul, ← hc, ← hc₀, hN, hN₀, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact D.edge_equivariant hW e.1 e.2

end DefectData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
