module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Generation

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open Topology Pointwise

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k]

theorem exists_ofFn_eq_wordSet {I : Type*} (W : I → Set (ZariskiGL ι k)) (a : List (I × ℤˣ)) :
    ∃ (m : ℕ) (i : Fin m → I) (e : Fin m → ℤˣ),
      wordSet W a = (List.ofFn fun j => W (i j) ^ ((e j : ℤˣ) : ℤ)).prod := by
  refine ⟨a.length, fun j => (a[j.val]).1, fun j => (a[j.val]).2, ?_⟩
  rw [wordSet]
  congr 1
  refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
  simp

theorem isDefinedOver_wordSet_subgroup [IsAlgClosed k] (k₀ : Subfield k) {J : Type*}
    (K : J → Subgroup (ZariskiGL ι k)) (hK : ∀ j, IsDefinedOver k₀ (K j : Set (ZariskiGL ι k)))
    (a : List (J × ℤˣ)) :
    IsDefinedOver k₀ (wordSet (fun j => (K j : Set (ZariskiGL ι k))) a) := by
  induction a with
  | nil =>
    rw [wordSet_nil, ← Set.singleton_one]
    exact isDefinedOver_one
  | cons p a ih =>
    rw [wordSet_cons]
    have hpow : (K p.1 : Set (ZariskiGL ι k)) ^ (p.2 : ℤ) = K p.1 := by
      rcases Int.units_eq_one_or p.2 with h | h
      · rw [h, Units.val_one, zpow_one]
      · rw [h, Units.val_neg, Units.val_one, zpow_neg_one, inv_coe_set]
    rw [hpow]
    exact isDefinedOver_mul (hK p.1) ih

variable [IsAlgClosed k]

theorem isDomainImage_affine {σ : Type} [Finite σ] {V : Set (ZariskiAffine σ k)}
    (hVc : IsClosed V) (hVi : IsIrreducible V) (f : V → ZariskiGL ι k)
    (hf : ∀ a b : ι, ∃ P : MvPolynomial σ k, ∀ v : V,
      (toGL (f v) : Matrix ι ι k) a b =
        MvPolynomial.eval (ZariskiAffine.coords (v : ZariskiAffine σ k)) P) :
    IsDomainImage k (pt '' Set.range f) := by
  choose P hP using hf
  refine isDomainImage_range ZariskiAffine.isInducing_pt hVc hVi f (Matrix.of P) fun v => ?_
  ext a b
  rw [Matrix.map_apply, Matrix.of_apply, ZariskiAffine.pt_apply, hP]

theorem isDomainImage_subgroup {K : Subgroup (ZariskiGL ι k)}
    (hKc : IsClosed (K : Set (ZariskiGL ι k))) (hKi : IsIrreducible (K : Set (ZariskiGL ι k))) :
    IsDomainImage k (pt '' (K : Set (ZariskiGL ι k))) := by
  have h := isDomainImage_range isInducing_pt hKc hKi
    (Subtype.val : ↥(K : Set (ZariskiGL ι k)) → ZariskiGL ι k)
    (Matrix.of fun a b => glEntry k ι a b) fun v => by
      ext a b
      simp
  rwa [Subtype.range_coe] at h

end ZariskiGL

open ZariskiGL in
theorem seminaire_exp3_algebraic_group_connectedness_generation (k : Type) [Field k]
    [IsAlgClosed k] :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ZariskiGL ι k)),
      IsClosed S ↔ ∃ F : Set (MvPolynomial (ι × ι ⊕ Unit) k), S = {g | ∀ P ∈ F, eval g P = 0}) ∧
    (∀ (N : ℕ) (V : Set (ZariskiAffine (Fin N) k)),
      IsClosed V ↔ ∃ F : Set (MvPolynomial (Fin N) k),
        V = {x | ∀ P ∈ F, MvPolynomial.eval (ZariskiAffine.coords x) P = 0}) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Subgroup (ZariskiGL ι k)),
      IsClosed (G : Set (ZariskiGL ι k)) →
      (IsConnected (G : Set (ZariskiGL ι k)) ↔ IsIrreducible (G : Set (ZariskiGL ι k))) ∧
      (IsIrreducible (G : Set (ZariskiGL ι k)) ↔
        (vanishingIdeal (G : Set (ZariskiGL ι k))).IsPrime) ∧
      (ZariskiGL.identityComponent G : Set (ZariskiGL ι k)) =
        connectedComponentIn (G : Set (ZariskiGL ι k)) 1 ∧
      ZariskiGL.identityComponent G ≤ G ∧
      IsClosed (ZariskiGL.identityComponent G : Set (ZariskiGL ι k)) ∧
      ((ZariskiGL.identityComponent G).subgroupOf G).Normal ∧
      ((ZariskiGL.identityComponent G).subgroupOf G).FiniteIndex ∧
      (∀ C ∈ irreducibleComponents G,
        ((1 : G) ∈ C ↔ Subtype.val '' C = (ZariskiGL.identityComponent G : Set (ZariskiGL ι k)))) ∧
      (∀ C : Set (ZariskiGL ι k), (∃ C' ∈ irreducibleComponents G, Subtype.val '' C' = C) ↔
        ∃ g ∈ G, C = g • (ZariskiGL.identityComponent G : Set (ZariskiGL ι k))) ∧
      ∀ L : Subgroup (ZariskiGL ι k), L ≤ G → IsClosed (L : Set (ZariskiGL ι k)) →
        (L.subgroupOf G).FiniteIndex → ZariskiGL.identityComponent G ≤ L) ∧
    (∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (G : Subgroup (ZariskiGL ι k)) (H : Subgroup (ZariskiGL κ k)) (φ : G →* H),
      IsClosed (G : Set (ZariskiGL ι k)) → IsClosed (H : Set (ZariskiGL κ k)) → IsMorphism φ →
      mapSubgroup φ G ≤ H ∧ IsClosed (mapSubgroup φ G : Set (ZariskiGL κ k)) ∧
      mapSubgroup φ (ZariskiGL.identityComponent G) =
        ZariskiGL.identityComponent (mapSubgroup φ G) ∧
      (IsConnected (G : Set (ZariskiGL ι k)) →
        IsConnected (mapSubgroup φ G : Set (ZariskiGL κ k))) ∧
      ∀ k₀ : Subfield k, PerfectField k₀ → IsDefinedOver k₀ (G : Set (ZariskiGL ι k)) →
        IsDefinedOver k₀ (H : Set (ZariskiGL κ k)) → IsMorphismOver k₀ φ →
        IsDefinedOver k₀ (mapSubgroup φ G : Set (ZariskiGL κ k))) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Subgroup (ZariskiGL ι k)),
      IsClosed (G : Set (ZariskiGL ι k)) →
      (∀ {I : Type*} (N : I → ℕ) (V : ∀ i, Set (ZariskiAffine (Fin (N i)) k))
        (f : ∀ i, V i → G) (W : I → Set (ZariskiGL ι k)),
        (∀ i, IsClosed (V i) ∧ IsIrreducible (V i)) →
        (∀ i (a b : ι), ∃ P : MvPolynomial (Fin (N i)) k, ∀ v : V i,
          (toGL (f i v : ZariskiGL ι k) : Matrix ι ι k) a b =
            MvPolynomial.eval (ZariskiAffine.coords (v : ZariskiAffine (Fin (N i)) k)) P) →
        (∀ i, W i = Set.range fun v => (f i v : ZariskiGL ι k)) →
        (∀ i, (1 : ZariskiGL ι k) ∈ W i) →
        Subgroup.closure (⋃ i, W i) ≤ G ∧
        IsClosed (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) ∧
        IsConnected (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) ∧
        ∃ (m : ℕ) (i : Fin m → I) (e : Fin m → ℤˣ),
          (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) =
            (List.ofFn fun j => W (i j) ^ ((e j : ℤˣ) : ℤ)).prod) ∧
      ∀ {J : Type*} (K : J → Subgroup (ZariskiGL ι k)),
        (∀ j, K j ≤ G ∧ IsClosed (K j : Set (ZariskiGL ι k)) ∧
          IsConnected (K j : Set (ZariskiGL ι k))) →
        IsClosed ((⨆ j, K j : Subgroup (ZariskiGL ι k)) : Set (ZariskiGL ι k)) ∧
        IsConnected ((⨆ j, K j : Subgroup (ZariskiGL ι k)) : Set (ZariskiGL ι k)) ∧
        ∀ k₀ : Subfield k, PerfectField k₀ →
          (∀ j, IsDefinedOver k₀ (K j : Set (ZariskiGL ι k))) →
          IsDefinedOver k₀ ((⨆ j, K j : Subgroup (ZariskiGL ι k)) : Set (ZariskiGL ι k))) := by
  refine ⟨fun ι _ _ S => ZariskiGL.isClosed_iff, fun N V => ZariskiAffine.isClosed_iff,
    fun ι _ _ G hG => seminaire_exp3_identityComponent G hG, ?_, ?_⟩
  · intro ι κ _ _ _ _ G H φ hG _ hφ
    obtain ⟨hle, hc, heq, hconn⟩ := seminaire_exp3_image hφ hG
    exact ⟨hle, hc, heq, hconn, fun k₀ _ hG₀ _ hφ₀ => isDefinedOver_mapSubgroup hG₀ hφ₀⟩
  · intro ι _ _ G _
    refine ⟨fun {I} N V f W hV hf hW h1 => ?_, fun {J} K hK => ?_⟩
    · have hdom : ∀ i, IsDomainImage k (pt '' W i) := fun i => by
        rw [hW i]
        exact isDomainImage_affine (hV i).1 (hV i).2 (fun v => (f i v : ZariskiGL ι k)) (hf i)
      obtain ⟨hc, hi, a, ha⟩ := closure_eq_wordSet W hdom h1
      refine ⟨?_, hc, hi.isConnected, ?_⟩
      · rw [Subgroup.closure_le]
        intro x hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
        rw [hW i] at hxi
        obtain ⟨v, rfl⟩ := hxi
        exact (f i v).2
      · obtain ⟨m, i, e, h⟩ := exists_ofFn_eq_wordSet W a
        exact ⟨m, i, e, ha.trans h⟩
    · have hKi : ∀ j, IsIrreducible (K j : Set (ZariskiGL ι k)) := fun j =>
        (isConnected_iff_isIrreducible (K j)).1 (hK j).2.2
      have hdom : ∀ j, IsDomainImage k (pt '' (K j : Set (ZariskiGL ι k))) := fun j =>
        isDomainImage_subgroup (hK j).2.1 (hKi j)
      obtain ⟨hc, hi, a, ha⟩ := closure_eq_wordSet (fun j => (K j : Set (ZariskiGL ι k))) hdom
        fun j => (K j).one_mem
      rw [Subgroup.iSup_eq_closure]
      refine ⟨hc, hi.isConnected, fun k₀ _ hK₀ => ?_⟩
      rw [ha]
      exact isDefinedOver_wordSet_subgroup k₀ K hK₀ a

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
