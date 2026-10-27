module

public import CFSG.ClassicalInvolution.AschTight.CStar

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GorensteinWalter
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]

theorem closure_pair_sup_eq_of_map {Ψ : Subgroup.normalizer (K : Set G) →* M} {C : Subgroup G}
    (hker : ∀ n, Ψ n = 1 → (n : G) ∈ C) {P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) {a b : M}
    (hab : Subgroup.closure {a, b} = (P.subgroupOf (Subgroup.normalizer (K : Set G))).map Ψ) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) ⊔ (P ⊓ C) = P := by
  classical
  set P' := P.subgroupOf (Subgroup.normalizer (K : Set G)) with hP'
  have ha : a ∈ P'.map Ψ := hab ▸ Subgroup.subset_closure (by simp)
  have hb : b ∈ P'.map Ψ := hab ▸ Subgroup.subset_closure (by simp)
  obtain ⟨a', ha'P, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb'P, rfl⟩ := Subgroup.mem_map.mp hb
  have hclP : Subgroup.closure ({(a' : G), (b' : G)} : Set G) ≤ P := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_subgroupOf.mp ha'P
    · exact Subgroup.mem_subgroupOf.mp hb'P
  refine ⟨{(a' : G), (b' : G)}, Finset.card_le_two, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_pair]
    exact sup_le hclP inf_le_left
  · intro x hxP
    rw [Finset.coe_pair]
    let x' : Subgroup.normalizer (K : Set G) := ⟨x, hPN hxP⟩
    have hx' : Ψ x' ∈ P'.map Ψ := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [← hab, ← Set.image_singleton, ← Set.image_insert_eq, ← MonoidHom.map_closure] at hx'
    obtain ⟨y', hy', hyx⟩ := Subgroup.mem_map.mp hx'
    have hy : (y' : G) ∈ Subgroup.closure ({(a' : G), (b' : G)} : Set G) := by
      have h := Subgroup.mem_map_of_mem (Subgroup.normalizer (K : Set G)).subtype hy'
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at h
      exact h
    have hc : (y' : G)⁻¹ * x ∈ C :=
      hker (y'⁻¹ * x') (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
    have hx : x = y' * ((y' : G)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup hy ⟨P.mul_mem (P.inv_mem (hclP hy)) hxP, hc⟩

end Lift

section Inner

variable {G : Type} [Group G] {K : Subgroup G}

theorem exists_closure_pair_eq_of_le_range_inl {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {H : Subgroup (PGammaL2 F)} (hH : IsPGroup 2 H)
    (hle : H ≤ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range) :
    ∃ a b : PGammaL2 F, Subgroup.closure {a, b} = H := by
  have hH' : IsPGroup 2 (H.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) :=
    hH.comap_of_injective _ SemidirectProduct.inl_injective
  obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_isPGroup_pgl2 hF hH'
  refine ⟨SemidirectProduct.inl a, SemidirectProduct.inl b, ?_⟩
  have h := congrArg (Subgroup.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) hab
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, Subgroup.map_comap_eq,
    inf_eq_right.mpr hle] at h
  exact h

@[expose] def InnerDiagonalTwo (p f : ℕ) [Fact p.Prime] (K : Subgroup G) : Prop :=
  ∀ (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (x : Subgroup.normalizer (K : Set G)), IsPGroup 2 (Subgroup.zpowers x) →
      normalizerToPGammaL2Mod e hFcard hF h3 x ∈
        (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range

variable {p f : ℕ} [Fact p.Prime]

theorem innerDiagonalTwo_of_odd (hf : Odd f) : InnerDiagonalTwo p f K := by
  intro e hFcard hF h3 x hx
  have h := le_range_inl_of_isPGroup Fact.out hFcard hf (hx.map (normalizerToPGammaL2Mod e
    hFcard hF h3))
  exact h (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers x))

theorem normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo [Finite G] {z : G}
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z)
    (hI : InnerDiagonalTwo p f K) : NormalizerQuotientTwoGeneratedStar K := by
  intro P hP hPN
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hF : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, Nat.Prime.odd_of_ne_two Fact.out hp2, Nat.one_le_iff_ne_zero.mpr hf0, hFcard⟩
  have h3 : 3 < Nat.card (GaloisField p f) := by omega
  set Ψ := normalizerToPGammaL2Mod (G := G) e hFcard hF h3 with hΨ
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.normalizer (K : Set G))) := hP.comap_subtype
  have hle : (P.subgroupOf (Subgroup.normalizer (K : Set G))).map Ψ ≤
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range := by
    rintro _ ⟨x, hx, rfl⟩
    refine hI e hFcard hF h3 x ?_
    exact hP'.to_le (Subgroup.zpowers_le.mpr hx)
  obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_le_range_inl hF (hP'.map Ψ) hle
  exact closure_pair_sup_eq_of_map (C := cStar K) (fun n hn => ⟨n,
    oddCoreQuotientAut_eq_one_of_normalizerToPGammaL2Mod_eq_one e hFcard hF h3 hn, rfl⟩) hPN hab

end Inner

section C19

variable {G : Type} [Group G]

@[expose] def xGroup (K : Subgroup G) (z : G) : Subgroup G :=
  ⨆ V ∈ {V : Subgroup G | (V ∈ Asc77.RSet (CoreAssembly.conjClass K) ∨
      V ∈ Asc77.USet (CoreAssembly.conjClass K)) ∧ V ≤ Subgroup.centralizer ({z} : Set G)}, V

theorem xGroup_le_centralizer (K : Subgroup G) (z : G) :
    xGroup K z ≤ Subgroup.centralizer ({z} : Set G) :=
  iSup₂_le fun _ hV => hV.2

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_5Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    S19R.TightStd p f K z →
    ∀ (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
      (hFcard : Nat.card (GaloisField p f) = p ^ f)
      (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
      (x : Subgroup.normalizer (K : Set G)), (x : G) ∈ xGroup K z →
        normalizerToPGammaL2Mod e hFcard hF h3 x ∈
          (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range

@[expose] def C19_16Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    S19R.TightStd p f K z → (∀ e : ℕ, 5 ≤ p ^ e → CITBelowU p e (Nat.card G)) →
    ∀ x ∈ Subgroup.centralizer ({z} : Set G), IsPGroup 2 (Subgroup.zpowers x) → x ∈ xGroup K z

variable {p f}

theorem innerDiagonalTwo_of_c19 (h5 : C19_5Tmp p f) (h16 : C19_16Tmp p f) [Finite G]
    [IsSimpleGroup G] {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z)
    (hIH : ∀ e : ℕ, 5 ≤ p ^ e → CITBelowU p e (Nat.card G)) : InnerDiagonalTwo p f K := by
  intro e hFcard hF h3 x hx
  refine h5 G K z ht e hFcard hF h3 x (h16 G K z ht hIH (x : G) ?_ ?_)
  · rw [← normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact x.2
  · have := hx.map (Subgroup.normalizer (K : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this

theorem normalizerQuotientTwoGeneratedStar_of_c19 (h5 : C19_5Tmp p f) (h16 : C19_16Tmp p f)
    [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z)
    (hIH : ∀ e : ℕ, 5 ≤ p ^ e → CITBelowU p e (Nat.card G)) :
    NormalizerQuotientTwoGeneratedStar K :=
  normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo ht.branch.odd ht.branch.five
    ht.branch.member (innerDiagonalTwo_of_c19 h5 h16 ht hIH)

end C19

end CFSG.ClassicalInvolution.Disconnected.AschTight
