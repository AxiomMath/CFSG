module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm6
public import CFSG.ClassicalInvolution.AschTight.E3StarD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GorensteinWalter
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_closure_sup_eq_of_hom {H C : Subgroup G} {M : Type} [Group M] (φ : ↥H →* M)
    (hker : ∀ x, φ x = 1 → (x : G) ∈ C) {P : Subgroup G} (hPH : P ≤ H) {a b : M}
    (hab : Subgroup.closure {a, b} = (P.subgroupOf H).map φ) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) ⊔ (P ⊓ C) = P := by
  classical
  have ha : a ∈ (P.subgroupOf H).map φ := hab ▸ Subgroup.subset_closure (by simp)
  have hb : b ∈ (P.subgroupOf H).map φ := hab ▸ Subgroup.subset_closure (by simp)
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
    let x' : H := ⟨x, hPH hxP⟩
    have hx' : φ x' ∈ (P.subgroupOf H).map φ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [← hab, ← Set.image_singleton, ← Set.image_insert_eq, ← MonoidHom.map_closure] at hx'
    obtain ⟨y', hy', hyx⟩ := Subgroup.mem_map.mp hx'
    have hy : (y' : G) ∈ Subgroup.closure ({(a' : G), (b' : G)} : Set G) := by
      have h := Subgroup.mem_map_of_mem H.subtype hy'
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at h
      exact h
    have hc : (y' : G)⁻¹ * x ∈ C :=
      hker (y'⁻¹ * x') (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
    have hx : x = y' * ((y' : G)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup hy ⟨P.mul_mem (P.inv_mem (hclP hy)) hxP, hc⟩

theorem centralizerModOdd_le_cStar (H K : Subgroup G) : centralizerModOdd H K ≤ cStar K := by
  rintro x ⟨-, hxN, -, hx⟩
  refine mem_cStar_iff.mpr ⟨hxN, fun k => ?_⟩
  obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp (hx ((k : G)⁻¹) (K.inv_mem k.2))
  have hoe' : (o : G) = ⁅x, (k : G)⁻¹⁆ := hoe
  have e : (normalizerConj K ⟨x, hxN⟩ k)⁻¹ * k = o := by
    apply Subtype.ext
    rw [hoe', Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe,
      commutatorElement_def]
    group
  rw [e]
  exact ho

theorem xGroup_eq_gammaGen (K : Subgroup G) (z : G) :
    xGroup K z = gammaGen (CoreAssembly.conjClass K) z := by
  simp only [xGroup, gammaGen, or_comm]

theorem twoGen_of_concl19_5 [Finite G] {X K R : Subgroup G}
    (h : (∃ (n : ℕ) (φ : ↥X →* DihedralGroup n), Function.Surjective φ ∧
        2 * n = Nat.card ↥R ∧ ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ centralizerModOdd X K) ∨
      (∃ (p' e : ℕ) (_ : Fact p'.Prime), p' ≠ 2 ∧ 0 < e ∧
        ∃ φ : ↥X →* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p' e),
          Function.Surjective φ ∧ ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ centralizerModOdd X K))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X) :
    ∃ s : Finset G, s.card ≤ 2 ∧
      Subgroup.closure (s : Set G) ⊔ (P ⊓ centralizerModOdd X K) = P := by
  rcases h with ⟨n, φ, -, -, hφ⟩ | ⟨p', e, hp', hp2, he, φ, -, hφ⟩
  · obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_dihedral ((P.subgroupOf X).map φ)
    exact exists_closure_sup_eq_of_hom φ (fun x hx => (hφ x).mp hx) hPX hab
  · have hF : IsOddPrimePower (Nat.card (GaloisField p' e)) :=
      ⟨p', e, hp'.out, Nat.Prime.odd_of_ne_two hp'.out hp2, he, GaloisField.card p' e he.ne'⟩
    have hP' : IsPGroup 2 ((P.subgroupOf X).map φ) := (hP.comap_subtype).map φ
    obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_isPGroup_pgl2 hF hP'
    exact exists_closure_sup_eq_of_hom φ (fun x hx => (hφ x).mp hx) hPX hab

variable {p f : ℕ} [Fact p.Prime]

theorem normalizerQuotientTwoGeneratedStar_of_c19_5 (h5 : C19_5 p f) (h16 : C19_16Tmp p f)
    [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z)
    (hIH : CITBelowAll p (Nat.card G)) {S : Sylow 2 G} {R : Subgroup G}
    (hstd : Std6 p f (CoreAssembly.conjClass K) K S R z) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass K)) (hWS : W ≤ (S : Subgroup G)) {L : Subgroup G}
    (hL : L ∈ CoreAssembly.conjClass K) {t : G} (htL : IsUniqueInvolution L t) (htz : t ≠ z)
    {V : Subgroup G} (hV : V ∈ USet (CoreAssembly.conjClass K)) (hVS : V ≤ (S : Subgroup G))
    (htV : t ∈ V) : NormalizerQuotientTwoGeneratedStar K := by
  intro P hP hPN
  have hX := h5 G _ K S R z hstd W hW hWS L hL t htL htz V hV hVS htV
  have hPX : P ≤ gammaGen (CoreAssembly.conjClass K) z := by
    intro x hx
    rw [← xGroup_eq_gammaGen]
    refine h16 G K z ht hIH x ?_ (hP.to_le (Subgroup.zpowers_le.mpr hx))
    rw [← normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact hPN hx
  obtain ⟨s, hs, hsP⟩ := twoGen_of_concl19_5 hX hP hPX
  refine ⟨s, hs, le_antisymm (sup_le (le_sup_left.trans hsP.le) inf_le_left) ?_⟩
  calc P = Subgroup.closure (s : Set G) ⊔
        (P ⊓ centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K) := hsP.symm
    _ ≤ Subgroup.closure (s : Set G) ⊔ (P ⊓ cStar K) :=
      sup_le_sup_left (inf_le_inf_left _ (centralizerModOdd_le_cStar _ K)) _

end CFSG.ClassicalInvolution.Disconnected.AschTight
