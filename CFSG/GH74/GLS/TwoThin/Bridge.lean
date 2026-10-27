module

public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pLayerOf_le (p : ℕ) (H : Subgroup G) : pLayerOf p H ≤ H := sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem pLayerOf_two_eq_map (H : Subgroup G) :
    pLayerOf 2 H = (TwoLayer.subgroup ↥H).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := isPCompIn_two_iff.mp hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup (isPCompIn_two_iff.mpr ⟨?_, ?_⟩)
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

omit [Finite G] in
theorem pumpUp_eq_map_pumpupY (K : Subgroup G) (y : G) :
    pumpUp 2 K y =
      (pumpupY ((pLayerOf 2 (K ⊓ centralizer ({y} : Set G))).subgroupOf
        (centralizer ({y} : Set G)))).map (centralizer ({y} : Set G)).subtype := by
  set Y' := centralizer ({y} : Set G) with hY'
  set Λ₀ := pLayerOf 2 (K ⊓ Y') with hΛ₀
  have hΛ₀Y : Λ₀ ≤ Y' := (pLayerOf_le 2 _).trans inf_le_right
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [pLayerOf_two_eq_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rintro _ ⟨a, ha, rfl⟩
    have hz := le_pumpupY (Λ₀.subgroupOf Y') hg' ⟨⟨a, hΛ₀Y ha⟩, ha, rfl⟩
    exact ⟨_, hz, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine pumpupY_le_of_forall fun g' hg' => ?_
    rintro _ ⟨⟨a, ha⟩, ha', rfl⟩
    have hg'mem : (g' : G) ∈ pLayerOf 2 Y' := by
      rw [pLayerOf_two_eq_map]
      exact ⟨g', hg', rfl⟩
    exact le_iSup₂ (f := fun g _ => Λ₀.map (MulAut.conj g).toMonoidHom) (g' : G) hg'mem
      ⟨a, ha', rfl⟩

theorem isTwoComponent_subgroupOf_subgroupOf {A B C : Subgroup G} (_hAB : A ≤ B) (hBC : B ≤ C)
    (h : TwoComponents.IsTwoComponent (A.subgroupOf B)) :
    TwoComponents.IsTwoComponent ((A.subgroupOf C).subgroupOf (B.subgroupOf C)) := by
  let e := (Subgroup.subgroupOfEquivOfLe hBC).symm
  have hmap : (A.subgroupOf B).map e.toMonoidHom =
      (A.subgroupOf C).subgroupOf (B.subgroupOf C) := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact hlift
    · intro hmem
      exact ⟨⟨element.val.val, element.property⟩, hmem, rfl⟩
  rw [← hmap]
  exact (TwoComponentTransport.equiv_iff e (A.subgroupOf B)).mpr h

omit [Finite G] in
theorem centralizer_singleton_eq_subgroupOf {x y : G} (hxy : x ∈ centralizer ({y} : Set G)) :
    centralizer ({(⟨x, hxy⟩ : ↥(centralizer ({y} : Set G)))} : Set ↥(centralizer ({y} : Set G))) =
      (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)).subgroupOf
        (centralizer ({y} : Set G)) := by
  ext a
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨?_, a.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff.mp hh']
    have := (Subgroup.mem_centralizer_iff.mp h) _ (Set.mem_singleton _)
    exact congrArg Subtype.val this
  · rintro ⟨h, -⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff.mp hh']
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h) x (Set.mem_singleton x))

theorem hat_equiv_map {Y : Type} [Group Y] [Finite Y] {M : Subgroup Y} (hM : M.IsSubnormal) :
    Nonempty ((↥M ⧸ pPrimeCore 2 ↥M) ≃* ↥(M.map (barMk Y))) := by
  let φ : ↥M →* ↥(M.map (barMk Y)) :=
    ((barMk Y).comp M.subtype).codRestrict (M.map (barMk Y)) fun l => ⟨l, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro k
    obtain ⟨c, hc, hck⟩ := k.2
    exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
  have hker : φ.ker = pPrimeCore 2 ↥M :=
    (MonoidHom.ker_codRestrict _ _ _).trans (ker_restrict_eq_pPrimeCore hM)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

omit [Finite G] in
theorem hat_equiv_subgroupOf {K Y' : Subgroup G} (h : K ≤ Y') :
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃*
      (↥(K.subgroupOf Y') ⧸ pPrimeCore 2 ↥(K.subgroupOf Y'))) := by
  let e := (Subgroup.subgroupOfEquivOfLe h).symm
  exact ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

theorem exists_odd_quotient_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    (ρ : A →* B) (hρ : Function.Surjective ρ) (ψ : A →* C) (hψ : Function.Surjective ψ)
    (hker : ρ.ker ≤ ψ.ker) (hodd : Odd (Nat.card ψ.ker)) :
    ∃ φ : B →* C, Function.Surjective φ ∧ Odd (Nat.card φ.ker) ∧ ∀ a, φ (ρ a) = ψ a := by
  let φ : B →* C := ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
    ⟨ψ, hker⟩
  have hφ : ∀ a, φ (ρ a) = ψ a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ψ, hker⟩ a
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := hψ c
    exact ⟨ρ a, hφ a⟩
  have hkerφ : φ.ker = ψ.ker.map ρ := by
    ext b
    obtain ⟨a, rfl⟩ := hρ b
    simp only [MonoidHom.mem_ker, Subgroup.mem_map, hφ]
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨a', ha', haa⟩
      have : ρ a' = ρ a := haa
      rw [← hφ a, ← this, hφ a']
      exact ha'
  refine ⟨φ, hsurj, ?_, hφ⟩
  rw [hkerφ]
  exact hodd.of_dvd_nat (Subgroup.card_map_dvd _ ρ)

end CFSG.GH74.GLS.TwoThin
