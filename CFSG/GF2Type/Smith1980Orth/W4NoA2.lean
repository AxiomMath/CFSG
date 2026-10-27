module

public import CFSG.GF2Type.Smith1980Orth.Defs
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.LargeExtraspecial.S12FiveMain
public import CFSG.LargeExtraspecial.S12EightMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions CFSG.Open

private theorem exists_threeCycle_normal {H K : Type*} [Group H] [Group K]
    (e : H ≃* Equiv.Perm (Fin 3) × K) :
    ∃ c : H, c ^ 3 = 1 ∧ c ≠ 1 ∧ ∀ m : H, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c⁻¹ := by
  let r : Equiv.Perm (Fin 3) := finRotate 3
  have hr3 : r ^ 3 = 1 := by decide
  have hr1 : r ≠ 1 := by decide
  have hrn : ∀ σ : Equiv.Perm (Fin 3), σ * r * σ⁻¹ = r ∨ σ * r * σ⁻¹ = r⁻¹ := by decide
  refine ⟨e.symm (r, 1), ?_, ?_, ?_⟩
  · rw [← map_pow, Prod.pow_def, hr3, one_pow]
    exact map_one _
  · intro h
    have h' : ((r, 1) : Equiv.Perm (Fin 3) × K) = 1 := (map_eq_one_iff _ e.symm.injective).mp h
    exact hr1 (congrArg Prod.fst h')
  · intro m
    obtain ⟨⟨σ, κ⟩, rfl⟩ := e.symm.surjective m
    rcases hrn σ with h | h
    · left
      rw [← map_mul, ← map_inv, ← map_mul]
      exact congrArg e.symm (Prod.ext (by simpa using h) (by simp))
    · right
      rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
      exact congrArg e.symm (Prod.ext (by simpa using h) (by simp))

private theorem two_mul_finrank_commSpace_of_inverts {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {c t : V ≃ₗ[ZMod 2] V}
    (hc3 : c * c * c = 1)
    (hfix : ∀ v, c v = v → v = 0) (ht2 : t * t = 1) (htc : t * c = c⁻¹ * t) :
    2 * finrank (ZMod 2) (commSpace t) = finrank (ZMod 2) V := by
  have hcc : c⁻¹ = c * c := (eq_inv_of_mul_eq_one_left hc3).symm
  have hc3' : ∀ v, c (c (c v)) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hc3
    simpa using this
  have hq : ∀ v, c (c v) + c v + v = 0 := by
    intro v
    apply hfix
    rw [map_add, map_add, hc3', add_comm (c (c v)) (c v)]
    abel
  have ht2' : ∀ v, t (t v) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) ht2
    simpa using this
  have htc' : ∀ v, t (c v) = c (c (t v)) := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) htc
    rw [hcc] at this
    simpa using this
  set u : V →ₗ[ZMod 2] V := (t : V →ₗ[ZMod 2] V) - 1 with hu
  have huv : ∀ v, u v = t v + v := fun v => by
    simp [hu, sub_eq_add_neg, ZModModule.neg_eq_self]
  have hrange : LinearMap.range u = LinearMap.ker u := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, huv, huv, map_add, ht2']
      calc y + t y + (t y + y) = (y + y) + (t y + t y) := by abel
        _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]
    · intro hx
      rw [LinearMap.mem_ker, huv, add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hx
      refine ⟨c x, ?_⟩
      rw [huv, htc', hx]
      have := hq x
      rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at this
      exact this
  have hrn := LinearMap.finrank_range_add_finrank_ker u
  rw [← hrange] at hrn
  have : commSpace t = LinearMap.range u := rfl
  rw [this]
  omega

private theorem eq_zero_of_fixed_of_irreducible {H V : Type*} [Group H] [AddCommGroup V]
    [Module (ZMod 2) V] (φ : H →* (V ≃ₗ[ZMod 2] V)) (hφ : Function.Injective φ) {c : H}
    (hc1 : c ≠ 1)
    (hcn : ∀ m : H, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c⁻¹)
    (hirr : ∀ W : Submodule (ZMod 2) V, W ≠ ⊥ → W ≠ ⊤ → ¬ ∀ m : H, ∀ v ∈ W, φ m v ∈ W) :
    ∀ v, φ c v = v → v = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨v₀, hv₀, hv₀ne⟩ := hne
  set W : Submodule (ZMod 2) V := LinearMap.ker ((φ c : V →ₗ[ZMod 2] V) - 1) with hW
  have hmemW : ∀ v, v ∈ W ↔ φ c v = v := fun v => by
    simp [hW, LinearMap.mem_ker, sub_eq_zero]
  refine hirr W ?_ ?_ ?_
  · intro hbot
    have hmem : v₀ ∈ W := (hmemW v₀).mpr hv₀
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv₀ne hmem
  · intro htop
    apply hc1
    apply hφ
    rw [map_one]
    ext v
    exact (hmemW v).mp (htop ▸ Submodule.mem_top)
  · intro m v hv
    have hv' : φ c v = v := (hmemW v).mp hv
    have hCv : (φ c)⁻¹ v = v := by
      calc (φ c)⁻¹ v = (φ c)⁻¹ (φ c v) := by rw [hv']
        _ = v := by simp
    rw [hmemW]
    have key : ∀ D : V ≃ₗ[ZMod 2] V, D v = v → φ c * φ m = φ m * D → φ c (φ m v) = φ m v := by
      intro D hDv hCM
      calc φ c (φ m v) = (φ c * φ m) v := rfl
        _ = (φ m * D) v := by rw [hCM]
        _ = φ m (D v) := rfl
        _ = φ m v := by rw [hDv]
    rcases hcn m⁻¹ with h | h
    · refine key (φ c) hv' ?_
      have h' := congrArg φ h
      rw [inv_inv, map_mul, map_mul, map_inv] at h'
      calc φ c * φ m = φ m * ((φ m)⁻¹ * φ c * φ m) := by group
        _ = φ m * φ c := by rw [h']
    · refine key (φ c)⁻¹ hCv ?_
      have h' := congrArg φ h
      rw [inv_inv, map_mul, map_mul, map_inv, map_inv] at h'
      calc φ c * φ m = φ m * ((φ m)⁻¹ * φ c * φ m) := by group
        _ = φ m * (φ c)⁻¹ := by rw [h']

private theorem not_commute_of_class {H : Type*} [Group H] {X : Subgroup H} {E : Set H}
    (hX : X = Subgroup.closure E) {t c : H} (hcls : ∀ τ ∈ E, ∃ x ∈ X, τ = x * t * x⁻¹)
    (hnorm : ∀ x ∈ X, x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c⁻¹)
    (hcent : (∀ x ∈ X, x * c = c * x) → c = 1) (hc1 : c ≠ 1) : t * c ≠ c * t := by
  intro hcomm
  have hcommi : t * c⁻¹ = c⁻¹ * t := (Commute.inv_right (show Commute t c from hcomm)).eq
  have hEle : E ⊆ (Subgroup.centralizer ({c} : Set H) : Set H) := by
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := hcls τ hτ
    have hd : x⁻¹ * c * x = c ∨ x⁻¹ * c * x = c⁻¹ := by
      have := hnorm x⁻¹ (X.inv_mem hx)
      rwa [inv_inv] at this
    have htd : t * (x⁻¹ * c * x) = (x⁻¹ * c * x) * t := by
      rcases hd with h1 | h1
      · rw [h1]
        exact hcomm
      · rw [h1]
        exact hcommi
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * (x * t * x⁻¹) = x * ((x⁻¹ * y * x) * t) * x⁻¹ := by group
      _ = x * (t * (x⁻¹ * y * x)) * x⁻¹ := by rw [htd]
      _ = x * t * x⁻¹ * y := by group
  have hXle : X ≤ Subgroup.centralizer ({c} : Set H) := hX ▸ (Subgroup.closure_le _).mpr hEle
  exact hc1 (hcent fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hXle hx) c (Set.mem_singleton _)).symm)

private theorem hom_mul_eq_inv_mul {A B : Type*} [Group A] [Group B] (φ : A →* B) {a c : A}
    (h : a * c * a⁻¹ = c⁻¹) : φ a * φ c = (φ c)⁻¹ * φ a := by
  have h' := congrArg φ h
  rw [map_mul, map_mul, map_inv, map_inv] at h'
  exact mul_inv_eq_iff_eq_mul.mp h'

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem false_of_mem_Ebar12 {K : Type*} [Group K] (e : S.Mbar ≃* Equiv.Perm (Fin 3) × K)
    (hirr : ¬ S.IsReducible12) (hw : S.width ≠ 2) {g : G} {t : S.O}
    (hcent : S.CXbar12 g = ⊥)
    (hcls : ∀ τ ∈ S.Ebar12 g, ∃ x ∈ S.Xbar12 g, τ = x * t * x⁻¹) (htE : t ∈ S.Ebar12 g) :
    False := by
  obtain ⟨c, hc3, hc1, hcn⟩ := exists_threeCycle_normal e
  obtain ⟨φ, hφ⟩ : ∃ φ : S.Mbar →* (S.Qt ≃ₗ[ZMod 2] S.Qt),
      ∀ x, φ x = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ⟨S.O.subtype.comp S.Mbar.subtype, fun _ => rfl⟩
  have hφinj : Function.Injective φ := fun a b h =>
    Subtype.ext (Subtype.ext (by rw [hφ, hφ] at h; exact h))
  have hC3 : φ c * φ c * φ c = 1 := by
    rw [← pow_three', ← map_pow, hc3, map_one]
  have hfix : ∀ v, φ c v = v → v = 0 :=
    eq_zero_of_fixed_of_irreducible φ hφinj hc1 hcn fun W hbot htop hinv =>
      hirr ⟨W, hbot, htop, fun m v hv => by
        have := hinv ⟨S.ρ m, m, rfl⟩ v hv
        rwa [hφ] at this⟩
  set tM : S.Mbar := ⟨t, htE.1⟩ with htMdef
  have htinv : tM * c * tM⁻¹ = c⁻¹ := by
    rcases hcn tM with h | h
    · exfalso
      refine not_commute_of_class (X := S.Xbar12 g) (E := S.Ebar12 g) (t := t)
        (c := (c : S.O)) rfl hcls ?_ ?_ ?_ ?_
      · intro x hx
        rcases hcn ⟨x, Setting.Xbar12_le_Mbar hx⟩ with h1 | h1
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h1)
      · intro hcomm
        have hcmem : (c : S.O) ∈ S.CXbar12 g :=
          ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx⟩
        rw [hcent, Subgroup.mem_bot] at hcmem
        exact hcmem
      · exact fun h1 => hc1 (Subtype.ext h1)
      · rw [mul_inv_eq_iff_eq_mul] at h
        exact congrArg Subtype.val h
    · exact h
  obtain ⟨-, -, hT2, hdim, -⟩ := Setting.isTypeA_of_mem_Ebar12 htE
  have hmain := two_mul_finrank_commSpace_of_inverts (V := S.Qt) (c := φ c) (t := φ tM) hC3 hfix
    (by rw [hφ]; exact hT2) (hom_mul_eq_inv_mul φ htinv)
  have hdim' : finrank (ZMod 2) (commSpace (φ tM)) = 2 := by
    rw [hφ]
    exact hdim
  rw [hdim', S.finrank_Qt_eq_two_mul_width] at hmain
  exact hw (by omega)

theorem OrthData.noA2All_of_not_isReducible (hRI : RootInvolutionComponentsInput.{0})
    (O : OrthData S) (hirr : ¬ S.IsReducible) : S11.NoA2All S := by
  intro g haQ hne hA
  obtain ⟨α, hαL, -, hαA⟩ := hA
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  have hn : 4 ≤ S.width := O.four_le
  have htE := Setting.mem_Ebar12_of_mem_Lbar ht hαA
  have hcls := (S.timmesfeld_12_5 hRI haQ hne hn ht hαA).resolve_left hirr
  have hcent := (S.timmesfeld_12_8 haQ hne hn ht hαA).resolve_right hirr
  rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact false_of_mem_Ebar12 e hirr (by omega) hcent hcls htE
  · exact false_of_mem_Ebar12 e hirr (by omega) hcent hcls htE

end CFSG.GF2Type.Smith1980Orth
