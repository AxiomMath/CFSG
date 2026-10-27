module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Lines
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Partition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Gen
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender Equiv Subgroup

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U] {H : Type} [Group H]

theorem map_alternatingGroup_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (f : α ≃ β) :
    (alternatingGroup α).map (f.permCongrHom : Perm α ≃* Perm β).toMonoidHom =
      alternatingGroup β := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup] at hτ
    rw [Perm.mem_alternatingGroup]
    simpa [Equiv.permCongrHom_coe, Perm.sign_permCongr] using hτ
  · intro hσ
    refine ⟨f.permCongr.symm σ, ?_, f.permCongr.apply_symm_apply σ⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
    rw [Perm.mem_alternatingGroup] at hσ
    have := Perm.sign_permCongr f (f.permCongr.symm σ)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    exact hσ

omit [Finite U] in
theorem OrderThree.pow_three {T : U ≃ₗ[ZMod 2] U} (hT : OrderThree T) : T ^ 3 = 1 := by
  refine LinearEquiv.ext fun m => ?_
  show T (T (T m)) = m
  rw [hT.sq, hT.sq]
  have := OrderThree.add_self (T m)
  calc T m + (m + T m) = m + (T m + T m) := by abel
    _ = m := by rw [this, add_zero]

omit [Finite U] in
theorem normT_of_conj_mem [Nontrivial U] {σ : H →* (U ≃ₗ[ZMod 2] U)} {c : H}
    (hT : OrderThree (σ c)) (h : H) (hz : h⁻¹ * c * h ∈ Subgroup.zpowers c) :
    NormT (σ c) (σ h) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h3 : (σ c) ^ (3 : ℤ) = 1 := by exact_mod_cast hT.pow_three
  have hconj : (σ h)⁻¹ * σ c * σ h = (σ c) ^ k := by
    rw [← map_zpow, hk, map_mul, map_mul, map_inv]
  have hrel : ∀ m, σ c (σ h m) = σ h (((σ c) ^ k) m) := by
    intro m
    have := congrArg (fun x : U ≃ₗ[ZMod 2] U => (σ h) (x m)) hconj
    simp only [LinearEquiv.mul_apply] at this
    simpa using this
  rw [zpow_eq_zpow_emod k h3] at hrel
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hrel
    obtain ⟨m₀, hm₀⟩ := exists_ne (0 : U)
    apply hm₀
    refine hT.fix m₀ ?_
    have := hrel ((σ h)⁻¹ m₀)
    simpa using this
  · left
    intro m
    rw [hrel m, h1, zpow_one]
  · right
    intro m
    rw [hrel m, h2]
    show σ h (((σ c) ^ (2 : ℤ)) m) = σ h (σ c (σ c m))
    rw [zpow_two, LinearEquiv.mul_apply]

theorem map_eq_of_forall_mem' {W : Submodule (ZMod 2) U} {g : U ≃ₗ[ZMod 2] U}
    (hg : ∀ w ∈ W, g w ∈ W) : W.map (g : U →ₗ[ZMod 2] U) = W := by
  refine CFSG.QuasithinUnique.Setup.Offender.submodule_eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hg w hw
  · rw [Nat.card_congr (Submodule.equivMapOfInjective (g : U →ₗ[ZMod 2] U) g.injective W).toEquiv.symm]

open scoped Classical in
theorem six_point_of_lines (σ : H →* (U ≃ₗ[ZMod 2] U)) (L : Subgroup H) [L.Normal]
    (hL : CFSG.IsQuasisimple ↥L) (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hcent : Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype)
    {c : H} (hZc : (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers c)
    (hT : OrderThree (σ c)) (hU : Nat.card U = 64)
    (hsimple : ∀ W : Submodule (ZMod 2) U, Offender.IsInvariant σ L W → W = ⊥ ∨ W = ⊤) :
    ∃ θ : H →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥L).map L.subtype ∧
      L.map θ = alternatingGroup (Fin 6) := by
  have hnt : Nontrivial U := by
    rw [← Finite.one_lt_card_iff_nontrivial, hU]; norm_num
  have hcmem : c ∈ (Subgroup.center ↥L).map L.subtype := by rw [hZc]; exact Subgroup.mem_zpowers c
  have hNorm : ∀ g : H, NormT (σ c) (σ g) := by
    intro g
    refine normT_of_conj_mem hT g ?_
    rw [← hZc]
    obtain ⟨z, hz, hzc⟩ := hcmem
    have hlz : g⁻¹ * c * g ∈ L := by
      rw [← hzc]
      have := (Subgroup.mem_normalizer_iff.1 (mem_normalizer_of_normal L g⁻¹) (z : H)).1 z.2
      simpa using this
    refine ⟨⟨g⁻¹ * c * g, hlz⟩, ?_, rfl⟩
    show (⟨g⁻¹ * c * g, hlz⟩ : ↥L) ∈ Subgroup.center ↥L
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Subgroup.mem_center_iff.1 hz ⟨g * (y : H) * g⁻¹, (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_of_normal L g) y).1 y.2⟩
    have h2 : g * (y : H) * g⁻¹ * c = c * (g * (y : H) * g⁻¹) := by
      have := congrArg Subtype.val h1
      rw [← hzc]
      exact this
    apply Subtype.ext
    show (y : H) * (g⁻¹ * c * g) = g⁻¹ * c * g * y
    calc (y : H) * (g⁻¹ * c * g) = g⁻¹ * ((g * y * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * c * g * y := by group
  classical
  let _ : Fintype (Lines (σ c)) := Fintype.ofFinite _
  have hT3 : (σ c) ^ (3 : ℤ) = 1 := by exact_mod_cast hT.pow_three
  have hline_zpow : ∀ {W : Submodule (ZMod 2) U}, IsLine (σ c) W → ∀ (k : ℤ) {w : U}, w ∈ W →
      ((σ c) ^ k) w ∈ W := by
    intro W hW k w hw
    rw [zpow_eq_zpow_emod k hT3]
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0, zpow_zero]; exact hw
    · rw [h1, zpow_one]; exact hW.2 w hw
    · rw [h2, zpow_two, LinearEquiv.mul_apply]; exact hW.2 _ (hW.2 w hw)
  let ρ : H →* Equiv.Perm (Lines (σ c)) := linesAct σ hNorm
  have hZtriv : ∀ z ∈ (Subgroup.center ↥L).map L.subtype, ρ z = 1 := by
    intro z hz
    rw [hZc] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Equiv.ext fun W => Subtype.ext ?_
    show W.1.map ((σ (c ^ k) : U ≃ₗ[ZMod 2] U) : U →ₗ[ZMod 2] U) = W.1
    refine map_eq_of_forall_mem' fun w hw => ?_
    rw [map_zpow]
    exact hline_zpow W.2 k hw
  have hZ' : ∀ g : ↥L, g ∈ Subgroup.center ↥L → ρ g = 1 := fun g hg => hZtriv g ⟨g, hg, rfl⟩
  let φQ : (↥L ⧸ Subgroup.center ↥L) →* Equiv.Perm (Lines (σ c)) :=
    QuotientGroup.lift _ (ρ.comp L.subtype) (fun g hg => MonoidHom.mem_ker.2 (hZ' g hg))
  have hP : Nat.card (Lines (σ c)) = 21 := by
    have := card_lines hT
    omega
  have hsz : ∀ x : Lines (σ c), {z | ∃ q, φQ q x = z}.ncard = 6 ∨
      {z | ∃ q, φQ q x = z}.ncard = 10 ∨ {z | ∃ q, φQ q x = z}.ncard = 12 ∨
      {z | ∃ q, φQ q x = z}.ncard = 15 ∨ {z | ∃ q, φQ q x = z}.ncard = 20 := by
    intro x
    have hle : {z | ∃ q, φQ q x = z}.ncard ≤ 21 := by
      have := Set.ncard_le_card {z | ∃ q, φQ q x = z}
      rwa [hP] at this
    rcases orbit_card_cases' φQ eQ x with h | ⟨h6, hdvd, h8, h9, h18⟩
    · exfalso
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
      have hxa : x = a := by
        have : x ∈ {z | ∃ q, φQ q x = z} := ⟨1, by simp⟩
        rw [ha] at this
        exact this
      have hinv : Offender.IsInvariant σ L x.1 := by
        intro l hl w hw
        have hmem : φQ (QuotientGroup.mk ⟨l, hl⟩) x ∈ {z | ∃ q, φQ q x = z} := ⟨_, rfl⟩
        rw [ha] at hmem
        have hx' : φQ (QuotientGroup.mk ⟨l, hl⟩) x = x :=
          (Set.mem_singleton_iff.1 hmem).trans hxa.symm
        have h3 : (φQ (QuotientGroup.mk ⟨l, hl⟩) x).1 = x.1 := congrArg Subtype.val hx'
        have h4 : σ l w ∈ (φQ (QuotientGroup.mk ⟨l, hl⟩) x).1 := ⟨w, hw, rfl⟩
        rw [h3] at h4
        exact h4
      rcases hsimple x.1 hinv with hb | ht
      · have h5 := x.2.1
        rw [hb] at h5
        simp at h5
      · have h5 := x.2.1
        rw [ht, Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := U)).toEquiv, hU] at h5
        omega
    · generalize {z | ∃ q, φQ q x = z}.ncard = n at *
      interval_cases n <;> omega
  obtain ⟨x, y, hx, hy, hcov⟩ := partition_six_fifteen (classSystem_orbit φQ) hP hsz
  have horb : ∀ z : Lines (σ c), orb ρ L z = {w | ∃ q, φQ q z = w} := by
    intro z
    ext w
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g.1, g.2, rfl⟩
  have hperf : Group.IsPerfect ↥L := hL.1
  obtain ⟨θ', hθ'1, hθ'2, hθ'3⟩ := six_point_abstract ρ L eQ hZ'
    (by rw [horb]; exact hx) (by rw [horb]; exact hy) (fun w => by rw [horb, horb]; exact hcov w)
  have hcard : Fintype.card (orb ρ L x) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, horb]; exact hx
  let f : orb ρ L x ≃ Fin 6 := Fintype.equivFinOfCardEq hcard
  let toN : H →* ↥(Subgroup.normalizer (L : Set H)) :=
    MonoidHom.codRestrict (MonoidHom.id H) _ (fun h => mem_normalizer_of_normal L h)
  let θ : H →* Equiv.Perm (Fin 6) := (f.permCongrHom : _ ≃* _).toMonoidHom.comp (θ'.comp toN)
  refine ⟨θ, ?_, ?_⟩
  · ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : θ' (toN h) = 1 := f.permCongrHom.injective (by rw [map_one]; exact h1)
      have h3 := hθ'2 (toN h) h2
      rw [← hcent]
      exact h3
    · intro hh
      have h2 : θ' (toN h) = 1 := by
        refine Equiv.ext fun z => Subtype.ext ?_
        rw [hθ'1]
        show ρ h z.1 = z.1
        rw [hZtriv h hh]
        rfl
      show f.permCongrHom (θ' (toN h)) = 1
      rw [h2, map_one]
  · have h1 : L.map toN = L.subgroupOf (Subgroup.normalizer (L : Set H)) := by
      ext y
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact hl
      · intro hy
        exact ⟨y.1, hy, rfl⟩
    show L.map ((f.permCongrHom : _ ≃* _).toMonoidHom.comp (θ'.comp toN)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, h1, hθ'3]
    exact map_alternatingGroup_permCongr f

end CFSG.QuasithinUnique.Setup.X3
