module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Defs
public import CFSG.Quasithin.Background.A1bKrullSchmidt
import all CFSG.Quasithin.Background.A1bKrullSchmidt

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

open CFSG.Quasithin

namespace Sigma3Dec

abbrev SL22 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

theorem sl22_center : ∀ x : SL22, (∀ y : SL22, x * y = y * x) → x = 1 := by decide

theorem sl22_cent3 : ∀ s : SL22, (∀ e : SL22, e ^ 3 = 1 → s * e * s⁻¹ = e) → s ^ 3 = 1 := by
  decide

theorem sl22_exists_three : ∃ t : SL22, t ^ 3 = 1 ∧ t ≠ 1 := by decide

theorem sl22_three_mem : ∀ t : SL22, t ^ 3 = 1 → t ≠ 1 → ∀ x : SL22, x ≠ 1 →
    t = x ∨ t = x⁻¹ ∨ ∃ u v : SL22, t = (u * x * u⁻¹) * (v * x * v⁻¹) := by decide

theorem isIndecomposableGroup_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : IsIndecomposableGroup B) : IsIndecomposableGroup A := by
  obtain ⟨hBn, hB2⟩ := hB
  refine ⟨e.toEquiv.nontrivial, fun C D hC hD hCD hsup => ?_⟩
  have hCn : (C.map e.toMonoidHom).Normal := hC.map e.toMonoidHom e.surjective
  have hDn : (D.map e.toMonoidHom).Normal := hD.map e.toMonoidHom e.surjective
  have h1 : C.map e.toMonoidHom ⊓ D.map e.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf _ _ _ e.injective, hCD, Subgroup.map_bot]
  have h2 : C.map e.toMonoidHom ⊔ D.map e.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]
  rcases hB2 _ _ hCn hDn h1 h2 with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)
  · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)

theorem isIndecomposableGroup_sl22 : IsIndecomposableGroup SL22 := by
  obtain ⟨t, ht3, ht1⟩ := sl22_exists_three
  refine ⟨⟨⟨t, 1, ht1⟩⟩, fun B C hB hC hBC _ => ?_⟩
  have key : ∀ D : Subgroup SL22, D.Normal → D ≠ ⊥ → t ∈ D := by
    intro D hD hne
    obtain ⟨⟨x, hxD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    rcases sl22_three_mem t ht3 ht1 x hx1' with h | h | ⟨u, v, h⟩
    · rw [h]; exact hxD
    · rw [h]; exact D.inv_mem hxD
    · rw [h]; exact D.mul_mem (hD.conj_mem x hxD u) (hD.conj_mem x hxD v)
  by_contra hcon
  push Not at hcon
  have h1 := key B hB hcon.1
  have h2 := key C hC hcon.2
  have : t ∈ B ⊓ C := ⟨h1, h2⟩
  rw [hBC, Subgroup.mem_bot] at this
  exact ht1 this

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : ∀ y : B, (∀ z, y * z = z * y) → y = 1) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h : e z = 1 := hB (e z) fun w => by
    have h1 := congrArg e (Subgroup.mem_center_iff.1 hz (e.symm w))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  exact e.map_eq_one_iff.1 h

theorem isIndexedDirectProduct_range_mulSingle {ι : Type*} [Finite ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Group (F i)] :
    IsIndexedDirectProduct (fun i : ι => (MonoidHom.mulSingle F i).range) where
  normal i := ⟨by
    rintro _ ⟨a, rfl⟩ g
    refine ⟨g i * a * (g i)⁻¹, ?_⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]⟩
  independent := by
    intro i
    rw [Subgroup.disjoint_def]
    rintro x ⟨a, rfl⟩ hx
    have hle : (⨆ (j : ι) (_ : j ≠ i), (MonoidHom.mulSingle F j).range) ≤
        (Pi.evalMonoidHom F i).ker := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨b, rfl⟩
      simp [hj]
    have h1 := hle hx
    rw [MonoidHom.mem_ker] at h1
    simp at h1
    simp [h1]
  iSup_eq_top := by
    rw [eq_top_iff]
    intro x _
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro i
    exact Subgroup.mem_iSup_of_mem i ⟨x i, rfl⟩

section Product

variable {𝔄 : Type*} [Group 𝔄]

abbrev ExtProd (I : Finset (Subgroup 𝔄)) : Type _ := ∀ i : ↥I, ↥(i.1 : Subgroup 𝔄)

variable {I : Finset (Subgroup 𝔄)}

theorem pairwise_commute (hI : IsSigma3Family I) :
    Pairwise fun i j : ↥I => ∀ x y : 𝔄, x ∈ i.1 → y ∈ j.1 → Commute x y := by
  intro i j hij x y hx hy
  exact hI.comm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy

theorem iSupIndep_fam (hI : IsSigma3Family I) :
    iSupIndep (fun i : ↥I => (i.1 : Subgroup 𝔄)) := by
  intro i
  refine Disjoint.mono_right ?_ (disjoint_iff.2 (hI.indep i.1 i.2))
  refine iSup₂_le fun j hj => ?_
  exact le_iSup₂_of_le j.1 j.2
    (le_iSup (fun _ : j.1 ≠ i.1 => (j.1 : Subgroup 𝔄)) (fun h => hj (Subtype.ext h)))

@[expose] def mulMap (hI : IsSigma3Family I) : ExtProd I →* 𝔄 :=
  Subgroup.noncommPiCoprod (H := fun i : ↥I => (i.1 : Subgroup 𝔄)) (pairwise_commute hI)

theorem mulMap_mulSingle [DecidableEq ↥I] (hI : IsSigma3Family I) (i : ↥I)
    (a : ↥(i.1 : Subgroup 𝔄)) : mulMap hI (Pi.mulSingle i a) = (a : 𝔄) :=
  Subgroup.noncommPiCoprod_mulSingle i a

theorem mulMap_injective (hI : IsSigma3Family I) : Function.Injective (mulMap hI) :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep (iSupIndep_fam hI)

theorem mulMap_range (hI : IsSigma3Family I) : (mulMap hI).range = ⨆ L ∈ I, L := by
  rw [mulMap, Subgroup.noncommPiCoprod_range]
  rw [iSup_subtype']

theorem mem_J_iff (hI : IsSigma3Family I) {x : 𝔄} :
    x ∈ (⨆ L ∈ I, L : Subgroup 𝔄) ↔ ∃ p : ExtProd I, mulMap hI p = x := by
  rw [← mulMap_range hI]
  exact MonoidHom.mem_range

abbrev factor (I : Finset (Subgroup 𝔄)) [DecidableEq ↥I] (i : ↥I) :
    Subgroup (ExtProd I) :=
  (MonoidHom.mulSingle (fun j : ↥I => ↥(j.1 : Subgroup 𝔄)) i).range

theorem center_extProd (hI : IsSigma3Family I) : Subgroup.center (ExtProd I) = ⊥ := by
  rw [Subgroup.center_pi, Subgroup.pi_eq_bot_iff]
  intro i
  obtain ⟨ε⟩ := hI.sigma3 i.1 i.2
  exact center_eq_bot_of_mulEquiv ε sl22_center

section Finite

variable [Finite 𝔄]

theorem exists_aut_conj (hI : IsSigma3Family I) {g : 𝔄}
    (hg : g ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup 𝔄) : Set 𝔄)) :
    ∃ α : MulAut (ExtProd I), ∀ x, mulMap hI (α x) = g * mulMap hI x * g⁻¹ := by
  have hmem : ∀ x : ExtProd I, ∃ y : ExtProd I, mulMap hI y = g * mulMap hI x * g⁻¹ := by
    intro x
    have h1 : mulMap hI x ∈ (⨆ L ∈ I, L : Subgroup 𝔄) := (mem_J_iff hI).2 ⟨x, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 hg _).1 h1
    exact (mem_J_iff hI).1 h2
  choose f hf using hmem
  have hinj := mulMap_injective hI
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    apply hinj
    simp only [hf, map_mul]
    group
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply hinj
    have := congrArg (mulMap hI) hxy
    rw [hf, hf] at this
    simpa using this
  let F : ExtProd I →* ExtProd I := MonoidHom.mk' f hmul
  exact ⟨MulEquiv.ofBijective F (Finite.injective_iff_bijective.1 hfinj), hf⟩

theorem conjBy_mem_aux (hI : IsSigma3Family I) {g : 𝔄}
    (hg : g ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup 𝔄) : Set 𝔄)) {L : Subgroup 𝔄}
    (hL : L ∈ I) : conjBy g L ∈ I := by
  classical
  obtain ⟨α, hα⟩ := exists_aut_conj hI hg
  have hind : ∀ i : ↥I, IsIndecomposableGroup (factor I i) := by
    intro i
    obtain ⟨ε⟩ := hI.sigma3 i.1 i.2
    exact isIndecomposableGroup_of_mulEquiv
      ((MonoidHom.ofInjective (f := MonoidHom.mulSingle (fun j : ↥I => ↥(j.1 : Subgroup 𝔄)) i)
        (Pi.mulSingle_injective (M := fun j : ↥I => ↥(j.1 : Subgroup 𝔄)) i)).symm.trans ε)
      isIndecomposableGroup_sl22
  obtain ⟨τ, hτ⟩ := krull_schmidt_aut_permutes
    (isIndexedDirectProduct_range_mulSingle (F := fun j : ↥I => ↥(j.1 : Subgroup 𝔄))) hind α
  have hcenter := center_extProd hI
  have hmap : ∀ i : ↥I, (factor I i).map α.toMonoidHom = factor I (τ i) := by
    intro i
    have := hτ i
    rwa [hcenter, sup_bot_eq, sup_bot_eq] at this
  have key : conjBy g L = ((τ ⟨L, hL⟩ : ↥I) : Subgroup 𝔄) := by
    set i : ↥I := ⟨L, hL⟩ with hi
    ext x
    rw [mem_conjBy]
    constructor
    · intro hx
      have hy : (Pi.mulSingle i (⟨g⁻¹ * x * g, hx⟩ : ↥(i.1 : Subgroup 𝔄)) : ExtProd I) ∈
          factor I i := ⟨_, rfl⟩
      have hy' : α (Pi.mulSingle i (⟨g⁻¹ * x * g, hx⟩ : ↥(i.1 : Subgroup 𝔄))) ∈
          factor I (τ i) := by
        rw [← hmap i]
        exact ⟨_, hy, rfl⟩
      obtain ⟨b, hb⟩ := hy'
      have h1 := hα (Pi.mulSingle i (⟨g⁻¹ * x * g, hx⟩ : ↥(i.1 : Subgroup 𝔄)))
      have hb' : Pi.mulSingle (τ i) b =
          α (Pi.mulSingle i (⟨g⁻¹ * x * g, hx⟩ : ↥(i.1 : Subgroup 𝔄))) := hb
      rw [← hb', mulMap_mulSingle, mulMap_mulSingle] at h1
      have h2 : (b : 𝔄) = x := by
        rw [h1]
        group
      rw [← h2]
      exact b.2
    · intro hx
      have hy : (Pi.mulSingle (τ i) (⟨x, hx⟩ : ↥((τ i).1 : Subgroup 𝔄)) : ExtProd I) ∈
          factor I (τ i) := ⟨_, rfl⟩
      rw [← hmap i] at hy
      obtain ⟨y, ⟨a, rfl⟩, hay⟩ := hy
      have hay' : α (Pi.mulSingle i a) =
          Pi.mulSingle (τ i) (⟨x, hx⟩ : ↥((τ i).1 : Subgroup 𝔄)) := hay
      have h1 := hα (Pi.mulSingle i a)
      rw [hay', mulMap_mulSingle, mulMap_mulSingle] at h1
      have h1' : x = g * (a : 𝔄) * g⁻¹ := h1
      have h2 : g⁻¹ * x * g = (a : 𝔄) := by
        rw [h1']
        group
      rw [h2]
      exact a.2
  rw [key]
  exact (τ ⟨L, hL⟩).2

end Finite

theorem eq_one_aux (hI : IsSigma3Family I) {s : 𝔄} (hsJ : s ∈ (⨆ L ∈ I, L : Subgroup 𝔄)) {k : ℕ}
    (hs : s ^ (2 ^ k) = 1)
    (hc : ∀ e ∈ (⨆ L ∈ I, L : Subgroup 𝔄), e ^ 3 = 1 → s * e * s⁻¹ = e) : s = 1 := by
  classical
  obtain ⟨p, rfl⟩ := (mem_J_iff hI).1 hsJ
  have hp : p ^ (2 ^ k) = 1 := mulMap_injective hI (by rw [map_pow, hs, map_one])
  suffices hp1 : p = 1 by rw [hp1, map_one]
  funext i
  obtain ⟨ε⟩ := hI.sigma3 i.1 i.2
  have h1 : (ε (p i)) ^ (2 ^ k) = 1 := by
    have h := congrFun hp i
    rw [Pi.pow_apply, Pi.one_apply] at h
    rw [← map_pow, h, map_one]
  have h2 : ∀ e : SL22, e ^ 3 = 1 → ε (p i) * e * (ε (p i))⁻¹ = e := by
    intro e he
    have ha3 : (ε.symm e) ^ 3 = 1 := by rw [← map_pow, he, map_one]
    have hJa : ((ε.symm e : ↥(i.1 : Subgroup 𝔄)) : 𝔄) ∈ (⨆ L ∈ I, L : Subgroup 𝔄) :=
      (mem_J_iff hI).2 ⟨Pi.mulSingle i (ε.symm e), mulMap_mulSingle hI i _⟩
    have ha3' : ((ε.symm e : ↥(i.1 : Subgroup 𝔄)) : 𝔄) ^ 3 = 1 := by
      simpa using congrArg Subtype.val ha3
    have h3 := hc _ hJa ha3'
    have h4 : p * Pi.mulSingle i (ε.symm e) * p⁻¹ = Pi.mulSingle i (ε.symm e) := by
      apply mulMap_injective hI
      rw [map_mul, map_mul, map_inv, mulMap_mulSingle]
      exact h3
    have h5 := congrFun h4 i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at h5
    have h6 := congrArg ε h5
    simpa using h6
  have h3 : (ε (p i)) ^ 3 = 1 := sl22_cent3 _ h2
  have h4 : ε (p i) = 1 := by
    have := pow_gcd_eq_one.2 ⟨h3, h1⟩
    rwa [Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2), pow_one] at this
  exact ε.map_eq_one_iff.1 h4

theorem conj_eq_aux (hI : IsSigma3Family I) {g : 𝔄}
    (hg : ∀ L ∈ I, ∀ a ∈ L, a ^ 3 = 1 → g * a * g⁻¹ = a) :
    ∀ e ∈ (⨆ L ∈ I, L : Subgroup 𝔄), e ^ 3 = 1 → g * e * g⁻¹ = e := by
  classical
  intro e he he3
  obtain ⟨p, rfl⟩ := (mem_J_iff hI).1 he
  have hp3 : p ^ 3 = 1 := mulMap_injective hI (by rw [map_pow, he3, map_one])
  have hS : p ∈ (Subgroup.centralizer ({g} : Set 𝔄)).comap (mulMap hI) := by
    refine Subgroup.pi_mem_of_mulSingle_mem p fun i => ?_
    have h3 : ((p i : ↥(i.1 : Subgroup 𝔄)) : 𝔄) ^ 3 = 1 := by
      have h := congrFun hp3 i
      rw [Pi.pow_apply, Pi.one_apply] at h
      simpa using congrArg Subtype.val h
    have h4 := hg i.1 i.2 _ (p i).2 h3
    rw [mul_inv_eq_iff_eq_mul] at h4
    rw [Subgroup.mem_comap, mulMap_mulSingle, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h4
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hS
  exact mul_inv_eq_iff_eq_mul.2 (hS g rfl)

end Product

end Sigma3Dec

variable {𝔄 : Type*} [Group 𝔄] [Finite 𝔄]

theorem IsSigma3Family.conjBy_mem {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {g : 𝔄}
    (hg : g ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup 𝔄) : Set 𝔄)) {L : Subgroup 𝔄}
    (hL : L ∈ I) : conjBy g L ∈ I :=
  Sigma3Dec.conjBy_mem_aux hI hg hL

theorem IsSigma3Family.eq_one_of_two_pow_of_centralizes {I : Finset (Subgroup 𝔄)}
    (hI : IsSigma3Family I) {s : 𝔄} (hsJ : s ∈ (⨆ L ∈ I, L : Subgroup 𝔄)) {k : ℕ}
    (hs : s ^ (2 ^ k) = 1)
    (hc : ∀ e ∈ (⨆ L ∈ I, L : Subgroup 𝔄), e ^ 3 = 1 → s * e * s⁻¹ = e) : s = 1 :=
  Sigma3Dec.eq_one_aux hI hsJ hs hc

theorem IsSigma3Family.conj_eq_of_components {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I)
    {g : 𝔄} (hg : ∀ L ∈ I, ∀ a ∈ L, a ^ 3 = 1 → g * a * g⁻¹ = a) :
    ∀ e ∈ (⨆ L ∈ I, L : Subgroup 𝔄), e ^ 3 = 1 → g * e * g⁻¹ = e :=
  Sigma3Dec.conj_eq_aux hI hg

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3
