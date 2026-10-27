module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinGen
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin

namespace QLift

@[expose] def Canon {X : Type*} [Group X] (K V : Subgroup X) : Prop :=
  V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set X) ∧ IsPGroup 2 V ∧
    ∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V

theorem Canon.comap {Y X : Type*} [Group Y] [Group X] (f : Y →* X) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) {K V : Subgroup X} (h : Canon K V) :
    Canon (K.comap f) (V.comap f) := by
  obtain ⟨hVK, hn, hV, hC⟩ := h
  refine ⟨Subgroup.comap_mono hVK, ?_, hV.comap_of_ker_isPGroup f hker, ?_⟩
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hn hy) (f z)
  · intro y hyK hyc
    refine hC (f y) hyK fun v hv => ?_
    obtain ⟨z, rfl⟩ := hf v
    have h1 := hyc z hv
    have h2 := congrArg f h1
    simpa only [map_mul] using h2

theorem mem_pCore_iff_apply {L : Type*} [Group L] (c : MulAut L) (x : L) :
    x ∈ CFSG.pCore 2 L ↔ c x ∈ CFSG.pCore 2 L := by
  have h := CFSG.pCore_map_iso 2 c
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := c.injective hyx
    rw [← this]
    exact hy

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G}

theorem exists_two_lifts (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf (R ⊓ L) L) {X : Type} [Group X] [Finite X] (f : ↥L →* X)
    (hf : Function.Surjective f) (hker : f.ker = CFSG.pCore 2 ↥L) {S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {K₀ V₀ K₁ V₁ : Subgroup X}
    (h₀ : Canon K₀ V₀) (h₁ : Canon K₁ V₁)
    (hinv₀ : ∀ α : MulAut X, S.map α.toMonoidHom = S → K₀.map α.toMonoidHom = K₀)
    (hinv₁ : ∀ α : MulAut X, S.map α.toMonoidHom = S → K₁.map α.toMonoidHom = K₁)
    (hgen : K₀ ⊔ K₁ = ⊤) :
    ∃ A B : Subgroup G, A ≤ L ∧ B ≤ L ∧ A ⊔ B = L ∧ R ≤ Subgroup.normalizer (A : Set G) ∧
      R ≤ Subgroup.normalizer (B : Set G) ∧ CharTwo A ∧ CharTwo B := by
  classical
  set P : Subgroup ↥L := (R ⊓ L).subgroupOf L with hPdef
  have hP2 : IsPGroup 2 P := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hPi : ¬ 2 ∣ P.index := hS.2.2
  obtain ⟨a, ha⟩ := exists_conj_comp_map_eq f hf hP2 hPi hS2 hSi
  set f' : ↥L →* X := (MulAut.conj a).toMonoidHom.comp f with hf'def
  have hf' : Function.Surjective f' := (MulAut.conj a).surjective.comp hf
  have hf'1 : ∀ x, f' x = 1 ↔ f x = 1 := fun x => by
    exact conj_eq_one_iff
  have hker' : f'.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext x
    exact hf'1 x
  have hker2 : IsPGroup 2 f'.ker := by
    rw [hker']
    exact CFSG.pCore_isPGroup
  have hPf : P.map f' = S := ha
  have hlift : ∀ (K : Subgroup X),
      (∀ α : MulAut X, S.map α.toMonoidHom = S → K.map α.toMonoidHom = K) →
      ∀ s (hs : s ∈ R), ∀ x : ↥L, x ∈ K.comap f' → conjAut L s (hRN hs) x ∈ K.comap f' := by
    intro K hK s hs x hx
    set c : MulAut ↥L := conjAut L s (hRN hs) with hc
    have hkerinv : ∀ y, f' y = 1 ↔ f' (c y) = 1 := fun y => by
      rw [hf'1, hf'1, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker]
      exact mem_pCore_iff_apply c y
    obtain ⟨α, hα⟩ := exists_descent hf' c hkerinv
    have hcP : P.map c.toMonoidHom = P := map_conjAut_subgroupOf_eq hRN hs
    have hαS : S.map α.toMonoidHom = S := by
      have h1 : S.map α.toMonoidHom = P.map (α.toMonoidHom.comp f') := by
        rw [← hPf, Subgroup.map_map]
      have h2 : α.toMonoidHom.comp f' = f'.comp c.toMonoidHom := by
        ext y
        exact (hα y).symm
      rw [h1, h2, ← Subgroup.map_map, hcP, hPf]
    have hKα := hK α hαS
    show f' (c x) ∈ K
    rw [hα x]
    have : α (f' x) ∈ K.map α.toMonoidHom := ⟨f' x, hx, rfl⟩
    rwa [hKα] at this
  have hc₀ := Canon.comap f' hf' hker2 h₀
  have hc₁ := Canon.comap f' hf' hker2 h₁
  refine ⟨(K₀.comap f').map L.subtype, (K₁.comap f').map L.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, Subgroup.comap_sup_eq f' _ _ hf', hgen, Subgroup.comap_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · exact le_normalizer_map_subtype hRN _ (hlift K₀ hinv₀)
  · exact le_normalizer_map_subtype hRN _ (hlift K₁ hinv₁)
  · exact charTwo_map_subtype_of_normal_pGroup hc₀.1 hc₀.2.1 hc₀.2.2.1 hc₀.2.2.2
  · exact charTwo_map_subtype_of_normal_pGroup hc₁.1 hc₁.2.1 hc₁.2.2.1 hc₁.2.2.2

end QLift

end CFSG.QuasithinUnique.Unc25G2
