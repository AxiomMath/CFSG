module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers

@[expose] def NormalizesRSub (d : TauCeti.ValidLieTypeIndex) (E : Subgroup (Cat d)) : Prop :=
  ∃ R : Subgroup (Cat d), R ≠ ⊥ ∧ IsPGroup d.1.characteristic R ∧
    ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R

@[expose] def RootInvariantHyperGeneration {G : Type*} [Group G] (N : Subgroup G) (r p : ℕ) :
    Prop :=
  ∀ A R : Subgroup G, A ≤ N → IsElementaryAbelian p ↥A → A ≠ ⊥ → R ≤ N →
    IsPGroup r ↥R → R ≠ ⊥ → A ≤ Subgroup.normalizer (R : Set G) →
    (⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      N ⊓ Subgroup.centralizer (B : Set G)) = N

theorem hyperGen_of_native {C G : Type*} [Group C] [Group G] {N : Subgroup G} (e : C ≃* N)
    {r p : ℕ} (hgen : RootInvariantHyperGeneration N r p) {E : Subgroup C}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hR : ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r ↥R ∧
      ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R) :
    HyperGen p (⊤ : Subgroup C) E := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hR
  let ι : C →* G := N.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιN : ∀ c, ι c ∈ N := fun c => (e c).2
  set A : Subgroup G := E.map ι with hA
  set R' : Subgroup G := R.map ι with hR'
  have hAN : A ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hR'N : R' ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hAel : IsElementaryAbelian p ↥A :=
    isElementaryAbelian_of_isElemAbelian (elementary_abelian_map p hE ι)
  have hA1 : A ≠ ⊥ := fun h => hE1 ((Subgroup.map_eq_bot_iff_of_injective E hι).mp h)
  have hR'p : IsPGroup r ↥R' :=
    hRp.of_surjective (ι.subgroupMap R) (ι.subgroupMap_surjective R)
  have hR'1 : R' ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R hι).mp h)
  have hnormC : ∀ c ∈ E, ∀ x : C, x ∈ R ↔ c * x * c⁻¹ ∈ R := by
    intro c hc x
    have hRc : R.map (MulAut.conj c).toMonoidHom = R := hRn c hc
    constructor
    · intro hx
      rw [← hRc]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hRc] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : c * y * c⁻¹ = c * x * c⁻¹ := hyx
        simpa using h2
      rw [← this]
      exact hy
  have hAnorm : A ≤ Subgroup.normalizer (R' : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c * x * c⁻¹, (hnormC c hc x).mp hx, by simp [map_mul]⟩
    · rintro ⟨y, hy, hyh⟩
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := (hnormC c⁻¹ (E.inv_mem hc) y).mp hy
        simpa using this
      · have h2 : ι y = ι c * h * (ι c)⁻¹ := hyh
        have h3 : h = (ι c)⁻¹ * ι y * ι c := by
          rw [h2]
          group
        rw [h3]
        simp [map_mul, map_inv]
  have hgenA := hgen A R' hAN hAel hA1 hR'N hR'p hR'1 hAnorm
  have hle : (⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      N ⊓ Subgroup.centralizer (B : Set G)) ≤ (hyperClosure p ⊤ E).map ι := by
    refine iSup₂_le fun B hB => iSup_le fun hBi => fun z hz => ?_
    obtain ⟨hzN, hzc⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨c, hc⟩ := e.surjective ⟨z, hzN⟩
    have hcz : ι c = z := congrArg Subtype.val hc
    refine ⟨c, Subgroup.subset_closure ⟨Subgroup.mem_top c, B.comap ι, ?_, ?_, ?_⟩, hcz⟩
    · intro y hy
      obtain ⟨y', hy', hyy'⟩ := hB hy
      rw [← hι hyy']
      exact hy'
    · rw [Subgroup.relIndex_comap]
      exact hBi
    · intro f hf
      have h1 := Subgroup.mem_centralizer_iff.1 hzc (ι f) hf
      apply hι
      rw [map_mul, map_mul, hcz]
      exact h1
  intro c _
  have hmem : ι c ∈ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      N ⊓ Subgroup.centralizer (B : Set G) := by
    rw [hgenA]
    exact hιN c
  obtain ⟨y, hy, hyc⟩ := hle hmem
  rw [← hι hyc]
  exact hy

@[expose] def SeitzExcParabolicHyperFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ d.1.characteristic → P d.1 →
    ∀ E : Subgroup (Cat d), IsElemAbelian p E → E ≠ ⊥ → NormalizesRSub d E → HyperGen p ⊤ E

theorem SeitzExcParabolicHyperFor.union {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : SeitzExcParabolicHyperFor P) (hQ : SeitzExcParabolicHyperFor Q) :
    SeitzExcParabolicHyperFor fun d => P d ∨ Q d := by
  intro d p hp hpd hd E hE hE1 hR
  rcases hd with h | h
  · exact hP d p hp hpd h E hE hE1 hR
  · exact hQ d p hp hpd h E hE hE1 hR

@[expose] def ExcCubeFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d → P d.1 →
    (∃ E₀ : Subgroup (Cat d), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3) →
    ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (NormalizesRSub d E ∨ HyperGen p ⊤ E)

theorem hyperExFor_of_cube {P : TauCeti.LieTypeIndex → Prop} (hP : SeitzExcParabolicHyperFor P)
    (hC : ExcCubeFor P) : HyperExFor fun d => P d.1 := by
  intro d p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hPd⟩
  obtain ⟨E, hE, hc, h⟩ := hC d p hp hp2 hpd hl hPd ⟨E₀, hE₀, hc₀⟩
  refine ⟨E, hE, hc, h.elim (fun hR => hP d p hp hpd hPd E hE ?_ hR) id⟩
  intro h0
  rw [h0, Subgroup.card_bot] at hc
  exact absurd hc.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'

theorem hyperExFor_or {P Q : TauCeti.ValidLieTypeIndex → Prop} (hP : HyperExFor P)
    (hQ : HyperExFor Q) : HyperExFor fun d => P d ∨ Q d :=
  SeitzHyperLieEx.of_cover (S₁ := fun d _ _ => P d) (S₂ := fun d _ _ => Q d)
    (fun _ _ _ h => h) hP hQ

theorem HyperExFor.mono {P Q : TauCeti.ValidLieTypeIndex → Prop} (h : ∀ d, Q d → P d)
    (hP : HyperExFor P) : HyperExFor Q := by
  intro d p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hQ⟩
  exact hP d p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, h d hQ⟩

end CFSG.LieType.SeitzGeneration
