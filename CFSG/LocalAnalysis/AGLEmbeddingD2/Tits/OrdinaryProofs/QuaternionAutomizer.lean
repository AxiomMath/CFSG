module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer

public section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.RankThree.PartTwo

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem autIn_congr_left {A B : Subgroup G} (X : Subgroup G) (h : A = B) :
    Nonempty (Sec4.autIn A X ≃* Sec4.autIn B X) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem autIn_congr_right (A : Subgroup G) {X Y : Subgroup G} (h : X = Y) :
    Nonempty (Sec4.autIn A X ≃* Sec4.autIn A Y) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem autIn_map_equiv (f : G →* H) (hf : Function.Injective f) (K X : Subgroup G) :
    Nonempty (Sec4.autIn K X ≃* Sec4.autIn (K.map f) (X.map f)) := by
  let eX : X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf
  let c : MulAut X ≃* MulAut ↥(X.map f) := MulAut.congr eX
  have mapNorm : ∀ {h : G}, h ∈ Subgroup.normalizer (X : Set G) →
      f h ∈ Subgroup.normalizer ((X.map f : Subgroup H) : Set H) := by
    intro h hN
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨h * x * h⁻¹, (hN x).mp hx, ?_⟩
      simp [map_mul, map_inv, mul_assoc]
    · rintro ⟨x, hx, hxy⟩
      have hconj : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      have hx' : h⁻¹ * x * h ∈ X := (hN (h⁻¹ * x * h)).mpr (by rw [hconj]; exact hx)
      have e : f (h⁻¹ * x * h) = (f h)⁻¹ * f x * f h := by
        simp [map_mul, map_inv, mul_assoc]
      refine ⟨h⁻¹ * x * h, hx', ?_⟩
      rw [e, hxy]
      group
  have backNorm : ∀ {h : G}, f h ∈ Subgroup.normalizer ((X.map f : Subgroup H) : Set H) →
      h ∈ Subgroup.normalizer (X : Set G) := by
    intro h hN
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro x
    rw [← Subgroup.mem_map_iff_mem hf, ← Subgroup.mem_map_iff_mem hf]
    have e : f (h * x * h⁻¹) = f h * f x * (f h)⁻¹ := by simp [map_mul, map_inv, mul_assoc]
    rw [e]
    exact hN (f x)
  have hconj : ∀ (h : G) (hN : h ∈ Subgroup.normalizer (X : Set G)),
      c (X.normalizerMonoidHom ⟨h, hN⟩) =
        (X.map f).normalizerMonoidHom ⟨f h, mapNorm hN⟩ := by
    intro h hN
    ext ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hsymm : eX.symm ⟨f x, hy⟩ = ⟨x, hx⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have key : c (X.normalizerMonoidHom ⟨h, hN⟩) ⟨f x, hy⟩ =
        eX (X.normalizerMonoidHom ⟨h, hN⟩ ⟨x, hx⟩) := by
      rw [← hsymm]
      rfl
    rw [key]
    simp only [eX, Subgroup.coe_equivMapOfInjective_apply]
    simp only [Sec4.normalizerMonoidHom_apply_coe, map_mul, map_inv]
  have hset : (Sec4.autIn K X).map c.toMonoidHom = Sec4.autIn (K.map f) (X.map f) := by
    ext σ'
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨h, hN, hK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      rw [MulEquiv.coe_toMonoidHom, hconj h hN]
      exact Sec4.mem_autIn_iff.mpr ⟨f h, mapNorm hN, Subgroup.mem_map_of_mem f hK, rfl⟩
    · intro hσ'
      obtain ⟨h', hN', hK', rfl⟩ := Sec4.mem_autIn_iff.mp hσ'
      obtain ⟨h, hK, rfl⟩ := Subgroup.mem_map.mp hK'
      have hN : h ∈ Subgroup.normalizer (X : Set G) := backNorm hN'
      refine ⟨X.normalizerMonoidHom ⟨h, hN⟩, Sec4.mem_autIn_iff.mpr ⟨h, hN, hK, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hconj h hN]
  exact ⟨(Subgroup.equivMapOfInjective _ c.toMonoidHom c.injective).trans
    (MulEquiv.subgroupCongr hset)⟩

end Transport

theorem exists_quaternion_le_automizer
    {X : Type} [Group X] [Finite X] {K : Subgroup X} (hK : CFSG.AGLEmbedding.IsLinThreeFour K)
    {E : Subgroup X} (hEK : E ≤ K) (hE : Nat.card E = 9) :
    ∃ Q : Subgroup (MulAut E),
      Q ≤ (K.subgroupOf (Subgroup.normalizer (E : Set X))).map E.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  obtain ⟨φ⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let E' : Subgroup K := E.subgroupOf K
  have hE' : Nat.card E' = 9 := by
    rw [← hE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  let E'' : Subgroup (projectiveSL 3 (GaloisField 2 2)) := E'.map φ.toMonoidHom
  have hE'' : Nat.card E'' = 9 := by
    rw [← hE']
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E' φ.toMonoidHom φ.injective).toEquiv).symm
  obtain ⟨e9⟩ := CFSG.RankThree.PartTwo.KFacts.L34.nonempty_autIn_of_card_eq_nine hk4 hE''
  obtain ⟨a1⟩ := autIn_map_equiv φ.toMonoidHom φ.injective ⊤ E'
  have htop : (⊤ : Subgroup K).map φ.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ φ.surjective
  obtain ⟨a1'⟩ := autIn_congr_left (G := projectiveSL 3 (GaloisField 2 2)) E'' htop
  obtain ⟨b1⟩ := autIn_map_equiv K.subtype (Subgroup.subtype_injective K) ⊤ E'
  have hKtop : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hEmap : E'.map K.subtype = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact ⟨⟨x, hEK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨b2⟩ := autIn_congr_left (G := X) (E'.map K.subtype) hKtop
  obtain ⟨b3⟩ := autIn_congr_right K hEmap
  refine ⟨Sec4.autIn K E, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨n, hN, hKn, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact Subgroup.mem_map.mpr ⟨⟨n, hN⟩, Subgroup.mem_subgroupOf.mpr hKn, rfl⟩
  · exact ⟨((b1.trans (b2.trans b3)).symm).trans ((a1.trans a1').trans e9)⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
