module

public import CFSG.CGT.Foote81L6.Normalizer.GBasic
public import CFSG.CGT.Foote81L6.Normalizer.Hyp
public import CFSG.CGT.Foote81L6.TStruct.Lemma2ThreeN

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

section Inputs

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ}

@[expose] def TvInput (D : FooteCore G T m n) : Prop :=
  ∀ E : Subgroup G, IsE64 T E → ∀ x c : G, x ∈ T → x ∈ normalizer (E : Set G) →
    (∀ v ∈ E, x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * c) → (∃ v ∈ E, x * v * x⁻¹ ≠ v) →
    (∃ α ∈ D.A, x * α⁻¹ ∈ E) ∨ (∃ β ∈ D.B₀, x * β⁻¹ ∈ E) ∨ (∃ β ∈ D.B₁, x * β⁻¹ ∈ E)

@[expose] def QuotInput (T : Subgroup G) : Prop :=
  ∀ E : Subgroup G, IsE64 T E →
    Nonempty (↥(T ⊓ normalizer (E : Set G)) ⧸ E.subgroupOf (T ⊓ normalizer (E : Set G)) ≃*
      DihedralGroup 4)

@[expose] def SwapInput (D : FooteCore G T m n) : Prop :=
  ∀ E : Subgroup G, IsE64 T E → ∀ d₀ d₁ τ : G,
    d₀ ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G) → d₀ ∉ E →
    d₁ ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G) → d₁ ∉ E →
    τ ∈ T ⊓ normalizer (E : Set G) → τ ∉ (D.B₀ ⊔ D.B₁) ⊔ E → τ * d₀ * τ⁻¹ * d₁⁻¹ ∈ E

@[expose] def SylNInput (T : Subgroup G) : Prop :=
  ∀ E : Subgroup G, IsE64 T E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
    (Q : Subgroup _) = T.subgroupOf (normalizer (E : Set G))

end Inputs

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n) {F : Subgroup G} [IsMulCommutative ↥F]
  (hF : IsE64 (T : Subgroup G) F)

include D hF in
theorem π_eq_one_iff_mem (x : ↥(normalizer (F : Set G))) (hxT : (x : G) ∈ (T : Subgroup G)) :
    NBar.π F x = 1 ↔ (x : G) ∈ F := by
  constructor
  · intro h
    by_contra hxF
    exact ρ_ne_one_of_not_mem D hF x hxT hxF (by rw [h, map_one])
  · intro hxF
    exact NBar.π_eq_one_of_mem F (fun u hu v hv =>
      congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)) x hxF

include D hF in
theorem nonempty_sylowImage_equiv (hquot : QuotInput (T : Subgroup G))
    {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G))) :
    Nonempty (↥(NBar.sylowImage F Q : Subgroup (NBar.Q F)) ≃* DihedralGroup 4) := by
  obtain ⟨ψ⟩ := hquot F hF
  set H := (T : Subgroup G) ⊓ normalizer (F : Set G) with hH
  set f : ↥H →* NBar.Q F :=
    (NBar.π F).comp (Subgroup.inclusion (inf_le_right : H ≤ normalizer (F : Set G))) with hf
  have hker : f.ker = F.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply]
    exact π_eq_one_iff_mem D hF _ (mem_inf.1 h.2).1
  have hrange : f.range = (NBar.sylowImage F Q : Subgroup (NBar.Q F)) := by
    rw [NBar.coe_sylowImage]
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨Subgroup.inclusion inf_le_right h, ?_, rfl⟩
      show _ ∈ (Q : Subgroup ↥(normalizer (F : Set G)))
      rw [hQ, mem_subgroupOf]
      exact (mem_inf.1 h.2).1
    · rintro ⟨yN, hyQ, rfl⟩
      have hyQ' : yN ∈ (Q : Subgroup ↥(normalizer (F : Set G))) := hyQ
      rw [hQ, mem_subgroupOf] at hyQ'
      exact ⟨⟨yN, mem_inf.2 ⟨hyQ', yN.2⟩⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans ψ))⟩

theorem π_mem_sylowImage {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G)))
    (x : ↥(normalizer (F : Set G))) (hxT : (x : G) ∈ (T : Subgroup G)) :
    NBar.π F x ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)) := by
  rw [NBar.coe_sylowImage]
  refine ⟨x, ?_, rfl⟩
  show x ∈ (Q : Subgroup ↥(normalizer (F : Set G)))
  rw [hQ, mem_subgroupOf]
  exact hxT

theorem conj_d₀_eq_d₁ (hswap : SwapInput D) {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)
    (τ : ↥(normalizer (F : Set G))) (hτT : (τ : G) ∈ (T : Subgroup G)) (hτ₁ : (τ : G) ∉ D.T₁) :
    NBar.π F τ * NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ * (NBar.π F τ)⁻¹ =
      NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ := by
  have hτE : (τ : G) ∉ (D.B₀ ⊔ D.B₁) ⊔ F := fun h =>
    hτ₁ (sup_le D.B₀B₁_le_T₁ (D.le_T₁_of_isE64 hF) h)
  have h := hswap F hF d₀ d₁ τ hd₀ hd₀F hd₁ hd₁F (mem_inf.2 ⟨hτT, τ.2⟩) hτE
  set d₀N : ↥(normalizer (F : Set G)) := ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩
  set d₁N : ↥(normalizer (F : Set G)) := ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  refine (π_eq_of_inv_mul_mem _ _ ?_).symm
  have hd₁N := d₁N.2
  have e : (d₁N : G)⁻¹ * ((τ * d₀N * τ⁻¹ : ↥(normalizer (F : Set G))) : G) =
      (d₁N : G)⁻¹ * ((τ : G) * d₀ * (τ : G)⁻¹ * d₁⁻¹) * (d₁N : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, d₀N, d₁N]
    group
  rw [e]
  have := (mem_normalizer_iff.1 (inv_mem hd₁N) _).1 h
  simpa only [inv_inv] using this

theorem fusion_mem (hTv : TvInput D) {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G))) {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)
    (y : NBar.Q F) (hy : y ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)))
    (hconj : IsConj (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) y) :
    y = NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ ∨
      y = NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ := by
  classical
  have hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)
  obtain ⟨htv₀, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀ hd₀F
  rw [NBar.coe_sylowImage] at hy
  obtain ⟨yN, hyQ, rfl⟩ := hy
  have hyT : (yN : G) ∈ (T : Subgroup G) := by
    have hyQ' : yN ∈ (Q : Subgroup ↥(normalizer (F : Set G))) := hyQ
    rw [hQ, mem_subgroupOf] at hyQ'
    exact hyQ'
  obtain ⟨gbar, hg⟩ := isConj_iff.1 hconj
  obtain ⟨gN, rfl⟩ := NBar.π_surjective F gbar
  set d₀N : ↥(normalizer (F : Set G)) := ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩
  have hρy : NBar.ρ F (NBar.π F yN) =
      NBar.ρ F (NBar.π F gN) * NBar.ρ F (NBar.π F d₀N) * (NBar.ρ F (NBar.π F gN))⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv]
  have htvy : IsTransvectionWith (NBar.ρ F (NBar.π F yN))
      (NBar.ρ F (NBar.π F gN) ⟨D.b₀, D.b₀_mem_E64 hF⟩) := hρy ▸ B1.tv_conj htv₀ _
  have hy1 : NBar.ρ F (NBar.π F yN) ≠ 1 := hρy ▸ B1.tv_conj_ne_one hd₀1 _
  set c : G := ((NBar.ρ F (NBar.π F gN) ⟨D.b₀, D.b₀_mem_E64 hF⟩ : ↥F) : G)
  have htvG : ∀ v ∈ F, (yN : G) * v * (yN : G)⁻¹ = v ∨ (yN : G) * v * (yN : G)⁻¹ = v * c := by
    intro v hv
    rcases htvy.2 ⟨v, hv⟩ with h | h
    · left
      have := congrArg Subtype.val h
      rwa [NBar.ρ_π] at this
    · right
      have := congrArg Subtype.val h
      rwa [NBar.ρ_π] at this
  have hmoveG := exists_moved_of_ρ_ne_one hy1
  have hβ : ∀ {β : G}, (yN : G) * β⁻¹ ∈ F → ∃ hβN : β ∈ normalizer (F : Set G),
      NBar.π F yN = NBar.π F ⟨β, hβN⟩ ∧ β ∉ F := by
    intro β hyβ
    have hβN : β ∈ normalizer (F : Set G) := by
      have : β = ((yN : G) * β⁻¹)⁻¹ * yN := by group
      rw [this]
      exact mul_mem (inv_mem (le_normalizer hyβ)) yN.2
    have hπ : NBar.π F yN = NBar.π F ⟨β, hβN⟩ := by
      refine π_eq_of_inv_mul_mem _ _ ?_
      have e : (yN : G)⁻¹ * β = (yN : G)⁻¹ * ((yN : G) * β⁻¹)⁻¹ * (yN : G)⁻¹⁻¹ := by group
      show (yN : G)⁻¹ * β ∈ F
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem yN.2) _).1 (inv_mem hyβ)
    refine ⟨hβN, hπ, fun hβF => hy1 ?_⟩
    rw [hπ, NBar.π_eq_one_of_mem F hFc _ hβF, map_one]
  have hR : ∀ {X : Subgroup G} {d β : G} (hd : d ∈ X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G))
      (hdF : d ∉ F) (hdN : d ∈ normalizer (F : Set G)) (hβX : β ∈ X)
      (hβN : β ∈ normalizer (F : Set G)) (hβF : β ∉ F)
      (hcard : Nat.card ↥(X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G)) = 2 * Nat.card ↥(F ⊓ X)),
      NBar.π F ⟨β, hβN⟩ = NBar.π F ⟨d, hdN⟩ := by
    intro X d β hd hdF hdN hβX hβN hβF hcard
    haveI : Finite ↥(X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G)) := inferInstance
    have hβR : β ∈ X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hβX, mem_normalizer_iff.2 fun h => ?_⟩
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 hβN h]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, mul_mem (mul_mem hβX h2) (inv_mem hβX)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : h = β⁻¹ * (β * h * β⁻¹) * β := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hβX) h2) hβX
    have hle : F ⊓ X ≤ X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G) :=
      le_inf inf_le_right le_normalizer
    have h := inv_mul_mem_of_card_eq_two_mul hle hcard hβR hd (fun h => hβF (mem_inf.1 h).1)
      (fun h => hdF (mem_inf.1 h).1)
    exact π_eq_of_inv_mul_mem _ _ (mem_inf.1 h).1
  obtain ⟨-, -, hB₀, hB₁⟩ := D.E64_decomp hF
  rcases hTv F hF yN c hyT yN.2 htvG hmoveG with ⟨α, hα, hyα⟩ | ⟨β, hβB, hyβ⟩ | ⟨β, hβB, hyβ⟩
  · exfalso
    obtain ⟨hαN, -, hαF⟩ := hβ hyα
    exact hαF (D.A_le_E64 rfl hF hα)
  · left
    obtain ⟨hβN, hπ, hβF⟩ := hβ hyβ
    rw [hπ]
    exact hR hd₀ hd₀F _ hβB hβN hβF (by rw [D.card_R₀ hF, hB₀.2.2])
  · right
    obtain ⟨hβN, hπ, hβF⟩ := hβ hyβ
    rw [hπ]
    exact hR hd₁ hd₁F _ hβB hβN hβF (by rw [D.card_R₁ hF, hB₁.2.2])

include hF in
theorem exists_not_mem_T₁ (hquot : QuotInput (T : Subgroup G))
    {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G))) {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    ∃ τ : ↥(normalizer (F : Set G)), (τ : G) ∈ (T : Subgroup G) ∧ (τ : G) ∉ D.T₁ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ⟩ := nonempty_sylowImage_equiv D hF hquot hQ
  set S : Set (NBar.Q F) := {1, NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩,
    NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩,
    NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ *
      NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩} with hS
  have hsub : ((NBar.sylowImage F Q : Subgroup (NBar.Q F)) : Set (NBar.Q F)) ⊆ S := by
    intro y hy
    rw [SetLike.mem_coe, NBar.coe_sylowImage] at hy
    obtain ⟨yN, hyQ, rfl⟩ := hy
    have hyT : (yN : G) ∈ (T : Subgroup G) := by
      have hyQ' : yN ∈ (Q : Subgroup ↥(normalizer (F : Set G))) := hyQ
      rw [hQ, mem_subgroupOf] at hyQ'
      exact hyQ'
    rcases π_mem_of_mem_T₁ D hF hd₀ hd₀F hd₁ hd₁F yN (hcon yN hyT) with h | h | h | h <;>
      rw [h, hS] <;> simp
  have hcard8 : Nat.card ↥(NBar.sylowImage F Q : Subgroup (NBar.Q F)) = 8 := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  have hS4 : S.ncard ≤ 4 := by
    rw [hS]
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
    rw [Set.ncard_singleton]
  have e : Nat.card ↥(NBar.sylowImage F Q : Subgroup (NBar.Q F)) =
      ((NBar.sylowImage F Q : Subgroup (NBar.Q F)) : Set (NBar.Q F)).ncard := Nat.card_coe_set_eq _
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem tvHyp (hTv : TvInput D) (hquot : QuotInput (T : Subgroup G)) (hswap : SwapInput D)
    {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G))) {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    TvHyp (NBar.ρ F) (NBar.sylowImage F Q)
      (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩)
      (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) := by
  obtain ⟨htv₀, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀ hd₀F
  obtain ⟨htv₁, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁ hd₁F
  have hd₀T : d₀ ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B (mem_inf.1 hd₀).1)
  have hd₁T : d₁ ∈ (T : Subgroup G) := D.B_le_T (D.B₁_le_B (mem_inf.1 hd₁).1)
  have hne : NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ ≠
      NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ := by
    intro h
    have hb := NBar.eq_of_isTransvectionWith htv₀ (h ▸ htv₁) hd₀1
    have hb' : D.b₀ = D.b₁ := congrArg Subtype.val hb
    have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, hb' ▸ D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₀_ne_one this
  refine ⟨NBar.ρ_injective F, fun v => Subtype.ext (hF.mul_self v v.2), hF.2.2,
    nonempty_sylowImage_equiv D hF hquot hQ, π_mem_sylowImage hQ _ hd₀T,
    π_mem_sylowImage hQ _ hd₁T, hne, ⟨hd₀1, _, htv₀⟩, fun y hy => ⟨fun hc =>
      fusion_mem D hF hTv hQ hd₀ hd₀F hd₁ hd₁F y hy hc, ?_⟩⟩
  rintro (rfl | rfl)
  · exact IsConj.refl _
  · obtain ⟨τ, hτT, hτ₁⟩ := exists_not_mem_T₁ D hF hquot hQ hd₀ hd₀F hd₁ hd₁F
    exact isConj_iff.2 ⟨NBar.π F τ, conj_d₀_eq_d₁ D hF hswap hd₀ hd₀F hd₁ hd₁F τ hτT hτ₁⟩

end CFSG.CGT.Foote81L6.Normalizer
