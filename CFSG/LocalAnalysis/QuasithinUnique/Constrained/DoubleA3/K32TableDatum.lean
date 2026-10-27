module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSwap

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

section Datum

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem k32_datum_of_normal (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (ctx : K32Ctx T M H S L s x z₁ z₂ K)
    (hKnorm : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G)) :
    ∃ X P R A V : Subgroup (MulAut ↥K), K32Datum ↥K X P R A V := by
  classical
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hB31 := basic31 hD h27_1 ctx.a3.toA3A3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hz₁U : z₁ ∈ blockU L := ctx.a3.z₁_mem.1
  have hLG₂ : L ≤ centralizerElem z₂ := ctx.a3.L_le_cent₂
  have hKG₂ : K ≤ centralizerElem z₂ := ctx.comp.1
  have hS₁G₂ : sOne S x ≤ centralizerElem z₂ := ctx.sylow.1
  have hRS₁ : baum S ≤ sOne S x := le_sup_left
  have hRL : baum S ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hB31.N_eq]; exact inf_le_right
  have hUR : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hRidx : (baum S).relIndex (sOne S x) = 2 := A3A3x.relIndex_baum_sOne' hD h27_1 ctx.a3
  set G₂ : Subgroup G := centralizerElem z₂ with hG₂def
  set φ := k32ActHom K G₂ hKnorm with hφ
  have hnc : ¬ ∀ k ∈ K, k * z₁ = z₁ * k := k32_z₁_not_central ctx
  have hCK : L ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    k32_inf_centralizer_eq_bot hA4 hz₁U (hLG₂.trans hKnorm) hnc
  let f₀ : ↥L →* MulAut ↥K := φ.comp (Subgroup.inclusion hLG₂)
  have hf₀inj : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : (a : G) ∈ Subgroup.centralizer (K : Set G) :=
      (k32ActHom_eq_one_iff K G₂ hKnorm (Subgroup.inclusion hLG₂ a)).mp ha
    have hmem : (a : G) ∈ L ⊓ Subgroup.centralizer (K : Set G) := ⟨a.2, hc⟩
    rw [hCK] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hA' : IsA4Block f₀.range (((blockU L).subgroupOf L).map f₀) :=
    k32_isA4Block_range hA4 f₀ hf₀inj
  have key : ∀ ρ' : ↥G₂, (ρ' : G) ∈ baum S → ∀ a ∈ f₀.range, φ ρ' * a * (φ ρ')⁻¹ ∈ f₀.range := by
    intro ρ' hρ' a ha
    obtain ⟨l, rfl⟩ := ha
    have hl' : (ρ' : G) * l * (ρ' : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hRL hρ') l).mp l.2
    refine ⟨⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩, ?_⟩
    have e : (Subgroup.inclusion hLG₂ ⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩ : ↥G₂) =
        ρ' * Subgroup.inclusion hLG₂ l * ρ'⁻¹ := Subtype.ext rfl
    show φ (Subgroup.inclusion hLG₂ ⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩) =
      φ ρ' * φ (Subgroup.inclusion hLG₂ l) * (φ ρ')⁻¹
    rw [e, map_mul, map_mul, map_inv]
  have keyV : ∀ ρ' : ↥G₂, (ρ' : G) ∈ baum S → ∀ a ∈ ((blockU L).subgroupOf L).map f₀,
      φ ρ' * a * (φ ρ')⁻¹ ∈ ((blockU L).subgroupOf L).map f₀ := by
    intro ρ' hρ' a ha
    obtain ⟨u, hu, rfl⟩ := ha
    have hu' : (u : G) ∈ blockU L := Subgroup.mem_subgroupOf.mp hu
    have hul' : (ρ' : G) * u * (ρ' : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hRL hρ') u).mp u.2
    have hU' : (ρ' : G) * u * (ρ' : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hRL hρ')) u).mp hu'
    refine ⟨⟨(ρ' : G) * u * (ρ' : G)⁻¹, hul'⟩, Subgroup.mem_subgroupOf.mpr hU', ?_⟩
    have e : (Subgroup.inclusion hLG₂ ⟨(ρ' : G) * u * (ρ' : G)⁻¹, hul'⟩ : ↥G₂) =
        ρ' * Subgroup.inclusion hLG₂ u * ρ'⁻¹ := Subtype.ext rfl
    show φ (Subgroup.inclusion hLG₂ ⟨(ρ' : G) * u * (ρ' : G)⁻¹, hul'⟩) =
      φ ρ' * φ (Subgroup.inclusion hLG₂ u) * (φ ρ')⁻¹
    rw [e, map_mul, map_mul, map_inv]
  refine ⟨φ.range, ((sOne S x).subgroupOf G₂).map φ, ((baum S).subgroupOf G₂).map φ, f₀.range,
    ((blockU L).subgroupOf L).map f₀, ?_⟩
  refine ⟨?_, k32_isSylowTwoOf_map φ ctx.sylow, hA', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨(k : G), hKG₂ k.2⟩, k32ActHom_of_mem K G₂ hKnorm _ k.2⟩
  ·
    rintro _ ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion hLG₂ l, rfl⟩
  ·
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨Subgroup.inclusion hLG₂ u,
      Subgroup.mem_subgroupOf.mpr (hUR (Subgroup.mem_subgroupOf.mp hu)), rfl⟩
  ·
    exact Subgroup.map_mono fun a ha =>
      Subgroup.mem_subgroupOf.mpr (hRS₁ (Subgroup.mem_subgroupOf.mp ha))
  ·
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρR : (ρ : G) ∈ baum S := Subgroup.mem_subgroupOf.mp hρ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact key ρ hρR a
    · intro h
      have h1 := key ρ⁻¹ (by simpa using (baum S).inv_mem hρR) _ h
      have e : (φ ρ⁻¹) * (φ ρ * a * (φ ρ)⁻¹) * (φ ρ⁻¹)⁻¹ = a := by
        rw [map_inv]; group
      rwa [e] at h1
  ·
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρR : (ρ : G) ∈ baum S := Subgroup.mem_subgroupOf.mp hρ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact keyV ρ hρR a
    · intro h
      have h1 := keyV ρ⁻¹ (by simpa using (baum S).inv_mem hρR) _ h
      have e : (φ ρ⁻¹) * (φ ρ * a * (φ ρ)⁻¹) * (φ ρ⁻¹)⁻¹ = a := by
        rw [map_inv]; group
      rwa [e] at h1
  ·
    have hsub : (baum S).subgroupOf G₂ ≤ (sOne S x).subgroupOf G₂ := fun a ha =>
      Subgroup.mem_subgroupOf.mpr (hRS₁ (Subgroup.mem_subgroupOf.mp ha))
    have h1 := k32_relIndex_map_dvd φ hsub
    have h2 : ((baum S).subgroupOf G₂).relIndex ((sOne S x).subgroupOf G₂) =
        (baum S).relIndex (sOne S x) := Subgroup.relIndex_subgroupOf hS₁G₂
    rw [h2, hRidx] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  ·
    intro hcon
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ blockU L, u ∉ Subgroup.zpowers z₁ := by
      by_contra hc
      push Not at hc
      have hle : blockU L ≤ Subgroup.zpowers z₁ := hc
      have h1 := Subgroup.card_le_of_le hle
      rw [hA4.card_U, Nat.card_zpowers] at h1
      have h2 : orderOf z₁ ∣ 2 := orderOf_dvd_of_pow_eq_one ctx.a3.sq₁
      have h3 := Nat.le_of_dvd (by norm_num) h2
      omega
    have hu' : u ∉ Subgroup.centralizer ((baum S : Subgroup G) : Set G) := fun hc =>
      hu (by rw [ctx.a3.z₁_gen]; exact ⟨huU, hc⟩)
    obtain ⟨ρ, hρ, hρu⟩ : ∃ ρ ∈ baum S, ρ * u ≠ u * ρ := by
      by_contra hc
      push Not at hc
      exact hu' (Subgroup.mem_centralizer_iff.mpr fun ρ hρ => hc ρ hρ)
    have huL : u ∈ L := hA4.le huU
    have hρG₂ : ρ ∈ G₂ := ctx.a3.baum_le_cent₂ hρ
    let ρ' : ↥G₂ := ⟨ρ, hρG₂⟩
    let u' : ↥L := ⟨u, huL⟩
    have hρ'R : φ ρ' ∈ ((baum S).subgroupOf G₂).map φ :=
      ⟨ρ', Subgroup.mem_subgroupOf.mpr hρ, rfl⟩
    have hu'V : f₀ u' ∈ ((blockU L).subgroupOf L).map f₀ :=
      ⟨u', Subgroup.mem_subgroupOf.mpr huU, rfl⟩
    have hcomm : f₀ u' * φ ρ' = φ ρ' * f₀ u' :=
      Subgroup.mem_centralizer_iff.mp (hcon hρ'R) (f₀ u') hu'V
    have hl' : ρ * u * ρ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRL hρ) u).mp huL
    have hconj : f₀ ⟨ρ * u * ρ⁻¹, hl'⟩ = f₀ u' := by
      have e : (Subgroup.inclusion hLG₂ ⟨ρ * u * ρ⁻¹, hl'⟩ : ↥G₂) =
          ρ' * Subgroup.inclusion hLG₂ u' * ρ'⁻¹ := Subtype.ext rfl
      show φ (Subgroup.inclusion hLG₂ ⟨ρ * u * ρ⁻¹, hl'⟩) = φ (Subgroup.inclusion hLG₂ u')
      rw [e, map_mul, map_mul, map_inv]
      have hcomm' : φ (Subgroup.inclusion hLG₂ u') * φ ρ' = φ ρ' * φ (Subgroup.inclusion hLG₂ u') :=
        hcomm
      calc φ ρ' * φ (Subgroup.inclusion hLG₂ u') * (φ ρ')⁻¹
          = (φ (Subgroup.inclusion hLG₂ u') * φ ρ') * (φ ρ')⁻¹ := by rw [hcomm']
        _ = φ (Subgroup.inclusion hLG₂ u') := by group
    have hρu' : ρ * u * ρ⁻¹ = u := congrArg Subtype.val (hf₀inj hconj)
    apply hρu
    calc ρ * u = (ρ * u * ρ⁻¹) * ρ := by group
      _ = u * ρ := by rw [hρu']

end Datum

end CFSG.QuasithinUnique.DoubleA3
