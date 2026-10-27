module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbLines
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbType
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGold

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace IIbData

variable {G : Type} [Group G] [Finite G] {A R T V₀ P : Subgroup G} {g t z₀ a σ c₁ : G}

theorem exists_conj_ss_c₁ (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {f : IIbSyl →* G} (hfinj : Function.Injective f) (hfrange : f.range = P ⊔ zpowers t)
    (hfP : IIbSyl.P.map f = P) (hfV0 : IIbSyl.V0.map f = V₀) (hfR : IIbSyl.R.map f = R)
    (hfz : f IIbSyl.z0 = z₀) (hfa : f IIbSyl.a = a) (hfc : f IIbSyl.c1 = c₁) :
    ∃ k ∈ normalizer (V₀ : Set G), k * c₁ * k⁻¹ = f IIbSyl.ss := by
  obtain ⟨b₀, b, hb₀N, hb₀3, hb₀tr, hbP, hbV, hbV₀, hbc⟩ := hS.exists_b hD.sylowP hD.inf_P
  have hc₁P : c₁ ∈ P := by
    rw [← hfc, ← hfP]
    exact mem_map_of_mem f IIbSyl.c1_mem_P
  have haR : a ∈ R := hD.outer.r_mem
  have hca : ⁅c₁, a⁆ = z₀ := by
    rw [← hfc, ← hfa, ← hfz, ← map_commutatorElement, commutatorElement_def, IIbSyl.comm_c1_a]
  have hz1 : z₀ ≠ 1 := hD.outer.z_ne
  have hV_comm : ∀ y ∈ R ⊔ T, ⁅y, a⁆ = 1 := fun y hy => by
    rw [commutatorElement_def, hS.comm hy (mem_sup_left haR)]
    group
  set c₂ := b * c₁ * b⁻¹ with hc₂
  have hc₂P : c₂ ∈ P := (mem_normalizer_iff.mp hbP c₁).mp hc₁P
  have hc₂a : ⁅c₂, a⁆ ≠ z₀ := by
    rw [hbc c₁ hc₁P a haR, hca]
    exact (hS.b₀_cycle hb₀N hb₀3 hb₀tr hD.outer.z_mem hz1).1
  have hc₂V : c₂ ∉ R ⊔ T := by
    intro hm
    have hc₁V : c₁ ∈ R ⊔ T := by
      have := (mem_normalizer_iff.mp hbV c₁).mpr hm
      exact this
    exact hz1 (hca ▸ hV_comm c₁ hc₁V)
  have hc₂2 : c₂ * c₂ = 1 := by
    have h1 : c₁ * c₁ = 1 := by rw [← hfc, ← map_mul, IIbSyl.c1_facts.2.1, map_one]
    calc c₂ * c₂ = b * (c₁ * c₁) * b⁻¹ := by rw [hc₂]; group
      _ = 1 := by rw [h1]; group
  obtain ⟨m₂, hm₂⟩ : c₂ ∈ f.range := hfrange ▸ mem_sup_left hc₂P
  have hm₂P : m₂ ∈ IIbSyl.P := by
    have h1 : f m₂ ∈ IIbSyl.P.map f := by rw [hfP, hm₂]; exact hc₂P
    obtain ⟨m', hm', he⟩ := h1
    exact hfinj he ▸ hm'
  have hm₂V : ∀ x y, m₂ ≠ IIbSyl.vElt x y := fun x y he =>
    hc₂V (by rw [← hm₂, he]; exact f_vElt_mem hS hfV0 hfR x y)
  have hm₂2 : m₂ * m₂ = 1 := hfinj (by rw [map_mul, hm₂, hc₂2, map_one])
  have hm₂a : m₂ * IIbSyl.a * m₂⁻¹ * IIbSyl.a⁻¹ ≠ IIbSyl.z0 := fun he => hc₂a (by
    rw [commutatorElement_def, ← hm₂, ← hfa, ← hfz, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, he])
  obtain ⟨x, r, hxr⟩ := IIbSyl.conj_ss m₂ hm₂2 (IIbSyl.right_eq_one_of_mem_P hm₂P) hm₂V hm₂a
  have hbN : b ∈ normalizer (V₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hbV₀ w hw]
      exact (mem_normalizer_iff.mp hb₀N w).mp hw
    · intro hw
      have hw' : b₀⁻¹ * (b * w * b⁻¹) * b₀ ∈ V₀ := by
        have := (mem_normalizer_iff.mp (inv_mem hb₀N) _).mp hw
        simpa using this
      have e := hbV₀ _ hw'
      have e' : b * w * b⁻¹ = b * (b₀⁻¹ * (b * w * b⁻¹) * b₀) * b⁻¹ := by
        rw [e]; group
      have hinj : w = b₀⁻¹ * (b * w * b⁻¹) * b₀ := by
        have := congrArg (fun y => b⁻¹ * y * b) e'
        simpa [mul_assoc] using this
      rw [hinj]
      exact hw'
  have key : ∀ y : IIbSyl, y * m₂ * y⁻¹ = IIbSyl.ss →
      ∃ k ∈ normalizer (V₀ : Set G), k * c₁ * k⁻¹ = f IIbSyl.ss := by
    intro y hy
    refine ⟨f y * b, mul_mem ((hD.S₁_le hS (hfrange ▸ ⟨y, rfl⟩ : f y ∈ P ⊔ zpowers t)).1) hbN, ?_⟩
    rw [← hy, map_mul, map_mul, map_inv, hm₂, hc₂]
    group
  rcases hxr with hxr | hxr
  · exact key _ hxr
  · exact key _ hxr

theorem isConj_ss_c₁ (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {f : IIbSyl →* G} (hfinj : Function.Injective f) (hfrange : f.range = P ⊔ zpowers t)
    (hfP : IIbSyl.P.map f = P) (hfV0 : IIbSyl.V0.map f = V₀) (hfR : IIbSyl.R.map f = R)
    (hfz : f IIbSyl.z0 = z₀) (hfa : f IIbSyl.a = a) (hfc : f IIbSyl.c1 = c₁) :
    IsConj (f IIbSyl.ss) c₁ := by
  obtain ⟨k, -, hk⟩ := exists_conj_ss_c₁ hS hD hfinj hfrange hfP hfV0 hfR hfz hfa hfc
  exact isConj_iff.mpr ⟨k⁻¹, by rw [← hk]; group⟩

theorem isConj_c₁_of_isConj (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    {u : G} (hu : u ∈ P ⊔ zpowers t) (hu2 : u * u = 1) (huV : u ∉ V₀) (huz : IsConj z₀ u) :
    IsConj z₀ c₁ := by
  obtain ⟨f, hfinj, hfrange, -, hfP, hfV0, hfR, hft, hfz, hfa, -, hfc⟩ := hD.emb
  obtain ⟨m, rfl⟩ : u ∈ f.range := hfrange ▸ hu
  have hm2 : m * m = 1 := hfinj (by rw [map_mul, hu2, map_one])
  rcases IIbSyl.invol_cases m hm2 with ⟨x, rfl⟩ | ⟨x, r, hr, rfl⟩ | ⟨x, r, hxr⟩ | ⟨x, r, hxr⟩ |
    ⟨x, r, hxr⟩
  · exact absurd (by rw [← hfV0]; exact mem_map_of_mem f ⟨Multiplicative.ofAdd x, rfl⟩) huV
  · exact absurd huz (hS.not_isConj_of_mem_V₀ hD.outer.z_mem hD.outer.z_ne
      (f_vElt_mem hS hfV0 hfR x r) huV)
  · exact huz.trans (isConj_iff.mpr ⟨f (IIbSyl.vElt x r), by
      rw [← hfc, ← hxr]; simp only [map_mul, map_inv]⟩)
  · have key : ∀ y : IIbSyl, y * m * y⁻¹ = IIbSyl.ss → IsConj (f m) (f IIbSyl.ss) := by
      intro y hy
      exact isConj_iff.mpr ⟨f y, by rw [← hy]; simp only [map_mul, map_inv]⟩
    have h1 : IsConj (f m) (f IIbSyl.ss) := by
      rcases hxr with hxr | hxr
      · exact key _ hxr
      · exact key _ hxr
    exact (huz.trans h1).trans (isConj_ss_c₁ hS hD hfinj hfrange hfP hfV0 hfR hfz hfa hfc)
  · exfalso
    apply hD.not_conj
    have key : ∀ y : IIbSyl, y⁻¹ * IIbSyl.t * y = m → IsConj t (f m) := by
      intro y hy
      exact isConj_iff.mpr ⟨(f y)⁻¹, by rw [← hy, inv_inv, ← hft]; simp only [map_mul, map_inv]⟩
    have h1 : IsConj t (f m) := by
      rcases hxr with hxr | hxr
      · exact key _ hxr
      · exact key _ hxr
    exact h1.trans huz.symm

theorem isConj_z₀_c₁ (hGold : Asc76X.GoldschmidtTheoremA)
    (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁) : IsConj z₀ c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnc
  obtain ⟨f, -, -, hfS0, -, -, -, -, -, hfa, -, -⟩ := hD.emb
  obtain ⟨S, hS₁⟩ := Asc76X.exists_sylow_eq_of_isSylowOf_top hD.sylow
  have hzV₀ : z₀ ∈ V₀ := hD.outer.z_mem
  have hz1 : z₀ ≠ 1 := hD.outer.z_ne
  have hWS : V₀ ≤ (S : Subgroup G) := hS₁ ▸ hD.S₁_le_of_V₀ hS
  have hWab : IsMulCommutative V₀ := ⟨⟨fun w w' => Subtype.ext
    (hS.comm (hS.V₀_le w.2) (hS.V₀_le w'.2))⟩⟩
  have hW1 : V₀ ≠ ⊥ := fun h0 => hz1 (by rw [h0, mem_bot] at hzV₀; exact hzV₀)
  have hWcl : ∀ w ∈ V₀, ∀ x : G, x⁻¹ * w * x ∈ (S : Subgroup G) → x⁻¹ * w * x ∈ V₀ := by
    intro w hw x hx
    by_contra hnot
    apply hnc
    have hw1 : w ≠ 1 := fun h1 => hnot (by rw [h1, mul_one, inv_mul_cancel]; exact one_mem _)
    refine isConj_c₁_of_isConj hS hD (u := x⁻¹ * w * x) (hS₁ ▸ hx) ?_ hnot ?_
    · have h2 := hS.mul_self (hS.V₀_le hw)
      calc x⁻¹ * w * x * (x⁻¹ * w * x) = x⁻¹ * (w * w) * x := by group
        _ = 1 := by rw [h2]; group
    · exact (hS.isConj_of_mem_V₀ hzV₀ hz1 hw hw1).trans (isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]⟩)
  have haX : a ∈ (P ⊔ zpowers t) ⊓ rankTwoX A := by
    rw [← hfS0, ← hfa]
    exact mem_map_of_mem f (MonoidHom.mem_ker.mpr IIbSyl.chi_eq_one.2.2.1)
  have haR : a ∈ R := hD.outer.r_mem
  have ha := (hS.goldschmidt_X hGold S hWS hWab hWcl hW1).2 a (hS₁ ▸ haX.1) haX.2
    (by rw [sq]; exact hS.mul_self (mem_sup_left haR))
  have h1 : a ∈ R ⊓ V₀ := mem_inf.mpr ⟨haR, ha⟩
  rw [hS.inf_R_V₀, mem_bot] at h1
  exact hD.outer.r_ne h1

theorem caseA (hGold : Asc76X.GoldschmidtTheoremA)
    (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁) :
    ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁ :=
  hD.conj_ptOf_of_isConj hS (isConj_z₀_c₁ hGold hS hD)

end IIbData

end CFSG.ComponentClassification.RankTwoAltFive
