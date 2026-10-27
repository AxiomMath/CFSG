module

public import CFSG.GH74.Generic.BProg.B3.KG531Defs
public import CFSG.GH74.Generic.BProg.B3.KG531RedAux
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

open KG531Red in
theorem kg_531a_of_table (hT : KG531Table) {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsQuasisimple ↥M)
    (hGH : GHList (↥M ⧸ center ↥M)) {t : X} (ht : orderOf t = 2) (htM : t ∈ M)
    {L₁ L₂ : Subgroup X} (h₁ : L₁ ≤ centralizer ({t} : Set X) ⊓ M) (h₂ : L₂ ≤ centralizer ({t} : Set X) ⊓ M)
    (hc₁ : IsComponent (L₁.subgroupOf (centralizer ({t} : Set X) ⊓ M)))
    (hc₂ : IsComponent (L₂.subgroupOf (centralizer ({t} : Set X) ⊓ M)))
    (htL : t ∈ (center ↥L₂).map L₂.subtype)
    (hcomm : ∀ g ∈ L₁, ∀ h ∈ L₂, g * h = h * g) (hdisj : L₁ ⊓ L₂ = ⊥)
    {F : Type} [Field F] [Fintype F] (hodd : Odd (Fintype.card F)) (hF : 5 ≤ Fintype.card F)
    (e₁ : Nonempty (↥L₁ ≃* SL(2, F))) (e₂ : Nonempty (↥L₂ ≃* SL(2, F)))
    (hZ : (center ↥L₁).map L₁.subtype ≤ (center ↥M).map M.subtype) : False := by
  classical
  have _hdisj := hdisj
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  have hS : IsSimpleGroup (↥M ⧸ center ↥M) := hM.2.1
  have hnab : ∃ a b : ↥M ⧸ center ↥M, a * b ≠ b * a := hM.2.2
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set u : ↥M := ⟨t, htM⟩ with hu
  set K : Subgroup X := centralizer ({t} : Set X) ⊓ M with hK
  have hKM : K ≤ M := inf_le_right
  have hL₁M : L₁ ≤ M := h₁.trans hKM
  have hL₂M : L₂ ≤ M := h₂.trans hKM
  set κ : ↥K →* ↥M := Subgroup.inclusion hKM with hκdef
  have hκ : Function.Injective κ := Subgroup.inclusion_injective hKM
  have hrange : κ.range = centralizer ({u} : Set ↥M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
      simpa [hu, hκdef] using this
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, x.2⟩⟩, rfl⟩
      simpa [hu] using congrArg Subtype.val hx
  set ρ : ↥K →* ↥M ⧸ center ↥M := π.comp κ with hρ
  set Cb : Subgroup (↥M ⧸ center ↥M) := centralizer ({π u} : Set (↥M ⧸ center ↥M)) with hCb
  have hcomp : ∀ J : Subgroup ↥K, IsComponent J → IsCompIn Cb (J.map ρ) := fun J hJ =>
    ⟨(Subgroup.map_le_range ρ J).trans (range_le_centralizer κ hrange),
      isComponent_central_quotient κ hκ hrange hJ⟩
  set φ₁ : ↥L₁ →* ↥M ⧸ center ↥M := π.comp (Subgroup.inclusion hL₁M) with hφ₁
  set φ₂ : ↥L₂ →* ↥M ⧸ center ↥M := π.comp (Subgroup.inclusion hL₂M) with hφ₂
  have hB : ∀ (L : Subgroup X) (hL : L ≤ M) (hLK : L ≤ K),
      (π.comp (Subgroup.inclusion hL)).range = (L.subgroupOf K).map ρ := by
    intro L hL hLK
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨⟨l, hLK l.2⟩, l.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hcomp₁ : IsCompIn Cb φ₁.range := by
    rw [hφ₁, hB L₁ hL₁M h₁]; exact hcomp _ hc₁
  have hcomp₂ : IsCompIn Cb φ₂.range := by
    rw [hφ₂, hB L₂ hL₂M h₂]; exact hcomp _ hc₂
  have hL₁q : IsQuasisimple ↥L₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h₁) hc₁.1
  have hcommB : ∀ b ∈ φ₁.range, ∀ c ∈ φ₂.range, b * c = c * b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show π (Subgroup.inclusion hL₁M x) * π (Subgroup.inclusion hL₂M y) =
      π (Subgroup.inclusion hL₂M y) * π (Subgroup.inclusion hL₁M x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm x x.2 y y.2)
  have hu1 : π u ≠ 1 := by
    intro h1
    have hCb1 : Cb = ⊤ := by
      rw [hCb, h1]
      ext x
      simp [Subgroup.mem_centralizer_iff]
    have c₁ := hcomp₁.2
    have c₂ := hcomp₂.2
    rw [hCb1] at c₁ c₂
    exact false_of_components_top hS hnab c₁ c₂ hcommB
  have hi : ∀ (L : Subgroup X) (hL : L ≤ M) (a : ↥L),
      (Subgroup.inclusion hL a : ↥M) ∈ center ↥M → a ∈ center ↥L := by
    intro L hL a ha
    rw [Subgroup.mem_center_iff] at ha ⊢
    intro g
    apply Subgroup.inclusion_injective hL
    simpa using ha (Subgroup.inclusion hL g)
  have hker_i : ∀ (L : Subgroup X) (hL : L ≤ M) (a : ↥L),
      (π.comp (Subgroup.inclusion hL)) a = 1 → a ∈ center ↥L := by
    intro L hL a ha
    apply hi L hL a
    simpa [hπ, QuotientGroup.eq_one_iff] using ha
  have hZ₁ : ∀ a : ↥L₁, a ∈ center ↥L₁ → φ₁ a = 1 := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := hZ ⟨a, ha, rfl⟩
    have hinc : Subgroup.inclusion hL₁M a = c := Subtype.ext hca.symm
    show π (Subgroup.inclusion hL₁M a) = 1
    rw [hinc]
    exact (QuotientGroup.eq_one_iff c).2 hc
  have hsurj₁ : Function.Surjective φ₁.rangeRestrict := φ₁.rangeRestrict_surjective
  have hker₁ : φ₁.rangeRestrict.ker ≤ center ↥L₁ := by
    intro a ha
    rw [MonoidHom.ker_rangeRestrict] at ha
    exact hker_i L₁ hL₁M a ha
  have hZ₁' := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hL₁q hsurj₁ hker₁
  have hcenter₁ : center ↥φ₁.range = ⊥ := by
    rw [hZ₁', eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact hZ₁ z hz
  obtain ⟨p, f, hp, hp2, hf, hcardF, h5⟩ := exists_prime_pow_card hodd hF
  have hSLq : IsQuasisimple SL(2, F) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁ hL₁q
  set ψ' : SL(2, F) →* ↥φ₁.range := φ₁.rangeRestrict.comp e₁.symm.toMonoidHom with hψ'
  have hsurj' : Function.Surjective ψ' := hsurj₁.comp e₁.symm.surjective
  have hker' : ψ'.ker ≤ center SL(2, F) := by
    intro s hs
    have h1 : e₁.symm s ∈ center ↥L₁ := hker₁ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hs))
    have := center_of_equiv e₁ h1
    simpa using this
  have eqv := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hSLq hsurj' hker'
  have hadm : StatedLieAdmissible .PSL (1 + 1) p f :=
    ⟨hp, hf, by norm_num, fun h => by have := (Prod.mk.inj h).2; omega,
      fun h => by have := (Prod.mk.inj h).2; omega⟩
  have hmodel₁ : StatedClassicalModel (↥φ₁.range ⧸ center ↥φ₁.range) .PSL 2 p f :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eqv.symm
      (CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 F hadm hcardF)
  obtain ⟨z₀, hz₀, hz₀t⟩ := htL
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    rw [h] at hz₀t
    have h1 : t = 1 := hz₀t.symm
    rw [h1, orderOf_one] at ht
    omega
  have hz₀u : φ₂ z₀ = π u := by
    show π (Subgroup.inclusion hL₂M z₀) = π u
    congr 1
    exact Subtype.ext hz₀t
  have hinj₂ : Function.Injective φ₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ center ↥L₂ := hker_i L₂ hL₂M x hx
    have h1 := center_of_equiv e₂ hxc
    have h2 := center_of_equiv e₂ hz₀
    rcases sl2_center_cases h1 h2 (fun h => hz₀1 (e₂.injective (by simpa using h))) with h | h
    · exact e₂.injective (by simpa using h)
    · exfalso
      apply hu1
      rw [← hz₀u, ← e₂.injective h]
      exact hx
  have hbij₂ : Function.Bijective φ₂.rangeRestrict :=
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), φ₂.rangeRestrict_surjective⟩
  have hmodel₂ : HasSL2Model ↥φ₂.range (fun q => q = p ^ f) :=
    ⟨F, inferInstance, inferInstance, hcardF,
      ⟨(MulEquiv.ofBijective φ₂.rangeRestrict hbij₂).symm.trans
        (e₂.trans (specialLinearGroupEquivStatedSL 2 F))⟩⟩
  have ht_mem : π u ∈ φ₂.range := ⟨z₀, hz₀u⟩
  have hdisj' : φ₁.range ⊓ φ₂.range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rw [Subgroup.mem_bot]
    apply hZ₁ a
    rw [Subgroup.mem_center_iff]
    intro g
    have hz : (Subgroup.inclusion hL₂M b)⁻¹ * Subgroup.inclusion hL₁M a ∈ center ↥M := by
      rw [← QuotientGroup.eq]
      exact hb
    set z := (Subgroup.inclusion hL₂M b)⁻¹ * Subgroup.inclusion hL₁M a with hzdef
    have hza : Subgroup.inclusion hL₁M a = Subgroup.inclusion hL₂M b * z := by
      rw [hzdef]; group
    apply Subgroup.inclusion_injective hL₁M
    rw [map_mul, map_mul, hza]
    have hgb : Subgroup.inclusion hL₁M g * Subgroup.inclusion hL₂M b =
        Subgroup.inclusion hL₂M b * Subgroup.inclusion hL₁M g :=
      Subtype.ext (hcomm g g.2 b b.2)
    have hzc : Subgroup.inclusion hL₁M g * z = z * Subgroup.inclusion hL₁M g :=
      Subgroup.mem_center_iff.mp hz _
    calc Subgroup.inclusion hL₁M g * (Subgroup.inclusion hL₂M b * z)
        = (Subgroup.inclusion hL₁M g * Subgroup.inclusion hL₂M b) * z := by group
      _ = (Subgroup.inclusion hL₂M b * Subgroup.inclusion hL₁M g) * z := by rw [hgb]
      _ = Subgroup.inclusion hL₂M b * (Subgroup.inclusion hL₁M g * z) := by group
      _ = Subgroup.inclusion hL₂M b * (z * Subgroup.inclusion hL₁M g) := by rw [hzc]
      _ = (Subgroup.inclusion hL₂M b * z) * Subgroup.inclusion hL₁M g := by group
  have hu2 : (π u) ^ 2 = 1 := by
    have h2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    rw [← map_pow]
    have : u ^ 2 = 1 := Subtype.ext (by simpa [hu] using h2)
    rw [this, map_one]
  have hord : orderOf (π u) = 2 := orderOf_eq_prime hu2 hu1
  exact hT (↥M ⧸ center ↥M) hS hnab hGH (π u) φ₁.range φ₂.range p f
    ⟨hord, hcomp₁, hcomp₂, hcenter₁, ht_mem, hcommB, hdisj', hp, hp2, h5, hmodel₁, hmodel₂⟩

end CFSG.GH74.Generic.BProg.B3
