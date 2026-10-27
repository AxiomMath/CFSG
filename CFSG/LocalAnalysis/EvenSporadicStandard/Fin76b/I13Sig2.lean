module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Sig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def SigmaCS {G : Type*} [Group G] (E : Subgroup G)
    (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : Prop :=
  ∀ φ₁ φ₂ : MulAut ↥E, BInv E π φ₁ → BInv E π φ₂ → φ₁ * φ₂ = φ₂ * φ₁ → φ₁ ≠ φ₂ →
    φ₁ * φ₂ ∉ innAutE E →
    Nat.card ↥(innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E))) = 64 ∧
    ∀ ψ ∈ innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E)), ψ * ψ = 1 →
      16 ≤ Nat.card ↥((innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E))) ⊓
        Subgroup.centralizer ({ψ} : Set (MulAut ↥E)))

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem card_inn : Nat.card ↥(innAutE E) = 16 := by
  let conjE : ↥E →* MulAut ↥E := MulAut.conj
  have h1 := Subgroup.card_ker_mul_card_range conjE
  have ht : t ∈ E := c.h.t_mem_E
  have hker : (conjE.ker : Set ↥E) = {1, ⟨t, ht⟩} := by
    ext e
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro he
      have hcomm : ∀ f ∈ E, f * (e : G) = e * f := by
        intro f hf
        have he' : (MulAut.conj e : MulAut ↥E) = 1 := he
        have := congrArg (fun φ : MulAut ↥E => ((φ ⟨f, hf⟩ : ↥E) : G)) he'
        have h5 : (e : G) * f * (e : G)⁻¹ = f := by
          simpa [MulAut.conj_apply] using this
        calc f * (e : G) = (e * f * (e : G)⁻¹) * e := by rw [h5]
          _ = e * f := by group
      rcases c.h.conf.econfig.center e e.2 hcomm with h2 | h2
      · exact Or.inl (Subtype.ext h2)
      · exact Or.inr (Subtype.ext h2)
    · rintro (rfl | rfl)
      · exact map_one conjE
      · refine MulEquiv.ext fun f => ?_
        apply Subtype.ext
        show t * (f : G) * t⁻¹ = f
        have := c.h.t_comm_E (e := (f : G)) f.2
        calc t * (f : G) * t⁻¹ = (t * f) * t⁻¹ := rfl
          _ = f := by rw [← this]; group
  have h2 : Nat.card conjE.ker = 2 := by
    have h3 : Nat.card ↥(conjE.ker : Set ↥E) = 2 := by
      rw [Nat.card_coe_set_eq, hker]
      exact Set.ncard_pair (fun h => c.h.t_ne (congrArg Subtype.val h).symm)
    exact h3
  have hE : Nat.card ↥E = 32 := c.h.wf.card_E
  show Nat.card conjE.range = 16
  rw [h2, hE] at h1
  omega

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ

theorem card_AE : Nat.card ↥((alternatingGroup (Fin 5)).comap π) = 960 := by
  set A := (alternatingGroup (Fin 5)).comap π with hA
  let g : ↥A →* Equiv.Perm (Fin 5) := π.comp A.subtype
  have h1 := Subgroup.card_ker_mul_card_range g
  have hmemA : ∀ φ ∈ innAutE E, φ ∈ A := by
    intro φ hφ
    have : π φ = 1 := (hπ.ker φ).2 hφ
    show π φ ∈ alternatingGroup (Fin 5)
    rw [this]; exact one_mem _
  have hker : Nat.card g.ker = 16 := by
    refine le_antisymm ?_ ?_
    · have := Nat.card_le_card_of_injective
        (fun a : g.ker => (⟨(a : ↥A).1, (hπ.ker _).1 a.2⟩ : ↥(innAutE E))) (by
          intro a b hab
          have h5 := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext h5))
      rwa [c.card_inn] at this
    · have := Nat.card_le_card_of_injective
        (fun φ : ↥(innAutE E) => (⟨⟨φ, hmemA φ φ.2⟩, (hπ.ker _).2 φ.2⟩ : g.ker)) (by
          intro a b hab
          have h5 := congrArg (fun u : g.ker => ((u : ↥A) : MulAut ↥E)) hab
          exact Subtype.ext h5)
      rwa [c.card_inn] at this
  have hrange : g.range = alternatingGroup (Fin 5) := by
    ext s
    constructor
    · rintro ⟨a, rfl⟩; exact a.2
    · intro hs
      obtain ⟨φ, rfl⟩ := hπ.surj s
      exact ⟨⟨φ, hs⟩, rfl⟩
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  rw [hker, hrange, h60] at h1
  omega

theorem cs_general (hcs : SigmaCS E π)
    {Sg : Subgroup (MulAut ↥E)} (hS2 : IsPGroup 2 Sg)
    (hSA : Sg ≤ (alternatingGroup (Fin 5)).comap π)
    (hSmax : ∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → P ≤ (alternatingGroup (Fin 5)).comap π →
      Sg ≤ P → P ≤ Sg)
    {ψ : MulAut ↥E} (hψ : ψ ∈ Sg) (hψ2 : ψ * ψ = 1) :
    16 ≤ Nat.card ↥(Sg ⊓ Subgroup.centralizer ({ψ} : Set (MulAut ↥E))) := by
  obtain ⟨b₁, hb₁, b₂, hb₂, h11, h22, h12, h1, h2, h3⟩ := c.exists_klein_B
  obtain ⟨hφ1, hφ2, hcomm, hne, hnin⟩ := c.klein_kappa hb₁ hb₂ h11 h22 h12 h1 h2 h3
  obtain ⟨hS0card, hS0cs⟩ := hcs _ _ hφ1 hφ2 hcomm hne hnin
  set Sg0 := innAutE E ⊔ Subgroup.closure
    ({c.kappa ⟨b₁, hb₁⟩, c.kappa ⟨b₂, hb₂⟩} : Set (MulAut ↥E)) with hSg0
  set A := (alternatingGroup (Fin 5)).comap π with hA
  have hS0p : IsPGroup 2 Sg0 := IsPGroup.of_card (n := 6) (by rw [hS0card]; norm_num)
  have hS0A : Sg0 ≤ A := by
    refine sup_le ?_ ?_
    · intro φ hφ
      have : π φ = 1 := (hπ.ker φ).2 hφ
      show π φ ∈ alternatingGroup (Fin 5)
      rw [this]; exact one_mem _
    · rw [Subgroup.closure_le]
      intro φ hφ
      rcases hφ with rfl | rfl
      · exact hφ1.2.1
      · exact hφ2.2.1
  have hS0max : ∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → P ≤ A → Sg0 ≤ P → P ≤ Sg0 := by
    intro P hP hPA hle
    have hdvd : Nat.card P ∣ 960 := (c.card_AE hπ) ▸ Subgroup.card_dvd_of_le hPA
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    have hk6 : k ≤ 6 := by
      by_contra hk7
      have h128 : 2 ^ 7 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h128.trans (hk ▸ hdvd)
      norm_num at this
    have hle64 : Nat.card P ≤ 64 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
        _ = 64 := by norm_num
    have heq : Sg0 = P := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq]
  obtain ⟨g, hgA, hg⟩ := sylow_conj hS0A hSA hS0p hS2 hS0max hSmax
  have hψ' : g⁻¹ * ψ * g ∈ Sg0 := (hg ψ).1 hψ
  have hψ'2 : (g⁻¹ * ψ * g) * (g⁻¹ * ψ * g) = 1 := by
    calc (g⁻¹ * ψ * g) * (g⁻¹ * ψ * g) = g⁻¹ * (ψ * ψ) * g := by group
      _ = 1 := by rw [hψ2]; group
  have h16 := hS0cs _ hψ' hψ'2
  have hmem : ∀ u : ↥(Sg0 ⊓ Subgroup.centralizer ({g⁻¹ * ψ * g} : Set (MulAut ↥E))),
      g * (u : MulAut ↥E) * g⁻¹ ∈ Sg ⊓ Subgroup.centralizer ({ψ} : Set (MulAut ↥E)) := by
    intro u
    refine ⟨(hg _).2 (by simpa [mul_assoc] using u.2.1),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hu := Subgroup.mem_centralizer_singleton_iff.1 u.2.2
    calc g * (u : MulAut ↥E) * g⁻¹ * ψ = g * ((u : MulAut ↥E) * (g⁻¹ * ψ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * ψ * g) * (u : MulAut ↥E)) * g⁻¹ := by rw [hu]
      _ = ψ * (g * (u : MulAut ↥E) * g⁻¹) := by group
  refine le_trans h16 (Nat.card_le_card_of_injective
    (fun u => (⟨g * (u : MulAut ↥E) * g⁻¹, hmem u⟩ :
      ↥(Sg ⊓ Subgroup.centralizer ({ψ} : Set (MulAut ↥E))))) ?_)
  intro a b hab
  have h5 := congrArg Subtype.val hab
  apply Subtype.ext
  have : g * (a : MulAut ↥E) * g⁻¹ = g * (b : MulAut ↥E) * g⁻¹ := h5
  simpa using this

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
