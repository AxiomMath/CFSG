module

public import CFSG.CGT.T75D.TypeBound
public import CFSG.CGT.T75D.ComponentSplit
public import CFSG.CGT.T75D.QuasiLemmas
public import CFSG.CGT.T75D.LayerBasic
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.Goldschmidt CFSG.CGT.Timmesfeld75

section Card

theorem card_map_of_inf_ker_eq_bot {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {P : Subgroup G} (h : P ⊓ f.ker = ⊥) : Nat.card (P.map f) = Nat.card P := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : P => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : P.map f)) ⟨?_, ?_⟩)).symm
  · intro x y hxy
    have h1 : f x = f y := congrArg Subtype.val hxy
    have h2 : (x : G)⁻¹ * y ∈ P ⊓ f.ker := ⟨P.mul_mem (P.inv_mem x.2) y.2, MonoidHom.mem_ker.2 (by
      rw [map_mul, map_inv, h1]; group)⟩
    rw [h, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

end Card

section Case

variable {H : Type} [Group H] [Finite H]

theorem case_bound
    (hcentral : ∀ o ∈ goldschmidtOddCore H, ∀ h : H, h * o = o * h)
    {X : Subgroup (H ⧸ goldschmidtOddCore H)} [X.Normal] (hXq : CFSG.Open.IsQuasisimple ↥X)
    (hsup : X ⊔ Subgroup.centralizer (X : Set (H ⧸ goldschmidtOddCore H)) = ⊤)
    (htype : goldschmidtSimpleType (↥X ⧸ Subgroup.center ↥X))
    {H₁ : Subgroup H}
    (hXM₁ : ¬ X ≤ H₁.map (QuotientGroup.mk' (goldschmidtOddCore H)))
    {P : Subgroup H} (hP : IsElemAbelian 2 P)
    (h36 : ∀ g : H, (∃ y ∈ P, y ≠ 1 ∧ ∃ y' ∈ P, y = g * y' * g⁻¹) →
      ∀ y₁ ∈ P, ∀ y₂ ∈ P, (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹))
    {p : H} (hpP : p ∈ P)
    (hpC : QuotientGroup.mk' (goldschmidtOddCore H) p ∉
      Subgroup.centralizer (X : Set (H ⧸ goldschmidtOddCore H)))
    {N : Type*} [Group N] [Finite N] {d : ℕ} (hN : Nat.card N = 2 ^ d)
    (ρ : H →* MulAut N) (hρ : ρ.ker ≤ H₁) :
    Nat.card P ≤ 8 ∨ Nat.card P ^ 2 ≤ 2 ^ d := by
  set O : Subgroup H := goldschmidtOddCore H with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  set C : Subgroup (H ⧸ O) := Subgroup.centralizer (X : Set (H ⧸ O)) with hC
  have hodd : Odd (Nat.card O) := odd_card_goldschmidtOddCore H
  have hsq : ∀ y ∈ P, y * y = 1 := fun y hy => by simpa [pow_two] using hP.2 y hy
  set P' : Subgroup (H ⧸ O) := P.map π with hP'
  have h36M : ∀ g ∈ X, (∃ y ∈ P', y ≠ 1 ∧ ∃ y' ∈ P', y = g * y' * g⁻¹) →
      ∀ y₁ ∈ P', ∀ y₂ ∈ P', (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹) := by
    rintro g _ ⟨y, ⟨β, hβP, rfl⟩, hy1, y', ⟨β', hβ'P, rfl⟩, hyy'⟩ y₁ ⟨z₁, hz₁P, rfl⟩ y₂
      ⟨z₂, hz₂P, rfl⟩
    obtain ⟨gt, rfl⟩ := QuotientGroup.mk_surjective g
    have hβe : β = gt * β' * gt⁻¹ := by
      refine eq_of_mk_eq O hcentral hodd (hsq β hβP) ?_ ?_
      · calc gt * β' * gt⁻¹ * (gt * β' * gt⁻¹) = gt * (β' * β') * gt⁻¹ := by group
          _ = 1 := by rw [hsq β' hβ'P]; group
      · show π β = π (gt * β' * gt⁻¹)
        rw [map_mul, map_mul, map_inv]
        exact hyy'
    have hβ1 : β ≠ 1 := by
      intro h1
      apply hy1
      rw [h1, map_one]
    have := h36 gt ⟨β, hβP, hβ1, β', hβ'P, hβe⟩ z₁ hz₁P z₂ hz₂P
    have h2 := congrArg π this
    simp only [map_mul, map_inv] at h2
    exact h2
  have hnot : ¬ P' ≤ C := fun h => hpC (h ⟨p, hpP, rfl⟩)
  have hPC : P' ⊓ C = ⊥ := inf_centralizer_eq_bot_of_not_le hXq h36M hnot
  obtain ⟨e⟩ := exists_mulEquiv_quotient_centralizer hsup
  have : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hXq.2
  have hS : IsSimpleGroup ((H ⧸ O) ⧸ C) := e.symm.isSimpleGroup
  have hStype : goldschmidtSimpleType ((H ⧸ O) ⧸ C) := goldschmidtSimpleType_of_mulEquiv e htype
  set mk : (H ⧸ O) →* ((H ⧸ O) ⧸ C) := QuotientGroup.mk' C with hmk
  set V : Subgroup ((H ⧸ O) ⧸ C) := P'.map mk with hV
  have hVel : IsElemAbelian 2 V := isElemAbelian_map_of_hom (isElemAbelian_map_of_hom hP π) mk
  have hVcard : Nat.card V = Nat.card P := by
    have h1 : Nat.card V = Nat.card P' := card_map_of_inf_ker_eq_bot mk (by
      rw [hmk, QuotientGroup.ker_mk']; exact hPC)
    have h2 : Nat.card P' = Nat.card P := card_map_of_inf_ker_eq_bot π (by
      rw [eq_bot_iff]
      intro y ⟨hyP, hyO⟩
      have hy : (QuotientGroup.mk' O) y = (QuotientGroup.mk' O) 1 := by
        rw [map_one]; exact (QuotientGroup.eq_one_iff y).2 (by simpa [hπ] using hyO)
      exact (Subgroup.mem_bot.2 (eq_of_mk_eq O hcentral hodd (hsq y hyP) (by group) hy)))
    rw [h1, h2]
  set Xh : Subgroup H := X.comap π with hXh
  let ψ : ↥Xh →* ↥X := (π.comp Xh.subtype).codRestrict X (fun h => h.2)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (x : H ⧸ O)
    exact ⟨⟨h, by show π h ∈ X; rw [hπ]; simpa using (hh ▸ x.2)⟩, Subtype.ext hh⟩
  let θ : ↥Xh →* ((H ⧸ O) ⧸ C) := mk.comp (X.subtype.comp ψ)
  have hθ : Function.Surjective θ := by
    intro s
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
    have hm : m ∈ ((X ⊔ C : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal] at hm
    obtain ⟨x, hx, c, hc, rfl⟩ := hm
    obtain ⟨h, hh⟩ := hψ ⟨x, hx⟩
    refine ⟨h, ?_⟩
    show mk ((ψ h : ↥X) : H ⧸ O) = mk (x * c)
    rw [hh]
    show (QuotientGroup.mk x : (H ⧸ O) ⧸ C) = QuotientGroup.mk (x * c)
    rw [QuotientGroup.eq]
    simpa using hc
  let ρ' : ↥Xh →* MulAut N := ρ.comp Xh.subtype
  have hker : ρ'.ker ≤ θ.ker := by
    set W : Subgroup ↥X := ρ'.ker.map ψ with hW
    have hWn : W.Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hWtop : W ≠ ⊤ := by
      intro htop
      apply hXM₁
      intro x hx
      have hxW : (⟨x, hx⟩ : ↥X) ∈ W := by rw [htop]; trivial
      obtain ⟨h, hh, hhx⟩ := hxW
      have hρh : ρ (h : H) = 1 := hh
      refine ⟨(h : H), hρ hρh, ?_⟩
      exact congrArg Subtype.val hhx
    have hWc : W ≤ Subgroup.center ↥X := normal_le_center hXq W hWtop
    intro h hh
    have hψh : ψ h ∈ Subgroup.center ↥X := hWc ⟨h, hh, rfl⟩
    have hcent : ((ψ h : ↥X) : H ⧸ O) ∈ C := (mem_centralizer_iff_mem_center _).2 hψh
    show mk ((ψ h : ↥X) : H ⧸ O) = 1
    exact (QuotientGroup.eq_one_iff _).2 hcent
  have := typeBound_of_ker_le hStype hVel hN ρ' θ hθ hker
  rw [hVcard] at this
  exact this

omit [Finite H] in
theorem isElemAbelian_of_le' {A P : Subgroup H} (hA : IsElemAbelian 2 A) (hP : P ≤ A) :
    IsElemAbelian 2 P := CFSG.Open.IsElemAbelian.mono hA hP

theorem layer_bound
    (hcentral : ∀ o ∈ goldschmidtOddCore H, ∀ h : H, h * o = o * h)
    (ha : CFSG.pCore 2 (H ⧸ goldschmidtOddCore H) ⊔
      goldschmidtLayer (H ⧸ goldschmidtOddCore H) = ⊤)
    (hc : ∀ X : Subgroup (H ⧸ goldschmidtOddCore H), IsComponentOf X ⊤ →
      goldschmidtSimpleType (↥X ⧸ Subgroup.center ↥X))
    {A P₁ P₂ : Subgroup H} (hA : IsElemAbelian 2 A) (hP₁ : P₁ ≤ A) (hP₂ : P₂ ≤ A)
    (hAP : ∀ α ∈ A, ∃ a ∈ P₁, ∃ b ∈ P₂, α = a * b)
    (h36₁ : ∀ g : H, (∃ y ∈ P₁, y ≠ 1 ∧ ∃ y' ∈ P₁, y = g * y' * g⁻¹) →
      ∀ y₁ ∈ P₁, ∀ y₂ ∈ P₁, (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹))
    (h36₂ : ∀ g : H, (∃ y ∈ P₂, y ≠ 1 ∧ ∃ y' ∈ P₂, y = g * y' * g⁻¹) →
      ∀ y₁ ∈ P₂, ∀ y₂ ∈ P₂, (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹))
    {H₁ : Subgroup H} (hH₁ : CFSG.pCore 2 H ≤ H₁)
    {N : Type*} [Group N] [Finite N] {d : ℕ} (hN : Nat.card N = 2 ^ d)
    (ρ : H →* MulAut N) (hρ : ρ.ker ≤ H₁) (hA₁ : ¬ A ≤ H₁) :
    (Nat.card P₁ ≤ 8 ∨ Nat.card P₁ ^ 2 ≤ 2 ^ d) ∨ (Nat.card P₂ ≤ 8 ∨ Nat.card P₂ ^ 2 ≤ 2 ^ d) := by
  set O : Subgroup H := goldschmidtOddCore H with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hodd : Odd (Nat.card O) := odd_card_goldschmidtOddCore H
  have hOM : goldschmidtOddCore (H ⧸ O) = ⊥ := goldschmidtOddCore_quotient_eq_bot H
  have hQM₁ : CFSG.Open.pCore 2 (H ⧸ O) ≤ H₁.map π := by
    exact (pCore_quotient_le_map O hcentral).trans (Subgroup.map_mono hH₁)
  obtain ⟨α, hαA, hαH₁⟩ := IsConcreteLE.not_le_iff_exists.1 hA₁
  have hαα : α * α = 1 := by simpa [pow_two] using hA.2 α hαA
  have hπα : π α ∉ H₁.map π := fun h => hαH₁ (mem_of_mk_mem_map O hcentral hodd hαα h)
  have ha' : CFSG.Open.pCore 2 (H ⧸ O) ⊔ goldschmidtLayer (H ⧸ O) = ⊤ := by
    exact ha
  obtain ⟨X, hXc, hXM₁, x, hxX, hxne⟩ := exists_component_not_le hOM ha' hQM₁ hπα
  have hXn : X.Normal := comp_normal ha' hXc
  have hsup := comp_sup_centralizer ha' hXc
  obtain ⟨a, haP₁, b, hbP₂, hab⟩ := hAP α hαA
  have hnc : π a ∉ Subgroup.centralizer (X : Set (H ⧸ O)) ∨
      π b ∉ Subgroup.centralizer (X : Set (H ⧸ O)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hmem : π α ∈ Subgroup.centralizer (X : Set (H ⧸ O)) := by
      rw [hab, map_mul]
      exact Subgroup.mul_mem _ h1 h2
    exact hxne ((Subgroup.mem_centralizer_iff.1 hmem x hxX).symm)
  rcases hnc with h | h
  · exact Or.inl (case_bound hcentral hXc.2.2 hsup (hc X hXc) hXM₁
      (isElemAbelian_of_le' hA hP₁) h36₁ haP₁ h hN ρ hρ)
  · exact Or.inr (case_bound hcentral hXc.2.2 hsup (hc X hXc) hXM₁
      (isElemAbelian_of_le' hA hP₂) h36₂ hbP₂ h hN ρ hρ)

end Case

end CFSG.CGT.T75D
