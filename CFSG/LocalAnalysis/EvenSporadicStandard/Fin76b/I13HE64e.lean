module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64d

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α) {P : Subgroup G} (pd : c.PData P)

section A

variable {b₁ b₂ : G} (k : IsKlein B b₁ b₂) (kE : c.KleinE b₁ b₂)
  (hinv : ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P)

include c pd k kE hinv

omit hinv in
theorem sq_A1 {p : G} (hp : p ∈ P ⊓ centralizer ({b₁, b₂} : Set G)) : p * p = 1 := by
  have hpP : p ∈ P := hp.1
  have hc₁ : b₁ * p = p * b₁ := mem_centralizer_iff.1 hp.2 b₁ (by simp)
  have hconj : b₁ * p * b₁⁻¹ = p := by rw [hc₁]; group
  have hθ := c.theta_mem (pd.le hpP)
  have hfix : b₁ * (p * (z * p * z⁻¹)) * b₁⁻¹ = p * (z * p * z⁻¹) := by
    rw [← c.theta_conj_B' k.mem₁ p, hconj]
  have hsq := kE.fix_sq _ hθ hfix
  have h1 : (p * p) * (z * (p * p) * z⁻¹) = 1 * (z * 1 * z⁻¹) := by
    rw [c.theta_mul' (pd.le hpP) (pd.le hpP), hsq]
    group
  exact pd.inj _ (mul_mem hpP hpP) 1 P.one_mem h1

theorem four_le_card_A1 : 4 ≤ Nat.card ↥(P ⊓ centralizer ({b₁, b₂} : Set G)) := by
  classical
  choose! f hfP hfθ using pd.surj
  set F : Set G := {e : G | e ∈ E ∧ b₁ * e * b₁⁻¹ = e} with hF
  have hmaps : ∀ e ∈ F, f e ∈ ((P ⊓ centralizer ({b₁, b₂} : Set G) : Subgroup G) : Set G) := by
    rintro e ⟨he, hfix⟩
    have hfe := hfP e he
    have hθ := hfθ e he
    refine ⟨hfe, mem_centralizer_iff.2 ?_⟩
    have key : ∀ b : G, b ∈ closure ({b₁, b₂} : Set G) → b * e * b⁻¹ = e → b * f e * b⁻¹ = f e := by
      intro b hb hbe
      have hbB := k.grp_le hb
      have hbP : b * f e * b⁻¹ ∈ P := hinv b hb _ hfe
      have h1 : (b * f e * b⁻¹) * (z * (b * f e * b⁻¹) * z⁻¹) = f e * (z * f e * z⁻¹) := by
        rw [c.theta_conj_B' hbB, hθ, hbe]
      exact pd.inj _ hbP _ hfe h1
    rintro h (rfl | rfl)
    · have := key h IsKlein.b₁_mem_grp hfix
      calc h * f e = (h * f e * h⁻¹) * h := by group
        _ = f e * h := by rw [this]
    · have := key h IsKlein.b₂_mem_grp (kE.fix_sub e he hfix)
      calc h * f e = (h * f e * h⁻¹) * h := by group
        _ = f e * h := by rw [this]
  have hinj : Set.InjOn f F := by
    rintro e ⟨he, -⟩ e' ⟨he', -⟩ h
    rw [← hfθ e he, ← hfθ e' he', h]
  have h1 := Set.ncard_le_ncard_of_injOn f hmaps hinj (Set.toFinite _)
  rw [kE.fix_card] at h1
  have h2 : Set.ncard (((P ⊓ centralizer ({b₁, b₂} : Set G) : Subgroup G) : Set G)) =
      Nat.card ↥(P ⊓ centralizer ({b₁, b₂} : Set G)) := (Nat.card_coe_set_eq _).symm
  omega

theorem exists_E64_of_PData {b : G} (hb : b ∈ closure ({b₁, b₂} : Set G)) :
    ∃ A₀ : Subgroup G, A₀ ≤ centralizer ({b} : Set G) ∧ (∀ a ∈ A₀, a * a = 1) ∧
      64 ≤ Nat.card A₀ := by
  set A₁ : Subgroup G := P ⊓ centralizer ({b₁, b₂} : Set G) with hA₁
  set A₂ : Subgroup G := E64.P2 P z ⊓ centralizer ({b₁, b₂} : Set G) with hA₂
  set A₃ : Subgroup G := closure ({b₁, b₂} : Set G) with hA₃
  have hBmem : ∀ h ∈ ({b₁, b₂} : Set G), h ∈ B := by
    rintro h (rfl | rfl)
    exacts [k.mem₁, k.mem₂]
  have hcl : ∀ a ∈ centralizer ({b₁, b₂} : Set G), ∀ g ∈ A₃, g * a = a * g := by
    intro a ha g hg
    rw [← Subgroup.centralizer_closure] at ha
    exact mem_centralizer_iff.1 ha g hg
  have hzc : ∀ x ∈ centralizer ({b₁, b₂} : Set G),
      z * x * z⁻¹ ∈ centralizer ({b₁, b₂} : Set G) := by
    intro x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro h hh
    have hzh : h * z = z * h := c.B_comm_z (hBmem h hh)
    have hzh' : z * h * z⁻¹ = h := by rw [← hzh]; group
    have hxh := hx h hh
    calc h * (z * x * z⁻¹) = (z * (h * x) * z⁻¹) := by
          calc h * (z * x * z⁻¹) = (h * z) * x * z⁻¹ := by group
            _ = (z * h) * x * z⁻¹ := by rw [hzh]
            _ = z * (h * x) * z⁻¹ := by group
      _ = z * (x * h) * z⁻¹ := by rw [hxh]
      _ = (z * x * z⁻¹) * (z * h * z⁻¹) := by group
      _ = (z * x * z⁻¹) * h := by rw [hzh']
  have hA₁sq : ∀ a ∈ A₁, a * a = 1 := fun a ha => c.sq_A1 pd k kE ha
  have hA₁P : ∀ a ∈ A₁, a ∈ P := fun a ha => ha.1
  have hA₂mem : ∀ a ∈ A₁, z * a * z⁻¹ ∈ A₂ := fun a ha =>
    ⟨c.z_conj_mem_P2 ha.1, hzc a ha.2⟩
  have hA₂sq : ∀ a ∈ A₂, a * a = 1 := by
    intro a ha
    have h1 : z * a * z⁻¹ ∈ A₁ := ⟨E64.mem_P2.1 ha.1, hzc a ha.2⟩
    have h2 := hA₁sq _ h1
    have hz2 : z * z = 1 := c.h.z_sq
    calc a * a = (z * z) * (a * a) * (z * z)⁻¹ := by rw [hz2]; group
      _ = z * ((z * a * z⁻¹) * (z * a * z⁻¹)) * z⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hA₃sq : ∀ a ∈ A₃, a * a = 1 := fun a ha => k.sq_grp ha
  have hcard₁ : 4 ≤ Nat.card A₁ := c.four_le_card_A1 pd k kE hinv
  have hcard₂ : 4 ≤ Nat.card A₂ := by
    refine hcard₁.trans (Nat.card_le_card_of_injective
      (fun a : A₁ => (⟨z * a * z⁻¹, hA₂mem a a.2⟩ : A₂)) ?_)
    intro a a' h
    have h1 : z * (a : G) * z⁻¹ = z * (a' : G) * z⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  have hcard₃ : 4 ≤ Nat.card A₃ := by
    have hne1 : b₁ * b₂ ≠ b₁ := fun h =>
      k.ne₂ (mul_left_cancel (a := b₁) (by rw [mul_one]; exact h))
    have hne2 : b₁ * b₂ ≠ b₂ := fun h =>
      k.ne₁ (mul_right_cancel (show b₁ * b₂ = 1 * b₂ by rw [one_mul]; exact h))
    have hne3 : b₁ * b₂ ≠ 1 := k.prod_ne_one
    have hset : ({1, b₁, b₂, b₁ * b₂} : Set G).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hne2.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨k.ne₁₂, hne1.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨k.ne₁.symm, k.ne₂.symm, hne3.symm⟩
    have hsub : ({1, b₁, b₂, b₁ * b₂} : Set G) ⊆ (A₃ : Set G) := by
      rintro y (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact IsKlein.b₁_mem_grp
      · exact IsKlein.b₂_mem_grp
      · exact mul_mem IsKlein.b₁_mem_grp IsKlein.b₂_mem_grp
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : Set.ncard ((A₃ : Subgroup G) : Set G) = Nat.card A₃ := (Nat.card_coe_set_eq _).symm
    omega
  have hc12 : A₂ ≤ centralizer (A₁ : Set G) := by
    intro a' ha'
    rw [mem_centralizer_iff]
    intro a ha
    exact c.P_comm_P2 pd (hA₁P a ha) ha'.1
  have hd12 : Disjoint A₁ A₂ := by
    refine Subgroup.disjoint_def.2 ?_
    intro x hx1 hx2
    exact c.P_inf_P2 pd hx1.1 hx2.1
  have hA₁₂Q : A₁ ⊔ A₂ ≤ c.Qs :=
    sup_le (fun a ha => c.P_le_Qs pd ha.1) (fun a ha => c.P2_le_Qs pd ha.1)
  have hc3 : A₃ ≤ centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (fun a ha => mem_centralizer_iff.2 fun g hg => hcl a ha.2 g hg)
      (fun a ha => mem_centralizer_iff.2 fun g hg => hcl a ha.2 g hg)
  have hd3 : Disjoint (A₁ ⊔ A₂) A₃ := by
    refine Subgroup.disjoint_def.2 ?_
    intro x hx1 hx3
    have hxQ := (c.mem_Qs.1 (hA₁₂Q hx1)).1
    exact c.h.B_inf_F c.hα (k.grp_le hx3) hxQ
  have hcard12 : Nat.card ↥(A₁ ⊔ A₂) = Nat.card A₁ * Nat.card A₂ := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (mulEquivProdSup hc12 hd12).toEquiv.symm
  have hcard123 : Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) = Nat.card ↥(A₁ ⊔ A₂) * Nat.card A₃ := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (mulEquivProdSup hc3 hd3).toEquiv.symm
  refine ⟨A₁ ⊔ A₂ ⊔ A₃, ?_, ?_, ?_⟩
  · refine sup_le (sup_le (fun a ha => ?_) (fun a ha => ?_)) (fun a ha => ?_)
    · exact mem_centralizer_singleton_iff.2 (hcl a ha.2 b hb).symm
    · exact mem_centralizer_singleton_iff.2 (hcl a ha.2 b hb).symm
    · exact mem_centralizer_singleton_iff.2 (k.comm_grp ha hb)
  · exact I13HE64.sq_eq_one_of_mem_sup hc3 (I13HE64.sq_eq_one_of_mem_sup hc12 hA₁sq hA₂sq) hA₃sq
  · rw [hcard123, hcard12]
    calc 64 = 4 * 4 * 4 := by norm_num
      _ ≤ Nat.card A₁ * Nat.card A₂ * Nat.card A₃ :=
        Nat.mul_le_mul (Nat.mul_le_mul hcard₁ hcard₂) hcard₃

end A

omit pd in
theorem exists_E64 (hF : EFacts613 E t) {b₁ b₂ : G} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h11 : b₁ * b₁ = 1) (h22 : b₂ * b₂ = 1) (h12 : b₁ * b₂ = b₂ * b₁) (h1 : b₁ ≠ 1) (h2 : b₂ ≠ 1)
    (h3 : b₁ ≠ b₂) {q b : G} (hq : q ∈ c.Qs) (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂)
    (hx2 : (q * b) * (q * b) = 1) :
    ∃ A : Subgroup G, A ≤ centralizer ({q * b} : Set G) ∧ (∀ a ∈ A, a * a = 1) ∧
      64 ≤ Nat.card A := by
  have k : IsKlein B b₁ b₂ := ⟨hb₁, hb₂, h11, h22, h12, h1, h2, h3⟩
  have kE := c.kleinE_of_facts hF k
  obtain ⟨P, pd, hinv⟩ := c.exists_PData k kE
  obtain ⟨g, -, hqb⟩ := c.exists_conj_of_inv pd k kE hinv hb hq hx2
  obtain ⟨A₀, hA₀c, hA₀2, hA₀card⟩ :=
    c.exists_E64_of_PData pd k kE hinv (E64.mem_grp_of hb)
  refine ⟨A₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff, hqb]
    have hab : a * b = b * a := mem_centralizer_singleton_iff.1 (hA₀c ha)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hA₀2 a ha]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hA₀card

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
