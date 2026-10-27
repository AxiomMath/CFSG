module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Cls
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSetting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillC

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G] [Finite G] {T₁ : Subgroup G} {N : ℕ} {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T₁ N mul) {inv : ℕ → ℕ} {gens : List ℕ} (h0 : mul 0 0 = 0)
  (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N)

noncomputable abbrev eltT (c : ℕ) : G := (Φ.g c : G)

omit [Finite G] in
include Φ h0 hinv hgens hG in
theorem inf_centralizer_le_of_not_mem {y : G} (hyN : y ∈ normalizer (T₁ : Set G))
    (hy2 : y * y ∈ T₁) {B : ℕ → ℕ} (hB : ∀ g : T₁, Φ.f (conjEquiv hyN g) = B (Φ.f g))
    {r : ℕ} (hr : r < N) (hO : orbOK mul inv N r (recM mul inv gens r) = true)
    (hCl : orbClosed mul inv gens r (recM mul inv gens r) = true)
    (hBr : B r ∉ (recM mul inv gens r).map Prod.fst) {g : T₁} :
    (T₁ ⊔ zpowers y) ⊓ centralizer ({((g * Φ.g r * g⁻¹ : T₁) : G)} : Set G) ≤ T₁ := by
  intro x hx
  obtain ⟨hxT₂, hxC⟩ := mem_inf.1 hx
  rcases (mem_sup_zpowers_iff hyN hy2).1 hxT₂ with h | h
  · exact h
  · exfalso
    set a : T₁ := ⟨x * y⁻¹, h⟩
    set u : T₁ := g * Φ.g r * g⁻¹
    have hxu : x * (u : G) * x⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hxC
      rw [this]; group
    have hx : x = (a : G) * y := by simp [a]
    have hyu : conjEquiv hyN u = a⁻¹ * u * a := by
      apply Subtype.ext
      rw [conjEquiv_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 := hxu
      rw [hx] at h1
      have : (a : G) * (y * u * y⁻¹) * (a : G)⁻¹ = u := by
        calc (a : G) * (y * u * y⁻¹) * (a : G)⁻¹ = (a : G) * y * u * ((a : G) * y)⁻¹ := by group
          _ = u := h1
      calc y * (u : G) * y⁻¹ = (a : G)⁻¹ * ((a : G) * (y * u * y⁻¹) * (a : G)⁻¹) * a := by group
        _ = (a : G)⁻¹ * u * a := by rw [this]
    have hyuG : y * (u : G) * y⁻¹ = (a : G)⁻¹ * u * a := by
      have := congrArg Subtype.val hyu
      simpa only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hmem : conjEquiv hyN (Φ.g r) ∈ MulAction.orbit (ConjAct T₁) (Φ.g r) := by
      rw [mem_orbit_iff_conj]
      refine ⟨(conjEquiv hyN g)⁻¹ * a⁻¹ * g, Subtype.ext ?_⟩
      simp only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      have hu : (u : G) = g * Φ.g r * (g : G)⁻¹ := by simp [u]
      calc (y * g * y⁻¹)⁻¹ * (a : G)⁻¹ * g * Φ.g r * ((y * g * y⁻¹)⁻¹ * (a : G)⁻¹ * g)⁻¹
          = (y * g * y⁻¹)⁻¹ * ((a : G)⁻¹ * (g * Φ.g r * (g : G)⁻¹) * a) * (y * g * y⁻¹) := by group
        _ = (y * g * y⁻¹)⁻¹ * (y * (g * Φ.g r * (g : G)⁻¹) * y⁻¹) * (y * g * y⁻¹) := by
            rw [← hu, hyuG]
        _ = y * Φ.g r * y⁻¹ := by group
    have hrO : orbOK mul inv N (Φ.f (Φ.g r)) (recM mul inv gens r) = true := by rw [Φ.f_g hr]; exact hO
    have hrC : orbClosed mul inv gens (Φ.f (Φ.g r)) (recM mul inv gens r) = true := by
      rw [Φ.f_g hr]; exact hCl
    have := (Φ.mem_orbit_iff h0 hinv hgens hG hrO hrC _).1 hmem
    rw [hB, Φ.f_g hr] at this
    exact hBr this

include Φ h0 hinv hgens hG in
theorem l2D_of {t : G} {TH : Subgroup G} {y : G} (hyN : y ∈ normalizer (T₁ : Set G))
    (hy2 : y * y ∈ T₁) {B : ℕ → ℕ} (hB : ∀ g : T₁, Φ.f (conjEquiv hyN g) = B (Φ.f g))
    {C : List (ℕ × ℕ)} (hcls : kClassOK mul inv gens N C = true) (hTHT₁ : TH ≤ T₁) {m : ℕ}
    (hm : Nat.card TH * m = 2 * N)
    (hact : ∀ r ∈ kRepsC C m, B r ∉ (recM mul inv gens r).map Prod.fst ∨
      ∀ K : Subgroup G, K ≤ TH → K.relIndex TH = 2 → t ∈ K →
        (nInv K, nOrd4 K) ≠ (nInv (T₁ ⊓ centralizer ({eltT Φ r} : Set G)),
          nOrd4 (T₁ ⊓ centralizer ({eltT Φ r} : Set G)))) :
    ∀ u ∈ T₁, u * u = 1 →
      2 * Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) = Nat.card TH →
        (T₁ ⊔ zpowers y) ⊓ centralizer ({u} : Set G) ≤ T₁ ∨
        ∀ K : Subgroup G, K ≤ TH → K.relIndex TH = 2 → t ∈ K →
          (nInv K, nOrd4 K) ≠ (nInv (T₁ ⊓ centralizer ({u} : Set G)),
            nOrd4 (T₁ ⊓ centralizer ({u} : Set G))) := by
  intro u huT hu2 hcard
  have hfin := Φ.finite
  set u' : T₁ := ⟨u, huT⟩
  have hu2' : u' * u' = 1 := Subtype.ext hu2
  have hcc : Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (centralizer ({u'} : Set T₁)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_centralizer_singleton_iff.1 x.2.2))⟩
        invFun := fun y => ⟨y.1, y.1.2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have horb : (MulAction.orbit (ConjAct T₁) u').ncard = m := by
    have e1 := card_centralizer_mul_ncard u'
    rw [← hcc, Φ.card_univ] at e1
    have hpos : 0 < Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) := Nat.card_pos
    have : Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) * (2 * m) =
        Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) *
          (2 * (MulAction.orbit (ConjAct T₁) u').ncard) := by
      rw [← mul_assoc, mul_comm _ 2, hcard, hm, ← e1]; ring
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega
  have hu1 : u' ≠ 1 := by
    rintro h
    have h1 : u = 1 := congrArg Subtype.val h
    have hle : Nat.card TH ≤ Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) := by
      refine Subgroup.card_le_of_le (le_inf hTHT₁ fun x _ => ?_)
      rw [mem_centralizer_singleton_iff, h1, one_mul, mul_one]
    have hpos : 0 < Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) := Nat.card_pos
    omega
  obtain ⟨hnd, hrecC, hsumC⟩ := classOK_parts hcls
  obtain ⟨c, hc, g, hgu, hcm⟩ := exists_rep Φ h0 hinv hgens hG (recM mul inv gens) hnd hrecC hsumC
    hu2' hu1
  rw [horb] at hcm
  have hcR : c.1 ∈ kRepsC C m := by
    unfold kRepsC
    exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by rw [beq_iff_eq, hcm]⟩, rfl⟩
  obtain ⟨hrl, -, -, hO, hCl, -, -⟩ := hrecC c hc
  have hug : u = ((g * Φ.g c.1 * g⁻¹ : T₁) : G) := by rw [hgu]
  rcases hact c.1 hcR with hBr | hK
  · left
    rw [hug]
    exact inf_centralizer_le_of_not_mem Φ h0 hinv hgens hG hyN hy2 hB hrl hO hCl hBr
  · right
    have hgN : (g : G) ∈ normalizer (T₁ : Set G) := le_normalizer g.2
    have hmap := map_conj_inf_centralizer hgN (eltT Φ c.1)
    have e1 : (g : G) * eltT Φ c.1 * (g : G)⁻¹ = u := by rw [hug]; simp [eltT]
    rw [e1] at hmap
    intro K hKTH hKi htK
    rw [← hmap, nInv_map, nOrd4_map]
    exact hK K hKTH hKi htK

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
