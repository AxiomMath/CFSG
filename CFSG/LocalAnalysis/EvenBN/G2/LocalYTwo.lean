module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalY

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

theorem elemModulo_of_mul_self_mem {G : Type*} [Group G] {N E : Subgroup G}
    (hEN : E ≤ normalizer (N : Set G)) (hsq : ∀ x ∈ E, x * x ∈ N) : ElemModulo N E := by
  intro x hx y hy
  refine ⟨hsq x hx, ?_⟩
  have e : ⁅x, y⁆ = (x * y) * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
    ((mem_normalizer_iff.1 (hEN (inv_mem hy)) _).1 (inv_mem (hsq x hx)))) (inv_mem (hsq y hy))

theorem normalizer_le_normalizer_closure_sq {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤
      normalizer ((closure {z | ∃ g ∈ H, z = g ^ 2} : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact subset_closure ⟨n * g * n⁻¹, (mem_normalizer_iff.1 hn g).1 hg, by rw [sq, sq]; group⟩
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact inv_mem hx

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

theorem mem_M_or_mem_U_of_commute {x y : ModGL .G2 K} (hx : x ∈ S K) (hy : y ∈ Y K)
    (hxy : x * y = y * x) : x ∈ M K ∨ y ∈ U K := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  obtain ⟨e, f, rfl⟩ := mem_Y.1 hy
  have h1 : ⁅g2N A B C D E F, g2N 0 0 0 0 e f⁆ = 1 := by
    rw [commutatorElement_def, hxy, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨-, -, -, h⟩ := coords_of_commutator_eq_one h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero, zero_add] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (g2N_mem_M_iff.2 h)
  · exact Or.inr (g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, h⟩)

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [CharP K 2]

theorem mem_M_or_mem_U_of_commute {x y : G} (hx : x ∈ d.S) (hy : y ∈ d.Y) (hxy : x * y = y * x) :
    x ∈ d.M ∨ y ∈ d.U := by
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
  obtain ⟨g', hg', rfl⟩ := d.mem_image.1 hy
  have e : g * g' = g' * g := d.emb_injective (by rw [map_mul, map_mul, hxy])
  rcases Model.mem_M_or_mem_U_of_commute hg hg' (congrArg Subtype.val e) with h | h
  · exact Or.inl (d.emb_mem_image h)
  · exact Or.inr (d.emb_mem_image h)

theorem not_D_le_M : ¬ d.D ≤ d.M := fun h =>
  Model.not_M_le_D.2 ((d.image_le_image_iff Model.D_le_adjointGroup).1 h)

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem tM_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.M ⊔ zpowers t ≤ yamadaL₂ d t := by
  rw [← (h.two_core_L₂ d hK).2.1]
  exact inf_le_left

theorem tD_le_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.D ⊔ zpowers t ≤ yamadaC₁ d t := by
  rw [← (h.two_core_C₁ d hK).2.1]
  exact inf_le_left

omit [Finite K] in
theorem S_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) :
    d.S ≤ normalizer (yamadaL₂ d t : Set G) := fun _ hs =>
  le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    ⟨h.S_le_centralizer d hs, d.S_le_normalizers.2.1 hs⟩)

omit [Finite K] in
theorem yamadaR₂_le_normalizer_tY (h : Setup G L f t) (d : G2Data L K) :
    yamadaR₂ d t ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (yamadaL₂_le d t) fun _ hs => h.centralizer_inf_normalizer_Y_le d
    ⟨h.S_le_centralizer d hs, d.S_le_normalizers.2.1 hs⟩

omit [Finite K] in
theorem yamadaR₁_le_normalizer_tU (h : Setup G L f t) (d : G2Data L K) :
    yamadaR₁ d t ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (yamadaC₁_le d t) fun _ hs => h.centralizer_inf_normalizer_U_le d
    ⟨h.S_le_centralizer d hs, d.S_le_normalizers.1 hs⟩

theorem yamadaR₂_le_centralizer_U (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₂ d t ≤ centralizer (d.U : Set G) := by
  rw [Subgroup.le_centralizer_iff, ← (h.yamada_5_5_4 d hK).2]
  exact inf_le_right

theorem yamadaR₂_le_normalizer_tM (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₂ d t ≤ normalizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [← (h.yamada_5_5_1 d hK).1]
  exact h.yamadaR₂_le_normalizer_tY d

theorem yamadaR₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR d t ≤ yamadaR₂ d t ∧ yamadaR₂ d t ⊓ centralizer ({t} : Set G) = yamadaR d t := by
  obtain ⟨-, h2, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hRR₂ : yamadaR d t ≤ yamadaR₂ d t := by
    rw [h.yamadaR_eq d]
    exact sup_le le_sup_right ((zpowers_le).2
      (mem_sup_left (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))))
  refine ⟨hRR₂, le_antisymm (fun z hz => ?_) (le_inf hRR₂ (h.yamadaR_le_centralizer d))⟩
  obtain ⟨hzR₂, hzt⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨x, hx, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₂ d) z hzR₂
  have hxC : x ∈ centralizer ({t} : Set G) := by
    have := mul_mem hzt (inv_mem (h.S_le_centralizer d hs))
    rwa [mul_inv_cancel_right] at this
  have hxB : x ∈ d.M ⊔ zpowers t := by
    rw [← h2]
    exact ⟨hx, hxC⟩
  rw [h.yamadaR_eq d]
  exact mul_mem (sup_le_sup_right hMS _ hxB) (mem_sup_left hs)

theorem yamadaR_le_yamadaR₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR d t ≤ yamadaR₁ d t := by
  obtain ⟨-, h2, -, -⟩ := h.two_core_C₁ d hK
  have htC₁ : t ∈ yamadaC₁ d t := by
    have : t ∈ d.D ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rw [← h2] at this
    exact this.1
  rw [h.yamadaR_eq d]
  exact sup_le le_sup_right ((zpowers_le).2 (mem_sup_left htC₁))

theorem yamadaC₁_le_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ≤ yamadaR₂ d t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form h.two_le K hK
  obtain ⟨hC₁U, hC₁t, hC₁tr, -⟩ := h.two_core_C₁ d hK
  obtain ⟨-, hL₂t, -, hfac⟩ := h.two_core_L₂ d hK
  obtain ⟨hRR₂, hR₂t⟩ := h.yamadaR₂_inf_centralizer d hK
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  have hc₁ := h.cosetData_tU d hK
  set C := centralizer ({t} : Set G) with hCdef
  set H₂ := normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) with hH₂
  have hYL : d.Y ≤ L := d.image_le _
  let ψ : G → (K ≃+* K) := fun g => if hg : g ∈ C then Θ (h.act d ⟨g, hg⟩) else 1
  have hψ : ∀ {g : G} (hg : g ∈ C), ψ g = Θ (h.act d ⟨g, hg⟩) := fun {g} hg => by
    simp only [ψ, hg, ↓reduceDIte]
  have hψmul : ∀ {g g' : G}, g ∈ C → g' ∈ C → ψ (g * g') = ψ g * ψ g' := fun hg hg' => by
    rw [hψ hg, hψ hg', hψ (mul_mem hg hg'), ← map_mul, ← map_mul]
    rfl
  have hψinv : ∀ {g : G}, g ∈ C → ψ g⁻¹ = (ψ g)⁻¹ := fun hg => by
    rw [hψ hg, hψ (inv_mem hg), ← map_inv, ← map_inv]
    rfl
  have hψ1 : ∀ {g : G} (hg : g ∈ C), ψ g = 1 ↔ g ∈ L ⊔ zpowers t := fun {g} hg => by
    rw [hψ hg, ← MonoidHom.mem_ker, hker, ← h.centralizer_L_inf]
    exact h.act_mem_inner_iff d ⟨g, hg⟩
  have hLt : ∀ {g : G}, g ∈ L → ψ g = 1 := fun hg =>
    (hψ1 (h.L_le_centralizer hg)).2 (mem_sup_left hg)
  let P : G → (K ≃+* K) → Prop := fun g σ =>
    ∃ c ∈ C ⊓ normalizer (d.Y : Set G), ∃ x ∈ yamadaL₂ d t, g = c * x ∧ ψ c = σ
  have hNC : C ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaL₂ d t : Set G) :=
    (h.centralizer_inf_normalizer_Y_le d).trans (le_normalizer_yamadaL₂ d t)
  have hPex : ∀ g ∈ H₂, ∃ σ, P g σ := fun g hg => by
    obtain ⟨c, hc, x, hx, rfl⟩ := hfac g hg
    exact ⟨ψ c, c, hc, x, hx, rfl, rfl⟩
  have hPuniq : ∀ {g σ σ'}, P g σ → P g σ' → σ = σ' := by
    rintro g σ σ' ⟨c, hc, x, hx, rfl, rfl⟩ ⟨c', hc', x', hx', he, rfl⟩
    replace hc := mem_inf.1 hc
    replace hc' := mem_inf.1 hc'
    have h1 : c'⁻¹ * c = x' * x⁻¹ := by
      calc c'⁻¹ * c = c'⁻¹ * (c * x) * x⁻¹ := by group
        _ = x' * x⁻¹ := by rw [he]; group
    have h2 : c'⁻¹ * c ∈ d.M ⊔ zpowers t := by
      rw [← hL₂t, h1]
      refine Subgroup.mem_inf.2 ⟨mul_mem hx' (inv_mem hx), ?_⟩
      rw [← h1]
      exact mul_mem (inv_mem hc'.1) hc.1
    have h3 : ψ (c'⁻¹ * c) = 1 :=
      (hψ1 (mul_mem (inv_mem hc'.1) hc.1)).2 (sup_le_sup_right (d.image_le _) _ h2)
    rw [hψmul (inv_mem hc'.1) hc.1, hψinv hc'.1, inv_mul_eq_one] at h3
    exact h3.symm
  have hPmul : ∀ {g g' σ σ'}, P g σ → P g' σ' → P (g * g') (σ * σ') := by
    rintro g g' σ σ' ⟨c, hc, x, hx, rfl, rfl⟩ ⟨c', hc', x', hx', rfl, rfl⟩
    refine ⟨c * c', mul_mem hc hc', c'⁻¹ * x * c' * x', mul_mem ?_ hx', by group,
      hψmul (mem_inf.1 hc).1 (mem_inf.1 hc').1⟩
    have := (mem_normalizer_iff.1 (hNC (inv_mem hc')) x).1 hx
    rwa [inv_inv] at this
  have hPconj : ∀ {j g σ}, j ∈ L → j ∈ C ⊓ normalizer (d.Y : Set G) → P g σ →
      P (j * g * j⁻¹) σ := by
    rintro j g σ hjL hj ⟨c, hc, x, hx, rfl, rfl⟩
    refine ⟨j * c * j⁻¹, mul_mem (mul_mem hj hc) (inv_mem hj), j * x * j⁻¹,
      (mem_normalizer_iff.1 (hNC hj) x).1 hx, by group, ?_⟩
    have hjC := (mem_inf.1 hj).1
    have hcC := (mem_inf.1 hc).1
    rw [hψmul (mul_mem hjC hcC) (inv_mem hjC), hψmul hjC hcC, hψinv hjC, hLt hjL,
      one_mul, inv_one, mul_one]
  have hPone : ∀ {g}, g ∈ d.D ⊔ zpowers t → P g 1 := by
    intro g hg
    have hgR := h.tD_le_yamadaR d hg
    have hgC := h.yamadaR_le_centralizer d hgR
    have hgY : g ∈ normalizer (d.Y : Set G) := by
      obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
      rw [h.yamadaR_eq d] at hgR
      refine (sup_le d.S_le_normalizers.2.1 ((zpowers_le).2 ?_)) hgR
      exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hYL hy)))
    refine ⟨g, ⟨hgC, hgY⟩, 1, one_mem _, by rw [mul_one], (hψ1 hgC).2 ?_⟩
    exact sup_le_sup_right (d.image_le _) _ hg
  have hC₁H₂ : yamadaC₁ d t ≤ H₂ := le_sup_left.trans (h.yamadaR₁_le_normalizer_tY d hK)
  have hX2 : IsPGroup 2 (yamadaL₂ d t ⊔ yamadaC₁ d t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) (hC₁H₂.trans (le_normalizer_yamadaL₂ d t))
  have hSX : d.S ≤ yamadaL₂ d t ⊔ yamadaC₁ d t := by
    have hDC : d.D ≤ yamadaC₁ d t := by
      have h1 : d.D ⊔ zpowers t ≤ yamadaC₁ d t := by
        rw [← hC₁t]
        exact inf_le_left
      exact le_sup_left.trans h1
    have hML : d.M ≤ yamadaL₂ d t := by
      have h1 : d.M ⊔ zpowers t ≤ yamadaL₂ d t := by
        rw [← hL₂t]
        exact inf_le_left
      exact le_sup_left.trans h1
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.2]
    exact sup_le (hDC.trans le_sup_right) (hML.trans le_sup_left)
  have hLX : L ⊓ (yamadaL₂ d t ⊔ yamadaC₁ d t) = d.S :=
    d.isSylowOf_S.eq_of_le (le_inf (d.image_le _) hSX) inf_le_left (hX2.to_le inf_le_right)
  have htL₂ : t ∈ yamadaL₂ d t := by
    have : t ∈ d.M ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rw [← hL₂t] at this
    exact this.1
  have hPker : ∀ {g}, g ∈ yamadaC₁ d t → P g 1 → g ∈ yamadaR₂ d t := by
    rintro g hg ⟨c, hc, x, hx, rfl, hc1⟩
    have hcL := (hψ1 (mem_inf.1 hc).1).1 hc1
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L (zpowers t)
      fun l hl y hy => (commute_of_mem_zpowers hy (h.L_le_centralizer hl))).2
    have hcL' : c ∈ ((L ⊔ zpowers t : Subgroup G) : Set G) := hcL
    rw [hset] at hcL'
    obtain ⟨l, hl, τ, hτ, rfl⟩ := hcL'
    have hτL₂ : τ ∈ yamadaL₂ d t := (zpowers_le).2 htL₂ hτ
    have hlX : l ∈ yamadaL₂ d t ⊔ yamadaC₁ d t := by
      rw [show l = l * τ * x * (x⁻¹ * τ⁻¹) by group]
      exact mul_mem (mem_sup_right hg) (mem_sup_left (mul_mem (inv_mem hx) (inv_mem hτL₂)))
    have hlS : l ∈ d.S := by
      rw [← hLX]
      exact ⟨hl, hlX⟩
    rw [mul_assoc]
    exact mul_mem (mem_sup_right hlS) (mem_sup_left (mul_mem hτL₂ hx))
  have hJY : d.J₃ ≤ normalizer (d.Y : Set G) := (d.image_mono inf_le_left).trans
    (d.image_le_normalizer (Model.J_le_adjointGroup K) Model.Y_le_adjointGroup fun j hj =>
      CFSG.ComponentClassification.AS81.G2.borelGroup_le_normalizer_g2BCGroup (mem_sup_left hj))
  have hJU : d.J₃ ≤ normalizer (d.U : Set G) := (d.image_mono inf_le_left).trans
    (d.image_le_normalizer (Model.J_le_adjointGroup K) (Model.U_le_adjointGroup K) fun j hj =>
      Model.borelGroup_le_normalizer_U (mem_sup_left hj))
  have hJ : ∀ {e : G}, e ∈ d.J₃ → e ∈ L ∧ e ∈ C ⊓ normalizer (d.Y : Set G) ∧
      e ∈ C ⊓ normalizer (d.U : Set G) := fun he =>
    ⟨d.image_le _ he, ⟨h.L_le_centralizer (d.image_le _ he), hJY he⟩,
      ⟨h.L_le_centralizer (d.image_le _ he), hJU he⟩⟩
  intro c hc
  have hcu : c⁻¹ * t * c = t * (c⁻¹ * t * c * t) :=
    (hc₁.crossed_eq_iff (hc₁.crossed_mem c (yamadaC₁_le d t hc))).1 rfl
  have hu := hc₁.crossed_mem c (yamadaC₁_le d t hc)
  set u := c⁻¹ * t * c * t with hudef
  by_cases hu1 : u = 1
  · have hcC : c ∈ C := by
      rw [hu1, mul_one] at hcu
      rw [hCdef, mem_centralizer_singleton_iff]
      calc c * t = c * (c⁻¹ * t * c) := by rw [hcu]
        _ = t * c := by group
    have hcB : c ∈ d.D ⊔ zpowers t := by
      rw [← hC₁t]
      exact ⟨hc, hcC⟩
    exact hRR₂ (h.tD_le_yamadaR d hcB)
  obtain ⟨y, hy⟩ := ι.surjective ⟨u, hu⟩
  have hux : u = ι (Multiplicative.ofAdd (Multiplicative.toAdd y)) :=
    (congrArg Subtype.val hy).symm
  set x := Multiplicative.toAdd y with hx
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one (hK ▸ h.four_le : 4 ≤ Nat.card K)
  have ha1' : 1 + a ≠ 0 := fun h0 => ha1 ((CharTwo.add_eq_zero.1 h0).symm)
  obtain ⟨e₁, he₁, he₁x⟩ := d.exists_mem_J₃_scalar ι hι ha0
  obtain ⟨e₂, he₂, he₂x⟩ := d.exists_mem_J₃_scalar ι hι ha1'
  have hmemC₁ : ∀ {e : G}, e ∈ d.J₃ → e * c * e⁻¹ ∈ yamadaC₁ d t := fun he =>
    (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t
      (h.centralizer_inf_normalizer_U_le d (hJ he).2.2)) c).1 hc
  have hconj : ∀ {e : G} {b : K}, e ∈ C → (∀ x' : K, e * (ι (Multiplicative.ofAdd x') : G) * e⁻¹ =
      ι (Multiplicative.ofAdd (b * x'))) →
        (e * c * e⁻¹)⁻¹ * t * (e * c * e⁻¹) = t * ι (Multiplicative.ofAdd (b * x)) := by
    intro e b heC heb
    have het : e * t = t * e := mem_centralizer_singleton_iff.1 heC
    calc (e * c * e⁻¹)⁻¹ * t * (e * c * e⁻¹) = e * (c⁻¹ * (e⁻¹ * t * e) * c) * e⁻¹ := by group
      _ = e * (c⁻¹ * t * c) * e⁻¹ := by
          rw [show e⁻¹ * t * e = t by rw [mul_assoc, ← het, inv_mul_cancel_left]]
      _ = e * (t * u) * e⁻¹ := by rw [hcu]
      _ = (e * t) * u * e⁻¹ := by group
      _ = t * (e * u * e⁻¹) := by rw [het]; group
      _ = t * ι (Multiplicative.ofAdd (b * x)) := by rw [hux, heb]
  have h1 := hconj (hJ he₁).2.1.1 he₁x
  have h2 := hconj (hJ he₂).2.1.1 he₂x
  have huc : (e₁ * c * e₁⁻¹)⁻¹ * u * (e₁ * c * e₁⁻¹) = u := by
    rw [mul_assoc, mem_centralizer_iff.1 (hC₁U (hmemC₁ he₁)) u hu, inv_mul_cancel_left]
  have h12 : (c * (e₁ * c * e₁⁻¹))⁻¹ * t * (c * (e₁ * c * e₁⁻¹)) =
      (e₂ * c * e₂⁻¹)⁻¹ * t * (e₂ * c * e₂⁻¹) := by
    rw [h2]
    calc (c * (e₁ * c * e₁⁻¹))⁻¹ * t * (c * (e₁ * c * e₁⁻¹)) =
        (e₁ * c * e₁⁻¹)⁻¹ * (c⁻¹ * t * c) * (e₁ * c * e₁⁻¹) := by group
      _ = ((e₁ * c * e₁⁻¹)⁻¹ * t * (e₁ * c * e₁⁻¹)) *
          ((e₁ * c * e₁⁻¹)⁻¹ * u * (e₁ * c * e₁⁻¹)) := by rw [hcu]; group
      _ = t * ι (Multiplicative.ofAdd ((1 + a) * x)) := by
          rw [h1, huc, hux, mul_assoc, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add]
          congr 4
          ring
  have hw := Common.mul_inv_mem_centralizer_of_conj_eq h12
  have hwB : (e₂ * c * e₂⁻¹) * (c * (e₁ * c * e₁⁻¹))⁻¹ ∈ d.D ⊔ zpowers t := by
    rw [← hC₁t]
    exact Subgroup.mem_inf.2 ⟨mul_mem (hmemC₁ he₂) (inv_mem (mul_mem hc (hmemC₁ he₁))), hw⟩
  obtain ⟨σ, hσ⟩ := hPex c (hC₁H₂ hc)
  have hP1 := hPconj (hJ he₁).1 (hJ he₁).2.1 hσ
  have hP2 := hPconj (hJ he₂).1 (hJ he₂).2.1 hσ
  have hP12 := hPmul (hPone hwB) (hPmul hσ hP1)
  rw [show (e₂ * c * e₂⁻¹) * (c * (e₁ * c * e₁⁻¹))⁻¹ * (c * (e₁ * c * e₁⁻¹)) =
    e₂ * c * e₂⁻¹ by group] at hP12
  have hσσ := hPuniq hP2 hP12
  rw [one_mul, left_eq_mul] at hσσ
  exact hPker hc (hσσ ▸ hσ)

theorem mem_yamadaR₁_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {z : G} (hz : z ∈ yamadaR₂ d t) : z ∈ yamadaR₁ d t ↔ z⁻¹ * t * z * t ∈ d.U := by
  refine ⟨fun hz₁ => (h.cosetData_tU d hK).crossed_mem z (h.yamadaR₁_le_normalizer_tU d hz₁),
    fun hzU => ?_⟩
  have hzc : z ∈ centralizer (d.U : Set G) := h.yamadaR₂_le_centralizer_U d hK hz
  have hUL : d.U ≤ L := d.image_le _
  set u := z⁻¹ * t * z * t with hudef
  have hut : u * t = t * u := mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hUL hzU))
  have hzt : z⁻¹ * t * z = t * u := by
    calc z⁻¹ * t * z = u * t := by rw [hudef, mul_assoc _ t t, h.t_mul_t, mul_one]
      _ = t * u := hut
  have hzi : z⁻¹ ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [inv_inv]
    rcases (h.mem_sup_zpowers_iff hUL).1 hw with hwU | hwU
    · rw [show z⁻¹ * w * z = w by rw [mul_assoc, mem_centralizer_iff.1 hzc w hwU,
        inv_mul_cancel_left]]
      exact hw
    · have e : z⁻¹ * w * z = (z⁻¹ * t * z) * (z⁻¹ * (t * w) * z) := by
        calc z⁻¹ * w * z = z⁻¹ * (t * (t * w)) * z := by
              rw [← mul_assoc t t w, h.t_mul_t, one_mul]
          _ = (z⁻¹ * t * z) * (z⁻¹ * (t * w) * z) := by group
      rw [e, hzt, show z⁻¹ * (t * w) * z = t * w by rw [mul_assoc,
        mem_centralizer_iff.1 hzc _ hwU, inv_mul_cancel_left]]
      exact mul_mem (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hzU)) (mem_sup_left hwU)
  have hzN : z ∈ ((normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
      Set G) := by
    have := inv_mem hzi
    rwa [inv_inv] at this
  rw [(h.yamada_5_3_1 d hK).2.2.1] at hzN
  obtain ⟨c, hc, n, hn, rfl⟩ := hzN
  have hnR₂ : n ∈ yamadaR₂ d t := by
    have := mul_mem (inv_mem (h.yamadaC₁_le_yamadaR₂ d hK hc)) hz
    rwa [inv_mul_cancel_left] at this
  have hnR : n ∈ yamadaR d t := by
    rw [← (h.yamadaR₂_inf_centralizer d hK).2]
    exact Subgroup.mem_inf.2 ⟨hnR₂, (Subgroup.mem_inf.1 hn).1⟩
  exact mul_mem (mem_sup_left hc) (h.yamadaR_le_yamadaR₁ d hK hnR)

theorem conj_mul_inv_mem_U (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {r w : G} (hr : r ∈ yamadaR₂ d t) (hw : w ∈ d.Y) : r * w * r⁻¹ * w⁻¹ ∈ d.U := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₂ d) r hr
  have hsw : s * w * s⁻¹ ∈ d.Y := (mem_normalizer_iff.1 (d.S_le_normalizers.2.1 hs) w).1 hw
  have hl' : l * (s * w * s⁻¹) * l⁻¹ = s * w * s⁻¹ := by
    rw [← mem_centralizer_iff.1 (hL₂Y hl) _ hsw, mul_inv_cancel_right]
  have hc : ⁅w, s⁆ ∈ d.U := (d.mem_Y_iff_commutator hK4 (hYS hw)).1 hw s hs
  have e : l * s * w * (l * s)⁻¹ * w⁻¹ = ⁅w, s⁆⁻¹ := by
    rw [commutatorElement_inv, commutatorElement_def,
      show l * s * w * (l * s)⁻¹ = l * (s * w * s⁻¹) * l⁻¹ by group, hl']
  rw [e]
  exact inv_mem hc

theorem exists_hom_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ∃ _ : (d.U.subgroupOf d.Y).Normal, ∃ Ψ : yamadaR₂ d t →* d.Y ⧸ d.U.subgroupOf d.Y,
      (∀ x : yamadaR₂ d t, ∃ hy : t * (x : G)⁻¹ * t * x ∈ d.Y,
        Ψ x = QuotientGroup.mk (⟨t * (x : G)⁻¹ * t * x, hy⟩ : d.Y)) ∧
      Function.Surjective Ψ ∧ Ψ.ker = (yamadaR₁ d t).subgroupOf (yamadaR₂ d t) := by
  obtain ⟨-, -, hL₂tr, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
  have hc₂ := h.cosetData_tY d hK
  have hN₂ : (d.U.subgroupOf d.Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUY).2 fun y hy => d.S_le_normalizers.1 (hYS hy)
  have hκe : ∀ x ∈ yamadaR₂ d t, t * x⁻¹ * t * x = x⁻¹ * t * x * t := fun x hx => by
    have hyt := hc₂.comm_of_mem (hc₂.crossed_mem x (h.yamadaR₂_le_normalizer_tY d hx))
    calc t * x⁻¹ * t * x = t * (x⁻¹ * t * x * t) * t⁻¹ := by group
      _ = x⁻¹ * t * x * t := by rw [hyt, mul_inv_cancel_right]
  have hκ : ∀ x : yamadaR₂ d t, t * (x : G)⁻¹ * t * x ∈ d.Y := fun x => by
    rw [hκe x x.2]
    exact hc₂.crossed_mem x (h.yamadaR₂_le_normalizer_tY d x.2)
  have hmul : ∀ x ∈ yamadaR₂ d t, ∀ y ∈ yamadaR₂ d t,
      (t * (x * y)⁻¹ * t * (x * y))⁻¹ * ((t * x⁻¹ * t * x) * (t * y⁻¹ * t * y)) ∈ d.U := by
    intro x hx y hy
    rw [hκe x hx, hκe y hy, hκe (x * y) (mul_mem hx hy)]
    have hp := hc₂.crossed_mem x (h.yamadaR₂_le_normalizer_tY d hx)
    have hq := hc₂.crossed_mem y (h.yamadaR₂_le_normalizer_tY d hy)
    set p := x⁻¹ * t * x * t with hpdef
    set q := y⁻¹ * t * y * t with hqdef
    have e1 : (x * y)⁻¹ * t * (x * y) * t = y⁻¹ * p * y * q := by
      calc (x * y)⁻¹ * t * (x * y) * t = y⁻¹ * x⁻¹ * t * x * (t * t) * y * t := by
            rw [h.t_mul_t, mul_one]
            group
        _ = y⁻¹ * p * y * q := by rw [hpdef, hqdef]; group
    have hyp : y⁻¹ * p * y ∈ d.Y := by
      have := (mem_normalizer_iff.1 (hc₂.le_normalizer (h.yamadaR₂_le_normalizer_tY d
        (inv_mem hy))) p).1 hp
      rwa [inv_inv] at this
    have hz : y⁻¹ * p⁻¹ * y⁻¹⁻¹ * p⁻¹⁻¹ ∈ d.U := h.conj_mul_inv_mem_U d hK (inv_mem hy) (inv_mem hp)
    have hzY : (y⁻¹ * p * y)⁻¹ * p ∈ d.Y := mul_mem (inv_mem hyp) hp
    rw [e1, show (y⁻¹ * p * y * q)⁻¹ * (p * q) = q⁻¹ * (((y⁻¹ * p * y)⁻¹ * p) * q) by group,
      hc₂.mul_comm_of_mem hzY hq, inv_mul_cancel_left,
      show (y⁻¹ * p * y)⁻¹ * p = y⁻¹ * p⁻¹ * y⁻¹⁻¹ * p⁻¹⁻¹ by group]
    exact hz
  let Ψ : yamadaR₂ d t →* d.Y ⧸ d.U.subgroupOf d.Y :=
    { toFun := fun x => QuotientGroup.mk (⟨t * (x : G)⁻¹ * t * x, hκ x⟩ : d.Y)
      map_one' := by
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
        simp [h.t_mul_t]
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        exact hmul x x.2 y y.2 }
  have hΨ : ∀ x : yamadaR₂ d t,
      Ψ x = QuotientGroup.mk (⟨t * (x : G)⁻¹ * t * x, hκ x⟩ : d.Y) := fun _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro w
    induction w using QuotientGroup.induction_on with | H y => ?_
    obtain ⟨x, hx, hxt⟩ := hL₂tr y y.2
    refine ⟨⟨x, mem_sup_left hx⟩, ?_⟩
    rw [hΨ]
    congr 1
    apply Subtype.ext
    change t * x⁻¹ * t * x = y
    rw [hκe x (mem_sup_left hx), hxt, mul_assoc, ← hc₂.comm_of_mem y.2, ← mul_assoc, h.t_mul_t,
      one_mul]
  have hker : Ψ.ker = (yamadaR₁ d t).subgroupOf (yamadaR₂ d t) := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker, hΨ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    change t * (x : G)⁻¹ * t * x ∈ d.U ↔ (x : G) ∈ yamadaR₁ d t
    rw [hκe x x.2]
    exact (h.mem_yamadaR₁_iff d hK x.2).symm
  exact ⟨hN₂, Ψ, fun x => ⟨hκ x, rfl⟩, hsurj, hker⟩

theorem yamada_5_6_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₁ d t = yamadaR₂ d t ⊓ normalizer (yamadaR d t : Set G) ∧
      yamadaR₁ d t ≤ yamadaR₂ d t ∧ yamadaR₂ d t ≤ normalizer (yamadaR₁ d t : Set G) ∧
      yamadaR₂ d t = yamadaL₂ d t ⊔ yamadaC₁ d t ∧
      (yamadaR₂ d t : Set G) = (yamadaL₂ d t : Set G) * (yamadaC₁ d t : Set G) := by
  have hC₁R₂ := h.yamadaC₁_le_yamadaR₂ d hK
  obtain ⟨-, hR₂t⟩ := h.yamadaR₂_inf_centralizer d hK
  have hR₁R₂ : yamadaR₁ d t ≤ yamadaR₂ d t := sup_le hC₁R₂ le_sup_right
  have hSX : d.S ≤ yamadaL₂ d t ⊔ yamadaC₁ d t := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.2]
    exact sup_le ((le_sup_left.trans (h.tD_le_yamadaC₁ d hK)).trans le_sup_right)
      ((le_sup_left.trans (h.tM_le_yamadaL₂ d hK)).trans le_sup_left)
  have hR₂ : yamadaR₂ d t = yamadaL₂ d t ⊔ yamadaC₁ d t :=
    le_antisymm (sup_le le_sup_left hSX) (sup_le le_sup_left hC₁R₂)
  have hC₁L₂ : yamadaC₁ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    (le_sup_left.trans (h.yamadaR₁_le_normalizer_tY d hK)).trans (le_normalizer_yamadaL₂ d t)
  obtain ⟨_, Ψ, -, -, hker⟩ := h.exists_hom_yamadaR₂ d hK
  have hN : ((yamadaR₁ d t).subgroupOf (yamadaR₂ d t)).Normal := hker ▸ Ψ.normal_ker
  refine ⟨le_antisymm (le_inf hR₁R₂ (h.yamada_5_3_3 d hK).2.2.le) fun x hx => ?_, hR₁R₂,
    (normal_subgroupOf_iff_le_normalizer hR₁R₂).1 hN, hR₂, by
      rw [hR₂, coe_mul_of_right_le_normalizer_left _ _ hC₁L₂]⟩
  obtain ⟨hxR₂, hxN⟩ := Subgroup.mem_inf.1 hx
  have hxs : x ∈ ((normalizer (yamadaR d t : Set G) : Subgroup G) : Set G) := hxN
  rw [(h.yamada_5_3_3 d hK).2.1] at hxs
  obtain ⟨c, hc, n, hn, rfl⟩ := hxs
  have hnR₂ : n ∈ yamadaR₂ d t := by
    have := mul_mem (inv_mem (hC₁R₂ hc)) hxR₂
    rwa [inv_mul_cancel_left] at this
  have hnR : n ∈ yamadaR d t := by
    rw [← hR₂t]
    exact Subgroup.mem_inf.2 ⟨hnR₂, (Subgroup.mem_inf.1 hn).1⟩
  exact mul_mem (mem_sup_left hc) (h.yamadaR_le_yamadaR₁ d hK hnR)

theorem mul_self_mem_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {x : G} (hx : x ∈ yamadaR₂ d t) : x * x ∈ yamadaL₂ d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, -, -, -, -, -, hFM, -, -, -⟩ := d.inclusions
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₂ d) x hx
  have hs2 : s * s ∈ yamadaL₂ d t := by
    have h1 : s ^ 2 ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, rfl⟩
    rw [(d.yamada_3_12_mho hK4).2.2, sq] at h1
    exact h.tM_le_yamadaL₂ d hK (mem_sup_left (hFM h1))
  have hsl : s * l * s⁻¹ ∈ yamadaL₂ d t :=
    (mem_normalizer_iff.1 (h.S_le_normalizer_yamadaL₂ d hs) l).1 hl
  rw [show l * s * (l * s) = l * (s * l * s⁻¹) * (s * s) by group]
  exact mul_mem (mul_mem hl hsl) hs2

theorem mul_self_mem_tM_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {x : G} (hx : x ∈ yamadaR₂ d t) :
    x * x ∈ d.M ⊔ zpowers t ↔ x ∈ yamadaL₂ d t ∨ x ∈ yamadaR₁ d t := by
  have hc₂ := h.cosetData_tY d hK
  obtain ⟨hL₂Y, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  have hxN := h.yamadaR₂_le_normalizer_tY d hx
  have hy := hc₂.crossed_mem x hxN
  set y := x⁻¹ * t * x * t with hydef
  have hsq : (x * x)⁻¹ * t * (x * x) * t = x⁻¹ * y * x * y := by
    calc (x * x)⁻¹ * t * (x * x) * t = x⁻¹ * x⁻¹ * t * x * (t * t) * x * t := by
          rw [h.t_mul_t, mul_one]
          group
      _ = x⁻¹ * y * x * y := by rw [hydef]; group
  have hxx := h.mul_self_mem_yamadaL₂ d hK hx
  have hiff : x * x ∈ d.M ⊔ zpowers t ↔ x⁻¹ * y * x * y = 1 := by
    rw [← hsq, ← hL₂t]
    constructor
    · rintro ⟨-, hC⟩
      rw [mul_assoc (x * x)⁻¹ t (x * x), ← mem_centralizer_singleton_iff.1 hC,
        inv_mul_cancel_left, h.t_mul_t]
    · intro e
      refine ⟨hxx, mem_centralizer_singleton_iff.2 ?_⟩
      have e' := (hc₂.crossed_eq_iff (one_mem _)).1 e
      rw [mul_one] at e'
      calc x * x * t = x * x * ((x * x)⁻¹ * t * (x * x)) := by rw [e']
        _ = t * (x * x) := by group
  rw [hiff]
  constructor
  · intro e
    obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.S_le_normalizer_yamadaL₂ d) x hx
    have hly : l⁻¹ * y * l = y := by
      rw [mul_assoc, mem_centralizer_iff.1 (hL₂Y hl) y hy, inv_mul_cancel_left]
    have hsy : s⁻¹ * y * s = y := by
      have e1 : (l * s)⁻¹ * y * (l * s) = s⁻¹ * (l⁻¹ * y * l) * s := by group
      rw [e1, hly] at e
      calc s⁻¹ * y * s = s⁻¹ * y * s * y * y := by
            rw [mul_assoc _ y y, hc₂.mul_self_of_mem hy, mul_one]
        _ = y := by rw [e, one_mul]
    have hcomm : s * y = y * s := by
      calc s * y = s * (s⁻¹ * y * s) := by rw [hsy]
        _ = y * s := by group
    rcases d.mem_M_or_mem_U_of_commute hs hy hcomm with hsM | hyU
    · exact Or.inl (mul_mem hl (h.tM_le_yamadaL₂ d hK (mem_sup_left hsM)))
    · exact Or.inr ((h.mem_yamadaR₁_iff d hK hx).2 hyU)
  · rintro (hxL | hxR)
    · have e : x⁻¹ * y * x = y := by
        rw [mul_assoc, mem_centralizer_iff.1 (hL₂Y hxL) y hy, inv_mul_cancel_left]
      rw [e, hc₂.mul_self_of_mem hy]
    · have hyU := (h.mem_yamadaR₁_iff d hK hx).1 hxR
      have e : x⁻¹ * y * x = y := by
        rw [mul_assoc, mem_centralizer_iff.1 (h.yamadaR₂_le_centralizer_U d hK hx) y hyU,
          inv_mul_cancel_left]
      rw [e, hc₂.mul_self_of_mem hy]

theorem yamada_5_6_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} = d.U := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, hC₁t, hC₁tr, -⟩ := h.two_core_C₁ d hK
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, -, -, -⟩ := d.inclusions
  have hc₁ := h.cosetData_tU d hK
  have hUF : d.U ≤ d.F := hUY.trans (hYX.trans hXF)
  have hFL : d.F ≤ L := d.image_le _
  have hnt : ∀ {a : G}, a ∈ L → t * a ∈ L → False := fun ha hta => h.t_not_mem_L (by
    have := mul_mem hta (inv_mem ha)
    rwa [mul_inv_cancel_right] at this)
  have hDM : ∀ {x : G}, x ∈ d.D → x ∈ d.M → x ∈ d.F := fun h1 h2 => by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact ⟨h1, h2⟩
  set Q := closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} with hQ
  have hsqF : ∀ g ∈ yamadaC₁ d t, g ^ 2 ∈ d.F ⊔ zpowers t := by
    intro g hg
    have hgV : g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hg, hC₁U hg⟩
    have h1 : (g * g)⁻¹ * t * (g * g) * t = 1 := by
      rw [hc₁.crossed_mul_of_mem hgV hgV, hc₁.mul_self_of_mem (hc₁.crossed_mem_of_mem hgV)]
    have hgC : g * g ∈ centralizer ({t} : Set G) := by
      have e' := (hc₁.crossed_eq_iff (one_mem _)).1 h1
      rw [mul_one] at e'
      rw [mem_centralizer_singleton_iff]
      calc g * g * t = g * g * ((g * g)⁻¹ * t * (g * g)) := by rw [e']
        _ = t * (g * g) := by group
    have hgD : g * g ∈ d.D ⊔ zpowers t := by
      rw [← hC₁t]
      exact ⟨mul_mem hg hg, hgC⟩
    have hgM : g * g ∈ d.M ⊔ zpowers t := by
      rw [← hL₂t]
      exact ⟨h.mul_self_mem_yamadaL₂ d hK (h.yamadaC₁_le_yamadaR₂ d hK hg), hgC⟩
    rw [sq]
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgD with h2 | h2 <;>
      rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgM with h3 | h3
    · exact mem_sup_left (hDM h2 h3)
    · exact (hnt (d.image_le _ h2) (d.image_le _ h3)).elim
    · exact (hnt (d.image_le _ h3) (d.image_le _ h2)).elim
    · rw [show g * g = t * (t * (g * g)) by rw [← mul_assoc, h.t_mul_t, one_mul]]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hDM h2 h3))
  have hQF : Q ≤ d.F ⊔ zpowers t := (closure_le _).2 fun z ⟨g, hg, e⟩ => e ▸ hsqF g hg
  have hNQ : L ⊓ normalizer (d.U : Set G) ≤ normalizer (Q : Set G) := fun n hn =>
    normalizer_le_normalizer_closure_sq _ (le_normalizer_yamadaC₁ d t
      (h.centralizer_inf_normalizer_U_le d ⟨h.L_le_centralizer hn.1, hn.2⟩))
  set E := (Q ⊔ d.U ⊔ zpowers t) ⊓ L with hE
  have hEF : E ≤ d.F := by
    rintro x ⟨hx, hxL⟩
    have hx' : x ∈ d.F ⊔ zpowers t :=
      (sup_le (sup_le hQF (hUF.trans le_sup_left)) le_sup_right) hx
    rcases (h.mem_sup_zpowers_iff hFL).1 hx' with h1 | h1
    · exact h1
    · exact (hnt hxL (hFL h1)).elim
  have hEU : E = d.U := by
    have hUE : d.U ≤ E := le_inf (le_sup_right.trans le_sup_left) (d.image_le _)
    have hN : L ⊓ normalizer (d.U : Set G) ≤ normalizer (E : Set G) := fun n hn =>
      Common.mem_normalizer_inf (Common.mem_normalizer_sup (Common.mem_normalizer_sup (hNQ hn)
        hn.2) (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1
          (h.L_le_centralizer hn.1)))) (le_normalizer hn.1)
    rcases ((d.yamada_3_16_1_G hK4 hUE (hEF.trans hFD)).1 hN) with h1 | h1
    · exact h1
    · exact absurd ((h1.symm.le.trans hEF).trans hFM) d.not_D_le_M
  have hQtU : Q ≤ d.U ⊔ zpowers t := by
    intro x hx
    have hx3 : x ∈ Q ⊔ d.U ⊔ zpowers t := mem_sup_left (mem_sup_left hx)
    rcases (h.mem_sup_zpowers_iff hFL).1 (hQF hx) with h1 | h1
    · have : x ∈ E := ⟨hx3, hFL h1⟩
      rw [hEU] at this
      exact mem_sup_left this
    · have : t * x ∈ E := ⟨mul_mem (mem_sup_right (mem_zpowers t)) hx3, hFL h1⟩
      rw [hEU] at this
      rw [show x = t * (t * x) by rw [← mul_assoc, h.t_mul_t, one_mul]]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left this)
  have hUQ : d.U ≤ Q := by
    rw [← (d.yamada_3_12_mho hK4).1]
    exact closure_mono fun z ⟨g, hg, e⟩ =>
      ⟨g, h.tD_le_yamadaC₁ d hK (mem_sup_left hg), e⟩
  refine le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => ?_) hUQ
  rw [e]
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1
      (hQtU (subset_closure ⟨g, hg, rfl⟩)) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨c, hc, hct⟩ := hC₁tr _ h1
    have hg2 : g ^ 2 = c⁻¹ * t * c := by rw [hct, ← mul_assoc, h.t_mul_t, one_mul]
    obtain ⟨y, hydef⟩ : ∃ y, y = c * g * c⁻¹ := ⟨_, rfl⟩
    have hy2 : y * y = t := by
      calc y * y = c * g ^ 2 * c⁻¹ := by rw [hydef, sq]; group
        _ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [hg2]
        _ = t := by group
    have hyC₁ : y ∈ yamadaC₁ d t := hydef ▸ mul_mem (mul_mem hc hg) (inv_mem hc)
    have hyt : y ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff, ← hy2]
      group
    have hyB : y ∈ d.D ⊔ zpowers t := by
      rw [← hC₁t]
      exact ⟨hyC₁, hyt⟩
    have hyt' : y * t = t * y := mem_centralizer_singleton_iff.1 hyt
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hyB with h2 | h2
    · exact h.t_not_mem_L (hy2 ▸ mul_mem (d.image_le _ h2) (d.image_le _ h2))
    · refine h.t_not_mem_L ?_
      have e2 : t * y * (t * y) = t := by
        calc t * y * (t * y) = t * (y * t) * y := by group
          _ = t * (t * y) * y := by rw [hyt']
          _ = t * t * (y * y) := by group
          _ = t := by rw [h.t_mul_t, one_mul, hy2]
      exact e2 ▸ mul_mem (d.image_le _ h2) (d.image_le _ h2)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
