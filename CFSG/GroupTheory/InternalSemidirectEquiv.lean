module

public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G G' : Type*} [Group G] [Group G']

abbrev conjHom (Q K : Subgroup G) (hK : K ≤ Subgroup.normalizer (Q : Set G)) : ↥K →* MulAut ↥Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hK)

theorem conjHom_apply {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G)) (k : ↥K)
    (q : ↥Q) : ((conjHom Q K hK k q : ↥Q) : G) = (k : G) * (q : G) * (k : G)⁻¹ := rfl

theorem conjHom_val {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G)) (k : ↥K)
    (q : ↥Q) :
    conjHom Q K hK k q = ⟨(k : G) * (q : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hK k.2) (q : G)).mp q.2⟩ :=
  Subtype.ext rfl

theorem monoidHomSubgroup_injective {Q K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) (hd : Disjoint Q K) :
    Function.Injective (SemidirectProduct.monoidHomSubgroup hK) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [SemidirectProduct.monoidHomSubgroup_apply] at hp
  have h1 : (p.left : G) = ((p.right : G))⁻¹ := eq_inv_of_mul_eq_one_left hp
  have hl : (p.left : G) ∈ Q ⊓ K := ⟨p.left.2, by rw [h1]; exact K.inv_mem p.right.2⟩
  rw [disjoint_iff.mp hd] at hl
  have hl1 : p.left = 1 := Subtype.ext (by simpa using hl)
  have hr1 : p.right = 1 := by
    apply Subtype.ext
    have : (p.right : G) = 1 := by
      rw [hl1] at hp
      simpa using hp
    simpa using this
  refine SemidirectProduct.ext ?_ ?_
  · simpa using hl1
  · simpa using hr1

theorem monoidHomSubgroup_range {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G)) :
    (SemidirectProduct.monoidHomSubgroup hK).range = Q ⊔ K := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [SemidirectProduct.monoidHomSubgroup_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.left.2) (Subgroup.mem_sup_right p.right.2)
  · intro x hx
    have := Subgroup.coe_mul_of_right_le_normalizer_left Q K hK
    rw [← SetLike.mem_coe, this] at hx
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨⟨⟨n, hn⟩, ⟨k, hk⟩⟩, rfl⟩

noncomputable def semiEquivSup {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (hd : Disjoint Q K) : (↥Q ⋊[conjHom Q K hK] ↥K) ≃* ↥(Q ⊔ K) :=
  (MonoidHom.ofInjective (monoidHomSubgroup_injective hK hd)).trans
    (MulEquiv.subgroupCongr (monoidHomSubgroup_range hK))

theorem semiEquivSup_inl {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (hd : Disjoint Q K) (q : ↥Q) :
    semiEquivSup hK hd (SemidirectProduct.inl q) = ⟨q, Subgroup.mem_sup_left q.2⟩ := by
  apply Subtype.ext
  change ((SemidirectProduct.monoidHomSubgroup hK (SemidirectProduct.inl q) : G)) = (q : G)
  rw [SemidirectProduct.monoidHomSubgroup_apply]
  simp

theorem semiEquivSup_inr {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (hd : Disjoint Q K) (k : ↥K) :
    semiEquivSup hK hd (SemidirectProduct.inr k) = ⟨k, Subgroup.mem_sup_right k.2⟩ := by
  apply Subtype.ext
  change ((SemidirectProduct.monoidHomSubgroup hK (SemidirectProduct.inr k) : G)) = (k : G)
  rw [SemidirectProduct.monoidHomSubgroup_apply]
  simp

theorem semidirectProduct_congr_inl {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂]
    [Group G₂] {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂} (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
    (h : ∀ g : G₁, MulEquiv.trans (φ₁ g) fn = fn.trans (φ₂ (fg g))) (n : N₁) :
    SemidirectProduct.congr fn fg h (SemidirectProduct.inl n) =
      SemidirectProduct.inl (fn n) := by
  apply SemidirectProduct.ext <;> simp

theorem semidirectProduct_congr_inr {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂]
    [Group G₂] {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂} (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
    (h : ∀ g : G₁, MulEquiv.trans (φ₁ g) fn = fn.trans (φ₂ (fg g))) (g : G₁) :
    SemidirectProduct.congr fn fg h (SemidirectProduct.inr g) =
      SemidirectProduct.inr (fg g) := by
  apply SemidirectProduct.ext <;> simp

theorem exists_mulEquiv_sup_extend {Q K : Subgroup G} {Q' K' : Subgroup G'}
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) (hd : Disjoint Q K)
    (hK' : K' ≤ Subgroup.normalizer (Q' : Set G')) (hd' : Disjoint Q' K')
    (Θ : ↥Q ≃* ↥Q') (Λ : ↥K ≃* ↥K')
    (h : ∀ (k : ↥K) (q : ↥Q) (hq : (k : G) * q * (k : G)⁻¹ ∈ Q),
      ((Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩ : ↥Q') : G') =
        (Λ k : G') * (Θ q : G') * (Λ k : G')⁻¹) :
    ∃ α : ↥(Q ⊔ K) ≃* ↥(Q' ⊔ K'),
      (∀ q : ↥Q, (α ⟨q, Subgroup.mem_sup_left q.2⟩ : G') = Θ q) ∧
      (∀ k : ↥K, (α ⟨k, Subgroup.mem_sup_right k.2⟩ : G') = Λ k) := by
  have hcongr : ∀ k : ↥K, (conjHom Q K hK k).trans Θ =
      Θ.trans (conjHom Q' K' hK' (Λ k)) := by
    intro k
    ext q
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, conjHom_val, h k q, conjHom_apply]
  let α₀ : ↥(Q ⊔ K) ≃* ↥(Q' ⊔ K') :=
    (semiEquivSup hK hd).symm.trans ((SemidirectProduct.congr Θ Λ hcongr).trans
      (semiEquivSup hK' hd'))
  refine ⟨α₀, ?_, ?_⟩
  · intro q
    have h1 : α₀ ⟨q, Subgroup.mem_sup_left q.2⟩ =
        semiEquivSup hK' hd' (SemidirectProduct.inl (Θ q)) := by
      change (semiEquivSup hK' hd') (SemidirectProduct.congr Θ Λ hcongr
        ((semiEquivSup hK hd).symm ⟨q, Subgroup.mem_sup_left q.2⟩)) = _
      rw [← semiEquivSup_inl hK hd q, MulEquiv.symm_apply_apply, semidirectProduct_congr_inl]
    rw [h1, semiEquivSup_inl]
  · intro k
    have h1 : α₀ ⟨k, Subgroup.mem_sup_right k.2⟩ =
        semiEquivSup hK' hd' (SemidirectProduct.inr (Λ k)) := by
      change (semiEquivSup hK' hd') (SemidirectProduct.congr Θ Λ hcongr
        ((semiEquivSup hK hd).symm ⟨k, Subgroup.mem_sup_right k.2⟩)) = _
      rw [← semiEquivSup_inr hK hd k, MulEquiv.symm_apply_apply, semidirectProduct_congr_inr]
    rw [h1, semiEquivSup_inr]

theorem monoidHomSubgroup_mem_ker_iff {Q N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (p : ↥Q ⋊[conjHom Q N hN] ↥N) :
    p ∈ (SemidirectProduct.monoidHomSubgroup hN).ker ↔ (p.left : G) = ((p.right : G))⁻¹ := by
  rw [MonoidHom.mem_ker, SemidirectProduct.monoidHomSubgroup_apply]
  constructor
  · intro hp
    exact eq_inv_of_mul_eq_one_left hp
  · intro hp
    rw [hp, inv_mul_cancel]

theorem semidirectProduct_congr_left {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂]
    [Group G₂] {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂} (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
    (h : ∀ g : G₁, MulEquiv.trans (φ₁ g) fn = fn.trans (φ₂ (fg g))) (p : N₁ ⋊[φ₁] G₁) :
    (SemidirectProduct.congr fn fg h p).left = fn p.left := by
  have hp : p = SemidirectProduct.inl p.left * SemidirectProduct.inr p.right := by
    simpa using (SemidirectProduct.mk_eq_inl_mul_inr p.right p.left)
  conv_lhs => rw [hp]
  rw [map_mul, semidirectProduct_congr_inl, semidirectProduct_congr_inr,
    SemidirectProduct.mul_left]
  simp

theorem semidirectProduct_congr_right {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂]
    [Group G₂] {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂} (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
    (h : ∀ g : G₁, MulEquiv.trans (φ₁ g) fn = fn.trans (φ₂ (fg g))) (p : N₁ ⋊[φ₁] G₁) :
    (SemidirectProduct.congr fn fg h p).right = fg p.right := by
  have hp : p = SemidirectProduct.inl p.left * SemidirectProduct.inr p.right := by
    simpa using (SemidirectProduct.mk_eq_inl_mul_inr p.right p.left)
  conv_lhs => rw [hp]
  rw [map_mul, semidirectProduct_congr_inl, semidirectProduct_congr_inr,
    SemidirectProduct.mul_right]
  simp

theorem semidirectProduct_congr_mem_ker_iff {Q N : Subgroup G} {Q' N' : Subgroup G'}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (hN' : N' ≤ Subgroup.normalizer (Q' : Set G'))
    (θQ : ↥Q ≃* ↥Q') (θN : ↥N ≃* ↥N')
    (hagree : ∀ (x : G) (hxQ : x ∈ Q) (hxN : x ∈ N), (θQ ⟨x, hxQ⟩ : G') = θN ⟨x, hxN⟩)
    (hback : ∀ n : ↥N, (θN n : G') ∈ Q' → (n : G) ∈ Q)
    (h : ∀ (n : ↥N) (q : ↥Q) (hq : (n : G) * q * (n : G)⁻¹ ∈ Q),
      ((θQ ⟨(n : G) * q * (n : G)⁻¹, hq⟩ : ↥Q') : G') =
        (θN n : G') * (θQ q : G') * (θN n : G')⁻¹)
    (hcongr : ∀ n : ↥N, (conjHom Q N hN n).trans θQ =
      θQ.trans (conjHom Q' N' hN' (θN n))) (p : ↥Q ⋊[conjHom Q N hN] ↥N) :
    SemidirectProduct.congr θQ θN hcongr p ∈ (SemidirectProduct.monoidHomSubgroup hN').ker ↔
      p ∈ (SemidirectProduct.monoidHomSubgroup hN).ker := by
  rw [monoidHomSubgroup_mem_ker_iff, monoidHomSubgroup_mem_ker_iff,
    semidirectProduct_congr_left, semidirectProduct_congr_right]
  constructor
  · intro hx
    have h1 : (θN (p.right⁻¹) : G') = (θQ p.left : G') := by
      simpa [map_inv] using hx.symm
    have h2 : (p.right : G)⁻¹ ∈ Q :=
      hback (p.right⁻¹) (by rw [h1]; exact (θQ p.left).2)
    have h5 : θQ p.left = θQ (⟨(p.right : G)⁻¹, h2⟩ : ↥Q) := by
      apply Subtype.ext
      rw [← h1]
      exact (hagree ((p.right : G)⁻¹) h2 (Subgroup.inv_mem N p.right.2)).symm
    have h6 : p.left = (⟨(p.right : G)⁻¹, h2⟩ : ↥Q) := θQ.injective h5
    simpa using congrArg Subtype.val h6
  · intro hp
    have hq : (p.right : G) ∈ Q := by
      have h2 : (p.right : G)⁻¹ ∈ Q := hp ▸ p.left.2
      simpa using Subgroup.inv_mem Q h2
    have h1 : p.left = (⟨(p.right : G), hq⟩ : ↥Q)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inv]
      exact hp
    have h4 : (θQ (⟨(p.right : G), hq⟩ : ↥Q) : G') = (θN p.right : G') :=
      hagree (p.right) hq p.right.2
    rw [h1, map_inv]
    simpa using congrArg Inv.inv h4

theorem map_ker_monoidHomSubgroup_congr {Q N : Subgroup G} {Q' N' : Subgroup G'}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (hN' : N' ≤ Subgroup.normalizer (Q' : Set G'))
    (θQ : ↥Q ≃* ↥Q') (θN : ↥N ≃* ↥N')
    (hagree : ∀ (x : G) (hxQ : x ∈ Q) (hxN : x ∈ N), (θQ ⟨x, hxQ⟩ : G') = θN ⟨x, hxN⟩)
    (hback : ∀ n : ↥N, (θN n : G') ∈ Q' → (n : G) ∈ Q)
    (h : ∀ (n : ↥N) (q : ↥Q) (hq : (n : G) * q * (n : G)⁻¹ ∈ Q),
      ((θQ ⟨(n : G) * q * (n : G)⁻¹, hq⟩ : ↥Q') : G') =
        (θN n : G') * (θQ q : G') * (θN n : G')⁻¹)
    (hcongr : ∀ n : ↥N, (conjHom Q N hN n).trans θQ =
      θQ.trans (conjHom Q' N' hN' (θN n))) :
    Subgroup.map (SemidirectProduct.congr θQ θN hcongr)
        (SemidirectProduct.monoidHomSubgroup hN).ker =
      (SemidirectProduct.monoidHomSubgroup hN').ker := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (semidirectProduct_congr_mem_ker_iff hN hN' θQ θN hagree hback h hcongr y).mpr hy
  · intro hx
    refine ⟨(SemidirectProduct.congr θQ θN hcongr).symm x, ?_, ?_⟩
    · exact (semidirectProduct_congr_mem_ker_iff hN hN' θQ θN hagree hback h hcongr _).mp
        (by simpa using hx)
    · exact MulEquiv.apply_symm_apply _ x

noncomputable def quotientKerSupEquiv {Q N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    (↥Q ⋊[conjHom Q N hN] ↥N) ⧸ (SemidirectProduct.monoidHomSubgroup hN).ker ≃* ↥(Q ⊔ N) :=
  (QuotientGroup.quotientKerEquivRange (SemidirectProduct.monoidHomSubgroup hN)).trans
    (MulEquiv.subgroupCongr (monoidHomSubgroup_range hN))

theorem quotientKerSupEquiv_mk {Q N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (p : ↥Q ⋊[conjHom Q N hN] ↥N) :
    quotientKerSupEquiv hN (QuotientGroup.mk p) =
      ⟨(p.left : G) * (p.right : G),
        Subgroup.mul_mem _ (Subgroup.mem_sup_left p.left.2)
          (Subgroup.mem_sup_right p.right.2)⟩ := by
  apply Subtype.ext
  exact SemidirectProduct.monoidHomSubgroup_apply hN p

theorem exists_mulEquiv_sup_glue {Q N : Subgroup G} {Q' N' : Subgroup G'}
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (hN' : N' ≤ Subgroup.normalizer (Q' : Set G'))
    (θQ : ↥Q ≃* ↥Q') (θN : ↥N ≃* ↥N')
    (hagree : ∀ (x : G) (hxQ : x ∈ Q) (hxN : x ∈ N), (θQ ⟨x, hxQ⟩ : G') = θN ⟨x, hxN⟩)
    (hback : ∀ n : ↥N, (θN n : G') ∈ Q' → (n : G) ∈ Q)
    (h : ∀ (n : ↥N) (q : ↥Q) (hq : (n : G) * q * (n : G)⁻¹ ∈ Q),
      ((θQ ⟨(n : G) * q * (n : G)⁻¹, hq⟩ : ↥Q') : G') =
        (θN n : G') * (θQ q : G') * (θN n : G')⁻¹) :
    ∃ ζ : ↥(Q ⊔ N) ≃* ↥(Q' ⊔ N'),
      (∀ q : ↥Q, (ζ ⟨q, Subgroup.mem_sup_left q.2⟩ : G') = θQ q) ∧
      (∀ n : ↥N, (ζ ⟨n, Subgroup.mem_sup_right n.2⟩ : G') = θN n) := by
  have hcongr : ∀ n : ↥N, (conjHom Q N hN n).trans θQ =
      θQ.trans (conjHom Q' N' hN' (θN n)) := by
    intro n
    ext q
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, conjHom_val, h n q, conjHom_apply]
  let Φ : (↥Q ⋊[conjHom Q N hN] ↥N) ≃* (↥Q' ⋊[conjHom Q' N' hN'] ↥N') :=
    SemidirectProduct.congr θQ θN hcongr
  have hker : Subgroup.map (Φ : (↥Q ⋊[conjHom Q N hN] ↥N) →*
        (↥Q' ⋊[conjHom Q' N' hN'] ↥N'))
      (SemidirectProduct.monoidHomSubgroup hN).ker =
      (SemidirectProduct.monoidHomSubgroup hN').ker :=
    map_ker_monoidHomSubgroup_congr hN hN' θQ θN hagree hback h hcongr
  let ζ : ↥(Q ⊔ N) ≃* ↥(Q' ⊔ N') :=
    (quotientKerSupEquiv hN).symm.trans
      ((QuotientGroup.congr _ _ Φ hker).trans (quotientKerSupEquiv hN'))
  refine ⟨ζ, ?_, ?_⟩
  · intro q
    have h1 : quotientKerSupEquiv hN (QuotientGroup.mk (SemidirectProduct.inl q)) =
        ⟨q, Subgroup.mem_sup_left q.2⟩ := by
      rw [quotientKerSupEquiv_mk]
      apply Subtype.ext
      simp
    have h2 : ζ ⟨q, Subgroup.mem_sup_left q.2⟩ =
        quotientKerSupEquiv hN' (QuotientGroup.mk (SemidirectProduct.inl (θQ q))) := by
      change quotientKerSupEquiv hN'
        (QuotientGroup.congr _ _ Φ hker
          ((quotientKerSupEquiv hN).symm ⟨q, Subgroup.mem_sup_left q.2⟩)) = _
      rw [← h1, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk, semidirectProduct_congr_inl]
    rw [h2, quotientKerSupEquiv_mk]
    simp
  · intro n
    have h1 : quotientKerSupEquiv hN (QuotientGroup.mk (SemidirectProduct.inr n)) =
        ⟨n, Subgroup.mem_sup_right n.2⟩ := by
      rw [quotientKerSupEquiv_mk]
      apply Subtype.ext
      simp
    have h2 : ζ ⟨n, Subgroup.mem_sup_right n.2⟩ =
        quotientKerSupEquiv hN' (QuotientGroup.mk (SemidirectProduct.inr (θN n))) := by
      change quotientKerSupEquiv hN'
        (QuotientGroup.congr _ _ Φ hker
          ((quotientKerSupEquiv hN).symm ⟨n, Subgroup.mem_sup_right n.2⟩)) = _
      rw [← h1, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk, semidirectProduct_congr_inr]
    rw [h2, quotientKerSupEquiv_mk]
    simp

theorem exists_mulEquiv_sup_glue_of_normal {Q N : Subgroup G} {Q' N' : Subgroup G'}
    (hQ : Q.Normal) (hQ' : Q'.Normal)
    (θQ : ↥Q ≃* ↥Q') (θN : ↥N ≃* ↥N')
    (hagree : ∀ (x : G) (hxQ : x ∈ Q) (hxN : x ∈ N), (θQ ⟨x, hxQ⟩ : G') = θN ⟨x, hxN⟩)
    (hback : ∀ n : ↥N, (θN n : G') ∈ Q' → (n : G) ∈ Q)
    (h : ∀ (n : ↥N) (q : ↥Q),
      ((θQ ⟨(n : G) * q * (n : G)⁻¹, hQ.conj_mem (q : G) q.2 (n : G)⟩ : ↥Q') : G') =
        (θN n : G') * (θQ q : G') * (θN n : G')⁻¹) :
    ∃ ζ : ↥(Q ⊔ N) ≃* ↥(Q' ⊔ N'),
      (∀ q : ↥Q, (ζ ⟨q, Subgroup.mem_sup_left q.2⟩ : G') = θQ q) ∧
      (∀ n : ↥N, (ζ ⟨n, Subgroup.mem_sup_right n.2⟩ : G') = θN n) := by
  haveI := hQ
  haveI := hQ'
  exact exists_mulEquiv_sup_glue (Subgroup.le_normalizer_of_normal (H := Q))
    (Subgroup.le_normalizer_of_normal (H := Q')) θQ θN hagree hback
    (fun n q _ => h n q)

end CFSG.GroupTheory
