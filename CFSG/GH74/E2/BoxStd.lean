module

public import CFSG.GH74.E2.ComponentsUnique
public import CFSG.GH74.E2.TermBasic

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

section Conj

variable {G : Type} [Group G]

theorem conj_mul (H : Subgroup G) (a b : G) :
    conjugate H (a * b) = conjugate (conjugate H a) b := by
  ext x
  rw [AS16.mem_conjugate_iff', AS16.mem_conjugate_iff', AS16.mem_conjugate_iff']
  have : (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
  rw [this]

theorem conj_one (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [AS16.mem_conjugate_iff']
  simp

theorem conj_inv_eq {H K : Subgroup G} {a : G} (h : conjugate H a = K) :
    conjugate K a⁻¹ = H := by
  have := conj_mul H a a⁻¹
  rw [mul_inv_cancel, conj_one, h] at this
  exact this.symm

@[expose] def swapGrp (A B : Subgroup G) : Subgroup G where
  carrier := {h | (conjugate A h = A ∧ conjugate B h = B) ∨
    (conjugate A h = B ∧ conjugate B h = A)}
  mul_mem' := by
    rintro a b (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩) (⟨hb1, hb2⟩ | ⟨hb1, hb2⟩)
    · left
      exact ⟨by rw [conj_mul, ha1, hb1], by rw [conj_mul, ha2, hb2]⟩
    · right
      exact ⟨by rw [conj_mul, ha1, hb1], by rw [conj_mul, ha2, hb2]⟩
    · right
      exact ⟨by rw [conj_mul, ha1, hb2], by rw [conj_mul, ha2, hb1]⟩
    · left
      exact ⟨by rw [conj_mul, ha1, hb2], by rw [conj_mul, ha2, hb1]⟩
  one_mem' := Or.inl ⟨conj_one A, conj_one B⟩
  inv_mem' := by
    rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
    · exact Or.inl ⟨conj_inv_eq ha1, conj_inv_eq ha2⟩
    · exact Or.inr ⟨conj_inv_eq ha2, conj_inv_eq ha1⟩

@[expose] def fixGrp (A B : Subgroup G) : Subgroup G where
  carrier := {h | conjugate A h = A ∧ conjugate B h = B}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [conj_mul, ha1, hb1], by rw [conj_mul, ha2, hb2]⟩
  one_mem' := ⟨conj_one A, conj_one B⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨conj_inv_eq ha1, conj_inv_eq ha2⟩

end Conj

section Three

variable {G : Type} [Group G]

theorem false_of_three_commuting [Finite G] (hG : Gen4 G) {K1 K2 K3 : Subgroup G}
    (c12 : ∀ x ∈ K1, ∀ y ∈ K2, x * y = y * x) (c13 : ∀ x ∈ K1, ∀ y ∈ K3, x * y = y * x)
    (c23 : ∀ x ∈ K2, ∀ y ∈ K3, x * y = y * x)
    (z1 : ∀ x ∈ K1, (∀ y ∈ K1, x * y = y * x) → x = 1)
    (z2 : ∀ x ∈ K2, (∀ y ∈ K2, x * y = y * x) → x = 1)
    {A1 A2 A3 : Subgroup G} (h1 : A1 ≤ K1) (h2 : A2 ≤ K2) (h3 : A3 ≤ K3)
    (p1 : IsPGroup 2 ↥A1) (p2 : IsPGroup 2 ↥A2) (p3 : IsPGroup 2 ↥A3)
    (r1 : 2 ≤ Group.rank ↥A1) (r2 : 2 ≤ Group.rank ↥A2) (r3 : 2 ≤ Group.rank ↥A3) : False := by
  have hc12 : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a := fun a ha b hb => c12 a (h1 ha) b (h2 hb)
  have hbot12 : A1 ⊓ A2 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    refine z1 x (h1 hx1) fun y hy => ?_
    exact (c12 y hy x (h2 hx2)).symm
  have hr0 : Group.rank ↥(A1 ⊓ A2) = 0 := by
    rw [Subgroup.rank_congr hbot12]
    exact Group.rank_eq_zero _
  have hF2 := rank_sup_add_inf_ge A1 A2 p1 p2 hc12
  rw [hr0] at hF2
  have hQ : IsPGroup 2 ↥(A1 ⊔ A2) := isPGroup_sup_of_commute A1 A2 p1 p2 hc12
  have hcQ3 : ∀ q ∈ A1 ⊔ A2, ∀ t ∈ A3, q * t = t * q := by
    intro q hq t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc12 hq
    have e1 := c13 a (h1 ha) t (h3 ht)
    have e2 := c23 b (h2 hb) t (h3 ht)
    calc a * b * t = a * (b * t) := by group
      _ = a * (t * b) := by rw [e2]
      _ = (a * t) * b := by group
      _ = (t * a) * b := by rw [e1]
      _ = t * (a * b) := by group
  have hbotQ3 : (A1 ⊔ A2) ⊓ A3 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxQ, hx3⟩
    rw [Subgroup.mem_bot]
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc12 hxQ
    have hxK3 := h3 hx3
    have ha1 : a = 1 := by
      refine z1 a (h1 ha) fun y hy => ?_
      have hx := c13 y hy (a * b) hxK3
      have hby := c12 y hy b (h2 hb)
      have e : y * (a * b) = (a * b) * y := hx
      have h5 : (a * y) * b = (y * a) * b := by
        calc (a * y) * b = a * (y * b) := by group
          _ = a * (b * y) := by rw [hby]
          _ = (a * b) * y := by group
          _ = y * (a * b) := e.symm
          _ = (y * a) * b := by group
      exact mul_right_cancel h5
    have hb1 : b = 1 := by
      refine z2 b (h2 hb) fun y hy => ?_
      have hx := c23 y hy (a * b) hxK3
      have hay := c12 a (h1 ha) y hy
      have e : y * (a * b) = (a * b) * y := hx
      have h5 : a * (b * y) = a * (y * b) := by
        calc a * (b * y) = (a * b) * y := by group
          _ = y * (a * b) := e.symm
          _ = (y * a) * b := by group
          _ = (a * y) * b := by rw [← hay]
          _ = a * (y * b) := by group
      exact mul_left_cancel h5
    rw [ha1, hb1, mul_one]
  have hr0' : Group.rank ↥((A1 ⊔ A2) ⊓ A3) = 0 := by
    rw [Subgroup.rank_congr hbotQ3]
    exact Group.rank_eq_zero _
  have h4 := gen4_rank_add_le hG (A1 ⊔ A2) A3 hQ p3 hcQ3
  rw [hr0'] at h4
  omega

end Three

@[expose] def ShapeLM (K : Type) [Group K] : Prop := ShapeL33 K ∨ ShapeM11 K

theorem ShapeLM.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) :
    ShapeLM K → ShapeLM L :=
  Or.imp (fun h => lieModel_of_mulEquiv e h) (fun h => isSporadic_of_mulEquiv e h)

theorem ShapeLM.k0 {K : Type} [Group K] (h : ShapeLM K) : K0Shape K := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem ShapeLM.center_bot (hD3 : K0Data3) {K : Type} [Group K] [Finite K]
    (h : ShapeLM K) : Subgroup.center K = ⊥ := by
  rcases h with h | h
  · exact hD3.center_bot K (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hD3.center_bot K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

section Comp

variable {G : Type} [Group G]

theorem shapeLM_conj {K : Subgroup G} (h : ShapeLM ↥K) (g : G) : ShapeLM ↥(conjugate K g) :=
  ShapeLM.of_mulEquiv (MulEquiv.subgroupMap (MulAut.conj g⁻¹) K) h

@[expose] def TermComp (K : Subgroup G) : Prop :=
  ∀ y ∈ centralizer (K : Set G), orderOf y = 2 → IsCompIn (centralizer ({y} : Set G)) K

theorem TermComp.conj {K : Subgroup G} (h : TermComp K) (g : G) : TermComp (conjugate K g) := by
  intro t ht ht2
  have ht' : g * t * g⁻¹ ∈ centralizer (K : Set G) := by
    rw [← AS16.mem_conjugate_iff' (centralizer (K : Set G)) g t, AS16.conjugate_centralizer]
    exact ht
  have ho : orderOf (g * t * g⁻¹) = 2 := by
    rw [← ht2]
    exact (MulAut.conj g).orderOf_eq t
  have h1 := AS16.isCompIn_conj (h _ ht' ho) g
  rwa [AS16.conjugate_centralizer_singleton, show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h1

end Comp

section Y

variable {G : Type} [Group G] [Finite G]

theorem lmData (hD : K0Data) (hD3 : K0Data3) {K : Subgroup G} (h : ShapeLM ↥K) :
    (∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) ∧
      ∃ A : Subgroup G, A ≤ K ∧ IsPGroup 2 ↥A ∧ 2 ≤ Group.rank ↥A := by
  have hZ : center ↥K = ⊥ := ShapeLM.center_bot hD3 h
  refine ⟨fun x hx hc => ?_, ?_⟩
  · have : (⟨x, hx⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · obtain ⟨A, hAK, hA, hr2, -⟩ := exists_two_subgroup hD (ShapeLM.k0 h)
    exact ⟨A, hAK, hA, hr2 hZ⟩

theorem conj_comp_eq (hH : Hyp G) (hD : K0Data) (hD3 : K0Data3) {K K1 K2 : Subgroup G}
    (hsh : ShapeLM ↥K) (h1 : IsCompIn (centralizer (K : Set G)) K1)
    (h2 : IsCompIn (centralizer (K : Set G)) K2) {g1 g2 : G} (hg1 : K1 = conjugate K g1)
    (hg2 : K2 = conjugate K g2) : K1 = K2 := by
  by_contra hne
  have hsh1 : ShapeLM ↥K1 := hg1 ▸ shapeLM_conj hsh g1
  have hsh2 : ShapeLM ↥K2 := hg2 ▸ shapeLM_conj hsh g2
  obtain ⟨zK, A, hAK, hA, hrA⟩ := lmData hD hD3 hsh
  obtain ⟨zK1, A1, hA1, hA1p, hrA1⟩ := lmData hD hD3 hsh1
  obtain ⟨-, A2, hA2, hA2p, hrA2⟩ := lmData hD hD3 hsh2
  have hcomm12 : ∀ x ∈ K1, ∀ y ∈ K2, x * y = y * x := by
    rcases AS16.isCompIn_commute h1 h2 with h | h
    · exact absurd h hne
    · intro x hx y hy
      have : K1 ≤ centralizer (K2 : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (mem_centralizer_iff.1 (this hx) y hy).symm
  have hc0 : ∀ (K' : Subgroup G), K' ≤ centralizer (K : Set G) →
      ∀ x ∈ K, ∀ y ∈ K', x * y = y * x :=
    fun K' hK' x hx y hy => (mem_centralizer_iff.1 (hK' hy) x hx)
  exact false_of_three_commuting hH.gen4 (K1 := K) (K2 := K1) (K3 := K2) (hc0 K1 h1.1)
    (hc0 K2 h2.1) hcomm12 zK zK1 hAK hA1 hA2 hA hA1p hA2p hrA hrA1 hrA2

theorem isCompIn_symm {K K' : Subgroup G} (hterm : TermComp K)
    (hK' : IsCompIn (centralizer (K : Set G)) K') : IsCompIn (centralizer (K' : Set G)) K := by
  have hq' : IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'.1) hK'.2.1
  obtain ⟨x, hxK', hx2⟩ := AS16.exists_involution_of_isQuasisimple hq'
  have hxC : x ∈ centralizer (K : Set G) := hK'.1 hxK'
  have h1 := hterm x hxC hx2
  have hKle : K ≤ centralizer (K' : Set G) := fun k hk =>
    mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (hK'.1 hy) k hk).symm
  have hle : centralizer (K' : Set G) ≤ centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by simpa using hxK')
  exact isCompIn_mono h1 hKle hle

end Y

end CFSG.GH74.E2.Box
