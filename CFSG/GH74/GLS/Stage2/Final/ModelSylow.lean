module

public import CFSG.GH74.GLS.Stage2.Final.ModelSylowQ
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

theorem isPGroup_sup_of_commute {X : Type*} [Group X] [Finite X] {P Q : Subgroup X}
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hc : ∀ x ∈ P, ∀ y ∈ Q, Commute x y) :
    IsPGroup 2 ↥(P ⊔ Q) := by
  obtain ⟨φ, hrange⟩ : ∃ φ : ↥P × ↥Q →* X, φ.range = P ⊔ Q :=
    ⟨P.subtype.noncommCoprod Q.subtype (fun x y => by
      show Commute (x : X) (y : X)
      exact hc x x.2 y y.2), by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]⟩
  have hPQ : IsPGroup 2 (↥P × ↥Q) := by
    intro g
    obtain ⟨k₁, hk₁⟩ := hP g.1
    obtain ⟨k₂, hk₂⟩ := hQ g.2
    refine ⟨k₁ + k₂, ?_⟩
    have e1 : g.1 ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [pow_add, pow_mul, hk₁, _root_.one_pow]
    have e2 : g.2 ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hk₂, _root_.one_pow]
    exact Prod.ext (by simpa [Prod.pow_fst] using e1) (by simpa [Prod.pow_snd] using e2)
  have h2 : IsPGroup 2 ↥φ.range :=
    hPQ.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  rw [← hrange]
  exact h2

theorem mem_sylow_of_commute {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) {y : X}
    (hy : ∃ i : ℕ, y ^ 2 ^ i = 1) (hc : ∀ x ∈ (S : Subgroup X), Commute x y) :
    y ∈ (S : Subgroup X) := by
  obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hy
  have hz : IsPGroup 2 ↥(zpowers y) := IsPGroup.of_card hj
  have hQ : IsPGroup 2 ↥((S : Subgroup X) ⊔ zpowers y) :=
    isPGroup_sup_of_commute S.isPGroup' hz (fun x hx z hz' => by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz'
      rw [← hn]
      exact (hc x hx).zpow_right n)
  have heq := S.is_maximal' hQ le_sup_left
  have : y ∈ (S : Subgroup X) ⊔ zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rw [heq] at this
  exact this

theorem GoodModel.exists_center_sylow [Finite F] {M : ModelData F} (hG : GoodModel M) :
    ∃ S : Sylow 2 (PG M), CenterIs (S : Subgroup (PG M)) (yP M) := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  obtain ⟨S, hS⟩ := exists_sylow_center M hG.two_ne_zero hG.odd_index (rhoQ hab) hH
    (rhoQ_irr hab hG.two_ne_zero) (rhoQ_nc hab) isPGroup_q8q8
  exact ⟨S, (centerIs_iff _ _).1 hS⟩

theorem orderOf_conj_yP {M : ModelData F} (h2 : (2 : F) ≠ 0) (g : PG M) :
    orderOf ((MulAut.conj g) (yP M)) = 2 := by
  rw [MulEquiv.orderOf_eq]
  exact orderOf_yP M h2

theorem sylow_center_of_le_Cg [Finite F] {M : ModelData F} (hG : GoodModel M) (S : Sylow 2 (PG M))
    (hS : (S : Subgroup (PG M)) ≤ Cg M) : CenterIs (S : Subgroup (PG M)) (yP M) := by
  have h2 := hG.two_ne_zero
  obtain ⟨S₁, hS₁⟩ := hG.exists_center_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PG M) S₁ S
  have hcoe : ((g • S₁ : Sylow 2 (PG M)) : Subgroup (PG M)) =
      (S₁ : Subgroup (PG M)).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have h1 : CenterIs (S : Subgroup (PG M)) ((MulAut.conj g) (yP M)) := by
    rw [← hg, hcoe]
    exact hS₁.map_equiv (MulAut.conj g)
  have hcomm : ∀ x ∈ (S : Subgroup (PG M)), Commute x (yP M) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hS hx)
  have hyS : yP M ∈ (S : Subgroup (PG M)) :=
    mem_sylow_of_commute S ⟨1, by rw [pow_one, sq]; exact yP_sq M⟩ hcomm
  have hmem : yP M ∈ Subgroup.zpowers ((MulAut.conj g) (yP M)) :=
    (h1 (yP M)).1 ⟨hyS, fun s hs => (hcomm s hs).eq⟩
  have heq : yP M = (MulAut.conj g) (yP M) :=
    eq_of_mem_zpowers_of_orderOf_two (orderOf_conj_yP h2 g) (orderOf_yP M h2) hmem
  rw [heq]
  exact h1


theorem map_inf_subtype {G : Type*} [Group G] {C E : Subgroup G} (hEC : E ≤ C) (S' : Subgroup ↥C) :
    (S' ⊓ E.subgroupOf C).map C.subtype = S'.map C.subtype ⊓ E := by
  rw [Subgroup.map_inf _ _ _ C.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hEC]

theorem exists_sylow_le_quot4 {G : Type*} [Group G] [Finite G] (C E : Subgroup G) (hCodd : Odd C.index)
    (hEC : E ≤ C) (hEn : (E.subgroupOf C).Normal) {o : ℕ} (ho : Odd o)
    (hidx : (E.subgroupOf C).index = 4 * o) {a b : G} {W : Subgroup G} (hW : IsPGroup 2 W)
    (haW : a ∈ W) (hbW : b ∈ W) (hWC : W ≤ C)
    (ha2 : a * a ∈ E) (haE : a ∉ E) (hbE : b ∉ E) (habE : a * b ∉ E) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ C ∧ a ∈ (S : Subgroup G) ∧ b ∈ (S : Subgroup G) ∧
      Nat.card (S : Subgroup G) = 4 * Nat.card ↥((S : Subgroup G) ⊓ E) ∧
      ∀ s ∈ (S : Subgroup G), ∃ k ∈ (S : Subgroup G) ⊓ E,
        s = k ∨ s = k * a ∨ s = k * b ∨ s = k * (a * b) := by
  classical
  have haC : a ∈ C := hWC haW
  have hbC : b ∈ C := hWC hbW
  have hW' : IsPGroup 2 (W.subgroupOf C) := hW.comap_subtype
  have hWe : IsPGroup 2 (W.subgroupOf C) := hW'
  obtain ⟨S', hS'a, hS'b, hS'c, hS'd⟩ := ModelSylowQ.exists_sylow_quot4 (E.subgroupOf C) ho hidx
    (a := ⟨a, haC⟩) (b := ⟨b, hbC⟩) hWe (by rw [Subgroup.mem_subgroupOf]; exact haW)
    (by rw [Subgroup.mem_subgroupOf]; exact hbW)
    (by rw [Subgroup.mem_subgroupOf]; exact ha2) (by rw [Subgroup.mem_subgroupOf]; exact haE)
    (by rw [Subgroup.mem_subgroupOf]; exact hbE) (by rw [Subgroup.mem_subgroupOf]; exact habE)
  obtain ⟨S, hS⟩ := sylow_of_odd_index C hCodd S'
  have hSC : (S : Subgroup G) ≤ C := by rw [hS]; exact Subgroup.map_subtype_le _
  have hmem : ∀ x : ↥C, x ∈ (S' : Subgroup ↥C) → (x : G) ∈ (S : Subgroup G) := fun x hx => by
    rw [hS]; exact ⟨x, hx, rfl⟩
  refine ⟨S, hSC, hmem _ hS'a, hmem _ hS'b, ?_, ?_⟩
  · have h1 : Nat.card (S : Subgroup G) = Nat.card (S' : Subgroup ↥C) := by
      rw [hS]; exact Subgroup.card_map_of_injective C.subtype_injective
    have h2 : (S : Subgroup G) ⊓ E = ((S' : Subgroup ↥C) ⊓ E.subgroupOf C).map C.subtype := by
      rw [map_inf_subtype hEC, hS]
    have h3 : Nat.card ↥((S : Subgroup G) ⊓ E) = Nat.card ↥((S' : Subgroup ↥C) ⊓ E.subgroupOf C) := by
      rw [h2]; exact Subgroup.card_map_of_injective C.subtype_injective
    rw [h1, h3]; exact hS'c
  · intro s hs
    rw [hS] at hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨k', hk', hk⟩ := hS'd s' hs'
    refine ⟨(k' : G), ?_, ?_⟩
    · refine ⟨hmem _ hk'.1, ?_⟩
      exact (Subgroup.mem_subgroupOf.1 hk'.2)
    · rcases hk with h | h | h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (Or.inl (congrArg Subtype.val h))
      · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
      · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem exists_sylow_le_quot2 {G : Type*} [Group G] [Finite G] (C E : Subgroup G) (hCodd : Odd C.index)
    (hEC : E ≤ C) (hEn : (E.subgroupOf C).Normal) {o : ℕ} (ho : Odd o)
    (hidx : (E.subgroupOf C).index = 2 * o) {a : G} {W : Subgroup G} (hW : IsPGroup 2 W)
    (haW : a ∈ W) (hWC : W ≤ C) (haE : a ∉ E) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ C ∧ a ∈ (S : Subgroup G) ∧ W ≤ (S : Subgroup G) ∧
      Nat.card (S : Subgroup G) = 2 * Nat.card ↥((S : Subgroup G) ⊓ E) ∧
      ∀ s ∈ (S : Subgroup G), ∃ k ∈ (S : Subgroup G) ⊓ E, s = k ∨ s = k * a := by
  classical
  have haC : a ∈ C := hWC haW
  have hWe : IsPGroup 2 (W.subgroupOf C) := hW.comap_subtype
  obtain ⟨S', hS'a, hS'W, hS'c, hS'd⟩ := ModelSylowQ.exists_sylow_quot2 (E.subgroupOf C) ho hidx
    (a := ⟨a, haC⟩) hWe (by rw [Subgroup.mem_subgroupOf]; exact haW)
    (by rw [Subgroup.mem_subgroupOf]; exact haE)
  obtain ⟨S, hS⟩ := sylow_of_odd_index C hCodd S'
  have hSC : (S : Subgroup G) ≤ C := by rw [hS]; exact Subgroup.map_subtype_le _
  have hmem : ∀ x : ↥C, x ∈ (S' : Subgroup ↥C) → (x : G) ∈ (S : Subgroup G) := fun x hx => by
    rw [hS]; exact ⟨x, hx, rfl⟩
  refine ⟨S, hSC, hmem _ hS'a, ?_, ?_, ?_⟩
  · intro x hx
    have hxC : x ∈ C := hWC hx
    exact hmem ⟨x, hxC⟩ (hS'W (by rw [Subgroup.mem_subgroupOf]; exact hx))
  · have h1 : Nat.card (S : Subgroup G) = Nat.card (S' : Subgroup ↥C) := by
      rw [hS]; exact Subgroup.card_map_of_injective C.subtype_injective
    have h2 : (S : Subgroup G) ⊓ E = ((S' : Subgroup ↥C) ⊓ E.subgroupOf C).map C.subtype := by
      rw [map_inf_subtype hEC, hS]
    have h3 : Nat.card ↥((S : Subgroup G) ⊓ E) = Nat.card ↥((S' : Subgroup ↥C) ⊓ E.subgroupOf C) := by
      rw [h2]; exact Subgroup.card_map_of_injective C.subtype_injective
    rw [h1, h3]; exact hS'c
  · intro s hs
    rw [hS] at hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨k', hk', hk⟩ := hS'd s' hs'
    refine ⟨(k' : G), ?_, ?_⟩
    · refine ⟨hmem _ hk'.1, ?_⟩
      exact (Subgroup.mem_subgroupOf.1 hk'.2)
    · rcases hk with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
