module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCLin
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Eleven

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.SectionRank.Ccomm

section Transport

theorem isSubnormal_subgroupOf_map_equiv {M M' : Type*} [Group M] [Group M'] (σ : M ≃* M')
    {A K : Subgroup M} (h : (A.subgroupOf K).IsSubnormal) :
    ((A.map σ.toMonoidHom).subgroupOf (K.map σ.toMonoidHom)).IsSubnormal := by
  let f : ↥K →* ↥(K.map σ.toMonoidHom) :=
    (σ.toMonoidHom.comp K.subtype).codRestrict (K.map σ.toMonoidHom) (fun x => ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨z, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have h1 := h.map hf
  convert h1 using 1
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxA, hxz⟩
    obtain ⟨x', hx'K, hx'⟩ := z.2
    have hxx : x' = x := σ.injective (hx'.trans hxz.symm)
    refine ⟨⟨x, hxx ▸ hx'K⟩, ?_, Subtype.ext hxz⟩
    rw [Subgroup.mem_subgroupOf]
    exact hxA
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ha
    exact ⟨a, ha, rfl⟩

theorem map_centralizer_singleton {M M' : Type*} [Group M] [Group M'] (σ : M ≃* M') (s : M) :
    (Subgroup.centralizer ({s} : Set M)).map σ.toMonoidHom =
      Subgroup.centralizer ({σ s} : Set M') := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hz
    refine ⟨σ.symm z, ?_, by simp⟩
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]

end Transport

section Gen

variable {V : Type} [CommGroup V]

theorem exists_gen_of_card_three {Y : Subgroup (MulAut V)} (h3 : Nat.card ↥Y = 3) :
    ∃ y : MulAut V, Y = Subgroup.zpowers y ∧ y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Y := isCyclic_of_prime_card h3
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨(g : MulAut V), ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      exact (Subgroup.zpowers_le.mpr g.2) hx
  · have := pow_card_eq_one' (G := ↥Y) (x := g)
    rw [h3] at this
    exact congrArg Subtype.val this

end Gen

section Hyp

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem card_eq_two_pow {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2)) :
    Nat.card V = 2 ^ n := by
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

omit [Finite V] in
theorem le_six_of_card_le {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2))
    (h : Nat.card V ≤ 64) : n ≤ 6 := by
  rw [card_eq_two_pow e] at h
  by_contra hn
  push Not at hn
  have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem two_le_of_card_commV {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2))
    (h : Nat.card ↥(commV Y) = 4) : 2 ≤ n := by
  have h1 : Nat.card ↥(commV Y) ≤ Nat.card V :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [h, card_eq_two_pow e] at h1
  by_contra hn
  push Not at hn
  have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

omit [Finite V] in
theorem conjSub_zpowers (g y : MulAut V) :
    CGT6E.conjSub g (Subgroup.zpowers y) = Subgroup.zpowers (g * y * g⁻¹) := by
  rw [CGT6E.conjSub, MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

omit [Finite V] in
theorem zpowers_sup_eq_closure (y d t : MulAut V) :
    Subgroup.zpowers d ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers t =
      Subgroup.closure {y, d, t} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

variable {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2))

omit [Finite V] in
theorem routeCGroup_eq_map {y d t : MulAut V}
    (hgen : Subgroup.zpowers d ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers t = G) :
    routeCGroup (elemAutEquivGL e y) (elemAutEquivGL e d) (elemAutEquivGL e t) =
      G.map (elemAutEquivGL e).toMonoidHom := by
  rw [← hgen, zpowers_sup_eq_closure, routeCGroup, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨y, Or.inl rfl, rfl⟩
    · exact ⟨d, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨t, Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨a, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

end Hyp

section Main

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}
  {n : ℕ} (e : V ≃* Multiplicative (Fin n → ZMod 2))

theorem pCore_map_eq_bot {M M' : Type} [Group M] [Group M'] (σ : M ≃* M') {X : Subgroup M}
    (h : CFSG.pCore 2 ↥X = ⊥) : CFSG.pCore 2 ↥(X.map σ.toMonoidHom) = ⊥ :=
  pCore_eq_bot_of_equiv (X.equivMapOfInjective σ.toMonoidHom σ.injective).symm h

theorem Emb5Cfg.routeCHyp (cfg : Emb5Cfg G T Y) {y t g : MulAut V}
    (hy : Y = Subgroup.zpowers y) (hy3 : y ^ 3 = 1)
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hgen : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G) :
    RouteCHyp (elemAutEquivGL e y) (elemAutEquivGL e (g * y * g⁻¹)) (elemAutEquivGL e t) := by
  set σ := elemAutEquivGL e with hσ
  set d : MulAut V := g * y * g⁻¹ with hd
  have hconj : CGT6E.conjSub g Y = Subgroup.zpowers d := by
    rw [hy]
    exact conjSub_zpowers g y
  have hgen' : Subgroup.zpowers d ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers t = G := by
    rw [← hconj, ← hy]
    exact hgen
  have hGm := routeCGroup_eq_map (e := e) hgen'
  have hY4 : Nat.card ↥(commV (Subgroup.zpowers y)) = 4 := by
    rw [← hy]
    exact cfg.adm.h4
  have hd4 : Nat.card ↥(commV (Subgroup.zpowers d)) = 4 := by
    rw [← hconj, CGT6E.card_commV_conjSub]
    exact cfg.adm.h4
  have hd3 : d ^ 3 = 1 := by
    have := congrArg (MulAut.conj g) hy3
    simpa [map_pow, hd, MulAut.conj_apply] using this
  have hcomm : commV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers d) ⊔
      commV (Subgroup.zpowers t) = ⊤ := by
    have := cfg.commV_gen hgen
    rw [hconj, hy] at this
    simpa [hy] using this
  refine
    { y3 := ?_, d3 := ?_, rk_y := finrank_imSubOne_of_card_commV e y hY4,
      rk_d := finrank_imSubOne_of_card_commV e d hd4, t2 := ?_, t1 := ?_, ty := ?_,
      comm := imSubOne_sup_eq_top e y d t hcomm, o2 := ?_, cent := ?_ }
  · rw [← map_pow, hy3, map_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_pow, ht2, map_one]
  · intro h
    exact ht1 (σ.injective (by rw [h, map_one]))
  · have hty : y * t = t * y :=
      Subgroup.mem_centralizer_iff.mp ht.2 y (hy ▸ Subgroup.mem_zpowers y)
    rw [← map_mul, ← map_mul, hty]
  · rw [hGm]
    exact pCore_map_eq_bot σ cfg.o2
  · rw [hGm]
    intro s hs hs1 hs2 hsy
    obtain ⟨s₀, hs₀G, rfl⟩ := hs
    have hs₀1 : s₀ ≠ 1 := fun h => hs1 (by simp [h])
    have hs₀2 : s₀ ^ 2 = 1 := by
      apply σ.injective
      simpa [map_pow] using hs2
    have hyc : y ∈ Subgroup.centralizer ({s₀} : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      apply σ.injective
      simpa [map_mul] using hsy
    have hs₀C : s₀ ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Subgroup.centralizer ({s₀} : Set (MulAut V)) :=
        (Subgroup.zpowers_le.mpr hyc) (hy ▸ hh)
      exact (Subgroup.mem_centralizer_iff.mp hh' s₀ rfl).symm
    have hsub := cfg.cent s₀ ⟨hs₀G, hs₀C⟩ hs₀1 hs₀2
    have h2 := isSubnormal_subgroupOf_map_equiv σ hsub
    rw [Subgroup.map_inf _ _ _ σ.injective, map_centralizer_singleton σ s₀, hy,
      MonoidHom.map_zpowers] at h2
    exact h2

end Main

end CFSG.CGT.PushingUpLit.CGT6
