module

public import CFSG.GH74.GLS.Balance.PStarUtil
public import CFSG.GH74.GLS.Balance.Bender.OpStarBasic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oResOf_eq_closure (p : ℕ) (X : Subgroup G) :
    oResOf p X = Subgroup.closure {x : G | x ∈ X ∧ Nat.Coprime (orderOf x) p} := by
  unfold oResOf oResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, by simpa using h, rfl⟩

omit [Finite G] in
theorem oResOf_le (p : ℕ) (X : Subgroup G) : oResOf p X ≤ X := by
  rw [oResOf_eq_closure]
  exact (Subgroup.closure_le X).2 fun x hx => hx.1

omit [Finite G] in
theorem mem_oResOf {p : ℕ} {X : Subgroup G} {x : G} (hx : x ∈ X) (h : Nat.Coprime (orderOf x) p) :
    x ∈ oResOf p X := by
  rw [oResOf_eq_closure]
  exact Subgroup.subset_closure ⟨hx, h⟩

omit [Finite G] in
theorem oResOf_mono {p : ℕ} {X Y : Subgroup G} (h : X ≤ Y) : oResOf p X ≤ oResOf p Y := by
  rw [oResOf_eq_closure, oResOf_eq_closure]
  exact Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

omit [Finite G] in
theorem oResOf_le_of {p : ℕ} {X H : Subgroup G} (h : ∀ x ∈ X, Nat.Coprime (orderOf x) p → x ∈ H) :
    oResOf p X ≤ H := by
  rw [oResOf_eq_closure]
  exact (Subgroup.closure_le H).2 fun x hx => h x hx.1 hx.2

theorem exists_isSylowIn (p : ℕ) [Fact p.Prime] (N : Subgroup G) :
    ∃ T : Subgroup G, IsSylowIn p T N := by
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥N))
  refine ⟨(S : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map N.subtype, fun T hTN hT2 => ?_⟩
  have hT' : IsPGroup p (T.subgroupOf N) := hT2.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  have e1 : Nat.card T = Nat.card (T.subgroupOf N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv.symm
  have e2 : Nat.card ((S : Subgroup ↥N).map N.subtype) = Nat.card S :=
    Subgroup.card_map_of_injective N.subtype_injective
  rw [e1, e2, Sylow.card_eq_multiplicity S]
  calc Nat.card (T.subgroupOf N) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    _ = _ := Sylow.card_eq_multiplicity S'

theorem isSylowIn_of_sylow (p : ℕ) [Fact p.Prime] {N : Subgroup G} (S : Sylow p ↥N) :
    IsSylowIn p ((S : Subgroup ↥N).map N.subtype) N := by
  refine ⟨Subgroup.map_subtype_le _, S.isPGroup'.map N.subtype, fun T hTN hT2 => ?_⟩
  have hT' : IsPGroup p (T.subgroupOf N) := hT2.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  have e1 : Nat.card T = Nat.card (T.subgroupOf N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv.symm
  have e2 : Nat.card ((S : Subgroup ↥N).map N.subtype) = Nat.card S :=
    Subgroup.card_map_of_injective N.subtype_injective
  rw [e1, e2, Sylow.card_eq_multiplicity S]
  calc Nat.card (T.subgroupOf N) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    _ = _ := Sylow.card_eq_multiplicity S'

theorem exists_sylow_of_isSylowIn (p : ℕ) [Fact p.Prime] {N T : Subgroup G} (hT : IsSylowIn p T N) :
    ∃ S : Sylow p ↥N, (S : Subgroup ↥N).map N.subtype = T := by
  obtain ⟨hTN, hT2, hTs⟩ := hT
  have hT' : IsPGroup p (T.subgroupOf N) := hT2.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨S, hS⟩ := hT'.exists_le_sylow
  have hmap : (T.subgroupOf N).map N.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTN
  have h1 : T ≤ (S : Subgroup ↥N).map N.subtype := by
    rw [← hmap]; exact Subgroup.map_mono hS
  have h2 : Nat.card ((S : Subgroup ↥N).map N.subtype) ≤ Nat.card T :=
    hTs _ (Subgroup.map_subtype_le _) (S.isPGroup'.map N.subtype)
  exact ⟨S, (Subgroup.eq_of_le_of_card_ge h1 h2).symm⟩

omit [Finite G] in
theorem IsSylowIn.map {G' : Type} [Group G'] {f : G' →* G} (hf : Function.Injective f)
    {p : ℕ} {T N : Subgroup G'} (h : IsSylowIn p T N) : IsSylowIn p (T.map f) (N.map f) := by
  obtain ⟨hTN, hT2, hTs⟩ := h
  refine ⟨Subgroup.map_mono hTN, hT2.map f, fun S hSN hS2 => ?_⟩
  have hSr : S ≤ f.range := hSN.trans (Subgroup.map_le_range f N)
  have hS' : S = (S.comap f).map f := (Subgroup.map_comap_eq_self hSr).symm
  have hc : S.comap f ≤ N := by
    intro x hx
    have : f x ∈ N.map f := hSN hx
    obtain ⟨y, hy, hyx⟩ := this
    rw [← hf hyx]; exact hy
  have hcp : IsPGroup p (S.comap f) := hS2.comap_of_injective f hf
  calc Nat.card S = Nat.card ((S.comap f).map f) := by rw [← hS']
    _ = Nat.card (S.comap f) := Subgroup.card_map_of_injective hf
    _ ≤ Nat.card T := hTs _ hc hcp
    _ = Nat.card (T.map f) := (Subgroup.card_map_of_injective hf).symm

theorem IsPStar.mul_centralizer {p : ℕ} [Fact p.Prime] {Y N Q : Subgroup G} (hY : IsPStar p ↥Y)
    (hNY : N ≤ Y) (hNn : (N.subgroupOf Y).Normal) (hQ : IsSylowIn p Q N) :
    ∀ y ∈ Y, ∃ n ∈ N, ∃ c ∈ Y ⊓ centralizer (Q : Set G), y = n * c := by
  obtain ⟨hQN, hQ2, hQs⟩ := hQ
  set N' : Subgroup ↥Y := N.subgroupOf Y with hN'
  set Q' : Subgroup ↥N' := (Q.subgroupOf Y).subgroupOf N' with hQ'
  have hQY : Q ≤ Y := hQN.trans hNY
  have hQN' : Q.subgroupOf Y ≤ N' := fun q hq => hQN hq
  have hQ'2 : IsPGroup p Q' := by
    have h1 : IsPGroup p (Q.subgroupOf Y) := hQ2.comap_of_injective Y.subtype Y.subtype_injective
    exact h1.comap_of_injective N'.subtype N'.subtype_injective
  obtain ⟨S, hS⟩ := hQ'2.exists_le_sylow
  set T'' : Subgroup G := ((S : Subgroup ↥N').map N'.subtype).map Y.subtype with hT''
  have hT''N : T'' ≤ N := by
    rintro _ ⟨_, ⟨s, _, rfl⟩, rfl⟩
    exact s.2
  have hT''2 : IsPGroup p T'' := (S.isPGroup'.map N'.subtype).map Y.subtype
  have hQT'' : Q ≤ T'' := by
    intro q hq
    have hq' : (⟨⟨q, hQY hq⟩, hQN hq⟩ : ↥N') ∈ Q' := hq
    exact ⟨_, ⟨_, hS hq', rfl⟩, rfl⟩
  have hcard1 : Nat.card T'' ≤ Nat.card Q := hQs T'' hT''N hT''2
  have hT''Q : T'' = Q := (Subgroup.eq_of_le_of_card_ge hQT'' hcard1).symm
  have hSQ : (S : Subgroup ↥N').map N'.subtype = Q.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [← hT'', hT''Q, Subgroup.map_subgroupOf_eq_of_le hQY]
  have htop := hY.2 N' hNn S
  rw [hSQ] at htop
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥Y) ∈ N' ⊔ centralizer ((Q.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [htop]; exact Subgroup.mem_top _
  have : N'.Normal := hNn
  obtain ⟨n', hn', c', hc', hnc⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(n' : G), hn', (c' : G), ⟨c'.2, ?_⟩, ?_⟩
  · show (c' : G) ∈ centralizer (Q : Set G)
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : (⟨q, hQY hq⟩ : ↥Y) ∈ Q.subgroupOf Y := hq
    have := mem_centralizer_iff.mp hc' _ hq'
    exact congrArg Subtype.val this
  · exact (congrArg Subtype.val hnc).symm

omit [Finite G] in
theorem IsPStar.oResOf_eq {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : IsPStar p ↥X) :
    oResOf p X = X := by
  have h := hX.1
  unfold oResOf
  rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isPStar_iff {p : ℕ} [Fact p.Prime] {X : Subgroup G} :
    IsPStar p ↥X ↔ oResOf p X = X ∧ ∀ N P : Subgroup G, N ≤ X → (N.subgroupOf X).Normal →
      IsSylowIn p P N → X ≤ N ⊔ (X ⊓ centralizer (P : Set G)) := by
  constructor
  · intro hX
    refine ⟨hX.oResOf_eq, fun N P hNX hNn hP y hy => ?_⟩
    obtain ⟨n, hn, c, hc, rfl⟩ := hX.mul_centralizer hNX hNn hP y hy
    exact Subgroup.mul_mem_sup hn hc
  · rintro ⟨hres, hmain⟩
    refine ⟨?_, fun N' hN' P' => ?_⟩
    · apply Subgroup.map_injective X.subtype_injective
      have h1 : (oResidual p ↥X).map X.subtype = oResOf p X := rfl
      rw [h1, hres, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · set N : Subgroup G := N'.map X.subtype with hN
      have hNX : N ≤ X := Subgroup.map_subtype_le _
      have hNsub : N.subgroupOf X = N' :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective N'
      have hNn : (N.subgroupOf X).Normal := by rw [hNsub]; exact hN'
      have hXn : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
      have hPs : IsSylowIn p (((P' : Subgroup ↥N').map N'.subtype).map X.subtype) N :=
        IsSylowIn.map X.subtype_injective (isSylowIn_of_sylow p P')
      have h := hmain N _ hNX hNn hPs
      rw [eq_top_iff]
      intro y _
      have hy := h y.2
      obtain ⟨n, hn, c, hc, hnc⟩ := (mem_sup_of_le_normalizer (inf_le_left.trans hXn)).1 hy
      obtain ⟨n', hn', rfl⟩ := hn
      have hcc : (⟨c, hc.1⟩ : ↥X) ∈
          centralizer (((P' : Subgroup ↥N').map N'.subtype : Subgroup ↥X) : Set ↥X) := by
        rw [mem_centralizer_iff]
        intro z hz
        have hz' : (z : G) ∈
            (((P' : Subgroup ↥N').map N'.subtype).map X.subtype : Subgroup G) := ⟨z, hz, rfl⟩
        have := mem_centralizer_iff.mp hc.2 _ hz'
        exact Subtype.ext this
      have hy' : y = n' * ⟨c, hc.1⟩ := Subtype.ext hnc.symm
      rw [hy']
      exact Subgroup.mul_mem_sup hn' hcc

end CFSG.GH74.GLS.Balance
