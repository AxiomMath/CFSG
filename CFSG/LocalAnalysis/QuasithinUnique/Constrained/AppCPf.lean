module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G]

namespace PiData

variable {L : Subgroup G} (D : PiData L)

open Classical in
@[expose] noncomputable def pf (g : G) : Perm (Fin 5) :=
  if h : g ∈ Subgroup.normalizer (L : Set G) then D.π ⟨g, h⟩ else 1

open Classical in
@[expose] noncomputable def bf (u : G) : evenWeight 5 :=
  if h : u ∈ blockU L then Multiplicative.toAdd (D.β ⟨u, h⟩) else 0

theorem pf_eq {g : G} (h : g ∈ Subgroup.normalizer (L : Set G)) : D.pf g = D.π ⟨g, h⟩ := by
  simp [pf, h]

theorem pf_mk (y : ↥(Subgroup.normalizer (L : Set G))) : D.pf (y : G) = D.π y :=
  D.pf_eq y.2

theorem pf_mul {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) : D.pf (g * h) = D.pf g * D.pf h := by
  rw [D.pf_eq hg, D.pf_eq hh, D.pf_eq (mul_mem hg hh)]
  exact map_mul D.π ⟨g, hg⟩ ⟨h, hh⟩

theorem pf_inv {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) : D.pf g⁻¹ = (D.pf g)⁻¹ := by
  rw [D.pf_eq hg, D.pf_eq (inv_mem hg)]
  exact map_inv D.π ⟨g, hg⟩

theorem bf_eq {u : G} (h : u ∈ blockU L) : D.bf u = Multiplicative.toAdd (D.β ⟨u, h⟩) := by
  simp [bf, h]

theorem bf_mul {u u' : G} (hu : u ∈ blockU L) (hu' : u' ∈ blockU L) :
    D.bf (u * u') = D.bf u + D.bf u' := by
  rw [D.bf_eq hu, D.bf_eq hu', D.bf_eq (mul_mem hu hu')]
  have : (⟨u * u', mul_mem hu hu'⟩ : ↥(blockU L)) = ⟨u, hu⟩ * ⟨u', hu'⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem bf_one : D.bf 1 = 0 := by
  rw [D.bf_eq (one_mem _)]
  have : (⟨1, one_mem _⟩ : ↥(blockU L)) = 1 := rfl
  rw [this, map_one]
  rfl

theorem bf_inj {u u' : G} (hu : u ∈ blockU L) (hu' : u' ∈ blockU L) (h : D.bf u = D.bf u') :
    u = u' := by
  rw [D.bf_eq hu, D.bf_eq hu'] at h
  have := D.β.injective (Multiplicative.toAdd.injective h)
  exact congrArg Subtype.val this

theorem bf_surj (w : evenWeight 5) : ∃ u, u ∈ blockU L ∧ D.bf u = w := by
  refine ⟨((D.β.symm (Multiplicative.ofAdd w) : ↥(blockU L)) : G), (D.β.symm _).2, ?_⟩
  rw [D.bf_eq (D.β.symm _).2]
  simp

theorem conj_mem_U [Finite G] {y u : G} (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hu : u ∈ blockU L) : y * u * y⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hy) u).mp hu

theorem bf_conj [Finite G] {y u : G} (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hu : u ∈ blockU L) : D.bf (y * u * y⁻¹) = vact (D.pf y) (D.bf u) := by
  rw [D.bf_eq (conj_mem_U hy hu), D.bf_eq hu, D.pf_eq hy]
  exact D.hcomp ⟨y, hy⟩ ⟨u, hu⟩ ⟨y * u * y⁻¹, conj_mem_U hy hu⟩ rfl

theorem comm_iff [Finite G] {y u : G} (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hu : u ∈ blockU L) : y * u = u * y ↔ vact (D.pf y) (D.bf u) = D.bf u := by
  have h := D.bf_conj hy hu
  constructor
  · intro hc
    have : y * u * y⁻¹ = u := by rw [hc]; group
    rw [← h, this]
  · intro hv
    have hb : D.bf (y * u * y⁻¹) = D.bf u := by rw [h, hv]
    have := D.bf_inj (conj_mem_U hy hu) hu hb
    calc y * u = (y * u * y⁻¹) * y := by group
      _ = u * y := by rw [this]

theorem mem_im_pf [Finite G] {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (L : Set G))
    {σ : Perm (Fin 5)} : σ ∈ D.im A ↔ ∃ y ∈ A, D.pf y = σ := by
  rw [D.mem_im]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, D.pf_mk y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hA hy⟩, hy, (D.pf_eq (hA hy)).symm⟩

theorem comm_vu [Finite G] {v v' u u' : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hv' : v' ∈ Subgroup.normalizer (L : Set G)) (hu : u ∈ blockU L) (hu' : u' ∈ blockU L)
    (hvv : v * v' = v' * v) :
    (v * u) * (v' * u') = (v' * u') * (v * u) ↔
      vact (D.pf v')⁻¹ (D.bf u) + D.bf u' = vact (D.pf v)⁻¹ (D.bf u') + D.bf u := by
  have e1 : (v * u) * (v' * u') = (v * v') * ((v'⁻¹ * u * v'⁻¹⁻¹) * u') := by group
  have e2 : (v' * u') * (v * u) = (v' * v) * ((v⁻¹ * u' * v⁻¹⁻¹) * u) := by group
  have hm1 : (v'⁻¹ * u * v'⁻¹⁻¹) * u' ∈ blockU L :=
    mul_mem (conj_mem_U (inv_mem hv') hu) hu'
  have hm2 : (v⁻¹ * u' * v⁻¹⁻¹) * u ∈ blockU L :=
    mul_mem (conj_mem_U (inv_mem hv) hu') hu
  have hb1 : D.bf ((v'⁻¹ * u * v'⁻¹⁻¹) * u') = vact (D.pf v')⁻¹ (D.bf u) + D.bf u' := by
    rw [D.bf_mul (conj_mem_U (inv_mem hv') hu) hu', D.bf_conj (inv_mem hv') hu, D.pf_inv hv']
  have hb2 : D.bf ((v⁻¹ * u' * v⁻¹⁻¹) * u) = vact (D.pf v)⁻¹ (D.bf u') + D.bf u := by
    rw [D.bf_mul (conj_mem_U (inv_mem hv) hu') hu, D.bf_conj (inv_mem hv) hu', D.pf_inv hv]
  rw [e1, e2, hvv, mul_right_inj, ← hb1, ← hb2]
  constructor
  · intro h; rw [h]
  · intro h; exact D.bf_inj hm1 hm2 h

theorem card_fix_set [Finite G] (s : Set G) (hs : s ⊆ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer s) =
      Nat.card {w : evenWeight 5 // ∀ y ∈ s, vact (D.pf y) w = w} := by
  refine Nat.card_congr
    { toFun := fun u => ⟨D.bf u.1, fun y hy =>
        (D.comm_iff (hs hy) u.2.1).1 (Subgroup.mem_centralizer_iff.1 u.2.2 y hy)⟩
      invFun := fun w => ⟨((D.β.symm (Multiplicative.ofAdd w.1) : ↥(blockU L)) : G),
        (D.β.symm _).2, Subgroup.mem_centralizer_iff.2 fun y hy =>
          (D.comm_iff (hs hy) (D.β.symm _).2).2 (by
            rw [D.bf_eq (D.β.symm _).2]
            simpa using w.2 y hy)⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply D.bf_inj (D.β.symm _).2 u.2.1
        rw [D.bf_eq (D.β.symm _).2]
        simp [D.bf_eq u.2.1]
      right_inv := fun w => by
        apply Subtype.ext
        show D.bf ((D.β.symm (Multiplicative.ofAdd w.1) : ↥(blockU L)) : G) = w.1
        rw [D.bf_eq (D.β.symm _).2]
        simp }

end PiData

theorem card_vfix (σ : Perm (Fin 5)) :
    Nat.card {w : evenWeight 5 // vact σ w = w} =
      (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ pact σ f = f).card := by
  rw [← Fintype.card_coe (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ pact σ f = f),
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨w.1.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w.1.2, congrArg Subtype.val w.2⟩⟩
      invFun := fun f => ⟨⟨f.1, by
        have := f.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this.1⟩, by
        have := f.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact Subtype.ext this.2⟩
      left_inv := fun w => rfl
      right_inv := fun f => rfl }

theorem card_vfix_t1 : Nat.card {w : evenWeight 5 // vact (swap 0 1) w = w} = 8 := by
  rw [card_vfix]; decide +kernel

theorem card_vfix_t2 : Nat.card {w : evenWeight 5 // vact (swap 2 3) w = w} = 8 := by
  rw [card_vfix]; decide +kernel

end CFSG.QuasithinUnique.AppC
