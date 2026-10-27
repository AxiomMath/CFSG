module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC (FixΔ card_evenWeight)

variable {G : Type} [Group G]

structure PiS (S U : Subgroup G) where
  β : ↥U ≃* Multiplicative (evenWeight 5)
  π : ↥S →* Perm (Fin 5)
  hSU : S ≤ Subgroup.normalizer (U : Set G)
  hcomp : ∀ (y : ↥S) (u u' : ↥U),
    (u' : G) = (y : G) * (u : G) * (y : G)⁻¹ →
    Multiplicative.toAdd (β u') = vact (π y) (Multiplicative.toAdd (β u))
  hker : ∀ y : ↥S, π y = 1 ↔ ∀ u ∈ U, (y : G) * u * (y : G)⁻¹ = u

namespace PiS

variable {S U : Subgroup G} (D : PiS S U)

@[expose] def im (K : Subgroup G) : Subgroup (Perm (Fin 5)) :=
  (K.subgroupOf S).map D.π

theorem mem_im {K : Subgroup G} {g : Perm (Fin 5)} :
    g ∈ D.im K ↔ ∃ y : ↥S, (y : G) ∈ K ∧ D.π y = g := by
  unfold im
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem im_mono {K K' : Subgroup G} (h : K ≤ K') : D.im K ≤ D.im K' := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  exact (D.mem_im).2 ⟨y, h hy, rfl⟩

theorem pi_mem_im {K : Subgroup G} {y : ↥S} (hy : (y : G) ∈ K) :
    D.π y ∈ D.im K :=
  (D.mem_im).2 ⟨y, hy, rfl⟩

theorem card_im_mul {A : Subgroup G} (hAS : A ≤ S) :
    Nat.card (D.im A) * Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) =
      Nat.card A := by
  set K' := A.subgroupOf S with hK'
  have h1 := Subgroup.card_ker_mul_card_range (D.π.domRestrict K')
  rw [MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card K' = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv
  have h3 : Nat.card (D.π.domRestrict K').ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1.1 : G), y.1.2, Subgroup.mem_centralizer_iff.2 fun u hu => by
          have := (D.hker y.1.1).1 y.2 u hu
          calc u * (y.1.1 : G) = ((y.1.1 : G) * u * (y.1.1 : G)⁻¹) * (y.1.1 : G) := by rw [this]
            _ = (y.1.1 : G) * u := by group⟩
        invFun := fun k => ⟨⟨⟨k, hAS k.2.1⟩, Subgroup.mem_subgroupOf.2 k.2.1⟩, by
          show D.π ⟨k, hAS k.2.1⟩ = 1
          rw [D.hker]
          intro u hu
          have := Subgroup.mem_centralizer_iff.1 k.2.2 u hu
          calc (k : G) * u * (k : G)⁻¹ = (u * (k : G)) * (k : G)⁻¹ := by rw [this]
            _ = u := by group⟩
        left_inv := fun y => rfl
        right_inv := fun k => rfl }
  rw [← h2, ← h1, h3]
  show Nat.card (Subgroup.map D.π K') * _ = _
  ring

theorem card_fix {A : Subgroup G} (hAS : A ≤ S) :
    Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) = Nat.card (FixΔ (D.im A)) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨Multiplicative.toAdd (D.β ⟨u.1, u.2.1⟩), fun σ hσ => by
        obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hσ
        have hc := Subgroup.mem_centralizer_iff.1 u.2.2 y hy
        have h := D.hcomp y ⟨u.1, u.2.1⟩ ⟨u.1, u.2.1⟩ (by
          show (u : G) = (y : G) * (u : G) * (y : G)⁻¹
          rw [hc]; group)
        exact h.symm⟩
      invFun := fun w => ⟨((D.β.symm (Multiplicative.ofAdd w.1) : ↥U) : G),
        (D.β.symm (Multiplicative.ofAdd w.1)).2, Subgroup.mem_centralizer_iff.2 fun a ha => by
          set u := D.β.symm (Multiplicative.ofAdd w.1) with hu
          have hmem : (a : G) * (u : G) * (a : G)⁻¹ ∈ U := by
            have := D.hSU (hAS ha)
            exact (Subgroup.mem_normalizer_iff.mp this u).mp u.2
          have h := D.hcomp ⟨a, hAS ha⟩ u ⟨_, hmem⟩ rfl
          have hw : vact (D.π ⟨a, hAS ha⟩) (Multiplicative.toAdd (D.β u)) =
              Multiplicative.toAdd (D.β u) := by
            have := w.2 (D.π ⟨a, hAS ha⟩) (D.pi_mem_im (K := A) ha)
            simpa [hu] using this
          rw [hw] at h
          have h2 : (⟨_, hmem⟩ : ↥U) = u := D.β.injective (Multiplicative.toAdd.injective h)
          have h3 : (a : G) * (u : G) * (a : G)⁻¹ = (u : G) := congrArg Subtype.val h2
          calc (a : G) * u = ((a : G) * (u : G) * (a : G)⁻¹) * a := by group
            _ = (u : G) * a := by rw [h3]⟩
      left_inv := fun u => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }

include D in
theorem card_U : Nat.card ↥U = 16 := by
  rw [Nat.card_congr D.β.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5),
    card_evenWeight]

theorem im_elemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    (∀ g ∈ D.im A, g * g = 1) ∧ ∀ g ∈ D.im A, ∀ h ∈ D.im A, g * h = h * g := by
  constructor
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hA.2 _ hy)
    rw [← map_mul, this, map_one]
  · intro g hg h hh
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
    obtain ⟨z, hz, rfl⟩ := (D.mem_im).1 hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA hy hz)


open Classical in
@[expose] noncomputable def pf (g : G) : Perm (Fin 5) :=
  if h : g ∈ S then D.π ⟨g, h⟩ else 1

open Classical in
@[expose] noncomputable def bf (u : G) : evenWeight 5 :=
  if h : u ∈ U then Multiplicative.toAdd (D.β ⟨u, h⟩) else 0

theorem pf_eq {g : G} (h : g ∈ S) : D.pf g = D.π ⟨g, h⟩ := by
  simp [pf, h]

theorem pf_mk (y : ↥S) : D.pf (y : G) = D.π y :=
  D.pf_eq y.2

theorem pf_mul {g h : G} (hg : g ∈ S)
    (hh : h ∈ S) : D.pf (g * h) = D.pf g * D.pf h := by
  rw [D.pf_eq hg, D.pf_eq hh, D.pf_eq (mul_mem hg hh)]
  exact map_mul D.π ⟨g, hg⟩ ⟨h, hh⟩

theorem pf_inv {g : G} (hg : g ∈ S) : D.pf g⁻¹ = (D.pf g)⁻¹ := by
  rw [D.pf_eq hg, D.pf_eq (inv_mem hg)]
  exact map_inv D.π ⟨g, hg⟩

theorem bf_eq {u : G} (h : u ∈ U) : D.bf u = Multiplicative.toAdd (D.β ⟨u, h⟩) := by
  simp [bf, h]

theorem bf_mul {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    D.bf (u * u') = D.bf u + D.bf u' := by
  rw [D.bf_eq hu, D.bf_eq hu', D.bf_eq (mul_mem hu hu')]
  have : (⟨u * u', mul_mem hu hu'⟩ : ↥U) = ⟨u, hu⟩ * ⟨u', hu'⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem bf_one : D.bf 1 = 0 := by
  rw [D.bf_eq (one_mem _)]
  have : (⟨1, one_mem _⟩ : ↥U) = 1 := rfl
  rw [this, map_one]
  rfl

theorem bf_inj {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) (h : D.bf u = D.bf u') :
    u = u' := by
  rw [D.bf_eq hu, D.bf_eq hu'] at h
  have := D.β.injective (Multiplicative.toAdd.injective h)
  exact congrArg Subtype.val this

theorem bf_surj (w : evenWeight 5) : ∃ u, u ∈ U ∧ D.bf u = w := by
  refine ⟨((D.β.symm (Multiplicative.ofAdd w) : ↥U) : G), (D.β.symm _).2, ?_⟩
  rw [D.bf_eq (D.β.symm _).2]
  simp

include D in
theorem conj_mem_U {y u : G} (hy : y ∈ S)
    (hu : u ∈ U) : y * u * y⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp (D.hSU hy) u).mp hu

theorem bf_conj {y u : G} (hy : y ∈ S)
    (hu : u ∈ U) : D.bf (y * u * y⁻¹) = vact (D.pf y) (D.bf u) := by
  rw [D.bf_eq (D.conj_mem_U hy hu), D.bf_eq hu, D.pf_eq hy]
  exact D.hcomp ⟨y, hy⟩ ⟨u, hu⟩ ⟨y * u * y⁻¹, D.conj_mem_U hy hu⟩ rfl

theorem comm_iff {y u : G} (hy : y ∈ S)
    (hu : u ∈ U) : y * u = u * y ↔ vact (D.pf y) (D.bf u) = D.bf u := by
  have h := D.bf_conj hy hu
  constructor
  · intro hc
    have : y * u * y⁻¹ = u := by rw [hc]; group
    rw [← h, this]
  · intro hv
    have hb : D.bf (y * u * y⁻¹) = D.bf u := by rw [h, hv]
    have := D.bf_inj (D.conj_mem_U hy hu) hu hb
    calc y * u = (y * u * y⁻¹) * y := by group
      _ = u * y := by rw [this]

theorem mem_im_pf {A : Subgroup G} (hA : A ≤ S)
    {σ : Perm (Fin 5)} : σ ∈ D.im A ↔ ∃ y ∈ A, D.pf y = σ := by
  rw [D.mem_im]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, D.pf_mk y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hA hy⟩, hy, (D.pf_eq (hA hy)).symm⟩

theorem comm_vu {v v' u u' : G} (hv : v ∈ S)
    (hv' : v' ∈ S) (hu : u ∈ U) (hu' : u' ∈ U)
    (hvv : v * v' = v' * v) :
    (v * u) * (v' * u') = (v' * u') * (v * u) ↔
      vact (D.pf v')⁻¹ (D.bf u) + D.bf u' = vact (D.pf v)⁻¹ (D.bf u') + D.bf u := by
  have e1 : (v * u) * (v' * u') = (v * v') * ((v'⁻¹ * u * v'⁻¹⁻¹) * u') := by group
  have e2 : (v' * u') * (v * u) = (v' * v) * ((v⁻¹ * u' * v⁻¹⁻¹) * u) := by group
  have hm1 : (v'⁻¹ * u * v'⁻¹⁻¹) * u' ∈ U :=
    mul_mem (D.conj_mem_U (inv_mem hv') hu) hu'
  have hm2 : (v⁻¹ * u' * v⁻¹⁻¹) * u ∈ U :=
    mul_mem (D.conj_mem_U (inv_mem hv) hu') hu
  have hb1 : D.bf ((v'⁻¹ * u * v'⁻¹⁻¹) * u') = vact (D.pf v')⁻¹ (D.bf u) + D.bf u' := by
    rw [D.bf_mul (D.conj_mem_U (inv_mem hv') hu) hu', D.bf_conj (inv_mem hv') hu, D.pf_inv hv']
  have hb2 : D.bf ((v⁻¹ * u' * v⁻¹⁻¹) * u) = vact (D.pf v)⁻¹ (D.bf u') + D.bf u := by
    rw [D.bf_mul (D.conj_mem_U (inv_mem hv) hu') hu, D.bf_conj (inv_mem hv) hu', D.pf_inv hv]
  rw [e1, e2, hvv, mul_right_inj, ← hb1, ← hb2]
  constructor
  · intro h; rw [h]
  · intro h; exact D.bf_inj hm1 hm2 h

theorem card_fix_set (s : Set G) (hs : s ⊆ S) :
    Nat.card ↥(U ⊓ Subgroup.centralizer s) =
      Nat.card {w : evenWeight 5 // ∀ y ∈ s, vact (D.pf y) w = w} := by
  refine Nat.card_congr
    { toFun := fun u => ⟨D.bf u.1, fun y hy =>
        (D.comm_iff (hs hy) u.2.1).1 (Subgroup.mem_centralizer_iff.1 u.2.2 y hy)⟩
      invFun := fun w => ⟨((D.β.symm (Multiplicative.ofAdd w.1) : ↥U) : G),
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
        show D.bf ((D.β.symm (Multiplicative.ofAdd w.1) : ↥U) : G) = w.1
        rw [D.bf_eq (D.β.symm _).2]
        simp }

end PiS

end CFSG.QuasithinUnique.AppD
