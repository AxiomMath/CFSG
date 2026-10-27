module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBAct

public section
namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_comm_of_card_le_F4 {V : Subgroup G} (hV : IsElemAbelian 2 V) {u : G}
    (hu : u ∈ Subgroup.normalizer (V : Set G)) (hu2 : u * u = 1)
    (hcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ Nat.card V) :
    ∀ x ∈ V ⊓ Subgroup.centralizer ({u} : Set G), ∃ v ∈ V, x = v * u * v⁻¹ * u⁻¹ := by
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hV hx hy
  have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV.2 x hx)
  have hmem : ∀ v ∈ V, v * u * v⁻¹ * u⁻¹ ∈ V := by
    intro v hv
    have : u * v⁻¹ * u⁻¹ ∈ V := conj_mem hu (V.inv_mem hv)
    simpa [mul_assoc] using V.mul_mem hv this
  let f : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨v * u * v⁻¹ * u⁻¹, hmem v v.2⟩) (by
    intro v w
    apply Subtype.ext
    have hfw := hmem w w.2
    have hfv := hmem v v.2
    show (v * w : G) * u * ((v * w : G))⁻¹ * u⁻¹ =
      ((v : G) * u * (v : G)⁻¹ * u⁻¹) * ((w : G) * u * (w : G)⁻¹ * u⁻¹)
    calc (v * w : G) * u * ((v * w : G))⁻¹ * u⁻¹
        = (v : G) * ((w : G) * u * (w : G)⁻¹ * u⁻¹) * (u * (v : G)⁻¹ * u⁻¹) := by group
      _ = ((w : G) * u * (w : G)⁻¹ * u⁻¹) * (v : G) * (u * (v : G)⁻¹ * u⁻¹) := by
          rw [hcomm _ v.2 _ hfw]
      _ = ((w : G) * u * (w : G)⁻¹ * u⁻¹) * ((v : G) * u * (v : G)⁻¹ * u⁻¹) := by group
      _ = ((v : G) * u * (v : G)⁻¹ * u⁻¹) * ((w : G) * u * (w : G)⁻¹ * u⁻¹) := by
          rw [hcomm _ hfw _ hfv])
  let C : Subgroup ↥V := (V ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf V
  have hker : f.ker = C := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show (⟨(v : G) * u * (v : G)⁻¹ * u⁻¹, hmem v v.2⟩ : ↥V) = 1 ↔ _
    rw [Subtype.ext_iff]
    simp only [Subgroup.coe_one, mul_inv_eq_one]
    constructor
    · intro h
      refine ⟨v.2, ?_⟩
      calc (v : G) * u = ((v : G) * u * (v : G)⁻¹) * v := by group
        _ = u * v := by rw [h]
    · rintro ⟨-, h⟩
      calc (v : G) * u * (v : G)⁻¹ = u * v * (v : G)⁻¹ := by rw [h]
        _ = u := by group
  have hrange : f.range ≤ C := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(f v).2, ?_⟩
    have hp : u * (v : G) * u⁻¹ ∈ V := conj_mem hu v.2
    have hu1 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
    have hz : u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹ = (v : G) * u * (v : G)⁻¹ * u⁻¹ := by
      have e1 : u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹ = (u * (v : G) * u⁻¹) * (v : G)⁻¹ := by
        calc u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹
            = u * v * u * (v : G)⁻¹ * (u⁻¹ * u⁻¹) := by group
          _ = u * v * u * (v : G)⁻¹ := by rw [hu1, mul_one]
          _ = (u * v * u⁻¹) * (u * u) * (v : G)⁻¹ := by group
          _ = (u * (v : G) * u⁻¹) * (v : G)⁻¹ := by rw [hu2, mul_one]
      have e2 : (v : G) * u * (v : G)⁻¹ * u⁻¹ = (v : G) * (u * (v : G) * u⁻¹)⁻¹ := by group
      rw [e1, e2, hinv _ v.2, hinv _ hp]
      exact hcomm _ hp _ v.2
    show (f v : G) * u = u * (f v : G)
    have hfv : (f v : G) = (v : G) * u * (v : G)⁻¹ * u⁻¹ := rfl
    rw [hfv]
    calc ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u
        = (u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹) * u := by rw [hz]
      _ = u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) := by group
  have hcardC : Nat.card C = Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hker] at hmul
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hle : Nat.card C ≤ Nat.card f.range := by
    have h1 : Nat.card C * Nat.card C ≤ Nat.card C * Nat.card f.range := by
      rw [hmul, ← pow_two, hcardC]
      have : Nat.card ↥V = Nat.card V := rfl
      exact hcard
    exact Nat.le_of_mul_le_mul_left h1 hCpos
  have heq : f.range = C := Subgroup.eq_of_le_of_card_ge hrange hle
  intro x hx
  have hxC : (⟨x, hx.1⟩ : ↥V) ∈ C := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  rw [← heq] at hxC
  obtain ⟨v, hv⟩ := hxC
  exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩

end CFSG.Quasithin.H13.GM22
