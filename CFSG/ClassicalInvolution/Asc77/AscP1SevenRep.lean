module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenAct

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

structure Rep (Ω : Set (Subgroup G)) (W : Subgroup G) where
  K : Subgroup G
  R : Subgroup G
  r : G
  hK : K ∈ Ω
  hR : R ∈ DSet Ω W
  hRK : IsSylow2In R K
  hr : r ∈ R
  hrW : r ∉ W

@[expose] noncomputable def Rep.img (ρ : Rep Ω W) : NQuot (W ⊔ OCW W) := piG W ρ.r

omit [Finite G] in
theorem Rep.r_mem_normalizer (ρ : Rep Ω W) : ρ.r ∈ Subgroup.normalizer (W : Set G) :=
  ρ.hR.2 ρ.hr

structure Ctx (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop where
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : HypOmegaMod p f Ω
  hW : W ∈ WSet Ω
  hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W
  hA : ∀ K ∈ Ω, AEmpty Ω K

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem comm_W : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := commutes_of_mem_WSet c.hp c.hq c.hΩ c.hW

theorem img_eq_of_K_eq (ρ σ : Rep Ω W) (h : ρ.K = σ.K) : ρ.img = σ.img := by
  have hle : σ.R ≤ ρ.R ⊔ W ⊔ OCW W :=
    c.hkey ρ.R ρ.hR σ.R σ.hR ρ.K ρ.hK ρ.hRK.1 (h ▸ σ.hRK.1)
  exact (piG_eq_of_le_sup c.hp c.hq c.hΩ c.hW ρ.hR σ.hR hle ρ.hr σ.hr ρ.hrW σ.hrW).symm

theorem K_eq_of_img_eq (ρ σ : Rep Ω W) (h : ρ.img = σ.img) : ρ.K = σ.K :=
  eq_of_piG_eq (l6_2 p f) c.hp c.hq c.hΩ c.hW ρ.hK σ.hK ρ.hR σ.hR ρ.hRK σ.hRK ρ.hr σ.hr σ.hrW h

theorem noncomm (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) :
    ρ.img * σ.img ≠ σ.img * ρ.img :=
  not_comm_of_not_mem_omegaNbr (l6_2 p f) c.hp c.hq c.hΩ c.hW c.hkey (c.hA ρ.K ρ.hK) ρ.hK σ.hK hne
    ρ.hR σ.hR ρ.hRK σ.hRK hnot ρ.hr σ.hr ρ.hrW σ.hrW

theorem omega_of_comm (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hcomm : ρ.img * σ.img = σ.img * ρ.img) : σ.K ∈ omegaNbr Ω ρ.K := by
  by_contra hnot
  exact c.noncomm ρ σ hne hnot hcomm

theorem comm_of_omega (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K) :
    ρ.img * σ.img = σ.img * ρ.img :=
  piG_comm_of_mem_omegaNbr (l6_2 p f) c.hp c.hq c.hΩ c.hW c.hkey ρ.hK σ.hK hnbr.2.1.symm ρ.hR σ.hR
    ρ.hRK σ.hRK hnbr ρ.hr σ.hr ρ.hrW

theorem centralizes (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : v ∈ σ.K ⊓ W) :
    ρ.r * v = v * ρ.r :=
  centralizes_inf_W_of_mem_omegaNbr (l6_2 p f) c.hp c.hq c.hΩ c.hW ρ.hK σ.hK hnbr.2.1.symm ρ.hR
    σ.hR ρ.hRK σ.hRK hnbr ρ.hr hv

theorem conj_inv (ρ : Rep Ω W) {u : G} (hu : u ∈ ρ.K ⊓ W) : ρ.r * u * ρ.r⁻¹ = u⁻¹ :=
  conj_eq_inv_of_mem_inf_W c.hp c.hq c.hΩ c.hW ρ.hK ρ.hR ρ.hRK ρ.hr ρ.hrW hu

theorem comm_mem (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) {v : G} (hv : v ∈ σ.K ⊓ W) :
    ρ.r * v * ρ.r⁻¹ * v⁻¹ ∈ ρ.K ⊓ W :=
  comm_mem_inf_W c.hp c.hq c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK ρ.hr hv

theorem conj_involution (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z j : G}
    (hz : IsUniqueInvolution ρ.K z) (hj : IsUniqueInvolution σ.K j) :
    ρ.r * j * ρ.r⁻¹ = z * j :=
  conj_involution_eq_mul (l6_2 p f) c.hp c.hq c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK hnot
    hz hj ρ.hr ρ.hrW

@[expose] def W4 : Subgroup G where
  carrier := {x | x ∈ W ∧ x ^ 4 = 1}
  one_mem' := ⟨W.one_mem, one_pow 4⟩
  mul_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    refine ⟨W.mul_mem hxW hyW, ?_⟩
    rw [(show Commute x y from c.comm_W x hxW y hyW).mul_pow, hx, hy, one_mul]
  inv_mem' := by
    rintro x ⟨hxW, hx⟩
    refine ⟨W.inv_mem hxW, ?_⟩
    rw [inv_pow, hx, inv_one]

theorem mem_W4 {x : G} : x ∈ c.W4 ↔ x ∈ W ∧ x ^ 4 = 1 := Iff.rfl

theorem W4_le : c.W4 ≤ W := fun _ hx => hx.1

theorem conj_mem_W4 {r : G} (hr : r ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ c.W4) :
    r * x * r⁻¹ ∈ c.W4 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hr x).mp hx.1, ?_⟩
  rw [conj_pow, hx.2]
  group

end Ctx

omit [Finite G] in
theorem exists_mem_closure_of_mem_closure_piG {L : Set G}
    (hL : L ⊆ Subgroup.normalizer (W : Set G)) {q : NQuot (W ⊔ OCW W)}
    (hq : q ∈ Subgroup.closure (piG W '' L)) : ∃ g ∈ Subgroup.closure L, piG W g = q := by
  have hcl : Subgroup.closure L ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.closure_le _).mpr hL
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, Subgroup.subset_closure hy, rfl⟩
  | one => exact ⟨1, Subgroup.one_mem _, by rw [piG_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', rfl⟩ := hy
    exact ⟨g * g', Subgroup.mul_mem _ hg hg', piG_mul (hcl hg) (hcl hg')⟩
  | inv x _ hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g⁻¹, Subgroup.inv_mem _ hg, piG_inv (hcl hg)⟩

end Thompson

end CFSG.ClassicalInvolution.Asc77
