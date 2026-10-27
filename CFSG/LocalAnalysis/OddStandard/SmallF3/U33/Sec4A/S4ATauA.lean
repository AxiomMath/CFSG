module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameExtras
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {K : Type} [Group K]

theorem aut_mul_conj_mul_inv (α : MulAut K) (x : K) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

theorem baseGrp_comm {x₁ x₂ lam : K} (h : WreathRel x₁ x₂ lam) {u v : K}
    (hu : u ∈ baseGrp x₁ x₂) (hv : v ∈ baseGrp x₁ x₂) : u * v = v * u := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := h.baseGrp_eq.1
  exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : baseGrp x₁ x₂) ⟨v, hv⟩)

theorem wr_lam_sq {x₁ x₂ lam : K} (h : WreathRel x₁ x₂ lam) : lam * lam = 1 := by
  have := pow_orderOf_eq_one lam
  rw [h.ord_lam, pow_two] at this
  exact this

theorem wr_lam_conj_x₂ {x₁ x₂ lam : K} (h : WreathRel x₁ x₂ lam) :
    lam * x₂ * lam⁻¹ = x₁ := by
  calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.conj_x₁]
    _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
    _ = x₁ := by rw [wr_lam_sq h]; group

theorem conj_mem_baseGrp_of_gens {a b g : K} (h1 : g * a * g⁻¹ ∈ baseGrp a b)
    (h2 : g * b * g⁻¹ ∈ baseGrp a b) : ∀ w ∈ baseGrp a b, g * w * g⁻¹ ∈ baseGrp a b := by
  intro w hw
  have hle : baseGrp a b ≤ (baseGrp a b).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le (K := (baseGrp a b).comap (MulAut.conj g).toMonoidHom)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      show g * a * g⁻¹ ∈ baseGrp a b
      exact h1
    · rw [hx]
      show g * b * g⁻¹ ∈ baseGrp a b
      exact h2
  exact Subgroup.mem_comap.mp (hle hw)

theorem alpha_inv_of_mem_baseGrp {x₁ x₂ lam : K} (h : WreathRel x₁ x₂ lam) {α : MulAut K}
    (h1 : α x₁ = x₁⁻¹) (h2 : α x₂ = x₂⁻¹) {w : K} (hw : w ∈ baseGrp x₁ x₂) : α w = w⁻¹ := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact h1
    · rw [hx]
      exact h2
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [map_mul, ihx, ihy, mul_inv_rev]
    exact baseGrp_comm h (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hy)
  | inv x hx ih => rw [map_inv, ih]

section Frame

variable [Finite K] {x₁ x₂ lam rho : K} {α : MulAut K}

theorem closure_acts_trivially (hf : U33Frame x₁ x₂ lam rho α) :
    ∀ n ∈ closure {x₁, x₂, rho, lam},
      n ∈ normalizer ((baseGrp x₁ x₂ : Subgroup K) : Set K) ∧ n⁻¹ * α n ∈ baseGrp x₁ x₂ := by
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      refine ⟨Subgroup.le_normalizer hx₁B, ?_⟩
      rw [hf.alpha_x₁]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₁B) (Subgroup.inv_mem _ hx₁B)
    · rw [hg]
      refine ⟨Subgroup.le_normalizer hx₂B, ?_⟩
      rw [hf.alpha_x₂]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂B) (Subgroup.inv_mem _ hx₂B)
    · rw [hg]
      refine ⟨mem_normalizer_of_conj_mem (conj_mem_baseGrp_of_gens ?_ ?_), ?_⟩
      · rw [hf.rho_x₁]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₁B) hx₂B
      · rw [hf.rho_x₂]
        exact Subgroup.inv_mem _ hx₁B
      · rw [hf.alpha_rho, inv_mul_cancel]
        exact Subgroup.one_mem _
    · rw [hg]
      refine ⟨mem_normalizer_of_conj_mem (conj_mem_baseGrp_of_gens ?_ ?_), ?_⟩
      · rw [hf.wreath.conj_x₁]
        exact hx₂B
      · rw [wr_lam_conj_x₂ hf.wreath]
        exact hx₁B
      · rw [hf.alpha_lam, inv_mul_cancel]
        exact Subgroup.one_mem _
  | one => simp
  | mul g g' _ _ ih ih' =>
    refine ⟨Subgroup.mul_mem _ ih.1 ih'.1, ?_⟩
    have h1 : g'⁻¹ * (g⁻¹ * α g) * g' ∈ baseGrp x₁ x₂ :=
      (Subgroup.mem_normalizer_iff''.mp ih'.1 _).mp ih.2
    have h2 := Subgroup.mul_mem _ h1 ih'.2
    have e : (g * g')⁻¹ * α (g * g') = g'⁻¹ * (g⁻¹ * α g) * g' * (g'⁻¹ * α g') := by
      rw [map_mul]
      group
    rw [e]
    exact h2
  | inv g _ ih =>
    refine ⟨Subgroup.inv_mem _ ih.1, ?_⟩
    have h1 : g * (g⁻¹ * α g)⁻¹ * g⁻¹ ∈ baseGrp x₁ x₂ :=
      (Subgroup.mem_normalizer_iff.mp ih.1 _).mp (Subgroup.inv_mem _ ih.2)
    have e : (g⁻¹)⁻¹ * α g⁻¹ = g * (g⁻¹ * α g)⁻¹ * g⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    exact h1

theorem tau_acts_trivially (hf : U33Frame x₁ x₂ lam rho α) (he : U33FrameExtras x₁ x₂ lam rho α)
    {n : K} (hn : ∀ w ∈ baseGrp x₁ x₂, n * w * n⁻¹ ∈ baseGrp x₁ x₂) :
    n⁻¹ * α n ∈ baseGrp x₁ x₂ :=
  (closure_acts_trivially hf n (he.norm_base n hn)).2

end Frame

theorem exists_adjust [Finite K] {B : Subgroup K} {r : K} (hrB : ∀ w ∈ B, r * w * r⁻¹ ∈ B)
    (hrC : ∀ w ∈ B, r * w = w * r → w = 1) {b : K} (hb : b ∈ B) :
    ∃ c ∈ B, (r⁻¹ * c * r)⁻¹ * c = b := by
  have hrN : r ∈ normalizer (B : Set K) := mem_normalizer_of_conj_mem hrB
  have hrB' : ∀ w ∈ B, r⁻¹ * w * r ∈ B := fun w hw =>
    (Subgroup.mem_normalizer_iff''.mp hrN w).mp hw
  let f : ↥B → ↥B := fun c =>
    ⟨(r⁻¹ * (c : K) * r)⁻¹ * (c : K), B.mul_mem (B.inv_mem (hrB' c c.2)) c.2⟩
  have hinj : Function.Injective f := by
    intro c d hcd
    have h1 : (r⁻¹ * (c : K) * r)⁻¹ * (c : K) = (r⁻¹ * (d : K) * r)⁻¹ * (d : K) :=
      congrArg Subtype.val hcd
    have h1' : r⁻¹ * (c : K)⁻¹ * r * (c : K) = r⁻¹ * (d : K)⁻¹ * r * (d : K) := by
      calc r⁻¹ * (c : K)⁻¹ * r * (c : K) = (r⁻¹ * (c : K) * r)⁻¹ * (c : K) := by group
        _ = (r⁻¹ * (d : K) * r)⁻¹ * (d : K) := h1
        _ = r⁻¹ * (d : K)⁻¹ * r * (d : K) := by group
    have h3 : (c : K)⁻¹ * r * (c : K) = (d : K)⁻¹ * r * (d : K) := by
      refine mul_left_cancel (a := r⁻¹) ?_
      calc r⁻¹ * ((c : K)⁻¹ * r * (c : K)) = r⁻¹ * (c : K)⁻¹ * r * (c : K) := by group
        _ = r⁻¹ * (d : K)⁻¹ * r * (d : K) := h1'
        _ = r⁻¹ * ((d : K)⁻¹ * r * (d : K)) := by group
    have he : (c : K) * (d : K)⁻¹ ∈ B := B.mul_mem c.2 (B.inv_mem d.2)
    have hcomm : r * ((c : K) * (d : K)⁻¹) = ((c : K) * (d : K)⁻¹) * r := by
      calc r * ((c : K) * (d : K)⁻¹) = (c : K) * ((c : K)⁻¹ * r * (c : K)) * (d : K)⁻¹ := by
            group
        _ = (c : K) * ((d : K)⁻¹ * r * (d : K)) * (d : K)⁻¹ := by rw [h3]
        _ = ((c : K) * (d : K)⁻¹) * r := by group
    exact Subtype.ext (mul_inv_eq_one.mp (hrC _ he hcomm))
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.mp hinj ⟨b, hb⟩
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
