module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSTwo
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1C

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_commutator_of_mem_normalizer {H : Subgroup G} {n x : G}
    (hn : n ∈ normalizer (H : Set G)) (hx : x ∈ ⁅H, H⁆) : n * x * n⁻¹ ∈ ⁅H, H⁆ := by
  have hle : ⁅H, H⁆ ≤ (⁅H, H⁆ : Subgroup G).comap (MulAut.conj n).toMonoidHom := by
    rw [commutator_le]
    intro g hg h hh
    change n * ⁅g, h⁆ * n⁻¹ ∈ ⁅H, H⁆
    rw [show n * ⁅g, h⁆ * n⁻¹ = ⁅n * g * n⁻¹, n * h * n⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hn g).1 hg)
      ((mem_normalizer_iff.1 hn h).1 hh)
  exact hle hx

theorem conj_mem_inf_centralizer_of_mem_normalizer {H : Subgroup G} {n x : G}
    (hn : n ∈ normalizer (H : Set G)) (hx : x ∈ H ⊓ centralizer (H : Set G)) :
    n * x * n⁻¹ ∈ H ⊓ centralizer (H : Set G) := by
  obtain ⟨hxH, hxC⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hn x).1 hxH, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ H := by
    have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
    rwa [inv_inv] at this
  have hc := mem_centralizer_iff.1 hxC _ hy'
  calc y * (n * x * n⁻¹) = n * (n⁻¹ * y * n * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
    _ = n * x * n⁻¹ * y := by group

theorem entry_commutator_eq_zero_of_add {H : Subgroup G} {e : G → F4}
    (hadd : ∀ {g h : G}, g ∈ H → h ∈ H → e (g * h) = e g + e h)
    {g h : G} (hg : g ∈ H) (hh : h ∈ H) : e ⁅g, h⁆ = 0 := by
  have h0 : e 1 = 0 := by
    have := hadd (one_mem H) (one_mem H)
    rw [one_mul] at this
    linear_combination -this
  have hinv : ∀ {x : G}, x ∈ H → e x⁻¹ = - e x := fun {x} hx => by
    have h1 := hadd hx (inv_mem hx)
    rw [mul_inv_cancel, h0] at h1
    linear_combination -h1
  rw [commutatorElement_def, hadd (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    hadd (mul_mem hg hh) (inv_mem hg), hadd hg hh, hinv hg, hinv hh]
  ring

end Generic

theorem mat_three_two {g : SU52} (hg : g ∈ Ssub) : mat g 3 2 = bar (mat g 2 1) := by
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, -, -⟩ :=
    exists_eq_nf_coord hg
  rw [k₁, mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄]
  simp [x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem mat_mul_three_zero {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) :
    mat (g * h) 3 0 = mat g 3 0 + mat g 3 1 * mat h 1 0 + mat g 3 2 * mat h 2 0 + mat h 3 0 := by
  obtain ⟨g1, g2⟩ := mem_Ssub.1 hg
  obtain ⟨-, h2⟩ := mem_Ssub.1 hh
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, g1 3 4 (by decide), h2 0, g2 3]
  ring

theorem commutator_commutator_Ssub : ⁅⁅Ssub, Ssub⁆, ⁅Ssub, Ssub⁆⁆ = ZX₄sub := by
  have hS' : ∀ {x : SU52}, x ∈ ⁅Ssub, Ssub⁆ → x ∈ Ssub ∧ mat x 2 1 = 0 ∧ mat x 1 0 = 0 :=
    fun {x} hx => by
      rw [commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff] at hx
      exact hx
  have h32 : ∀ {x : SU52}, x ∈ ⁅Ssub, Ssub⁆ → mat x 3 2 = 0 := fun {x} hx => by
    rw [mat_three_two (hS' hx).1, (hS' hx).2.1, map_zero]
  refine le_antisymm (commutator_le.2 fun g hg h hh => ?_) fun z hz => ?_
  · have hc : ⁅g, h⁆ ∈ ⁅Ssub, Ssub⁆ :=
      commutator_mem_commutator (commutator_Ssub_le_Ssub hg) (commutator_Ssub_le_Ssub hh)
    have a20 := entry_commutator_eq_zero_of_add (H := ⁅Ssub, Ssub⁆) (e := fun x => mat x 2 0)
      (fun {x y} hx hy => by
        rw [mat_mul_two_zero (hS' hx).1 (hS' hy).1, (hS' hy).2.2, mul_zero, add_zero]) hg hh
    have a30 := entry_commutator_eq_zero_of_add (H := ⁅Ssub, Ssub⁆) (e := fun x => mat x 3 0)
      (fun {x y} hx hy => by
        rw [mat_mul_three_zero (hS' hx).1 (hS' hy).1, (hS' hy).2.2, h32 hx, mul_zero, zero_mul,
          add_zero, add_zero]) hg hh
    have a31 := entry_commutator_eq_zero_of_add (H := ⁅Ssub, Ssub⁆) (e := fun x => mat x 3 1)
      (fun {x y} hx hy => by
        rw [mat_mul_three_one (hS' hx).1 (hS' hy).1, h32 hx, zero_mul, add_zero]) hg hh
    obtain ⟨hcS, hc21, hc10⟩ := hS' hc
    have hF : ⁅g, h⁆ ∈ Fsub := mem_Fsub.2 ⟨hcS, hc21, hc10, a20⟩
    obtain ⟨⟨b₁, γ, b₄⟩, -, h₄, hm⟩ := exists_fMat_of_mem_Fsub hF
    rw [hm, fMat_eq] at a30 a31
    change γ = 0 at a30
    change b₁ = 0 at a31
    subst a30 a31
    refine mem_x₄Sub.2 ⟨0, b₄, rfl, ?_⟩
    rw [hm, fMat_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [x₄Mat, map_zero]
  · obtain ⟨a, b, ha, hzm⟩ := mem_x₄Sub.1 hz
    subst ha
    rcases eq_zero_or_one_of_valid b (x₄_coord_rel hzm) with rfl | rfl
    · rw [show z = 1 from ext_mat (by rw [hzm, x₄Mat_zero, mat_one])]
      exact one_mem _
    · rw [show z = x₄SU 0 1 zero_one_rel from ext_mat hzm, ← commutator_x₄_x₄_eq]
      exact commutator_mem_commutator (inv_mem (X₄sub_le_commutator_Ssub (x₄SU_mem _ _ _)))
        (inv_mem (X₄sub_le_commutator_Ssub (x₄SU_mem _ _ _)))

theorem commutator_Ssub_inf_centralizer :
    ⁅Ssub, Ssub⁆ ⊓ centralizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) = Fsub := by
  have hFC : Fsub ≤ centralizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) := by
    rw [← Ssub_inf_centralizer_commutator_Ssub]
    exact inf_le_right
  refine le_antisymm (fun x hx => ?_) (le_inf Fsub_le_commutator_Ssub hFC)
  rw [← Ssub_inf_centralizer_commutator_Ssub]
  exact mem_inf.2 ⟨commutator_Ssub_le_Ssub (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩

theorem Ssub_eq_A₁sub_sup_A₂sub : Ssub = A₁sub ⊔ A₂sub := by
  refine le_antisymm ?_ (sup_le A₁sub_le_Ssub A₂sub_le_Ssub)
  rw [Ssub_eq_sup]
  exact sup_le le_sup_right (X₂sub_le_A₁sub.trans le_sup_left)

theorem mem_normalizer_Ssub_of_conj {n : SU52} (h₁ : ∀ a ∈ A₁sub, n * a * n⁻¹ ∈ A₁sub)
    (h₂ : ∀ a ∈ A₂sub, n * a * n⁻¹ ∈ A₂sub) : n ∈ normalizer (Ssub : Set SU52) := by
  have hle : A₁sub ⊔ A₂sub ≤ (A₁sub ⊔ A₂sub).comap (MulAut.conj n).toMonoidHom :=
    sup_le (fun a ha => show n * a * n⁻¹ ∈ A₁sub ⊔ A₂sub from mem_sup_left (h₁ a ha))
      fun a ha => show n * a * n⁻¹ ∈ A₁sub ⊔ A₂sub from mem_sup_right (h₂ a ha)
  refine mem_normalizer_fintype fun x hx => ?_
  rw [Ssub_eq_A₁sub_sup_A₂sub] at hx ⊢
  exact hle hx

theorem normalizer_commutator_Ssub :
    normalizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) = normalizer (Ssub : Set SU52) := by
  refine le_antisymm (fun n hn => ?_) fun n hn =>
    mem_normalizer_fintype fun x hx => normalizer_Ssub_conj_mem_commutator hn hx
  have hz' : zSU ∈ ⁅⁅Ssub, Ssub⁆, ⁅Ssub, Ssub⁆⁆ := by
    rw [commutator_commutator_Ssub]
    exact zSU_mem
  have hz := conj_mem_commutator_of_mem_normalizer hn hz'
  rw [commutator_commutator_Ssub] at hz
  have hcz : n * zSU = zSU * n := comm_zSU_of_mem (mul_mem (inv_mem zSU_mem) hz)
  have hnF : n ∈ normalizer (Fsub : Set SU52) := mem_normalizer_fintype fun f hf => by
    rw [← commutator_Ssub_inf_centralizer] at hf ⊢
    exact conj_mem_inf_centralizer_of_mem_normalizer hn hf
  exact mem_normalizer_Ssub_of_conj (fun a ha => conj_mem_A₁sub_of_comm_z hcz ha)
    fun a ha => conj_mem_A₂sub_of_mem_normalizer hnF ha

theorem normalizer_Ssub_conj_mem_ZX₄sub {n z : SU52} (hn : n ∈ normalizer (Ssub : Set SU52))
    (hz : z ∈ ZX₄sub) : n * z * n⁻¹ ∈ ZX₄sub := by
  rw [← Ssub_inf_centralizer_Ssub] at hz ⊢
  exact conj_mem_inf_centralizer_of_mem_normalizer hn hz

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
