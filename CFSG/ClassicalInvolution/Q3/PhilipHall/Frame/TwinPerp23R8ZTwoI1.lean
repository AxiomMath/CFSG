module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Pkg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance


section ZTwoI1

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem i1In_of_zTwo (hc : P23Cfg n Y R S t K' W u e g) {y : Y}
    (hyt : y * t = t * y) (hye : y * e = e * y) (hyy : y * y = 1)
    (hyl : ∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    (hρ : ∃ ρ : ↥(Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e) →* Equiv.Perm (Fin 6),
      Function.Surjective ρ ∧ ρ.ker ≤ (rLayer (Om R) e).subgroupOf
        (Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e)) :
    I1In R t e (Subgroup.closure ({e, t, y} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hJC : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hz
  have hJ'C : K' ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hz'
  have hLC : tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) := sup_le hJC hJ'C
  have htC : t ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
    Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab e (T7K.e_mem_inf hd).1 t hd.hzW)
  have hebar : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ ∈ p23ABar t 1 e :=
    Subgroup.subset_closure ⟨⟨e, heC⟩, ⟨1, one_mem _, by simp⟩, rfl⟩
  have hbar := ABar_cent_twins hc _ hebar
  have hgen : ∀ x ∈ ({e, t, y} : Set Y), x ∈ Subgroup.centralizer ({t} : Set Y) ∧
      ∀ l ∈ tightCore R ⊔ K',
        x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
    intro x hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact ⟨heC, fun l hl => comm_clause_of_bar hJC hJ'C heC hbar.1 hbar.2 l hl⟩
    · rw [hx]
      refine ⟨htC, fun l hl => ?_⟩
      have h1 : t * l * t⁻¹ * l⁻¹ = 1 := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)]
        group
      rw [h1]
      exact one_mem _
    · rw [hx]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyt, fun l hl => hyl l hl⟩
  have hcl : ∀ x ∈ Subgroup.closure ({e, t, y} : Set Y), x ∈ Subgroup.centralizer ({t} : Set Y) ∧
      ∀ l ∈ tightCore R ⊔ K',
        x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact ⟨one_mem _, fun l _ => by simp⟩
    | mul x z _ _ hxC hzC =>
      refine ⟨mul_mem hxC.1 hzC.1, fun l hl => ?_⟩
      have key : x * z * l * (x * z)⁻¹ * l⁻¹ =
          x * (z * l * z⁻¹ * l⁻¹) * x⁻¹ * (x * l * x⁻¹ * l⁻¹) := by group
      rw [key]
      exact mul_mem
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hxC.1 (hzC.2 l hl)) (hxC.2 l hl)
    | inv x _ hxC =>
      refine ⟨inv_mem hxC.1, fun l hl => ?_⟩
      have key : x⁻¹ * l * x⁻¹⁻¹ * l⁻¹ = x⁻¹ * (x * l * x⁻¹ * l⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [key]
      exact CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
        (inv_mem hxC.1) (inv_mem (hxC.2 l hl))
  have hpair : ∀ a ∈ ({e, t, y} : Set Y), ∀ b ∈ ({e, t, y} : Set Y), a * b = b * a := by
    have hc1 : e * t = t * e := Subgroup.mem_centralizer_singleton_iff.mp heC
    intro a ha b hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
    · rw [ha, hb]
    · rw [ha, hb]; exact hc1
    · rw [ha, hb]; exact hye.symm
    · rw [ha, hb]; exact hc1.symm
    · rw [ha, hb]
    · rw [ha, hb]; exact hyt.symm
    · rw [ha, hb]; exact hye
    · rw [ha, hb]; exact hyt
    · rw [ha, hb]
  have hSC : ({e, t, y} : Set Y) ⊆ (Subgroup.centralizer ({e, t, y} : Set Y) : Set Y) :=
    fun s hs => Subgroup.mem_centralizer_iff.mpr fun h hh => hpair h hh s hs
  have hcomm : ∀ a ∈ Subgroup.closure ({e, t, y} : Set Y),
      ∀ b ∈ Subgroup.closure ({e, t, y} : Set Y), a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer ({e, t, y} : Set Y) :=
      ((Subgroup.closure_le _).mpr hSC) hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.closure_le_centralizer_centralizer ({e, t, y} : Set Y) ha) b hb').symm
  have hsq : ∀ x ∈ Subgroup.closure ({e, t, y} : Set Y), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx | hx
      · rw [hx]; exact hd.he2
      · rw [hx]; exact hz.sq
      · rw [hx]; exact hyy
    | one => exact mul_one 1
    | mul x z hxm hzm ihx ihz =>
      have hzx : z * x = x * z := hcomm z hzm x hxm
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [hzx]
        _ = x * x * (z * z) := by group
        _ = 1 := by rw [ihx, ihz, one_mul]
    | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]
  have hZel : ∀ x ∈ Subgroup.closure ({e, t, y} : Set Y),
      ∀ z ∈ Subgroup.closure ({e, t, y} : Set Y), x * z = z * x ∧ x * x = 1 :=
    fun x hx z hz => ⟨hcomm x hx z hz, hsq x hx⟩
  have hcl_le : Subgroup.closure ({e, t, y} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) :=
    fun x hx => (hcl x hx).1
  refine ⟨hcl_le, Subgroup.subset_closure (Set.mem_insert e _), hd.he1, hZel, hρ, ?_⟩
  exact ⟨tightCore R, K', (p23_twin_tq hc).1, (p23_twin_tq hc).2, hc.std.hne, hz, hz',
    fun x hx l hl => (hcl x hx).2 l hl⟩

theorem exists_i1In_of_zTwo (hZ2 : P23E8ZTwo n) :
    CIT3Below n → TL4.TightBelowRPlus 3 n →
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
      (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
        u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 → ∃ Z : Subgroup Y, I1In R t e Z := by
  intro h1 h2 Y _ _ R S t K' W u e g hc hno hu hae
  obtain ⟨y, hyt, hye, hyy, hyl, hρ⟩ := hZ2 h1 h2 Y R S t K' W u e g hc hno hu hae
  exact ⟨_, i1In_of_zTwo hc hyt hye hyy hyl hρ⟩

end ZTwoI1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
