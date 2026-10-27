module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpE

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)
  {Fn : Subgroup (V ≃ₗ[k] V)} (hF : OverGroup G Fn N)

include h F hF

theorem D_le_Fn : natD N A g ≤ Fn := (h.D_le_N F).trans hF.N_le

theorem centralizes_D {f : V ≃ₗ[k] V} (hf : f ∈ Fn) :
    ∀ d ∈ natD N A g, f * d = d * f := by
  intro d hd
  refine Subgroup.iSup_induction (natL N A g) hd (C := fun d => f * d = d * f) ?_ ?_ ?_
  · intro i x hx
    exact h.centralizes_L F hF hf i x hx
  · simp
  · intro x y hx hy
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem C_eq_Fn :
    Fn ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g) =
      Fn ⊓ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V)) := by
  have fd := h.famData F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ext f
  constructor
  · rintro ⟨hfF, hfW⟩
    refine ⟨hfF, ?_⟩
    show f ∈ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V))
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [h.B_eq F] at hb
    refine Subgroup.iSup_induction (natS N A g) hb (C := fun b => b * f = f * b) ?_ (by simp) ?_
    · intro i b' hb'
      have pd := h.planeData_family F i
      obtain ⟨l, hl, a, ha, rfl⟩ := mem_sup_mul pd.A_norm hb'
      have hfl : l * f = f * l := (h.centralizes_L F hF hfF i l hl).symm
      have haS : a ∈ natS N A g i := (le_sup_right : natA A g i ≤ natS N A g i) ha
      have hfa : a * f = f * a := by
        obtain ⟨hSi, -⟩ := h.normalizes_S F hF hfF i
        obtain ⟨hW, -⟩ := h.S_action F i
        have h1 : f * a * f⁻¹ ∈ natS N A g i := hSi ▸ conjSub_mem_of_mem haS
        have h2 : f * a * f⁻¹ = a := by
          refine h.S_ext F i h1 haS (fun w hw => ?_)
          have hwW : w ∈ natW N A g := h.W_le_of F i hw
          have hfw0 : f w = w := hfW w hwW
          have hfw : f⁻¹ w = w := by
            calc f⁻¹ w = f⁻¹ (f w) := by rw [hfw0]
              _ = w := gl_inv_apply f w
          have haw : a w ∈ natW N A g := h.W_le_of F i (hW a haS w hw)
          show f (a (f⁻¹ w)) = a w
          rw [hfw]
          exact hfW _ haw
        exact (mul_inv_eq_iff_eq_mul.1 h2).symm
      calc l * a * f = l * (a * f) := mul_assoc _ _ _
        _ = l * (f * a) := by rw [hfa]
        _ = (l * f) * a := (mul_assoc _ _ _).symm
        _ = (f * l) * a := by rw [hfl]
        _ = f * (l * a) := mul_assoc _ _ _
    · intro x y hx hy
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  · rintro ⟨hfF, hfB⟩
    refine ⟨hfF, ?_⟩
    have hfB' : ∀ b ∈ (natB G N A : Set (V ≃ₗ[k] V)), b * f = f * b :=
      Subgroup.mem_centralizer_iff.1 hfB
    intro w hw
    have hW : natW N A g = ⨆ i, natI N A g i := fd.W_eq
    rw [hW] at hw
    refine fix_iSup_of_fix (x := f) (U := natI N A g) (fun i w' hw' => ?_) w hw
    have pd := h.planeData_family F i
    obtain ⟨l, hl, hlf⟩ := h.acts_via_L F hF hfF i
    obtain ⟨a, ha, ha1⟩ := h.exists_ne_one_A F i
    obtain ⟨hWi, -⟩ := h.S_action F i
    have haS : a ∈ natS N A g i := (le_sup_right : natA A g i ≤ natS N A g i) ha
    have hlS : l ∈ natS N A g i := (le_sup_left : natL N A g i ≤ natS N A g i) hl
    have hfa : f * a = a * f := (hfB' a (h.S_le_B F i haS)).symm
    have hal : l * a = a * l := by
      refine h.S_ext F i ((natS N A g i).mul_mem hlS haS) ((natS N A g i).mul_mem haS hlS)
        (fun w hw => ?_)
      have haw : a w ∈ natI N A g i := hWi a haS w hw
      show l (a w) = a (l w)
      rw [← hlf _ haw, ← hlf w hw]
      exact congrArg (fun e : V ≃ₗ[k] V => e w) hfa
    have hl1 : l = 1 := by
      by_contra hl1
      refine h.not_centralizes_A F i ha ha1 (fun x hx => ?_)
      have hz := mem_zpowers_of_prime_card (g := (⟨l, hl⟩ : ↥(natL N A g i))) pd.card_L
        (fun e => hl1 (congrArg Subtype.val e)) (g' := ⟨x, hx⟩)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hxn : l ^ n = x := by simpa using congrArg Subtype.val hn
      have hc : Commute a l := hal.symm
      rw [← hxn]
      exact (hc.zpow_right n).eq
    rw [hlf w' hw', hl1]
    rfl

theorem N_eq_Fn :
    natD N A g ⊔ (Fn ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) = Fn := by
  refine le_antisymm (sup_le (h.D_le_Fn F hF) inf_le_left) ?_
  intro f hf
  obtain ⟨d, hdD, hd⟩ := h.exists_D_agree F (fun i => h.acts_via_L F hF hf i)
  have e : f = d * (d⁻¹ * f) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hdD) (Subgroup.mem_sup_right ⟨?_, ?_⟩)
  · exact Fn.mul_mem (Fn.inv_mem (h.D_le_Fn F hF hdD)) hf
  · intro w hw
    have hW : natW N A g = ⨆ i, natI N A g i := (h.famData F).W_eq
    rw [hW] at hw
    refine fix_iSup_of_fix (x := d⁻¹ * f) (U := natI N A g) (fun i w' hw' => ?_) w hw
    show d⁻¹ (f w') = w'
    rw [← hd i w' hw']
    exact gl_inv_apply d w'

omit hF in
theorem N_disjoint_Fn :
    Disjoint (natD N A g) (Fn ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) := by
  rw [Subgroup.disjoint_def]
  intro x hxD hxC
  exact (h.famData F).faithful x hxD (fun w hw => hxC.2 w hw)

theorem comm_Fn_eq : ⁅Fn, A⁆ = ⁅N, A⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro f hf a ha
    obtain ⟨d, hdD, hd⟩ := h.exists_D_agree F (fun i => h.acts_via_L F hF hf i)
    have hdF : d ∈ Fn := h.D_le_Fn F hF hdD
    have hcF : d⁻¹ * f ∈ Fn := Fn.mul_mem (Fn.inv_mem hdF) hf
    have hcW : d⁻¹ * f ∈ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g) := by
      intro w hw
      have hW : natW N A g = ⨆ i, natI N A g i := (h.famData F).W_eq
      rw [hW] at hw
      refine fix_iSup_of_fix (x := d⁻¹ * f) (U := natI N A g) (fun i w' hw' => ?_) w hw
      show d⁻¹ (f w') = w'
      rw [← hd i w' hw']
      exact gl_inv_apply d w'
    have hcB : d⁻¹ * f ∈ Fn ⊓ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V)) := by
      rw [← h.C_eq_Fn F hF]
      exact ⟨hcF, hcW⟩
    have haB : a ∈ natB G N A :=
      OddAbelianSetting.LA_le_B ((le_sup_right : A ≤ ⁅N, A⁆ ⊔ A) ha)
    have hcomm : a * (d⁻¹ * f) = (d⁻¹ * f) * a := Subgroup.mem_centralizer_iff.1 hcB.2 a haB
    have hca : (d⁻¹ * f) * a * (d⁻¹ * f)⁻¹ = a := mul_inv_eq_iff_eq_mul.2 hcomm.symm
    have e : ⁅f, a⁆ = ⁅d, a⁆ := by
      have hf' : f = d * (d⁻¹ * f) := by group
      calc ⁅f, a⁆ = ⁅d * (d⁻¹ * f), a⁆ := by rw [← hf']
        _ = d * ((d⁻¹ * f) * a * (d⁻¹ * f)⁻¹) * d⁻¹ * a⁻¹ := by
          simp only [commutatorElement_def]
          group
        _ = ⁅d, a⁆ := by
          rw [hca]
          simp only [commutatorElement_def]
    rw [e]
    exact Subgroup.commutator_mem_commutator (h.D_le_N F hdD) ha
  · exact Subgroup.commutator_mono hF.N_le le_rfl

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
