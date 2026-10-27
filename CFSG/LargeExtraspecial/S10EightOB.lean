module

public import CFSG.LargeExtraspecial.S10EightOA
public import CFSG.LargeExtraspecial.S10EightG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem inv_of_frame (hCE : CentralExtInput.{u}) {F : Frame X} (hFY : (D.dec.piY F).range = Γ₂)
    {y : S.O} (hyY : y ∈ Yb) (hyL : y ∈ S.Lbar g) (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂)
    {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆) : y * d * y⁻¹ = d⁻¹ := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, mul_inv_cancel, inv_one]
  obtain ⟨h1, h3, -⟩ := D.dec.pi_spec hCE hFY hd hd1
  have hdY : d ∈ Yb := (D.dec.mem_commutator_iff.mp hd).1
  have key : D.dec.piY F (⟨y, hyY⟩ * ⟨d, hdY⟩ * (⟨y, hyY⟩ : Yb)⁻¹) =
      D.dec.piY F (⟨d, hdY⟩ : Yb)⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, DirDec.piY_apply, DirDec.piY_apply]
    have hy : F.π ⟨y, D.dec.le_Rbar_right hyY⟩ = τ₂ := hπy
    rw [hy]
    exact τ₂_inv _ h1 h3
  have := D.dec.piY_injective hCE F key
  exact congrArg Subtype.val this

theorem conj_not_mem_Vt (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {F : Frame X}
    (hFY : (D.dec.piY F).range = Γ₂) {y : S.O} (hyY : y ∈ Yb) (hyL : y ∈ S.Lbar g)
    (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂) {k : S.M}
    (hkN : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (hτA : τ ∈ S.Lbar g ⊓ Nbar S g t) (hτt : τ ≠ t)
    {e : Vt S g t}
    (he : ∀ γ : Gm, γ.1 = 1 → ∀ a b : ZMod 2, F.φ e ≠ a • E00 + b • act γ E00) :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e ∉ Vt S g t := by
  intro hmem
  have haQ := X.haQ
  have Y : Hyp10 S g τ := X.conj' hkN hτ
  have hτE : τ ∈ S.Lbar g ⊓ Xb := ⟨hτA.1, D.dec.Nbar_le hCE X hτA.2⟩
  have htE : t ∈ S.Lbar g ⊓ Xb := D.t_mem_Ebar hCE
  have hkY : ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
    refine D.map_commutator_eq hCE hP hτE Y.ht1 ?_
    rw [mem_map_cK_iff, hτ]
    have e1 : (S.ρ k)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * S.ρ k = t := by group
    rw [e1]
    exact htE
  obtain ⟨kd, hkdY, hkd1, -, -, -⟩ := D.exists_d hCE
  obtain ⟨hdYb, hd3⟩ := D.dec.mem_commutator_iff.mp hkdY
  have hinv := D.inv_of_frame hCE hFY hyY hyL hπy hkdY
  have hcardY := D.dec.card_commutator
  have hzp : zpowers (S.ρ kd) = ⁅Yb, Yb⁆ := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hkdY) ?_
    rw [hcardY, Nat.card_zpowers, orderOf_eq_prime hd3 hkd1]
  have hfpf : ∀ v : S.Qt, ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := by
    intro v hv
    refine timmesfeld_10_3_alpha hCE X D.dec (fun y' hy' => ?_)
    have hst : S.ρ kd ∈ vecStab S v := mem_vecStab.mpr hv
    rw [← hzp] at hy'
    exact mem_vecStab.mp ((zpowers_le.mpr hst) hy')
  have hinvU : ∀ x ∈ Yb, ∀ v ∈ Vt S g t ⊓ Vt S g τ,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t ⊓ Vt S g τ := by
    intro x hx v hv
    obtain ⟨m, rfl⟩ := D.exists_ρ_of_mem_Yb hx
    have hmt : S.ρ m * t = t * S.ρ m := (D.dec.comm t htE.2 _ hx).symm
    have hmτ : S.ρ m * τ = τ * S.ρ m := (D.dec.comm τ hτE.2 _ hx).symm
    exact ⟨apply_mem_Vt haQ hmt hv.1, apply_mem_Vt haQ hmτ hv.2⟩
  have hD3 : ∀ v, ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
        v := by
    intro v
    have h1 : S.ρ kd * S.ρ kd * S.ρ kd = 1 := by rw [← pow_three', hd3]
    calc _ = ((S.ρ kd * S.ρ kd * S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl
      _ = v := by rw [h1]; rfl
  have hyy : y * y = 1 := S4.mul_self_of_mem_Lbar S haQ hyL
  have hT2 : ∀ v, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
    intro v
    calc _ = ((y * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl
      _ = v := by rw [hyy]; rfl
  have hTD : ∀ v, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) := by
    intro v
    have h1 : y * S.ρ kd = S.ρ kd * S.ρ kd * y := by
      have hdd : (S.ρ kd)⁻¹ = S.ρ kd * S.ρ kd := by
        rw [inv_eq_iff_mul_eq_one, ← pow_three, hd3]
      calc y * S.ρ kd = y * S.ρ kd * y⁻¹ * y := by group
        _ = S.ρ kd * S.ρ kd * y := by rw [hinv, hdd]
    have h2 := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h1
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using h2
  obtain ⟨-, hdim⟩ := half_dim ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap hD3 hT2 hTD (Vt S g t ⊓ Vt S g τ)
    (fun v hv => hinvU _ hdYb v hv) (fun v hv => hinvU _ hyY v hv)
    (fun v _ hv => hfpf v hv)
  have hav : S.cl (g * S.z * g⁻¹) ∈ Vt S g t ⊓ Vt S g τ := ⟨cl_a_mem_Vt X.ht, cl_a_mem_Vt Y.ht⟩
  have hdav := hinvU _ hdYb _ hav
  have hekτ : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e ∈ Vt S g t ⊓ Vt S g τ := by
    refine Submodule.mem_inf.mpr ⟨hmem, ?_⟩
    rw [mem_Vt_conj' haQ hτ, inv_apply_apply_O]
    exact e.2
  have ha0 : S.cl (g * S.z * g⁻¹) ≠ 0 := fun h => aV_ne_zero X.H X.ht (Subtype.ext h)
  have hne : ∀ a b : ZMod 2, ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e ≠
      a • S.cl (g * S.z * g⁻¹) + b • ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (g * S.z * g⁻¹)) := by
    intro a b hab
    have hd'Y : (S.ρ k)⁻¹ * S.ρ kd * S.ρ k ∈ ⁅Yb, Yb⁆ := by
      rw [← hkY] at hkdY
      exact (mem_map_cK_iff k).mp hkdY
    have hd'R : (S.ρ k)⁻¹ * S.ρ kd * S.ρ k ∈ Rbar S g t :=
      D.dec.le_Rbar_right (D.dec.mem_commutator_iff.mp hd'Y).1
    have hfixk : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      conv_lhs => rw [← fix_cl_of_mem_normalizer X.H hkN]
      exact inv_apply_apply_O _ _
    have he' : (e : S.Qt) = a • S.cl (g * S.z * g⁻¹) + b •
        (((S.ρ k)⁻¹ * S.ρ kd * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
      have h1 := congrArg (fun v => (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hab
      simp only [inv_apply_apply_O, map_add, map_smul] at h1
      rw [h1, hfixk]
      congr 2
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
      rw [fix_cl_of_mem_normalizer X.H hkN]
    have heV : e = a • aV X.ht + b • resV X.haQ t ⟨_, hd'R⟩ (aV X.ht) := by
      apply Subtype.ext
      rw [he']
      rfl
    have hφ : F.φ e = a • E00 + b • act (F.π ⟨_, hd'R⟩) E00 := by
      rw [heV, map_add, map_smul, map_smul, F.compat, F.base]
    have hd'1 : (S.ρ k)⁻¹ * S.ρ kd * S.ρ k ≠ 1 := by
      intro h
      apply hkd1
      calc S.ρ kd = S.ρ k * ((S.ρ k)⁻¹ * S.ρ kd * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨hγ1, -, -⟩ := D.dec.pi_spec hCE hFY hd'Y hd'1
    exact he _ hγ1 a b hφ
  have hind : ∀ a b c : ZMod 2, a • S.cl (g * S.z * g⁻¹) +
      b • ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
        c • ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c h
    have hda : ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
        S.cl (g * S.z * g⁻¹) := fun h' => ha0 (hfpf _ h')
    have hd0 : ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ 0 := by
      intro h'
      apply ha0
      have := congrArg (fun v => (((S.ρ kd)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h'
      simpa only [inv_apply_apply_O, map_zero] using this
    rcases zmod2_cases c with rfl | rfl
    · rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
      · exact ⟨rfl, rfl, rfl⟩
      · exact absurd (by simpa using h) hd0
      · exact absurd (by simpa using h) ha0
      · refine absurd ?_ hda
        have h' : S.cl (g * S.z * g⁻¹) + ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl (g * S.z * g⁻¹)) = 0 := by simpa using h
        rw [← ZModModule.sub_eq_add, sub_eq_zero] at h'
        exact h'.symm
    · exfalso
      have h' : a • S.cl (g * S.z * g⁻¹) + b • ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl (g * S.z * g⁻¹)) + ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e = 0 := by
        simpa using h
      rw [← ZModModule.sub_eq_add, sub_eq_zero] at h'
      exact hne a b h'.symm
  have hsum : ∀ f : Fin 3 → ZMod 2, ∑ i, f i • ![S.cl (g * S.z * g⁻¹),
      ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)),
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e] i = f 0 • S.cl (g * S.z * g⁻¹) +
        f 1 • ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          f 2 • ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e := by
    intro f
    rw [Fin.sum_univ_three]
    rfl
  have hli : LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹),
      ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)),
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    rw [hsum] at hf
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ hf
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hspan : Submodule.span (ZMod 2) (Set.range ![S.cl (g * S.z * g⁻¹),
      ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)),
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e]) ≤ Vt S g t ⊓ Vt S g τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hav
    · exact hdav
    · exact hekτ
  have h3 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h3
  have h4 : finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) ≤ 4 :=
    X.h4 ▸ Submodule.finrank_mono inf_le_left
  have hU : finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) = finrank (ZMod 2) (Vt S g t) := by
    rw [X.h4]
    omega
  have hUt := Submodule.eq_of_le_of_finrank_eq inf_le_left hU
  have hle : Vt S g t ≤ Vt S g τ := hUt ▸ inf_le_right
  have hVeq := Submodule.eq_of_le_of_finrank_eq hle (by rw [X.h4, Y.h4])
  exact Vt_ne_of_ne X Y hτt hVeq.symm

end Dec108

end CFSG.LargeExtraspecial.S10
