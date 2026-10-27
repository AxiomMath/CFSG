module

public import CFSG.LargeExtraspecial.S8KJ
public import CFSG.LargeExtraspecial.S7Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem commute_of_commSpace_le {Y : Submodule (ZMod 2) S.Qt} (hY : Y ≤ S2.perp S.q Y)
    {e e' : S.O} (he : commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y)
    (he' : commSpace (e' : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y) : e * e' = e' * e := by
  have hfix : ∀ f : S.O, commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y →
      Y ≤ fixSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun f hf => by
    rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate f.2]
    exact hY.trans (LinearMap.BilinForm.orthogonal_le hf)
  have key : ∀ f f' : S.O, commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y →
      commSpace (f' : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y → ∀ x : S.Qt,
        (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f' : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
          (f : S.Qt ≃ₗ[ZMod 2] S.Qt) x + ((f' : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
    intro f f' hf hf' x
    have h1 : (f' : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Y := hf' (mem_commSpace.mpr ⟨x, rfl⟩)
    have h2 := mem_fixSpace.mp (hfix f hf h1)
    rw [map_sub] at h2
    rw [← h2]
    abel
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e' : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
    (e' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
  rw [key e e' he he' x, key e' e he' he x]
  abel

theorem conj_mem_Lbar_of_cl_mem_commSpace {D : Std H C ht ht1 hVQ} (R : Red4 D) {z : S.O}
    (hzM : z ∈ S.Mbar)
    (hz : S.cl (g * S.z * g⁻¹) ∈ commSpace ((z * t * z⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    z * t * z⁻¹ ∈ S.Lbar g := by
  have haQ := H.conj_mem
  rw [S7.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1] at hz
  obtain ⟨v, hv, hzv⟩ := hz
  have hv' : ((z⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = v := by
    rw [← hzv]
    exact inv_apply_apply_O z v
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (inv_mem hzM)
  have hkv := ρ_cl_conj_z S k haQ
  rw [hk, hv'] at hkv
  rw [hkv] at hv
  obtain ⟨r, hr, hra⟩ := R.hfus k hv
  have hmM : r⁻¹ * z⁻¹ ∈ S.Mbar := mul_mem (inv_mem (Rbar_le_Mbar hr)) (inv_mem hzM)
  have hfix : ((r⁻¹ * z⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹)) =
        S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹) := by
    simp only [OneMemClass.coe_one, one_mul]
    rw [coe_mul_apply, hv', hkv, hra, inv_apply_apply_O]
  have hmN := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hmM hfix
  simp only [OneMemClass.coe_one, one_mul] at hmN
  have h1 := (mem_normalizer_iff.mp (inv_mem hmN) t).mp ht
  have hrt : r * t = t * r := commute_of_mem_Rbar haQ hr
  have e : (r⁻¹ * z⁻¹)⁻¹ * t * (r⁻¹ * z⁻¹)⁻¹⁻¹ = z * t * z⁻¹ := by
    calc (r⁻¹ * z⁻¹)⁻¹ * t * (r⁻¹ * z⁻¹)⁻¹⁻¹ = z * (r * t) * r⁻¹ * z⁻¹ := by group
      _ = z * (t * r) * r⁻¹ * z⁻¹ := by rw [hrt]
      _ = z * t * z⁻¹ := by group
  rwa [e] at h1

theorem conj_mem_conjCentM (ht : t ∈ S.Lbar g) {y : S.O} (hyM : y ∈ S.Mbar)
    (hyt : y * t * y⁻¹ * t = t * (y * t * y⁻¹)) : y * t * y⁻¹ ∈ conjCentM S t :=
  ⟨mul_mem (mul_mem hyM (S.Lbar_le_Mbar g ht)) (inv_mem hyM), hyt, y, hyM, rfl⟩

structure Bad4 (D : Std H C ht ht1 hVQ) (τ : S.O) : Prop where
  red : Red4 D
  mem : τ ∈ conjCentM S t
  not_mem : τ ∉ Nbar S g t

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem N1bar_eq {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    N1bar S g t σ = N1bar S g t τ :=
  B.red.N1bar_eq hσ hσN B.mem B.not_mem

theorem sup_eq {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  B.red.sup_commSpace_eq hσ hσN B.mem B.not_mem

theorem Fbar_le : S9.Fbar S g t ≤ N1bar S g t τ := by
  have := B.red.nqHyp
  intro f hf
  have hfN : f ∈ Nbar S g t := S9.Fbar_le_of_subset (conjL_subset_Nbar B.red.hsub) hf
  have h1 : nqMk ⟨f, hfN⟩ ∈ nqSub S g t (N1bar S g t τ) := by
    rw [B.red.nqSub_N1bar_eq B.mem B.not_mem]
    exact Submodule.mem_sup_left ⟨⟨f, hfN⟩, hf, rfl⟩
  exact (mem_nqSub t_mem_N1bar _).mp h1

theorem conj_mem {r ν : S.O} (hr : r ∈ Rbar S g t) (hν : ν ∈ N1bar S g t τ) :
    r * ν * r⁻¹ ∈ N1bar S g t τ := by
  have := B.red.nqHyp
  have hle := (B.red.N1bar_spec B.mem B.not_mem).1
  have hνN := hle hν
  have hτK := mem_CMt_of_mem_conjCentM B.mem
  have h1 : nqMk ⟨ν, hνN⟩ ∈ LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
    rw [← nqSub_N1bar H hτK hle]
    exact ⟨_, hν, rfl⟩
  have h2 := nqHom_mem_range_nqComm H D.hX hτK (B.red.fix_Vt B.mem) ⟨r, hr⟩ h1
  rw [nqHom_mk, ← nqSub_N1bar H hτK hle] at h2
  exact (mem_nqSub t_mem_N1bar _).mp h2

theorem mem_N1bar_of_mem_Nbar {ρ : S.O} (hρ : ρ ∈ conjCentM S t) (hρN : ρ ∈ Nbar S g t) :
    ρ ∈ N1bar S g t τ := by
  have R := B.red
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  by_cases hρt : ρ = t
  · rw [hρt]
    exact t_mem_N1bar
  obtain ⟨-, -, x, hxM, hxρ⟩ := hρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [← hxρ, h]; group
  have hρz : ρ ∉ zpowers t := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers htt h with h | h
    · exact hρ1 h
    · exact hρt h
  obtain ⟨n, hn, hnρ⟩ : ∃ n ∈ Nbar S g t, n * ρ * n⁻¹ = t * ρ := by
    have hnc : ¬ ∀ n ∈ Nbar S g t, n * ρ = ρ * n := fun h =>
      hρz (Zbar_le_zpowers R.hNo R.hΩ D (mem_Zbar.mpr ⟨hρN, h⟩))
    push Not at hnc
    obtain ⟨n, hn, hnρ⟩ := hnc
    refine ⟨n, hn, ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers htt (D.hNc n hn ρ hρN) with h | h
    · exfalso
      apply hnρ
      calc n * ρ = (n * ρ * n⁻¹ * ρ⁻¹) * (ρ * n) := by group
        _ = ρ * n := by rw [h, one_mul]
    · calc n * ρ * n⁻¹ = (n * ρ * n⁻¹ * ρ⁻¹) * ρ := by group
        _ = t * ρ := by rw [h]
  have hρV : ∀ v ∈ Vt S g t, (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Nbar.mp hρN).2
  have hdimρ : finrank (ZMod 2) (commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxρ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hk : ¬ 2 * finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt)) <
      finrank (ZMod 2) (Vt S g t) := fun hk =>
    ne_conj_mul_of_fix H C ht ht1 hVQ hρV hdimρ hk (n * x) (by
      rw [show n * x * t * (n * x)⁻¹ = n * (x * t * x⁻¹) * n⁻¹ by group, ← hxρ, hnρ])
  have h4 : 4 ≤ finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    rw [D.hdim, R.hm4] at hk
    omega
  set W : Submodule (ZMod 2) (Vt S g t) :=
    (Vt S g t ⊓ commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt)).comap (Vt S g t).subtype with hW
  have hWdim : finrank (ZMod 2) W =
      finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  obtain ⟨c, hc0, hcQ⟩ := CFSG.ClassicalGroups.Orthogonal.exists_ne_zero_map_eq_zero
    (Q := D.Q.comp W.subtype) (by omega)
  have hc0' : (c : Vt S g t) ≠ 0 := fun h => hc0 (Subtype.ext h)
  obtain ⟨e, heR, hea⟩ := (D.hsing _ hc0').mp hcQ
  rw [← range_resV haQ t] at heR
  obtain ⟨r, rfl⟩ := heR
  have hcρ : ((c : Vt S g t) : S.Qt) ∈ commSpace (ρ : S.Qt ≃ₗ[ZMod 2] S.Qt) := c.2.2
  have hcr : ((c : Vt S g t) : S.Qt) =
      ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    rw [← hea, coe_resV_apply]
    rfl
  have hmem : S.cl (g * S.z * g⁻¹) ∈ commSpace ((((r : S.O)⁻¹ * x) * t *
      ((r : S.O)⁻¹ * x)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have e1 : ((r : S.O)⁻¹ * x) * t * ((r : S.O)⁻¹ * x)⁻¹ =
        (r : S.O)⁻¹ * ρ * (r : S.O)⁻¹⁻¹ := by
      rw [hxρ]; group
    rw [e1, S7.commSpace_conj]
    refine ⟨_, hcρ, ?_⟩
    rw [hcr]
    exact inv_apply_apply_O _ _
  have hxM' : (r : S.O)⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem (Rbar_le_Mbar r.2)) hxM
  have hL := conj_mem_Lbar_of_cl_mem_commSpace R hxM' hmem
  have hF : (r : S.O)⁻¹ * x * t * ((r : S.O)⁻¹ * x)⁻¹ ∈ S9.Fbar S g t :=
    subset_closure ⟨hL, _, hxM', rfl⟩
  have h5 := B.conj_mem r.2 (B.Fbar_le hF)
  have e2 : (r : S.O) * ((r : S.O)⁻¹ * x * t * ((r : S.O)⁻¹ * x)⁻¹) * (r : S.O)⁻¹ = ρ := by
    rw [hxρ]; group
  rwa [e2] at h5

theorem le_perp : Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
    S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  rw [perp_sup_commSpace]
  exact sup_le_inf_fixSpace H ht1 (B.red.fix_Vt B.mem) (mul_self_of_mem_conjCentM H ht B.mem)

theorem commSpace_le {σ : S.O} (hσ : σ ∈ conjCentM S t) :
    commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  by_cases hσN : σ ∈ Nbar S g t
  · have hν := B.mem_N1bar_of_mem_Nbar hσ hσN
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    exact apply_sub_mem_of_mem_N1bar D (B.red.fix_Vt B.mem) hν u
  · rw [← B.sup_eq hσ hσN]
    exact le_sup_right

theorem map_eq_of_commSpace_le {y : S.O} (hyM : y ∈ S.Mbar)
    (hy : commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set Y := Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hYdef
  have hY := B.le_perp
  have hVY : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y := by
    rw [(commSpace_t_eq H C ht ht1 hVQ).1]
    exact le_sup_left
  have key : ∀ e : S.O, (∃ w ∈ S.Mbar, e = w * t * w⁻¹) →
      commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y →
        commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
          Y.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rintro e ⟨w, hwM, rfl⟩ he
    have hc := commute_of_commSpace_le hY he hy
    have hmem : y⁻¹ * (w * t * w⁻¹) * y⁻¹⁻¹ ∈ conjCentM S t := by
      refine ⟨?_, ?_, y⁻¹ * w, mul_mem (inv_mem hyM) hwM, by group⟩
      · exact mul_mem (mul_mem (inv_mem hyM)
          (mul_mem (mul_mem hwM (S.Lbar_le_Mbar g ht)) (inv_mem hwM))) (inv_mem (inv_mem hyM))
      · calc y⁻¹ * (w * t * w⁻¹) * y⁻¹⁻¹ * t =
            y⁻¹ * ((w * t * w⁻¹) * (y * t * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * t * y⁻¹) * (w * t * w⁻¹)) * y := by rw [hc]
          _ = t * (y⁻¹ * (w * t * w⁻¹) * y⁻¹⁻¹) := by group
    have h1 := B.commSpace_le hmem
    have e1 : w * t * w⁻¹ = y * (y⁻¹ * (w * t * w⁻¹) * y⁻¹⁻¹) * y⁻¹ := by group
    rw [e1, S7.commSpace_conj]
    exact Submodule.map_mono h1
  have hle : Y ≤ Y.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    refine sup_le ?_ ?_
    · have := key t ⟨1, one_mem _, by group⟩ hVY
      rwa [(commSpace_t_eq H C ht ht1 hVQ).1] at this
    · obtain ⟨-, -, w, hwM, hwτ⟩ := B.mem
      exact key τ ⟨w, hwM, hwτ⟩ le_sup_right
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearEquiv.finrank_map_eq]

end Bad4

end CFSG.LargeExtraspecial.S8
