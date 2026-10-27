module

public import CFSG.LargeExtraspecial.AS35ZMTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem commSpace_le_orth_ZM (h65 : S.SixFiveConcl) {a b : S.O} (ha : a ∈ S.DbarAsc)
    (hb : b ∈ S.DbarAsc) (hab : a * b = b * a) (hne : a ≠ b) :
    commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  rw [← fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate b.2]
  have hbaL : (b : S.Qt ≃ₗ[ZMod 2] S.Qt) * a = a * b :=
    congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) hab.symm
  have hdis : commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rw [inf_comm]
    exact h65.disjoint a ha b hb hab hne
  exact S.commSpace_le_fixSpace_of_commute_disjoint hbaL hdis

section Pair

variable (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
  (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3)
include hS h65 hr ht h3

theorem frame_pieces_ZM {k : ℕ} {F F' : Fin (k / 2) → S.O}
    (hFD : ∀ i, F i ∈ S.DbarAsc ∧ F' i ∈ S.DbarAsc)
    (hFc : ∀ i, F i * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * F i ∧ F i * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * F i ∧
      F' i * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * F' i ∧ F' i * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * F' i)
    (hFn : ∀ i, F i * F' i ≠ F' i * F i)
    (hFo : ∀ i j, i ≠ j → F i * F j = F j * F i ∧ F i * F' j = F' j * F i ∧
      F' i * F j = F j * F' i ∧ F' i * F' j = F' j * F' i) :
    (∀ i, (commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
        LinearMap.BilinForm.orthogonal S.q.polarBilin
          (commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ ∧
      finrank (ZMod 2) (commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
        commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt) : Submodule (ZMod 2) S.Qt) = 4) ∧
    (∀ i, commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (S.rhoL hrM * S.rhoL htM))) ∧
    ∀ i j, i ≠ j →
      commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        LinearMap.BilinForm.orthogonal S.q.polarBilin
          (commSpace (F j : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' j : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · have h3i : orderOf ((F i : S.Qt ≃ₗ[ZMod 2] S.Qt) * (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 3 := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact S.orderOf_mul_eq_three_ZM h65 (hFD i).1 (hFD i).2 (hFn i)
    obtain ⟨-, hsup, hfin, hnd, -⟩ := commSpace_mul_of_orderOf_eq_three S.q_nondegenerate
      (S.typeA_of_mem_DbarAsc_ZM hS (hFD i).1) (S.typeA_of_mem_DbarAsc_ZM hS (hFD i).2) h3i
    rw [← hsup]
    exact ⟨hnd, hfin⟩
  · have hg : S.rhoL hrM * S.rhoL htM ∈ TauCeti.QuadraticMap.orthogonalGroup S.q :=
      (S.ρ ⟨r, hrM⟩ * S.ρ ⟨t, htM⟩).2
    rw [← fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate hg]
    exact sup_le (S.Dx_facts_ZM hS h65 hr ht hrM htM h3 (hFD i).1 (hFc i).1 (hFc i).2.1).2.1
      (S.Dx_facts_ZM hS h65 hr ht hrM htM h3 (hFD i).2 (hFc i).2.2.1 (hFc i).2.2.2).2.1
  · obtain ⟨c1, c2, c3, c4⟩ := hFo i j hij
    have n1 : F i ≠ F j := fun h => hFn j (by rw [← h]; exact c2)
    have n2 : F i ≠ F' j := fun h => hFn j (by rw [← h]; exact c1.symm)
    have n3 : F' i ≠ F j := fun h => hFn j (by rw [← h]; exact c4)
    have n4 : F' i ≠ F' j := fun h => hFn j (by rw [← h]; exact c3.symm)
    refine sup_le (AS35ZM.le_orth_sup S.q ?_ ?_) (AS35ZM.le_orth_sup S.q ?_ ?_)
    · exact S.commSpace_le_orth_ZM h65 (hFD i).1 (hFD j).1 c1 n1
    · exact S.commSpace_le_orth_ZM h65 (hFD i).1 (hFD j).2 c2 n2
    · exact S.commSpace_le_orth_ZM h65 (hFD i).2 (hFD j).1 c3 n3
    · exact S.commSpace_le_orth_ZM h65 (hFD i).2 (hFD j).2 c4 n4

section Main

variable {J : S.Qt ≃ₗ[ZMod 2] S.Qt} (hJ : ∀ v, J (J v) + J v + v = 0)
  (hJq : ∀ v, S.q (J v) = S.q v)
  (hJD : ∀ a ∈ S.DbarAsc, ∀ v, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
  {R : Subgroup S.O} (hRM : R ≤ S.Mbar) (hxM : r * t ∈ S.M)
  (hRx : ∀ σ ∈ R, σ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * σ)
  (hRn : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * τ → ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R)
  (hR2 : IsPGroup 2 R)
include hrM htM hJ hJq hJD hRM hRx hRn hR2

theorem eq_one_of_linear_ZM {k : ℕ} (hk : S.width = k + 2) {u : S.O} (hu : u ∈ R)
    (huJ : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) :
    u = 1 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨n, hn⟩ := S.exists_pow_two_eq_one_ZM hR2 hu
  have hux := S.linear_of_mem_ZM hrM htM hxM hRx hu
  obtain ⟨hW, -, -⟩ := S.linear_facts_ZM hS hr ht hrM htM h3 hJ hJD hn huJ hux
  have hnc := S.rho_not_commute_ZM hr ht hrM htM h3
  obtain ⟨-, ⟨F, F', hFD, hFc, hFn, hFo⟩, -⟩ := S.pg_data_ZM h65 hk
    (S.ρ_mem_DbarAsc hr hrM) (S.ρ_mem_DbarAsc ht htM) hnc
  obtain ⟨hP, hPW, hPP⟩ := S.frame_pieces_ZM hS h65 hr ht hrM htM h3 hFD hFc hFn hFo
  have hcF : ∀ i, u * F i = F i * u := fun i => S.commute_of_linear_ZM hS h65 hr ht hrM htM h3
    hJ hJD hRM hxM hRx hRn hR2 hk hu huJ (hFD i).1 (hFc i).1 (hFc i).2.1
  have hcF' : ∀ i, u * F' i = F' i * u := fun i => S.commute_of_linear_ZM hS h65 hr ht hrM htM
    h3 hJ hJD hRM hxM hRx hRn hR2 hk hu huJ (hFD i).2 (hFc i).2.2.1 (hFc i).2.2.2
  set P : Fin (k / 2) → Submodule (ZMod 2) S.Qt := fun i =>
    commSpace (F i : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (F' i : S.Qt ≃ₗ[ZMod 2] S.Qt) with hPdef
  set Vs : ℕ → Submodule (ZMod 2) S.Qt := fun j => if h : j < k / 2 then P ⟨j, h⟩ else ⊥
    with hVs
  have hVs' : ∀ j (h : j < k / 2), Vs j = P ⟨j, h⟩ := fun j h => by simp [hVs, h]
  obtain ⟨-, -, hWfin, hWnd, -⟩ := S.commSpace_rt_ZM hS hr ht hrM htM h3
  obtain ⟨hYnd, hYfin, -⟩ := AS35ZM.orthSum_nondeg S.q (Vs := Vs) (M := k / 2) (d := 4) hWnd
    (fun i hi => by rw [hVs' i hi]; exact (hP _).1)
    (fun i hi => by rw [hVs' i hi]; exact (hP _).2)
    (fun i hi => by rw [hVs' i hi]; exact hPW _)
    (fun i hi j hj hij => by
      rw [hVs' i hi, hVs' j hj]
      exact hPP _ _ (fun h => hij (congrArg Fin.val h)))
    (k / 2) le_rfl
  set Y := AS35ZM.orthSum (commSpace (S.rhoL hrM * S.rhoL htM)) Vs (k / 2) with hY
  have hPu : ∀ i, P i ≤ fixSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun i =>
    sup_le
      (fun w hw => mem_fixSpace.2 (S.triv_commSpace_ZM hS hJ hJD hn huJ (hFD i).1 (hcF i) w hw))
      (fun w hw => mem_fixSpace.2 (S.triv_commSpace_ZM hS hJ hJD hn huJ (hFD i).2 (hcF' i) w hw))
  have huY : Y ≤ fixSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    AS35ZM.orthSum_le (fun w hw => mem_fixSpace.2 (hW w hw)) fun i hi => by
      rw [hVs' i hi]
      exact hPu _
  have hgJ : ∀ v, (S.rhoL hrM * S.rhoL htM) (J v) = J ((S.rhoL hrM * S.rhoL htM) v) := by
    intro v
    have h1 : S.rhoL htM (J v) = J (S.rhoL htM v) := hJD _ (S.ρ_mem_DbarAsc ht htM) v
    have h2 : ∀ w, S.rhoL hrM (J w) = J (S.rhoL hrM w) := hJD _ (S.ρ_mem_DbarAsc hr hrM)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2]
  have hJcs : ∀ {f : S.O}, f ∈ S.DbarAsc → ∀ x ∈ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt),
      J x ∈ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun hf x hx =>
    AS35ZM.commSpace_mem_of_commute (fun v => (hJD _ hf v).symm) hx
  have hJY : ∀ y ∈ Y, J y ∈ Y := by
    have hle : Y ≤ Y.comap J.toLinearMap := by
      refine AS35ZM.orthSum_le (fun w hw => ?_) fun i hi => ?_
      · exact AS35ZM.le_orthSum_W _ _ _ (AS35ZM.J_mem_commSpace hgJ hw)
      · intro x hx
        rw [hVs' i hi] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
        change J (a + b) ∈ Y
        refine AS35ZM.le_orthSum_V _ Vs hi ?_
        rw [hVs' i hi, map_add]
        exact Submodule.add_mem_sup (hJcs (hFD _).1 a ha) (hJcs (hFD _).2 b hb)
    exact fun y hy => hle hy
  have hYpfin : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin Y) ≤ 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, S.finrank_Qt_eq_two_mul_width,
      hk, hYfin, hWfin]
    omega
  have hJYp : ∀ v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y,
      J v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y := fun v hv =>
    AS35ZM.orth_mem_of_isometry S.q hJq
      (fun y hy => ⟨J (J y), hJY _ (hJY _ hy), AS35ZM.J_J_J hJ y⟩) hv
  have huq : ∀ v, S.q ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v := fun v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup u.2 v
  have huYp : ∀ v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y,
      (u : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y :=
    fun v hv => AS35ZM.orth_mem_of_isometry S.q huq
      (fun y hy => ⟨y, hy, mem_fixSpace.1 (huY hy)⟩) hv
  have hYpu := AS35ZM.point_two_elt hJ hYpfin hJYp huJ huYp hn
  have htop := AS35ZM.sup_orth_eq_top S.q S.q_nondegenerate hYnd
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ Y ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin Y := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, mem_fixSpace.1 (huY hy), hYpu w hw]
  rfl

end Main

end Pair

end Setting

end CFSG.LargeExtraspecial
