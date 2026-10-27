module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoStdForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameSupp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerFull
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem linTwo_ds_conj (n x : V ≃ₗ[ZMod 2] V) (v : V) :
    S172A.GL.ds (n * x * n⁻¹) (n v) = n (S172A.GL.ds x v) := by
  rw [S172A.GL.ds_apply, S172A.GL.ds_apply, map_sub]
  congr 1
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp

private theorem linTwo_map_mem_comSp_conj {n x : V ≃ₗ[ZMod 2] V} {v : V}
    (hv : v ∈ S172A.GL.comSp x) : n v ∈ S172A.GL.comSp (n * x * n⁻¹) := by
  obtain ⟨w, hw⟩ := S172A.GL.mem_comSp.1 hv
  refine S172A.GL.mem_comSp.2 ⟨n w, ?_⟩
  rw [← S172A.GL.ds_apply, linTwo_ds_conj, ← hw, S172A.GL.ds_apply]

private theorem linTwo_comSp_le_iSup_P {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V}
    {V0 : Submodule (ZMod 2) V} (hF : LinTwoStdFrame E x P V0)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ E) : comSp a ≤ ⨆ j, P j := by
  have hFc := hF
  obtain ⟨-, hint, -, -, hxcom, -, -⟩ := hF
  have htop : V0 ⊔ (⨆ j, P j) = ⊤ := by
    have := hint.submodule_iSup_eq_top
    rwa [iSup_option_elim] at this
  intro w hw
  obtain ⟨v, hv⟩ := S172A.GL.mem_comSp.1 hw
  rw [← hv]
  have hvsup : v ∈ V0 ⊔ (⨆ j, P j) := htop ▸ Submodule.mem_top
  obtain ⟨v0, hv0, u, hu, hvu⟩ := Submodule.mem_sup.1 hvsup
  have hact := lin_two_frame_action hFc ha
  have haP : ∀ j, ∀ z ∈ P j, a z ∈ P j := by
    intro j z hz
    obtain ⟨k, hk⟩ := hact.2 j
    rw [hk z hz]
    have hstep : ∀ y ∈ P j, x j y ∈ P j := by
      intro y hy
      rw [← hxcom j] at hy ⊢
      exact S172A.GL.e_mem_comSp hy
    clear hk
    induction k with
    | zero => simpa using hz
    | succ k ih =>
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hstep (((x j) ^ k) z) ih
  have haW : a u ∈ ⨆ j, P j := by
    refine Submodule.iSup_induction P (motive := fun z => a z ∈ ⨆ j, P j) hu ?_ ?_ ?_
    · intro j z hz
      exact Submodule.mem_iSup_of_mem j (haP j z hz)
    · simp
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have hav : a v - v = a u - u := by
    rw [← hvu, map_add, hact.1 v0 hv0]
    abel
  rw [hav]
  exact Submodule.sub_mem _ haW hu

private theorem linTwo_sup_P_fixed_eq_zero {r : ℕ} {x : Fin r → V ≃ₗ[ZMod 2] V}
    {P : Fin r → Submodule (ZMod 2) V}
    (hx3 : ∀ i, x i ^ 3 = 1) (hxcom : ∀ i, comSp (x i) = P i)
    (hxoff : ∀ i j, i ≠ j → ∀ v ∈ P j, x i v = v) :
    ∀ (s : Finset (Fin r)) {z : V}, z ∈ s.sup P → (∀ i ∈ s, x i z = z) → z = 0 := by
  intro s
  induction s using Finset.induction with
  | empty => intro z hz _; simpa using hz
  | insert k t hk ih =>
      intro z hz hfix
      rw [Finset.sup_insert] at hz
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hz
      have hqfix : x k q = q := by
        have hle : t.sup P ≤ LinearMap.ker (S172A.GL.ds (x k)) := by
          refine Finset.sup_le fun j hj => ?_
          intro y hy
          rw [LinearMap.mem_ker, S172A.GL.ds_apply, hxoff k j ?_ y hy, sub_self]
          exact fun hkj => hk (hkj ▸ hj)
        have hkq := hle hq
        rw [LinearMap.mem_ker, S172A.GL.ds_apply, sub_eq_zero] at hkq
        exact hkq
      have hpk : x k p = p := by
        have h1 := hfix k (Finset.mem_insert_self k t)
        rw [← hpq, map_add, hqfix] at h1
        exact add_right_cancel h1
      have hp0 : p = 0 :=
        S172A.GL.eq_zero_of_mem_comSp_fixed (hx3 k) ((hxcom k).symm ▸ hp) hpk
      have hzq : z = q := by rw [← hpq, hp0, zero_add]
      rw [hzq]
      exact ih hq fun i hi => by
        have h2 := hfix i (Finset.mem_insert_of_mem hi)
        rw [← hpq, hp0, zero_add] at h2
        exact h2

private theorem linTwo_mem_V0_of_forall_fix {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V}
    {V0 : Submodule (ZMod 2) V} (hF : LinTwoStdFrame E x P V0)
    {v : V} (hv : ∀ i, x i v = v) : v ∈ V0 := by
  have hFc := hF
  obtain ⟨hAeq, hint, -, hx3, hxcom, -, hxoff⟩ := hF
  have htop : V0 ⊔ (⨆ j, P j) = ⊤ := by
    have := hint.submodule_iSup_eq_top
    rwa [iSup_option_elim] at this
  have hxmem : ∀ i, x i ∈ E := by
    intro i
    rw [hAeq]
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers (x i))
  have hvsup : v ∈ V0 ⊔ (⨆ j, P j) := htop ▸ Submodule.mem_top
  obtain ⟨v0, hv0, u, hu, hvu⟩ := Submodule.mem_sup.1 hvsup
  have huW : u ∈ (Finset.univ : Finset (Fin r)).sup P := by
    rw [Finset.sup_eq_iSup]
    simpa using hu
  have hufix : ∀ i, x i u = u := by
    intro i
    have h1 : x i (v0 + u) = v0 + u := by rw [hvu]; exact hv i
    rw [map_add, (lin_two_frame_action hFc (hxmem i)).1 v0 hv0] at h1
    exact add_left_cancel h1
  have hu0 : u = 0 :=
    linTwo_sup_P_fixed_eq_zero hx3 hxcom hxoff Finset.univ huW fun i _ => hufix i
  rw [← hvu, hu0, add_zero]
  exact hv0

private theorem linTwo_conj_mem_linTwoOddBlock {g n h : V ≃ₗ[ZMod 2] V}
    (hnV0 : ∀ v ∈ fixSp g, n⁻¹ v ∈ fixSp g)
    (hnW : ∀ w ∈ comSp g, n w ∈ comSp g)
    (hnWi : ∀ w ∈ comSp g, n⁻¹ w ∈ comSp g)
    (hh : h ∈ linTwoOddBlock g) : n * h * n⁻¹ ∈ linTwoOddBlock g := by
  obtain ⟨hhfix, hhcom⟩ := hh
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhfix (n⁻¹ v) (hnV0 v hv)]
    simp
  · intro w
    constructor
    · intro hw
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      exact hnW _ ((hhcom (n⁻¹ w)).1 (hnWi w hw))
    · intro hw
      have h1 : h (n⁻¹ w) ∈ comSp g := by
        have hthis := hnWi _ hw
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hthis
        simpa using hthis
      have h2 : n⁻¹ w ∈ comSp g := (hhcom (n⁻¹ w)).2 h1
      simpa using hnW _ h2

theorem lin_two_oddFull_innerClosure_le (hV : 6 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} (hA : GLAIsBmax 3 A)
    (hg : IsStdElt 3 A g) (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    innerClosure A g ≤ linTwoOddBlock g := by
  obtain ⟨hgA, -, hg3, -, -⟩ := hg
  obtain ⟨x, P, V0, hF⟩ := lin_two_std_form_of_bmax (by omega) hA
  have hFc := hF
  obtain ⟨hAeq, -, -, hx3, hxcom, -, hxoff⟩ := hF
  have hsum := S172A.GL.finrank_fixSp hg3
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp hg3
  have hodd : Odd (Module.finrank (ZMod 2) V) := ⟨m, by omega⟩
  obtain ⟨hfixV0, hcomW⟩ := lin_two_frame_full_support hFc hodd hgA hg3 hfix
  have hxmem : ∀ i, x i ∈ A := by
    intro i
    rw [hAeq]
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers (x i))
  have hstd : stdLayer g ≤ linTwoOddBlock g := by
    intro h hh
    have hC : h ∈ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)) :=
      CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le _ hh
    have hcomm : h * g = g * h := Subgroup.mem_centralizer_singleton_iff.1 hC
    refine ⟨?_, ?_⟩
    · exact S172A.GL.fix_of_finrank_one hfix fun u hu => S172A.GL.cent_fix hcomm hu
    · intro w
      constructor
      · intro hw
        exact S172A.GL.cent_com hcomm hw
      · intro hw
        have hcommi : h⁻¹ * g = g * h⁻¹ :=
          Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.inv_mem _ hC)
        have h1 := S172A.GL.cent_com hcommi hw
        simpa using h1
  rw [innerClosure, closureIn]
  refine iSup₂_le fun n hn => ?_
  have hnV0i : ∀ v ∈ fixSp g, n⁻¹ v ∈ fixSp g := by
    intro v hv
    rw [hfixV0] at hv ⊢
    refine linTwo_mem_V0_of_forall_fix hFc fun i => ?_
    have ha : n * x i * n⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 hn (x i)).1 (hxmem i)
    have hafix : (n * x i * n⁻¹) v = v := (lin_two_frame_action hFc ha).1 v hv
    have hco : n⁻¹ * (n * x i * n⁻¹) * n = x i := by group
    calc x i (n⁻¹ v) = (n⁻¹ * (n * x i * n⁻¹) * n) (n⁻¹ v) := by rw [hco]
      _ = n⁻¹ ((n * x i * n⁻¹) (n (n⁻¹ v))) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = n⁻¹ ((n * x i * n⁻¹) v) := by simp
      _ = n⁻¹ v := by rw [hafix]
  have hnW : ∀ w ∈ comSp g, n w ∈ comSp g := by
    intro w hw
    rw [hcomW] at hw ⊢
    refine Submodule.iSup_induction P (motive := fun z => n z ∈ ⨆ j, P j) hw ?_ ?_ ?_
    · intro j z hz
      have hz' : z ∈ comSp (x j) := (hxcom j).symm ▸ hz
      have ha : n * x j * n⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 hn (x j)).1 (hxmem j)
      exact linTwo_comSp_le_iSup_P hFc ha (linTwo_map_mem_comSp_conj hz')
    · simp
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have hnWi : ∀ w ∈ comSp g, n⁻¹ w ∈ comSp g := by
    intro w hw
    rw [hcomW] at hw ⊢
    refine Submodule.iSup_induction P (motive := fun z => n⁻¹ z ∈ ⨆ j, P j) hw ?_ ?_ ?_
    · intro j z hz
      have hz' : z ∈ comSp (x j) := (hxcom j).symm ▸ hz
      have ha : n⁻¹ * x j * n ∈ A :=
        (Subgroup.mem_normalizer_iff''.1 hn (x j)).1 (hxmem j)
      have hconj := linTwo_map_mem_comSp_conj (n := n⁻¹) (x := x j) hz'
      exact linTwo_comSp_le_iSup_P hFc (by simpa using ha) (by simpa using hconj)
    · simp
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  refine Subgroup.map_le_iff_le_comap.2 fun h hh => ?_
  have hconj := linTwo_conj_mem_linTwoOddBlock hnV0i hnW hnWi (hstd hh)
  simpa [MulAut.conj_apply] using hconj

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
