module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameSupp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoGF4Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp mem_fixSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X (innerClosure stdLayer)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private lemma comSp_conj (a e : V ≃ₗ[ZMod 2] V) :
    comSp (a * e * a⁻¹) = (comSp e).map (a : V →ₗ[ZMod 2] V) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := S172A.GL.mem_comSp.1 hx
    refine Submodule.mem_map.2 ⟨e (a⁻¹ y) - a⁻¹ y, S172A.GL.mem_comSp.2 ⟨a⁻¹ y, rfl⟩, ?_⟩
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp
  · rintro x ⟨w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := S172A.GL.mem_comSp.1 hw
    exact S172A.GL.mem_comSp.2 ⟨a v, by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub]
      simp⟩

private lemma comSp_inv (e : V ≃ₗ[ZMod 2] V) : comSp e⁻¹ = comSp e := by
  have hmap : (comSp e).map (e : V →ₗ[ZMod 2] V) = comSp e := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.map_le_iff_le_comap]
      intro x hx
      exact S172A.GL.cent_com (show e * e = e * e from rfl) hx
    · rw [LinearEquiv.finrank_map_eq]
  have hmapinv : (comSp e).map ((e⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = comSp e := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ (comSp e).map (e : V →ₗ[ZMod 2] V) := by rwa [hmap]
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
      rw [← hyx]
      simpa using hy
    · rw [LinearEquiv.finrank_map_eq]
  have hds : S172A.GL.ds e⁻¹ =
      ((e⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V).comp (S172A.GL.ds e) := by
    ext v
    show e⁻¹ v - v = e⁻¹ (e v - v)
    rw [map_sub]
    rw [show e⁻¹ (e v) = v from LinearEquiv.symm_apply_apply e v]
    rw [S172A.GL.sub_V, S172A.GL.sub_V, add_comm]
  calc comSp e⁻¹ = LinearMap.range (S172A.GL.ds e⁻¹) := rfl
    _ = LinearMap.range (((e⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V).comp
          (S172A.GL.ds e)) := by rw [hds]
    _ = (LinearMap.range (S172A.GL.ds e)).map ((e⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) :=
        LinearMap.range_comp _ _
    _ = (comSp e).map ((e⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) := rfl
    _ = comSp e := hmapinv

private theorem le_closureIn_self' {G : Type} [Group G] (K H : Subgroup G) : K ≤ closureIn K H := by
  intro k hk
  exact le_iSup₂ (f := fun (a : G) (_ : a ∈ H) => K.map (MulAut.conj a).toMonoidHom) 1 H.one_mem
    ⟨k, hk, by simp⟩

private theorem conj_mem_closureIn' {G : Type} [Group G] {K H : Subgroup G} {n k : G} (hn : n ∈ H)
    (hk : k ∈ K) : n * k * n⁻¹ ∈ closureIn K H :=
  le_iSup₂ (f := fun (a : G) (_ : a ∈ H) => K.map (MulAut.conj a).toMonoidHom) n hn
    ⟨k, hk, by simp [MulAut.conj_apply]⟩

private def twoOddLin (g : V ≃ₗ[ZMod 2] V) (a : V) (f : V →ₗ[ZMod 2] ZMod 2) :
    V →ₗ[ZMod 2] V :=
  f.smulRight (g (g a)) + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a

private def twoOddAnti (g : V ≃ₗ[ZMod 2] V) (a : V) (f : V →ₗ[ZMod 2] ZMod 2) :
    V →ₗ[ZMod 2] V :=
  f.smulRight (g a) + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a

private lemma twoOddLin_apply (g : V ≃ₗ[ZMod 2] V) (a : V)
    (f : V →ₗ[ZMod 2] ZMod 2) (v : V) :
    twoOddLin g a f v = f v • g (g a) + f (g v) • a := rfl

private lemma twoOddAnti_apply (g : V ≃ₗ[ZMod 2] V) (a : V)
    (f : V →ₗ[ZMod 2] ZMod 2) (v : V) :
    twoOddAnti g a f v = f v • g a + f (g v) • a := rfl

theorem lin_two_oddFull_transv_mem {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x : Fin (Module.finrank (ZMod 2) V / 2) → V ≃ₗ[ZMod 2] V}
    {P : Fin (Module.finrank (ZMod 2) V / 2) → Submodule (ZMod 2) V}
    {V0 : Submodule (ZMod 2) V} (hF : LinTwoStdFrame A x P V0)
    {g : V ≃ₗ[ZMod 2] V} (hgA : g ∈ A) (hg3 : g ^ 3 = 1)
    (hfix : Module.finrank (ZMod 2) (fixSp g) = 1)
    {i j : Fin (Module.finrank (ZMod 2) V / 2)} (hij : i ≠ j) {a : V} (ha : a ∈ P i)
    (f : V →ₗ[ZMod 2] ZMod 2) (hfV0 : ∀ v ∈ V0, f v = 0)
    (hfP : ∀ k, k ≠ j → ∀ v ∈ P k, f v = 0) :
    S172A.GL.tv a f (hfP i hij a ha) ∈ innerClosure A g := by
  have hfa : f a = 0 := hfP i hij a ha
  have hsum := S172A.GL.finrank_fixSp (V := V) hg3
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp (V := V) hg3
  have hodd : Odd (Module.finrank (ZMod 2) V) := ⟨m, by omega⟩
  obtain ⟨hfixV0, hcomW⟩ := lin_two_frame_full_support hF hodd hgA hg3 hfix
  have haW : a ∈ comSp g := by
    rw [hcomW]; exact Submodule.mem_iSup_of_mem i ha
  have hquad : g (g a) + g a + a = 0 := S172A.GL.quad_of_mem_comSp hg3 haW
  have hg2a : g (g a) + g a = a := by
    have h : (g (g a) + g a) + a = (a) + a := by rw [hquad, S172A.GL.add_self_V]
    exact add_right_cancel h
  have hg2a' : g (g a) = a + g a := by
    have h := congrArg (· + g a) hg2a
    rw [add_assoc, S172A.GL.add_self_V, add_zero] at h
    exact h
  have hgPk : ∀ k, ∀ v ∈ P k, g v ∈ P k := by
    intro k v hv
    obtain ⟨e, he⟩ := (lin_two_frame_action hF hgA).2 k
    have hxk : ∀ w ∈ P k, x k w ∈ P k := by
      intro w hw
      have hmem : w ∈ comSp (x k) := by rwa [hF.2.2.2.2.1 k]
      have := S172A.GL.cent_com (show x k * x k = x k * x k from rfl) hmem
      rwa [hF.2.2.2.2.1 k] at this
    have hxke : (x k ^ e) v ∈ P k := by
      clear he
      induction e with
      | zero => simpa using hv
      | succ e ih => rw [pow_succ']; exact hxk _ ih
    rwa [he v hv]
  have hPig : ∀ v ∈ P i, g v ∈ P i := hgPk i
  have hga : g a ∈ P i := hPig a ha
  have hgga : g (g a) ∈ P i := hPig (g a) hga
  have hfga : f (g a) = 0 := hfP i hij (g a) hga
  have hfgga : f (g (g a)) = 0 := hfP i hij (g (g a)) hgga
  have hm2 : 2 ≤ m := by
    have hdisj : Disjoint (P i) (P j) := by
      have hpd := hF.2.1.submodule_iSupIndep.pairwiseDisjoint
      have hne : (some i : Option (Fin (Module.finrank (ZMod 2) V / 2))) ≠ some j := by
        simp [hij]
      have := hpd hne
      exact this
    have hfin4 : Module.finrank (ZMod 2) ↥(P i ⊔ P j) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (P i) (P j)
      rw [disjoint_iff.mp hdisj, hF.2.2.1 i, hF.2.2.1 j] at h
      simp at h
      omega
    have hle : Module.finrank (ZMod 2) ↥(P i ⊔ P j) ≤ Module.finrank (ZMod 2) (comSp g) := by
      apply Submodule.finrank_mono
      rw [hcomW]
      exact sup_le (le_iSup P i) (le_iSup P j)
    have : 4 ≤ Module.finrank (ZMod 2) (comSp g) := hfin4 ▸ hle
    omega
  have hm' : Module.finrank (ZMod 2) (comSp g) = 2 * m := by rw [hm, two_mul]
  obtain ⟨F, hFcent, hFnorm, hFq, hFfix, hFtrans, hFinv⟩ :=
    lin_two_gf4_layer (V := V) hg3 hm' hm2
  have hFstd : F ≤ stdLayer g :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer
      ⟨hFcent, IsSubnormal.step hFcent hFnorm (IsSubnormal.refl _), hFq⟩
  have hsumf' : ∀ v, f (v + g v + g (g v)) = 0 := by
    intro v
    obtain ⟨u, u', huv⟩ := S172A.GL.exists_decomp (S172A.GL.isCompl_fixSp_comSp hg3) v
    have hgu : g (u : V) = u := mem_fixSp.1 u.2
    have hg2u : g (g (u : V)) = u := by rw [hgu, hgu]
    have hqu : (u' : V) + g (u' : V) + g (g (u' : V)) = 0 := by
      have := S172A.GL.quad_of_mem_comSp hg3 u'.2
      rw [← this]; abel
    have huV0 : (u : V) ∈ V0 := hfixV0 ▸ u.2
    calc f (v + g v + g (g v))
        = f ((u : V) + (u' : V) + g ((u : V) + (u' : V)) + g (g ((u : V) + (u' : V)))) := by
          rw [huv]
      _ = f ((u : V) + ((u' : V) + g (u' : V) + g (g (u' : V)))) := by
          congr 1
          have hfac : (u : V) + (u' : V) + g ((u : V) + (u' : V)) + g (g ((u : V) + (u' : V)))
              = ((u : V) + g (u : V) + g (g (u : V)))
                + ((u' : V) + g (u' : V) + g (g (u' : V))) := by
            simp only [map_add]
            abel
          rw [hfac]
          have hu : (u : V) + g (u : V) + g (g (u : V)) = (u : V) := by
            rw [hg2u, hgu, add_assoc, S172A.GL.add_self_V, add_zero]
          rw [hu]
      _ = f ((u : V) + 0) := by rw [hqu]
      _ = f (u : V) := by rw [add_zero]
      _ = 0 := hfV0 _ huV0
  have hsumf : ∀ v, f v + f (g v) + f (g (g v)) = 0 := fun v => by
    simpa only [map_add] using hsumf' v
  have hlin_comm : ∀ v, twoOddLin g a f (g v) = g (twoOddLin g a f v) := by
    intro v
    have h1 := hsumf v
    have h1' : f (g v) + f (g (g v)) = f v := by
      have h1a : f v + (f (g v) + f (g (g v))) = 0 := by rw [← add_assoc]; exact h1
      exact add_left_cancel (by rw [h1a, S172A.GL.add_self_V])
    rw [twoOddLin_apply, twoOddLin_apply, map_add, map_smul, map_smul,
      S172A.GL.cube hg3 a, hg2a', smul_add]
    have hrearr : (f (g v) • a + f (g v) • g a) + f (g (g v)) • a
        = (f (g v) + f (g (g v))) • a + f (g v) • g a := by
      rw [add_smul]; abel
    rw [hrearr, h1']
  have hlin_fix : ∀ l ∈ fixSp g, twoOddLin g a f l = 0 := by
    intro l hl
    have hlV0 : l ∈ V0 := hfixV0 ▸ hl
    have hgl : g l = l := mem_fixSp.1 hl
    rw [twoOddLin_apply, hgl, hfV0 l hlV0, zero_smul, zero_smul, add_zero]
  have hlin_mem_Pi : ∀ v, twoOddLin g a f v ∈ P i := by
    intro v
    rw [twoOddLin_apply]
    exact (P i).add_mem ((P i).smul_mem _ hgga) ((P i).smul_mem _ ha)
  have hlin_sq : ∀ v, twoOddLin g a f (twoOddLin g a f v) = 0 := by
    intro v
    have hmem := hlin_mem_Pi v
    have hgmem : g (twoOddLin g a f v) ∈ P i := hPig _ hmem
    rw [twoOddLin_apply, hfP i hij (twoOddLin g a f v) hmem,
      hfP i hij (g (twoOddLin g a f v)) hgmem, zero_smul, zero_smul, add_zero]
  have hanti_mem_Pi : ∀ v, twoOddAnti g a f v ∈ P i := by
    intro v
    rw [twoOddAnti_apply]
    exact (P i).add_mem ((P i).smul_mem _ hga) ((P i).smul_mem _ ha)
  have hanti_sq : ∀ v, twoOddAnti g a f (twoOddAnti g a f v) = 0 := by
    intro v
    have hmem := hanti_mem_Pi v
    have hgmem : g (twoOddAnti g a f v) ∈ P i := hPig _ hmem
    rw [twoOddAnti_apply, hfP i hij (twoOddAnti g a f v) hmem,
      hfP i hij (g (twoOddAnti g a f v)) hgmem, zero_smul, zero_smul, add_zero]
  have hlin_anti : ∀ v, twoOddLin g a f (twoOddAnti g a f v) = 0 := by
    intro v
    have hmem := hanti_mem_Pi v
    have hgmem : g (twoOddAnti g a f v) ∈ P i := hPig _ hmem
    rw [twoOddLin_apply, hfP i hij (twoOddAnti g a f v) hmem,
      hfP i hij (g (twoOddAnti g a f v)) hgmem, zero_smul, zero_smul, add_zero]
  have hlin_anti_sum : twoOddLin g a f + twoOddAnti g a f = f.smulRight a := by
    rw [twoOddLin, twoOddAnti]
    have h1 : f.smulRight (g (g a)) + f.smulRight (g a) = f.smulRight (g (g a) + g a) := by
      ext w; simp [smul_add]
    have h2 : (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a
        + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a = 0 :=
      S172A.GL.add_self_V _
    rw [show f.smulRight (g (g a)) + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a
          + (f.smulRight (g a) + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a)
        = (f.smulRight (g (g a)) + f.smulRight (g a))
          + ((f.comp (g : V →ₗ[ZMod 2] V)).smulRight a
              + (f.comp (g : V →ₗ[ZMod 2] V)).smulRight a) by abel,
      h1, hg2a, h2, add_zero]
  set Alin : V ≃ₗ[ZMod 2] V :=
    S172A.GL.tv (g (g a)) f hfgga * S172A.GL.tv a (f.comp (g : V →ₗ[ZMod 2] V)) hfga with hAlin
  set Aanti : V ≃ₗ[ZMod 2] V :=
    S172A.GL.tv (g a) f hfga * S172A.GL.tv a (f.comp (g : V →ₗ[ZMod 2] V)) hfga with hAanti
  have hAlin_apply : ∀ v, Alin v = v + twoOddLin g a f v := by
    intro v
    rw [hAlin, LinearEquiv.mul_apply, S172A.GL.tv_apply, S172A.GL.tv_apply, twoOddLin_apply]
    rw [map_add, map_smul, hfa, smul_zero, add_zero, LinearMap.comp_apply]
    module
  have hAanti_apply : ∀ v, Aanti v = v + twoOddAnti g a f v := by
    intro v
    rw [hAanti, LinearEquiv.mul_apply, S172A.GL.tv_apply, S172A.GL.tv_apply, twoOddAnti_apply]
    rw [map_add, map_smul, hfa, smul_zero, add_zero, LinearMap.comp_apply]
    module
  have hAlin_cent : Alin ∈ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply LinearEquiv.ext
    intro v
    change Alin (g v) = g (Alin v)
    rw [hAlin_apply (g v), hAlin_apply v, map_add]
    congr 1
    exact hlin_comm v
  have hAlin_fix : ∀ l ∈ fixSp g, Alin l = l := by
    intro l hl
    rw [hAlin_apply l, hlin_fix l hl, add_zero]
  have hAlin_sq : Alin * Alin = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, hAlin_apply (Alin v), hAlin_apply v, map_add, hlin_sq v, add_zero,
      add_assoc, S172A.GL.add_self_V, add_zero]
    rfl
  have hAlin_in : Alin ∈ innerClosure A g := by
    rw [innerClosure]
    exact le_closureIn_self' (stdLayer g) (Subgroup.normalizer (A : Set (V ≃ₗ[ZMod 2] V)))
      (hFstd (hFinv Alin hAlin_cent hAlin_fix hAlin_sq))
  obtain ⟨s, hsN, hsx, hsV0, hsP⟩ := lin_two_frame_inv (V := V) hF j
  set h : V ≃ₗ[ZMod 2] V := s * g * s⁻¹ with hh
  have hV0act : ∀ v ∈ V0, h v = v := by
    intro v hv
    have hsv : s⁻¹ v = v := S172A.GL.inv_apply_of_fix (hsV0 v hv)
    have hgv : g v = v := (lin_two_frame_action hF hgA).1 v hv
    calc h v = s (g (s⁻¹ v)) := by rw [hh, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s (g v) := by rw [hsv]
      _ = s v := by rw [hgv]
      _ = v := hsV0 v hv
  have hPkact : ∀ k, k ≠ j → ∀ v ∈ P k, h v = g v := by
    intro k hk v hv
    have hsv : s⁻¹ v = v := S172A.GL.inv_apply_of_fix (hsP k hk v hv)
    have hgv : g v ∈ P k := hgPk k v hv
    calc h v = s (g (s⁻¹ v)) := by rw [hh, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s (g v) := by rw [hsv]
      _ = g v := hsP k hk (g v) hgv
  have hPjact : ∀ v ∈ P j, h v = g (g v) := by
    intro v hv
    obtain ⟨e, he⟩ := (lin_two_frame_action hF hgA).2 j
    have hxj : ∀ w ∈ P j, x j w ∈ P j := by
      intro w hw
      have hmem : w ∈ comSp (x j) := by rwa [hF.2.2.2.2.1 j]
      have := S172A.GL.cent_com (show x j * x j = x j * x j from rfl) hmem
      rwa [hF.2.2.2.2.1 j] at this
    have hxje : ∀ w ∈ P j, (x j ^ e) w ∈ P j := by
      have hxjpow : ∀ n, ∀ w ∈ P j, (x j ^ n) w ∈ P j := by
        intro n w hw
        induction n with
        | zero => simpa using hw
        | succ n ih => rw [pow_succ']; exact hxj _ ih
      exact hxjpow e
    have hsPj : (P j).map (s : V →ₗ[ZMod 2] V) = P j := by
      have h1 := comSp_conj s (x j)
      rw [hsx, comSp_inv] at h1
      rw [hF.2.2.2.2.1 j] at h1
      exact h1.symm
    have hsinvPj : ∀ w ∈ P j, s⁻¹ w ∈ P j := by
      intro w hw
      have hmem : w ∈ (P j).map (s : V →ₗ[ZMod 2] V) := by rwa [hsPj]
      obtain ⟨z, hz, hzw⟩ := Submodule.mem_map.1 hmem
      rw [← hzw]
      simpa using hz
    have hsv : s⁻¹ v ∈ P j := hsinvPj v hv
    have hconj_e : s * x j ^ e * s⁻¹ = (x j)⁻¹ ^ e := by
      have hc : MulAut.conj s (x j) = (x j)⁻¹ := by rw [MulAut.conj_apply]; exact hsx
      calc s * x j ^ e * s⁻¹ = MulAut.conj s (x j ^ e) := by rw [MulAut.conj_apply]
        _ = (MulAut.conj s (x j)) ^ e := map_pow _ _ _
        _ = (x j)⁻¹ ^ e := by rw [hc]
    have hy3 : (x j ^ e) ^ 3 = 1 := by
      have h3 : ((x j) ^ 3) ^ e = 1 := by rw [hF.2.2.2.1 j, one_pow]
      have h4 : ((x j) ^ 3) ^ e = (x j ^ e) ^ 3 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 e]
      rw [← h4]
      exact h3
    have hinv_e : (x j ^ e)⁻¹ = (x j ^ e) ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hy3])
    calc h v = s (g (s⁻¹ v)) := by rw [hh, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = s ((x j ^ e) (s⁻¹ v)) := by rw [he (s⁻¹ v) hsv]
      _ = (s * x j ^ e * s⁻¹) v := by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = ((x j)⁻¹ ^ e) v := by rw [hconj_e]
      _ = ((x j ^ e)⁻¹) v := by rw [inv_pow]
      _ = ((x j ^ e) ^ 2) v := by rw [hinv_e]
      _ = (x j ^ e) ((x j ^ e) v) := by rw [pow_two, LinearEquiv.mul_apply]
      _ = g (g v) := by rw [he v hv, he ((x j ^ e) v) (hxje v hv)]
  set U : Submodule (ZMod 2) V :=
    V0 ⊔ ⨆ (k : Fin (Module.finrank (ZMod 2) V / 2)) (_ : k ≠ j), P k with hU
  have hfU : U ≤ f.ker := by
    rw [hU]
    apply sup_le
    · intro x hx
      exact LinearMap.mem_ker.mpr (hfV0 x hx)
    · apply iSup_le; intro k
      apply iSup_le; intro hk
      intro x hx
      exact LinearMap.mem_ker.mpr (hfP k hk x hx)
  set L1 : V →ₗ[ZMod 2] V := LinearMap.id + (h : V →ₗ[ZMod 2] V) + (g : V →ₗ[ZMod 2] V) with hL1
  have hL1_le : LinearMap.range L1 ≤ U := by
    rw [← Submodule.map_top, ← hF.2.1.submodule_iSup_eq_top, Submodule.map_iSup]
    apply iSup_le
    intro o
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    show L1 x ∈ U
    rw [hL1, LinearMap.add_apply, LinearMap.add_apply, LinearMap.id_apply]
    change x + h x + g x ∈ U
    rcases o with _ | k
    · rw [hV0act x hx, (lin_two_frame_action hF hgA).1 x hx]
      rw [S172A.GL.add_self_V x, zero_add]
      exact Submodule.mem_sup_left hx
    · by_cases hk : k = j
      · have hx' : x ∈ P j := by rwa [← hk]
        rw [hPjact x hx']
        have hxW : x ∈ comSp g := by rw [hcomW]; exact Submodule.mem_iSup_of_mem j hx'
        have hq := S172A.GL.quad_of_mem_comSp hg3 hxW
        have hzero : x + g (g x) + g x = 0 := by rw [← hq]; abel
        rw [hzero]
        exact Submodule.zero_mem _
      · rw [hPkact k hk x hx]
        have hzero : x + g x + g x = x := by rw [add_assoc, S172A.GL.add_self_V, add_zero]
        rw [hzero]
        exact Submodule.mem_sup_right
          (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk hx))
  have hid1 : ∀ u, f (u + h u + g u) = 0 := by
    intro u
    have hmem : L1 u ∈ U := hL1_le ⟨u, rfl⟩
    have : f (L1 u) = 0 := LinearMap.mem_ker.mp (hfU hmem)
    rwa [hL1, LinearMap.add_apply, LinearMap.add_apply, LinearMap.id_apply] at this
  set L2 : V →ₗ[ZMod 2] V := LinearMap.id + (g : V →ₗ[ZMod 2] V).comp (h : V →ₗ[ZMod 2] V)
    with hL2
  have hL2_le : LinearMap.range L2 ≤ U := by
    rw [← Submodule.map_top, ← hF.2.1.submodule_iSup_eq_top, Submodule.map_iSup]
    apply iSup_le
    intro o
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    show L2 x ∈ U
    rw [hL2, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply]
    change x + g (h x) ∈ U
    rcases o with _ | k
    · rw [hV0act x hx, (lin_two_frame_action hF hgA).1 x hx]
      rw [S172A.GL.add_self_V x]
      exact Submodule.zero_mem _
    · by_cases hk : k = j
      · have hx' : x ∈ P j := by rwa [← hk]
        rw [hPjact x hx', S172A.GL.cube hg3 x]
        rw [S172A.GL.add_self_V x]
        exact Submodule.zero_mem _
      · rw [hPkact k hk x hx]
        have hgx : g x ∈ P k := hgPk k x hx
        have hggx : g (g x) ∈ P k := hgPk k (g x) hgx
        exact Submodule.mem_sup_right
          (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
            ((P k).add_mem hx hggx)))
  have hid2 : ∀ u, f (u + (g * h) u) = 0 := by
    intro u
    have hmem : L2 u ∈ U := hL2_le ⟨u, rfl⟩
    have : f (L2 u) = 0 := LinearMap.mem_ker.mp (hfU hmem)
    rwa [hL2, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply] at this
  set psi : V →ₗ[ZMod 2] V :=
    (f.comp (s : V →ₗ[ZMod 2] V)).smulRight (g a) +
      (f.comp ((g : V →ₗ[ZMod 2] V).comp (s : V →ₗ[ZMod 2] V))).smulRight a with hpsi
  have hpsi_apply : ∀ v, psi v = f (s v) • g a + f (g (s v)) • a := by
    intro v; rw [hpsi]; rfl
  have hpsi_mem_Pi : ∀ v, psi v ∈ P i := by
    intro v
    rw [hpsi_apply]
    exact (P i).add_mem ((P i).smul_mem _ hga) ((P i).smul_mem _ ha)
  have hpsi_sq : ∀ v, psi (psi v) = 0 := by
    intro v
    have hmem := hpsi_mem_Pi v
    have hsmem : s (psi v) ∈ P i := by rw [hsP i hij (psi v) hmem]; exact hmem
    have hgmem : g (s (psi v)) ∈ P i := hPig _ hsmem
    rw [hpsi_apply, hfP i hij (s (psi v)) hsmem,
      hfP i hij (g (s (psi v))) hgmem, zero_smul, zero_smul, add_zero]
  have hpsi_fix : ∀ l ∈ fixSp g, psi l = 0 := by
    intro l hl
    have hlV0 : l ∈ V0 := hfixV0 ▸ hl
    have hsl : s l = l := hsV0 l hlV0
    have hgl : g l = l := mem_fixSp.1 hl
    rw [hpsi_apply, hsl, hgl, hfV0 l hlV0, zero_smul, zero_smul, add_zero]
  have hpsi_comm : ∀ v, psi (g v) = g (psi v) := by
    intro v
    have hsgs : s (g v) = h (s v) := by
      rw [hh]
      simp
    have h1 : f (s v) + f (h (s v)) + f (g (s v)) = 0 := by
      simpa only [map_add] using hid1 (s v)
    have h2 : f (s v) + f (g (h (s v))) = 0 := by
      have := hid2 (s v)
      simpa only [map_add, LinearEquiv.mul_apply] using this
    have hrearr : (f (h (s v)) • g a + f (g (h (s v))) • a)
        + (f (s v) • g (g a) + f (g (s v)) • g a)
        = (f (s v) + f (h (s v)) + f (g (s v))) • g a
          + (f (s v) + f (g (h (s v)))) • a := by
      rw [hg2a', smul_add, add_smul, add_smul, add_smul]
      abel
    have hsum0 : psi (g v) + g (psi v) = 0 := by
      rw [hpsi_apply (g v), hpsi_apply v, hsgs, map_add, map_smul, map_smul,
        hrearr, h1, h2, zero_smul, zero_smul, add_zero]
    have h : psi (g v) + g (psi v) = g (psi v) + g (psi v) := by
      rw [hsum0, S172A.GL.add_self_V]
    exact add_right_cancel h
  set T : V ≃ₗ[ZMod 2] V := s⁻¹ * Aanti * s with hT
  have hT_apply : ∀ v, T v = v + psi v := by
    intro v
    have hsv : s⁻¹ (s v) = v := by
      have h : (s⁻¹ * s : V ≃ₗ[ZMod 2] V) v = v := by rw [inv_mul_cancel]; rfl
      rw [LinearEquiv.mul_apply] at h
      exact h
    rw [hT, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hAanti_apply (s v), twoOddAnti_apply]
    rw [map_add, hsv, map_add, map_smul, map_smul,
      S172A.GL.inv_apply_of_fix (hsP i hij (g a) hga),
      S172A.GL.inv_apply_of_fix (hsP i hij a ha), hpsi_apply v]
  have hT_cent : T ∈ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply LinearEquiv.ext
    intro v
    change T (g v) = g (T v)
    rw [hT_apply (g v), hT_apply v, map_add]
    congr 1
    exact hpsi_comm v
  have hT_fix : ∀ l ∈ fixSp g, T l = l := by
    intro l hl
    rw [hT_apply l, hpsi_fix l hl, add_zero]
  have hT_sq : T * T = 1 := by
    have hAanti_sq : Aanti * Aanti = 1 := by
      apply LinearEquiv.ext
      intro v
      rw [LinearEquiv.mul_apply, hAanti_apply (Aanti v), hAanti_apply v, map_add, hanti_sq v,
        add_zero, add_assoc, S172A.GL.add_self_V, add_zero]
      rfl
    rw [hT, show s⁻¹ * Aanti * s * (s⁻¹ * Aanti * s) = s⁻¹ * (Aanti * Aanti) * s by group,
      hAanti_sq]
    group
  have hT_in : T ∈ stdLayer g := hFstd (hFinv T hT_cent hT_fix hT_sq)
  have hAanti_in : Aanti ∈ innerClosure A g := by
    rw [innerClosure]
    have heq : Aanti = s * T * s⁻¹ := by rw [hT]; group
    rw [heq]
    exact conj_mem_closureIn' hsN hT_in
  have hfactor : S172A.GL.tv a f hfa = Alin * Aanti := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, hAlin_apply (Aanti v), hAanti_apply v, S172A.GL.tv_apply,
      map_add, hlin_anti v, add_zero]
    have hsumlin : twoOddLin g a f v + twoOddAnti g a f v = f v • a := by
      simp only [← LinearMap.add_apply, hlin_anti_sum, LinearMap.smulRight_apply]
    rw [show (v + twoOddAnti g a f v) + twoOddLin g a f v
        = v + (twoOddLin g a f v + twoOddAnti g a f v) by abel, hsumlin]
  rw [hfactor]
  exact mul_mem hAlin_in hAanti_in

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
