module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Centralizer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannA3
import CFSG.Quasithin.EmptyFaithful.A10ConfigurationSetup

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

omit [Finite Ω] in
open scoped Pointwise in
private theorem exists_conj_eq_mul_g45ld {V Q A B : Subgroup Ω}
    (hB : B = V ⊔ (Q ⊓ A)) (hA : IsElemAbelian 2 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set Ω)) {a b : Ω} (ha : a ∈ A) (hb : b ∈ B) :
    ∃ v ∈ V, a * b * a⁻¹ = v * b := by
  have hQV : Q ⊓ A ≤ Subgroup.normalizer (V : Set Ω) := inf_le_right.trans hAV
  have hset : ((V ⊔ (Q ⊓ A) : Subgroup Ω) : Set Ω) =
      (V : Set Ω) * ((Q ⊓ A : Subgroup Ω) : Set Ω) :=
    Subgroup.coe_mul_of_right_le_normalizer_left V (Q ⊓ A) hQV
  have hb' : b ∈ (V : Set Ω) * ((Q ⊓ A : Subgroup Ω) : Set Ω) := by
    rw [← hset]
    exact hB ▸ hb
  rw [Set.mem_mul] at hb'
  obtain ⟨v, hv, k, hk, rfl⟩ := hb'
  have hav : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV ha) v).mp hv
  have hcomm : a * k = k * a := IsElemAbelian.comm hA ha hk.2
  refine ⟨(a * v * a⁻¹) * v⁻¹, V.mul_mem hav (V.inv_mem hv), ?_⟩
  calc a * (v * k) * a⁻¹ = (a * v * a⁻¹) * (a * k * a⁻¹) := by group
    _ = (a * v * a⁻¹) * k := by rw [hcomm]; group
    _ = (a * v * a⁻¹) * v⁻¹ * (v * k) := by group

omit [Finite Ω] in
private theorem conj_mem_normalizer_g45ld {A V Z B W : Subgroup Ω} {g a : Ω}
    (hW : W = V ⊔ Z) (hZB : Z ≤ B.map (MulAut.conj g).toMonoidHom)
    (hkey : ∀ x ∈ A, ∀ b ∈ B, ∃ v ∈ V, x * b * x⁻¹ = v * b)
    (hAV : A ≤ Subgroup.normalizer (V : Set Ω))
    (hgV : g ∈ Subgroup.normalizer (V : Set Ω)) (ha : a ∈ A) :
    g * a * g⁻¹ ∈ Subgroup.normalizer (W : Set Ω) := by
  have hmem : ∀ x ∈ A, g * x * g⁻¹ ∈ Subgroup.normalizer (V : Set Ω) := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgV (hAV hx)) (Subgroup.inv_mem _ hgV)
  have hstep : ∀ x ∈ A, ∀ w ∈ W, MulAut.conj (g * x * g⁻¹) w ∈ W := by
    intro x hx w hw
    rw [hW] at hw ⊢
    have hsup : V ⊔ Z ≤ (V ⊔ Z).comap (MulAut.conj (g * x * g⁻¹)).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro v hv
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (by
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
            (Subgroup.mem_normalizer_iff.mp (hmem x hx) v).mp hv)
      · intro z hz
        rw [Subgroup.mem_comap]
        obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp (hZB hz)
        obtain ⟨v, hv, hvx⟩ := hkey x hx b hb
        have hzv : MulAut.conj (g * x * g⁻¹) z = (g * v * g⁻¹) * z := by
          rw [← hbz]
          calc MulAut.conj (g * x * g⁻¹) ((MulAut.conj g).toMonoidHom b)
              = g * (x * b * x⁻¹) * g⁻¹ := by
                simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
            _ = g * (v * b) * g⁻¹ := by rw [hvx]
            _ = (g * v * g⁻¹) * (MulAut.conj g).toMonoidHom b := by
                simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
        change MulAut.conj (g * x * g⁻¹) z ∈ V ⊔ Z
        rw [hzv]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hgV v).mp hv))
          (Subgroup.mem_sup_right hz)
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] using hsup hw
  rw [Subgroup.mem_normalizer_iff]
  refine fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hstep a ha w hw
  · have hw' : MulAut.conj (g * a * g⁻¹) w ∈ W := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hw
    have h := hstep a⁻¹ (A.inv_mem ha) _ hw'
    rwa [show MulAut.conj (g * a⁻¹ * g⁻¹) (MulAut.conj (g * a * g⁻¹) w) = w by
      simp only [MulAut.conj_apply]; group] at h

private theorem le_normalizer_sup_sylow_g45ld (h : GomiThm45Counterexample c G S) :
    S ≤ Subgroup.normalizer
      ((gomiV G ⊔ omegaOneCenterOf (thompsonJ S) : Subgroup Ω) : Set Ω) := by
  have hSG : S ≤ G := h.isSylowTwoOf.1
  refine (le_inf (hSG.trans (gomiV_moduleSetting G).2) ?_).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (gomiV G) _)
  exact (Subgroup.le_normalizer.trans
    (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ S)).trans
    (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
      CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv (thompsonJ S))

theorem le_normalizer_gomiV_sup (h : GomiThm45Counterexample c G S) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) (hS : pCoreOf 2 G ⊔ A = S)
    (hB : IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A))) {g : Ω} (hg : g ∈ G)
    (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G) :
    G ≤ Subgroup.normalizer
      ((gomiV G ⊔ omegaOneCenterOf (thompsonJ S) : Subgroup Ω) : Set Ω) := by
  have hSG : S ≤ G := h.isSylowTwoOf.1
  have hQS : pCoreOf 2 G ≤ S :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hQmap : (pCoreOf 2 G).map (MulAut.conj g).toMonoidHom = pCoreOf 2 G :=
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) hg)
  have hGNW : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hAV : A ≤ Subgroup.normalizer (gomiV G : Set Ω) := hA.1.trans (hSG.trans hGNW)
  have hBQ : gomiV G ⊔ (pCoreOf 2 G ⊓ A) ≤ pCoreOf 2 G :=
    sup_le (gomiV_le_pCoreOf G) inf_le_left
  have hB' := CFSG.Quasithin.A10.isMaxElemAbelian_map_conj hB g
    ((Subgroup.map_mono hBQ).trans
      ((le_of_eq (CFSG.Quasithin.map_conj_eq_of_mem_normalizer
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) hg))).trans hQS))
  have hZB : omegaOneCenterOf (thompsonJ S) ≤
      (gomiV G ⊔ (pCoreOf 2 G ⊓ A)).map (MulAut.conj g).toMonoidHom :=
    C56.omegaOneCenter_thompsonJ_le hB'
  have hkey : ∀ x ∈ A, ∀ b ∈ (gomiV G ⊔ (pCoreOf 2 G ⊓ A)),
      ∃ v ∈ gomiV G, x * b * x⁻¹ = v * b :=
    fun x hx b hb => exists_conj_eq_mul_g45ld (Q := pCoreOf 2 G) rfl hA.2.1 hAV hx hb
  have hSNW : S ≤ Subgroup.normalizer
      ((gomiV G ⊔ omegaOneCenterOf (thompsonJ S) : Subgroup Ω) : Set Ω) :=
    le_normalizer_sup_sylow_g45ld h
  have hAgNW : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer
      ((gomiV G ⊔ omegaOneCenterOf (thompsonJ S) : Subgroup Ω) : Set Ω) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hnor := conj_mem_normalizer_g45ld (W := gomiV G ⊔ omegaOneCenterOf (thompsonJ S))
      rfl hZB hkey hAV (hGNW hg) ha
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hnor w).mp hw
  have hSgNW : S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer
      ((gomiV G ⊔ omegaOneCenterOf (thompsonJ S) : Subgroup Ω) : Set Ω) := by
    calc S.map (MulAut.conj g).toMonoidHom
        = ((pCoreOf 2 G ⊔ A).map (MulAut.conj g).toMonoidHom) := by rw [hS]
      _ = (pCoreOf 2 G).map (MulAut.conj g).toMonoidHom ⊔
          A.map (MulAut.conj g).toMonoidHom := Subgroup.map_sup _ _ _
      _ = pCoreOf 2 G ⊔ A.map (MulAut.conj g).toMonoidHom := by rw [hQmap]
      _ ≤ _ := sup_le (hQS.trans hSNW) hAgNW
  calc G = S ⊔ S.map (MulAut.conj g).toMonoidHom := hG.symm
    _ ≤ _ := sup_le hSNW hSgNW

private theorem le_centralizer_omegaOneCenter_g45ld {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) :
    A ≤ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set Ω) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (IsElemAbelian.comm hA.2.1 ha (C56.omegaOneCenter_thompsonJ_le hA hz)).symm

private theorem le_centralizer_inf_g45ld {A : Subgroup Ω} (hA : IsMaxElemAbelian S A) {g : Ω} :
    A ≤ Subgroup.centralizer
      ((omegaOneCenterOf (thompsonJ S) ⊓
        (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom :
          Subgroup Ω) : Set Ω) :=
  (le_centralizer_omegaOneCenter_g45ld hA).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))

private theorem map_conj_le_centralizer_inf_g45ld {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) {g : Ω} :
    A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer
      ((omegaOneCenterOf (thompsonJ S) ⊓
        (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom :
          Subgroup Ω) : Set Ω) := by
  refine (Subgroup.map_mono (le_centralizer_omegaOneCenter_g45ld hA)).trans ?_
  refine (Subgroup.map_centralizer_le_centralizer_image
    (omegaOneCenterOf (thompsonJ S) : Set Ω) (MulAut.conj g).toMonoidHom).trans ?_
  refine Subgroup.centralizer_le ?_
  simp only [Subgroup.coe_inf, Subgroup.coe_map]
  exact inf_le_right

private theorem le_normalizer_inf_g45ld (h : GomiThm45Counterexample c G S)
    {A : Subgroup Ω} (hA : IsMaxElemAbelian S A) (hS : pCoreOf 2 G ⊔ A = S) {g : Ω}
    (hg : g ∈ G) (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G) :
    G ≤ Subgroup.normalizer
      ((omegaOneCenterOf (thompsonJ S) ⊓
        (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom :
          Subgroup Ω) : Set Ω) := by
  set Z : Subgroup Ω := omegaOneCenterOf (thompsonJ S) with hZ
  set Zg : Subgroup Ω := Z.map (MulAut.conj g).toMonoidHom with hZg
  have hQS : pCoreOf 2 G ≤ S :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hQmap : (pCoreOf 2 G).map (MulAut.conj g).toMonoidHom = pCoreOf 2 G :=
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) hg)
  have hSNZ : S ≤ Subgroup.normalizer (Z : Set Ω) :=
    (Subgroup.le_normalizer.trans
      (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ S)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
        CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv (thompsonJ S))
  have hSZg : S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Zg : Set Ω) := by
    rw [← Subgroup.map_equiv_normalizer_eq Z (MulAut.conj g)]
    exact Subgroup.map_mono hSNZ
  have hQSg : pCoreOf 2 G ≤ S.map (MulAut.conj g).toMonoidHom := by
    rw [← hQmap]
    exact Subgroup.map_mono hQS
  have hQNY : pCoreOf 2 G ≤ Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) :=
    (le_inf (hQS.trans hSNZ) (hQSg.trans hSZg)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hANY : A ≤ Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) :=
    (le_centralizer_inf_g45ld hA).trans
      (Subgroup.centralizer_le_normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω))
  have hAgNY : A.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) :=
    (map_conj_le_centralizer_inf_g45ld hA).trans
      (Subgroup.centralizer_le_normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω))
  have hSg : S.map (MulAut.conj g).toMonoidHom =
      pCoreOf 2 G ⊔ A.map (MulAut.conj g).toMonoidHom := by
    rw [← hS, Subgroup.map_sup, hQmap]
  have hSNY : S ≤ Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) := by
    rw [← hS]
    exact sup_le hQNY hANY
  have hSgNY : S.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) := by
    rw [hSg]
    exact sup_le hQNY hAgNY
  calc G = S ⊔ S.map (MulAut.conj g).toMonoidHom := hG.symm
    _ ≤ _ := sup_le hSNY hSgNY

omit [Finite Ω] in
private theorem conjClosure_baum_le_centralizer_g45ld {Y : Subgroup Ω}
    (hY : G ≤ Subgroup.normalizer (Y : Set Ω))
    (hbaum : baum S ≤ Subgroup.centralizer (Y : Set Ω)) :
    conjClosure (baum S) G ≤ Subgroup.centralizer (Y : Set Ω) :=
  CFSG.Quasithin.conjClosure_le fun x hx k hk => by
    have hkY : k ∈ Subgroup.centralizer (Y : Set Ω) := hbaum hk
    rw [Subgroup.mem_centralizer_iff] at hkY ⊢
    intro y hy
    have hxy : x⁻¹ * y * x ∈ Y := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hY hx)) y).mp hy
      simpa using h
    have hcomm : (x⁻¹ * y * x) * k = k * (x⁻¹ * y * x) := hkY _ hxy
    calc y * (x * k * x⁻¹) = x * ((x⁻¹ * y * x) * k) * x⁻¹ := by group
      _ = x * (k * (x⁻¹ * y * x)) * x⁻¹ := by rw [hcomm]
      _ = x * k * x⁻¹ * y := by group

theorem inf_map_conj_le_centralizer (h : GomiThm45Counterexample c G S) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) (hS : pCoreOf 2 G ⊔ A = S) {g : Ω} (hg : g ∈ G)
    (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G) (hi : G ≤ conjClosure (baum S) G) :
    omegaOneCenterOf (thompsonJ S) ⊓
        (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (G : Set Ω) := by
  set Z : Subgroup Ω := omegaOneCenterOf (thompsonJ S) with hZ
  set Zg : Subgroup Ω := Z.map (MulAut.conj g).toMonoidHom with hZg
  have hGNY : G ≤ Subgroup.normalizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) :=
    le_normalizer_inf_g45ld h hA hS hg hG
  have hbaum : baum S ≤ Subgroup.centralizer ((Z ⊓ Zg : Subgroup Ω) : Set Ω) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hk.2) y hy.1
  have hcl := conjClosure_baum_le_centralizer_g45ld (S := S) hGNY hbaum
  exact Subgroup.le_centralizer_iff.mpr (hi.trans hcl)

end CFSG.GroupTheory.GomiThm45Counterexample
