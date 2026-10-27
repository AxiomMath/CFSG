module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathHyp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

namespace WreathHyp

variable {H : Type*} [Group H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

include h

@[expose] def B : Subgroup (MulAut ↥W) := @baseGp ↥W h.cg (Fin r) (planesIn W I)

@[expose] noncomputable def D : Subgroup (MulAut ↥W) := @cubeBase ↥W h.cg (Fin r) (planesIn W I) h.planeFamily

@[expose] noncomputable def Dat (i : Fin r) : Subgroup (MulAut ↥W) :=
  @cubeAt ↥W h.cg (Fin r) (planesIn W I) h.planeFamily i

end WreathHyp

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

theorem rho_map_odd : (oddOrderSubgroup (⊤ : Subgroup H)).map h.rho = h.D := by
  let _ := h.cg
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply oddOrderSubgroup_le_of_pow_mem
    intro x _
    have hx : h.rho x ∈ wreathAut h.planeFamily Pm := by
      rw [← h.rho_range]
      exact ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_two_pow_mem_cubeBase h.planeFamily h.Pm_two hx
    exact ⟨m, by rw [Subgroup.mem_comap, map_pow]; exact hm⟩
  · intro d hd
    have hdB : d ∈ baseGp (planesIn W I) := cubeBase_le_baseGp h.planeFamily hd
    have hdr : d ∈ h.rho.range := by
      rw [h.rho_range]
      exact baseGp_le_wreathAut h.planeFamily Pm hdB
    obtain ⟨x, rfl⟩ := hdr
    have h3 : h.rho x ^ 3 = 1 := pow_three_of_mem_cubeBase h.planeFamily hd
    have hodd : Odd (orderOf (h.rho x)) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hy : x ^ 2 ^ a ∈ oddOrderSubgroup (⊤ : Subgroup H) := by
      apply Subgroup.subset_closure
      refine ⟨Subgroup.mem_top _, ?_⟩
      have hdvd : 2 ^ a ∣ orderOf x := ⟨b, hab⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab,
        Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
      exact hb
    exact mem_of_odd_orderOf_of_pow_mem (k := a) hodd ⟨x ^ 2 ^ a, hy, map_pow _ _ _⟩

omit [Finite H] in
theorem V_isPGroup : IsPGroup 2 ↥V := fun g => ⟨1, Subtype.ext (by
  simpa using h.V_elem.2 g g.2)⟩

omit [Finite H] in
theorem V_le_R : V ≤ R := by
  have hVn := h.V_normal
  have h1 : V ≤ CFSG.Open.pCore 2 H := CFSG.LieType.BorelTits.le_pCore 2 hVn h.V_isPGroup
  have h2 : CFSG.Open.pCoreOf 2 (⊤ : Subgroup H) ≤ R := h.sylow.pCoreOf_le
  rw [CFSG.Quasithin.B6.pCoreOf_top] at h2
  exact h1.trans h2

omit [Finite H] in
theorem conj_planes_of_rho_mem_B {n : H} (hn : h.rho n ∈ h.B) :
    ∀ i, (I i).map (MulAut.conj n).toMonoidHom = I i := by
  let _ := h.cg
  intro i
  have hcond := (smul_planes_iff (h.rho n) i i).mp ((mem_baseGp.mp hn) i)
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (hcond ⟨y, h.I_le i hy⟩).mpr hy
    rwa [h.rho_apply] at this
  · intro hz
    have hzW : z ∈ W := h.I_le i hz
    have hyW : n⁻¹ * z * n ∈ W := by simpa using h.W_normal.conj_mem z hzW n⁻¹
    refine ⟨n⁻¹ * z * n, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    refine (hcond ⟨n⁻¹ * z * n, hyW⟩).mp ?_
    rw [h.rho_apply]
    simpa [mul_assoc] using hz

theorem rho_mem_B_of_mem_odd {n : H} (hn : n ∈ oddOrderSubgroup (⊤ : Subgroup H)) :
    h.rho n ∈ h.B := by
  let _ := h.cg
  have : h.rho n ∈ (oddOrderSubgroup (⊤ : Subgroup H)).map h.rho := ⟨n, hn, rfl⟩
  rw [h.rho_map_odd] at this
  exact cubeBase_le_baseGp h.planeFamily this

theorem odd_centralizes_F {n : H} (hn : n ∈ oddOrderSubgroup (⊤ : Subgroup H)) {f : H}
    (hf : f ∈ F) : n * f = f * n :=
  h.centralizes n (h.conj_planes_of_rho_mem_B (h.rho_mem_B_of_mem_odd hn)) f hf

omit [Finite H] h in
theorem normal_le_normalizer' {K : Subgroup H} (hK : K.Normal) (S : Subgroup H) :
    S ≤ Subgroup.normalizer (K : Set H) := fun g _ => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hK.conj_mem y hy g, fun hy => ?_⟩
  simpa [mul_assoc] using hK.conj_mem _ hy g⁻¹

omit [Finite H] in
theorem centralizer_W_eq_V :
    Subgroup.centralizer (W : Set H) = Subgroup.centralizer (V : Set H) := by
  apply le_antisymm
  · intro x hx
    have hxB : ∀ i, (I i).map (MulAut.conj x).toMonoidHom = I i := by
      intro i
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        have e : (MulAut.conj x).toMonoidHom y = y := by
          have := Subgroup.mem_centralizer_iff.mp hx y (h.I_le i hy)
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← this]
          group
        rw [e]
        exact hy
      · intro hz
        refine ⟨z, hz, ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hx z (h.I_le i hz)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← this]
        group
    have hF := h.centralizes x hxB
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ W ⊔ F := h.W_sup_F ▸ hv
    obtain ⟨w, hw, f, hf, rfl⟩ :=
      CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul (normal_le_normalizer' h.W_normal F) hv'
    have h1 := Subgroup.mem_centralizer_iff.mp hx w hw
    calc w * f * x = w * (f * x) := mul_assoc _ _ _
      _ = w * (x * f) := by rw [hF f hf]
      _ = (w * x) * f := (mul_assoc _ _ _).symm
      _ = (x * w) * f := by rw [h1]
      _ = x * (w * f) := mul_assoc _ _ _
  · exact Subgroup.centralizer_le (by exact_mod_cast h.W_le)

theorem commutator_V_N : ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ = W := by
  let _ := h.cg
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv n hn
    have hv' : v ∈ W ⊔ F := h.W_sup_F ▸ hv
    obtain ⟨w, hw, f, hf, rfl⟩ :=
      CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul (normal_le_normalizer' h.W_normal F) hv'
    have hfn := h.odd_centralizes_F hn hf
    have e : ⁅w * f, n⁆ = w * (n * w⁻¹ * n⁻¹) := by
      calc ⁅w * f, n⁆ = w * (f * n * f⁻¹) * w⁻¹ * n⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = w * n * w⁻¹ * n⁻¹ := by rw [show f * n * f⁻¹ = n by rw [← hfn]; group]
        _ = w * (n * w⁻¹ * n⁻¹) := by group
    rw [e]
    exact W.mul_mem hw (by simpa using h.W_normal.conj_mem w⁻¹ (W.inv_mem hw) n)
  · rw [← h.I_sup]
    refine iSup_le fun i => ?_
    intro x hx
    obtain ⟨d, hd, hnt⟩ := exists_cubeAt_nontrivial h.planeFamily i
    have hdD : d ∈ h.D := cubeAt_le_cubeBase h.planeFamily i hd
    rw [← h.rho_map_odd] at hdD
    obtain ⟨n, hn, hnd⟩ := hdD
    obtain ⟨y, hy, hdy⟩ :=
      exists_div_eq_of_cubeAt h.planeFamily hd hnt (x := (⟨x, h.I_le i hx⟩ : ↥W)) hx
    have hyV : (y : H) ∈ V := h.W_le y.2
    have e1 : ((d y : ↥W) : H) = n * (y : H) * n⁻¹ := by
      rw [← hnd]
      exact h.rho_apply n y
    have e2 : ((d y * y⁻¹ : ↥W) : H) = x := congrArg Subtype.val hdy
    have key : ⁅n, (y : H)⁆ = x := by
      rw [commutatorElement_def, ← e1]
      simpa using e2
    have hmem : ⁅n, (y : H)⁆ ∈ ⁅oddOrderSubgroup (⊤ : Subgroup H), V⁆ :=
      Subgroup.commutator_mem_commutator hn hyV
    rw [Subgroup.commutator_comm, key] at hmem
    exact hmem

theorem F_eq_centralizer :
    F = V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H) := by
  let _ := h.cg
  apply le_antisymm
  · intro f hf
    refine ⟨h.F_le hf, Subgroup.mem_centralizer_iff.mpr fun n hn => h.odd_centralizes_F hn hf⟩
  · rintro v ⟨hv, hvc⟩
    have hv' : v ∈ W ⊔ F := h.W_sup_F ▸ hv
    obtain ⟨w, hw, f, hf, rfl⟩ :=
      CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul (normal_le_normalizer' h.W_normal F) hv'
    have hwfix : ∀ n ∈ oddOrderSubgroup (⊤ : Subgroup H), n * w = w * n := by
      intro n hn
      have h1 := Subgroup.mem_centralizer_iff.mp hvc n hn
      have h2 := h.odd_centralizes_F hn hf
      have : n * w * f = w * n * f := by
        calc n * w * f = n * (w * f) := mul_assoc _ _ _
          _ = (w * f) * n := h1
          _ = w * (f * n) := mul_assoc _ _ _
          _ = w * (n * f) := by rw [h2]
          _ = w * n * f := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    have hw1 : (⟨w, hw⟩ : ↥W) = 1 := by
      apply eq_one_of_fixed_cubeAt h.planeFamily
      intro i d hd
      have hdD : d ∈ h.D := cubeAt_le_cubeBase h.planeFamily i hd
      rw [← h.rho_map_odd] at hdD
      obtain ⟨n, hn, rfl⟩ := hdD
      apply Subtype.ext
      rw [h.rho_apply]
      have := hwfix n hn
      calc n * w * n⁻¹ = w * n * n⁻¹ := by rw [this]
        _ = w := by group
    have : w = 1 := congrArg Subtype.val hw1
    rw [this, one_mul]
    exact hf

omit [Finite H] h in
theorem oddOrderSubgroup_top_normal : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup H)
    (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup H) : Set H))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem W_le_blockQ_odd : W ≤ blockQ (oddOrderSubgroup (⊤ : Subgroup H)) := by
  have hNn := oddOrderSubgroup_top_normal (H := H)
  have hWN : W ≤ oddOrderSubgroup (⊤ : Subgroup H) := by
    rw [← h.commutator_V_N]
    exact Subgroup.commutator_le_right _ _
  have hnormal : (W.subgroupOf (oddOrderSubgroup (⊤ : Subgroup H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr
      (normal_le_normalizer' h.W_normal _)
  have hW2 : IsPGroup 2 ↥W := fun g => ⟨1, Subtype.ext (by simpa using h.W_elem.2 g g.2)⟩
  exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hWN hnormal hW2

theorem not_top_le_centralizer_V : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H) := by
  let _ := h.cg
  intro htop
  let i0 : Fin r := ⟨0, h.r_pos⟩
  obtain ⟨d, hd, x, hx, hdx⟩ := exists_cubeAt_nontrivial h.planeFamily i0
  have hdD : d ∈ h.D := cubeAt_le_cubeBase h.planeFamily i0 hd
  rw [← h.rho_map_odd] at hdD
  obtain ⟨n, -, rfl⟩ := hdD
  apply hdx
  have hxV : (x : H) ∈ V := h.W_le x.2
  have := Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top n)) x hxV
  apply Subtype.ext
  rw [h.rho_apply, ← this]
  group

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
