module

public import CFSG.GH74.GLS.IVK.Defs
import CFSG.GH74.GLS.IVK.L2.Lemma12
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PEF8A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK

private noncomputable abbrev sec5pef_psi {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) : CFSG.GorensteinWalter.PGL2 F ≃* ↥(innDiagSub e) :=
  MonoidHom.ofInjective (innDiagHom_injective e)

private lemma sec5pef_psi_coe
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    (g : CFSG.GorensteinWalter.PGL2 F) :
    ((sec5pef_psi e g : ↥(innDiagSub e)) : MulAut K) = innDiagHom e g :=
  MonoidHom.ofInjective_apply (innDiagHom_injective e)

private lemma sec5pef_psi_symm_coe
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    (z : ↥(innDiagSub e)) :
    innDiagHom e ((sec5pef_psi e).symm z) = (z : MulAut K) :=
  MonoidHom.apply_ofInjective_symm (innDiagHom_injective e) z

private lemma sec5pef_psi_symm_coe_self
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    {y : MulAut K} (hy : y ∈ innDiagSub e) :
    innDiagHom e ((sec5pef_psi e).symm ⟨y, hy⟩) = y :=
  sec5pef_psi_symm_coe e ⟨y, hy⟩

private lemma sec5pef_innDiagHom_toPGL_toPSL
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F) (k : K) :
    innDiagHom e (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
        (toPSL e k)) = MulAut.conj k := by
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom]
  simp [MulAut.conj_apply]

private lemma sec5pef_conj_symm_toPSL
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    (x : CFSG.GorensteinWalter.PSL2 F) :
    MulAut.conj ((toPSL e).symm x) =
      innDiagHom e (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x) := by
  rw [← sec5pef_innDiagHom_toPGL_toPSL e ((toPSL e).symm x), (toPSL e).apply_symm_apply x]

private lemma sec5pef_innDiagHom_mem_centralizer
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    {y : MulAut K} (hy : y ∈ innDiagSub e) {g : CFSG.GorensteinWalter.PGL2 F}
    (hg : g ∈ Subgroup.centralizer
      ({(sec5pef_psi e).symm ⟨y, hy⟩} : Set (CFSG.GorensteinWalter.PGL2 F))) :
    innDiagHom e g ∈ Subgroup.centralizer ({y} : Set (MulAut K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  rw [← sec5pef_psi_symm_coe_self e hy, ← map_mul, ← map_mul, hg]

private lemma sec5pef_centralizer_transport
    {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)
    {y : MulAut K} (hy : y ∈ innDiagSub e) :
    (Subgroup.centralizer
        ({(sec5pef_psi e).symm ⟨y, hy⟩} : Set (CFSG.GorensteinWalter.PGL2 F))).map
      (sec5pef_psi e).toMonoidHom =
      (Subgroup.centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e).subgroupOf
        (innDiagSub e) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, (sec5pef_psi e h).2⟩
    change (↑(sec5pef_psi e h) : MulAut K) ∈
      Subgroup.centralizer ({y} : Set (MulAut K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hh' : h * (sec5pef_psi e).symm ⟨y, hy⟩ =
        (sec5pef_psi e).symm ⟨y, hy⟩ * h := by
      simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hh
    rw [sec5pef_psi_coe, ← sec5pef_psi_symm_coe_self e hy, ← map_mul, ← map_mul, hh']
  · intro hz
    refine ⟨(sec5pef_psi e).symm g, ?_, (sec5pef_psi e).apply_symm_apply g⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hzcent : (g : MulAut K) * y = y * (g : MulAut K) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hz).1
    apply (innDiagHom_injective e)
    rw [map_mul, map_mul, sec5pef_psi_symm_coe, sec5pef_psi_symm_coe]
    exact hzcent

theorem sec5pef_involution_centralizer
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] (e : K ≃* L2 F)
    {y : MulAut K} (hy : y ∈ innDiagSub e) (hy2 : orderOf y = 2) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∃ n : ℕ, (n : ℤ) = (Nat.card F : ℤ) - δ ∧
      Nonempty (↥(Subgroup.centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e) ≃*
        DihedralGroup n) ∧
      ∃ C : Subgroup (MulAut K), C ≤ Subgroup.centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e ∧
        IsCyclic C ∧ Nat.card C = n ∧ ∀ c ∈ C, Odd (orderOf c) → c ∈ innAut K := by
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    isOddPrimePower_of_L2Field hF
  have hcard : 3 < Nat.card F := hF.2
  let S : Subgroup (MulAut K) :=
    Subgroup.centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e
  let y' : CFSG.GorensteinWalter.PGL2 F := (sec5pef_psi e).symm ⟨y, hy⟩
  have hy'2 : orderOf y' = 2 := by
    rw [← orderOf_injective (innDiagHom e) (innDiagHom_injective e) y',
      sec5pef_psi_symm_coe_self e hy]
    exact hy2
  obtain ⟨δ, hδ, n, hn, ⟨D⟩, C', hC'le, hC'cyc, hC'card, hC'odd⟩ :=
    sec5pef_pgl2_involution_centralizer hK hcard hy'2
  have hmap : S.subgroupOf (innDiagSub e) =
      (Subgroup.centralizer ({y'} : Set (CFSG.GorensteinWalter.PGL2 F))).map
        (sec5pef_psi e).toMonoidHom := by
    simpa only [S, y'] using (sec5pef_centralizer_transport e hy).symm
  let C : Subgroup (MulAut K) := C'.map (innDiagHom e)
  refine ⟨δ, hδ, n, hn, ?_, C, ?_, ?_, ?_, ?_⟩
  · exact ⟨((Subgroup.subgroupOfEquivOfLe (show S ≤ innDiagSub e from inf_le_right)).symm).trans
      ((MulEquiv.subgroupCongr hmap).trans
        (((MulEquiv.subgroupMap (sec5pef_psi e)
          (Subgroup.centralizer ({y'} : Set (CFSG.GorensteinWalter.PGL2 F)))).symm).trans D))⟩
  · intro c hc
    rcases Subgroup.mem_map.mp hc with ⟨g, hg, rfl⟩
    exact ⟨sec5pef_innDiagHom_mem_centralizer e hy (hC'le hg), ⟨g, rfl⟩⟩
  · exact ((C'.equivMapOfInjective (innDiagHom e) (innDiagHom_injective e)).isCyclic).mp hC'cyc
  · rw [← Nat.card_congr
        (C'.equivMapOfInjective (innDiagHom e) (innDiagHom_injective e)).toEquiv, hC'card]
  · intro c hc hodd
    rcases Subgroup.mem_map.mp hc with ⟨g, hg, rfl⟩
    have hg_odd : Odd (orderOf g) := by
      rwa [← orderOf_injective (innDiagHom e) (innDiagHom_injective e) g]
    rcases hC'odd g hg hg_odd with ⟨x, rfl⟩
    exact ⟨(toPSL e).symm x, sec5pef_conj_symm_toPSL e x⟩

theorem sec5pef_exists_fixed_of_prime_dvd
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] (e : K ≃* L2 F)
    {y : MulAut K} (hy : y ∈ innDiagSub e) (hy2 : orderOf y = 2) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∀ s : ℕ, s.Prime → s ≠ 2 → (s : ℤ) ∣ (Nat.card F : ℤ) - δ →
      ∃ w : K, orderOf w = s ∧ y w = w := by
  obtain ⟨δ, hδ, n, hn, _hiso, C, hCle, _hCcyc, hCcard, hCodd⟩ :=
    sec5pef_involution_centralizer hF e hy hy2
  refine ⟨δ, hδ, ?_⟩
  intro s hs hs2 hsdiv
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Finite (CFSG.GorensteinWalter.PGL2 F) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* CFSG.GorensteinWalter.PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  have hCle' : C ≤ innDiagSub e := le_trans hCle inf_le_right
  haveI : Finite ↥(innDiagSub e) :=
    Finite.of_equiv (CFSG.GorensteinWalter.PGL2 F) (innDiagEquiv e).toEquiv.symm
  haveI : Finite ↥C :=
    Finite.of_equiv ↥(C.subgroupOf (innDiagSub e))
      (Subgroup.subgroupOfEquivOfLe hCle').toEquiv
  have hdivn : s ∣ n := by
    apply Int.natCast_dvd_natCast.mp
    rw [hn]
    exact hsdiv
  have hdvdC : s ∣ Nat.card ↥C := by
    rw [hCcard]
    exact hdivn
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) s hdvdC
  have hcS : (c : MulAut K) ∈
      Subgroup.centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e := hCle c.2
  have hc_cent : (c : MulAut K) * y = y * (c : MulAut K) :=
    Subgroup.mem_centralizer_singleton_iff.mp hcS.1
  have hodd_c : Odd (orderOf (c : MulAut K)) := by
    rw [Subgroup.orderOf_coe, hc]
    exact hs.odd_of_ne_two hs2
  have hinner : (c : MulAut K) ∈ innAut K := hCodd (c : MulAut K) c.2 hodd_c
  rcases hinner with ⟨w, hw⟩
  refine ⟨w, ?_, ?_⟩
  · have h1 : orderOf (MulAut.conj w) = orderOf w :=
      orderOf_injective (MulAut.conj : K →* MulAut K) (conj_injective_of_L2 e) w
    rw [← h1, hw, Subgroup.orderOf_coe, hc]
  · have hconj : MulAut.conj (y w) = MulAut.conj w := by
      have h1 : MulAut.conj (y w) = y * MulAut.conj w * y⁻¹ := by
        ext x
        simp [MulAut.conj_apply, map_mul]
      rw [h1, hw, mul_inv_eq_iff_eq_mul]
      exact hc_cent.symm
    exact conj_injective_of_L2 e hconj

end CFSG.OddStandard.SmallF3.Omega
