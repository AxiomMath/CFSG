module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeIdent
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem map_congrHom_trans_of_mem {V W : Type*} [CommGroup V] [CommGroup W]
    {H : Subgroup (MulAut V)} {H₀ : Subgroup (MulAut W)} {e : V ≃* W}
    (he : H.map (CFSG.Quasithin.H.congrHom e) = H₀) {h : MulAut W} (hh : h ∈ H₀) :
    H.map (CFSG.Quasithin.H.congrHom (e.trans h)) = H₀ := by
  have hc : CFSG.Quasithin.H.congrHom (e.trans h) =
      (CFSG.Quasithin.H.congrHom h).comp (CFSG.Quasithin.H.congrHom e) := by
    ext x w
    rfl
  rw [hc, ← Subgroup.map_map, he, CFSG.Quasithin.H.ZTrans.map_congrHom_self hh]

theorem apply_z_mem_orbit_z0 (hm : M24Out G E t) {z : G} (hz : IsZ E t z) (e : ↥E ≃* W11)
    (he : (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
      img11 AutPerm) :
    e ⟨z, hz.1⟩ ∈ orbit ↥(img11 AutPerm) CFSG.Quasithin.H.Coc24.z0 :=
  (mem_orbit_z0_iff_notMem_normClass hm e he hz.1 hz.2.1).2 hz.2.2.1

theorem apply_t_mem_D0 (hm : M24Out G E t) {z : G} (hz : IsZ E t z) (e : ↥E ≃* W11)
    (he : (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
      img11 AutPerm)
    (hez : e ⟨z, hz.1⟩ = CFSG.Quasithin.H.Coc24.z0) :
    e ⟨t, hm.t_mem⟩ ∈ CocodeModelPair.D0 := by
  have htE : t ∈ E := hm.t_mem
  have ht1 : t ≠ 1 := hm.t_ne_one
  have htz1 : t * z ≠ 1 := by
    intro h
    obtain ⟨n, -, hn⟩ := hz.2.2.2
    rw [h] at hn
    exact ht1 (by simpa using hn)
  have h1 := (mem_normClass_iff_notMem_orbit_z0 hm e he htE ht1).1
    ⟨1, one_mem _, by simp⟩
  have h2 := (mem_normClass_iff_notMem_orbit_z0 hm e he (E.mul_mem htE hz.1) htz1).1 hz.2.2.2
  have hmul : e ⟨t * z, E.mul_mem htE hz.1⟩ = e ⟨t, htE⟩ * e ⟨z, hz.1⟩ :=
    map_mul e ⟨t, htE⟩ ⟨z, hz.1⟩
  rw [hez] at hmul
  refine ⟨?_, h1, ?_, ?_⟩
  · intro h
    exact ht1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  · rw [← hmul]
    intro h
    exact htz1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  · rw [← hmul]
    exact h2

theorem exists_equiv_std
    (hm : M24Out G E t) {z : G} (hz : IsZ E t z) :
    ∃ e : ↥E ≃* W11,
      (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
        img11 AutPerm ∧
      e ⟨z, hz.1⟩ = CFSG.Quasithin.H.Coc24.z0 ∧ e ⟨t, hm.t_mem⟩ = CocodeModelPair.t0 := by
  letI := commGroupOfM24Out hm
  obtain ⟨e₁, he₁⟩ := exists_equiv_w11 hm
  obtain ⟨⟨g, hg⟩, hgz⟩ := apply_z_mem_orbit_z0 hm hz e₁ he₁
  have hgz' : g CFSG.Quasithin.H.Coc24.z0 = e₁ ⟨z, hz.1⟩ := hgz
  have he₂ : (S44.XE E).map (CFSG.Quasithin.H.congrHom (e₁.trans g⁻¹)) = img11 AutPerm :=
    map_congrHom_trans_of_mem he₁ ((img11 AutPerm).inv_mem hg)
  have he₂z : (e₁.trans g⁻¹) ⟨z, hz.1⟩ = CFSG.Quasithin.H.Coc24.z0 := by
    show g⁻¹ (e₁ ⟨z, hz.1⟩) = _
    rw [← hgz']
    exact MulAut.inv_apply_self _ _ _
  have hD0 := apply_t_mem_D0 hm hz (e₁.trans g⁻¹) he₂ he₂z
  obtain ⟨g', hg'L, hg't⟩ := CocodeModelPair.exists_apply_t0_eq hD0
  have hg'S := CFSG.Quasithin.H.Coc24.img11_Lz_le_stab hg'L
  have hg'z : g' CFSG.Quasithin.H.Coc24.z0 = CFSG.Quasithin.H.Coc24.z0 :=
    CFSG.Quasithin.H.Coc24.mem_centSub_zpowers.1 hg'S.2
  refine ⟨(e₁.trans g⁻¹).trans g'⁻¹,
    map_congrHom_trans_of_mem he₂ ((img11 AutPerm).inv_mem hg'S.1), ?_, ?_⟩
  · show g'⁻¹ ((e₁.trans g⁻¹) ⟨z, hz.1⟩) = _
    rw [he₂z]
    have h1 : g'⁻¹ CFSG.Quasithin.H.Coc24.z0 = g'⁻¹ (g' CFSG.Quasithin.H.Coc24.z0) := by
      rw [hg'z]
    exact h1.trans (MulAut.inv_apply_self _ _ _)
  · show g'⁻¹ ((e₁.trans g⁻¹) ⟨t, hm.t_mem⟩) = _
    rw [← hg't]
    exact MulAut.inv_apply_self _ _ _

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
