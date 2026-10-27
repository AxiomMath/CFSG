module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
import CFSG.LieType.Steinberg.BorelCommutator
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
open scoped commutatorElement Pointwise

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ}

omit [Finite K] in
private theorem leviM_le_normalizer_leviRad (hext : SteinbergExtras D n H) (I : Set (Fin D.rank)) :
    leviM D I ≤ Subgroup.normalizer (leviRad D I : Set K) :=
  le_normalizer_leviRad fun _j hj => iSup₂_le fun _i hi =>
    rankOne_le_normalizer_radical hext fun hij => hj (hij ▸ hi)

omit [Finite K] [Finite Y] in
private theorem map_conj_posUnipotent_of_mem_leviM (h : BorelQuotient D n H π e)
    {J : Set (Fin D.rank)} {m : K} (hm : m ∈ leviM D J)
    (hcent : (leviM D J).map π ≤ Subgroup.centralizer ({π m} : Set Y)) :
    ∀ g ∈ (posUnipotent D).map π, π m * g * (π m)⁻¹ ∈ (posUnipotent D).map π := by
  intro g hg
  obtain ⟨k, hkU, rfl⟩ := hg
  have hkW : k ∈ leviRad D J ⊔ leviM D J := posUnipotent_le_leviRad_sup_leviM h.ct hkU
  have hcoe : (↑(leviRad D J ⊔ leviM D J) : Set K) =
      (leviRad D J : Set K) * (leviM D J : Set K) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (leviRad D J) (leviM D J)
      (leviM_le_normalizer_leviRad h.extras J)
  have hkW' : k ∈ (leviRad D J : Set K) * (leviM D J : Set K) := by
    rw [← hcoe]
    exact hkW
  obtain ⟨a, ha, b, hb, hab⟩ := hkW'
  have hma : m * a * m⁻¹ ∈ leviRad D J :=
    (Subgroup.mem_normalizer_iff.1 ((leviM_le_normalizer_leviRad h.extras J) hm) a).1 ha
  have hbU : b ∈ posUnipotent D := by
    have hb_eq : b = a⁻¹ * k := by rw [← hab]; group
    rw [hb_eq]
    exact mul_mem (inv_mem (leviRad_le_posUnipotent ha)) hkU
  refine ⟨(m * a * m⁻¹) * b, mul_mem (leviRad_le_posUnipotent hma) hbU, ?_⟩
  have hkab : π k = π a * π b := by rw [← hab, map_mul]
  have hbm : Commute (π m) (π b) :=
    Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_map_of_mem π hb)) (π m)
      (Set.mem_singleton (π m))
  have hbm' : (π m)⁻¹ * π b = π b * (π m)⁻¹ := hbm.inv_left.eq
  simp only [map_mul, map_inv, hkab]
  calc π m * π a * (π m)⁻¹ * π b
      = π m * (π a * ((π m)⁻¹ * π b)) := by group
    _ = π m * (π a * (π b * (π m)⁻¹)) := by rw [hbm']
    _ = π m * (π a * π b) * (π m)⁻¹ := by group

omit [Finite K] [Finite Y] in
private theorem map_leviM_le_centralizer_of_center (h : BorelQuotient D n H π e)
    {J C : Set (Fin D.rank)}
    (h0 : ∀ k ∈ C, ∀ l ∈ J, l ∉ C → D.cartan k l = 0)
    {z : ↥((leviM D C).map π)} (hz : z ∈ Subgroup.center ↥((leviM D C).map π)) :
    (leviM D J).map π ≤ Subgroup.centralizer ({(z:Y)} : Set Y) := by
  rw [leviM]
  simp_rw [Subgroup.map_iSup]
  refine iSup₂_le fun i hi => ?_
  by_cases hiC : i ∈ C
  · refine (Subgroup.map_mono (rankOne_le_leviM hiC)).trans ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact (Subtype.ext_iff.mp (Subgroup.mem_center_iff.1 hz ⟨w, hw⟩)).symm
  · have hcomm : Commutes (leviM D C) (rankOne D.rootGroup i) := by
      rw [commutes_iff_le_centralizer, leviM]
      refine iSup₂_le fun k hk => ?_
      rw [← commutes_iff_le_centralizer]
      exact commutes_rankOne_of_cartan_eq_zero h.extras (by rintro rfl; exact hiC hk)
        (h0 k hk i hi hiC)
    have hcomm' : Commutes ((leviM D C).map π) ((rankOne D.rootGroup i).map π) := by
      rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩
      simpa only [map_mul] using congrArg π (hcomm w hw v hv)
    refine (commutes_iff_le_centralizer.mp hcomm'.symm).trans ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr z.2)

omit [Finite Y] in
private theorem mem_map_borel_of_centralizes_leviM (h : BorelQuotient D n H π e)
    {J C : Set (Fin D.rank)} (hCJ : C ⊆ J) {z : ↥((leviM D C).map π)}
    (hcent : (leviM D J).map π ≤ Subgroup.centralizer ({(z:Y)} : Set Y)) :
    (z:Y) ∈ (borel D H).map π := by
  obtain ⟨m, hm, hzm⟩ := Subgroup.mem_map.1 z.2
  have hmJ : m ∈ leviM D J := by
    have hsub : leviM D C ≤ leviM D J := by
      change (⨆ i ∈ C, rankOne D.rootGroup i) ≤ ⨆ i ∈ J, rankOne D.rootGroup i
      exact iSup₂_le fun i hi => le_iSup₂_of_le i (hCJ hi) le_rfl
    exact hsub hm
  rw [← h.normalizer_map_posUnipotent, Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have h1 := map_conj_posUnipotent_of_mem_leviM (J := J) h hmJ
      (by rw [hzm]; exact hcent) u hu
    simpa [hzm] using h1
  · intro hu
    have hcent' : (leviM D J).map π ≤ Subgroup.centralizer ({π m⁻¹} : Set Y) := by
      rw [map_inv, hzm]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      have hc : Commute (z:Y) w :=
        Subgroup.mem_centralizer_iff.1 (hcent hw) (z:Y) (Set.mem_singleton (z:Y))
      exact hc.inv_left.eq
    have h1 := map_conj_posUnipotent_of_mem_leviM (J := J) h (inv_mem hmJ) hcent' _ hu
    have he : u = (z:Y)⁻¹ * ((z:Y) * u * (z:Y)⁻¹) * (z:Y) := by group
    rw [he]
    simpa [hzm, map_inv] using h1

private theorem conj_mem_center_center {Y : Type*} [Group Y] {C : Subgroup Y} {z : ↥C} {a : Y}
    (hz : z ∈ Subgroup.center ↥C) (ha : a ∈ Subgroup.normalizer (C : Set Y))
    (hmem : a * (z:Y) * a⁻¹ ∈ C) :
    (⟨a * (z:Y) * a⁻¹, hmem⟩ : ↥C) ∈ Subgroup.center ↥C := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hmem' : a⁻¹ * (g:Y) * a ∈ C := by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem ha) (g:Y)).1 g.2
  have hgz : (a⁻¹ * (g:Y) * a) * (z:Y) = (z:Y) * (a⁻¹ * (g:Y) * a) := by
    simpa using Subtype.ext_iff.mp
      (Subgroup.mem_center_iff.1 hz (⟨a⁻¹ * (g:Y) * a, hmem'⟩ : ↥C))
  calc (g:Y) * (a * (z:Y) * a⁻¹)
      = a * (a⁻¹ * (g:Y) * a * (z:Y)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * (g:Y) * a) * (z:Y)) * a⁻¹ := by group
    _ = a * ((z:Y) * (a⁻¹ * (g:Y) * a)) * a⁻¹ := by rw [hgz]
    _ = (a * (z:Y) * a⁻¹) * (g:Y) := by group

omit [Finite K] [Finite Y] in
private theorem commutator_torus_map_eq_one (h : BorelQuotient D n H π e)
    {C : Set (Fin D.rank)} {z : ↥((leviM D C).map π)}
    (hzB : (z:Y) ∈ (borel D H).map π)
    (hz : z ∈ Subgroup.center ↥((leviM D C).map π))
    (hodd : ∀ w ∈ Subgroup.center ↥((leviM D C).map π), ∀ k : ℕ, w ^ 2 ^ k = 1 → w = 1)
    {a : Y} (ha : a ∈ (⨆ k, H k).map π) : ⁅(z:Y), a⁆ = 1 := by
  have haN : a ∈ Subgroup.normalizer (((leviM D C).map π : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer_map π (Subgroup.map_mono (torus_le_normalizer_leviM (I := C) h.ct) ha)
  obtain ⟨b, hb, hzb⟩ := Subgroup.mem_map.1 hzB
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ha
  have hbt : ⁅b, t⁆ ∈ posUnipotent D :=
    commutator_mem_posUnipotent_of_mem_borel h.ct h.extras b hb t
      (show t ∈ borel D H from (le_sup_left : (⨆ k, H k) ≤ borel D H) ht)
  have hza : ⁅(z:Y), π t⁆ = π ⁅b, t⁆ := by
    rw [← hzb]
    exact (map_commutatorElement π b t).symm
  have htN : π t * (z:Y) * (π t)⁻¹ ∈ (leviM D C).map π :=
    (Subgroup.mem_normalizer_iff.1 haN (z:Y)).1 z.2
  have hmemC : ⁅(z:Y), π t⁆ ∈ (leviM D C).map π := by
    have he : ⁅(z:Y), π t⁆ = (z:Y) * (π t * (z:Y) * (π t)⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [he]
    exact mul_mem z.2 (inv_mem htN)
  have haz_center := conj_mem_center_center hz haN htN
  have hcenter : (⟨⁅(z:Y), π t⁆, hmemC⟩ : ↥((leviM D C).map π)) ∈
      Subgroup.center ↥((leviM D C).map π) := by
    have hw : (⟨⁅(z:Y), π t⁆, hmemC⟩ : ↥((leviM D C).map π)) =
        (⟨(z:Y), z.2⟩ : ↥((leviM D C).map π)) *
          (⟨π t * (z:Y) * (π t)⁻¹, htN⟩ : ↥((leviM D C).map π))⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [commutatorElement_def]
      group
    rw [hw]
    exact mul_mem hz (inv_mem haz_center)
  obtain ⟨k, hk⟩ := (isPGroup_iSup_pos h.extras h.pGroup).exists_pow_pow_eq_one
    (⟨⁅b, t⁆, hbt⟩ : ↥(posUnipotent D))
  have hw1 : (⟨⁅(z:Y), π t⁆, hmemC⟩ : ↥((leviM D C).map π)) = 1 :=
    hodd _ hcenter k (by
      apply Subtype.ext
      change ⁅(z:Y), π t⁆ ^ 2 ^ k = 1
      rw [hza]
      have hk' : ⁅b, t⁆ ^ 2 ^ k = 1 := by
        have h2 := Subtype.ext_iff.mp hk
        change ((⟨⁅b, t⁆, hbt⟩ : ↥(posUnipotent D)) : K) ^ 2 ^ k = 1 at h2
        simpa using h2
      simpa [map_pow, map_commutatorElement] using congrArg π hk')
  exact Subtype.ext_iff.mp hw1

private theorem commutator_mem_of_mem_closure {Y : Type*} [Group Y] {z : Y} {N G : Subgroup Y}
    (hNG : G ≤ Subgroup.normalizer (N : Set Y))
    {S : Set Y} (hSG : S ⊆ G) (hgen : G ≤ Subgroup.closure S)
    (hSmem : ∀ s ∈ S, ⁅z, s⁆ ∈ N) {x : Y} (hx : x ∈ G) : ⁅z, x⁆ ∈ N := by
  have hclG : Subgroup.closure S ≤ G := by
    rw [Subgroup.closure_le]
    exact hSG
  have key : ∀ y ∈ Subgroup.closure S, ⁅z, y⁆ ∈ N := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs => exact hSmem s hs
    | one => simp
    | mul a b ha hb iha ihb =>
        have haG : a ∈ G := hclG ha
        have hconj : a * ⁅z, b⁆ * a⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hNG haG) ⁅z, b⁆).1 ihb
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa only [mul_assoc] using N.mul_mem iha hconj
    | inv a ha iha =>
        have haG : a ∈ G := hclG ha
        have hconj : a⁻¹ * ⁅z, a⁆⁻¹ * a ∈ N := by
          simpa using
            (Subgroup.mem_normalizer_iff.1 (hNG (inv_mem haG)) ⁅z, a⁆⁻¹).1 (N.inv_mem iha)
        rw [commutatorElement_inv_right, ← commutatorElement_inv]
        exact hconj
  exact key x (hgen hx)

omit [Finite K] [Finite Y] in
private theorem map_parJ_le_normalizer_map_leviRad (h : BorelQuotient D n H π e)
    (J : Set (Fin D.rank)) :
    (parJ D H J).map π ≤ Subgroup.normalizer ((leviRad D J).map π : Set Y) := by
  have hpos : parJ D H J ≤ Subgroup.normalizer (leviRad D J : Set K) := by
    rw [show parJ D H J = borel D H ⊔ leviM D J from rfl]
    exact sup_le (borel_le_normalizer_leviRad h.ct h.extras)
      (leviM_le_normalizer_leviRad h.extras J)
  exact (Subgroup.map_mono hpos).trans (Subgroup.le_normalizer_map π)

omit [Finite K] [Finite Y] in
private theorem map_parJ_le_closure (h : BorelQuotient D n H π e) {J : Set (Fin D.rank)} :
    (parJ D H J).map π ≤ Subgroup.closure
      (((⨆ k, H k).map π : Set Y) ∪ ((leviRad D J).map π : Set Y) ∪
        ((leviM D J).map π : Set Y)) := by
  have hparJ : parJ D H J ≤ (⨆ k, H k) ⊔ leviRad D J ⊔ leviM D J := by
    rw [show parJ D H J = borel D H ⊔ leviM D J from rfl, CFSG.LieType.Steinberg.borel]
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right
    exact (posUnipotent_le_leviRad_sup_leviM h.ct).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hGle : (parJ D H J).map π ≤ (⨆ k, H k).map π ⊔ (leviRad D J).map π ⊔
      (leviM D J).map π := by
    refine (Subgroup.map_mono hparJ).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
  have hsup : (⨆ k, H k).map π ⊔ (leviRad D J).map π ⊔ (leviM D J).map π =
      Subgroup.closure (((⨆ k, H k).map π : Set Y) ∪ ((leviRad D J).map π : Set Y) ∪
        ((leviM D J).map π : Set Y)) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
  exact hGle.trans (le_of_eq hsup)

omit [Finite Y] in
theorem BorelQuotient.commutator_mem_map_leviRad (h : BorelQuotient D n H π e)
    {J C : Set (Fin D.rank)} (hCJ : C ⊆ J) (h0 : ∀ k ∈ C, ∀ l ∈ J, l ∉ C → D.cartan k l = 0)
    (hodd : ∀ z ∈ Subgroup.center ↥((leviM D C).map π), ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    {z : ↥((leviM D C).map π)} (hz : z ∈ Subgroup.center ↥((leviM D C).map π)) {x : Y}
    (hx : x ∈ (parJ D H J).map π) : ⁅(z : Y), x⁆ ∈ (leviRad D J).map π := by
  have hcent : (leviM D J).map π ≤ Subgroup.centralizer ({(z:Y)} : Set Y) :=
    map_leviM_le_centralizer_of_center h h0 hz
  have hzB : (z:Y) ∈ (borel D H).map π := mem_map_borel_of_centralizes_leviM h hCJ hcent
  have hNG := map_parJ_le_normalizer_map_leviRad h J
  have hgen := map_parJ_le_closure h (J := J)
  have hAG : (⨆ k, H k) ≤ parJ D H J :=
    (le_sup_left : (⨆ k, H k) ≤ borel D H).trans (le_sup_left : borel D H ≤ parJ D H J)
  have hBG : leviRad D J ≤ parJ D H J :=
    leviRad_le_posUnipotent.trans ((le_sup_right : posUnipotent D ≤ borel D H).trans
      (le_sup_left : borel D H ≤ parJ D H J))
  have hCG : leviM D J ≤ parJ D H J := (le_sup_right : leviM D J ≤ parJ D H J)
  have hSsub : (((⨆ k, H k).map π : Set Y) ∪ ((leviRad D J).map π : Set Y) ∪
      ((leviM D J).map π : Set Y)) ⊆ (parJ D H J).map π := by
    intro s hs
    rcases hs with hsAB | hsC
    · rcases hsAB with hsA | hsB
      · exact Subgroup.map_mono hAG hsA
      · exact Subgroup.map_mono hBG hsB
    · exact Subgroup.map_mono hCG hsC
  have hMCJ : leviM D C ≤ leviM D J := by
    change (⨆ i ∈ C, rankOne D.rootGroup i) ≤ ⨆ i ∈ J, rankOne D.rootGroup i
    exact iSup₂_le fun i hi => le_iSup₂_of_le i (hCJ hi) le_rfl
  have hzG : (z:Y) ∈ (parJ D H J).map π := Subgroup.map_mono (hMCJ.trans hCG) z.2
  have hA : ∀ s ∈ (⨆ k, H k).map π, ⁅(z:Y), s⁆ = 1 :=
    fun s hs => commutator_torus_map_eq_one h hzB hz hodd hs
  have hC : ∀ s ∈ (leviM D J).map π, ⁅(z:Y), s⁆ = 1 := fun s hs =>
    commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_iff.1 (hcent hs) (z:Y) (Set.mem_singleton (z:Y)))
  have hSmem : ∀ s ∈ (((⨆ k, H k).map π : Set Y) ∪ ((leviRad D J).map π : Set Y) ∪
      ((leviM D J).map π : Set Y)), ⁅(z:Y), s⁆ ∈ (leviRad D J).map π := by
    intro s hs
    rcases hs with hsAB | hsC
    · rcases hsAB with hsA | hsB
      · rw [hA s hsA]; exact Subgroup.one_mem _
      · rw [commutatorElement_def]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hNG hzG) s).1 hsB) (inv_mem hsB)
    · rw [hC s hsC]; exact Subgroup.one_mem _
  exact commutator_mem_of_mem_closure hNG hSsub hgen hSmem hx

omit [Finite Y] in
theorem BorelQuotient.commutator_map_center_le (h : BorelQuotient D n H π e)
    {J C : Set (Fin D.rank)} (hCJ : C ⊆ J) (h0 : ∀ k ∈ C, ∀ l ∈ J, l ∉ C → D.cartan k l = 0)
    (hodd : ∀ z ∈ Subgroup.center ↥((leviM D C).map π), ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1) :
    ⁅(Subgroup.center ↥((leviM D C).map π)).map ((leviM D C).map π).subtype,
      (parJ D H J).map π⁆ ≤ (leviRad D J).map π :=
  Subgroup.commutator_le.2 fun _ ⟨_, hz, hzy⟩ _ hx =>
    hzy ▸ h.commutator_mem_map_leviRad hCJ h0 hodd hz hx

end CFSG.AGLEmbedding.ParabHub
