module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpRad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public noncomputable section

namespace CFSG.QuasithinUnique.B113Lie.Sp

open Matrix CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits

variable {r : ℕ} {K : Type} [Field K]

theorem exists_transvection (x : Fin r ⊕ Fin r → K) :
    ∃ h : StatedSp r K, ∀ v, natRep (StatedSp r K) h v = v + (spForm r K).β x v • x :=
  exists_natRep_eq_of_isometry r K
    { toFun := fun v => v + (spForm r K).β x v • x
      map_add' := fun u v => by
        simp only [(spForm r K).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm r K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm r K).β_transvection rfl (spForm_self r K) x)

theorem exists_siegel (x y : Fin r ⊕ Fin r → K) (hxy : (spForm r K).β x y = 0) :
    ∃ h : StatedSp r K, ∀ v, natRep (StatedSp r K) h v =
      v + (spForm r K).β x v • y + (spForm r K).β y v • x :=
  exists_natRep_eq_of_isometry r K
    { toFun := fun v => v + (spForm r K).β x v • y + (spForm r K).β y v • x
      map_add' := fun u v => by
        simp only [(spForm r K).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm r K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm r K).β_siegel rfl (spForm_self r K) hxy)

abbrev sprad (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : (spForm r K).IsTotallyIsotropic W) : Subgroup (StatedSp r K) :=
  rad (spForm r K) (natRep (StatedSp r K)) W hW

theorem rep_mem_of_mem_stabilizer {W : Submodule K (Fin r ⊕ Fin r → K)} {q : StatedSp r K}
    (hq : q ∈ SymplecticFlag.stabilizer r K W) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    natRep (StatedSp r K) q w ∈ W := by
  have h1 : mulVecLin ((q : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) w ∈
      W.map (mulVecLin ((q : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := ⟨w, hw, rfl⟩
  rw [SymplecticFlag.mem_stabilizer.mp hq, mulVecLin_apply] at h1
  rwa [natRep_apply]

theorem sprad_le_stabilizer {W : Submodule K (Fin r ⊕ Fin r → K)}
    {hW : (spForm r K).IsTotallyIsotropic W} : sprad W hW ≤ SymplecticFlag.stabilizer r K W := by
  intro g hg
  refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
  · have := hg.1 v hv
    rw [natRep_apply] at this
    rw [this]
    exact hv
  · have := (inv_mem hg : g⁻¹ ∈ sprad W hW).1 v hv
    rw [natRep_apply] at this
    rw [this]
    exact hv

theorem stabilizer_le_normalizer_sprad {W : Submodule K (Fin r ⊕ Fin r → K)}
    {hW : (spForm r K).IsTotallyIsotropic W} :
    SymplecticFlag.stabilizer r K W ≤
      Subgroup.normalizer ((sprad W hW : Subgroup (StatedSp r K)) : Set (StatedSp r K)) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact rad_conj_mem (isIsometric_natRep_statedSp r K)
      (fun w hw => rep_mem_of_mem_stabilizer hq hw)
      (fun w hw => rep_mem_of_mem_stabilizer (inv_mem hq) hw) hg
  · intro hg
    have := rad_conj_mem (isIsometric_natRep_statedSp r K) (q := q⁻¹)
      (fun w hw => rep_mem_of_mem_stabilizer (inv_mem hq) hw)
      (fun w hw => by simpa using rep_mem_of_mem_stabilizer hq hw) hg
    simpa [mul_assoc] using this

theorem eq_one_of_mem_sprad_of_mem_spScalars {W : Submodule K (Fin r ⊕ Fin r → K)}
    {hW : (spForm r K).IsTotallyIsotropic W} (hW0 : W ≠ ⊥) {g : StatedSp r K}
    (hg : g ∈ sprad W hW) (hZ : g ∈ SymplecticHigher.spScalars r K) : g = 1 := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hfix := hg.1 w hwW
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hZ
  obtain ⟨c, hc⟩ := hZ
  have hmul : ∀ u : Fin r ⊕ Fin r → K, natRep (StatedSp r K) g u = (c : K) • u := fun u => by
    rw [natRep_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]
    ext x
    simp [mulVec_diagonal]
  have hc1 : (c : K) = 1 := by
    have h1 : ((c : K) - 1) • w = 0 := by
      rw [sub_smul, ← hmul w, hfix, one_smul, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  apply natRep_injective (StatedSp r K)
  refine LinearMap.ext fun u => ?_
  rw [hmul, hc1, one_smul, map_one, Module.End.one_apply]

theorem map_le_normalizer_map {G G' : Type*} [Group G] [Group G'] (π : G →* G')
    {Q R : Subgroup G} (hQ : Q ≤ Subgroup.normalizer (R : Set G)) :
    Q.map π ≤ Subgroup.normalizer ((R.map π : Subgroup G') : Set G') := by
  rintro _ ⟨q, hq, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hq' := Subgroup.mem_normalizer_iff.1 (hQ hq)
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨q * r * q⁻¹, (hq' r).1 hr, by simp [map_mul, map_inv]⟩
  · rintro ⟨r, hr, hry⟩
    refine ⟨q⁻¹ * r * q, ?_, ?_⟩
    · exact (hq' (q⁻¹ * r * q)).2 (by simpa [mul_assoc] using hr)
    · have h1 : π r = π q * y * (π q)⁻¹ := hry
      calc π (q⁻¹ * r * q) = (π q)⁻¹ * π r * π q := by simp [map_mul, map_inv]
        _ = y := by rw [h1]; group

theorem charTwo_projStabilizer_of_cent [Finite K] [CharP K 2]
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥) (hW : (spForm r K).IsTotallyIsotropic W)
    (hcent : ∀ g : StatedSp r K, (∀ q ∈ sprad W hW, g * q = q * g) → g ∈ sprad W hW) :
    CharTwo (SymplecticHigher.projStabilizer r K W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedProj (StatedSp r K)) := inferInstance
  refine Lin.charTwo_of_core (R := (sprad W hW).map (SymplecticFlag.proj r K)) ?_ ?_ ?_ ?_
  · exact Subgroup.map_mono sprad_le_stabilizer
  · exact map_le_normalizer_map _ stabilizer_le_normalizer_sprad
  · exact (rad_isPGroup (isIsometric_natRep_statedSp r K) (natRep_injective _) 2 hW).map
      (SymplecticFlag.proj r K)
  · rintro x ⟨hxP, hxC⟩
    obtain ⟨g, hgQ, rfl⟩ := hxP
    have hxC' := Subgroup.mem_centralizer_iff.1
      (show SymplecticFlag.proj r K g ∈ Subgroup.centralizer
        (((sprad W hW).map (SymplecticFlag.proj r K) :
          Subgroup (StatedProj (StatedSp r K))) : Set (StatedProj (StatedSp r K))) from hxC)
    have hcomm : ∀ q ∈ sprad W hW, g * q = q * g := by
      intro q hq
      have h1 : SymplecticFlag.proj r K q * SymplecticFlag.proj r K g =
          SymplecticFlag.proj r K g * SymplecticFlag.proj r K q :=
        hxC' (SymplecticFlag.proj r K q) ⟨q, hq, rfl⟩
      have hcommR : g * q * g⁻¹ * q⁻¹ ∈ sprad W hW := by
        refine mul_mem ?_ (inv_mem hq)
        exact rad_conj_mem (isIsometric_natRep_statedSp r K)
          (fun w hw => rep_mem_of_mem_stabilizer hgQ hw)
          (fun w hw => rep_mem_of_mem_stabilizer (inv_mem hgQ) hw) hq
      have hsc : g * q * g⁻¹ * q⁻¹ ∈ SymplecticHigher.spScalars r K := by
        rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [← h1]
        group
      have h2 := eq_one_of_mem_sprad_of_mem_spScalars hW0 hcommR hsc
      calc g * q = g * q * g⁻¹ * q⁻¹ * (q * g) := by group
        _ = q * g := by rw [h2, one_mul]
    exact ⟨g, hcent g hcomm, rfl⟩

theorem charTwo_projStabilizer_point [Finite K] [CharP K 2] {e : Fin r ⊕ Fin r → K}
    (he : e ≠ 0) : CharTwo (SymplecticHigher.projStabilizer r K (K ∙ e)) := by
  have hW := isTotallyIsotropic_span_singleton (F := spForm r K) (spForm_self r K) e
  refine charTwo_projStabilizer_of_cent (W := K ∙ e) ?_ hW fun g hg => ?_
  · exact fun h => he (Submodule.span_singleton_eq_bot.mp h)
  · exact mem_rad_of_commute_point rfl (isIsometric_natRep_statedSp r K) exists_transvection
      exists_siegel he hW hg

theorem charTwo_projStabilizer_lagrangian [Finite K] [CharP K 2]
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : (spForm r K).perp W = W) (hW0 : W ≠ ⊥) :
    CharTwo (SymplecticHigher.projStabilizer r K W) :=
  charTwo_projStabilizer_of_cent hW0 hW.ge fun _ hg =>
    mem_rad_of_commute_lagrangian rfl (isIsometric_natRep_statedSp r K) exists_transvection hW hg

theorem two_dvd_card_statedProj [Finite K] [CharP K 2] {e : Fin r ⊕ Fin r → K} (he : e ≠ 0) :
    2 ∣ Nat.card (StatedProj (StatedSp r K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedProj (StatedSp r K)) := inferInstance
  have hW := isTotallyIsotropic_span_singleton (F := spForm r K) (spForm_self r K) e
  have hR : IsPGroup 2 ((sprad (K ∙ e) hW).map (SymplecticFlag.proj r K)) :=
    (rad_isPGroup (isIsometric_natRep_statedSp r K) (natRep_injective _) 2 hW).map
      (SymplecticFlag.proj r K)
  obtain ⟨t, ht⟩ := exists_transvection (K := K) (r := r) e
  have htR : t ∈ sprad (K ∙ e) hW := transvection_mem_rad (Submodule.mem_span_singleton_self e) ht
  have hne : (sprad (K ∙ e) hW).map (SymplecticFlag.proj r K) ≠ ⊥ := by
    intro hbot
    have hproj : SymplecticFlag.proj r K t = 1 := by
      have : SymplecticFlag.proj r K t ∈ (sprad (K ∙ e) hW).map (SymplecticFlag.proj r K) :=
        ⟨t, htR, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have ht1 : t = 1 := eq_one_of_mem_sprad_of_mem_spScalars
      (fun h => he (Submodule.span_singleton_eq_bot.mp h)) htR
      (by rw [← SymplecticHigher.ker_proj]; exact hproj)
    obtain ⟨v, hv⟩ := exists_β_eq_one (F := spForm r K) he
    have h1 := ht v
    rw [ht1, map_one, Module.End.one_apply, hv, one_smul] at h1
    exact he (by simpa using h1)
  rcases hR.card_eq_or_dvd with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
  · exact h.trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.QuasithinUnique.B113Lie.Sp
