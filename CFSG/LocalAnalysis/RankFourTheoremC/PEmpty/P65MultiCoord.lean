module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Coord
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open scoped commutatorElement
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62 (mem_normalizer_of_conj_mem
  mem_normalizer_sup' π_conj_fix π_commutator_fix)

variable {Y : Type} [Group Y] [Finite Y]

theorem fixes_components {p f : ℕ} (hp : p.Prime) (hf : f.Prime) (hfp : f ≠ p)
    (hcard : Nat.card (ComponentIndex Y) = p)
    {x : Y} (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {T : Subgroup Y} (hTf : IsPGroup f T) (hxT : x ∈ normalizer (T : Set Y)) :
    ∀ t ∈ T, ∀ C : ComponentIndex Y, cjComp t C = C := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hmod := hTf.card_modEq_card_fixedPoints (ComponentIndex Y)
  rw [hcard] at hmod
  have hfix : Nonempty (MulAction.fixedPoints ↥T (ComponentIndex Y)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Nat.card_of_isEmpty, Nat.modEq_zero_iff_dvd] at hmod
    exact hfp ((Nat.prime_dvd_prime_iff_eq hf hp).mp hmod)
  obtain ⟨⟨C₀, hC₀⟩⟩ := hfix
  intro t ht C
  obtain ⟨k, hk⟩ := htrans C₀ C
  have ht' : (x ^ k)⁻¹ * t * x ^ k ∈ T := by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxT k)) t).mp ht
    simpa using this
  have hfix : cjComp ((x ^ k)⁻¹ * t * x ^ k) C₀ = C₀ := hC₀ ⟨_, ht'⟩
  calc cjComp t C = cjComp t (cjComp (x ^ k) C₀) := by rw [hk]
    _ = cjComp (t * x ^ k) C₀ := (cjComp_mul t (x ^ k) C₀).symm
    _ = cjComp (x ^ k * ((x ^ k)⁻¹ * t * x ^ k)) C₀ := by congr 1; group
    _ = cjComp (x ^ k) (cjComp ((x ^ k)⁻¹ * t * x ^ k) C₀) := cjComp_mul _ _ _
    _ = C := by rw [hfix, hk]

theorem zcoord_mem_normalizer
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {p f : ℕ} (hp : p.Prime) (hf : f.Prime)
    (hfp : f ≠ p) {x z : Y} (hxz : x * z = z * x) (hzL : z ∈ layer Y)
    (hcard : Nat.card (ComponentIndex Y) = p)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {T : Subgroup Y} (hT : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) ⊤ T)
    (C₀ : ComponentIndex Y) : π hZ C₀ z hzL ∈ normalizer (T : Set Y) := by
  obtain ⟨⟨-, hTf, hBT⟩, hmax⟩ := hT
  have hxT : x ∈ normalizer (T : Set Y) := hBT (Subgroup.mem_sup_left (mem_zpowers x))
  have hzT : z ∈ normalizer (T : Set Y) := hBT (Subgroup.mem_sup_right (mem_zpowers z))
  have hfix := fixes_components hp hf hfp hcard htrans hTf hxT
  obtain ⟨zc, hzc⟩ : ∃ zc : ComponentIndex Y → Y, ∀ C, zc C = π hZ C z hzL :=
    ⟨fun C => π hZ C z hzL, fun C => rfl⟩
  have hzcC : ∀ C, zc C ∈ C.1 := fun C => by rw [hzc]; exact π_mem C z hzL
  obtain ⟨EC, hEC⟩ : ∃ EC : ComponentIndex Y → Subgroup Y,
      ∀ C, EC C = ⁅T, zpowers (zc C)⁆ := ⟨fun C => ⁅T, zpowers (zc C)⁆, fun C => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup Y, E = ⁅T, zpowers z⁆ := ⟨_, rfl⟩
  have hE_T : E ≤ T := by
    rw [hE]
    exact le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hzT)
  have hEC_le : ∀ C, EC C ≤ C.1 := by
    intro C
    rw [hEC, commutator_le]
    intro t ht g hg
    have hg' : g ∈ C.1 := zpowers_le.mpr (hzcC C) hg
    have h1 : t * g * t⁻¹ ∈ C.1 := by
      have := mem_cjComp_of_mem t C hg'
      rwa [hfix t ht C] at this
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hg')
  have hEC_f : ∀ C, IsPGroup f (EC C) := by
    intro C
    let ρ : layer Y →* Y := C.1.subtype.comp (coord hZ C)
    have hρ : ∀ (y : Y) (hy : y ∈ layer Y), ρ ⟨y, hy⟩ = π hZ C y hy := fun y hy => rfl
    have hG2 : IsPGroup f ((E.subgroupOf (layer Y)).map ρ) :=
      ((hTf.to_le hE_T).comap_subtype).map ρ
    refine hG2.to_le ?_
    rw [hEC, commutator_le]
    intro t ht g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hzk : z ^ k ∈ layer Y := zpow_mem hzL k
    have hmem : ⁅t, z ^ k⁆ ∈ layer Y := by
      rw [commutatorElement_def]
      exact mul_mem (conj_mem_layer t hzk) (inv_mem hzk)
    have hEmem : ⁅t, z ^ k⁆ ∈ E := by
      rw [hE]
      exact commutator_mem_commutator ht (zpow_mem_zpowers z k)
    refine ⟨⟨⁅t, z ^ k⁆, hmem⟩, hEmem, ?_⟩
    rw [hρ _ hmem, π_commutator_fix C (hfix t ht C) hzk hmem, π_zpow C hzL k, hzc]
  have hEC_normT : ∀ C, T ≤ normalizer (EC C : Set Y) := by
    intro C
    rw [hEC]
    exact normalizer_commutator_ge_left T _
  have hzc_norm : ∀ C, zc C ∈ normalizer (EC C : Set Y) := by
    intro C
    rw [hEC]
    exact normalizer_commutator_ge_right T _ (mem_zpowers _)
  have hxzx : x * z * x⁻¹ = z := by rw [hxz]; group
  have hzc_x : ∀ C₁, x * zc C₁ * x⁻¹ = zc (cjComp x C₁) := by
    intro C₁
    have h := π_conj (hZ := hZ) x C₁ hzL
    rw [K62.π_congr (hZ := hZ) (cjComp x C₁) hxzx (conj_mem_layer x hzL) hzL] at h
    simp only [hzc]
    exact h.symm
  have hx_EC : ∀ C₁, ∀ e ∈ EC C₁, x * e * x⁻¹ ∈ EC (cjComp x C₁) := by
    intro C₁
    have hle : EC C₁ ≤ (EC (cjComp x C₁)).comap (MulAut.conj x).toMonoidHom := by
      rw [hEC, commutator_le]
      intro t ht g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      show (MulAut.conj x).toMonoidHom ⁅t, zc C₁ ^ k⁆ ∈ EC (cjComp x C₁)
      have e1 : (MulAut.conj x).toMonoidHom ⁅t, zc C₁ ^ k⁆ =
          ⁅(MulAut.conj x).toMonoidHom t, ((MulAut.conj x).toMonoidHom (zc C₁)) ^ k⁆ := by
        rw [map_commutatorElement, map_zpow]
      rw [e1, hEC]
      refine commutator_mem_commutator ?_ ?_
      · exact (mem_normalizer_iff.mp hxT t).mp ht
      · have h2 : (MulAut.conj x).toMonoidHom (zc C₁) = zc (cjComp x C₁) := by
          simpa [MulAut.conj_apply] using hzc_x C₁
        rw [h2]
        exact zpow_mem_zpowers _ k
    intro e he
    exact hle he
  obtain ⟨Es, hEs⟩ : ∃ Es : Subgroup Y,
      ∀ e, e ∈ Es ↔ ∃ he : e ∈ layer Y, ∀ C, π hZ C e he ∈ EC C := by
    refine ⟨{ carrier := {e | ∃ he : e ∈ layer Y, ∀ C, π hZ C e he ∈ EC C}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun e => Iff.rfl⟩
    · rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
      refine ⟨mul_mem ha hb, fun C => ?_⟩
      rw [π_mul C ha hb]
      exact (EC C).mul_mem (hA C) (hB C)
    · exact ⟨one_mem _, fun C => by rw [π_one]; exact (EC C).one_mem⟩
    · rintro a ⟨ha, hA⟩
      refine ⟨inv_mem ha, fun C => ?_⟩
      rw [π_inv C ha]
      exact (EC C).inv_mem (hA C)
  have hEs_f : IsPGroup f Es := by
    intro e
    obtain ⟨he, hEe⟩ := (hEs e).mp e.2
    have h1 : ∀ C, ∃ n : ℕ, (π hZ C e he) ^ f ^ n = 1 := fun C => by
      obtain ⟨n, hn⟩ := hEC_f C ⟨_, hEe C⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    choose n hn using h1
    refine ⟨Finset.univ.sup n, Subtype.ext ?_⟩
    show (e : Y) ^ f ^ (Finset.univ.sup n) = 1
    refine eq_one_of_π_eq_one (hZ := hZ) (pow_mem he _) fun C => ?_
    rw [π_pow C he]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (Finset.mem_univ C) : n C ≤
      Finset.univ.sup n)
    rw [hm, Nat.pow_add, pow_mul, hn C, one_pow]
  have hEs_T : T ≤ normalizer (Es : Set Y) := by
    intro t ht
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer t hel, fun C => ?_⟩
    rw [π_conj_fix C (hfix t ht C) hel]
    exact (mem_normalizer_iff.mp (hEC_normT C ht) _).mp (hEe C)
  have hEs_z : z ∈ normalizer (Es : Set Y) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer z hel, fun C => ?_⟩
    have h1 : π hZ C (z * e * z⁻¹) (conj_mem_layer z hel) =
        π hZ C z hzL * π hZ C e hel * (π hZ C z hzL)⁻¹ := by
      rw [π_mul C (mul_mem hzL hel) (inv_mem hzL), π_mul C hzL hel, π_inv C hzL]
    rw [h1, ← hzc C]
    exact (mem_normalizer_iff.mp (hzc_norm C) _).mp (hEe C)
  have hEs_x : x ∈ normalizer (Es : Set Y) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer x hel, fun C => ?_⟩
    have hC1 : cjComp x (cjComp x⁻¹ C) = C := by
      rw [← cjComp_mul, mul_inv_cancel, cjComp_one]
    have h := π_conj (hZ := hZ) x (cjComp x⁻¹ C) hel
    rw [hC1] at h
    rw [h]
    have := hx_EC (cjComp x⁻¹ C) _ (hEe (cjComp x⁻¹ C))
    rwa [hC1] at this
  have hQf : IsPGroup f (Es ⊔ T : Subgroup Y) := hEs_f.to_sup_of_normal_left' hTf hEs_T
  have hxQ := mem_normalizer_sup' hEs_x hxT
  have hzQ := mem_normalizer_sup' hEs_z hzT
  have hBQ : zpowers x ⊔ zpowers z ≤ normalizer ((Es ⊔ T : Subgroup Y) : Set Y) :=
    sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr hzQ)
  have hQT : Es ⊔ T = T := hmax _ ⟨le_top, hQf, hBQ⟩ le_sup_right
  have hEsT : Es ≤ T := le_sup_left.trans hQT.le
  have hECEs : EC C₀ ≤ Es := by
    intro e he
    have heC : e ∈ C₀.1 := hEC_le C₀ he
    have hel : e ∈ layer Y := component_le_layer C₀.2 heC
    refine (hEs e).mpr ⟨hel, fun C' => ?_⟩
    by_cases h : C' = C₀
    · subst h
      rw [π_of_mem C' heC]
      exact he
    · rw [π_of_mem_of_ne (Ne.symm h) heC]
      exact (EC C').one_mem
  have hcomm : ⁅T, zpowers (zc C₀)⁆ ≤ T := by
    rw [← hEC]
    exact (hECEs.trans hEsT)
  have := le_normalizer_iff_commutator_le_left.mpr hcomm (mem_zpowers (zc C₀))
  rwa [hzc] at this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M
