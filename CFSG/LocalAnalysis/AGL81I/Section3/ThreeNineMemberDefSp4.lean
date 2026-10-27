module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Def
public import CFSG.Quasithin.Background.F918V3T3A
public import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem threeNineOut_psp_four {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hG : StatedClassicalModel G .PSp 2 p 1) :
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hG
  letI := hKfield
  letI := hKfinite
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hKcard
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  let P := StatedProj (StatedSp 2 K)
  have hcenterP : Subgroup.center P = ⊥ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_psp4_eq_bot hodd
  have hcenterG : Subgroup.center G = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz w]
    rw [hcenterP, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd (hp.odd_of_ne_two hp2)
  have houtP : Nat.card (Outer P) ∣ 2 := by
    have h := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
      (ℓ := p) (f := 1) (r := 2) hp hp2 le_rfl (by norm_num) hKcard).1
    rw [one_mul, hgcd] at h
    exact h
  have houtG : Nat.card (Outer G) = Nat.card (Outer P) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  refine ⟨hcenterG, ?_, ?_, ?_⟩
  · intro h
    rw [houtG] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (h.trans houtP))
  · intro q hq hq2 hqd
    rw [houtG] at hqd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hqd.trans houtP)) hq2
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.F918V3T3.three_dvd_card_PSp_two (K := K)

private theorem flagStabilizer_two_two {K : Type} [Field K] :
    SymplecticHigher.flagStabilizer 2 K {1, 2} = SymplecticFlag.borelSubgroup 2 K := by
  ext g
  rw [SymplecticHigher.mem_flagStabilizer, SymplecticFlag.mem_borelSubgroup]
  constructor
  · intro h i hi1 hi2
    interval_cases i
    · exact h 1 (by norm_num)
    · exact h 2 (by norm_num)
  · intro h i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact h 1 le_rfl (by norm_num)
    · exact h 2 (by norm_num) le_rfl

private theorem comap_projBorel {K : Type} [Field K] :
    (SymplecticFlag.projBorel 2 K).comap (SymplecticFlag.proj 2 K) =
      SymplecticFlag.borelSubgroup 2 K := by
  rw [SymplecticFlag.projBorel, Subgroup.comap_map_eq_self]
  rw [SymplecticHigher.ker_proj]
  exact (SymplecticHigher.spScalars_le_flagStabilizer {1, 2}).trans
    (le_of_eq flagStabilizer_two_two)

private theorem overgroup_projBorel {K : Type} [Field K]
    {Y : Subgroup (StatedProj (StatedSp 2 K))}
    (hB : SymplecticFlag.projBorel 2 K ≤ Y) (hY : Y < ⊤) :
    Y = SymplecticFlag.projBorel 2 K ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
  classical
  set A : Subgroup (StatedSp 2 K) := Y.comap (SymplecticFlag.proj 2 K) with hA
  have hBA : SymplecticFlag.borelSubgroup 2 K ≤ A := by
    intro b hb
    exact hB (Subgroup.mem_map_of_mem _ hb)
  obtain ⟨hAeq, -⟩ := SymplecticHigher.borel_overgroups A hBA
  have hYeq : Y = A.map (SymplecticFlag.proj 2 K) :=
    (Subgroup.map_comap_eq_self_of_surjective (SymplecticHigher.proj_surjective) Y).symm
  have hIsub : SymplecticHigher.borelCuts K A ⊆ {1, 2} := by
    rintro i ⟨k, rfl, -⟩
    have hk := k.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hne : (SymplecticHigher.borelCuts K A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have htop : Y = ⊤ := by
      rw [hYeq, hAeq, hempty, SymplecticHigher.flagStabilizer_empty]
      exact Subgroup.map_top_of_surjective _ SymplecticHigher.proj_surjective
    exact hY.ne htop
  by_cases h1 : 1 ∈ SymplecticHigher.borelCuts K A
  · by_cases h2 : 2 ∈ SymplecticHigher.borelCuts K A
    · left
      have hIeq : SymplecticHigher.borelCuts K A = {1, 2} := by
        ext j
        constructor
        · exact fun hj => hIsub hj
        · intro hj
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
          rcases hj with rfl | rfl
          · exact h1
          · exact h2
      rw [hYeq, hAeq, hIeq, flagStabilizer_two_two]
      rfl
    · right; left
      have hIeq : SymplecticHigher.borelCuts K A = {1} := by
        ext j
        constructor
        · intro hj
          have hj' := hIsub hj
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj' ⊢
          rcases hj' with rfl | rfl
          · rfl
          · exact absurd hj h2
        · intro hj
          rw [Set.mem_singleton_iff] at hj
          rwa [hj]
      rw [hYeq, hAeq, hIeq, SymplecticHigher.flagStabilizer_singleton]
      rfl
  · right; right
    have h2 : 2 ∈ SymplecticHigher.borelCuts K A := by
      obtain ⟨j, hj⟩ := hne
      have hj' := hIsub hj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj'
      rcases hj' with rfl | rfl
      · exact absurd hj h1
      · exact hj
    have hIeq : SymplecticHigher.borelCuts K A = {2} := by
      ext j
      constructor
      · intro hj
        have hj' := hIsub hj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj' ⊢
        rcases hj' with rfl | rfl
        · exact absurd hj h1
        · rfl
      · intro hj
        rw [Set.mem_singleton_iff] at hj
        rwa [hj]
    rw [hYeq, hAeq, hIeq, SymplecticHigher.flagStabilizer_singleton]
    rfl

private theorem dotW_one {K : Type} [Field K] :
    SymplecticFlag.dotW K (1 : SymplecticTorusWeyl.signedPermGroup 2) = 1 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [SymplecticFlag.coe_dotW]
  have hε : SymplecticFlag.dotSign (K := K) (1 : Equiv.Perm (Fin 2 ⊕ Fin 2)) = 1 := by
    funext x
    rcases x with i | i <;> rfl
  simp [hε, CFSG.LieType.Universal.SpecialLinear.signedPerm_one]

private theorem dotW_mem_normalizer_torus {K : Type} [Field K] [Finite K]
    (w : SymplecticTorusWeyl.signedPermGroup 2) :
    SymplecticFlag.dotW K w ∈
      Subgroup.normalizer (SymplecticTorusWeyl.torus 2 K : Set (StatedSp 2 K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    change SymplecticFlag.dotW K w * t * (SymplecticFlag.dotW K w)⁻¹ ∈
      SymplecticTorusWeyl.torus 2 K
    have hline : SymplecticTorusWeyl.IsLinePerm (1 : Equiv.Perm (Fin 2 ⊕ Fin 2))
        (((SymplecticFlag.dotW K w * t * (SymplecticFlag.dotW K w)⁻¹ : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      have h1 := ((SymplecticHigher.isLinePerm_dotW (K := K) w).mul
        (SymplecticHigher.isLinePerm_torusHom' ht)).mul
        (SymplecticHigher.isLinePerm_dotW (K := K) w).inv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
      simpa using h1
    obtain ⟨t', ht', heq⟩ := SymplecticHigher.exists_torus_of_isLinePerm (K := K) (w := 1) hline
    rw [heq, dotW_one, one_mul]
    exact ht'
  · rw [Subgroup.card_map_of_injective (MulAut.conj (SymplecticFlag.dotW K w)).injective]

private noncomputable def spFourSwap : SymplecticTorusWeyl.signedPermGroup 2 :=
  ⟨Equiv.sumComm (Fin 2) (Fin 2), by
    intro x
    simp only [Equiv.sumComm_apply, Sum.swap_swap]⟩

private theorem single_inr_zero_not_mem_flag {K : Type} [Field K] (i : ℕ) (hi : i ≤ 2) :
    Pi.single (Sum.inr (0 : Fin 2)) 1 ∉ SymplecticFlag.flag 2 K i := by
  intro hmem
  have h := (SymplecticHigher.mem_flag_iff (r := 2) (K := K) (i := i)
    (v := Pi.single (Sum.inr (0 : Fin 2)) 1)).mp hmem (Sum.inr 0) (by
      rw [SymplecticFlag.flagOrder_inr]
      omega)
  simpa using h

private theorem single_inl_zero_mem_flag {K : Type} [Field K] (i : ℕ) (hi : 1 ≤ i) :
    Pi.single (Sum.inl (0 : Fin 2)) 1 ∈ SymplecticFlag.flag 2 K i := by
  rw [SymplecticHigher.mem_flag_iff]
  intro x hx
  rcases x with j | j
  · rw [SymplecticFlag.flagOrder_inl] at hx
    have hj : j ≠ 0 := by omega
    rw [Pi.single_eq_of_ne]
    simp [hj]
  · simp

private theorem proj_not_mem_projBorel {K : Type} [Field K] {g : StatedSp 2 K}
    (hg : g ∉ SymplecticFlag.stabilizer 2 K (SymplecticFlag.flag 2 K 1)) :
    SymplecticFlag.proj 2 K g ∉ SymplecticFlag.projBorel 2 K := by
  intro hmem
  have hcomap : g ∈ (SymplecticFlag.projBorel 2 K).comap (SymplecticFlag.proj 2 K) := hmem
  rw [comap_projBorel] at hcomap
  exact hg (SymplecticHigher.borelSubgroup_le_stabilizer_flag (by norm_num) hcomap)

private theorem proj_not_mem_projStabilizer {K : Type} [Field K]
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} {g : StatedSp 2 K}
    (hg : g ∉ SymplecticFlag.stabilizer 2 K W) :
    SymplecticFlag.proj 2 K g ∉ SymplecticHigher.projStabilizer 2 K W := by
  intro hmem
  have hcomap : g ∈ (SymplecticHigher.projStabilizer 2 K W).comap (SymplecticFlag.proj 2 K) := hmem
  rw [SymplecticHigher.comap_projStabilizer] at hcomap
  exact hg hcomap

private theorem dotW_spFourSwap_not_mem_stab_one {K : Type} [Field K] :
    SymplecticFlag.dotW K spFourSwap ∉
      SymplecticFlag.stabilizer 2 K (SymplecticFlag.flag 2 K 1) := by
  intro hstab
  have hmaps := SymplecticFlag.mem_stabilizer.mp hstab
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((SymplecticFlag.dotW K spFourSwap : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hv : M.mulVec (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈ SymplecticFlag.flag 2 K 1 := by
    have hmem : M.mulVec (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈
        (SymplecticFlag.flag 2 K 1).map (Matrix.mulVecLin M) :=
      Submodule.mem_map_of_mem (single_inl_zero_mem_flag (K := K) 1 le_rfl)
    rwa [hmaps] at hmem
  rw [(SymplecticFlag.dotW_mulVec_inr (K := K) spFourSwap (i := 0) (j := 0) rfl).1] at hv
  exact single_inr_zero_not_mem_flag (K := K) 1 (by norm_num) hv

private theorem dotW_spFourSwap_not_mem_stab_two {K : Type} [Field K] :
    SymplecticFlag.dotW K spFourSwap ∉
      SymplecticFlag.stabilizer 2 K (SymplecticFlag.flag 2 K 2) := by
  intro hstab
  have hmaps := SymplecticFlag.mem_stabilizer.mp hstab
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((SymplecticFlag.dotW K spFourSwap : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hv : M.mulVec (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈ SymplecticFlag.flag 2 K 2 := by
    have hmem : M.mulVec (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈
        (SymplecticFlag.flag 2 K 2).map (Matrix.mulVecLin M) :=
      Submodule.mem_map_of_mem (single_inl_zero_mem_flag (K := K) 2 (by norm_num))
    rwa [hmaps] at hmem
  rw [(SymplecticFlag.dotW_mulVec_inr (K := K) spFourSwap (i := 0) (j := 0) rfl).1] at hv
  exact single_inr_zero_not_mem_flag (K := K) 2 le_rfl hv

private theorem false_of_dvd_pred {K : Type} [Field K] [Finite K] {p d : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (hKp : Nat.card K = p) (h2 : (2 : K) ≠ 0) (hdvd : d ∣ p - 1)
    {Y : Subgroup (StatedProj (StatedSp 2 K))}
    (hY : IsBorelDLocal p d Y) (hB : SymplecticFlag.projBorel 2 K ≤ Y)
    (hclas : Y = SymplecticFlag.projBorel 2 K ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2)) : False := by
  let T := SymplecticTorusWeyl.torus 2 K
  let H := T.map (SymplecticFlag.proj 2 K)
  have hHle : H ≤ Y := (Subgroup.map_mono (SymplecticFlag.torus_le_borelSubgroup)).trans hB
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨a, rfl⟩ := ht
    obtain ⟨b, rfl⟩ := hs
    simp only [← map_mul, mul_comm]
  have hKunits : Nat.card Kˣ = p - 1 := by
    rw [Nat.card_units, hKp]
  have hdvd' : d ∣ Nat.card Kˣ := hKunits ▸ hdvd
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' d hdvd'
  set hS : StatedSp 2 K := SymplecticTorusWeyl.torusHom (Pi.mulSingle (0 : Fin 2) a) with hSdef
  set hP : StatedProj (StatedSp 2 K) := SymplecticFlag.proj 2 K hS with hPdef
  have hS_order : orderOf hS = d := by
    rw [hSdef, orderOf_injective (SymplecticTorusWeyl.torusHom (r := 2) (k := K))
      SymplecticTorusWeyl.torusHom_injective, orderOf_piMulSingle, ha]
  have hS_not : hS ∉ SymplecticHigher.spScalars 2 K := by
    intro hmem
    have hdvd2 : d ∣ Nat.card (SymplecticHigher.spScalars 2 K) := by
      rw [← hS_order]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    rw [CFSG.ClassicalInvolution.card_scalars_subgroupOf_statedSp h2 (by norm_num)] at hdvd2
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hdvd2)
  have hP_order_dvd : orderOf hP ∣ d := by
    rw [hPdef, ← hS_order]
    exact orderOf_map_dvd (SymplecticFlag.proj 2 K) hS
  have hP_ne_one : orderOf hP ≠ 1 := by
    intro h1
    have hmem : hS ∈ (SymplecticFlag.proj 2 K).ker := by
      rw [MonoidHom.mem_ker, ← hPdef, orderOf_eq_one_iff.mp h1]
    rw [SymplecticHigher.ker_proj] at hmem
    exact hS_not hmem
  have hP_order : orderOf hP = d := by
    rcases (Nat.dvd_prime hd).mp hP_order_dvd with h | h
    · exact absurd h hP_ne_one
    · exact h
  have hP_mem : hP ∈ H := ⟨hS, SymplecticTorusWeyl.torusHom_mem_torus _, rfl⟩
  have hdH : d ∣ Nat.card H := by
    rw [← hP_order]
    exact Subgroup.orderOf_dvd_natCard H hP_mem
  have hw0mem : SymplecticFlag.dotW K spFourSwap ∈
      Subgroup.normalizer (T : Set (StatedSp 2 K)) := dotW_mem_normalizer_torus spFourSwap
  have hw0N : SymplecticFlag.proj 2 K (SymplecticFlag.dotW K spFourSwap) ∈
      Subgroup.normalizer (H : Set (StatedProj (StatedSp 2 K))) :=
    Subgroup.le_normalizer_map (SymplecticFlag.proj 2 K) ⟨_, hw0mem, rfl⟩
  have hnotB : SymplecticFlag.proj 2 K (SymplecticFlag.dotW K spFourSwap) ∉
      SymplecticFlag.projBorel 2 K := proj_not_mem_projBorel dotW_spFourSwap_not_mem_stab_one
  have hnot1 : SymplecticFlag.proj 2 K (SymplecticFlag.dotW K spFourSwap) ∉
      SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) :=
    proj_not_mem_projStabilizer dotW_spFourSwap_not_mem_stab_one
  have hnot2 : SymplecticFlag.proj 2 K (SymplecticFlag.dotW K spFourSwap) ∉
      SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2) :=
    proj_not_mem_projStabilizer dotW_spFourSwap_not_mem_stab_two
  have hnotY : SymplecticFlag.proj 2 K (SymplecticFlag.dotW K spFourSwap) ∉ Y := by
    rcases hclas with h | h | h
    · rw [h]; exact hnotB
    · rw [h]; exact hnot1
    · rw [h]; exact hnot2
  exact hnotY (hY.normalizer_le_of_dvd hd hHle hHcomm hdH hw0N)

private theorem false_of_not_dvd_pred {K : Type} [Field K] [Finite K] {p d : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (hKp : Nat.card K = p) (h2 : (2 : K) ≠ 0) (hnot : ¬ d ∣ p - 1)
    (hdP : d ∣ Nat.card (StatedProj (StatedSp 2 K)))
    {Y : Subgroup (StatedProj (StatedSp 2 K))}
    (hY : IsBorelDLocal p d Y)
    (hclas : Y = SymplecticFlag.projBorel 2 K ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 1) ∨
      Y = SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K 2)) : False := by
  have hPcard : Nat.card (StatedProj (StatedSp 2 K)) * 2 =
      p ^ 4 * (p ^ 2 - 1) * (p ^ 4 - 1) := by
    have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero
      (K := K) h2 (n := 2) (by norm_num)
    rw [hKp] at h
    have hprod : (∏ j ∈ Finset.Icc 1 2, (p ^ (2 * j) - 1)) =
        (p ^ 2 - 1) * (p ^ 4 - 1) := by
      have e : Finset.Icc 1 2 = {1, 2} := by decide
      rw [e]
      simp
    rw [hprod] at h
    have hp4 : p ^ 2 ^ 2 = p ^ 4 := by norm_num
    rw [hp4, ← mul_assoc] at h
    exact h
  have hdvdP : d ∣ p ^ 4 * (p ^ 2 - 1) * (p ^ 4 - 1) := by
    have h : d ∣ Nat.card (StatedProj (StatedSp 2 K)) * 2 := dvd_mul_of_dvd_left hdP 2
    rwa [hPcard] at h
  have hnotp4 : ¬ d ∣ p ^ 4 := by
    intro h
    exact hdp ((Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow h))
  have hsq1 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using sq_tsub_sq p 1
  have hsq2 : p ^ 4 - 1 = (p ^ 2 + 1) * (p ^ 2 - 1) := by
    have h := sq_tsub_sq (p ^ 2) 1
    have hp4 : (p ^ 2) ^ 2 = p ^ 4 := by ring
    rwa [hp4] at h
  have hmain : d ∣ (p + 1) * (p ^ 2 + 1) := by
    have hdvdP' : d ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
      rw [← mul_assoc]
      exact hdvdP
    have h1 : d ∣ (p ^ 2 - 1) * (p ^ 4 - 1) := by
      rcases (hd.dvd_mul).mp hdvdP' with h | h
      · exact absurd h hnotp4
      · exact h
    rw [hsq1, hsq2] at h1
    rcases (hd.dvd_mul).mp h1 with hL | hR
    · rcases (hd.dvd_mul).mp hL with h' | h'
      · exact h'.mul_right _
      · exact absurd h' hnot
    · rcases (hd.dvd_mul).mp hR with h' | h'
      · exact h'.mul_left _
      · rw [hsq1] at h'
        rcases (hd.dvd_mul).mp h' with h'' | h''
        · exact h''.mul_right _
        · exact absurd h'' hnot
  have hIndex : ∀ i : ℕ, (i = 1 ∨ i = 2) →
      (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K i)).index =
        (p + 1) * (p ^ 2 + 1) := by
    intro i hi
    have hi2 : i ≤ 2 := by omega
    have hi1 : 1 ≤ i := by omega
    have hW0 : SymplecticFlag.flag 2 K i ≠ ⊥ := by
      intro hbot
      have hf := SymplecticHigher.finrank_flag (r := 2) (K := K) (i := i) (by omega)
      rw [hbot, finrank_bot] at hf
      omega
    have hWiso : SymplecticFlag.IsTotallyIsotropic (pairedSympForm K 2)
        (SymplecticFlag.flag 2 K i) :=
      SymplecticHigher.isCompleteIsotropicFlag_flag.2.2 i hi2
    have hidx := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.index_projStabilizer_isotropic
      (F := K) hW0 hWiso
    rwa [hKp] at hidx
  have hdvdY : d ∣ Nat.card Y := by
    have hmul : d ∣ Nat.card Y * Y.index := by
      rw [Subgroup.card_mul_index]
      exact hdP
    exact (hd.coprime_iff_not_dvd.mpr (hY.not_dvd_index hd)).dvd_of_dvd_mul_right hmul
  rcases hclas with hYc | hYc | hYc
  · have hBcard : Nat.card (SymplecticFlag.borelSubgroup 2 K) = p ^ 4 * (p - 1) ^ 2 := by
      rw [SymplecticFlag.card_borelSubgroup, hKp]
      norm_num
    have hdvdB : d ∣ p ^ 4 * (p - 1) ^ 2 := by
      have h1 : d ∣ Nat.card (SymplecticFlag.borelSubgroup 2 K) :=
        (hYc ▸ hdvdY).trans (Subgroup.card_map_dvd (SymplecticFlag.borelSubgroup 2 K)
          (SymplecticFlag.proj 2 K))
      rwa [hBcard] at h1
    rcases (hd.dvd_mul).mp hdvdB with h | h
    · exact hnotp4 h
    · exact hnot (hd.dvd_of_dvd_pow h)
  · rw [hYc] at hY
    exact (hY.not_dvd_index hd) (hIndex 1 (Or.inl rfl) ▸ hmain)
  · rw [hYc] at hY
    exact (hY.not_dvd_index hd) (hIndex 2 (Or.inr rfl) ▸ hmain)

theorem not_isBorelDLocal_psp_four {G : Type} [Group G] [Finite G] {p d : ℕ} {Y : Subgroup G}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (hdG : d ∣ Nat.card G) (hG : StatedClassicalModel G .PSp 2 p 1) :
    ¬ IsBorelDLocal p d Y := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hG
  letI := hKfield
  letI := hKfinite
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hKcard
  have hKp : Nat.card K = p := by simpa using hKcard
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hKcard
  intro hY
  have hY_e : IsBorelDLocal p d (Y.map e.toMonoidHom) := hY.map_equiv e
  obtain ⟨T, hT⟩ := SymplecticFlag.exists_sylow_projUnipotent (K := K) p (r := 2) (by norm_num)
  obtain ⟨g, hYg, hNg⟩ := hY_e.exists_conj hp T
  set Yg : Subgroup (StatedProj (StatedSp 2 K)) :=
    (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom with hYgdef
  have hB : SymplecticFlag.projBorel 2 K ≤ Yg := by
    have hnorm : Subgroup.normalizer ((T : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K))) = SymplecticFlag.projBorel 2 K := by
      rw [hT]
      exact SymplecticHigher.normalizer_projUnipotent p (by norm_num)
    rwa [hnorm] at hNg
  have hclas := overgroup_projBorel hB hYg.lt_top
  have hdP : d ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
    rwa [Nat.card_congr e.toEquiv] at hdG
  by_cases hdvd : d ∣ p - 1
  · exact false_of_dvd_pred hp hp2 hd hd2 hdp hKp h2 hdvd hYg hB hclas
  · exact false_of_not_dvd_pred hp hp2 hd hd2 hdp hKp h2 hdvd hdP hYg hclas

end CFSG.LocalAnalysis.AGL81I.Section3
