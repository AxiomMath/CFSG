module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsSpOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsDefs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)

section Inner

variable {X : Type*} [Group X]

private theorem fixSubgroup_conj_eq_centralizer (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem conj_mem_commutator_of_iSup {ι : Type*} (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (i : ι) :
    ∀ c ∈ ⨆ j, A j, ∀ g ∈ ⁅A i, A i⁆, c * g * c⁻¹ ∈ ⁅A i, A i⁆ := by
  classical
  have hnormA : ∀ c ∈ ⨆ j, A j, ∀ g ∈ A i, c * g * c⁻¹ ∈ A i := by
    intro c hc'
    refine Subgroup.iSup_induction A (C := fun c => ∀ g ∈ A i, c * g * c⁻¹ ∈ A i) hc' ?_ ?_ ?_
    · intro j y hy g hg
      by_cases hji : j = i
      · subst hji
        exact (A j).mul_mem ((A j).mul_mem hy hg) ((A j).inv_mem hy)
      · rw [(hc j i hji y hy g hg).eq, mul_inv_cancel_right]
        exact hg
    · intro g hg
      simpa using hg
    · intro u v hu hv g hg
      have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
      rw [e]
      exact hu _ (hv g hg)
  intro c hc' g hg
  have hmap : (A i).map (MulAut.conj c).toMonoidHom ≤ A i := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnormA c hc' y hy
  have h1 : (⁅A i, A i⁆).map (MulAut.conj c).toMonoidHom ≤ ⁅A i, A i⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact h1 ⟨g, hg, rfl⟩

variable {r : ℕ} {K : Type} [Field K]

open Polynomial CFSG.RankThree.Classical in
theorem compNormal_conj_proj_sp {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hr : 1 ≤ r) (hpℓ : p ≠ ℓ) (s : StatedSp r K)
    (hs : s ^ p = 1) (hs1 : s ≠ 1) : CompNormal (MulAut.conj (SymplecticFlag.proj r K s)) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hq : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set π := SymplecticFlag.proj r K with hπdef
  have hZc : π.ker ≤ Subgroup.center (StatedSp r K) := by
    rw [hπdef, SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hz2 : z ^ 2 = 1 := CFSG.RankThree.PartOne.sq_eq_one_of_proj_eq_one hr hz
    have h1 : z ^ Nat.gcd p 2 = 1 := pow_gcd_eq_one.2 ⟨hzp, hz2⟩
    rwa [(Nat.coprime_primes hp Nat.prime_two).mpr hp2, pow_one] at h1
  have hπs : Function.Surjective π := SymplecticHigher.proj_surjective
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hZp' : Nat.Coprime (Nat.card π.ker) p := by
    rw [hπdef, SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have ha1 : π s ≠ 1 := fun h =>
    hs1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
      π hZc hZp' (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  have ha : orderOf (π s) = p := orderOf_eq_prime (by rw [← map_pow, hs, map_one]) ha1
  have hsp : orderOf s = p := orderOf_eq_prime hs hs1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ hr _
    ha).2 s rfl hsp
  have hsq := (altPrimaryData_spLin hpK hs).squarefree
  haveI : Finite (reciprocalOrbits (spEnd s)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  let A : reciprocalOrbits (spEnd s) → Subgroup (StatedSp r K) :=
    fun O => spSupported s (O : Set K[X])
  have hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b :=
    fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have hcomp := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family π hπs hZc s A hc hjoin
    (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
      hp3 hq hsq blocks O)
  refine compNormal_of_lift π hπs (MulAut.conj s) (MulAut.conj (π s))
    (fun g => by simp [MulAut.conj_apply]) (by rw [← map_pow, hs, map_one])
    (fun z hz => by
      rw [MulAut.conj_apply, (Subgroup.mem_center_iff.1 (hZc hz) s), mul_inv_cancel_right])
    hZp (fun O => ⁅A O, A O⁆) (fun O c hc' g hg => ?_) (fun K' hK' => ?_)
  · rw [fixSubgroup_conj_eq_centralizer, ← hjoin] at hc'
    exact conj_mem_commutator_of_iSup A hc O c hc' g hg
  · obtain ⟨O, -, hO⟩ := hcomp K' hK'
    exact ⟨O, hO⟩

end Inner

section Field

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem compNormal_fieldAut_sp {p : ℕ} (hp : Odd p) (hr : 2 ≤ r) (σ : K ≃+* K) (hσ : σ ^ p = 1)
    (hex : ¬(r = 2 ∧ Nat.card ↥(descentField σ) = 2)) :
    CompNormal (SymplecticHigher.fieldAut r K σ) := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  haveI : Finite ↥(descentField σ) := Subtype.finite
  have hfix : fixSubgroup (SymplecticHigher.fieldAut r K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := r) σ).range := by
    rw [CFSG.RankThree.PartOne.KCSpComm.range_subfieldInj,
      ← CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range hp hσ]
    exact Subgroup.ext fun x =>
      mem_fixSubgroup.trans CFSG.RankThree.PartOne.KCSpComm.mem_spFixedGroup.symm
  let e : ↥(fixSubgroup (SymplecticHigher.fieldAut r K σ)) ≃*
      StatedProj (StatedSp r (descentField σ)) :=
    (MulEquiv.subgroupCongr hfix).trans
      (MonoidHom.ofInjective (CFSG.RankThree.PartOne.KCSpComm.subfieldInj_injective (r := r) σ)).symm
  obtain ⟨hs, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := descentField σ) hr hex
  haveI := hs
  have hnc : ∃ a b : StatedProj (StatedSp r (descentField σ)), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : commutator (StatedProj (StatedSp r (descentField σ))) = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact hcon h g
    have htop := hperf.commutator_eq_top
    rw [hc] at htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne (StatedProj (StatedSp r (descentField σ)))
    have ha : a ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)
  refine compNormal_of_isSimpleGroup e.isSimpleGroup ?_
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end Field

section Dispatch

private theorem center_statedProj_sp_eq_bot {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 2 ≤ r)
    (hne : ¬(r = 2 ∧ Nat.card K = 2)) : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
  obtain ⟨hs, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr hne
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp r K)))
    with h | h
  · exact h
  · exfalso
    have hc : commutator (StatedProj (StatedSp r K)) = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top g) k)
    have htop := hperf.commutator_eq_top
    rw [hc] at htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne (StatedProj (StatedSp r K))
    have ha : a ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)

private theorem card_descentField_ne_two {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) :
    Nat.card ↥(descentField σ) ≠ 2 := by
  intro h2
  haveI := Fintype.ofFinite K
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  have hpow : Fintype.card K =
      Fintype.card ↥(descentField σ) ^ Module.finrank ↥(descentField σ) K :=
    Module.card_eq_pow_finrank
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h2, hK] at hpow
  have h0 : Module.finrank ↥(descentField σ) K ≠ 0 := Module.finrank_pos.ne'
  have hdvd : 2 ∣ ℓ ^ f := hpow ▸ dvd_pow_self 2 h0
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 (Nat.prime_two.dvd_of_dvd_pow hdvd)).symm

theorem compNormal_of_statedPSp {G : Type} [Group G] {r ℓ f p : ℕ}
    (hG : StatedClassicalModel G .PSp r ℓ f) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (β : MulAut G) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : CompNormal β := by
  classical
  obtain ⟨⟨hℓ, hf, hr, -⟩, K, _, _, hK, ⟨e'⟩⟩ := hG
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : ¬(r = 2 ∧ Nat.card K = 2) := fun h => by
    have := h.2
    rw [hK] at this
    have hdvd : ℓ ∣ 2 := this ▸ dvd_pow_self ℓ (by omega)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd)
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ SymplecticHigher.spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  refine CompNormal.of_congr e' ?_
  by_cases hD : MulAut.congr e' β ∈ SymplecticHigher.spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex
        (SymplecticHigher.spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp
      hp2 hD hβ'
    have hZ := center_statedProj_sp_eq_bot hr hne
    have htp : t ^ p = 1 := by
      have hc : t ^ p ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g)
          (show MulAut.conj (t ^ p) = 1 by rw [map_pow, ht]; exact hβ')
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * t ^ p = t ^ p * g * (t ^ p)⁻¹ * t ^ p := by rw [h1]
          _ = t ^ p * g := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    obtain ⟨s, hst, hsp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
        (by omega) hp hp2 htp
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply hβ1'
      rw [← ht, ← hst, map_one, map_one]
    rw [← ht, ← hst]
    exact compNormal_conj_proj_sp hp hp2 hℓ hf hK (by omega) hpℓ s hsp hs1
  ·
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hβ1'
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp _ hE hD hord
    have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    rw [hβeq]
    refine CompNormal.of_conj h⁻¹ ?_
    have : h⁻¹ * (h * SymplecticHigher.fieldAut r K σ * h⁻¹) * h⁻¹⁻¹ =
        SymplecticHigher.fieldAut r K σ := by group
    rw [this]
    exact compNormal_fieldAut_sp (hp.odd_of_ne_two hp2) hr σ hσp
      (fun h => card_descentField_ne_two hℓ hℓ2 hK σ h.2)


theorem genNormalAllOn_sp : GenNormalAllOn S267SpIdx := by
  intro p T _ _ d hd hQ x hx hx1
  obtain ⟨e⟩ := hd.iso
  obtain ⟨d1, hv⟩ := d
  have hchar : d1.characteristic ≠ 2 := hd.charOdd
  have hpq : p ≠ d1.characteristic := hd.ne
  cases d1 with
  | C r q =>
    exact compNormal_of_statedPSp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) (by simpa using hchar)
      hd.prime hd.odd (by simpa using hpq) x hx hx1
  | B n q =>
    obtain rfl : n = 2 := by
      rcases n with _ | _ | _ | n <;> simp_all [S267SpIdx]
    exact compNormal_of_statedPSp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) (by simpa using hchar)
      hd.prime hd.odd (by simpa using hpq) x hx hx1
  | _ => exact absurd hQ (by simp [S267SpIdx])

end Dispatch

section Plane


theorem genPlaneCompOn_sp_of_seitz (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) :
    GenPlaneCompOn S267SpIdx :=
  genPlaneCompOn_of_normalAll hS genNormalAllOn_sp

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
