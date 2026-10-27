module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open
open scoped commutatorElement

theorem map_mem_center_of_surj {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {z : A} (hz : z ∈ Subgroup.center A) :
    f z ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff]
  intro b
  obtain ⟨a, rfl⟩ := hf b
  have h := Subgroup.mem_center_iff.1 hz a
  rw [← map_mul, ← map_mul, h]

theorem isQuasisimple_of_surj_central {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center A)
    (hA : commutator A = ⊤) (hB : CFSG.Open.IsQuasisimple B) :
    CFSG.Open.IsQuasisimple A := by
  obtain ⟨-, hBs⟩ := hB
  haveI : IsSimpleGroup (B ⧸ Subgroup.center B) := hBs
  let g : A →* B ⧸ Subgroup.center B := (QuotientGroup.mk' (Subgroup.center B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = Subgroup.center A := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxB : f x ∈ Subgroup.center B := (QuotientGroup.eq_one_iff (f x)).1 hx
      have hcomm : ∀ a : A, ⁅x, a⁆ ∈ Subgroup.center A := by
        intro a
        apply hk
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hxB (f a)).symm
      have hcentral : ∀ a b : A, a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
        intro a b
        rw [Subgroup.mem_center_iff.1 (hcomm b) a]
        group
      let ψ : A →* Subgroup.center A :=
        { toFun := fun a => ⟨⁅x, a⁆, hcomm a⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by
            show ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆
            have key : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
              rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
              group
            rw [key, hcentral]) }
      have hcomm' : ∀ u v : Subgroup.center A, u * v = v * u := fun u v =>
        Subtype.ext (by simpa using Subgroup.mem_center_iff.1 v.2 (u : A))
      have hkill : commutator A ≤ ψ.ker := by
        show ⁅(⊤ : Subgroup A), ⊤⁆ ≤ ψ.ker
        refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm' _ _)
      have htop : (⊤ : Subgroup A) ≤ ψ.ker := by rw [← hA]; exact hkill
      have hx1 : ∀ a : A, ⁅x, a⁆ = 1 := fun a => congrArg Subtype.val (htop (Subgroup.mem_top a))
      exact Subgroup.mem_center_iff.2 fun a =>
        (commutatorElement_eq_one_iff_mul_comm.1 (hx1 a)).symm
    · intro z hz
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (f z)).2 (map_mem_center_of_surj f hf hz)
  have e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  refine ⟨hA, MulEquiv.isSimpleGroup e⟩

theorem isQuasisimple_quot_of_le_center {A : Type*} [Group A] [Finite A]
    (hA : CFSG.Open.IsQuasisimple A) (M : Subgroup A) [M.Normal]
    (hM : M ≤ Subgroup.center A) (hMt : M ≠ ⊤) :
    CFSG.Open.IsQuasisimple (A ⧸ M) := by
  obtain ⟨hAc, hAs⟩ := hA
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := hAs
  have hπ : Function.Surjective (QuotientGroup.mk' M : A →* A ⧸ M) :=
    QuotientGroup.mk'_surjective M
  have hnt : Nontrivial (A ⧸ M) := QuotientGroup.nontrivial_iff.2 hMt
  have hcomm_top : commutator (A ⧸ M) = ⊤ := by
    have h1 : (⁅(⊤ : Subgroup A), ⊤⁆ : Subgroup A) = ⊤ := hAc
    have h := Subgroup.map_commutator (⊤ : Subgroup A) (⊤ : Subgroup A) (QuotientGroup.mk' M)
    rw [h1, Subgroup.map_top_of_surjective _ hπ] at h
    exact h.symm
  let g : A →* (A ⧸ M) ⧸ Subgroup.center (A ⧸ M) :=
    (QuotientGroup.mk' (Subgroup.center (A ⧸ M))).comp (QuotientGroup.mk' M)
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hπ
  have hZ : Subgroup.center A ≤ g.ker := fun z hz => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (map_mem_center_of_surj _ hπ hz)
  have hnorm : ((g.ker).map (QuotientGroup.mk' (Subgroup.center A))).Normal :=
    Subgroup.Normal.map (inferInstance : g.ker.Normal) _ (QuotientGroup.mk'_surjective _)
  refine ⟨hcomm_top, ?_⟩
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((g.ker).map (QuotientGroup.mk' (Subgroup.center A))) with hbot | htop
  · have hK : g.ker = Subgroup.center A := by
      apply le_antisymm
      · intro x hx
        have hx' : (QuotientGroup.mk x : A ⧸ Subgroup.center A) ∈
            (g.ker).map (QuotientGroup.mk' (Subgroup.center A)) := Subgroup.mem_map_of_mem _ hx
        rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hx'
        exact hx'
      · exact hZ
    have e : A ⧸ Subgroup.center A ≃* (A ⧸ M) ⧸ Subgroup.center (A ⧸ M) :=
      (QuotientGroup.quotientMulEquivOfEq hK).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg)
    exact MulEquiv.isSimpleGroup e.symm
  · exfalso
    have hall : ∀ x : A, x ∈ g.ker := by
      intro x
      have hx : (QuotientGroup.mk x : A ⧸ Subgroup.center A) ∈
          (g.ker).map (QuotientGroup.mk' (Subgroup.center A)) := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hz : y⁻¹ * x ∈ Subgroup.center A := QuotientGroup.eq.1 hyx
      have hxy : x = y * (y⁻¹ * x) := by group
      rw [hxy]
      exact g.ker.mul_mem hy (hZ hz)
    have hcenter : ∀ u : A ⧸ M, u ∈ Subgroup.center (A ⧸ M) := by
      intro u
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      exact (QuotientGroup.eq_one_iff _).1 (hall x)
    have hbot' : commutator (A ⧸ M) ≤ ⊥ := by
      show ⁅(⊤ : Subgroup (A ⧸ M)), ⊤⁆ ≤ ⊥
      refine Subgroup.commutator_le.2 fun u _ v _ => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 (hcenter u) v).symm
    have key : ∀ u : A ⧸ M, u = 1 := fun u => by
      have hu : u ∈ commutator (A ⧸ M) := by rw [hcomm_top]; exact Subgroup.mem_top u
      exact Subgroup.mem_bot.1 (hbot' hu)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (A ⧸ M)
    exact hab ((key a).trans (key b).symm)

theorem commute_of_isSubnormal_of_quasisimple {X : Type*} [Group X] {B : Subgroup X}
    (hB : CFSG.Open.IsQuasisimple B) {A : Subgroup X} (hsn : CFSG.Open.IsSubnormal A B)
    (hne : A ≠ B) : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  induction hsn with
  | refl => exact absurd rfl hne
  | @step H M K hHM hHn hMK ih =>
    by_cases hMB : M = K
    · subst hMB
      have hHtop : H.subgroupOf M ≠ ⊤ := by
        intro h
        rw [Subgroup.subgroupOf_eq_top] at h
        exact hne (le_antisymm hHM h)
      have hcen := le_center_of_normal_of_isQuasisimple hB hHn hHtop
      intro x hx y hy
      have := Subgroup.mem_center_iff.1 (hcen (show (⟨x, hHM hx⟩ : M) ∈ H.subgroupOf M from hx))
        ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have hMB' := ih hB hMB
      intro x hx y hy
      exact hMB' x (hHM hx) y hy

theorem components_commute_of_ne {X : Type*} [Group X] [Finite X] {H L M : Subgroup X}
    (hL : CFSG.Open.IsComponentOf L H) (hM : CFSG.Open.IsComponentOf M H) (hLM : L ≠ M) :
    ∀ x ∈ L, ∀ y ∈ M, x * y = y * x := by
  rcases CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm hL hM.1 hM.2.1 with
    hle | hcomm
  ·
    have hsn : CFSG.Open.IsSubnormal L M :=
      CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hL.2.1 hle hM.1
    exact commute_of_isSubnormal_of_quasisimple hM.2.2 hsn hLM
  · intro x hx y hy
    have hc : L ≤ Subgroup.centralizer (M : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hc hx) y hy).symm

theorem dvd_card_center_quot_of_pPrimeCore_eq_bot {A : Type*} [Group A] [Finite A] {p : ℕ}
    [hp : Fact p.Prime] (hA : CFSG.Open.IsQuasisimple A) (h0 : CFSG.pPrimeCore p A = ⊥) :
    p ∣ Nat.card (A ⧸ Subgroup.center A) := by
  classical
  obtain ⟨hAc, hAs⟩ := hA
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := hAs
  haveI : Nontrivial A := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (A ⧸ Subgroup.center A)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨x, y, fun h => hab (congrArg _ h)⟩⟩
  by_contra hnd
  obtain ⟨R⟩ : Nonempty (Sylow p A) := inferInstance
  have hRc : ∀ r ∈ (R : Subgroup A), r ∈ Subgroup.center A := by
    intro r hr
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
    have hrk : r ^ p ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf ((QuotientGroup.mk' (Subgroup.center A) : A →* A ⧸ Subgroup.center A) r)
        ∣ p ^ k :=
      (orderOf_map_dvd _ r).trans (orderOf_dvd_of_pow_eq_one hrk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 h1
    have h2 := orderOf_dvd_natCard
      ((QuotientGroup.mk' (Subgroup.center A) : A →* A ⧸ Subgroup.center A) r)
    have hj0 : j = 0 := by
      by_contra hj0
      exact hnd ((dvd_pow_self p hj0).trans (hj ▸ h2))
    have h3 : (QuotientGroup.mk' (Subgroup.center A) : A →* A ⧸ Subgroup.center A) r = 1 :=
      orderOf_eq_one_iff.1 (by rw [hj, hj0, pow_zero])
    exact (QuotientGroup.eq_one_iff r).1 h3
  have hP : Subgroup.normalizer ((R : Subgroup A) : Set A) ≤
      Subgroup.centralizer ((R : Subgroup A) : Set A) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_center_iff.1 (hRc r hr) g).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' R hP
  set M := (MonoidHom.transferSylow R hP).ker with hMdef
  have hcard : Nat.card M * Nat.card (R : Subgroup A) = Nat.card A := hcomp.card_mul
  have hindex := Subgroup.card_mul_index (R : Subgroup A)
  have hMidx : Nat.card M = (R : Subgroup A).index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (R : Subgroup A)))
    rw [hcard, mul_comm, hindex]
  have hnM : ¬ p ∣ Nat.card M := by
    rw [hMidx]
    exact Sylow.not_dvd_index R
  have hMbot : M = ⊥ := by
    have hcop : Nat.Coprime p (Nat.card M) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hnM
    have hle : M ≤ CFSG.pPrimeCore p A :=
      le_sSup (show M ∈ {K : Subgroup A | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
        ⟨inferInstance, hcop⟩)
    rw [h0] at hle
    exact le_bot_iff.1 hle
  have hRidx : (R : Subgroup A).index = 1 := by
    rw [← hMidx, hMbot, Subgroup.card_bot]
  have hRtop : (R : Subgroup A) = ⊤ := Subgroup.index_eq_one.1 hRidx
  have hPG : IsPGroup p A := by
    intro g
    have hg : g ∈ (R : Subgroup A) := by rw [hRtop]; exact Subgroup.mem_top g
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨g, hg⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  haveI := hPG.isNilpotent
  have hlt : commutator A < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial A
  exact hlt.ne hAc

theorem not_dvd_card_sSup_components {S : Type*} [Group S] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (H : Subgroup S) (h : ∀ M : Subgroup S, CFSG.Open.IsComponentOf M H → ¬ p ∣ Nat.card M) :
    ¬ p ∣ Nat.card ↥(sSup {M : Subgroup S | CFSG.Open.IsComponentOf M H}) := by
  classical
  have hfin : Set.Finite {M : Subgroup S | CFSG.Open.IsComponentOf M H} := Set.toFinite _
  have key : ∀ F : Finset (Subgroup S), (∀ M ∈ F, CFSG.Open.IsComponentOf M H) →
      ¬ p ∣ Nat.card ↥(F.sup id) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sup_empty, Subgroup.card_bot]
      exact hp.out.not_dvd_one
    | @insert A F hA ih =>
      intro hcomp
      have hAc : CFSG.Open.IsComponentOf A H := hcomp A (Finset.mem_insert_self _ _)
      have hF : ∀ M ∈ F, CFSG.Open.IsComponentOf M H :=
        fun M hM => hcomp M (Finset.mem_insert_of_mem hM)
      have hBn : F.sup id ≤ Subgroup.normalizer ((A : Subgroup S) : Set S) := by
        refine Finset.sup_le fun M hM => ?_
        have hne : A ≠ M := fun e => hA (e ▸ hM)
        have hMc : M ≤ Subgroup.centralizer ((A : Subgroup S) : Set S) := by
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact components_commute_of_ne hAc (hF M hM) hne a ha y hy
        exact hMc.trans (Subgroup.centralizer_le_normalizer _)
      have hcardeq := card_sup_mul_card_inf_of_le_normalizer hBn
      intro hdvd
      rw [Finset.sup_insert] at hdvd
      have h2 : p ∣ Nat.card ↥(A ⊔ F.sup id) * Nat.card ↥(A ⊓ F.sup id) :=
        Dvd.dvd.mul_right (show p ∣ Nat.card ↥(A ⊔ F.sup id) from hdvd) _
      rw [hcardeq] at h2
      rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h3 | h3
      · exact h A hAc h3
      · exact ih hF h3
  have hsup : sSup {M : Subgroup S | CFSG.Open.IsComponentOf M H} = hfin.toFinset.sup id := by
    rw [Finset.sup_id_eq_sSup, Set.Finite.coe_toFinset]
  rw [hsup]
  apply key
  intro M hM
  exact (Set.Finite.mem_toFinset hfin).1 hM

end CFSG.LocalAnalysis.GLTheoremA.I142
