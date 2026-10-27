module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Criterion
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut eq_or_eq_top_of_index_dvd_two)

@[expose] def SmallNormalFree (C : Type*) [Group C] : Prop :=
  ∀ B : Subgroup (C ⧸ CFSG.Assembly.oddCore C), B.Normal →
    ¬ (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))

theorem SmallNormalFree.of_noNormalFour {C : Type*} [Group C] (hO : CFSG.Assembly.oddCore C = ⊥)
    (hN : NoNormalFour C) : SmallNormalFree C := by
  intro B hB hiso
  let e : C ⧸ CFSG.Assembly.oddCore C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hBn : (B.map e.toMonoidHom).Normal := hB.map _ e.surjective
  obtain ⟨h4, h24⟩ := hN _ hBn
  have eB : B ≃* B.map e.toMonoidHom := e.subgroupMap B
  rcases hiso with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
  · exact h4.false (eB.symm.trans i)
  · exact h24.false (eB.symm.trans i)

theorem SmallNormalFree.of_fourClassesLarge {C : Type*} [Group C] [Finite C]
    (hO : CFSG.Assembly.oddCore C = ⊥) (hF : FourClassesLarge C) : SmallNormalFree C :=
  .of_noNormalFour hO hF.noNormalFour

theorem SmallNormalFree.of_no_orderOf_four {C : Type*} [Group C] [Finite C]
    (hO : CFSG.Assembly.oddCore C = ⊥) (h4 : ∀ x : C, x ^ 4 = 1 → x ^ 2 = 1) :
    SmallNormalFree C :=
  .of_fourClassesLarge hO fun x hx hx2 => absurd (h4 x hx) hx2

theorem SmallNormalFree.of_mulEquiv {C C' : Type*} [Group C] [Group C'] (e : C ≃* C')
    (h : SmallNormalFree C) : SmallNormalFree C' := by
  intro B' hB' hiso
  let q : C ⧸ CFSG.Assembly.oddCore C ≃* C' ⧸ CFSG.Assembly.oddCore C' :=
    QuotientGroup.congr _ _ e (CFSG.EvenSmallLie.oddCore_map_mulEquiv e)
  have hB : (B'.comap q.toMonoidHom).Normal := hB'.comap _
  have eB : B'.comap q.toMonoidHom ≃* B' := (q.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective q.surjective B'))
  refine h _ hB ?_
  rcases hiso with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
  · exact Or.inl ⟨eB.trans i⟩
  · exact Or.inr ⟨eB.trans i⟩

theorem SmallNormalFree.centralizer_of_centralizerIn {G : Type*} [Group G] (K : Subgroup G)
    [Finite K] (t : K) (hO : CFSG.Assembly.oddCore (centralizer ({t} : Set K)) = ⊥)
    (hF : FourClassesLarge (centralizerIn K (t : G))) :
    SmallNormalFree (centralizer ({t} : Set K)) :=
  .of_fourClassesLarge hO (FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv K t) hF)

theorem hypothesisOne_of_centralizer_in {Y : Type*} [Group Y]
    (h : ∀ J : Subgroup (MulAut Y), innAut Y ≤ J → ∀ u : J, orderOf u = 2 →
      SmallNormalFree (centralizer ({u} : Set J))) : HypothesisOne Y := by
  intro M hM x hxM hx2 B hB hiso
  have hu : orderOf (⟨x, hxM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have h' := SmallNormalFree.of_mulEquiv (centralizerSubgroupEquiv M (⟨x, hxM⟩ : M))
    (h M hM ⟨x, hxM⟩ hu)
  exact h' B hB hiso

theorem map_conj_centralizer {Y : Type*} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) (y : Y) :
    (centralizer ({y} : Set Y)).map (MulAut.conj : Y →* MulAut Y) =
      innAut Y ⊓ centralizer ({MulAut.conj y} : Set (MulAut Y)) := by
  ext α
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, hc]
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, ?_, rfl⟩
    apply hinj
    rw [map_mul, map_mul]
    exact hc

@[expose] noncomputable def centralizerInnEquiv {Y : Type*} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) (y : Y) :
    centralizer ({y} : Set Y) ≃*
      ↥(innAut Y ⊓ centralizer ({MulAut.conj y} : Set (MulAut Y))) :=
  ((centralizer ({y} : Set Y)).equivMapOfInjective (MulAut.conj : Y →* MulAut Y) hinj).trans
    (MulEquiv.subgroupCongr (map_conj_centralizer hinj y))

theorem hypothesisOne_of_inner {Y : Type*} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hsurj : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g)
    (h : ∀ y : Y, orderOf y = 2 → SmallNormalFree (centralizer ({y} : Set Y))) :
    HypothesisOne Y := by
  intro M hM x hxM hx2 B hB hiso
  obtain ⟨y, rfl⟩ := hsurj x
  have hy2 : orderOf y = 2 := by
    rw [← hx2]
    exact (orderOf_injective (MulAut.conj : Y →* MulAut Y) hinj y).symm
  have hMtop : M = ⊤ := top_unique fun α _ => by
    obtain ⟨g, rfl⟩ := hsurj α
    exact hM ⟨g, rfl⟩
  subst hMtop
  have h' := SmallNormalFree.of_mulEquiv (centralizerInnEquiv hinj y) (h y hy2)
  have hinn : innAut Y = ⊤ := top_unique fun α _ => by
    obtain ⟨g, rfl⟩ := hsurj α
    exact ⟨g, rfl⟩
  rw [hinn] at h'
  exact h' B hB hiso

theorem hypothesisOne_of_index_two {Y : Type*} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) (hidx : (innAut Y).index ∣ 2)
    (hin : ∀ y : Y, orderOf y = 2 → SmallNormalFree (centralizer ({y} : Set Y)))
    (hout : ∀ x : MulAut Y, orderOf x = 2 →
      SmallNormalFree (centralizer ({x} : Set (MulAut Y)))) : HypothesisOne Y := by
  intro M hM x hxM hx2 B hB hiso
  rcases eq_or_eq_top_of_index_dvd_two hidx hM with rfl | rfl
  · obtain ⟨y, rfl⟩ := hxM
    have hy2 : orderOf y = 2 := by
      rw [← hx2]
      exact (orderOf_injective (MulAut.conj : Y →* MulAut Y) hinj y).symm
    exact SmallNormalFree.of_mulEquiv (centralizerInnEquiv hinj y) (hin y hy2) B hB hiso
  · have h' := SmallNormalFree.of_mulEquiv
      (MulEquiv.subgroupCongr (top_inf_eq (centralizer ({x} : Set (MulAut Y))))).symm
      (hout x hx2)
    exact h' B hB hiso

theorem fourClassesLarge_centralizerIn_of_reps {G : Type*} [Group G] (K : Subgroup G)
    (reps : List G)
    (hcov : ∀ v ∈ K, orderOf v = 2 → ∃ r ∈ reps, ∃ c ∈ K, v = c * r * c⁻¹)
    (hreps : ∀ r ∈ reps, FourClassesLarge (centralizerIn K r)) :
    ∀ v ∈ K, orderOf v = 2 → FourClassesLarge (centralizerIn K v) := by
  intro v hv h2
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov v hv h2
  exact FourClassesLarge.of_mulEquiv (centralizerInConjEquiv K hc r).symm (hreps r hr)

theorem SmallNormalFree.of_forall_pow_four {C : Type*} [Group C] [Finite C]
    (h4 : ∀ x : C, x ^ 4 = 1 → x ^ 2 = 1) : SmallNormalFree C := by
  intro B hB hiso
  obtain ⟨b, hb4, hb2⟩ : ∃ b : C ⧸ CFSG.Assembly.oddCore C, b ^ 4 = 1 ∧ b ^ 2 ≠ 1 := by
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine ⟨((e.symm (Multiplicative.ofAdd 1) : B) : C ⧸ CFSG.Assembly.oddCore C), ?_, ?_⟩
      · rw [← SubgroupClass.coe_pow, ← map_pow]
        have : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by decide
        rw [this, map_one]
        rfl
      · intro h
        have h' : e.symm (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 :=
          Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
        have := congrArg e h'
        rw [map_pow, MulEquiv.apply_symm_apply, map_one e] at this
        revert this
        decide
    · refine ⟨((e.symm (1, Multiplicative.ofAdd 1) : B) : C ⧸ CFSG.Assembly.oddCore C), ?_, ?_⟩
      · rw [← SubgroupClass.coe_pow, ← map_pow]
        have : ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by
          decide
        rw [this, map_one]
        rfl
      · intro h
        have h' : e.symm ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 =
            1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
        have := congrArg e h'
        rw [map_pow, MulEquiv.apply_symm_apply, map_one e] at this
        revert this
        decide
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
  have hodd : Odd (Nat.card (CFSG.Assembly.oddCore C)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.assembly_oddCore_eq]
    exact CFSG.OrderReductions.OddCore.oddCore_odd C
  have hc4 : c ^ 4 ∈ CFSG.Assembly.oddCore C := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hb4
  set m := orderOf (⟨c ^ 4, hc4⟩ : CFSG.Assembly.oddCore C) with hm
  have hmodd : Odd m := by
    have h1 : m ∣ Nat.card (CFSG.Assembly.oddCore C) := by
      rw [hm]
      exact orderOf_dvd_natCard _
    exact hodd.of_dvd_nat h1
  have hcm : (c ^ 4) ^ m = 1 := by
    have := pow_orderOf_eq_one (⟨c ^ 4, hc4⟩ : CFSG.Assembly.oddCore C)
    exact congrArg Subtype.val this
  obtain ⟨j, hj⟩ := hmodd
  have hk4 : m * m = 4 * (j * j + j) + 1 := by rw [hj]; ring
  have hd4 : (c ^ (m * m)) ^ 4 = 1 := by
    calc (c ^ (m * m)) ^ 4 = (c ^ 4) ^ (m * m) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [pow_mul, hcm, one_pow]
  have hdc : ((c ^ (m * m) : C) : C ⧸ CFSG.Assembly.oddCore C) =
      (c : C ⧸ CFSG.Assembly.oddCore C) := by
    rw [QuotientGroup.mk_pow, hk4, pow_succ, pow_mul, hb4, one_pow, one_mul]
  have hd2 : (c ^ (m * m)) ^ 2 ≠ 1 := by
    intro h
    apply hb2
    rw [← hdc, ← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
  exact hd2 (h4 _ hd4)

theorem conj_injective_of_center_eq_bot {Y : Type*} [Group Y] (h : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro g k hgk
  have hx : MulAut.conj (g⁻¹ * k) = 1 := by rw [map_mul, map_inv, hgk, inv_mul_cancel]
  have hmem : g⁻¹ * k ∈ center Y := by
    rw [mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut Y => φ z) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * (g⁻¹ * k) = (g⁻¹ * k * z * (g⁻¹ * k)⁻¹) * (g⁻¹ * k) := by rw [this]
      _ = g⁻¹ * k * z := by group
  rw [h, mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem)

theorem center_eq_bot_of_isSimpleGroup {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h : ¬ (Nat.card Y).Prime) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h0 | h0
  · exact h0
  · exfalso
    let : CommGroup Y := { ‹Group Y› with
      mul_comm := fun a b => (mem_center_iff.mp (h0 ▸ mem_top a) b).symm }
    exact h (IsSimpleGroup.prime_card (α := Y))

theorem hypothesisOne_of_inner_of_forall_pow_four {Y : Type*} [Group Y] [Finite Y]
    (hcenter : center Y = ⊥) (hsurj : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g)
    (h4 : ∀ x : Y, x ^ 4 = 1 → x ^ 2 = 1) : HypothesisOne Y :=
  hypothesisOne_of_inner (conj_injective_of_center_eq_bot hcenter) hsurj fun y _ =>
    SmallNormalFree.of_forall_pow_four fun x hx =>
      Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        apply h4
        rw [← SubgroupClass.coe_pow, hx, OneMemClass.coe_one])

end CFSG.EvenSporadicStandard.HypOne
