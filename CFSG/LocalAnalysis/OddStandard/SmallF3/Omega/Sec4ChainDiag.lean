module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private lemma mem_centerIn_iff {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2,
      fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩,
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

private lemma inf_le_centerIn {K K' : Subgroup G}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) : K ⊓ K' ≤ centerIn K := by
  intro a ha
  exact (mem_centerIn_iff a).mpr ⟨ha.1, fun k hk => (hcomm k hk a ha.2).symm⟩

private lemma commute_commutatorElement {a b c : G} (hab : Commute a b) (hac : Commute a c) :
    Commute a ⁅b, c⁆ := by
  rw [commutatorElement_def]
  exact ((hab.mul_right hac).mul_right hab.inv_right).mul_right hac.inv_right

private lemma commutator_mul_mul_eq {a a' b b' : G}
    (haa' : Commute a a') (hab : Commute a b) (hab' : Commute a b')
    (ha'b : Commute a' b) (ha'b' : Commute a' b') :
    ⁅a * b, a' * b'⁆ = ⁅b, b'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅a, a' * b'⁆ = 1 := (haa'.mul_right hab').commutator_eq
  have hx : Commute a ⁅b, a' * b'⁆ := commute_commutatorElement hab (haa'.mul_right hab')
  have h2 : a * ⁅b, a' * b'⁆ * a⁻¹ = ⁅b, a' * b'⁆ := by
    rw [hx.eq]
    group
  have h3 : ⁅b, a' * b'⁆ = ⁅b, b'⁆ := by
    rw [ha'b'.eq, commutatorElement_mul_right_eq_mul_conj, ha'b.symm.commutator_eq, mul_one]
    group
  rw [h1, mul_one, h2, h3]

private lemma center_commutator_eq_bot {H : Type*} [Group H] (N : Subgroup H) :
    ⁅Subgroup.center H, N⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  exact Subgroup.mem_center_iff.mp hz n

private lemma commutator_center_eq_bot {H : Type*} [Group H] (N : Subgroup H) :
    ⁅N, Subgroup.center H⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_center_iff.mp hz n).symm

private lemma quotient_center_eq_one_iff {K : Subgroup G} (a : ↥K) :
    (a : ↥K ⧸ Subgroup.center ↥K) = 1 ↔ (a : G) ∈ centerIn K := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨fun h => (mem_centerIn_iff (a : G)).mpr
      ⟨a.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨k, hk⟩)).symm⟩,
    fun h => Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (((mem_centerIn_iff (a : G)).mp h).2 y y.2).symm⟩

private theorem exists_center_quotient_lift {K K' : Subgroup G}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) :
    ∃ π : ↥(K ⊔ K') →* ↥K ⧸ Subgroup.center ↥K,
      ∀ j : ↥(K ⊔ K'), π j = 1 ↔ ∃ a ∈ centerIn K, ∃ b ∈ K', (j : G) = a * b := by
  classical
  haveI : Nonempty (↥K × ↥K') := ⟨(1, 1)⟩
  let f : ↥K × ↥K' →* ↥(K ⊔ K') :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), mul_mem_sup x.1.2 x.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [hcomm y.1 y.1.2 x.2 x.2.2]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group) }
  have hf : Function.Surjective f := by
    have htop : K.subgroupOf (K ⊔ K') ⊔ K'.subgroupOf (K ⊔ K') = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    apply MonoidHom.range_eq_top.mp
    rw [eq_top_iff, ← htop]
    apply sup_le
    · rintro a ha
      exact ⟨(⟨(a : G), ha⟩, 1), Subtype.ext (by simp [f])⟩
    · rintro b hb
      exact ⟨(1, ⟨(b : G), hb⟩), Subtype.ext (by simp [f])⟩
  let g : ↥K × ↥K' →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (MonoidHom.fst ↥K ↥K')
  have hker : f.ker ≤ g.ker := by
    rintro ⟨a, b⟩ hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hmem : (a : G) * (b : G) = 1 := by
      have := congrArg Subtype.val hx
      simpa [f] using this
    have hbK : (b : G) ∈ K := by
      rw [eq_inv_of_mul_eq_one_right hmem]
      exact K.inv_mem a.2
    have hbZ : (b : G) ∈ centerIn K := inf_le_centerIn hcomm ⟨hbK, b.2⟩
    have haZ : (a : G) ∈ centerIn K := by
      rw [eq_inv_of_mul_eq_one_left hmem]
      exact (centerIn K).inv_mem hbZ
    change (a : ↥K ⧸ Subgroup.center ↥K) = 1
    exact (quotient_center_eq_one_iff a).mpr haZ
  let π : ↥(K ⊔ K') →* ↥K ⧸ Subgroup.center ↥K :=
    f.liftOfRightInverseAux (Function.invFun f) (Function.rightInverse_invFun hf) g hker
  have hπf : ∀ x : ↥K × ↥K', π (f x) = (x.1 : ↥K ⧸ Subgroup.center ↥K) := by
    intro x
    exact MonoidHom.liftOfRightInverseAux_comp_apply (f := f) (f_inv := Function.invFun f)
      (Function.rightInverse_invFun hf) g hker x
  refine ⟨π, ?_⟩
  intro j
  constructor
  · intro hj
    obtain ⟨⟨a, b⟩, hab⟩ := hf j
    have hjab : (j : G) = (a : G) * (b : G) := by
      have := congrArg Subtype.val hab
      simpa [f] using this.symm
    have hja : (a : ↥K ⧸ Subgroup.center ↥K) = 1 := by
      rw [← hab, hπf] at hj
      exact hj
    exact ⟨a, (quotient_center_eq_one_iff a).mp hja, b, b.2, hjab⟩
  · rintro ⟨a, haZ, b, hb, hjab⟩
    have haK : a ∈ K := ((mem_centerIn_iff a).mp haZ).1
    have hfj : f (⟨a, haK⟩, ⟨b, hb⟩) = j := Subtype.ext (by simpa [f] using hjab.symm)
    rw [← hfj, hπf]
    exact (quotient_center_eq_one_iff ⟨a, haK⟩).mpr haZ

theorem ctrQ_dvd_of_le_sup_of_commute [Finite G] {X K K' : Subgroup G} (hX : IsQuasisimple X)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hle : X ≤ K ⊔ K') :
    X ≤ K' ∨
      (ctrQ X ∣ ctrQ K ∧ (ctrQ X = ctrQ K → Nonempty (X ⧸ center X ≃* K ⧸ center K))) := by
  classical
  obtain ⟨π, hπ⟩ := exists_center_quotient_lift hcomm
  let ψ : ↥X →* ↥K ⧸ Subgroup.center ↥K := π.comp (Subgroup.inclusion hle)
  let N : Subgroup ↥X := ψ.ker
  by_cases hNcenter : N ≤ Subgroup.center ↥X
  ·
    have hNker : N ≤ (QuotientGroup.mk' (Subgroup.center ↥X)).ker := by
      simpa [QuotientGroup.ker_mk'] using hNcenter
    have hq : Function.Surjective
        (QuotientGroup.lift N (QuotientGroup.mk' (Subgroup.center ↥X)) hNker) :=
      QuotientGroup.lift_surjective_of_surjective N (QuotientGroup.mk' (Subgroup.center ↥X))
        (QuotientGroup.mk'_surjective _) hNker
    have h1 : ctrQ X ∣ Nat.card (↥X ⧸ N) := Subgroup.card_dvd_of_surjective hq
    have h2 : Nat.card (↥X ⧸ N) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have h3 : Nat.card ψ.range ∣ ctrQ K := Subgroup.card_subgroup_dvd_card ψ.range
    refine Or.inr ⟨h1.trans (h2.symm ▸ h3), ?_⟩
    intro hc
    have hrange_eq : Nat.card ψ.range = ctrQ K := Nat.dvd_antisymm h3 (hc ▸ h2 ▸ h1)
    have hNcard : Nat.card (↥X ⧸ N) = Nat.card (↥X ⧸ Subgroup.center ↥X) :=
      (Nat.dvd_antisymm h1 (h2 ▸ hc.symm ▸ h3)).symm
    have hcardN : Nat.card N = Nat.card (Subgroup.center ↥X) := by
      have hmul : Nat.card (↥X ⧸ Subgroup.center ↥X) * Nat.card N =
          Nat.card (↥X ⧸ Subgroup.center ↥X) * Nat.card (Subgroup.center ↥X) := by
        conv_lhs => rw [← hNcard]
        rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup N,
          ← Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)]
      exact mul_left_cancel₀ (by
        haveI : Nonempty (↥X ⧸ Subgroup.center ↥X) := ⟨1⟩
        exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩) hmul
    have hNeq : N = Subgroup.center ↥X :=
      Subgroup.eq_of_le_of_card_ge hNcenter (le_of_eq hcardN.symm)
    have hrange : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq ψ.range hrange_eq
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hNeq).symm.trans
      (QuotientGroup.quotientKerEquivRange ψ)).trans
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv)⟩
  ·
    have hOpen : CFSG.Open.IsQuasisimple ↥X := ⟨Group.isPerfect_def.mp hX.1, hX.2.1⟩
    have hNsup : N ⊔ Subgroup.center ↥X = ⊤ := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hOpen
          (N ⊔ Subgroup.center ↥X) with h | h
      · exact absurd (le_sup_left.trans h) hNcenter
      · exact h
    have hperf : commutator ↥X = ⊤ := Group.isPerfect_def.mp hX.1
    have hcommNN : ⁅N, N⁆ = ⊤ := by
      have hEq : ⁅N ⊔ Subgroup.center ↥X, N ⊔ Subgroup.center ↥X⁆ = ⁅N, N⁆ := by
        rw [Subgroup.commutator_sup_left, Subgroup.commutator_sup_right,
          Subgroup.commutator_sup_right, commutator_center_eq_bot N,
          center_commutator_eq_bot N, center_commutator_eq_bot _]
        simp
      rw [← hEq, hNsup, ← _root_.commutator_def, hperf]
    have hMtop : K'.comap X.subtype = ⊤ := by
      rw [eq_top_iff, ← hcommNN, Subgroup.commutator_le]
      intro n hn n' hn'
      rw [Subgroup.mem_comap, map_commutatorElement]
      have hn1 : π (Subgroup.inclusion hle n) = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hn
      have hn'1 : π (Subgroup.inclusion hle n') = 1 := by
        simpa [ψ] using MonoidHom.mem_ker.mp hn'
      obtain ⟨a, haZ, b, hb, hnab⟩ := (hπ (Subgroup.inclusion hle n)).mp hn1
      obtain ⟨a', ha'Z, b', hb', hna'b'⟩ := (hπ (Subgroup.inclusion hle n')).mp hn'1
      have haK : a ∈ K := ((mem_centerIn_iff a).mp haZ).1
      have hac : ∀ k ∈ K, a * k = k * a := ((mem_centerIn_iff a).mp haZ).2
      have ha'K : a' ∈ K := ((mem_centerIn_iff a').mp ha'Z).1
      have ha'c : ∀ k ∈ K, a' * k = k * a' := ((mem_centerIn_iff a').mp ha'Z).2
      rw [show X.subtype n = a * b by simpa using hnab,
        show X.subtype n' = a' * b' by simpa using hna'b',
        commutator_mul_mul_eq (show Commute a a' from hac a' ha'K)
          (show Commute a b from hcomm a haK b hb)
          (show Commute a b' from hcomm a haK b' hb')
          (show Commute a' b from hcomm a' ha'K b hb)
          (show Commute a' b' from hcomm a' ha'K b' hb')]
      exact Subgroup.commutator_le_self K' (Subgroup.commutator_mem_commutator hb hb')
    left
    intro x hx
    have hxM : (⟨x, hx⟩ : ↥X) ∈ K'.comap X.subtype := by
      rw [hMtop]
      trivial
    simpa using (Subgroup.mem_comap.mp hxM)

theorem ctrQ_dvd_of_walterArrow [Finite G] {X Y : Subgroup G} (h : WalterArrow X Y) :
    ctrQ X ∣ ctrQ Y ∧ ctrQ X ≠ ctrQ Y := by
  unfold WalterArrow at h
  obtain ⟨x, y, hx, hy, hxy, hXc, hYc, hXY, hYcomm⟩ := h
  refine ⟨ctrQ_dvd_of_le hXY, ?_⟩
  intro hc
  have hXYeq : X = Y := eq_of_le_of_ctrQ_eq hYc.isQuasisimple hXY hc
  have hYx : Y ≤ centralizer ({x} : Set G) := hXYeq ▸ hXc.le
  have hbot : ⁅Y, zpowers x⁆ = ⊥ := commutator_zpowers_eq_bot_of_le_centralizer hYx
  rw [hYcomm] at hbot
  exact hYc.ne_bot hbot

theorem ctrQ_dvd_of_walterArrowDiag [Finite G] {X Y : Subgroup G} (h : WalterArrowDiag X Y) :
    ctrQ X ∣ ctrQ Y ∧ (ctrQ X = ctrQ Y → Nonempty (X ⧸ center X ≃* Y ⧸ center Y)) := by
  unfold WalterArrowDiag at h
  obtain ⟨x, y, hx, hy, hxy, hXc, hYc, hle, hne⟩ := h
  have hxCy : x ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hxy
  have hK'c : IsComponentIn (CFSG.conjugate Y x) (centralizer ({y} : Set G)) :=
    hYc.conjugate hxCy
  have hne' : Y ≠ CFSG.conjugate Y x := by
    intro heq
    exact hne (by rw [heq.symm, sup_idem])
  have hcommY : ∀ a ∈ Y, ∀ b ∈ CFSG.conjugate Y x, a * b = b * a :=
    hYc.commute_of_ne hK'c hne'
  rcases ctrQ_dvd_of_le_sup_of_commute hXc.isQuasisimple hcommY hle with hXK' | ⟨hdvd, hiso⟩
  · refine ⟨(ctrQ_conjugate Y x) ▸ ctrQ_dvd_of_le hXK', ?_⟩
    intro hc
    have hc' : ctrQ X = ctrQ (CFSG.conjugate Y x) := hc.trans (ctrQ_conjugate Y x).symm
    have hXeq : X = CFSG.conjugate Y x := eq_of_le_of_ctrQ_eq hK'c.isQuasisimple hXK' hc'
    rw [hXeq]
    exact ⟨(nonempty_equiv_ctrQ_conjugate Y x).some.symm⟩
  · exact ⟨hdvd, hiso⟩

end CFSG.OddStandard.SmallF3.Omega
