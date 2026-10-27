module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.VCSetting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem sup_pPrimeCore_eq_of_trivial_action {H : Type} [Group H] [Finite H] {M : Subgroup H}
    {x : H} {T : Subgroup H} {w : H} (h : VCSetting M x T w)
    (htriv : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype) :
    T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  let O' : Subgroup ↥M := pPrimeCore 2 ↥M
  have hO'N : O'.Normal := by dsimp only [O']; infer_instance
  haveI : O'.Normal := hO'N
  let π : ↥M →* ↥M ⧸ O' := QuotientGroup.mk' O'
  let C : Subgroup H := M ⊓ centralizer ({x} : Set H)
  have hTC : T ≤ C := le_inf h.hTM h.hTx
  have hx2 : x ^ 2 = 1 := by simpa [h.ox] using pow_orderOf_eq_one x
  have hxM' : M.map (MulAut.conj x).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h.hxM
  let σ : MulAut ↥M := conjAut M x hxM'
  have hσcoe : ∀ n : ↥M, ((σ n : ↥M) : H) = x * (n : H) * x⁻¹ :=
    fun n => coe_conjAut_apply M x hxM' n
  have hσ2 : σ ^ 2 = 1 := by
    rw [pow_two]
    ext n
    rw [MulAut.mul_apply, hσcoe, hσcoe]
    change x * (x * (n : H) * x⁻¹) * x⁻¹ = (n : H)
    have h1 : x * x = 1 := by rw [← pow_two]; exact hx2
    calc x * (x * (n : H) * x⁻¹) * x⁻¹ = (x * x) * (n : H) * (x * x)⁻¹ := by group
      _ = (n : H) := by rw [h1]; simp
  have hσπ : ∀ n : ↥M, π (σ • n) = π n := by
    intro n
    rw [MulAut.smul_def]
    change (QuotientGroup.mk' O') (σ n) = (QuotientGroup.mk' O') n
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp (htriv (n : H) n.2)
    have ho' : o = (σ n) * n⁻¹ := by
      apply Subtype.ext
      exact hoo
    rw [div_eq_mul_inv, ← ho']
    exact ho
  let K : Subgroup (MulAut ↥M) :=
    { carrier := {p | ∀ n : ↥M, π (p • n) = π n}
      one_mem' := by intro n; simp
      mul_mem' := by
        intro p q hp hq n
        rw [mul_smul, hp (q • n), hq n]
      inv_mem' := by
        intro p hp n
        have h1 : π (p • (p⁻¹ • n)) = π (p⁻¹ • n) := hp (p⁻¹ • n)
        rw [← mul_smul, mul_inv_cancel, one_smul] at h1
        exact h1.symm }
  have hσK : σ ∈ K := hσπ
  have hCMtop : (C.subgroupOf M).map π = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective O' q
    let S : Set ↥M := {n | π n = π m}
    have hSinv : ∀ p : Subgroup.zpowers σ, ∀ n : ↥M, π n = π m → π (p • n) = π m := by
      intro p n hn
      have hp := (Subgroup.zpowers_le.mpr hσK) p.2
      rw [Subgroup.smul_def, hp n, hn]
    have hcardS : Nat.card S = Nat.card O' := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun n => ⟨m⁻¹ * (n : ↥M), by
              have hnS : π (n : ↥M) = π m := n.2
              have h1 : π (m⁻¹ * (n : ↥M)) = 1 := by
                rw [map_mul, map_inv, hnS]
                exact inv_mul_cancel (π m)
              exact (QuotientGroup.eq_one_iff (m⁻¹ * (n : ↥M))).mp h1⟩
          invFun := fun o => ⟨m * (o : ↥M), by
              show π (m * (o : ↥M)) = π m
              have h1 : π (o : ↥M) = 1 := (QuotientGroup.eq_one_iff (o : ↥M)).mpr o.2
              simp [map_mul, h1]⟩
          left_inv := fun n => by
              apply Subtype.ext
              group
          right_inv := fun o => by
              apply Subtype.ext
              group }
    have hSodd : Odd (Nat.card S) := by
      rw [hcardS]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := ↥M) (p := 2))
    have hσ2ord : orderOf σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hσ2
    have hP : IsPGroup 2 (Subgroup.zpowers σ) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact hσ2ord)
    letI : MulAction (Subgroup.zpowers σ) S :=
      { smul := fun p n => ⟨p • (n : ↥M), hSinv p (n : ↥M) n.2⟩
        one_smul := fun n => Subtype.ext (one_smul (Subgroup.zpowers σ) (n : ↥M))
        mul_smul := fun p q n => Subtype.ext (mul_smul p q (n : ↥M)) }
    obtain ⟨c, hc⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hSodd)
    have hfixσ : σ (c : ↥M) = (c : ↥M) := by
      have hfix :=
        MulAction.mem_fixedPoints.mp hc (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ)
      have hval := congrArg Subtype.val hfix
      change (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) • (c : ↥M) = (c : ↥M) at hval
      simpa only [Subgroup.smul_def, MulAut.smul_def] using hval
    have hcCx : ((c : ↥M) : H) ∈ centralizer ({x} : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hcoe : ((σ (c : ↥M) : ↥M) : H) = x * ((c : ↥M) : H) * x⁻¹ := hσcoe (c : ↥M)
      rw [hfixσ] at hcoe
      calc x * ((c : ↥M) : H) = x * ((c : ↥M) : H) * x⁻¹ * x := by group
        _ = ((c : ↥M) : H) * x := by rw [← hcoe]
    have hcCM : (c : ↥M) ∈ C.subgroupOf M := ⟨(c : ↥M).2, hcCx⟩
    exact Subgroup.mem_map.mpr ⟨(c : ↥M), hcCM, c.2⟩
  have hsubCx : (T.subgroupOf (centralizer ({x} : Set H))).IsSubnormal :=
    ((ComponentClassification.HarrisLit.isTwoComponentIn_iff h.hTx).mpr h.hT).2.1
  have hsubC : (T.subgroupOf C).IsSubnormal := by
    have hle : C ≤ centralizer ({x} : Set H) := inf_le_right
    have h' := hsubCx.comap (Subgroup.inclusion hle)
    have heq : (T.subgroupOf (centralizer ({x} : Set H))).comap (Subgroup.inclusion hle) =
        T.subgroupOf C := by
      ext t; rfl
    rwa [heq] at h'
  let πC : ↥C →* ↥M ⧸ O' := π.comp (Subgroup.inclusion (inf_le_left : C ≤ M))
  have hπCsurj : Function.Surjective πC := by
    rw [← MonoidHom.range_eq_top]
    have h1 : πC.range = (C.subgroupOf M).map π := by
      dsimp only [πC]
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [h1, hCMtop]
  let U : Subgroup (↥M ⧸ O') := (T.subgroupOf C).map πC
  have hTqs : ComponentClassification.HarrisLit.IsTwoQuasisimple
      ↥(T.subgroupOf (centralizer ({x} : Set H))) :=
    ((ComponentClassification.HarrisLit.isTwoComponent_iff_isPComponent _).mpr h.hT).2
  have hTperf : Group.IsPerfect ↥T :=
    (ComponentClassification.HarrisLit.isTwoQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.hTx) hTqs).1
  have hTCperf : Group.IsPerfect ↥(T.subgroupOf C) := by
    haveI : Group.IsPerfect ↥T := hTperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hTC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hTC).symm.surjective
  have hUperf : Group.IsPerfect ↥U := by
    haveI : Group.IsPerfect ↥(T.subgroupOf C) := hTCperf
    show Group.IsPerfect ↥((T.subgroupOf C).map πC)
    exact Group.IsPerfect.map (f := πC)
  have hUsub : U.IsSubnormal := hsubC.map hπCsurj
  have hUnebot : U ≠ ⊥ := by
    intro hUbot
    have hwM : w ∈ M := h.hTM h.hwT
    have hwU : π (⟨w, hwM⟩ : ↥M) ∈ U := by
      refine Subgroup.mem_map.mpr ⟨⟨w, hTC h.hwT⟩, ?_, ?_⟩
      · exact h.hwT
      · show π (Subgroup.inclusion (inf_le_left : C ≤ M) ⟨w, hTC h.hwT⟩) = π ⟨w, hwM⟩
        exact congrArg π (Subtype.ext rfl)
    rw [hUbot, Subgroup.mem_bot] at hwU
    have hwO' : (⟨w, hwM⟩ : ↥M) ∈ O' := (QuotientGroup.eq_one_iff _).mp hwU
    have hwO : w ∈ O'.map M.subtype := Subgroup.mem_map.mpr ⟨⟨w, hwM⟩, hwO', rfl⟩
    have hoddO : Odd (Nat.card (O'.map M.subtype)) := by
      rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := ↥M) (p := 2))
    have hdvd : 2 ∣ Nat.card (O'.map M.subtype) := by
      rw [← h.ow]
      simpa [Subgroup.orderOf_mk] using
        orderOf_dvd_natCard (⟨w, hwO⟩ : ↥(O'.map M.subtype))
    exact (Nat.not_even_iff_odd.mpr hoddO) (even_iff_two_dvd.mpr hdvd)
  have hM2 : ComponentClassification.HarrisLit.IsTwoComponent M :=
    (ComponentClassification.HarrisLit.isTwoComponent_iff_isPComponent M).mpr h.hM
  have hMbar_qs : IsQuasisimple (↥M ⧸ O') := by
    simpa only [O'] using hM2.2.2
  have hcomp_top : IsComponent (⊤ : Subgroup (↥M ⧸ O')) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hMbar_qs,
      Subgroup.IsSubnormal.top⟩
  have hUtm : U = (T.subgroupOf M).map π := by
    ext q
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion (inf_le_left : C ≤ M) c, ?_, rfl⟩
      exact hc
    · rintro ⟨n, hn, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨(n : H), hTC hn⟩, ?_, ?_⟩
      · exact hn
      · show π (Subgroup.inclusion (inf_le_left : C ≤ M) ⟨(n : H), hTC hn⟩) = π n
        exact congrArg π (Subtype.ext rfl)
  have hTmTop : (T.subgroupOf M).map π = ⊤ := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hcomp_top hUsub with hle | hcen
    · have hUtop : U = ⊤ := top_le_iff.mp hle
      rw [hUtop] at hUtm
      exact hUtm.symm
    · exfalso
      have hUZ : U ≤ Subgroup.center (↥M ⧸ O') :=
        Subgroup.commutator_top_left_eq_bot_iff_le_center.mp hcen
      have hUcomm : IsMulCommutative ↥U :=
        IsMulCommutative.of_comm fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.mp (hUZ a.2) (b : ↥M ⧸ O')).symm
      haveI : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUnebot
      haveI : Group.IsPerfect ↥U := hUperf
      exact (Group.IsPerfect.not_isMulCommutative ↥U) hUcomm
  have hcodisj : (T.subgroupOf M) ⊔ O' = ⊤ := by
    have h' := (Subgroup.map_eq_range_iff (f := π) (H := T.subgroupOf M)).mp
      (by rwa [QuotientGroup.range_mk'])
    rwa [QuotientGroup.ker_mk', codisjoint_iff] at h'
  have hmap : ((T.subgroupOf M) ⊔ O').map M.subtype =
      (⊤ : Subgroup ↥M).map M.subtype := congrArg (Subgroup.map M.subtype) hcodisj
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.hTM, Subgroup.map_top,
    Subgroup.range_subtype] at hmap
  simpa only [O'] using hmap

end CFSG.OddStandard.SmallF3.HypA2
