module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem centerIn_commute {G : Type} [Group G] {H : Subgroup G} {a x : G}
    (ha : a ∈ centerIn H) (hx : x ∈ H) : a * x = x * a := by
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' ⟨x, hx⟩)).symm

private theorem mem_oddCoreIn_map {G : Type} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ oddCoreIn H) : x ∈ (CFSG.oddCore ↥H).map H.subtype := by
  simpa only [oddCoreIn, CFSG.inSubgroup] using hx

private theorem oddCoreIn_le' {G : Type} [Group G] (H : Subgroup G) : oddCoreIn H ≤ H := by
  rw [oddCoreIn, CFSG.inSubgroup]
  exact Subgroup.map_subtype_le _

private def conjHom {G : Type} [Group G] (H : Subgroup G) (n : G)
    (hn : n ∈ Subgroup.normalizer (H : Set G)) : H →* H where
  toFun x := ⟨n * (x : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn (x : G)).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change n * ((a : G) * (b : G)) * n⁻¹ =
      (n * (a : G) * n⁻¹) * (n * (b : G) * n⁻¹)
    group)

private theorem exists_sqrt_of_odd_inv {A : Type*} [Group A] {o x : A} (ho : Odd (orderOf o))
    (hx : x * o * x⁻¹ = o⁻¹) :
    ∃ o' ∈ Subgroup.zpowers o, o' * o' = o ∧ x * o' * x⁻¹ = o'⁻¹ := by
  refine ⟨o ^ ((orderOf o + 1) / 2), Subgroup.pow_mem _ (Subgroup.mem_zpowers o) _, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := ho
    have h2 : (orderOf o + 1) / 2 + (orderOf o + 1) / 2 = orderOf o + 1 := by omega
    rw [← pow_add, h2, pow_succ, pow_orderOf_eq_one, one_mul]
  · rw [← conj_pow, hx, inv_pow]

private theorem inv_conj_of_oddCore_aux {A : Type*} [Group A] {a o m e : A}
    (ha2 : a * a = 1) (hea : e * a = a * e) (hao : a * o = o * a)
    (hm : m = a * o) (he : m * (e * m * e⁻¹) = 1) :
    e * o * e⁻¹ = o⁻¹ := by
  have hee : e * m * e⁻¹ = m⁻¹ := eq_inv_of_mul_eq_one_right he
  rw [hm] at hee
  have h1 : e * (a * o) * e⁻¹ = (e * a * e⁻¹) * (e * o * e⁻¹) := by group
  rw [h1] at hee
  have hea' : e * a * e⁻¹ = a := by rw [hea]; group
  rw [hea'] at hee
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hm_inv : (a * o)⁻¹ = o⁻¹ * a := by rw [mul_inv_rev, ha_inv]
  rw [hm_inv] at hee
  have hao_inv : a * o⁻¹ = o⁻¹ * a := by
    have h := congrArg Inv.inv hao
    rw [mul_inv_rev, mul_inv_rev, ha_inv] at h
    exact h.symm
  have hR : a * (o⁻¹ * a) = o⁻¹ := by
    rw [← mul_assoc, hao_inv, mul_assoc, ha2, mul_one]
  have hL : a * (a * (e * o * e⁻¹)) = e * o * e⁻¹ := by
    rw [← mul_assoc, ha2, one_mul]
  have hfin := congrArg (fun x => a * x) hee
  rw [hL, hR] at hfin
  exact hfin

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_conj_of_coverAct (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) {b e : G} (hb2 : b * b = 1)
    (he2 : e * e = 1) (hbe : ∃ u ∈ L, e = u * b) {s g : OGroup Q}
    (hb : CoverAct L φ b (orthToSim Q s)) (he : CoverAct L φ e (orthToSim Q g))
    {c : omegaGroup hQ} (hc : (c : OGroup Q) * s * (c : OGroup Q)⁻¹ = g) :
    e ∈ conjClassIn L b ∨ e ∈ conjClassIn L (t * b) := by
  obtain ⟨l, hl⟩ := h.surjective c
  let e' : G := (l : G) * b * (l : G)⁻¹
  have he'2 : e' * e' = 1 := by
    dsimp only [e']
    calc ((l : G) * b * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹)
        = (l : G) * (b * b) * (l : G)⁻¹ := by group
      _ = 1 := by rw [hb2, mul_one, mul_inv_cancel]
  have hlg_norm : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have he'norm : e' ∈ normalizer (L : Set G) := by
    dsimp only [e']
    exact mul_mem (mul_mem hlg_norm hb.1) (inv_mem hlg_norm)
  have hb_lg : b * (l : G)⁻¹ * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hb.1 ((l : G)⁻¹)).mp (inv_mem l.2)
  have he'Lb : ∃ u' ∈ L, e' = u' * b := by
    refine ⟨(l : G) * (b * (l : G)⁻¹ * b⁻¹), mul_mem l.2 hb_lg, ?_⟩
    dsimp only [e']
    group
  obtain ⟨u, hu, he_eq⟩ := hbe
  obtain ⟨u', hu', he'_eq⟩ := he'Lb
  let m : G := e' * e⁻¹
  have he'_me : e' = m * e := by dsimp only [m]; group
  have hm_eq : m = u' * u⁻¹ := by
    dsimp only [m]
    rw [he'_eq, he_eq]
    group
  have hmL : m ∈ L := by
    rw [hm_eq]
    exact mul_mem hu' (inv_mem hu)
  let σe : ↥L →* ↥L := conjHom L e he.1
  let σe' : ↥L →* ↥L := conjHom L e' he'norm
  let σb : ↥L →* ↥L := conjHom L b hb.1
  have hσe_coe : ∀ x : ↥L, (σe x : G) = e * (x : G) * e⁻¹ := fun _ => rfl
  have hσe'_coe : ∀ x : ↥L, (σe' x : G) = e' * (x : G) * e'⁻¹ := fun _ => rfl
  have hσb_coe : ∀ x : ↥L, (σb x : G) = b * (x : G) * b⁻¹ := fun _ => rfl
  let Φ : ↥L →* OGroup Q := (Subgroup.subtype (omegaGroup hQ)).comp φ
  have hΦσe : ∀ x : ↥L, Φ (σe x) = g * Φ x * g⁻¹ := by
    intro x
    have h1 := he.2 x (σe x) (hσe_coe x)
    rw [simAct_orthToSim] at h1
    exact h1
  have hΦl : Φ l = (c : OGroup Q) := by
    change ((φ l : omegaGroup hQ) : OGroup Q) = (c : OGroup Q)
    rw [hl]
  have hΦσe' : ∀ x : ↥L, Φ (σe' x) = g * Φ x * g⁻¹ := by
    intro x
    let y : ↥L := ⟨(l : G)⁻¹ * (x : G) * (l : G),
      mul_mem (mul_mem (inv_mem l.2) x.2) l.2⟩
    have hy_val : (y : G) = (l : G)⁻¹ * (x : G) * (l : G) := rfl
    have hσb : Φ (σb y) = s * Φ y * s⁻¹ := by
      have h1 := hb.2 y (σb y) (hσb_coe y)
      rw [simAct_orthToSim] at h1
      exact h1
    have hσe'_factor : σe' x = l * σb y * l⁻¹ := by
      apply Subtype.ext
      show (σe' x : G) = ((l * σb y * l⁻¹ : ↥L) : G)
      rw [hσe'_coe x]
      change e' * (x : G) * e'⁻¹ = (l : G) * (σb y : G) * (l : G)⁻¹
      rw [hσb_coe, hy_val]
      dsimp only [e']
      group
    have hΦy : Φ y = (c : OGroup Q)⁻¹ * Φ x * (c : OGroup Q) := by
      have hy_eq : y = l⁻¹ * x * l := by apply Subtype.ext; rfl
      rw [hy_eq, map_mul, map_mul, map_inv, hΦl]
    rw [hσe'_factor, map_mul, map_mul, map_inv, hσb, hΦy, hΦl, ← hc]
    group
  have hφeq : ∀ x : ↥L, φ (σe x) = φ (σe' x) := by
    intro x
    apply Subtype.ext
    change Φ (σe x) = Φ (σe' x)
    exact (hΦσe x).trans (hΦσe' x).symm
  have hker : ∀ x : ↥L, (σe x)⁻¹ * σe' x ∈ Subgroup.center ↥L := by
    intro x
    apply (h.oddCentralCover hL).ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφeq x]
    exact inv_mul_cancel _
  have hσ_eq : σe = σe' := t5_eq_of_inv_mul_mem_center hL.1.1 σe σe' hker
  have hm_centerL : (⟨m, hmL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * m = m * (y : G)
    have hx_mem : (e : G)⁻¹ * (y : G) * e ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp (inv_mem he.1) (y : G)).mp y.2
      simpa using h
    let x : ↥L := ⟨(e : G)⁻¹ * (y : G) * e, hx_mem⟩
    have hσx : σe x = σe' x := DFunLike.congr_fun hσ_eq x
    have hval : (σe x : G) = (σe' x : G) := congrArg Subtype.val hσx
    have h1 : (σe x : G) = (y : G) := by
      rw [hσe_coe x]
      change e * ((e : G)⁻¹ * (y : G) * e) * e⁻¹ = (y : G)
      group
    have h2 : (σe' x : G) = m * (y : G) * m⁻¹ := by
      rw [hσe'_coe x]
      change e' * ((e : G)⁻¹ * (y : G) * e) * e'⁻¹ = m * (y : G) * m⁻¹
      rw [he'_me]
      group
    have hconj : m * (y : G) * m⁻¹ = (y : G) := by rw [← h2, ← hval, h1]
    have hcomm : m * (y : G) = (y : G) * m := by
      calc m * (y : G) = m * (y : G) * m⁻¹ * m := by group
        _ = (y : G) * m := by rw [hconj]
    exact hcomm.symm
  have hm_cent_omega : φ ⟨m, hmL⟩ ∈ Subgroup.center (omegaGroup hQ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := h.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subgroup.mem_center_iff.mp hm_centerL z)
  have hπ_mem : piOrth Q ∈ omegaGroup hQ :=
    (piOrth_mem_omegaGroup_iff hQ).mpr
      ⟨by rw [h.finrank_eq]; decide, by rw [h.quadSign_eq, h.finrank_eq]; decide⟩
  have hπ_ne : piOrth Q ≠ 1 := piOrth_ne_one (by rw [h.finrank_eq]; norm_num)
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) = 2 :=
    natCard_center_omegaGroup_six_minus hQ h.finrank_eq h.quadSign_eq
  have htL : t ∈ L := by
    have h : t ∈ (Subgroup.center ↥L).map L.subtype := ht
    exact Subgroup.map_subtype_le _ h
  have ht_sq : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hφt : ((φ ⟨t, htL⟩ : omegaGroup hQ) : OGroup Q) = piOrth Q :=
    h.map_central hL ht ht2 htL
  have hdecomp : ∃ a o : G, a ∈ centerIn L ∧ (a = 1 ∨ a = t) ∧ o ∈ oddCoreIn L ∧
      m = a * o ∧ a * a = 1 ∧ e * a = a * e ∧ a * o = o * a := by
    rcases t5_center_omegaGroup_eq_one_or_pi hQ hZ hπ_mem hπ_ne hm_cent_omega with hφm | hφm
    · have ho_mem : m ∈ oddCoreIn L := by
        have hker : (⟨m, hmL⟩ : ↥L) ∈ φ.ker := by
          rw [MonoidHom.mem_ker]; exact hφm
        rw [h.ker_eq] at hker
        exact Subgroup.mem_map_of_mem L.subtype hker
      exact ⟨1, m, Subgroup.one_mem _, Or.inl rfl, ho_mem, (one_mul m).symm,
        by simp, by simp, by simp⟩
    · have ho_mem : t * m ∈ oddCoreIn L := by
        have htmL : t * m ∈ L := mul_mem htL hmL
        have hker : (⟨t * m, htmL⟩ : ↥L) ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          apply Subtype.ext
          change ((φ (⟨t, htL⟩ * ⟨m, hmL⟩) : omegaGroup hQ) : OGroup Q) = 1
          rw [map_mul]
          change ((φ ⟨t, htL⟩ : omegaGroup hQ) : OGroup Q) *
            ((φ ⟨m, hmL⟩ : omegaGroup hQ) : OGroup Q) = 1
          rw [hφt, hφm, piOrth_mul_self]
        rw [h.ker_eq] at hker
        exact Subgroup.mem_map_of_mem L.subtype hker
      have hm_to : m = t * (t * m) := by
        rw [← mul_assoc, ht_sq, one_mul]
      have hoL : t * m ∈ L := oddCoreIn_le' L ho_mem
      refine ⟨t, t * m, ht, Or.inr rfl, ho_mem, hm_to, ht_sq,
        t5_normalizer_commute hL ht ht2 he.1, ?_⟩
      exact centerIn_commute ht hoL
  obtain ⟨a, o, ha_center, hac, ho, hm_ao, ha2, he_a, ha_o⟩ := hdecomp
  have hoL : o ∈ L := oddCoreIn_le' L ho
  have hker_odd : Odd (Nat.card (CFSG.oddCore ↥L)) :=
    h.ker_eq ▸ (h.oddCentralCover hL).odd_card_ker
  have ho_odd : Odd (orderOf o) := by
    obtain ⟨o0, ho0, ho0eq⟩ := Subgroup.mem_map.mp (mem_oddCoreIn_map ho)
    have hodd0 : Odd (orderOf o0) :=
      hker_odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (CFSG.oddCore ↥L) ho0)
    have hord : orderOf o = orderOf o0 := by
      rw [← ho0eq]
      exact orderOf_injective L.subtype L.subtype_injective o0
    rwa [hord]
  have hm_inv : m * (e * m * e⁻¹) = 1 := by
    have h := he'2
    rw [he'_me] at h
    have hcalc : (m * e) * (m * e) = m * (e * m * e⁻¹) := by
      calc (m * e) * (m * e) = m * (e * m * e⁻¹) * (e * e) := by group
        _ = m * (e * m * e⁻¹) := by rw [he2, mul_one]
    rwa [hcalc] at h
  have hoe : e * o * e⁻¹ = o⁻¹ :=
    inv_conj_of_oddCore_aux ha2 he_a ha_o hm_ao hm_inv
  obtain ⟨o', ho'zp, ho'sq, ho'inv⟩ := exists_sqrt_of_odd_inv ho_odd hoe
  have ho'L : o' ∈ L := Subgroup.zpowers_le.mpr hoL ho'zp
  have hooe : o' * e * o'⁻¹ = o * e := by
    have h1 : o' * e * o'⁻¹ = o' * (e * o'⁻¹ * e⁻¹) * e := by group
    have h2 : e * o'⁻¹ * e⁻¹ = o' := by
      rw [show e * o'⁻¹ * e⁻¹ = (e * o' * e⁻¹)⁻¹ by group, ho'inv, inv_inv]
    rw [h1, h2, ho'sq]
  have hconj_eq : (o'⁻¹ * (l : G)) * (a * b) * (o'⁻¹ * (l : G))⁻¹ = e := by
    have hla : a * (l : G) = (l : G) * a := centerIn_commute ha_center l.2
    have h_lb : (l : G) * b * (l : G)⁻¹ = e' := rfl
    calc
      (o'⁻¹ * (l : G)) * (a * b) * (o'⁻¹ * (l : G))⁻¹
          = o'⁻¹ * ((l : G) * (a * b) * (l : G)⁻¹) * o' := by group
      _ = o'⁻¹ * (a * ((l : G) * b * (l : G)⁻¹)) * o' := by
            rw [show (l : G) * (a * b) * (l : G)⁻¹ = a * ((l : G) * b * (l : G)⁻¹) by
              calc (l : G) * (a * b) * (l : G)⁻¹
                  = ((l : G) * a) * b * (l : G)⁻¹ := by group
                _ = (a * (l : G)) * b * (l : G)⁻¹ := by rw [← hla]
                _ = a * ((l : G) * b * (l : G)⁻¹) := by group]
      _ = o'⁻¹ * (a * e') * o' := by rw [h_lb]
      _ = o'⁻¹ * (a * (a * o * e)) * o' := by rw [he'_me, hm_ao]
      _ = o'⁻¹ * (o * e) * o' := by
            rw [show a * (a * o * e) = o * e by
              rw [← mul_assoc, ← mul_assoc, ha2, one_mul]]
      _ = o'⁻¹ * (o' * e * o'⁻¹) * o' := by rw [← hooe]
      _ = e := by group
  have hmem_conj : e ∈ conjClassIn L (a * b) :=
    ⟨o'⁻¹ * (l : G), mul_mem (inv_mem ho'L) l.2, hconj_eq.symm⟩
  rcases hac with rfl | rfl
  · left
    rwa [one_mul] at hmem_conj
  · right
    exact hmem_conj

end CFSG.OddStandard.SmallF3.Omega
