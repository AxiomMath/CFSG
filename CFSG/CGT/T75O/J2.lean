module

public import CFSG.CGT.T75E.J2
public import CFSG.CGT.T75O.Class
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Facts

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75E CFSG.ComponentClassification.J2Cover CFSG.Blueprint
  CFSG.Timmesfeld CFSG.GH74.GLS.C3.Layer1.Bk.J2C CFSG.Sporadic.Schreier

theorem false_of_sq_conj_permA
    {y z u : ↥P} (hy4 : orderOf y = 4) (hyz : y ^ 2 = z)
    (hu : z = u * (⟨permA, permA_mem⟩ : ↥P) * u⁻¹) : False := by
  set y' : ↥P := u⁻¹ * y * u with hy'
  have hy'4 : orderOf y' = 4 := by
    have := CorB.orderOf_conj u⁻¹ y
    rw [inv_inv] at this
    rw [hy', this]
    exact hy4
  have hy'2 : y' ^ 2 = ⟨permA, permA_mem⟩ := by
    have h1 : y' ^ 2 = u⁻¹ * y ^ 2 * u := by
      rw [hy', pow_two, pow_two]
      group
    rw [h1, hyz, hu]
    group
  have hmem : (y' : Equiv.Perm (Fin 315)) ∈ centralizerIn P permA := by
    refine mem_centralizerIn.2 ⟨y'.2, ?_⟩
    have h2 : (y' : Equiv.Perm (Fin 315)) ^ 2 = permA := by
      rw [← Subgroup.coe_pow, hy'2]
    rw [← h2]
    group
  exact orderOf_ne_four_of_mem_centralizerIn_permA hmem
    (by rw [Subgroup.orderOf_coe]; exact hy'4)

theorem centralizer_conj_tP
    (c : ↥P) :
    Subgroup.centralizer ({c * tP * c⁻¹} : Set ↥P) =
      MulAction.stabilizer ↥P (c • (314 : Fin 315)) := by
  ext g
  have hg : g ∈ Subgroup.centralizer ({c * tP * c⁻¹} : Set ↥P) ↔
      c⁻¹ * g * c ∈ Subgroup.centralizer ({tP} : Set ↥P) := by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc c⁻¹ * g * c * tP = c⁻¹ * (g * (c * tP * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * tP * c⁻¹ * g) * c := by rw [h]
        _ = tP * (c⁻¹ * g * c) := by group
    · intro h
      calc g * (c * tP * c⁻¹) = c * (c⁻¹ * g * c * tP) * c⁻¹ := by group
        _ = c * (tP * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
        _ = c * tP * c⁻¹ * g := by group
  rw [hg, centralizer_tP, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [mul_smul, mul_smul] at h
    exact inv_smul_eq_iff.1 h
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]


theorem sec56_j2_excl : Sec56ExclAt fun Y _ => NativeSporadic.IsSporadic Y .J2 := by
  intro G _ T T₁ c Y _ ⟨e⟩ hJ
  have hJG : NativeSporadic.IsSporadic G .J2 := isSporadic_of_mulEquiv e.symm hJ
  have := c.hy.finite
  obtain ⟨a, ha, ha1⟩ := c.exists_mem_secA_ne_one
  have hs := c.setup ha ha1
  obtain ⟨φ⟩ := id hJG
  let ψ : G ≃* ↥P := φ.trans nativeEquivP
  have ha2' : orderOf (ψ a : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hs.orderOf_eq
  obtain ⟨r, hr, w, hw, hψa⟩ := inner_classes.1 (ψ a : Equiv.Perm (Fin 315)) (ψ a).2 ha2'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    have hψa' : ψ a = (⟨w, hw⟩ : ↥P) * ⟨permA, permA_mem⟩ * (⟨w, hw⟩ : ↥P)⁻¹ :=
      Subtype.ext hψa
    obtain ⟨d, e', hd, he', h4⟩ := c.exists_orderOf_eq_four ha ha1
    obtain ⟨hz, -, -⟩ := hs.pow_mem_of_orderOf_eq (d := d) (e := e') hd he' (m := 2)
      (by rw [h4]) (by norm_num)
    have hconj : IsConj (ψ a) (ψ ((d * e') ^ 2)) := MonoidHom.map_isConj ψ.toMonoidHom hz
    obtain ⟨v, hv⟩ := isConj_iff.1 hconj
    refine false_of_sq_conj_permA (y := ψ (d * e')) (z := ψ ((d * e') ^ 2))
      (u := v * ⟨w, hw⟩) ?_ (by rw [map_pow]) ?_
    · rw [MulEquiv.orderOf_eq]
      exact h4
    · rw [← hv, hψa']
      group
  ·
    have hψa' : ψ a = (⟨w, hw⟩ : ↥P) * tP * (⟨w, hw⟩ : ↥P)⁻¹ := Subtype.ext hψa
    have hcard : Nat.card (Subgroup.centralizer ({a} : Set G)) = 1920 := by
      have h1 := card_cent_symm ψ (ψ a)
      rw [MulEquiv.symm_apply_apply] at h1
      rw [h1, hψa', centralizer_conj_tP, card_stabilizer_P]
    have h128 : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({a} : Set G)) := by
      rw [hcard]
      norm_num
    obtain ⟨E, hE⟩ := j2_cent_facts hJG hs.orderOf_eq h128
    have haT : a ∈ T := secA_le_left ha
    have hnorm : ∀ y ∈ Subgroup.centralizer ({a} : Set G), ∀ n ∈ T, y * n * y⁻¹ ∈ T :=
      fun y hy n hn => (Subgroup.mem_normalizer_iff.1
        (c.hy.pair.wc.centralizer_le_normalizer haT ha1 hy) n).1 hn
    have hTC : T ≤ Subgroup.centralizer ({a} : Set G) := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.mul_comm_T hx haT
    have hTE : T ≤ E :=
      hE.two_core T hTC hnorm (isPGroup_two_of_isElemAbelian c.hy.pair.wc.1)
    have hx : ∃ x ∈ T, x ≠ 1 ∧ x ≠ a := by
      by_contra hcon
      push Not at hcon
      have hle : T ≤ Subgroup.zpowers a := by
        intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]
          exact one_mem _
        · rw [hcon x hx hx1]
          exact Subgroup.mem_zpowers a
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hs.orderOf_eq] at h1
      have h2 := c.hy.card
      omega
    have hET : E ≤ T := hE.irred T hTE haT hnorm hx
    have hEz : E ≤ Subgroup.zpowers a := by
      intro x hx
      have hx12 := hE.center x hx (fun y hy => c.mul_comm_T (hET hx) (hET hy))
      rcases hx12 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers a
    have h1 := Subgroup.card_le_of_le hEz
    rw [Nat.card_zpowers, hs.orderOf_eq, hE.card_E] at h1
    omega

end CFSG.CGT.T75O
