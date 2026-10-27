module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7E
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

@[expose] def c4 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem c4_vec : pact (ptab c4).2 g23 + g23 = pact (ptab c4).2 (pact (ptab c4).2 g23) ∧
    pact (ptab c4).2 g23 ≠ g23 := by decide +kernel

theorem z_facts_of_card_two {G : Type*} [Group G] {z : G} (h : Nat.card (Subgroup.zpowers z) = 2) :
    z ≠ 1 ∧ z ^ 2 = 1 := by
  have h2 : orderOf z = 2 := by rw [← Nat.card_zpowers]; exact h
  exact ⟨fun h1 => by rw [h1, orderOf_one] at h2; omega, by rw [← h2]; exact pow_orderOf_eq_one z⟩

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem u0_mul_zU' (C : StdCfg T M H S L) : C.u0 * C.zU = ((C.iV g23w : ↥H) : G) := by
  have h := C.iV_add g1w StdCfg.z0V
  have e : g1w + StdCfg.z0V = g23w := Subtype.ext g1_add_z0
  rw [e] at h
  rw [C.zU_eq_iV]
  exact (congrArg (fun y : ↥H => (y : G)) h).symm

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem pi_huHom_one
    (s : Equiv.Perm (Fin 4)) : C.D.π (X.huHom (1, s)) = (ptab s).2 := by
  rw [X.pi_huHom]
  show (dtab 1).2 * (ptab s).2 = _
  rw [dtab_one]
  exact one_mul _

theorem conj_c_iV (w : evenWeight 5) :
    ((X.huHom (1, c4) : ↥H) : G) * ((C.iV w : ↥H) : G) * ((X.huHom (1, c4) : ↥H) : G)⁻¹ =
      ((C.iV (vact (ptab c4).2 w) : ↥H) : G) := by
  have h := C.conj_iV X.hTC (X.huHom (1, c4)) w
  rw [X.pi_huHom_one] at h
  exact congrArg (fun y : ↥H => (y : G)) h

theorem oddCoreIn_Gu_eq_bot
    (hinv : ∀ y ∈ oddCoreIn (centralizerElem C.u0), C.zU⁻¹ * y * C.zU = y⁻¹) :
    oddCoreIn (centralizerElem C.u0) = ⊥ := by
  set u : G := C.u0 with hu
  set z : G := C.zU with hz
  set O : Subgroup G := oddCoreIn (centralizerElem u) with hO
  have hzz : z * z = 1 := C.zU_mul_self
  have huu : u * u = 1 := C.u0_mul_self
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hOGu : O ≤ centralizerElem u := oddCoreIn_le _
  have hcentu : ∀ g ∈ centralizerElem u, g * u = u * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hzu : z * u = u * z := (C.U_comm C.u0_mem_U C.zU_mem).symm
  set w1 : G := u * z with hw1
  have hw1inv : w1⁻¹ = u * z := by rw [hw1, mul_inv_rev, hzi, hui, hzu]
  have hinv1 : ∀ y ∈ O, w1 * y * w1⁻¹ = y⁻¹ := by
    intro y hy
    have h1 : z * y * z = y⁻¹ := by
      have := hinv y hy
      rwa [hzi] at this
    calc w1 * y * w1⁻¹ = u * z * y * (u * z) := by rw [hw1inv]
      _ = u * z * (y * u) * z := by group
      _ = u * z * (u * y) * z := by rw [hcentu y (hOGu hy)]
      _ = u * (z * u) * y * z := by group
      _ = u * (u * z) * y * z := by rw [hzu]
      _ = (u * u) * (z * y * z) := by group
      _ = y⁻¹ := by rw [huu, one_mul, h1]
  set c : G := ((X.huHom (1, c4) : ↥H) : G) with hc
  have hcGu : c ∈ centralizerElem u := X.huHom_mem_cent (1, c4)
  have hnormO : centralizerElem u ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_oddCoreIn (centralizerElem u)
  have hcO' : ∀ y ∈ O, c⁻¹ * y * c ∈ O := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp (hnormO ((centralizerElem u).inv_mem hcGu)) y).mp hy
    simpa using this
  set w2 : G := c * w1 * c⁻¹ with hw2
  set w3 : G := c * w2 * c⁻¹ with hw3
  have hinv2 : ∀ y ∈ O, w2 * y * w2⁻¹ = y⁻¹ := by
    intro y hy
    have h := hinv1 (c⁻¹ * y * c) (hcO' y hy)
    calc w2 * y * w2⁻¹ = c * (w1 * (c⁻¹ * y * c) * w1⁻¹) * c⁻¹ := by rw [hw2]; group
      _ = c * (c⁻¹ * y * c)⁻¹ * c⁻¹ := by rw [h]
      _ = y⁻¹ := by group
  have hinv3 : ∀ y ∈ O, w3 * y * w3⁻¹ = y⁻¹ := by
    intro y hy
    have h := hinv2 (c⁻¹ * y * c) (hcO' y hy)
    calc w3 * y * w3⁻¹ = c * (w2 * (c⁻¹ * y * c) * w2⁻¹) * c⁻¹ := by rw [hw3]; group
      _ = c * (c⁻¹ * y * c)⁻¹ * c⁻¹ := by rw [h]
      _ = y⁻¹ := by group
  have hw1' : w1 = ((C.iV g23w : ↥H) : G) := C.u0_mul_zU'
  have hw2' : w2 = ((C.iV (vact (ptab c4).2 g23w) : ↥H) : G) := by
    rw [hw2, hw1']
    exact X.conj_c_iV g23w
  have hw3' : w3 = ((C.iV (vact (ptab c4).2 (vact (ptab c4).2 g23w)) : ↥H) : G) := by
    rw [hw3, hw2']
    exact X.conj_c_iV _
  have hw12 : w1 * w2 = w3 := by
    have hm : ((C.iV g23w : ↥H) : G) * ((C.iV (vact (ptab c4).2 g23w) : ↥H) : G) =
        ((C.iV (g23w + vact (ptab c4).2 g23w) : ↥H) : G) := by
      rw [C.iV_add]
      rfl
    have e : g23w + vact (ptab c4).2 g23w = vact (ptab c4).2 (vact (ptab c4).2 g23w) :=
      Subtype.ext (by rw [add_comm]; exact c4_vec.1)
    rw [hw1', hw2', hw3', hm, e]
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hcent : (w1 * w2) * y * (w1 * w2)⁻¹ = y := by
    calc (w1 * w2) * y * (w1 * w2)⁻¹ = w1 * (w2 * y * w2⁻¹) * w1⁻¹ := by group
      _ = w1 * y⁻¹ * w1⁻¹ := by rw [hinv2 y hy]
      _ = (w1 * y * w1⁻¹)⁻¹ := by group
      _ = y := by rw [hinv1 y hy]; group
  have hyy : y = y⁻¹ := by
    calc y = (w1 * w2) * y * (w1 * w2)⁻¹ := hcent.symm
      _ = w3 * y * w3⁻¹ := by rw [hw12]
      _ = y⁻¹ := hinv3 y hy
  have h3 : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← hyy]
      _ = 1 := by group
  have hyO : y ∈ O := hy
  have hord : orderOf (⟨y, hyO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have hord2 : orderOf (⟨y, hyO⟩ : O) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h3))
  have hcop : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr (odd_card_oddCoreIn _)
  have hone : orderOf (⟨y, hyO⟩ : O) = 1 := by
    have := Nat.dvd_gcd hord2 hord
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have : (⟨y, hyO⟩ : O) = 1 := orderOf_eq_one_iff.mp hone
  exact congrArg Subtype.val this

end Sec

end CFSG.QuasithinUnique.A5
