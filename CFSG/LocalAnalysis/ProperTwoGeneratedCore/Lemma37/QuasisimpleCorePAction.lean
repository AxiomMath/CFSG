module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYAltFour
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYSzEight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneInner

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open
open Equiv

noncomputable def autAlternatingFiveEquiv : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))

section Action

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal]

noncomputable def permAction (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    X →* Perm (Fin 5) :=
  autAlternatingFiveEquiv.symm.toMonoidHom.comp
    ((MulAut.congr eA).toMonoidHom.comp (quotientConj L))

theorem permOf_quotientConj (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) (x : X)
    (y : L ⧸ Subgroup.center L) :
    permOf eA (quotientConj L x y) = permAction eA x * permOf eA y * (permAction eA x)⁻¹ := by
  have h : MulAut.conjNormal (permAction eA x) = MulAut.congr eA (quotientConj L x) := by
    have h1 : autAlternatingFiveEquiv (permAction eA x) =
        MulAut.congr eA (quotientConj L x) := by
      simp only [permAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
    rw [← h1]
    rfl
  have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) =>
    ((φ (eA y) : alternatingGroup (Fin 5)) : Perm (Fin 5))) h
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  exact h2.symm

theorem permOf_mk_conj (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) (x : X)
    {l : X} (hl : l ∈ L) :
    permOf eA (((⟨x * l * x⁻¹, (inferInstance : L.Normal).conj_mem l hl x⟩ : L) :
      L ⧸ Subgroup.center L)) =
      permAction eA x * permOf eA ((⟨l, hl⟩ : L) : L ⧸ Subgroup.center L) *
        (permAction eA x)⁻¹ := by
  rw [← permOf_quotientConj, quotientConj_mk]
  rfl

theorem mem_sup_centralizer_of_sign (hperf : commutator L = ⊤)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) {x : X}
    (hx : Perm.sign (permAction eA x) = 1) : x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
  set w := eA.symm ⟨permAction eA x, Perm.mem_alternatingGroup.mpr hx⟩ with hw
  have hpw : permOf eA w = permAction eA x := by simp [hw, permOf]
  have hinner : quotientConj L x = MulAut.conj w := by
    ext y
    apply permOf_injective eA
    rw [permOf_quotientConj, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv, hpw]
  obtain ⟨l, hl⟩ := exists_mul_mem_centralizer_of_quotientConj_eq hperf hinner
  rw [show x = l * ((l : X)⁻¹ * x) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hl)

theorem sign_eq_neg_one_of_not_mem (hperf : commutator L = ⊤)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) {x : X}
    (hx : x ∉ L ⊔ Subgroup.centralizer (L : Set X)) : Perm.sign (permAction eA x) = -1 :=
  (Int.units_eq_one_or _).resolve_left fun h => hx (mem_sup_centralizer_of_sign hperf eA h)

end Action

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {e v : X} {L : Subgroup X}

namespace OneComponent

theorem exists_sylow_map_eq (hL : OneComponent Y e v L) (T : Sylow 2 X) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype = (T : Subgroup X) ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hL.component.2

theorem le_inf_of_isPGroup (hL : OneComponent Y e v L) (T : Sylow 2 X) {R : Subgroup X}
    (hR : IsPGroup 2 R) (hRL : R ≤ L) (hTR : (T : Subgroup X) ⊓ L ≤ R) :
    R ≤ (T : Subgroup X) ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hL.exists_sylow_map_eq T
  have hSR : (S : Subgroup L) ≤ R.subgroupOf L := fun s hs => by
    rw [Subgroup.mem_subgroupOf]
    exact hTR (hS ▸ Subgroup.mem_map_of_mem _ hs)
  have heq := S.is_maximal' (hR.comap_subtype (K := L)) hSR
  intro r hr
  have hmem : (⟨r, hRL hr⟩ : L) ∈ (S : Subgroup L) := by
    rw [← heq]
    exact hr
  rw [← hS]
  exact ⟨_, hmem, rfl⟩

theorem exists_mul_eq_of_mem_sup (hL : OneComponent Y e v L)
    (hZ : Nat.card (Subgroup.center L) = 2) (T : Sylow 2 X) {t : X}
    (htT : t ∈ (T : Subgroup X)) (ht : t ∈ L ⊔ Subgroup.centralizer (L : Set X)) :
    ∃ l ∈ (T : Subgroup X) ⊓ L, ∃ k ∈ (T : Subgroup X) ⊓ Subgroup.centralizer (L : Set X),
      l * k = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := hL.normal
  have := hL.centralizer_normal
  obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
  have hlk : Commute l k := (Subgroup.mem_centralizer_iff.mp hk l hl)
  obtain ⟨n, hn⟩ := T.isPGroup' ⟨l * k, htT⟩
  have hn' : l ^ 2 ^ n * k ^ 2 ^ n = 1 := by
    rw [← hlk.mul_pow]
    simpa using congrArg Subtype.val hn
  have hlnL : l ^ 2 ^ n ∈ L := L.pow_mem hl _
  have hlnK : l ^ 2 ^ n ∈ Subgroup.centralizer (L : Set X) := by
    rw [eq_inv_of_mul_eq_one_left hn']
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk _)
  have hlnZ := mem_center_of_mem_centralizer (l := ⟨l ^ 2 ^ n, hlnL⟩) hlnK
  have hl2 : IsPGroup 2 (Subgroup.zpowers l) := by
    have h1 := CoverExclusion.mul_self_eq_one_of_mem_center hZ hlnZ
    have h2 : l ^ 2 ^ (n + 1) = 1 := by
      rw [pow_succ, pow_mul, pow_two]
      exact congrArg Subtype.val h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hnorm : Subgroup.zpowers l ≤ Subgroup.normalizer
      (((T : Subgroup X) ⊓ L : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem fun q hq => ?_
    have hkq : k * q = q * k := (Subgroup.mem_centralizer_iff.mp hk q hq.2).symm
    have hconj : l * q * l⁻¹ = (l * k) * q * (l * k)⁻¹ := by
      calc l * q * l⁻¹ = l * (q * k) * k⁻¹ * l⁻¹ := by group
        _ = l * (k * q) * k⁻¹ * l⁻¹ := by rw [hkq]
        _ = (l * k) * q * (l * k)⁻¹ := by group
    rw [hconj]
    exact ⟨(T : Subgroup X).mul_mem ((T : Subgroup X).mul_mem htT hq.1)
      ((T : Subgroup X).inv_mem htT), hLn.conj_mem q hq.2 _⟩
  have hR := IsPGroup.to_sup_of_normal_left' (T.isPGroup'.to_le inf_le_left) hl2 hnorm
  have hlT := hL.le_inf_of_isPGroup T hR (_root_.sup_le inf_le_right (Subgroup.zpowers_le.mpr hl))
    le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers l))
  refine ⟨l, hlT, k, ⟨?_, hk⟩, rfl⟩
  rw [show k = l⁻¹ * (l * k) by group]
  exact (T : Subgroup X).mul_mem ((T : Subgroup X).inv_mem hlT.1) htT

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
