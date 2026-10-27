module

public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.RankThree.PartOne.Q1327T.R8Homo
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27)
open CFSG.RankThree.PartOne.Q1327T.R8 (Homo card_torsion_homo nonempty_sigmaModel_mulEquiv_homo)
open CFSG.GroupTheory.WeirSylow (sigmaModel)

namespace Weir

theorem card_le_of_homo {a m : ℕ} (hm : m ≤ 2) {E : Subgroup (Homo 3 a m)}
    (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : Nat.card (Homo 3 0 m) = 1 := by
      rw [Nat.card_pi]
      simp
    have := Subgroup.card_le_card_group E
    omega
  · have hinj : Function.Injective
        (fun x : E => (⟨x, hE x x.2⟩ : {y : Homo 3 a m // y ^ 3 = 1})) := fun x y h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [card_torsion_homo ha m] at h1
    have h2 : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    omega

theorem noE27_of_sigma {G : Type} [Group G] [Finite G] {e a N : ℕ} (hlt : N / e < 3)
    (h : ∀ P : Sylow 3 G, Nonempty (↥P ≃* sigmaModel 3 e a N)) : NoE27 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨E, hE, hc⟩
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card (n := 3) (by rw [hc]; norm_num) :
    IsPGroup 3 E).exists_le_sylow
  obtain ⟨φ⟩ := h P
  obtain ⟨ψ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := 3) (e := e) (a := a) hlt
  let χ : ↥(P : Subgroup G) ≃* Homo 3 a (N / e) := φ.trans ψ
  have hE' : ∀ x ∈ (E.subgroupOf (P : Subgroup G)).map χ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have : y ^ 3 = 1 := Subtype.ext (hE.2 _ hy)
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, this, map_one]
  have hc' : Nat.card ((E.subgroupOf (P : Subgroup G)).map χ.toMonoidHom) = 27 := by
    rw [card_map_of_injective χ.injective, Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv, hc]
  have := card_le_of_homo (by omega) hE'
  omega

end Weir

theorem NoE27.of_injective {G H : Type} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) (h : NoE27 H) : NoE27 G := by
  rintro ⟨E, hE, hc⟩
  exact h ⟨E.map φ, hE.map φ, by rw [card_map_of_injective hφ, hc]⟩

theorem NoE27.of_surjective {G H : Type} [Group G] [Group H] [Finite G] {π : G →* H}
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) (h : NoE27 G) : NoE27 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite H := Finite.of_surjective π hπ
  rintro ⟨E, hE, hc⟩
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card (n := 3) (by rw [hc]; norm_num) :
    IsPGroup 3 E).exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hπ 3 Q
  rw [Sylow.coe_mapSurjective] at hEQ
  have hinjS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), π a = π b → a = b := by
    intro a ha b hb hab
    have hm : a * b⁻¹ ∈ (S : Subgroup G) ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem hb), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have hp : IsPGroup 3 ↥((S : Subgroup G) ⊓ π.ker) := S.isPGroup'.to_le inf_le_left
    have hbot : (S : Subgroup G) ⊓ π.ker = ⊥ := by
      by_contra hne
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne ((Subgroup.card_eq_one).1 (by simpa using hk))
      exact hker ((hk ▸ dvd_pow_self 3 hk0 : 3 ∣ Nat.card ↥((S : Subgroup G) ⊓ π.ker)).trans
        (Subgroup.card_dvd_of_le inf_le_right))
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  set F : Subgroup G := E.comap π ⊓ (S : Subgroup G)
  refine h ⟨F, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · show (a : G) * b = (b : G) * a
    refine hinjS _ (mul_mem a.2.2 b.2.2) _ (mul_mem b.2.2 a.2.2) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2.1⟩ ⟨_, b.2.1⟩)
  · refine hinjS _ (pow_mem ha.2 3) _ (one_mem _) ?_
    rw [map_pow, map_one]
    exact hE.2 _ ha.1
  ·
    have hbij : Function.Bijective (fun x : F => (⟨π x, x.2.1⟩ : E)) := by
      refine ⟨fun x y hxy => Subtype.ext (hinjS _ x.2.2 _ y.2.2
        (congrArg Subtype.val hxy)), ?_⟩
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := hEQ hy
      exact ⟨⟨x, hy, hx⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), hc]

section Linear

variable {F : Type} [Field F] [Finite F]

theorem orderOf_card_zmod_three {q : ℕ} (hq : q % 3 = 2) : orderOf (q : ZMod 3) = 2 := by
  have h2 : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, hq]
    rfl
  rw [h2]
  exact orderOf_eq_prime (by decide) (by decide)

theorem noE27_projSL (hF : ¬ 3 ∣ Nat.card F) {n : ℕ} (hn3 : ¬ 3 ∣ n)
    (hlt : n / orderOf (Nat.card F : ZMod 3) < 3) : NoE27 (StatedProj (StatedSL n F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL : NoE27 (GL (Fin n) F) := by
    refine Weir.noE27_of_sigma (by rwa [← Nat.card_eq_fintype_card]) fun P =>
      CFSG.GroupTheory.WeirSylow.sylow_GL (by decide) F hF' n P
  have hSL : NoE27 (StatedSL n F) := NoE27.of_injective (StatedSL n F).subtype_injective hGL
  exact NoE27.of_surjective (QuotientGroup.mk'_surjective _)
    (CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.ProjLin.not_three_dvd_card_ker hn3
      (StatedSL n F) fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSL hg) hSL

end Linear

section Unitary

variable {L : Type} [Field L] [Finite L]

theorem noE27_projSU {ℓ f n : ℕ} (hL : Nat.card L = (ℓ ^ f) ^ 2) (hq3 : ¬ 3 ∣ ℓ ^ f)
    (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n) (hlt : n / orderOf (-((ℓ ^ f : ℕ) : ZMod 3)) < 3) :
    NoE27 (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype L := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  have hGU : NoE27 ↥(CFSG.Quasithin.StatedGU n (ℓ ^ f) L) :=
    Weir.noE27_of_sigma hlt fun P =>
      CFSG.GroupTheory.WeirSylow.sylow_GU (by decide) L hLc hq3 hn P
  have hle : StatedSU n (ℓ ^ f) L ≤ CFSG.Quasithin.StatedGU n (ℓ ^ f) L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
  have hSU : NoE27 ↥(StatedSU n (ℓ ^ f) L) :=
    NoE27.of_injective (Subgroup.inclusion_injective hle) hGU
  exact NoE27.of_surjective (QuotientGroup.mk'_surjective _)
    (CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.ProjLin.not_three_dvd_card_ker hn3
      (StatedSU n (ℓ ^ f) L) fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSU hg) hSU

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
