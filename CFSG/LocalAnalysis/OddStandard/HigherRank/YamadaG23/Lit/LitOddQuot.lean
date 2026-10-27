module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]
variable {G : Type*} [Group G] [Finite G] {π : X →* G}

private theorem card_comap_of_surjective {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y]
    (f : Y →* Y') (hf : Function.Surjective f) (H : Subgroup Y') :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let g : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hgk : Nat.card g.ker = Nat.card f.ker := by
    have hle : f.ker ≤ H.comap f := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem H
    have : g.ker = f.ker.subgroupOf (H.comap f) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hrange : g.range = ⊤ := MonoidHom.range_eq_top_of_surjective g hg
  have h := Subgroup.card_ker_mul_card_range g
  rw [hrange, Subgroup.card_top, hgk] at h
  exact h.symm

private theorem conj_mem_map_of_characteristic {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    {K : Subgroup N} [hK : K.Characteristic] (h : H) {c : H} (hc : c ∈ K.map N.subtype) :
    h * c * h⁻¹ ∈ K.map N.subtype := by
  obtain ⟨k, hk, rfl⟩ := hc
  have h1 : (MulAut.conjNormal h k : N) ∈ K := by
    have hfix := hK.fixed (MulAut.conjNormal h).symm
    rw [← hfix]
    change ((MulAut.conjNormal h).symm (MulAut.conjNormal h k)) ∈ K
    rw [MulEquiv.symm_apply_apply]
    exact hk
  refine ⟨_, h1, ?_⟩
  show ((MulAut.conjNormal h k : N) : H) = h * (k : H) * h⁻¹
  exact MulAut.conjNormal_apply h k

private theorem litP_card (h : LitCtx Z A) :
    Nat.card (litP Z) = 4 * Nat.card (CFSG.oddCore X) := by
  have hZO : Z ⊓ CFSG.oddCore X = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hcop : Nat.Coprime 4 (Nat.card (CFSG.oddCore X)) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (lit_odd_card_oddCore X))
    have h1 : Nat.card (Z ⊓ CFSG.oddCore X : Subgroup X) ∣ 4 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ CFSG.oddCore X ≤ Z)
      rwa [h.card_Z] at this
    have h2 : Nat.card (Z ⊓ CFSG.oddCore X : Subgroup X) ∣ Nat.card (CFSG.oddCore X) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hsub : Z.subgroupOf (CFSG.oddCore X) = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    apply Subtype.ext
    have hoZ : (o : X) ∈ Z := ho
    have hmem : (o : X) ∈ Z ⊓ CFSG.oddCore X := ⟨hoZ, o.2⟩
    rw [hZO, Subgroup.mem_bot] at hmem
    exact hmem
  have hsubidx : Z.relIndex (CFSG.oddCore X) = Nat.card (CFSG.oddCore X) := by
    change (Z.subgroupOf (CFSG.oddCore X)).index = Nat.card (CFSG.oddCore X)
    rw [hsub, Subgroup.index_bot]
  have hcard : Nat.card Z * Z.relIndex (Z ⊔ CFSG.oddCore X) =
      Nat.card (Z ⊔ CFSG.oddCore X : Subgroup X) := by
    have hmul := (Z.subgroupOf (Z ⊔ CFSG.oddCore X)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at hmul
    exact hmul
  rw [h.card_Z, Subgroup.relIndex_sup_left (H := CFSG.oddCore X) (K := Z), hsubidx] at hcard
  exact hcard.symm

theorem lit_oddCore_quot (h : LitCtx Z A) (hπ : Function.Surjective π) (hk : π.ker = litP Z) :
    CFSG.oddCore G = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Obar : Subgroup G := CFSG.oddCore G with hObardef
  haveI hObarnormal : Obar.Normal := by rw [hObardef]; infer_instance
  set L : Subgroup X := Obar.comap π with hLdef
  haveI hLnormal : L.Normal := by rw [hLdef]; infer_instance
  have hZL : Z ≤ L := by
    intro z hz
    rw [hLdef, Subgroup.mem_comap]
    have hzker : z ∈ π.ker := by
      rw [hk]
      exact Subgroup.mem_sup_left hz
    rw [MonoidHom.mem_ker] at hzker
    rw [hzker]
    exact Obar.one_mem
  have hZLcard : Nat.card (Z.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, h.card_Z]
  have hLcard : Nat.card L = Nat.card (litP Z) * Nat.card Obar := by
    rw [hLdef, card_comap_of_surjective π hπ Obar, hk]
  have hZidx : ¬ 2 ∣ (Z.subgroupOf L).index := by
    have hcard : Nat.card (Z.subgroupOf L) * (Z.subgroupOf L).index = Nat.card L :=
      Subgroup.card_mul_index (Z.subgroupOf L)
    rw [hZLcard, hLcard, litP_card h, mul_assoc] at hcard
    have hidx : (Z.subgroupOf L).index = Nat.card (CFSG.oddCore X) * Nat.card Obar := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 4 by norm_num)
      exact hcard
    rw [hidx]
    exact ((lit_odd_card_oddCore X).mul (lit_odd_card_oddCore G)).not_two_dvd_nat
  have hZP : IsPGroup 2 (Z.subgroupOf L) :=
    IsPGroup.of_card (n := 2) (by rw [hZLcard]; norm_num)
  have hSnorm : Subgroup.normalizer ((Z.subgroupOf L : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((Z.subgroupOf L : Subgroup L) : Set L) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    change (z : X) * (g : X) = (g : X) * (z : X)
    have hzZ : (z : X) ∈ Z := hz
    exact h.central (z : X) hzZ (g : X)
  set S : Sylow 2 L := hZP.toSylow hZidx with hSdef
  have hScoe : (S : Subgroup L) = Z.subgroupOf L := IsPGroup.toSylow_coe hZP hZidx
  have hSnorm' : Subgroup.normalizer ((S : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((S : Subgroup L) : Set L) := by
    rw [hScoe]; exact hSnorm
  obtain ⟨K, hKn, hKp, hKidx, huniq, hKchar, hKcomp, hKsup, hKinf, hKiso, hKcomm⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S hSnorm'
  have hKidx4 : K.index = 4 := by rw [hKidx, hScoe, hZLcard]
  haveI : K.Characteristic := hKchar
  have hK'normal : (K.map L.subtype).Normal :=
    ⟨fun c hc x => conj_mem_map_of_characteristic x hc⟩
  have hK'card : Nat.card (K.map L.subtype) = Nat.card K :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hK'odd : Odd (Nat.card (K.map L.subtype)) := by
    rw [hK'card]
    exact Nat.not_even_iff_odd.mp fun hEven => hKp (even_iff_two_dvd.mp hEven)
  have hK'le : K.map L.subtype ≤ CFSG.oddCore X := lit_le_oddCore X hK'normal hK'odd
  have hKcard : Nat.card K = Nat.card (CFSG.oddCore X) * Nat.card Obar := by
    have hcardK : Nat.card K * K.index = Nat.card L := Subgroup.card_mul_index K
    rw [hKidx4, hLcard, litP_card h] at hcardK
    rw [mul_assoc] at hcardK
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 4 by norm_num)
      (by rw [hcardK, mul_comm])
  have hKle : Nat.card K ≤ Nat.card (CFSG.oddCore X) := by
    have hdvd : Nat.card K ∣ Nat.card (CFSG.oddCore X) := by
      rw [← hK'card]
      exact Subgroup.card_dvd_of_le hK'le
    haveI : Nonempty (CFSG.oddCore X) := ⟨1⟩
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hObar_le : Nat.card Obar ≤ 1 := by
    have hmul : Nat.card (CFSG.oddCore X) * Nat.card Obar ≤
        Nat.card (CFSG.oddCore X) * 1 := by
      rw [mul_one, ← hKcard]; exact hKle
    haveI : Nonempty (CFSG.oddCore X) := ⟨1⟩
    exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos
  have hObar_one : Nat.card Obar = 1 := by
    have hpos : 0 < Nat.card Obar := by
      haveI : Nonempty Obar := ⟨1⟩
      exact Nat.card_pos
    exact le_antisymm hObar_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))
  exact Subgroup.card_eq_one.mp hObar_one

end CFSG.OddStandard.HigherRank.YamadaG23
