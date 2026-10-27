module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.FixedPointQuotientCard
import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

private theorem map_mem_normalizer_of_map_eq {L : Type} [Group L] {U : Subgroup L}
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) {x : L}
    (hx : x ∈ Subgroup.normalizer (U : Set L)) :
    α x ∈ Subgroup.normalizer (U : Set L) := by
  have hαN : (Subgroup.normalizer (U : Set L)).map α.toMonoidHom =
      Subgroup.normalizer (U : Set L) := by
    rw [Subgroup.map_equiv_normalizer_eq, hα]
  have hαE : (Subgroup.normalizer (U : Set L)).map α.toMonoidHom ≤
      Subgroup.normalizer (U : Set L) := le_of_eq hαN
  exact hαE (Subgroup.mem_map_of_mem α.toMonoidHom hx)

private theorem characteristic_subgroupOf_sup_center {L : Type} [Group L] [Finite L]
    {U Z : Subgroup L} (hZ : Z ≤ Subgroup.center L)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    (U.subgroupOf (U ⊔ Z)).Characteristic := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUidx : ¬ 2 ∣ U.index := by
    simpa only [show (U.subgroupOf ⊤).index = U.index from
      Subgroup.relIndex_top_right U] using hU.2.2
  have hUZnorm : U ⊔ Z ≤ Subgroup.normalizer (U : Set L) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact hZ.trans (Subgroup.center_le_normalizer (U : Set L))
  have hUnorm : (U.subgroupOf (U ⊔ Z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hUZnorm
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf U (U ⊔ Z) := by
    refine ⟨le_sup_left, hU.2.1, ?_⟩
    intro h2
    have hmul : U.relIndex (U ⊔ Z) * (U ⊔ Z).index = U.index :=
      Subgroup.relIndex_mul_index le_sup_left
    exact hUidx (by rw [← hmul]; exact dvd_mul_of_dvd_left h2 _)
  let C : Subgroup ↥(U ⊔ Z) := U.subgroupOf (U ⊔ Z)
  have hCsyl : IsPGroup 2 C := by
    change IsPGroup 2 (U.subgroupOf (U ⊔ Z))
    exact hU.2.1.comap_subtype
  have hCidx : ¬ 2 ∣ C.index := by
    change ¬ 2 ∣ (U.subgroupOf (U ⊔ Z)).index
    exact hUsyl.2.2
  let S : Sylow 2 ↥(U ⊔ Z) := hCsyl.toSylow hCidx
  have hScoe : (S : Subgroup ↥(U ⊔ Z)) = C := IsPGroup.toSylow_coe hCsyl hCidx
  have hSnorm : S.Normal := by simpa [C, hScoe] using hUnorm
  have h := Sylow.characteristic_of_normal S hSnorm
  simpa [C, hScoe] using h

private theorem normalizer_sup_center_le_normalizer {L : Type} [Group L] [Finite L]
    {U Z : Subgroup L} (hZ : Z ≤ Subgroup.center L)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Subgroup.normalizer ((U ⊔ Z : Subgroup L) : Set L) ≤
      Subgroup.normalizer (U : Set L) := by
  have hCchar : (U.subgroupOf (U ⊔ Z)).Characteristic :=
    characteristic_subgroupOf_sup_center hZ hU
  have hCmap : (U.subgroupOf (U ⊔ Z)).map (U ⊔ Z).subtype = U :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  intro x hx
  let α : MulAut ↥(U ⊔ Z) := (U ⊔ Z).normalizerMonoidHom ⟨x, hx⟩
  have hhom : (MulAut.conj x).toMonoidHom.comp (U ⊔ Z).subtype =
      (U ⊔ Z).subtype.comp α.toMonoidHom := by
    ext m
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe (U ⊔ Z) ⟨x, hx⟩ m).symm
  have hmap : U.map (MulAut.conj x).toMonoidHom = U := by
    calc U.map (MulAut.conj x).toMonoidHom
        = ((U.subgroupOf (U ⊔ Z)).map (U ⊔ Z).subtype).map
            (MulAut.conj x).toMonoidHom := by rw [hCmap]
      _ = (U.subgroupOf (U ⊔ Z)).map
            ((MulAut.conj x).toMonoidHom.comp (U ⊔ Z).subtype) := by
            rw [Subgroup.map_map]
      _ = (U.subgroupOf (U ⊔ Z)).map
            ((U ⊔ Z).subtype.comp α.toMonoidHom) := by rw [hhom]
      _ = ((U.subgroupOf (U ⊔ Z)).map α.toMonoidHom).map (U ⊔ Z).subtype := by
            rw [Subgroup.map_map]
      _ = (U.subgroupOf (U ⊔ Z)).map (U ⊔ Z).subtype := by
            rw [Subgroup.characteristic_iff_map_eq.mp hCchar α]
      _ = U := hCmap
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

private theorem exists_sylow_preimage_map {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    {Ebar : Subgroup (L ⧸ Subgroup.center L)} (hEbarCard : Nat.card Ebar = q ^ 2) :
    ∃ E : Subgroup L, IsPGroup q E ∧
      E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let P : Subgroup L := Ebar.comap π
  let E : Sylow q ↥P := Sylow.nonempty.some
  let E₀ : Subgroup L := (E : Subgroup ↥P).map P.subtype
  have hE₀q : IsPGroup q E₀ := E.isPGroup'.map P.subtype
  have hE₀syl : CFSG.ABGLocalTools.IsSylowOf q E₀ P := ⟨E, rfl⟩
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ q ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [QuotientGroup.ker_mk' (Subgroup.center L)]
    exact hqZ
  have hmapSyl : CFSG.ABGLocalTools.IsSylowOf q (E₀.map π) (P.map π) :=
    CFSG.isSylowOf_map_of_not_dvd_card_ker π hπsurj hq hker hE₀syl
  have hPmap : P.map π = Ebar := Subgroup.map_comap_eq_self_of_surjective hπsurj Ebar
  have hmapSyl' : CFSG.ABGLocalTools.IsSylowOf q (E₀.map π) Ebar := by
    rwa [hPmap] at hmapSyl
  have hcard : Nat.card (E₀.map π) = q ^ 2 := by
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hmapSyl', hEbarCard,
      Nat.factorization_pow_self hq]
  have hmap : E₀.map π = Ebar :=
    Subgroup.eq_of_le_of_card_ge hmapSyl'.le (by rw [hcard, hEbarCard])
  exact ⟨E₀, hE₀q, hmap⟩

private theorem inf_center_eq_bot_of_isPGroup {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {E : Subgroup L}
    (hEq : IsPGroup q E) :
    E ⊓ Subgroup.center L = ⊥ := by
  have hcop : Nat.Coprime q (Nat.card (Subgroup.center L)) := hq.coprime_iff_not_dvd.mpr hqZ
  have hdisj : Disjoint E (Subgroup.center L) :=
    IsPGroup.disjoint_of_coprime hEq IsPGroup.card hcop
  exact disjoint_iff.mp hdisj

private theorem card_of_sylow_preimage {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {E : Subgroup L}
    {Ebar : Subgroup (L ⧸ Subgroup.center L)} (hEq : IsPGroup q E)
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEbarCard : Nat.card Ebar = q ^ 2) : Nat.card E = q ^ 2 := by
  have hinfCenter := inf_center_eq_bot_of_isPGroup hq hqZ hEq
  have hinfKer : E ⊓ (QuotientGroup.mk' (Subgroup.center L)).ker = ⊥ := by
    rw [show (QuotientGroup.mk' (Subgroup.center L)).ker = Subgroup.center L from
      QuotientGroup.ker_mk' _]
    exact hinfCenter
  rw [← CFSG.card_map_eq_card_of_inf_ker_eq_bot
    (QuotientGroup.mk' (Subgroup.center L)) hinfKer, hEmap, hEbarCard]

private theorem isMulCommutative_of_map_eq {L : Type} [Group L] {q : ℕ}
    {E : Subgroup L} {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEbarElem : IsElemAbelian q Ebar)
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEinf : E ⊓ Subgroup.center L = ⊥) :
    IsMulCommutative E := by
  rw [isMulCommutative_iff]
  intro x y
  apply Subtype.ext
  have hxbar : (QuotientGroup.mk' (Subgroup.center L)) (x : L) ∈ Ebar := by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ x.2
  have hybar : (QuotientGroup.mk' (Subgroup.center L)) (y : L) ∈ Ebar := by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ y.2
  have hcomm : (⟨(QuotientGroup.mk' (Subgroup.center L)) (x : L), hxbar⟩ : Ebar) *
      ⟨(QuotientGroup.mk' (Subgroup.center L)) (y : L), hybar⟩ =
      ⟨(QuotientGroup.mk' (Subgroup.center L)) (y : L), hybar⟩ *
        ⟨(QuotientGroup.mk' (Subgroup.center L)) (x : L), hxbar⟩ :=
    hEbarElem.1.is_comm.comm _ _
  have hq : (QuotientGroup.mk' (Subgroup.center L)) ((x : L) * y) =
      (QuotientGroup.mk' (Subgroup.center L)) ((y : L) * x) := by
    simpa [map_mul] using congrArg Subtype.val hcomm
  have hzZ : ((x : L) * y) * ((y : L) * x)⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center L), MonoidHom.mem_ker]
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  have hzE : ((x : L) * y) * ((y : L) * x)⁻¹ ∈ E :=
    E.mul_mem (E.mul_mem x.2 y.2) (E.inv_mem (E.mul_mem y.2 x.2))
  have hbot : ((x : L) * y) * ((y : L) * x)⁻¹ ∈ (⊥ : Subgroup L) := by
    rw [← hEinf]
    exact ⟨hzE, hzZ⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)

private theorem pow_eq_one_of_map_eq {L : Type} [Group L] {q : ℕ}
    {E : Subgroup L} {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEbarElem : IsElemAbelian q Ebar)
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEinf : E ⊓ Subgroup.center L = ⊥) :
    ∀ x ∈ E, x ^ q = 1 := by
  intro x hx
  have hxbar : (QuotientGroup.mk' (Subgroup.center L)) (x : L) ∈ Ebar := by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hxq : ((QuotientGroup.mk' (Subgroup.center L)) (x : L)) ^ q = 1 :=
    hEbarElem.2 _ hxbar
  have hq : (QuotientGroup.mk' (Subgroup.center L)) ((x : L) ^ q) = 1 := by
    rw [map_pow]
    exact hxq
  have hzZ : (x : L) ^ q ∈ Subgroup.center L := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center L), MonoidHom.mem_ker]
    exact hq
  have hzE : (x : L) ^ q ∈ E := E.pow_mem hx q
  have hbot : (x : L) ^ q ∈ (⊥ : Subgroup L) := by
    rw [← hEinf]
    exact ⟨hzE, hzZ⟩
  simpa using Subgroup.mem_bot.mp hbot

private theorem isElemAbelian_of_map_eq {L : Type} [Group L] {q : ℕ}
    {E : Subgroup L} {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEbarElem : IsElemAbelian q Ebar)
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEinf : E ⊓ Subgroup.center L = ⊥) :
    IsElemAbelian q E :=
  ⟨isMulCommutative_of_map_eq hEbarElem hEmap hEinf,
    pow_eq_one_of_map_eq hEbarElem hEmap hEinf⟩

private theorem exists_center_factor {L : Type} [Group L] {U : Subgroup L}
    {α : MulAut L} {x y : L} (hxy : α x * y⁻¹ ∈ U ⊔ Subgroup.center L) :
    ∃ u ∈ U, ∃ z ∈ Subgroup.center L, u * z = α x * y⁻¹ := by
  haveI : (Subgroup.center L).Normal := inferInstance
  exact (Subgroup.mem_sup_of_normal_right (s := U) (t := Subgroup.center L)).mp hxy

private theorem center_factor_pow_mem {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) {U E : Subgroup L} (hE : IsElemAbelian q E)
    (hEN : E ≤ Subgroup.normalizer (U : Set L))
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) {x y u z : L}
    (hxE : x ∈ E) (hyE : y ∈ E) (huU : u ∈ U)
    (hzZ : z ∈ Subgroup.center L) (huz : u * z = α x * y⁻¹) :
    z ^ q ∈ U := by
  classical
  have haN : α x ∈ Subgroup.normalizer (U : Set L) :=
    map_mem_normalizer_of_map_eq hα (hEN hxE)
  have hbN : z * y ∈ Subgroup.normalizer (U : Set L) :=
    (Subgroup.normalizer (U : Set L)).mul_mem
      ((Subgroup.center_le_normalizer (U : Set L)) hzZ) (hEN hyE)
  have ha_eq : α x = u * (z * y) := by
    calc α x = (α x * y⁻¹) * y := by group
      _ = (u * z) * y := by rw [huz]
      _ = u * (z * y) := by group
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  let πN : N →* N ⧸ U.subgroupOf N := QuotientGroup.mk' (U.subgroupOf N)
  have hdiv : (⟨α x, haN⟩ : N) / ⟨z * y, hbN⟩ ∈ U.subgroupOf N := by
    rw [Subgroup.mem_subgroupOf]
    change α x / (z * y) ∈ U
    rw [div_eq_mul_inv, ha_eq]
    have h : (u * (z * y)) * (z * y)⁻¹ = u := by group
    rw [h]
    exact huU
  have hquot : πN ⟨α x, haN⟩ = πN ⟨z * y, hbN⟩ :=
    (QuotientGroup.eq_iff_div_mem (N := U.subgroupOf N) (x := ⟨α x, haN⟩)
      (y := ⟨z * y, hbN⟩)).mpr hdiv
  have ha_pow : (α x) ^ q = 1 := by rw [← map_pow, hE.2 x hxE, map_one]
  have hb_pow : (z * y) ^ q = z ^ q := by
    have hcomm : Commute z y := (Subgroup.mem_center_iff.mp hzZ y).symm
    rw [hcomm.mul_pow, hE.2 y hyE, mul_one]
  have hpow : πN (⟨α x, haN⟩ ^ q) = πN (⟨z * y, hbN⟩ ^ q) := by
    rw [map_pow, map_pow]
    exact congrArg (fun t => t ^ q) hquot
  have hmem : (⟨α x, haN⟩ : N) ^ q / (⟨z * y, hbN⟩ : N) ^ q ∈ U.subgroupOf N :=
    (QuotientGroup.eq_iff_div_mem (N := U.subgroupOf N) (x := (⟨α x, haN⟩ : N) ^ q)
      (y := (⟨z * y, hbN⟩ : N) ^ q)).mp hpow
  rw [Subgroup.mem_subgroupOf] at hmem
  change (α x) ^ q / (z * y) ^ q ∈ U at hmem
  rw [ha_pow, hb_pow] at hmem
  simpa using U.inv_mem hmem

private theorem mem_of_mul_inv_mem_sup_center {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U E : Subgroup L}
    (hE : IsElemAbelian q E) (hEN : E ≤ Subgroup.normalizer (U : Set L))
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) {x y : L}
    (hxE : x ∈ E) (hyE : y ∈ E) (hxy : α x * y⁻¹ ∈ U ⊔ Subgroup.center L) :
    α x * y⁻¹ ∈ U := by
  obtain ⟨u, huU, z, hzZ, huz⟩ := exists_center_factor hxy
  have hzqU := center_factor_pow_mem hq hE hEN hα hxE hyE huU hzZ huz
  have hcop : Nat.Coprime q (orderOf z) := by
    have hzo : orderOf z ∣ Nat.card (Subgroup.center L) :=
      Subgroup.orderOf_dvd_natCard _ hzZ
    exact (hq.coprime_iff_not_dvd.mpr hqZ).coprime_dvd_right hzo
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := z) hcop
  have hzU : z ∈ U := by
    rw [← hm]
    exact U.pow_mem hzqU m
  rw [← huz]
  exact U.mul_mem huU hzU

private theorem exists_lift_subgroup {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEbar : IsScalarTorus q (U.map (QuotientGroup.mk' (Subgroup.center L))) Ebar) :
    ∃ E : Subgroup L, E ≤ Subgroup.normalizer (U : Set L) ∧ IsElemAbelian q E ∧
      Nat.card E = q ^ 2 ∧ E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar := by
  obtain ⟨E, hEq, hEmap⟩ :=
    exists_sylow_preimage_map hq hqZ hU hEbar.2.2.1
  have hEinf := inf_center_eq_bot_of_isPGroup hq hqZ hEq
  have hEcard := card_of_sylow_preimage hq hqZ hEq hEmap hEbar.2.2.1
  have hEelem := isElemAbelian_of_map_eq hEbar.2.1 hEmap hEinf
  have hEN : E ≤ Subgroup.normalizer (U : Set L) := by
    have hE_Nbar : E ≤ (Subgroup.normalizer
        ((U.map (QuotientGroup.mk' (Subgroup.center L))) :
          Set (L ⧸ Subgroup.center L))).comap
          (QuotientGroup.mk' (Subgroup.center L)) := by
      intro x hx
      rw [Subgroup.mem_comap]
      exact hEbar.1 (by rw [← hEmap]; exact Subgroup.mem_map_of_mem _ hx)
    have hcomapN : (Subgroup.normalizer
        ((U.map (QuotientGroup.mk' (Subgroup.center L))) :
          Set (L ⧸ Subgroup.center L))).comap
          (QuotientGroup.mk' (Subgroup.center L)) =
        Subgroup.normalizer ((U ⊔ Subgroup.center L : Subgroup L) : Set L) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective
        (H := (U.map (QuotientGroup.mk' (Subgroup.center L)) :
          Subgroup (L ⧸ Subgroup.center L))) (QuotientGroup.mk'_surjective _),
        QuotientGroup.comap_map_mk', sup_comm]
    exact (hcomapN ▸ hE_Nbar).trans
      (normalizer_sup_center_le_normalizer (le_rfl : Subgroup.center L ≤
        Subgroup.center L) hU)
  exact ⟨E, hEN, hEelem, hEcard, hEmap⟩

private theorem quotientAut_map_eq {L : Type} [Group L] {U : Subgroup L}
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) :
    (U.map (QuotientGroup.mk' (Subgroup.center L))).map
        (CFSG.quotientAut α).toMonoidHom =
      U.map (QuotientGroup.mk' (Subgroup.center L)) := by
  rw [Subgroup.map_map]
  have hcomp : (CFSG.quotientAut α).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center L)) =
      (QuotientGroup.mk' (Subgroup.center L)).comp α.toMonoidHom := by
    ext x
    exact CFSG.quotientAut_mk α x
  rw [hcomp, ← Subgroup.map_map, hα]

private theorem quotientAut_involutive {L : Type} [Group L] {α : MulAut L}
    (hα2 : α * α = 1) : CFSG.quotientAut α * CFSG.quotientAut α = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    change CFSG.quotientAut α (CFSG.quotientAut α
      (QuotientGroup.mk' (Subgroup.center L) x)) =
      QuotientGroup.mk' (Subgroup.center L) x
    rw [show CFSG.quotientAut α (QuotientGroup.mk' (Subgroup.center L) x) =
      QuotientGroup.mk' (Subgroup.center L) (α x) from CFSG.quotientAut_mk α x]
    rw [show CFSG.quotientAut α (QuotientGroup.mk' (Subgroup.center L) (α x)) =
      QuotientGroup.mk' (Subgroup.center L) (α (α x)) from
      CFSG.quotientAut_mk α (α x)]
    rw [show α (α x) = (α * α) x from rfl, hα2]
    rfl

private theorem power_clause {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U E : Subgroup L}
    (hE : IsElemAbelian q E) (hEN : E ≤ Subgroup.normalizer (U : Set L))
    {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEbar : IsScalarTorus q (U.map (QuotientGroup.mk' (Subgroup.center L))) Ebar)
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) :
    ∃ j : ℕ, ∀ x ∈ E, α x * (x ^ j)⁻¹ ∈ U := by
  let αbar : MulAut (L ⧸ Subgroup.center L) := CFSG.quotientAut α
  have hαbarU := quotientAut_map_eq hα
  obtain ⟨j, hj⟩ := (hEbar.2.2.2 αbar hαbarU).1
  refine ⟨j, ?_⟩
  intro x hx
  have hxbar : (QuotientGroup.mk' (Subgroup.center L)) x ∈ Ebar := by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hmemUZ : α x * (x ^ j)⁻¹ ∈ U ⊔ Subgroup.center L := by
    have h1 : (QuotientGroup.mk' (Subgroup.center L)) (α x * (x ^ j)⁻¹) ∈
        U.map (QuotientGroup.mk' (Subgroup.center L)) := by
      have h2 := hj ((QuotientGroup.mk' (Subgroup.center L)) x) hxbar
      rw [show αbar ((QuotientGroup.mk' (Subgroup.center L)) x) =
        (QuotientGroup.mk' (Subgroup.center L)) (α x) from CFSG.quotientAut_mk α x] at h2
      rwa [show (QuotientGroup.mk' (Subgroup.center L)) (α x * (x ^ j)⁻¹) =
        (QuotientGroup.mk' (Subgroup.center L)) (α x) *
          ((QuotientGroup.mk' (Subgroup.center L)) x ^ j)⁻¹ by
          simp [map_mul, map_pow]]
    have h2 : α x * (x ^ j)⁻¹ ∈
        (U.map (QuotientGroup.mk' (Subgroup.center L))).comap
          (QuotientGroup.mk' (Subgroup.center L)) := h1
    rwa [QuotientGroup.comap_map_mk', sup_comm] at h2
  exact mem_of_mul_inv_mem_sup_center hq hqZ hE hEN hα hx (E.pow_mem hx j) hmemUZ

private theorem involution_clause {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U E : Subgroup L}
    (hE : IsElemAbelian q E) (hEN : E ≤ Subgroup.normalizer (U : Set L))
    {Ebar : Subgroup (L ⧸ Subgroup.center L)}
    (hEmap : E.map (QuotientGroup.mk' (Subgroup.center L)) = Ebar)
    (hEbar : IsScalarTorus q (U.map (QuotientGroup.mk' (Subgroup.center L))) Ebar)
    {α : MulAut L} (hα : U.map α.toMonoidHom = U) (hα2 : α * α = 1) :
    ∀ x ∈ E, α x * x⁻¹ ∈ U := by
  let αbar : MulAut (L ⧸ Subgroup.center L) := CFSG.quotientAut α
  have hαbarU := quotientAut_map_eq hα
  have hαbar2 := quotientAut_involutive hα2
  intro x hx
  have hxbar : (QuotientGroup.mk' (Subgroup.center L)) x ∈ Ebar := by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hmemUZ : α x * x⁻¹ ∈ U ⊔ Subgroup.center L := by
    have h1 : (QuotientGroup.mk' (Subgroup.center L)) (α x * x⁻¹) ∈
        U.map (QuotientGroup.mk' (Subgroup.center L)) := by
      have h2 := (hEbar.2.2.2 αbar hαbarU).2 hαbar2
        ((QuotientGroup.mk' (Subgroup.center L)) x) hxbar
      rw [show αbar ((QuotientGroup.mk' (Subgroup.center L)) x) =
        (QuotientGroup.mk' (Subgroup.center L)) (α x) from CFSG.quotientAut_mk α x] at h2
      rwa [show (QuotientGroup.mk' (Subgroup.center L)) (α x * x⁻¹) =
        (QuotientGroup.mk' (Subgroup.center L)) (α x) *
          ((QuotientGroup.mk' (Subgroup.center L)) x)⁻¹ by simp [map_mul]]
    have h2 : α x * x⁻¹ ∈
        (U.map (QuotientGroup.mk' (Subgroup.center L))).comap
          (QuotientGroup.mk' (Subgroup.center L)) := h1
    rwa [QuotientGroup.comap_map_mk', sup_comm] at h2
  exact mem_of_mul_inv_mem_sup_center hq hqZ hE hEN hα hx hx hmemUZ

theorem HasScalarTorus.of_quotient_center {L : Type} [Group L] [Finite L] {q : ℕ}
    (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (h : HasScalarTorus (L ⧸ Subgroup.center L) q
      (U.map (QuotientGroup.mk' (Subgroup.center L)))) :
    HasScalarTorus L q U := by
  obtain ⟨Ebar, hEbar⟩ := h
  obtain ⟨E, hEN, hEelem, hEcard, hEmap⟩ := exists_lift_subgroup hq hqZ hU hEbar
  refine ⟨E, hEN, hEelem, hEcard, ?_⟩
  intro α hα
  exact ⟨power_clause hq hqZ hEelem hEN hEmap hEbar hα,
    fun hα2 => involution_clause hq hqZ hEelem hEN hEmap hEbar hα hα2⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
