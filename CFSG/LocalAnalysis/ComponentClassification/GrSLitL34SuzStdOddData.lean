module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzFourGroup
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.SuzukiTwoGroupsCoprime
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.EvenSporadicStandard.Induction.Cover
open scoped commutatorElement

private theorem isMulCommutative_comap_center_of_forall_sq_one {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X)))
    {E : Subgroup (X ⧸ Subgroup.center X)} (hE : ∀ e ∈ E, e ^ 2 = 1) :
    IsMulCommutative (E.comap (QuotientGroup.mk' (Subgroup.center X))) := by
  have hEcomm : IsMulCommutative E :=
    CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one fun e =>
      Subtype.ext (by
        have := hE (e : X ⧸ Subgroup.center X) e.2
        simpa [pow_two] using this)
  let q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hqab : q ((a : X) * (b : X)) = q ((b : X) * (a : X)) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hEcomm.is_comm.comm ⟨q (a : X), a.2⟩ ⟨q (b : X), b.2⟩)
  have hcommZ : ⁅(a : X), (b : X)⁆ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    change q ⁅(a : X), (b : X)⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hqab
  have ha2Z : (a : X) * (a : X) ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    change q ((a : X) * (a : X)) = 1
    rw [map_mul]
    simpa [pow_two] using hE (q (a : X)) a.2
  have hpow : ⁅(a : X), (b : X)⁆ ^ 2 = 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.commutatorElement_pow_left_of_mem_center hcommZ 2]
    rw [commutatorElement_eq_one_iff_mul_comm]
    show (a : X) ^ 2 * (b : X) = (b : X) * (a : X) ^ 2
    simpa [pow_two] using (Subgroup.mem_center_iff.mp ha2Z (b : X)).symm
  have h1 : ⁅(a : X), (b : X)⁆ = 1 :=
    CFSG.EvenSporadicStandard.Induction.Closing.eq_one_of_sq_eq_one_of_odd_center hodd hcommZ
      (by simpa [pow_two] using hpow)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private structure SuzFourSetup {G : Type} [Group G] [Finite G] (A : Subgroup G) where
  E : Subgroup (↥A ⧸ center ↥A)
  H : Subgroup (↥A ⧸ center ↥A)
  n : ↥A ⧸ center ↥A
  card_E : Nat.card E = 4
  sq_E : ∀ e ∈ E, e ^ 2 = 1
  centralizer_card : ∀ e ∈ E, e ≠ 1 →
    Nat.card (Subgroup.centralizer ({e} : Set (↥A ⧸ center ↥A))) = 161280
  centralizer_eq : Subgroup.centralizer (E : Set (↥A ⧸ center ↥A)) = H ⊔ E
  inf_E : H ⊓ E = ⊥
  H_le : H ≤ Subgroup.centralizer (E : Set (↥A ⧸ center ↥A))
  der_H : ⁅H, H⁆ = H
  card_H : Nat.card H = 20160
  orderOf_n : orderOf n = 3
  n_centralizes_H : n ∈ Subgroup.centralizer (H : Set (↥A ⧸ center ↥A))
  n_normalizes_E : n ∈ Subgroup.normalizer (E : Set (↥A ⧸ center ↥A))
  n_moves_E : ∀ e ∈ E, e ≠ 1 → n * e * n⁻¹ ≠ e
  lie : CFSG.Blueprint.LieModel ↥H .PSL 3 2 2

private theorem exists_suzFourSetup
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz) :
    Nonempty (SuzFourSetup A) := by
  obtain ⟨E, H, n, hdata, hlie⟩ :=
    CFSG.EvenSporadicStandard.Solomon78.sol78Lemma44SuzFourGroup_l34_holds
      (↥A ⧸ center ↥A) hsuz
  obtain ⟨hcardE, hsqE, hcentE, hcentEq, hinf, hle, _, hderH, hcardH, hordn, hnCH, hnNE,
    hfix⟩ := hdata
  exact ⟨
    { E := E, H := H, n := n, card_E := hcardE, sq_E := hsqE,
      centralizer_card := hcentE, centralizer_eq := hcentEq, inf_E := hinf, H_le := hle,
      der_H := hderH, card_H := hcardH, orderOf_n := hordn, n_centralizes_H := hnCH,
      n_normalizes_E := hnNE, n_moves_E := hfix, lie := hlie }⟩

private theorem exists_sylow_four_comap {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hodd : Odd (Nat.card (center ↥A))) (S : SuzFourSetup A) :
    ∃ V₀ : Sylow 2 (S.E.comap (q ↥A)),
      Nat.card (V₀ : Subgroup (S.E.comap (q ↥A))) = 4 ∧
        (V₀ : Subgroup (S.E.comap (q ↥A))).Characteristic := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Subgroup ↥A := S.E.comap (q ↥A)
  have hWcard : Nat.card W = 4 * Nat.card (center ↥A) := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (q ↥A)
      QuotientGroup.mk_surjective S.E
    rw [QuotientGroup.ker_mk'] at h
    rw [h, S.card_E]
    ring
  have hWcomm : IsMulCommutative W :=
    isMulCommutative_comap_center_of_forall_sq_one hodd S.sq_E
  let V₀ : Sylow 2 W := Sylow.nonempty.some
  have hV₀card : Nat.card (V₀ : Subgroup W) = 4 := by
    rw [Sylow.card_eq_multiplicity, hWcard]
    have hZodd : Odd (Nat.card (center ↥A)) := hodd
    have hZne : Nat.card (center ↥A) ≠ 0 := Nat.card_pos.ne'
    have h4ne : (4 : ℕ) ≠ 0 := by norm_num
    have h4fac : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow_self Nat.prime_two]
    have hZfac : (Nat.card (center ↥A)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h2 =>
        (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2)
    rw [Nat.factorization_mul h4ne hZne, Finsupp.add_apply, h4fac, hZfac, add_zero]
    norm_num
  have hV₀normal : (V₀ : Subgroup W).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (congrArg Subtype.val (hWcomm.is_comm.comm v w).symm)
  have huniq : Unique (Sylow 2 W) := Sylow.unique_of_normal V₀ hV₀normal
  have hV₀char : (V₀ : Subgroup W).Characteristic :=
    Sylow.characteristic_of_subsingleton V₀
  exact ⟨V₀, hV₀card, hV₀char⟩

private theorem sylow_comap_inf_sq {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hodd : Odd (Nat.card (center ↥A))) (S : SuzFourSetup A)
    {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A)) {V₀ : Sylow 2 W} :
    (V₀ : Subgroup W) ⊓ (center ↥A).subgroupOf W = ⊥ ∧
      (∀ v : W, v ∈ (V₀ : Subgroup W) → v * v = 1) := by
  subst W
  have hinf : (V₀ : Subgroup (S.E.comap (q ↥A))) ⊓
      (center ↥A).subgroupOf (S.E.comap (q ↥A)) = ⊥ := by
    have hZW : center ↥A ≤ S.E.comap (q ↥A) := by
      intro z hz
      rw [Subgroup.mem_comap]
      have hqz : q ↥A z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      simp [hqz]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxV : x ∈ (V₀ : Subgroup (S.E.comap (q ↥A))) := hx.1
    have hxZ : x ∈ (center ↥A).subgroupOf (S.E.comap (q ↥A)) := hx.2
    have hoddZsub : Odd (Nat.card ((center ↥A).subgroupOf (S.E.comap (q ↥A)))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv]
      exact hodd
    have hxpow : (⟨x, hxV⟩ : ↥(V₀ : Subgroup (S.E.comap (q ↥A)))) ^
        Nat.card ((center ↥A).subgroupOf (S.E.comap (q ↥A))) = 1 := by
      apply Subtype.ext
      have h1 := pow_card_eq_one'
        (G := ↥((center ↥A).subgroupOf (S.E.comap (q ↥A)))) (x := ⟨x, hxZ⟩)
      have h1' : (x : S.E.comap (q ↥A)) ^
          Nat.card ((center ↥A).subgroupOf (S.E.comap (q ↥A))) = 1 := congrArg Subtype.val h1
      exact h1'
    have hone : (⟨x, hxV⟩ : ↥(V₀ : Subgroup (S.E.comap (q ↥A)))) = 1 :=
      CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd V₀.isPGroup' hoddZsub hxpow
    exact Subtype.ext_iff.mp hone
  refine ⟨hinf, ?_⟩
  intro v hv
  have hqvv : q ↥A ((v : ↥A) * (v : ↥A)) = 1 := by
    rw [map_mul]
    simpa [pow_two] using S.sq_E (q ↥A (v : ↥A)) v.2
  have hmemZ : v * v ∈ (center ↥A).subgroupOf (S.E.comap (q ↥A)) := by
    rw [Subgroup.mem_subgroupOf]
    simpa using (QuotientGroup.eq_one_iff ((v : ↥A) * (v : ↥A))).mp hqvv
  have hmemV : v * v ∈ (V₀ : Subgroup (S.E.comap (q ↥A))) := V₀.1.mul_mem hv hv
  have hbot : v * v ∈ (V₀ : Subgroup (S.E.comap (q ↥A))) ⊓
      (center ↥A).subgroupOf (S.E.comap (q ↥A)) := ⟨hmemV, hmemZ⟩
  rw [hinf] at hbot
  exact Subgroup.mem_bot.mp hbot

private theorem four_lift_facts {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A))
    {V₀ : Sylow 2 W} (hV₀card : Nat.card (V₀ : Subgroup W) = 4)
    (hV₀sq : ∀ v : W, v ∈ (V₀ : Subgroup W) → v * v = 1)
    (hV₀inf : (V₀ : Subgroup W) ⊓ (center ↥A).subgroupOf W = ⊥) :
    Nat.card ((V₀ : Subgroup W).map W.subtype) = 4 ∧
      (∀ v ∈ (V₀ : Subgroup W).map W.subtype, v * v = 1) ∧
      IsMulCommutative ((V₀ : Subgroup W).map W.subtype) ∧
      ((V₀ : Subgroup W).map W.subtype) ⊓ center ↥A = ⊥ ∧
      ((V₀ : Subgroup W).map W.subtype).map (q ↥A) = S.E := by
  subst W
  let V_A : Subgroup ↥A := (V₀ : Subgroup (S.E.comap (q ↥A))).map
    (S.E.comap (q ↥A)).subtype
  have hVAsq : ∀ v ∈ V_A, v * v = 1 := by
    rintro v ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hV₀sq w hw)
  have hVAcomm : IsMulCommutative V_A :=
    CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one fun v =>
      Subtype.ext (by
        have := hVAsq v.val v.2
        simpa [pow_two] using this)
  have hVAcard : Nat.card V_A = 4 := by
    rw [show V_A = (V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype from rfl,
      Subgroup.card_map_of_injective (S.E.comap (q ↥A)).subtype_injective, hV₀card]
  have hVAinfZ : V_A ⊓ center ↥A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxV, hxZ⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hxV
    have hwZ : w ∈ (center ↥A).subgroupOf (S.E.comap (q ↥A)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hxZ
    have hbot : w ∈ (V₀ : Subgroup (S.E.comap (q ↥A))) ⊓
        (center ↥A).subgroupOf (S.E.comap (q ↥A)) := ⟨hw, hwZ⟩
    rw [hV₀inf] at hbot
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hbot)
  have hqVA : V_A.map (q ↥A) = S.E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_comap.mp (Subgroup.map_subtype_le _ hv)
    · have hinj : Function.Injective ((q ↥A).comp V_A.subtype) := by
        intro a b hab
        have hmemZ : ((a : ↥A))⁻¹ * b ∈ center ↥A := (QuotientGroup.eq).mp hab
        have hmemVA : (a : ↥A)⁻¹ * b ∈ V_A := V_A.mul_mem (V_A.inv_mem a.2) b.2
        have hbot : (a : ↥A)⁻¹ * b ∈ V_A ⊓ center ↥A := ⟨hmemVA, hmemZ⟩
        rw [hVAinfZ] at hbot
        have hone : (a : ↥A)⁻¹ * b = 1 := Subgroup.mem_bot.mp hbot
        exact Subtype.ext (inv_mul_eq_one.mp hone)
      have hcard : Nat.card (V_A.map (q ↥A)) = Nat.card V_A := by
        have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
        rw [MonoidHom.range_comp, Subgroup.range_subtype] at h1
        exact h1.symm
      rw [hcard, hVAcard, S.card_E]
  exact ⟨hVAcard, hVAsq, hVAcomm, hVAinfZ, hqVA⟩

private theorem centralizer_lift {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hodd : Odd (Nat.card (center ↥A))) (S : SuzFourSetup A)
    {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A)) {V₀ : Sylow 2 W}
    (hV₀char : (V₀ : Subgroup W).Characteristic)
    (hV₀sq : ∀ v : W, v ∈ (V₀ : Subgroup W) → v * v = 1) :
    ∀ x : ↥A, q ↥A x ∈ Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) →
      x ∈ Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A) := by
  subst W
  intro x hx
  have hxNE : q ↥A x ∈ Subgroup.normalizer (S.E : Set (↥A ⧸ center ↥A)) :=
    Subgroup.centralizer_le_normalizer (S.E : Set (↥A ⧸ center ↥A)) hx
  have hxNW : x ∈ Subgroup.normalizer (S.E.comap (q ↥A) : Set ↥A) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective S.E
      (f := q ↥A) QuotientGroup.mk_surjective]
    exact hxNE
  let φ : MulAut (S.E.comap (q ↥A)) :=
    Subgroup.normalizerMonoidHom (H := S.E.comap (q ↥A)) ⟨x, hxNW⟩
  have hφV : (V₀ : Subgroup (S.E.comap (q ↥A))).map φ.toMonoidHom = V₀ :=
    Subgroup.characteristic_iff_map_eq.mp hV₀char φ
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
  have hφmem : (φ v₀ : S.E.comap (q ↥A)) ∈ V₀ := by
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom hv₀
    rwa [hφV] at h
  have hconj : ((φ v₀ : S.E.comap (q ↥A)) : ↥A) =
      x * ((v₀ : S.E.comap (q ↥A)) : ↥A) * x⁻¹ := rfl
  have hφsq : ((φ v₀ : S.E.comap (q ↥A)) : ↥A) *
      ((φ v₀ : S.E.comap (q ↥A)) : ↥A) = 1 :=
    congrArg Subtype.val (hV₀sq (φ v₀) hφmem)
  have hv₀sq : ((v₀ : S.E.comap (q ↥A)) : ↥A) *
      ((v₀ : S.E.comap (q ↥A)) : ↥A) = 1 := congrArg Subtype.val (hV₀sq v₀ hv₀)
  have hqconj : q ↥A ((φ v₀ : S.E.comap (q ↥A)) : ↥A) =
      q ↥A ((v₀ : S.E.comap (q ↥A)) : ↥A) := by
    rw [hconj, map_mul, map_mul, map_inv]
    have hcomm := Subgroup.mem_centralizer_iff.mp hx
      (q ↥A ((v₀ : S.E.comap (q ↥A)) : ↥A)) v₀.2
    calc q ↥A x * q ↥A ((v₀ : S.E.comap (q ↥A)) : ↥A) * (q ↥A x)⁻¹
        = (q ↥A ((v₀ : S.E.comap (q ↥A)) : ↥A) * q ↥A x) * (q ↥A x)⁻¹ := by rw [hcomm]
      _ = q ↥A ((v₀ : S.E.comap (q ↥A)) : ↥A) := by group
  have heq : ((φ v₀ : S.E.comap (q ↥A)) : ↥A) =
      ((v₀ : S.E.comap (q ↥A)) : ↥A) :=
    CFSG.EvenSporadicStandard.Induction.Closing.eq_of_mk_eq_of_sq hodd hφsq hv₀sq hqconj
  have hxv : x * ((v₀ : S.E.comap (q ↥A)) : ↥A) * x⁻¹ =
      ((v₀ : S.E.comap (q ↥A)) : ↥A) := by rw [← hconj, heq]
  have hxv2 : x * ((v₀ : S.E.comap (q ↥A)) : ↥A) =
      ((v₀ : S.E.comap (q ↥A)) : ↥A) * x := by
    have h' : (x * ((v₀ : S.E.comap (q ↥A)) : ↥A) * x⁻¹) * x =
        ((v₀ : S.E.comap (q ↥A)) : ↥A) * x :=
      congrArg (fun z : ↥A => z * x) hxv
    rw [mul_assoc, inv_mul_cancel, mul_one] at h'
    exact h'
  exact hxv2.symm

private theorem map_centralizer_eq {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A))
    {V₀ : Sylow 2 W}
    (hqVA : ((V₀ : Subgroup W).map W.subtype).map (q ↥A) = S.E)
    (hXlift : ∀ x : ↥A, q ↥A x ∈ Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) →
      x ∈ Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)) :
    (Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)).map
        (q ↥A) = Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) := by
  subst W
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer (((V₀ : Subgroup (S.E.comap (q ↥A))).map
      (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A) at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro e he
    rw [← hqVA] at he
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp he
    simpa only [map_mul] using congrArg (q ↥A) (hx v hv)
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact Subgroup.mem_map_of_mem (q ↥A) (hXlift x hy)

private theorem comap_H_basic {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A))
    {V₀ : Sylow 2 W}
    (hqVA : ((V₀ : Subgroup W).map W.subtype).map (q ↥A) = S.E)
    (hVAcomm : IsMulCommutative ((V₀ : Subgroup W).map W.subtype))
    (hVAinfZ : ((V₀ : Subgroup W).map W.subtype) ⊓ center ↥A = ⊥)
    (hXlift : ∀ x : ↥A, q ↥A x ∈ Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) →
      x ∈ Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)) :
    Nat.card (S.H.comap (q ↥A)) = Nat.card (center ↥A) * 20160 ∧
      (S.H.comap (q ↥A) ≤
        Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)) ∧
      (((V₀ : Subgroup W).map W.subtype) ≤
        Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)) ∧
      (∀ p ∈ S.H.comap (q ↥A),
        ∀ v ∈ (V₀ : Subgroup W).map W.subtype, Commute p v) ∧
      (S.H.comap (q ↥A) ⊓ ((V₀ : Subgroup W).map W.subtype) = ⊥) ∧
      Nat.card (Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A))) =
        Nat.card S.H * Nat.card S.E := by
  subst W
  have hq : Function.Surjective (q ↥A) := QuotientGroup.mk_surjective
  have hPcard : Nat.card (S.H.comap (q ↥A)) = Nat.card (center ↥A) * 20160 := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (q ↥A) hq S.H
    rw [QuotientGroup.ker_mk'] at h
    rw [h, S.card_H]
  have hPX : S.H.comap (q ↥A) ≤
      Subgroup.centralizer (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A) := by
    intro p hp
    exact hXlift p (S.H_le hp)
  have hVX : ((V₀ : Subgroup (S.E.comap (q ↥A))).map
      (S.E.comap (q ↥A)).subtype) ≤
      Subgroup.centralizer (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A) := by
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact hVAcomm
  have hcommPV : ∀ p ∈ S.H.comap (q ↥A),
      ∀ v ∈ (V₀ : Subgroup (S.E.comap (q ↥A))).map (S.E.comap (q ↥A)).subtype,
      Commute p v := by
    intro p hp v hv
    exact (Subgroup.mem_centralizer_iff.mp (hPX hp) v hv).symm
  have hPinfV : S.H.comap (q ↥A) ⊓
      ((V₀ : Subgroup (S.E.comap (q ↥A))).map (S.E.comap (q ↥A)).subtype) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxP, hxV⟩
    have hxH : q ↥A x ∈ S.H := hxP
    have hxE : q ↥A x ∈ S.E := by
      rw [← hqVA]
      exact Subgroup.mem_map_of_mem (q ↥A) hxV
    have hxbot : q ↥A x ∈ S.H ⊓ S.E := ⟨hxH, hxE⟩
    rw [S.inf_E] at hxbot
    have hxZ : x ∈ center ↥A := (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hxbot)
    have hbot : x ∈ ((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype) ⊓ center ↥A := ⟨hxV, hxZ⟩
    rw [hVAinfZ] at hbot
    exact Subgroup.mem_bot.mp hbot
  have hcardC : Nat.card (Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A))) =
      Nat.card S.H * Nat.card S.E := by
    rw [S.centralizer_eq]
    exact CFSG.card_sup_eq_mul_of_commute S.H S.E
      (fun h hh e he => (Subgroup.mem_centralizer_iff.mp (S.H_le hh) e he).symm) S.inf_E
  exact ⟨hPcard, hPX, hVX, hcommPV, hPinfV, hcardC⟩

private theorem centralizer_eq_sup {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A))
    {V₀ : Sylow 2 W}
    (hqX : (Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A)).map
      (q ↥A) = Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)))
    (hVAcard : Nat.card ((V₀ : Subgroup W).map W.subtype) = 4)
    (hPcard : Nat.card (S.H.comap (q ↥A)) = Nat.card (center ↥A) * 20160)
    (hPX : S.H.comap (q ↥A) ≤
      Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A))
    (hVX : ((V₀ : Subgroup W).map W.subtype) ≤
      Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A))
    (hcommPV : ∀ p ∈ S.H.comap (q ↥A),
      ∀ v ∈ (V₀ : Subgroup W).map W.subtype, Commute p v)
    (hPinfV : S.H.comap (q ↥A) ⊓ ((V₀ : Subgroup W).map W.subtype) = ⊥)
    (hcardC : Nat.card (Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A))) =
      Nat.card S.H * Nat.card S.E) :
    Subgroup.centralizer (((V₀ : Subgroup W).map W.subtype : Subgroup ↥A) : Set ↥A) =
      S.H.comap (q ↥A) ⊔ ((V₀ : Subgroup W).map W.subtype) := by
  subst W
  have hcardSup : Nat.card ↥(S.H.comap (q ↥A) ⊔
      ((V₀ : Subgroup (S.E.comap (q ↥A))).map (S.E.comap (q ↥A)).subtype)) =
      Nat.card (S.H.comap (q ↥A)) *
        Nat.card ((V₀ : Subgroup (S.E.comap (q ↥A))).map
          (S.E.comap (q ↥A)).subtype) :=
    CFSG.card_sup_eq_mul_of_commute _ _ hcommPV hPinfV
  have hcardX : Nat.card (Subgroup.centralizer
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A)) =
      Nat.card (S.H.comap (q ↥A)) *
        Nat.card ((V₀ : Subgroup (S.E.comap (q ↥A))).map
          (S.E.comap (q ↥A)).subtype) := by
    let X_A : Subgroup ↥A := Subgroup.centralizer
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A)
    have hf := Subgroup.card_ker_mul_card_range ((q ↥A).comp X_A.subtype)
    have hker : ((q ↥A).comp X_A.subtype).ker = (center ↥A).subgroupOf X_A := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (x : ↥A)
    have hrange : ((q ↥A).comp X_A.subtype).range =
        Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hqX]
    rw [hker, hrange] at hf
    have hZX : center ↥A ≤ X_A := Subgroup.center_le_centralizer
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A)
    have hZsub : Nat.card ((center ↥A).subgroupOf X_A) = Nat.card (center ↥A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv
    rw [hZsub, hcardC, S.card_E, S.card_H] at hf
    rw [hPcard, hVAcard]
    rw [← hf]
    ring
  have hcardEq : Nat.card (Subgroup.centralizer
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A)) =
      Nat.card ↥(S.H.comap (q ↥A) ⊔
        ((V₀ : Subgroup (S.E.comap (q ↥A))).map
          (S.E.comap (q ↥A)).subtype)) := by
    rw [hcardX, hcardSup]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hPX hVX) (le_of_eq hcardEq)).symm

private theorem K_eq_and_commutator {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {V_A : Subgroup ↥A} {P : Subgroup ↥A} {X_A : Subgroup ↥A}
    {K : Subgroup G}
    (hK : K = ⁅A ⊓ Subgroup.centralizer ((V_A.map A.subtype : Subgroup G) : Set G),
      A ⊓ Subgroup.centralizer ((V_A.map A.subtype : Subgroup G) : Set G)⁆)
    (hP : P = S.H.comap (q ↥A)) (hXA : X_A = Subgroup.centralizer (V_A : Set ↥A))
    (hXeq : X_A = P ⊔ V_A) (hVAcomm : IsMulCommutative V_A)
    (hcommPV : ∀ p ∈ P, ∀ v ∈ V_A, Commute p v) :
    K = ⁅X_A, X_A⁆.map A.subtype ∧ ⁅X_A, X_A⁆ = ⁅P, P⁆ ∧
      (⁅P, P⁆).map (q ↥A) = S.H := by
  have hKmap : K = ⁅X_A, X_A⁆.map A.subtype := by
    let V : Subgroup G := V_A.map A.subtype
    have hXG : A ⊓ Subgroup.centralizer (V : Set G) =
        (Subgroup.centralizer (V_A : Set ↥A)).map A.subtype := by
      ext g
      constructor
      · rintro ⟨hgA, hgC⟩
        change g ∈ Subgroup.centralizer (V : Set G) at hgC
        refine Subgroup.mem_map.mpr ⟨⟨g, hgA⟩, ?_, rfl⟩
        rw [Subgroup.mem_centralizer_iff] at hgC ⊢
        intro v hv
        apply Subtype.ext
        exact hgC (A.subtype v) (Subgroup.mem_map_of_mem A.subtype hv)
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        change x ∈ Subgroup.centralizer (V_A : Set ↥A) at hx
        change A.subtype x ∈ Subgroup.centralizer (V : Set G)
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro v hv
        obtain ⟨vx, hvx, rfl⟩ := Subgroup.mem_map.mp hv
        exact congrArg (fun z : ↥A => (z : G)) (hx vx hvx)
    rw [hXA, hK, hXG, ← Subgroup.map_commutator]
  have hKA : ⁅X_A, X_A⁆ = ⁅P, P⁆ := by
    apply le_antisymm
    · rw [hXeq]
      have h := CFSG.commutator_sup_le_commutator_right (G := ↥A) (A := V_A) (B := P)
        (fun a ha a' ha' => CFSG.commute_of_mem_of_isMulCommutative hVAcomm ha ha')
        (fun a ha b hb => (hcommPV b hb a ha).symm)
      simpa [sup_comm] using h
    · rw [hXeq]
      exact Subgroup.commutator_mono (H₁ := P) (H₂ := P) (K₁ := P ⊔ V_A) (K₂ := P ⊔ V_A)
        le_sup_left le_sup_left
  have hPq : P.map (q ↥A) = S.H := by
    rw [hP]
    exact Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective S.H
  have hP'q : (⁅P, P⁆).map (q ↥A) = S.H := by
    rw [Subgroup.map_commutator, hPq, S.der_H]
  exact ⟨hKmap, hKA, hP'q⟩

private theorem comap_H_le_commutator_sup_center {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (S : SuzFourSetup A)
    (hP'q : (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆).map (q ↥A) = S.H) :
    S.H.comap (q ↥A) ≤ ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A := by
  intro p hp
  have hqp : q ↥A p ∈ (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆).map (q ↥A) := by
    rw [hP'q]
    exact hp
  obtain ⟨p', hp', hp'q⟩ := Subgroup.mem_map.mp hqp
  have hz : (p' : ↥A)⁻¹ * p ∈ center ↥A := (QuotientGroup.eq).mp hp'q
  have hp_eq : p = p' * ((p' : ↥A)⁻¹ * p) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hp_eq]
  exact Subgroup.mul_mem_sup (S := ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆)
    (T := center ↥A) hp' hz

private theorem comap_H_eq_commutator_sup_center {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (S : SuzFourSetup A)
    (hP_le : S.H.comap (q ↥A) ≤ ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A)
    (hP'q : (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆).map (q ↥A) = S.H) :
    S.H.comap (q ↥A) = ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A := by
  have hq : Function.Surjective (q ↥A) := QuotientGroup.mk_surjective
  have hPcard : Nat.card (S.H.comap (q ↥A)) = Nat.card (center ↥A) * 20160 := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (q ↥A) hq S.H
    rw [QuotientGroup.ker_mk'] at h
    rw [h, S.card_H]
  refine Subgroup.eq_of_le_of_card_ge hP_le ?_
  have hqZ : (center ↥A).map (q ↥A) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff z).mpr hz
  have hqP'sup : (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A).map (q ↥A) = S.H := by
    rw [Subgroup.map_sup, hP'q, hqZ, sup_bot_eq]
  have hf := Subgroup.card_ker_mul_card_range
    ((q ↥A).comp (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A).subtype)
  have hker : ((q ↥A).comp (⁅S.H.comap (q ↥A),
      S.H.comap (q ↥A)⁆ ⊔ center ↥A).subtype).ker =
      (center ↥A).subgroupOf (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : ↥A)
  have hrange : ((q ↥A).comp (⁅S.H.comap (q ↥A),
      S.H.comap (q ↥A)⁆ ⊔ center ↥A).subtype).range = S.H := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hqP'sup]
  rw [hker, hrange] at hf
  have hZsub : Nat.card ((center ↥A).subgroupOf
      (⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A)) = Nat.card (center ↥A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : center ↥A ≤ ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A)).toEquiv
  rw [hZsub, S.card_H] at hf
  have hcard : Nat.card ↥(⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A) =
      Nat.card (S.H.comap (q ↥A)) := by
    rw [hPcard, ← hf]
  exact le_of_eq hcard

private theorem perfect_commutator {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A)
    (hP_eq : S.H.comap (q ↥A) = ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A) :
    ⁅⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆, ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆⁆ =
      ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ := by
  apply le_antisymm
    (CFSG.EvenSporadicStandard.Induction.Cover.commutator_self_le
      ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆)
  calc ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ =
        ⁅⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A,
          ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆ ⊔ center ↥A⁆ := by
        conv_lhs => rw [hP_eq]
    _ ≤ ⁅⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆,
          ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆⁆ :=
        CFSG.EvenSporadicStandard.Induction.Cover.commutator_sup_center_le
          ⁅S.H.comap (q ↥A), S.H.comap (q ↥A)⁆

private theorem center_eq_bot_of_lieModel {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) : Subgroup.center ↥S.H = ⊥ := by
  have hHsimple : IsSimpleGroup ↥S.H :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) S.lie
  by_contra h
  have htop : Subgroup.center ↥S.H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S.H) with h' | h'
    · exact absurd h' h
    · exact h'
  have hcomm : IsMulCommutative ↥S.H := Subgroup.center_eq_top_iff.mp htop
  have hp : Nat.Prime (Nat.card ↥S.H) := IsSimpleGroup.prime_card
  rw [S.card_H] at hp
  norm_num at hp

private theorem center_commutator_eq {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {X_A : Subgroup ↥A}
    (hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H)
    (hHcenter : Subgroup.center ↥S.H = ⊥) :
    Subgroup.center ↥⁅X_A, X_A⁆ = (center ↥A).subgroupOf ⁅X_A, X_A⁆ := by
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hzH : q ↥A (z : ↥A) ∈ S.H := by
      rw [← hKAq]
      exact Subgroup.mem_map_of_mem (q ↥A) z.2
    have hzq : (⟨q ↥A (z : ↥A), hzH⟩ : ↥S.H) ∈ Subgroup.center ↥S.H := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      change (h : ↥A ⧸ center ↥A) * q ↥A (z : ↥A) =
        q ↥A (z : ↥A) * (h : ↥A ⧸ center ↥A)
      obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp (by
        rw [hKAq]
        exact h.2)
      rw [← hkq, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    have hzq1 : q ↥A (z : ↥A) = 1 := by
      have hbot : (⟨q ↥A (z : ↥A), hzH⟩ : ↥S.H) ∈ (⊥ : Subgroup ↥S.H) :=
        hHcenter ▸ hzq
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hbot)
    exact (QuotientGroup.eq_one_iff (z : ↥A)).mp hzq1
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hzZ : (z : ↥A) ∈ center ↥A := Subgroup.mem_subgroupOf.mp hz
    exact Subgroup.mem_center_iff.mp hzZ (k : ↥A)

private theorem isL34Type_commutator {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {X_A : Subgroup ↥A}
    (hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H)
    (hcenterKA : Subgroup.center ↥⁅X_A, X_A⁆ = (center ↥A).subgroupOf ⁅X_A, X_A⁆) :
    IsL34Type (↥⁅X_A, X_A⁆ ⧸ Subgroup.center ↥⁅X_A, X_A⁆) := by
  let qKA : ↥⁅X_A, X_A⁆ →* ↥S.H :=
    ((q ↥A).comp ⁅X_A, X_A⁆.subtype).codRestrict S.H fun x => by
      rw [← hKAq]
      exact Subgroup.mem_map_of_mem (q ↥A) x.2
  have hqKA : Function.Surjective qKA := by
    intro h
    have hh : (h : ↥A ⧸ center ↥A) ∈ (⁅X_A, X_A⁆).map (q ↥A) := by
      rw [hKAq]
      exact h.2
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hh
    exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
  have hkerKA : qKA.ker = (center ↥A).subgroupOf ⁅X_A, X_A⁆ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : ↥A)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : ↥A)).mpr h)
  let e1 : (↥⁅X_A, X_A⁆) ⧸ Subgroup.center ↥⁅X_A, X_A⁆ ≃* ↥S.H :=
    (QuotientGroup.quotientMulEquivOfEq hcenterKA).trans
      ((QuotientGroup.quotientMulEquivOfEq hkerKA.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective qKA hqKA))
  exact S.lie.of_mulEquiv e1.symm

private theorem K_perfect_l34_image {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {X_A : Subgroup ↥A} {K : Subgroup G}
    (hKmap : K = ⁅X_A, X_A⁆.map A.subtype)
    (hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H)
    (hKAperf : ⁅⁅X_A, X_A⁆, ⁅X_A, X_A⁆⁆ = ⁅X_A, X_A⁆)
    (hX : IsL34Type (↥⁅X_A, X_A⁆ ⧸ Subgroup.center ↥⁅X_A, X_A⁆)) :
    ⁅K, K⁆ = K ∧ IsL34Type (↥K ⧸ Subgroup.center ↥K) ∧
      Nat.card ↥((K.subgroupOf A).map (q ↥A)) = 20160 := by
  have hKperf : ⁅K, K⁆ = K := by
    calc ⁅K, K⁆ = ⁅(⁅X_A, X_A⁆).map A.subtype, (⁅X_A, X_A⁆).map A.subtype⁆ := by
          rw [hKmap]
      _ = (⁅⁅X_A, X_A⁆, ⁅X_A, X_A⁆⁆).map A.subtype := by
          rw [← Subgroup.map_commutator]
      _ = (⁅X_A, X_A⁆).map A.subtype := by rw [hKAperf]
      _ = K := hKmap.symm
  have hKsubA : K.subgroupOf A = ⁅X_A, X_A⁆ := by
    rw [← Subgroup.comap_subtype]
    rw [hKmap, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hcard_image : Nat.card ↥((K.subgroupOf A).map (q ↥A)) = 20160 := by
    rw [hKsubA, hKAq, S.card_H]
  have hl34 : IsL34Type (↥K ⧸ Subgroup.center ↥K) := by
    let eK : ↥⁅X_A, X_A⁆ ≃* ↥K :=
      (Subgroup.equivMapOfInjective ⁅X_A, X_A⁆ A.subtype A.subtype_injective).trans
        (MulEquiv.subgroupCongr hKmap.symm)
    let eQ : (↥⁅X_A, X_A⁆) ⧸ Subgroup.center ↥⁅X_A, X_A⁆ ≃*
        ↥K ⧸ Subgroup.center ↥K :=
      QuotientGroup.congr (Subgroup.center ↥⁅X_A, X_A⁆) (Subgroup.center ↥K) eK
        (Subgroup.map_center_eq eK)
    exact hX.of_mulEquiv eQ
  exact ⟨hKperf, hl34, hcard_image⟩

private theorem odd_orderOf_lift {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) (hodd : Odd (Nat.card (center ↥A))) {yA : ↥A}
    (hyA : q ↥A yA = S.n) : Odd (orderOf (A.subtype yA)) := by
  have hyA_odd : Odd (orderOf yA) := by
    apply CFSG.EvenSporadicStandard.Induction.Cover.odd_orderOf_of_mk hodd
    rw [show q ↥A yA = S.n from hyA, S.orderOf_n]
    norm_num
  change Odd (orderOf ((yA : ↥A) : G))
  exact Subgroup.orderOf_coe yA ▸ hyA_odd

private theorem lift_centralizes_commutator {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {X_A : Subgroup ↥A}
    (hKAperf : ⁅⁅X_A, X_A⁆, ⁅X_A, X_A⁆⁆ = ⁅X_A, X_A⁆)
    (hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H) {yA : ↥A} (hyA : q ↥A yA = S.n) :
    yA ∈ Subgroup.centralizer ((⁅X_A, X_A⁆ : Subgroup ↥A) : Set ↥A) := by
  rw [CFSG.EvenSporadicStandard.Induction.Cover.mem_centralizer_iff_of_perfect
    (K := ⁅X_A, X_A⁆) hKAperf]
  rw [hKAq, hyA]
  exact S.n_centralizes_H

private theorem lift_centralizes_K {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {X_A : Subgroup ↥A} {K : Subgroup G}
    (hKmap : K = ⁅X_A, X_A⁆.map A.subtype)
    {yA : ↥A} (hyKA : yA ∈ Subgroup.centralizer ((⁅X_A, X_A⁆ : Subgroup ↥A) : Set ↥A)) :
    A.subtype yA ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : k ∈ (⁅X_A, X_A⁆).map A.subtype := by
    rwa [← hKmap]
  obtain ⟨kA, hkA, rfl⟩ := Subgroup.mem_map.mp hk'
  exact congrArg (fun z : ↥A => (z : G))
    (Subgroup.mem_centralizer_iff.mp hyKA kA hkA)

private theorem lift_normalizes_V {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A))
    {V₀ : Sylow 2 W} (hV₀char : (V₀ : Subgroup W).Characteristic)
    {yA : ↥A} (hyA : q ↥A yA = S.n) :
    A.subtype yA ∈ Subgroup.normalizer
      ((((V₀ : Subgroup W).map W.subtype).map A.subtype : Subgroup G) : Set G) := by
  subst W
  have hyA_NW : yA ∈ Subgroup.normalizer (S.E.comap (q ↥A) : Set ↥A) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective S.E
      (f := q ↥A) QuotientGroup.mk_surjective]
    rw [Subgroup.mem_comap, hyA]
    exact S.n_normalizes_E
  let φy : MulAut (S.E.comap (q ↥A)) :=
    Subgroup.normalizerMonoidHom (H := S.E.comap (q ↥A)) ⟨yA, hyA_NW⟩
  have hφyV : (V₀ : Subgroup (S.E.comap (q ↥A))).map φy.toMonoidHom = V₀ :=
    Subgroup.characteristic_iff_map_eq.mp hV₀char φy
  have hyA_normV_A : yA ∈ Subgroup.normalizer
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype : Subgroup ↥A) : Set ↥A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
      have hmem : (φy v₀ : S.E.comap (q ↥A)) ∈ V₀ := by
        have h := Subgroup.mem_map_of_mem φy.toMonoidHom hv₀
        rwa [hφyV] at h
      have hmem' : ((φy v₀ : S.E.comap (q ↥A)) : ↥A) ∈
          (V₀ : Subgroup (S.E.comap (q ↥A))).map (S.E.comap (q ↥A)).subtype :=
        Subgroup.mem_map_of_mem (S.E.comap (q ↥A)).subtype hmem
      exact hmem'
    · exact le_of_eq (Subgroup.card_map_of_injective (K :=
        (V₀ : Subgroup (S.E.comap (q ↥A))).map (S.E.comap (q ↥A)).subtype)
        (f := (MulAut.conj yA).toMonoidHom) (MulAut.conj yA).injective).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨vA, hvA, rfl⟩ := Subgroup.mem_map.mp hv
    have hmem : yA * vA * yA⁻¹ ∈ (V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype :=
      (Subgroup.mem_normalizer_iff.mp hyA_normV_A vA).mp hvA
    have hyconj : A.subtype yA * A.subtype vA * (A.subtype yA)⁻¹ =
        A.subtype (yA * vA * yA⁻¹) := by
      simp [map_mul, map_inv]
    change A.subtype yA * A.subtype vA * (A.subtype yA)⁻¹ ∈
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype).map A.subtype)
    rw [hyconj]
    exact Subgroup.mem_map_of_mem A.subtype hmem
  · exact le_of_eq (Subgroup.card_map_of_injective (K :=
      (((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype).map A.subtype))
      (f := (MulAut.conj (A.subtype yA)).toMonoidHom) (MulAut.conj _).injective).symm

private theorem lift_moves {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A)) {V₀ : Sylow 2 W}
    (hVAinfZ : ((V₀ : Subgroup W).map W.subtype) ⊓ center ↥A = ⊥)
    (hqVA : ((V₀ : Subgroup W).map W.subtype).map (q ↥A) = S.E)
    {yA : ↥A} (hyA : q ↥A yA = S.n) :
    ∀ v ∈ ((V₀ : Subgroup W).map W.subtype).map A.subtype, v ≠ 1 →
      A.subtype yA * v * (A.subtype yA)⁻¹ ≠ v := by
  subst W
  intro v hv hv1 hconj
  obtain ⟨vA, hvA, rfl⟩ := Subgroup.mem_map.mp hv
  have hvA_ne : vA ≠ 1 := by
    intro h
    apply hv1
    rw [h]
    rfl
  have hvE : q ↥A vA ∈ S.E := by
    rw [← hqVA]
    exact Subgroup.mem_map_of_mem (q ↥A) hvA
  have hv_ne : q ↥A vA ≠ 1 := by
    intro hq1
    have hvZ : vA ∈ center ↥A := (QuotientGroup.eq_one_iff vA).mp hq1
    have hbot : vA ∈ ((V₀ : Subgroup (S.E.comap (q ↥A))).map
        (S.E.comap (q ↥A)).subtype) ⊓ center ↥A := ⟨hvA, hvZ⟩
    rw [hVAinfZ] at hbot
    exact hvA_ne (Subgroup.mem_bot.mp hbot)
  have hfixn := S.n_moves_E (q ↥A vA) hvE hv_ne
  have hXeq' : yA * vA * yA⁻¹ = vA := by
    apply A.subtype_injective
    simpa [map_mul, map_inv] using hconj
  have hqeq : S.n * q ↥A vA * S.n⁻¹ = q ↥A vA := by
    have h := congrArg (q ↥A) hXeq'
    simpa [hyA, map_mul, map_inv] using h
  exact hfixn hqeq

private theorem exists_lift_y {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) (hodd : Odd (Nat.card (center ↥A))) {W : Subgroup ↥A}
    (hW : W = S.E.comap (q ↥A)) {V₀ : Sylow 2 W}
    (hV₀char : (V₀ : Subgroup W).Characteristic)
    (hVAinfZ : ((V₀ : Subgroup W).map W.subtype) ⊓ center ↥A = ⊥)
    (hqVA : ((V₀ : Subgroup W).map W.subtype).map (q ↥A) = S.E)
    {X_A : Subgroup ↥A} {K : Subgroup G}
    (hKAperf : ⁅⁅X_A, X_A⁆, ⁅X_A, X_A⁆⁆ = ⁅X_A, X_A⁆)
    (hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H)
    (hKmap : K = ⁅X_A, X_A⁆.map A.subtype) :
    ∃ y : G, y ∈ A ∧ y ∈ Subgroup.centralizer (K : Set G) ∧ Odd (orderOf y) ∧
      y ∈ Subgroup.normalizer
        ((((V₀ : Subgroup W).map W.subtype).map A.subtype : Subgroup G) : Set G) ∧
      ∀ v ∈ ((V₀ : Subgroup W).map W.subtype).map A.subtype, v ≠ 1 →
        y * v * y⁻¹ ≠ v := by
  have hqA : Function.Surjective (q ↥A) := QuotientGroup.mk_surjective
  obtain ⟨yA, hyA⟩ := hqA S.n
  have hodd_y := odd_orderOf_lift S hodd hyA
  have hyKA := lift_centralizes_commutator S hKAperf hKAq hyA
  have hy_centralizes := lift_centralizes_K hKmap hyKA
  have hy_normV := lift_normalizes_V S hW hV₀char hyA
  have hy_moves := lift_moves S hW hVAinfZ hqVA hyA
  exact ⟨A.subtype yA, yA.2, hy_centralizes, hodd_y, hy_normV, hy_moves⟩

private theorem card_centralizer_lift {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (S : SuzFourSetup A) {W : Subgroup ↥A} (hW : W = S.E.comap (q ↥A)) {V₀ : Sylow 2 W}
    (hV₀inf : (V₀ : Subgroup W) ⊓ (center ↥A).subgroupOf W = ⊥) :
    ∀ v (hv : v ∈ ((V₀ : Subgroup W).map W.subtype).map A.subtype), v ≠ 1 →
      Nat.card (Subgroup.centralizer
        ({((⟨v, Subgroup.map_subtype_le _ hv⟩ : ↥A) : ↥A ⧸ center ↥A)} :
          Set (↥A ⧸ center ↥A))) = 161280 := by
  subst W
  intro v hv hv1
  obtain ⟨vA, hvA, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨v0, hv0, rfl⟩ := Subgroup.mem_map.mp hvA
  have hv0ne : v0 ≠ 1 := by
    intro h
    apply hv1
    rw [h]
    rfl
  have hv0E : q ↥A (v0 : S.E.comap (q ↥A)) ∈ S.E := v0.2
  have hv0_ne : q ↥A (v0 : S.E.comap (q ↥A)) ≠ 1 := by
    intro hq1
    have hv0Z : (v0 : S.E.comap (q ↥A)) ∈
        (center ↥A).subgroupOf (S.E.comap (q ↥A)) := by
      rw [Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff (v0 : ↥A)).mp hq1
    have hbot : v0 ∈ (V₀ : Subgroup (S.E.comap (q ↥A))) ⊓
        (center ↥A).subgroupOf (S.E.comap (q ↥A)) := ⟨hv0, hv0Z⟩
    rw [hV₀inf] at hbot
    exact hv0ne (Subgroup.mem_bot.mp hbot)
  change Nat.card (Subgroup.centralizer
    ({q ↥A (v0 : S.E.comap (q ↥A))} : Set (↥A ⧸ center ↥A))) = 161280
  exact S.centralizer_card (q ↥A (v0 : S.E.comap (q ↥A))) hv0E hv0_ne

private theorem map_V_card_sq {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {V_A : Subgroup ↥A} (hVAcard : Nat.card V_A = 4)
    (hVAsq : ∀ v ∈ V_A, v * v = 1) :
    Nat.card (V_A.map A.subtype) = 4 ∧ (∀ v ∈ V_A.map A.subtype, v * v = 1) := by
  have hcard : Nat.card (V_A.map A.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hVAcard]
  refine ⟨hcard, ?_⟩
  intro v hv
  obtain ⟨vA, hvA, rfl⟩ := Subgroup.mem_map.mp hv
  exact congrArg (fun z : ↥A => (z : G)) (hVAsq vA hvA)

private theorem mk_l34SuzOddData {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {y : G}
    (hVA : V ≤ A) (hVcard : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (hcent : ∀ v (hv : v ∈ V), v ≠ 1 →
      Nat.card (Subgroup.centralizer ({((⟨v, hVA hv⟩ : ↥A) : ↥A ⧸ center ↥A)} :
        Set (↥A ⧸ center ↥A))) = 161280)
    (hK : K = ⁅A ⊓ Subgroup.centralizer (V : Set G),
      A ⊓ Subgroup.centralizer (V : Set G)⁆)
    (hperf : ⁅K, K⁆ = K) (hl34 : IsL34Type (↥K ⧸ Subgroup.center ↥K))
    (himage : Nat.card ↥((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) = 20160)
    (hy : y ∈ A) (hyc : y ∈ Subgroup.centralizer (K : Set G)) (hyo : Odd (orderOf y))
    (hyn : y ∈ Subgroup.normalizer (V : Set G))
    (hym : ∀ v ∈ V, v ≠ 1 → y * v * y⁻¹ ≠ v) :
    L34SuzOddData A V K y where
  le_A := hVA
  card_V := hVcard
  mul_self := hVsq
  card_centralizer := hcent
  K_eq := hK
  perfect := hperf
  l34 := hl34
  card_image := himage
  y_mem := hy
  y_centralizes := hyc
  odd_orderOf_y := hyo
  y_normalizes := hyn
  y_moves := hym

theorem exists_l34SuzOddData
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ (V K : Subgroup G) (y : G), L34SuzOddData A V K y := by
  classical
  obtain ⟨S⟩ := exists_suzFourSetup (A := A) hsuz
  let W : Subgroup ↥A := S.E.comap (q ↥A)
  obtain ⟨V₀, hV₀card, hV₀char⟩ := exists_sylow_four_comap hodd S
  obtain ⟨hV₀inf, hV₀sq⟩ := sylow_comap_inf_sq (V₀ := V₀) hodd S rfl
  obtain ⟨hVAcard, hVAsq, hVAcomm, hVAinfZ, hqVA⟩ :=
    four_lift_facts S rfl hV₀card hV₀sq hV₀inf
  let V_A : Subgroup ↥A := (V₀ : Subgroup W).map W.subtype
  let V : Subgroup G := V_A.map A.subtype
  let X_A : Subgroup ↥A := Subgroup.centralizer (V_A : Set ↥A)
  have hXlift : ∀ x : ↥A, q ↥A x ∈ Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) →
      x ∈ X_A := centralizer_lift hodd S rfl hV₀char hV₀sq
  have hqX : X_A.map (q ↥A) = Subgroup.centralizer (S.E : Set (↥A ⧸ center ↥A)) :=
    map_centralizer_eq S rfl hqVA hXlift
  obtain ⟨hPcard, hPX, hVX, hcommPV, hPinfV, hcardC⟩ :=
    comap_H_basic S rfl hqVA hVAcomm hVAinfZ hXlift
  have hXeq : X_A = S.H.comap (q ↥A) ⊔ V_A :=
    centralizer_eq_sup S rfl hqX hVAcard hPcard hPX hVX hcommPV hPinfV hcardC
  let P : Subgroup ↥A := S.H.comap (q ↥A)
  let K : Subgroup G := ⁅A ⊓ Subgroup.centralizer (V : Set G),
    A ⊓ Subgroup.centralizer (V : Set G)⁆
  obtain ⟨hKmap, hKA, hP'q⟩ :=
    K_eq_and_commutator (V_A := V_A) (P := P) (X_A := X_A) (K := K) S rfl rfl rfl hXeq
      hVAcomm hcommPV
  have hKAq : (⁅X_A, X_A⁆).map (q ↥A) = S.H := by
    rw [hKA]
    exact hP'q
  have hP_le := comap_H_le_commutator_sup_center S hP'q
  have hP_eq := comap_H_eq_commutator_sup_center S hP_le hP'q
  have hP'perf := perfect_commutator S hP_eq
  have hKAperf : ⁅⁅X_A, X_A⁆, ⁅X_A, X_A⁆⁆ = ⁅X_A, X_A⁆ := by
    rw [hKA]
    exact hP'perf
  have hH0center : Subgroup.center ↥S.H = ⊥ := center_eq_bot_of_lieModel S
  have hcenterKA := center_commutator_eq S hKAq hH0center
  have hXl34 := isL34Type_commutator S hKAq hcenterKA
  obtain ⟨hKperf, hl34, hcard_image⟩ :=
    K_perfect_l34_image (X_A := X_A) (K := K) S hKmap hKAq hKAperf hXl34
  obtain ⟨y, hy_mem, hy_centralizes, hodd_y, hy_normV, hy_moves⟩ :=
    exists_lift_y S hodd rfl hV₀char hVAinfZ hqVA hKAperf hKAq hKmap
  have hcard_cent := card_centralizer_lift S rfl hV₀inf
  obtain ⟨hVcard, hVsq⟩ := map_V_card_sq hVAcard hVAsq
  exact ⟨V, K, y,
    mk_l34SuzOddData (Subgroup.map_subtype_le V_A) hVcard hVsq hcard_cent rfl hKperf hl34
      hcard_image hy_mem hy_centralizes hodd_y hy_normV hy_moves⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
