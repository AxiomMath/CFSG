module

public import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
public import CFSG.FeitThompson.Local.FittingMonoNormal
public import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
public import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
public import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
public import CFSG.FeitThompson.Local.MinimalCounterexampleUniqueMinimalNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open scoped commutatorElement

universe u

attribute [local instance] conjMulDistribMulAction

section Aux

variable {L : Type*} [Group L]

private theorem mem_normalizer_of_forall_conj {W : Subgroup L} {g : L}
    (h : ∀ x ∈ W, g * x * g⁻¹ ∈ W) (h' : ∀ x ∈ W, g⁻¹ * x * g ∈ W) :
    g ∈ normalizer (W : Set L) :=
  mem_normalizer_iff.2 fun x => ⟨h x, fun hx => by simpa [mul_assoc] using h' _ hx⟩

private theorem mem_normalizer_of_normal {W : Subgroup L} (hW : W.Normal) (g : L) :
    g ∈ normalizer (W : Set L) := by
  rw [Subgroup.normalizer_eq_top_iff.2 hW]; exact mem_top g

private theorem conj_mem_centralizer {K : Subgroup L} {g x : L}
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ K) (hx : x ∈ centralizer (K : Set L)) :
    g * x * g⁻¹ ∈ centralizer (K : Set L) := by
  rw [mem_centralizer_iff]
  intro k hk
  have hcomm := mem_centralizer_iff.1 hx _ (hg k hk)
  calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * x * g⁻¹) * k := by group

private theorem mem_normalizer_inf_centralizer {V K : Subgroup L} {g : L}
    (hV : g ∈ normalizer (V : Set L)) (hK : g ∈ normalizer (K : Set L)) :
    g ∈ normalizer ((V ⊓ centralizer (K : Set L) : Subgroup L) : Set L) := by
  have hKf : ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun k hk => by
    simpa using (mem_normalizer_iff.1 (inv_mem hK) k).1 hk
  have hKf' : ∀ k ∈ K, (g⁻¹)⁻¹ * k * g⁻¹ ∈ K := fun k hk => by
    simpa using (mem_normalizer_iff.1 hK k).1 hk
  refine mem_normalizer_of_forall_conj (fun x hx => mem_inf.2 ⟨?_, ?_⟩)
    (fun x hx => mem_inf.2 ⟨?_, ?_⟩)
  · exact (mem_normalizer_iff.1 hV x).1 (mem_inf.1 hx).1
  · exact conj_mem_centralizer hKf (mem_inf.1 hx).2
  · simpa using (mem_normalizer_iff.1 (inv_mem hV) x).1 (mem_inf.1 hx).1
  · simpa using conj_mem_centralizer (g := g⁻¹) hKf' (mem_inf.1 hx).2

private theorem mem_normalizer_commutator {V K : Subgroup L} {g : L}
    (hV : g ∈ normalizer (V : Set L)) (hK : g ∈ normalizer (K : Set L)) :
    g ∈ normalizer ((⁅V, K⁆ : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff_map_conj_eq] at hV hK ⊢
  rw [Subgroup.map_commutator, hV, hK]

private theorem le_normalizer_of_le_of_isMulCommutative {V W : Subgroup L}
    (hV : IsMulCommutative ↥V) (hWV : W ≤ V) : V ≤ normalizer (W : Set L) := by
  have key : ∀ v ∈ V, ∀ x ∈ W, v * x = x * v := fun v hv x hx =>
    congrArg Subtype.val (hV.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨x, hWV hx⟩)
  intro v hv
  refine mem_normalizer_of_forall_conj (fun x hx => ?_) (fun x hx => ?_)
  · rw [key v hv x hx, mul_inv_cancel_right]; exact hx
  · rw [key v⁻¹ (V.inv_mem hv) x hx, inv_mul_cancel_right]; exact hx

private theorem map_subtype_top (V : Subgroup L) : (⊤ : Subgroup ↥V).map V.subtype = V := by
  rw [← Subgroup.top_subgroupOf (H := V), Subgroup.subgroupOf_map_subtype, top_inf_eq]

private instance distribMulActionAdditive {M N : Type*} [Monoid M] [CommGroup N]
    [MulDistribMulAction M N] : DistribMulAction M (Additive N) where
  smul m x := Additive.ofMul (m • x.toMul)
  one_smul x := by
    change Additive.ofMul ((1 : M) • x.toMul) = x
    rw [one_smul, ofMul_toMul]
  mul_smul m n x := by
    change Additive.ofMul ((m * n) • x.toMul)
      = Additive.ofMul (m • (Additive.ofMul (n • x.toMul)).toMul)
    rw [mul_smul, toMul_ofMul]
  smul_zero m := by
    change Additive.ofMul (m • (1 : N)) = 0
    rw [smul_one]; rfl
  smul_add m x y := by
    change Additive.ofMul (m • (x.toMul * y.toMul)) = _
    rw [smul_mul']; rfl

private theorem ofMul_smul' {M N : Type*} [Monoid M] [CommGroup N] [MulDistribMulAction M N]
    (m : M) (v : N) : Additive.ofMul (m • v) = m • Additive.ofMul v := rfl

private theorem toMul_smul' {M N : Type*} [Monoid M] [CommGroup N] [MulDistribMulAction M N]
    (m : M) (x : Additive N) : (m • x).toMul = m • x.toMul := rfl

private theorem toAddSubgroup_fixedPoints {B V : Type*} [Group B] [CommGroup V]
    [MulDistribMulAction B V] :
    (FixedPoints.subgroup B V).toAddSubgroup = FixedPoints.addSubgroup B (Additive V) := by
  ext x
  rw [show (x ∈ (FixedPoints.subgroup B V).toAddSubgroup) ↔ x.toMul ∈ FixedPoints.subgroup B V
    from Iff.rfl, FixedPoints.mem_subgroup, FixedPoints.mem_addSubgroup]
  exact ⟨fun h m => Additive.toMul.injective (by rw [toMul_smul', h m]),
    fun h m => by rw [← toMul_smul', h m]⟩

private theorem ofMul_inv_mul_smul' {B V : Type*} [Group B] [CommGroup V]
    [MulDistribMulAction B V] (a : B) (v : V) :
    Additive.ofMul (v⁻¹ * a • v) = a • Additive.ofMul v - Additive.ofMul v := by
  rw [mul_comm, ← div_eq_mul_inv, ofMul_div, ofMul_smul']

private theorem toAddSubgroup_smulDisplacementSubgroup {B V : Type*} [Group B] [CommGroup V]
    [MulDistribMulAction B V] :
    (smulDisplacementSubgroup B V).toAddSubgroup = displacementAddSubgroup B (Additive V) := by
  rw [smulDisplacementSubgroup_eq_closure, Subgroup.toAddSubgroup_closure,
    displacementAddSubgroup_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, v, hv⟩
    exact ⟨a, Additive.ofMul v, by rw [← ofMul_inv_mul_smul', hv, ofMul_toMul]⟩
  · rintro ⟨a, v, hv⟩
    refine ⟨a, v.toMul, ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_inv_mul_smul', ofMul_toMul, hv, ofMul_toMul]

private theorem isCompl_fixedPoints_smulDisplacementSubgroup_commGroup {B V : Type*} [Group B]
    [CommGroup V] [MulDistribMulAction B V] [Finite B] [Finite V]
    (hcop : (Nat.card B).Coprime (Nat.card V)) :
    IsCompl (FixedPoints.subgroup B V) (smulDisplacementSubgroup B V) := by
  have hcard : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  have h := isCompl_fixedPoints_displacementAddSubgroup (B := B) (V := Additive V) (by rwa [hcard])
  rw [← toAddSubgroup_fixedPoints, ← toAddSubgroup_smulDisplacementSubgroup] at h
  exact (Subgroup.toAddSubgroup (G := V)).isCompl_iff.2 h

theorem isCompl_fixedPoints_smulDisplacementSubgroup {B V : Type*} [Group B] [Group V]
    [MulDistribMulAction B V] [Finite B] [Finite V] (hV : IsMulCommutative V)
    (hcop : (Nat.card B).Coprime (Nat.card V)) :
    IsCompl (FixedPoints.subgroup B V) (smulDisplacementSubgroup B V) :=
  letI : CommGroup V := hV.instCommGroup
  isCompl_fixedPoints_smulDisplacementSubgroup_commGroup hcop

theorem map_subtype_fixedPoints_conj (V K : Subgroup L) [V.Normal] :
    (FixedPoints.subgroup ↥K ↥V).map V.subtype = V ⊓ centralizer (K : Set L) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf, mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, fun k hk => ?_⟩
    have h := congrArg Subtype.val ((FixedPoints.mem_subgroup ↥K ↥V v).1 hv ⟨k, hk⟩)
    rw [conjMulDistribMulAction_smul_coe] at h
    calc k * (v : L) = (k * (v : L) * k⁻¹) * k := by group
      _ = (v : L) * k := by rw [h]
  · rintro ⟨hxV, hx⟩
    refine ⟨⟨x, hxV⟩, (FixedPoints.mem_subgroup ↥K ↥V _).2 fun k => Subtype.ext ?_, rfl⟩
    rw [conjMulDistribMulAction_smul_coe]
    change (k : L) * x * (k : L)⁻¹ = x
    rw [hx (k : L) k.2, mul_inv_cancel_right]

variable [Finite L] (V K : Subgroup L) [V.Normal]

theorem inf_centralizer_inf_commutator_eq_bot (hVab : IsMulCommutative ↥V)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥V)) :
    (V ⊓ centralizer (K : Set L)) ⊓ ⁅V, K⁆ = ⊥ := by
  have h := (isCompl_fixedPoints_smulDisplacementSubgroup (B := ↥K) (V := ↥V) hVab hcop).inf_eq_bot
  have h2 := congrArg (fun S : Subgroup ↥V => S.map V.subtype) h
  simpa [Subgroup.map_inf _ _ _ V.subtype_injective, map_subtype_fixedPoints_conj,
    map_subtype_smulDisplacementSubgroup_eq_commutator] using h2

theorem sup_inf_centralizer_commutator_eq (hVab : IsMulCommutative ↥V)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥V)) :
    (V ⊓ centralizer (K : Set L)) ⊔ ⁅V, K⁆ = V := by
  have h := (isCompl_fixedPoints_smulDisplacementSubgroup (B := ↥K) (V := ↥V) hVab hcop).sup_eq_top
  have h2 := congrArg (fun S : Subgroup ↥V => S.map V.subtype) h
  simp only [Subgroup.map_sup] at h2
  rwa [map_subtype_fixedPoints_conj, map_subtype_smulDisplacementSubgroup_eq_commutator,
    map_subtype_top] at h2

end Aux

variable {G : Type u} [Group G] [Finite G]

structure IsPrimeCentralizerComplementSetup (p : ℕ) (H R R0 V K U N P : Subgroup G) : Prop where
  admissible : IsAdmissibleCoprimeActionQuadruple G H R R0
  prime_p : p.Prime
  not_hasPLengthLeOne : ¬ HasPLengthLeOne p ↥⁅H, R⁆
  minimal : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
      HasPLengthLeOne p ↥⁅J, A⁆
  V_eq : V = (fittingRaw ↥H).map H.subtype
  K_le_H : K ≤ H
  R_le_normalizer_K : R ≤ normalizer (K : Set G)
  U_eq : U = V ⊔ K
  N_eq : N = normalizer (K : Set G) ⊓ H
  P_le_N : P ≤ N
  card_P : Nat.card ↥P = p ^ (Nat.card ↥N).factorization p
  R_le_normalizer_P : R ≤ normalizer (P : Set G)
  U_subgroupOf_eq : U.subgroupOf H = fittingRawPreimage ↥H
  inf_K_V : K ⊓ V = ⊥
  coprime_card_K : (Nat.card ↥K).Coprime p
  sup_V_N : V ⊔ N = H
  commutator_K_P_ne_bot : ⁅K, P⁆ ≠ ⊥

namespace IsPrimeCentralizerComplementSetup

variable {p : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerComplementSetup p H R R0 V K U N P)

include hc

theorem isSolvable : Group.IsSolvable G := hc.admissible.isSolvable

theorem V_le_H : V ≤ H := hc.V_eq ▸ Subgroup.map_subtype_le _

theorem V_normal : V.Normal := hc.V_eq ▸ normal_map_subtype_fittingRaw hc.admissible.normal

theorem N_le_H : N ≤ H := hc.N_eq ▸ inf_le_right

theorem K_le_N : K ≤ N := hc.N_eq ▸ le_inf Subgroup.le_normalizer hc.K_le_H

theorem N_le_normalizer_K : N ≤ normalizer (K : Set G) := hc.N_eq ▸ inf_le_left

theorem isElementaryAbelian_V : IsElementaryAbelian p V := by
  have : Fact p.Prime := ⟨hc.prime_p⟩
  rw [hc.V_eq]
  exact isElementaryAbelian_map_subtype_fittingRaw_of_minimal hc.admissible
    hc.not_hasPLengthLeOne hc.minimal

theorem isMulCommutative_V : IsMulCommutative ↥V := hc.isElementaryAbelian_V.isMulCommutative

theorem centralizer_V_inf_H : centralizer (V : Set G) ⊓ H = V := by
  have : Fact p.Prime := ⟨hc.prime_p⟩
  rw [hc.V_eq]
  exact centralizer_map_subtype_fittingRaw_inf_eq_of_minimal hc.admissible
    hc.not_hasPLengthLeOne hc.minimal

theorem coprime_card_K_card_V : (Nat.card ↥K).Coprime (Nat.card ↥V) := by
  obtain ⟨d, hd⟩ := hc.isElementaryAbelian_V.exists_natCard_eq_pow hc.prime_p
  rw [hd]
  exact hc.coprime_card_K.pow_right d

theorem sup_sup_eq_top : V ⊔ N ⊔ R = ⊤ := by
  rw [hc.sup_V_N]; exact hc.admissible.sup_eq_top

theorem normal_inf_centralizer : (V ⊓ centralizer (K : Set G)).Normal := by
  have hVn := hc.V_normal
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hc.sup_sup_eq_top]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_normalizer_of_le_of_isMulCommutative hc.isMulCommutative_V inf_le_left
  · exact fun n hn => mem_normalizer_inf_centralizer (mem_normalizer_of_normal hVn n)
      (hc.N_le_normalizer_K hn)
  · exact fun r hr => mem_normalizer_inf_centralizer (mem_normalizer_of_normal hVn r)
      (hc.R_le_normalizer_K hr)

theorem normal_commutator : (⁅V, K⁆ : Subgroup G).Normal := by
  have hVn := hc.V_normal
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hc.sup_sup_eq_top]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_normalizer_of_le_of_isMulCommutative hc.isMulCommutative_V
      (Subgroup.commutator_le_left V K)
  · exact fun n hn => mem_normalizer_commutator (mem_normalizer_of_normal hVn n)
      (hc.N_le_normalizer_K hn)
  · exact fun r hr => mem_normalizer_commutator (mem_normalizer_of_normal hVn r)
      (hc.R_le_normalizer_K hr)

theorem inf_centralizer_eq_bot : V ⊓ centralizer (K : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨hc.prime_p⟩
  have := hc.V_normal
  have := hc.normal_inf_centralizer
  have := hc.normal_commutator
  rcases eq_bot_or_eq_bot_of_inf_eq_bot_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal
    (V₁ := V ⊓ centralizer (K : Set G)) (V₂ := ⁅V, K⁆) (inf_le_left.trans hc.V_le_H)
    ((Subgroup.commutator_le_left V K).trans hc.V_le_H)
    (inf_centralizer_inf_commutator_eq_bot V K hc.isMulCommutative_V
      hc.coprime_card_K_card_V) with h | h
  · exact h
  · exfalso
    have hKcent : K ≤ centralizer (V : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
    have hKV : K ≤ V := by
      calc K ≤ centralizer (V : Set G) ⊓ H := le_inf hKcent hc.K_le_H
        _ = V := hc.centralizer_V_inf_H
    have hKbot : K = ⊥ := by rw [← hc.inf_K_V]; exact (inf_eq_left.2 hKV).symm
    exact hc.commutator_K_P_ne_bot (by rw [hKbot]; exact Subgroup.commutator_bot_left P)

theorem commutator_eq : (⁅V, K⁆ : Subgroup G) = V := by
  have := hc.V_normal
  have h := sup_inf_centralizer_commutator_eq V K hc.isMulCommutative_V hc.coprime_card_K_card_V
  rwa [hc.inf_centralizer_eq_bot, bot_sup_eq] at h

theorem inf_N_eq_bot : V ⊓ N = ⊥ := by
  have hVn := hc.V_normal
  refine le_bot_iff.1 ?_
  rw [← hc.inf_centralizer_eq_bot]
  refine le_inf inf_le_left fun v hv => ?_
  have hvV : v ∈ V := (mem_inf.1 hv).1
  have hvN : v ∈ normalizer (K : Set G) := hc.N_le_normalizer_K (mem_inf.1 hv).2
  rw [mem_centralizer_iff]
  intro k hk
  have h1 : ⁅v, k⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem ((mem_normalizer_iff.1 hvN k).1 hk) (K.inv_mem hk)
  have h2 : ⁅v, k⁆ ∈ V := by
    have hx : k * v⁻¹ * k⁻¹ ∈ V := hVn.conj_mem _ (V.inv_mem hvV) k
    have hassoc : v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, hassoc]
    exact V.mul_mem hvV hx
  have hbot : ⁅v, k⁆ = 1 := by
    have hmem : ⁅v, k⁆ ∈ K ⊓ V := mem_inf.2 ⟨h1, h2⟩
    rw [hc.inf_K_V, Subgroup.mem_bot] at hmem
    exact hmem
  exact (commutatorElement_eq_one_iff_mul_comm.1 hbot).symm

theorem subgroupOf_V_eq : V.subgroupOf H = fittingRaw ↥H := by
  rw [hc.V_eq]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem exists_mulEquiv_quotient :
    ∃ e : ↥N ≃* (↥H ⧸ fittingRaw ↥H),
      ∀ n : ↥N, e n = QuotientGroup.mk (Subgroup.inclusion hc.N_le_H n) := by
  have hVn := hc.V_normal
  set f : ↥N →* (↥H ⧸ fittingRaw ↥H) :=
    (QuotientGroup.mk' (fittingRaw ↥H)).comp (Subgroup.inclusion hc.N_le_H) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← hc.subgroupOf_V_eq, Subgroup.mem_subgroupOf] at hx
    have hxVN : (x : G) ∈ V ⊓ N := mem_inf.2 ⟨hx, x.2⟩
    rw [hc.inf_N_eq_bot, Subgroup.mem_bot] at hxVN
    exact Subgroup.mem_bot.2 (Subtype.ext hxVN)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ y =>
      have hy : (y : G) ∈ V ⊔ N := hc.sup_V_N ▸ y.2
      have hy2 : (y : G) ∈ (V : Set G) * (N : Set G) := by
        rw [← Subgroup.normal_mul]; exact hy
      obtain ⟨v, hv, n, hn, hvn⟩ := hy2
      refine ⟨⟨n, hn⟩, ?_⟩
      rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        ← hc.subgroupOf_V_eq, Subgroup.mem_subgroupOf]
      have hmem : (n : G)⁻¹ * (y : G) ∈ V := by
        rw [← hvn]
        simpa [mul_assoc] using hVn.conj_mem v hv n⁻¹
      exact hmem
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem K_eq_map_subtype_fittingRaw_N : K = (fittingRaw ↥N).map N.subtype := by
  have hVn := hc.V_normal
  obtain ⟨e, he⟩ := hc.exists_mulEquiv_quotient
  have he' : ∀ n : ↥N, (e : ↥N →* (↥H ⧸ fittingRaw ↥H)) n
      = QuotientGroup.mk (Subgroup.inclusion hc.N_le_H n) := he
  have hKU : K ≤ U := hc.U_eq ▸ le_sup_right
  have hUVK : U ≤ V ⊔ K := hc.U_eq.le
  have hKimage : (K.subgroupOf N).map (e : ↥N →* (↥H ⧸ fittingRaw ↥H))
      = fittingRaw (↥H ⧸ fittingRaw ↥H) := by
    rw [← map_mk'_fittingRawPreimage ↥H, ← hc.U_subgroupOf_eq]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ y =>
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨n, hn, hnq⟩
        refine ⟨Subgroup.inclusion hc.N_le_H n, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.2 (hKU (Subgroup.mem_subgroupOf.1 hn))
        · rw [QuotientGroup.mk'_apply, ← he' n, hnq]
      · rintro ⟨z, hz, hzq⟩
        have hz2 : (z : G) ∈ (V : Set G) * (K : Set G) := by
          rw [← Subgroup.normal_mul]
          exact hUVK (Subgroup.mem_subgroupOf.1 hz)
        obtain ⟨v, hv, k, hk, hvk⟩ := hz2
        refine ⟨⟨k, hc.K_le_N hk⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
        rw [he']
        rw [QuotientGroup.mk'_apply] at hzq
        rw [← hzq, QuotientGroup.eq, ← hc.subgroupOf_V_eq, Subgroup.mem_subgroupOf]
        change (k : G)⁻¹ * (z : G) ∈ V
        rw [← hvk]
        simpa [mul_assoc] using hVn.conj_mem v hv k⁻¹
  have hfit : (fittingRaw ↥N).map (e : ↥N →* (↥H ⧸ fittingRaw ↥H))
      = fittingRaw (↥H ⧸ fittingRaw ↥H) := map_fittingRaw_of_mulEquiv e
  have hKN : K.subgroupOf N = fittingRaw ↥N :=
    Subgroup.map_injective e.injective (hKimage.trans hfit.symm)
  calc K = K ⊓ N := (inf_eq_left.2 hc.K_le_N).symm
    _ = (K.subgroupOf N).map N.subtype := (Subgroup.subgroupOf_map_subtype K N).symm
    _ = (fittingRaw ↥N).map N.subtype := by rw [hKN]

theorem inf_centralizer_le : H ⊓ centralizer (K : Set G) ≤ K := by
  have : Group.IsSolvable G := hc.isSolvable
  intro x hx
  have hxH : x ∈ H := (mem_inf.1 hx).1
  have hxC : x ∈ centralizer (K : Set G) := (mem_inf.1 hx).2
  have hxN : x ∈ N := by
    rw [hc.N_eq]
    exact mem_inf.2 ⟨Subgroup.centralizer_le_normalizer _ hxC, hxH⟩
  have hy : (⟨x, hxN⟩ : ↥N) ∈ centralizer ((fittingRaw ↥N : Subgroup ↥N) : Set ↥N) := by
    rw [mem_centralizer_iff]
    intro z hz
    have hzK : (z : G) ∈ K := by
      rw [hc.K_eq_map_subtype_fittingRaw_N]
      exact ⟨z, hz, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 hxC _ hzK)
  have hmem := centralizer_fittingRaw_le_fittingRaw ↥N hy
  have h2 : x ∈ (fittingRaw ↥N).map N.subtype := ⟨_, hmem, rfl⟩
  rwa [← hc.K_eq_map_subtype_fittingRaw_N] at h2

theorem primeCentralizerComplementSelfCentralizing :
    V ⊓ centralizer (K : Set G) = ⊥ ∧ V ⊓ N = ⊥ ∧ (⁅V, K⁆ : Subgroup G) = V ∧
      (∃ e : ↥N ≃* (↥H ⧸ fittingRaw ↥H),
        ∀ n : ↥N, e n = QuotientGroup.mk (Subgroup.inclusion hc.N_le_H n)) ∧
      K = (fittingRaw ↥N).map N.subtype ∧ H ⊓ centralizer (K : Set G) ≤ K :=
  ⟨hc.inf_centralizer_eq_bot, hc.inf_N_eq_bot, hc.commutator_eq, hc.exists_mulEquiv_quotient,
    hc.K_eq_map_subtype_fittingRaw_N, hc.inf_centralizer_le⟩

end IsPrimeCentralizerComplementSetup

end

end CFSG.FeitThompson

