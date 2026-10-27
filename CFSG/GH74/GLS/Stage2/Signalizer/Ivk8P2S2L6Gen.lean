module

public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.ComponentClassification.UnbalancedLayer (pComponent_eq_of_map_eq)
open CFSG.LocalAnalysis.ComponentInitial (isPComponent_two_of_isComponent)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (le_normalizer_of_commute)
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_eq_map_O22Res)

section Generic

variable {X : Type} [Group X] [Finite X]

theorem isComponent_map_pPrimeCore {J : Subgroup X} (hJ : IsComponent J) :
    IsComponent (J.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  obtain ⟨K, hK, -, hmap, -⟩ := isPComponent_two_of_isComponent hJ
  rw [hmap]
  exact hK

theorem eq_of_isComponent_of_map_eq {J J' : Subgroup X} (hJ : IsComponent J)
    (hJ' : IsComponent J')
    (h : J.map (QuotientGroup.mk' (pPrimeCore 2 X)) = J'.map (QuotientGroup.mk' (pPrimeCore 2 X))) :
    J = J' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pComponent_eq_of_map_eq (isPComponent_two_of_isComponent hJ)
    (isPComponent_two_of_isComponent hJ') h

omit [Finite X] in
theorem exists_isComponent_of_layer_ne_bot (h : layer X ≠ ⊥) : ∃ J : Subgroup X, IsComponent J := by
  by_contra hno
  push Not at hno
  apply h
  have : {K : Subgroup X | IsComponent K} = ∅ := Set.eq_empty_iff_forall_notMem.2 hno
  simp only [CFSG.layer.eq_sSup]
  rw [this, sSup_empty]

omit [Finite X] in
theorem layer_eq_of_forall_eq {J : Subgroup X} (hJ : IsComponent J)
    (hu : ∀ J' : Subgroup X, IsComponent J' → J' = J) : layer X = J := by
  have : {K : Subgroup X | IsComponent K} = {J} :=
    Set.ext fun K => ⟨fun h => hu K h, fun h => by rw [Set.mem_singleton_iff.1 h]; exact hJ⟩
  simp only [CFSG.layer.eq_sSup]
  rw [this, sSup_singleton]

theorem pLayer_eq_layer_of_images
    (h : ∀ K : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent K →
      ∃ J : Subgroup X, IsComponent J ∧ J.map (QuotientGroup.mk' (pPrimeCore 2 X)) = K) :
    pLayer X 2 = layer X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (sSup_le fun L hL => ?_) layer_le_pLayer
  obtain ⟨K, hK, -, hmap, -⟩ := id hL
  obtain ⟨J, hJ, hJK⟩ := h K hK
  have hLJ : L = J :=
    pComponent_eq_of_map_eq hL (isPComponent_two_of_isComponent hJ) (hmap.trans hJK.symm)
  rw [hLJ]
  exact le_sSup hJ

theorem eq_of_mk_eq_of_commute {a b : X} (hab : Commute a b) {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hb : b ^ (2 ^ k) = 1)
    (h : QuotientGroup.mk' (pPrimeCore 2 X) a = QuotientGroup.mk' (pPrimeCore 2 X) b) : a = b := by
  have hd : a⁻¹ * b ∈ pPrimeCore 2 X := QuotientGroup.eq.1 h
  have hodd : (orderOf (a⁻¹ * b)).Coprime 2 := coprime_orderOf_of_mem_pPrimeCore hd
  have h1 : (a⁻¹ * b) ^ (2 ^ k) = 1 := by
    rw [(hab.inv_left).mul_pow, inv_pow, ha, hb]
    simp
  have h2 : orderOf (a⁻¹ * b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (a⁻¹ * b) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd) h2
  exact inv_mul_eq_one.1 (orderOf_eq_one_iff.1 h3)

end Generic

section Cen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zBar_central (z : G) (g : CentralizerBar z) : g * zBar z = zBar z * g := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
  show QuotientGroup.mk (c * zElt z) = QuotientGroup.mk (zElt z * c)
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)

theorem zBar_ne_one {z : G} (hz : orderOf z = 2) : zBar z ≠ 1 := by
  intro h
  have hmem : zElt z ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h
  have hcop := coprime_orderOf_of_mem_pPrimeCore hmem
  have : orderOf (zElt z) = 2 := by
    rw [← hz, ← Subgroup.orderOf_coe]
    rfl
  rw [this] at hcop
  exact absurd hcop (by decide)

theorem zBar_mem_generalizedFitting (z : G) : zBar z ∈ generalizedFitting (CentralizerBar z) :=
  centralizer_generalizedFitting_le (CentralizerBar z) (by
    rw [mem_centralizer_iff]
    intro h _
    exact zBar_central z h)

omit [Finite G] in
theorem zBar_mem_barOf (z : G) : zBar z ∈ barOf z (zpowers z) :=
  ⟨zElt z, mem_subgroupOf.2 (mem_zpowers z), rfl⟩

theorem mem_zpowers_of_toBar_mem {z : G} (hz : orderOf z = 2) {s : G} (hs : s ∈ Cen z)
    (h2 : ∃ k : ℕ, s ^ (2 ^ k) = 1) (hb : toBar z ⟨s, hs⟩ ∈ barOf z (zpowers z)) :
    s ∈ zpowers z := by
  obtain ⟨k, hk⟩ := h2
  obtain ⟨y, hy, hyb⟩ := hb
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (mem_subgroupOf.1 hy)
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hy2 : (y : G) ^ 2 = 1 := by
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hyk : (y : G) ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, hy2, one_pow]
  have hsk : s ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, hk, one_pow]
  have hcomm : Commute (y : G) s := by
    rw [← hn]
    exact Commute.zpow_left (mem_centralizer_singleton_iff.1 hs).symm n
  have heq : y = ⟨s, hs⟩ := by
    refine eq_of_mk_eq_of_commute (k := k + 1) ?_ ?_ ?_ hyb
    · exact Subtype.ext hcomm.eq
    · exact Subtype.ext hyk
    · exact Subtype.ext hsk
  have hys : (y : G) = s := congrArg Subtype.val heq
  rw [← hys, ← hn]
  exact zpow_mem_zpowers z n

theorem thm4c_of_WBar_le {z : G} {S : Subgroup G} (hz : orderOf z = 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hW : WBar z ≤ barOf z (zpowers z)) :
    Thm4c z (Cen z) := by
  intro _
  refine isInternalDirectProduct_of_sylow_of_centralizes hS ?_
  intro s hs f hf
  obtain ⟨hsS, w, hw, hws⟩ := hs
  obtain ⟨f', -, rfl⟩ := hf
  have hwb : toBar z w ∈ barOf z (zpowers z) := by
    apply hW
    rw [WBar_eq_map_O22Res]
    exact mem_map_of_mem _ hw
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hsS⟩
  have h2 : ∃ k : ℕ, s ^ (2 ^ k) = 1 := ⟨k, congrArg Subtype.val hk⟩
  have hsC : s ∈ Cen z := by
    rw [← hws]
    exact w.2
  have hs' : s ∈ zpowers z := by
    refine mem_zpowers_of_toBar_mem hz hsC h2 ?_
    have : (⟨s, hsC⟩ : ↥(Cen z)) = w := Subtype.ext hws.symm
    rw [this]
    exact hwb
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs'
  exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 f'.2).symm n).eq

theorem thm4Concl_of_images {z : G} {k : Kind} {S : Subgroup G} (hz : orderOf z = 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z))
    (hI : ∀ K : Subgroup (CentralizerBar z), IsComponent K →
      ∃ J : Subgroup ↥(Cen z), IsComponent J ∧ J.map (toBar z) = K)
    (hW : WBar z ≤ barOf z (zpowers z)) : Thm4Concl z k S (Cen z) := by
  refine ⟨?_, fun h => absurd h (lt_irrefl _), thm4c_of_WBar_le hz hS hW⟩
  show pLayerOf 2 (Cen z) = Em (Cen z)
  rw [pLayerOf_eq_map, Em_eq, pLayer_eq_layer_of_images hI]

end Cen

section SL2Pair

variable {Y : Type} [Group Y]

theorem mem_zpowers_of_card_two {H : Subgroup Y} (hH : Nat.card ↥H = 2) {x w : Y} (hx : x ∈ H)
    (hx1 : x ≠ 1) (hw : w ∈ H) : w ∈ zpowers x := by
  have hfin : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hord : orderOf x = 2 := by
    have h1 : orderOf (⟨x, hx⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hH] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hle : zpowers x ≤ H := zpowers_le.2 hx
  have hcard : Nat.card ↥(zpowers x) = 2 := by rw [Nat.card_zpowers, hord]
  have heq : zpowers x = H := Subgroup.eq_of_le_of_card_ge hle (by rw [hH, hcard])
  rw [heq]
  exact hw

theorem central_le_inf {A B : Subgroup Y} {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (hA : HasSL2Model ↥A (fun r => r = a)) (hB : HasSL2Model ↥B (fun r => r = b))
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hI : Nat.card ↥(A ⊓ B) = 2)
    {x : Y} (hx : x ∈ A ⊔ B) (hxc : ∀ y ∈ A ⊔ B, y * x = x * y) : x ∈ A ⊓ B := by
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
  have hZA := (sl2_model_center_inv ha hA).1
  have hZB := (sl2_model_center_inv hb hB).1
  have hcomm' : ∀ x ∈ B, ∀ y ∈ A, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hca : ∀ c ∈ A, c * a₀ = a₀ * c := by
    intro c hc
    have h1 := hxc c (mem_sup_left hc)
    have h2 : c * a₀ * b₀ = a₀ * c * b₀ := by
      calc c * a₀ * b₀ = c * (a₀ * b₀) := by rw [mul_assoc]
        _ = a₀ * b₀ * c := h1
        _ = a₀ * (b₀ * c) := by rw [mul_assoc]
        _ = a₀ * (c * b₀) := by rw [hcomm c hc b₀ hb₀]
        _ = a₀ * c * b₀ := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hcb : ∀ c ∈ B, c * b₀ = b₀ * c := by
    intro c hc
    have h1 := hxc c (mem_sup_right hc)
    have h2 : a₀ * (c * b₀) = a₀ * (b₀ * c) := by
      calc a₀ * (c * b₀) = (a₀ * c) * b₀ := by rw [mul_assoc]
        _ = (c * a₀) * b₀ := by rw [hcomm' c hc a₀ ha₀]
        _ = c * (a₀ * b₀) := by rw [mul_assoc]
        _ = a₀ * b₀ * c := h1
        _ = a₀ * (b₀ * c) := by rw [mul_assoc]
    exact mul_left_cancel h2
  have ha_mem : a₀ ∈ B := central_mem_of_card_inf hcomm hZA hI ha₀ hca
  have hb_mem : b₀ ∈ A := central_mem_of_card_inf hcomm' hZB (by rwa [inf_comm]) hb₀ hcb
  exact mul_mem (Subgroup.mem_inf.2 ⟨ha₀, ha_mem⟩) (Subgroup.mem_inf.2 ⟨hb_mem, hb₀⟩)

theorem isSubnormal_of_commute {A B T : Subgroup Y} (hT : T.Normal) (hAB : A ⊔ B = T)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A.IsSubnormal := by
  have hAT : A ≤ T := hAB ▸ le_sup_left
  refine Subgroup.IsSubnormal.step A T hAT hT.isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAT]
  rw [← hAB]
  exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm)

end SL2Pair

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
