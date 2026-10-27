module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34LocalA
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.U42.CoordsB

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34Loc

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement Matrix

section Sides

variable {G : Type} [Group G]

theorem comm_of_elemAb {Q : Subgroup G} (hQ : IsElemAbelian 2 Q) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b = b * a :=
  congrArg Subtype.val (hQ.1.is_comm.comm (⟨a, ha⟩ : ↥Q) ⟨b, hb⟩)

theorem le_normalizer_pCore (H : Subgroup G) : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf H)

theorem isElemAbelian_of_le {Q E : Subgroup G} (hQ : IsElemAbelian 2 Q) (hE : E ≤ Q) :
    IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_elemAb hQ (hE a.2) (hE b.2))⟩⟩, fun x hx => hQ.2 x (hE hx)⟩

theorem a5pre_self [Finite G] {L : Subgroup G} (hQe : IsElemAbelian 2 (pCoreOf 2 L))
    (hQc : Nat.card (pCoreOf 2 L) = 16) (hquot : IsL2Quot 2 (oTwoQuot ↥L))
    (hnt : ∃ l ∈ L, ∃ e ∈ pCoreOf 2 L, ⁅l, e⁆ ∉ (⊥ : Subgroup G)) :
    A5Pre L L (pCoreOf 2 L) ⊥ := by
  have hcent : pCoreOf 2 L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => comm_of_elemAb hQe hb ha
  refine
    { le := le_rfl
      norm_L := Subgroup.le_normalizer
      norm_E := le_normalizer_pCore L
      norm_K := fun g _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp
      sec := ⟨bot_le, ?_, fun e he => Subgroup.mem_bot.mpr (hQe.2 e he)⟩
      card := ?_
      core := fun q hq e he => Subgroup.mem_bot.mpr
        (commutatorElement_eq_one_iff_mul_comm.mpr (comm_of_elemAb hQe hq he))
      quot := hquot
      nontriv := hnt }
  · have : ⁅pCoreOf 2 L, pCoreOf 2 L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    exact this.le
  · rw [Subgroup.relIndex_bot_left, hQc]

theorem a5model_of_natSec [Finite G] {L : Subgroup G}
    (hQe : IsElemAbelian 2 (pCoreOf 2 L)) (hQc : Nat.card (pCoreOf 2 L) = 16)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hnat : NatSec L ⊥ (pCoreOf 2 L))
    (hnt : ∃ l ∈ L, ∃ e ∈ pCoreOf 2 L, ⁅l, e⁆ ∉ (⊥ : Subgroup G)) :
    Nonempty (A5Model L L (pCoreOf 2 L) ⊥ Certificates.A5GL42.HN) := by
  rcases A5Pre.exists_model' (a5pre_self hQe hQc hquot hnt) with ⟨_, hm⟩ | ⟨hn, _⟩
  · exact hm
  · exact absurd hnat hn

theorem nontriv_of_natSec [Finite G] {L : Subgroup G} (hnat : NatSec L ⊥ (pCoreOf 2 L))
    (hcard : Nat.card (pCoreOf 2 L) = 16) {x : G} (hxL : x ∈ L) (hx3 : orderOf x = 3) :
    ∃ l ∈ L, ∃ e ∈ pCoreOf 2 L, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
  by_contra hcon
  push_neg at hcon
  have hall : pCoreOf 2 L = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have hc : ⁅e, x⁆ ∈ (⊥ : Subgroup G) := by
      have h1 := hcon x hxL e he
      have h2 := (⊥ : Subgroup G).inv_mem h1
      rwa [← commutatorElement_inv, inv_inv] at h2
    exact hnat x hxL hx3 e he hc
  rw [hall, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem card_mul_le_of_inf_bot [Finite G] {C A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card C := by
  let f : ↥A × ↥B → ↥C := fun p => ⟨(p.1 : G) * (p.2 : G), C.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val h
    have hx : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * (a : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [hx]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have hae : (a : G) = a' := (inv_mul_eq_one.mp hmem).symm
    have hbe : (b : G) = b' := by
      have h2 : (a : G) * (b : G) = (a : G) * (b' : G) := by rw [h', hae]
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hae) (Subtype.ext hbe)
  have := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_prod] at this

theorem split_of_sylow [Finite G] {H T R' : Subgroup G} (hT : IsSylowTwoOf T H) (hT64 : Nat.card T = 64)
    (hQT : pCoreOf 2 H ≤ T) (hQe : IsElemAbelian 2 (pCoreOf 2 H)) (hQc : Nat.card (pCoreOf 2 H) = 16)
    (hR'T : R' ≤ T) (hR'e : IsElemAbelian 2 R') (hR'c : Nat.card R' = 16)
    (hE : Nat.card ↥(pCoreOf 2 H ⊓ R') = 4) :
    ∃ A : Subgroup G, A ≤ H ∧ A ⊓ pCoreOf 2 H = ⊥ ∧ pCoreOf 2 H ⊔ A = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K0, hK0R', hK0c, hK0E⟩ := exists_complement_four hR'e hR'c inf_le_right hE
  have hK0T : K0 ≤ T := hK0R'.trans hR'T
  have hinf : pCoreOf 2 H ⊓ K0 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxK⟩
    have hxE : x ∈ K0 ⊓ (pCoreOf 2 H ⊓ R') := ⟨hxK, ⟨hxR, hK0R' hxK⟩⟩
    rw [hK0E, Subgroup.mem_bot] at hxE
    exact Subgroup.mem_bot.mpr hxE
  have hdec := exists_mul_of_card_eq hQT hK0T hinf (by rw [hQc, hK0c, hT64])
  have hQH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQp : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  obtain ⟨A, hAH, hAV, hVA⟩ :=
    CFSG.GH74.QTGen4.U42.gaschutzSplitU hQH hQT hT.1 (fun h hh v hv => conj_mem_pCoreOf (Subgroup.le_normalizer hh) hv)
      hQp (fun a ha b hb => comm_of_elemAb hQe ha hb) hT.2.1 hT.2.2 hK0T hinf hdec
  exact ⟨A, hAH, hAV, hVA⟩

theorem card_inf_four [Finite G] {M M' T0 : Subgroup G} (hT64 : Nat.card T0 = 64)
    {x : G} (hxMM : x ∈ M ⊓ M') (hx3 : orderOf x = 3)
    (hQe : IsElemAbelian 2 (pCoreOf 2 M)) (hQc : Nat.card (pCoreOf 2 M) = 16)
    (hNat : NatSec M ⊥ (pCoreOf 2 M))
    (hQT : pCoreOf 2 M ≤ T0) (hQ'T : pCoreOf 2 M' ≤ T0) (hQ'c : Nat.card (pCoreOf 2 M') = 16)
    (hne : pCoreOf 2 M ≠ pCoreOf 2 M') :
    Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 M') = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxM : x ∈ M := hxMM.1
  have hxM' : x ∈ M' := hxMM.2
  have hxE : ∀ e ∈ pCoreOf 2 M ⊓ pCoreOf 2 M', x * e * x⁻¹ ∈ pCoreOf 2 M ⊓ pCoreOf 2 M' := fun e he =>
    ⟨conj_mem_pCoreOf (Subgroup.le_normalizer hxM) he.1, conj_mem_pCoreOf (Subgroup.le_normalizer hxM') he.2⟩
  have hEe : IsElemAbelian 2 (pCoreOf 2 M ⊓ pCoreOf 2 M') := isElemAbelian_of_le hQe inf_le_left
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hff : ∀ e ∈ pCoreOf 2 M ⊓ pCoreOf 2 M', x * e * x⁻¹ = e → e = 1 := by
    intro e he hfix
    have hcomm : ⁅e, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      calc e * x = (x * e * x⁻¹) * x := by rw [hfix]
        _ = x * e := by group
    have hb : ⁅e, x⁆ ∈ (⊥ : Subgroup G) := Subgroup.mem_bot.mpr hcomm
    exact Subgroup.mem_bot.mp (hNat x hxM hx3 e he.1 hb)
  have hmod := card_modEq_one_of_fixedPointFree hEe hx3' hxE hff
  have hdvd : Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 M') ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hQc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hEi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hER : pCoreOf 2 M ⊓ pCoreOf 2 M' ≠ pCoreOf 2 M := by
    intro h
    have hRR' : pCoreOf 2 M ≤ pCoreOf 2 M' := fun r hr => by
      have hr' : r ∈ pCoreOf 2 M ⊓ pCoreOf 2 M' := by rw [h]; exact hr
      exact hr'.2
    exact hne (Subgroup.eq_of_le_of_card_ge hRR' (by rw [hQc, hQ'c]))
  have hEq16 : Nat.card ↥(pCoreOf 2 M ⊓ pCoreOf 2 M') ≠ 16 := by
    intro h
    exact hER (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hQc]))
  interval_cases i
  · exfalso
    have h1 : pCoreOf 2 M ⊓ pCoreOf 2 M' = ⊥ := Subgroup.card_eq_one.mp (by simpa using hEi)
    have := card_mul_le_of_inf_bot hQT hQ'T h1
    rw [hQc, hQ'c, hT64] at this
    norm_num at this
  · exfalso
    rw [hEi] at hmod
    norm_num [Nat.ModEq] at hmod
  · rw [hEi]; norm_num
  · exfalso
    rw [hEi] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact absurd (by rw [hEi]; norm_num) hEq16

theorem glMat_mul' (g h : GL (Fin 4) (ZMod 2)) : glMat (g * h) = glMat g * glMat h := Units.val_mul g h

theorem glMat_one' : glMat (1 : GL (Fin 4) (ZMod 2)) = 1 := Units.val_one

theorem alpha_beta {Y : Type} [Group Y] [Finite G] {L K : Subgroup G} {M K' : Subgroup Y}
    (hKL : K ≤ L) (hK'M : K' ≤ M)
    (hKQ : K ⊓ pCoreOf 2 L = ⊥) (hK'R : K' ⊓ pCoreOf 2 M = ⊥)
    (hdecL : ∀ x ∈ L, ∃ q ∈ pCoreOf 2 L, ∃ k ∈ K, q * k = x)
    (hdecM : ∀ y ∈ M, ∃ r ∈ pCoreOf 2 M, ∃ k ∈ K', r * k = y)
    (AL : A5Model L L (pCoreOf 2 L) ⊥ Certificates.A5GL42.HN)
    (AM : A5Model M M (pCoreOf 2 M) ⊥ Certificates.A5GL42.HN) :
    ∃ (β : ↥(pCoreOf 2 L) ≃* ↥(pCoreOf 2 M)) (α : ↥K ≃* ↥K'),
      ∀ (k : ↥K) (q q' : ↥(pCoreOf 2 L)), (q' : G) = (k : G) * (q : G) * (k : G)⁻¹ →
        (β q' : Y) = (α k : Y) * (β q : Y) * (α k : Y)⁻¹ := by
  classical
  let FL := AL.F
  let FM := AM.F
  let iL : ↥K →* ↥L := Subgroup.inclusion hKL
  let iM : ↥K' →* ↥M := Subgroup.inclusion hK'M
  have exM : ∀ k : ↥K, ∃ k' : ↥K', glMat (FM.M (iM k')) = glMat (FL.M (iL k)) := by
    intro k
    obtain ⟨l, hlM, hl⟩ := AM.surjL _ (AL.imgL (iL k) (iL k).2)
    obtain ⟨r, hr, k', hk', hrk⟩ := hdecM (l : Y) hlM
    let rM : ↥M := ⟨r, CFSG.LieType.BorelTits.pCoreOf_le 2 M hr⟩
    let k'M : ↥M := iM ⟨k', hk'⟩
    have hlfac : l = rM * k'M := Subtype.ext (by
      rw [Subgroup.coe_mul]
      exact hrk.symm)
    have hcomp : FM.M l = FM.M k'M := by
      rw [hlfac, map_mul, AM.core rM hr, one_mul]
    exact ⟨⟨k', hk'⟩, by rw [← hcomp]; exact hl⟩
  have exL : ∀ k' : ↥K', ∃ k : ↥K, glMat (FL.M (iL k)) = glMat (FM.M (iM k')) := by
    intro k'
    obtain ⟨l, hlL, hl⟩ := AL.surjL _ (AM.imgL (iM k') (iM k').2)
    obtain ⟨q, hq, k, hk, hqk⟩ := hdecL (l : G) hlL
    let qL : ↥L := ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 L hq⟩
    let kL : ↥L := iL ⟨k, hk⟩
    have hlfac : l = qL * kL := Subtype.ext (by
      rw [Subgroup.coe_mul]
      exact hqk.symm)
    have hcomp : FL.M l = FL.M kL := by
      rw [hlfac, map_mul, AL.core qL hq, one_mul]
    exact ⟨⟨k, hk⟩, by rw [← hcomp]; exact hl⟩
  have uniqM : ∀ a b : ↥K', glMat (FM.M (iM a)) = glMat (FM.M (iM b)) → a = b := by
    intro a b h
    have h1 : FM.M (iM a) = FM.M (iM b) := Units.ext h
    have h2 : FM.M (iM a * (iM b)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : ((iM a * (iM b)⁻¹ : ↥M) : Y) ∈ pCoreOf 2 M := (AM.kerL _ (iM a * (iM b)⁻¹).2).mp h2
    have h4 : (a : Y) * (b : Y)⁻¹ ∈ K' ⊓ pCoreOf 2 M :=
      ⟨K'.mul_mem a.2 (K'.inv_mem b.2), h3⟩
    rw [hK'R, Subgroup.mem_bot] at h4
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  choose f hf using exM
  let fhom : ↥K →* ↥K' :=
    { toFun := f
      map_one' := by
        apply uniqM
        rw [hf 1]
        simp only [map_one, glMat_one']
      map_mul' := fun k₁ k₂ => by
        apply uniqM
        have e1 : glMat (FM.M (iM (f (k₁ * k₂)))) = glMat (FL.M (iL (k₁ * k₂))) := hf _
        have e2 : glMat (FM.M (iM (f k₁ * f k₂))) =
            glMat (FM.M (iM (f k₁))) * glMat (FM.M (iM (f k₂))) := by
          rw [map_mul, map_mul, glMat_mul']
        rw [e1, e2, hf k₁, hf k₂, map_mul iL, map_mul FL.M, glMat_mul'] }
  have hinjf : Function.Injective fhom := by
    rw [injective_iff_map_eq_one fhom]
    intro k hk
    have hk1 : f k = 1 := hk
    have h1 : glMat (FL.M (iL k)) = 1 := by
      rw [← hf k, hk1]
      simp only [map_one, glMat_one']
    have h2 : FL.M (iL k) = 1 := Units.ext h1
    have h3 : ((iL k : ↥L) : G) ∈ pCoreOf 2 L := (AL.kerL _ (iL k).2).mp h2
    have h4 : (k : G) ∈ K ⊓ pCoreOf 2 L := ⟨k.2, h3⟩
    rw [hKQ, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hsurjf : Function.Surjective fhom := by
    intro k'
    obtain ⟨k, hk⟩ := exL k'
    exact ⟨k, uniqM _ _ ((hf k).trans hk)⟩
  let α : ↥K ≃* ↥K' := MulEquiv.ofBijective fhom ⟨hinjf, hsurjf⟩
  have hφL_inj : Function.Injective FL.φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h := (FL.ker q).mp hq
    exact Subtype.ext (Subgroup.mem_bot.mp h)
  have hφM_inj : Function.Injective FM.φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h := (FM.ker q).mp hq
    exact Subtype.ext (Subgroup.mem_bot.mp h)
  let bL : ↥(pCoreOf 2 L) ≃* Multiplicative (Fin 4 → ZMod 2) := MulEquiv.ofBijective FL.φ ⟨hφL_inj, FL.surj⟩
  let bM : ↥(pCoreOf 2 M) ≃* Multiplicative (Fin 4 → ZMod 2) := MulEquiv.ofBijective FM.φ ⟨hφM_inj, FM.surj⟩
  let β : ↥(pCoreOf 2 L) ≃* ↥(pCoreOf 2 M) := bL.trans bM.symm
  have hβ : ∀ q : ↥(pCoreOf 2 L), FM.φ (β q) = FL.φ q := fun q => by
    show FM.φ (bM.symm (bL q)) = FL.φ q
    exact bM.apply_symm_apply _
  refine ⟨β, α, ?_⟩
  intro k q q' hq'
  have A1 := FL.act (iL k) q q' hq'
  let e2 : ↥(pCoreOf 2 M) := ⟨(f k : Y) * (β q : Y) * (f k : Y)⁻¹,
    conj_mem_pCoreOf (Subgroup.le_normalizer (hK'M (f k).2)) (β q).2⟩
  have A2 := FM.act (iM (f k)) (β q) e2 rfl
  have key : Multiplicative.toAdd (FM.φ (β q')) = Multiplicative.toAdd (FM.φ e2) := by
    calc Multiplicative.toAdd (FM.φ (β q')) = Multiplicative.toAdd (FL.φ q') := by rw [hβ q']
      _ = glMat (FL.M (iL k)) *ᵥ Multiplicative.toAdd (FL.φ q) := A1.symm
      _ = glMat (FM.M (iM (f k))) *ᵥ Multiplicative.toAdd (FM.φ (β q)) := by rw [hf k, hβ q]
      _ = Multiplicative.toAdd (FM.φ e2) := A2
  have hEq : β q' = e2 := hφM_inj (Multiplicative.toAdd.injective key)
  rw [hEq]
  rfl


end Sides

end CFSG.GH74.QTGen4.DSGen4.L34Loc
