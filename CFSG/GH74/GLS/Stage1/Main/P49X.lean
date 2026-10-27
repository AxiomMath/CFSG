module

public import CFSG.GH74.GLS.Stage1.Main.P49XA
public import CFSG.GH74.GLS.Stage1.Main.P49Bar

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement Pointwise

section XE

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y u₁ u₂ : G}

omit [Finite G] in
theorem quat_central49 {Q Q₀ : Subgroup G} {n : ℕ} (hQ : IVK.IsQuaternionTwoGroup ↥Q n)
    (hle : Q₀ ≤ Q) (hnc : ¬ IsCyclic ↥Q₀) {c : G} (hcQ : c ∈ Q) (hc : ∀ x ∈ Q₀, c * x = x * c) :
    c * c = 1 := by
  obtain ⟨hn3, ⟨e⟩⟩ := hQ
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  let Q₀A : Subgroup ↥Q := Q₀.subgroupOf Q
  have hnc' : ¬ IsCyclic ↥(Q₀A.map e.toMonoidHom) := by
    intro hcyc
    apply hnc
    let f : ↥Q₀ →* ↥(Q₀A.map e.toMonoidHom) :=
      ((Subgroup.equivMapOfInjective Q₀A e.toMonoidHom e.injective).toMonoidHom).comp
        (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
    exact isCyclic_of_injective f (by
      exact (Subgroup.equivMapOfInjective Q₀A e.toMonoidHom e.injective).injective.comp
        (Subgroup.subgroupOfEquivOfLe hle).symm.injective)
  have key := quatModel_central49 (Q₀A.map e.toMonoidHom) hnc' (c := e ⟨c, hcQ⟩) (by
    rintro _ ⟨a, ha, rfl⟩
    show e ⟨c, hcQ⟩ * e a = e a * e ⟨c, hcQ⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc a ha))
  rw [← map_mul] at key
  have := e.injective (key.trans (map_one e).symm)
  simpa using congrArg Subtype.val this


theorem central_Y_49 (hc : Closed49) (h : Ctx49 G z S K F U x y)
    (c : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂)
    {Q₀ : Subgroup G} (hQ₀ : Q₀ ≤ S ⊓ cSec K) (hnc : ¬ IsCyclic ↥Q₀) {r : G}
    (hr : r ∈ (S ⊓ cSec K) ⊔ zpowers y) (hcomm : ∀ x ∈ Q₀, r * x = x * r) : r = 1 ∨ r = z := by
  have hz2 := c.hz2
  have hz1 := c.hz1
  have hy2 := y_sq_one49 h
  obtain ⟨hyQ, hysd⟩ := y_data49 h
  have hnorm : ∀ p ∈ S ⊓ cSec K, y * p * y⁻¹ ∈ S ⊓ cSec K := fun p hp => c.cfg.Q_norm y h.y_S p hp
  have hsdf := hc.hsd G (S ⊓ cSec K) z y c.quatQ c.cfg.z_Q hz2 hz1 hy2 hyQ hnorm hysd
  by_cases hrQ : r ∈ S ⊓ cSec K
  · have := quat_central49 c.quatQ.choose_spec hQ₀ hnc hrQ hcomm
    exact c.Q_inv r hrQ this
  · exfalso
    obtain ⟨q, hq, hrq⟩ := (mem_sup_zpowers_inv49 hy2 hnorm hr).resolve_left hrQ
    have hrr : r * r = q * (y * q * y⁻¹) := by
      rw [hrq]
      calc q * y * (q * y) = q * (y * q * y⁻¹) * (y * y) := by group
        _ = q * (y * q * y⁻¹) := by rw [hy2, mul_one]
    have hrrQ : r * r ∈ S ⊓ cSec K := by rw [hrr]; exact mul_mem hq (hnorm q hq)
    by_cases hr1 : r * r = 1
    · obtain ⟨p', hp', hp'eq⟩ := hsdf.2 q hq (by rw [← hrq]; exact hr1)
      have hQz : Q₀ ≤ zpowers z := by
        intro x hx
        have e1 : (p'⁻¹ * y * p') * x = x * (p'⁻¹ * y * p') := by
          rw [hp'eq, ← hrq]
          exact hcomm x hx
        have e2 : y * (p' * x * p'⁻¹) = (p' * x * p'⁻¹) * y := by
          calc y * (p' * x * p'⁻¹) = p' * ((p'⁻¹ * y * p') * x) * p'⁻¹ := by group
            _ = p' * (x * (p'⁻¹ * y * p')) * p'⁻¹ := by rw [e1]
            _ = (p' * x * p'⁻¹) * y := by group
        have hxQ : x ∈ S ⊓ cSec K := hQ₀ hx
        have hmem : p' * x * p'⁻¹ ∈ S ⊓ cSec K := mul_mem (mul_mem hp' hxQ) (inv_mem hp')
        have hpz : p'⁻¹ * z * p' = z := by
          calc p'⁻¹ * z * p' = p'⁻¹ * (z * p') := by group
            _ = p'⁻¹ * (p' * z) := by rw [← c.z_comm hp'.1]
            _ = z := by group
        rcases hsdf.1 _ hmem e2 with e | e
        · have : x = 1 := by
            calc x = p'⁻¹ * (p' * x * p'⁻¹) * p' := by group
              _ = 1 := by rw [e]; group
          rw [this]; exact one_mem _
        · have : x = z := by
            calc x = p'⁻¹ * (p' * x * p'⁻¹) * p' := by group
              _ = z := by rw [e, hpz]
          rw [this]; exact Subgroup.mem_zpowers z
      exact hnc (isCyclic_of_injective (Subgroup.inclusion hQz) (Subgroup.inclusion_injective hQz))
    · have hsq : (r * r) * (r * r) = 1 :=
        quat_central49 c.quatQ.choose_spec hQ₀ hnc hrrQ (fun x hx => by
          calc (r * r) * x = r * (r * x) := by group
            _ = r * (x * r) := by rw [hcomm x hx]
            _ = (r * x) * r := by group
            _ = (x * r) * r := by rw [hcomm x hx]
            _ = x * (r * r) := by group)
      rcases c.Q_inv (r * r) hrrQ hsq with e | e
      · exact hr1 e
      · exact hc.hsdq G (S ⊓ cSec K) z y c.quatQ c.cfg.z_Q hz2 hz1 hy2 hyQ hnorm hysd q hq
          (by rw [← hrq]; exact e)


omit [Finite G] in
theorem eq_one_of_mem_S_odd49 {S N : Subgroup G} (hS : IsPGroup 2 ↥S) (hN : Odd (Nat.card ↥N)) {g : G}
    (hgS : g ∈ S) (hgN : g ∈ N) : g = 1 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨g, hgS⟩
  have hm' : orderOf g = 2 ^ m := (Subgroup.orderOf_coe (⟨g, hgS⟩ : ↥S)).trans hm
  have hdvd : orderOf g ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hgN
  have hcop : Nat.Coprime (2 ^ m) (Nat.card ↥N) := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hN)
  rw [hm'] at hdvd
  have h1 : 2 ^ m = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [← orderOf_eq_one_iff, hm', h1]

theorem centralizer_S_le_P49 (hc : Closed49) (h : Ctx49 G z S K F U x y)
    (c : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂)
    {Q₀ : Subgroup G} (hQ₀ : Q₀ ≤ S ⊓ cSec K) (hnc : ¬ IsCyclic ↥Q₀) {s : G} (hsS : s ∈ S)
    (hcomm : ∀ x ∈ Q₀, s * x = x * s) : s ∈ S ⊓ K := by
  have hPQ := c.cfg.PQ_comm
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  have hzP : z ∈ S ⊓ K := c.cfg.z_P
  have hy2 := y_sq_one49 h
  obtain ⟨hyQ, -⟩ := y_data49 h
  by_cases hsR : s ∈ Rz S z
  · obtain ⟨p, hp, q, hq, rfl⟩ := M.mem_sup_of_commute hPQ (hRz ▸ hsR)
    have hqc : ∀ x ∈ Q₀, q * x = x * q := by
      intro x hx
      have hpx : p * x = x * p := hPQ p hp x (hQ₀ hx)
      calc q * x = p⁻¹ * (p * q * x) := by group
        _ = p⁻¹ * (x * (p * q)) := by rw [hcomm x hx]
        _ = p⁻¹ * (x * p) * q := by group
        _ = p⁻¹ * (p * x) * q := by rw [hpx]
        _ = x * q := by group
    have hqY : q ∈ (S ⊓ cSec K) ⊔ zpowers y := Subgroup.mem_sup_left hq
    rcases central_Y_49 hc h c hQ₀ hnc hqY hqc with e | e
    · rw [e, mul_one]; exact hp
    · rw [e]; exact mul_mem hp hzP
  · exfalso
    have hidx : ((Rz S z).subgroupOf S).index = 2 := h.idx
    have hr : s * y⁻¹ ∈ Rz S z := by
      have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨s, hsS⟩)
        (b := ⟨y⁻¹, S.inv_mem h.y_S⟩)).2 (by
          simp only [Subgroup.mem_subgroupOf]
          exact iff_of_false hsR (fun hh => h.y_R (by simpa using inv_mem hh)))
      simpa [Subgroup.mem_subgroupOf] using key
    obtain ⟨p, hp, q, hq, hpq⟩ := M.mem_sup_of_commute hPQ (hRz ▸ hr)
    have hsq : s = p * (q * y) := by
      calc s = (s * y⁻¹) * y := by group
        _ = (p * q) * y := by rw [hpq]
        _ = p * (q * y) := by group
    have hqyY : q * y ∈ (S ⊓ cSec K) ⊔ zpowers y :=
      mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    have hqc : ∀ x ∈ Q₀, (q * y) * x = x * (q * y) := by
      intro x hx
      have hpx : p * x = x * p := hPQ p hp x (hQ₀ hx)
      have h1 := hcomm x hx
      rw [hsq] at h1
      calc (q * y) * x = p⁻¹ * (p * (q * y) * x) := by group
        _ = p⁻¹ * (x * (p * (q * y))) := by rw [h1]
        _ = p⁻¹ * (x * p) * (q * y) := by group
        _ = p⁻¹ * (p * x) * (q * y) := by rw [hpx]
        _ = x * (q * y) := by group
    have hmemQ : q * y ∈ S ⊓ cSec K := by
      rcases central_Y_49 hc h c hQ₀ hnc hqyY hqc with e | e
      · rw [e]; exact one_mem _
      · rw [e]; exact c.cfg.z_Q
    apply hyQ
    have : y = q⁻¹ * (q * y) := by group
    rw [this]
    exact mul_mem (inv_mem hq) hmemQ


theorem inf_not_cyclic49 (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cz z)) {L : Subgroup G}
    (hL : IsPCompIn 2 (Cz z) L) : ¬ IsCyclic ↥(S ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  have hSyl' := isSylowOf_inf_isPCompIn49 hSyl hL
  obtain ⟨PL, hPL⟩ := hSyl'.exists_sylow_eq_subgroupOf
  have hq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := TwoThin.isQuasisimple_hat hL
  have hsurj : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hPLcyc : IsCyclic ↥(PL : Subgroup ↥L) := by
    rw [hPL]
    exact ((Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).isCyclic).2 hcyc
  have hcyc' : IsCyclic ↥((PL.mapSurjective hsurj : Sylow 2 (↥L ⧸ pPrimeCore 2 ↥L)) :
      Subgroup (↥L ⧸ pPrimeCore 2 ↥L)) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective
      ((QuotientGroup.mk' (pPrimeCore 2 ↥L)).subgroupMap (PL : Subgroup ↥L))
      (MonoidHom.subgroupMap_surjective _ _)
  exact not_isCyclic_sylow_quasisimple49 hq _ hcyc'


omit [Finite G] in
theorem map_conj_Cz49 {g : G} (hg : g ∈ Cz z) : (Cz z).map (MulAut.conj g).toMonoidHom = Cz z := by
  rw [map_centralizer_singleton_conj z g]
  have h1 : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hg
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
      _ = z := by group
  rw [h1]

theorem invol_CxK_eq_z49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {L : Subgroup G}
    (hL : IsPCompIn 2 (Cz z) L) (hne : L ≠ K) :
    ∀ t ∈ Cz z ⊓ cSec L, orderOf t = 2 → t = z := by
  intro t ht ht2
  obtain ⟨u₁, u₂, c9⟩ := setup9_of_ctx49 hc h
  have hK : IsPCompIn 2 (Cz z) K := h.std.comp_isPCompIn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cz z) := h.std.sylow
  have hSC : S ≤ Cz z := hSyl.le
  have hS2 : IsPGroup 2 ↥S := hSyl.isPGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by
    have : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    rwa [sq] at this
  have ht1 : t ≠ 1 := by
    intro e
    rw [e, orderOf_one] at ht2
    omega
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  let tA : ↥(Cz z) := ⟨t, ht.1⟩
  have htA : IsPGroup 2 ↥(zpowers tA) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : orderOf tA = 2 := by
      rw [← Subgroup.orderOf_coe]; exact ht2
    exact this
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow49 Q htA
  have hts : (g : G)⁻¹ * t * g ∈ S := by
    have h1 := hg tA (Subgroup.mem_zpowers tA)
    rw [hQ] at h1
    exact h1
  set c : G := (g : G) with hcdef
  have hcC : c ∈ Cz z := g.2
  have hL' : IsPCompIn 2 (Cz z) (cj c⁻¹ L) := by
    have h1 := isPCompIn_map_conj hL c⁻¹
    rwa [map_conj_Cz49 (inv_mem hcC)] at h1
  have hne' : cj c⁻¹ L ≠ K := by
    intro e
    apply hne
    have h1 : cj c (cj c⁻¹ L) = L := cj_cancel c L
    rw [e] at h1
    rw [← h1]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.1 (h.std.toStd6r1.normalizes_K hcC))
  have ht' : c⁻¹ * t * c ∈ cSec (cj c⁻¹ L) := by
    have := mem_cSec_cj ht.2 c⁻¹
    simpa using this
  have hQ₀ : S ⊓ cj c⁻¹ L ≤ S ⊓ cSec K := fun w hw =>
    ⟨hw.1, le_cSec_of_ne hL' hK hne' hw.2⟩
  have hnc := inf_not_cyclic49 hSyl hL'
  have hcomm : ∀ x ∈ S ⊓ cj c⁻¹ L, (c⁻¹ * t * c) * x = x * (c⁻¹ * t * c) := by
    intro x hx
    have h1 : ⁅x, c⁻¹ * t * c⁆ ∈ pPrimeCoreOf 2 (cj c⁻¹ L) := ht'.2.2 x hx.2
    have h2 : ⁅x, c⁻¹ * t * c⁆ ∈ S := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx.1 hts) (inv_mem hx.1)) (inv_mem hts)
    have h3 := eq_one_of_mem_S_odd49 hS2 (TwoThin.card_pPrimeCoreOf_odd (cj c⁻¹ L)) h2 h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  have hP := centralizer_S_le_P49 hc h c9 hQ₀ hnc hts hcomm
  have ht'sq : (c⁻¹ * t * c) * (c⁻¹ * t * c) = 1 := by
    calc (c⁻¹ * t * c) * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c := by group
      _ = 1 := by rw [htt]; group
  have ht'1 : c⁻¹ * t * c ≠ 1 := by
    intro e
    apply ht1
    calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  rcases c9.cfg.P_inv _ hP ht'sq with e | e
  · exact absurd e ht'1
  · calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [e]
      _ = z := by rw [hzc]; group


theorem invol_L_eq_z49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {L : Subgroup G}
    (hL : IsPCompIn 2 (Cz z) L) (hne : L ≠ K) :
    z ∈ L ∧ ∀ w ∈ L, w * w = 1 → w = 1 ∨ w = z := by
  obtain ⟨u₁, u₂, c9⟩ := setup9_of_ctx49 hc h
  have hK : IsPCompIn 2 (Cz z) K := h.std.comp_isPCompIn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cz z) := h.std.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ₀ : S ⊓ L ≤ S ⊓ cSec K := fun w hw => ⟨hw.1, le_cSec_of_ne hL hK hne hw.2⟩
  have hnc := inf_not_cyclic49 hSyl hL
  have hSyl' := isSylowOf_inf_isPCompIn49 hSyl hL
  have hL2 : IsPGroup 2 ↥(S ⊓ L) := hSyl'.isPGroup
  have hzL : z ∈ L := by
    rcases hL2.card_eq_or_dvd with h1 | h2
    · exfalso
      apply hnc
      have : Subsingleton ↥(S ⊓ L) := Finite.card_le_one_iff_subsingleton.mp (le_of_eq h1)
      exact isCyclic_of_subsingleton
    · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S ⊓ L)) 2 h2
      have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
      have htt : (t : G) * (t : G) = 1 := by
        have : (t : G) ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one _
        rwa [sq] at this
      have htQ : (t : G) ∈ S ⊓ cSec K := hQ₀ t.2
      rcases c9.Q_inv _ htQ htt with e | e
      · exfalso
        rw [e, orderOf_one] at ht2
        omega
      · rw [← e]; exact t.2.2
  refine ⟨hzL, fun w hw hw2 => ?_⟩
  obtain ⟨PL, hPL⟩ := hSyl'.exists_sylow_eq_subgroupOf
  let wA : ↥L := ⟨w, hw⟩
  have hwA : IsPGroup 2 ↥(zpowers wA) := by
    by_cases hw1 : w = 1
    · refine IsPGroup.of_card (n := 0) ?_
      have : wA = 1 := Subtype.ext hw1
      rw [this, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot, pow_zero]
    · refine IsPGroup.of_card (n := 1) ?_
      have h2 : w ^ 2 = 1 := by rw [sq]; exact hw2
      rw [Nat.card_zpowers, pow_one]
      have : orderOf wA = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime h2 hw1
      exact this
  obtain ⟨l, hl⟩ := exists_conj_mem_sylow49 PL hwA
  have hwl : (l : G)⁻¹ * w * l ∈ S ⊓ L := by
    have h1 := hl wA (Subgroup.mem_zpowers wA)
    rw [hPL] at h1
    exact h1
  have hwlsq : ((l : G)⁻¹ * w * l) * ((l : G)⁻¹ * w * l) = 1 := by
    calc ((l : G)⁻¹ * w * l) * ((l : G)⁻¹ * w * l) = (l : G)⁻¹ * (w * w) * l := by group
      _ = 1 := by rw [hw2]; group
  have hlC : (l : G) ∈ Cz z := hL.1 l.2
  have hzl : (l : G) * z = z * (l : G) := Subgroup.mem_centralizer_singleton_iff.1 hlC
  rcases c9.Q_inv _ (hQ₀ hwl) hwlsq with e | e
  · left
    calc w = (l : G) * ((l : G)⁻¹ * w * l) * (l : G)⁻¹ := by group
      _ = 1 := by rw [e]; group
  · right
    calc w = (l : G) * ((l : G)⁻¹ * w * l) * (l : G)⁻¹ := by group
      _ = (l : G) * z * (l : G)⁻¹ := by rw [e]
      _ = z := by rw [hzl]; group


theorem pRank_L_eq_one49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {L : Subgroup G}
    (hL : IsPCompIn 2 (Cz z) L) (hne : L ≠ K) : CFSG.pRank 2 ↥L = 1 := by
  obtain ⟨hzL, hinv⟩ := invol_L_eq_z49 hc h hL hne
  obtain ⟨u₁, u₂, c9⟩ := setup9_of_ctx49 hc h
  refine le_antisymm (pRank_le_one_of_inv49 (⟨z, hzL⟩ : ↥L) fun t ht => ?_) ?_
  · have h1 : (t : G) * (t : G) = 1 := by
      have := congrArg Subtype.val ht
      simpa using this
    rcases hinv t t.2 h1 with e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Subtype.ext e)
  · refine one_le_pRank49 (t := (⟨z, hzL⟩ : ↥L)) (Subtype.ext (by simpa using c9.hz2)) ?_
    intro e
    exact c9.hz1 (congrArg Subtype.val e)

theorem isPRigid49 (hc : Closed49) (h : Ctx49 G z S K F U x y) {L : Subgroup G}
    (hL : IsPCompIn 2 (Cz z) L) (hne : L ≠ K) : IsPRigid 2 z L := by
  have hKrig : IsRigidRankOneComp z K := by
    have hmem : K ∈ {K' : Subgroup G | IsRigidRankOneComp z K'} := by
      rw [h.std.toStd6r1.comps]
      exact Set.mem_singleton K
    exact hmem
  have hILoK : IsILo 2 z K := hKrig.1.1
  have hILoL : IsILo 2 z L := ⟨hILoK.1, hILoK.2.1, hL⟩
  refine ⟨hILoL, fun x' K' hlong => ?_⟩
  obtain ⟨-, hchain⟩ := hlong
  have hinv := invol_CxK_eq_z49 hc h hL hne
  have key : ∀ b : G × Subgroup G,
      Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) (z, L) b →
        b = (z, L) := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail hab hbc ih =>
      rw [ih] at hbc
      obtain ⟨h1, h2⟩ := pumpUpLT_self49 hL hinv hbc
      exact Prod.ext h1 h2
  have hfin := key _ hchain
  have hK'L : K' = L := (Prod.mk.inj hfin).2
  rw [hK'L]
  exact ⟨MulEquiv.refl _⟩

theorem no_second_comp49 (hc : Closed49) (h : Ctx49 G z S K F U x y) :
    ∀ L : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) L → L = K := by
  intro L hL
  by_contra hne
  have hrig : IsRigidRankOneComp z L := ⟨isPRigid49 hc h hL hne, pRank_L_eq_one49 hc h hL hne⟩
  have hmem : L ∈ {K' : Subgroup G | IsRigidRankOneComp z K'} := hrig
  rw [h.std.toStd6r1.comps] at hmem
  exact hne hmem

end XE

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
