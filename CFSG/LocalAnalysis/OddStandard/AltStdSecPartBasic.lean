module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapSetting
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2a

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

structure ShapeTwo {G : Type} [Group G] (L Q : Subgroup G) (z u : G) : Prop where
  card : Nat.card Q = 2
  cent : u ∈ centralizer ({z} : Set G)
  outer : u ∉ L ⊔ Q
  sq : u ^ 2 = 1

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem ShapeTwo.sq_mem (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) : x * x ∈ L := by
  have hz2 : z * z = 1 := d.mul_self
  have hq : ∀ q ∈ Q, q * q = 1 ∧ ∀ c ∈ centralizer ({z} : Set G), c * q = q * c := by
    intro q hq
    rcases eq_one_or_eq_of_card_eq_two d T.card hq with rfl | rfl
    · exact ⟨by simp, fun c _ => by simp⟩
    · exact ⟨hz2, fun c hc => (mem_centralizer_singleton_iff.1 hc)⟩
  have huN : u ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d T.cent
  have hu1 : u * u = 1 := by rw [← pow_two, T.sq]
  rcases mem_sup_or_inv_mul_mem_sup h d T.cent T.outer hx with hx1 | hx1
  · obtain ⟨l, hl, q, hqQ, rfl⟩ := (mem_sup_iff_mul d).1 hx1
    obtain ⟨hq2, hqc⟩ := hq q hqQ
    have hlc : l ∈ centralizer ({z} : Set G) := le_centralizer_single h d hl
    have h1 : q * l = l * q := (hqc l hlc).symm
    have h2 : l * q * (l * q) = l * l := by
      calc l * q * (l * q) = l * (q * l) * q := by group
        _ = l * (l * q) * q := by rw [h1]
        _ = l * l * (q * q) := by group
        _ = l * l := by rw [hq2, mul_one]
    rw [h2]
    exact mul_mem hl hl
  · obtain ⟨l, hl, q, hqQ, hlq⟩ := (mem_sup_iff_mul d).1 hx1
    obtain ⟨hq2, hqc⟩ := hq q hqQ
    have hxe : x = u * (l * q) := by rw [hlq]; group
    have hlc : l ∈ centralizer ({z} : Set G) := le_centralizer_single h d hl
    have hq1 : q * l = l * q := (hqc l hlc).symm
    have hq2' : q * u = u * q := (hqc u T.cent).symm
    have hulu : u * l * u⁻¹ ∈ L := (mem_normalizer_iff.1 huN l).1 hl
    have hu1' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
    have h2 : x * x = (u * l * u⁻¹) * l := by
      rw [hxe, hu1']
      calc u * (l * q) * (u * (l * q)) = u * l * (q * u) * l * q := by group
        _ = u * l * (u * q) * l * q := by rw [hq2']
        _ = u * l * u * (q * l) * q := by group
        _ = u * l * u * (l * q) * q := by rw [hq1]
        _ = u * l * u * l * (q * q) := by group
        _ = u * l * u * l := by rw [hq2, mul_one]
    rw [h2]
    exact mul_mem hulu hl

theorem ShapeTwo.mem_of_odd (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf x)) : x ∈ L := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have h2 : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [h1, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, pow_two]
  exact h2 ▸ pow_mem (T.sq_mem h d hx) (k + 1)

end Basic

section Perm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

@[expose] noncomputable def permOf (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    Perm (Fin n) :=
  rho e h.hn ⟨x, AltStdBal.centralizer_le_normalizer h d hx⟩

theorem permOf_mul (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G)) (hy : y ∈ centralizer ({z} : Set G))
    (hxy : x * y ∈ centralizer ({z} : Set G)) :
    permOf h d e hxy = permOf h d e hx * permOf h d e hy := by
  unfold permOf
  rw [← map_mul]
  rfl

theorem permOf_inv (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hx' : x⁻¹ ∈ centralizer ({z} : Set G)) :
    permOf h d e hx' = (permOf h d e hx)⁻¹ := by
  unfold permOf
  rw [← map_inv]
  rfl

theorem permOf_of_mem (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hxL : x ∈ L) :
    permOf h d e hx = ((e ⟨x, hxL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
  rho_of_mem e h.hn ⟨x, hxL⟩ (AltStdBal.centralizer_le_normalizer h d hx)

theorem comm_of_permOf_comm (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ centralizer ({z} : Set G))
    (hcomm : permOf h d e hx * permOf h d e hy = permOf h d e hy * permOf h d e hx) :
    x * y = y * x := by
  have hc : x * y * x⁻¹ * y⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hcL : x * y * x⁻¹ * y⁻¹ ∈ L := by
    have h1 := commutator_centralizer_le h d hQ2
    exact h1 (Subgroup.commutator_mem_commutator hx hy)
  have hperm : permOf h d e hc = 1 := by
    have hxy := mul_mem hx hy
    have hxyx := mul_mem hxy (inv_mem hx)
    rw [permOf_mul h d e hxyx (inv_mem hy) hc, permOf_mul h d e hxy (inv_mem hx) hxyx,
      permOf_mul h d e hx hy hxy, permOf_inv h d e hx (inv_mem hx),
      permOf_inv h d e hy (inv_mem hy), hcomm]
    group
  have h2 := permOf_of_mem h d e hc hcL
  rw [hperm] at h2
  have h3 : e ⟨x * y * x⁻¹ * y⁻¹, hcL⟩ = 1 := by
    apply Subtype.ext
    simpa using h2.symm
  have h4 : (⟨x * y * x⁻¹ * y⁻¹, hcL⟩ : L) = 1 := by
    apply e.injective
    rw [h3, map_one]
  have h5 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h4
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h5, one_mul]

theorem comm_of_mem_corr_of_permOf_fix (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    {F : Finset (Fin n)} (hF : ∀ i ∈ F, permOf h d e hx i = i) {w : G}
    (hw : w ∈ corr (X := G) e (altSub F)) : x * w = w * x := by
  obtain ⟨hwL, hwT⟩ := mem_corr.1 hw
  have hxN : x ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hx
  have hxw : x * w * x⁻¹ ∈ L := (mem_normalizer_iff.1 hxN w).1 hwL
  have h1 := rho_conj_apply e h.hn hxN ⟨w, hwL⟩ ⟨x * w * x⁻¹, hxw⟩ rfl
  have hfix : permOf h d e hx ∈ fixSub F := hF
  have h2 := comm_altSub_fixSub hwT hfix
  have h3 : (e ⟨x * w * x⁻¹, hxw⟩ : alternatingGroup (Fin n)) = e ⟨w, hwL⟩ := by
    apply Subtype.ext
    rw [← h1]
    change permOf h d e hx * _ * (permOf h d e hx)⁻¹ = _
    rw [← h2]
    simp
  have h4 := e.injective h3
  have h5 : x * w * x⁻¹ = w := congrArg Subtype.val h4
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [h5]

theorem mem_normalizer_corr_fixFin (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {a y : G} (ha : a ∈ centralizer ({z} : Set G))
    (hy : y ∈ centralizer ({z} : Set G)) (hay : y * a = a * y) :
    y ∈ normalizer (corr (X := G) e (altSub (fixFin (permOf h d e ha))) : Set G) := by
  have hyN : y ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hy
  refine mem_normalizer_corr e h.hn hyN (mem_normalizer_altSub fun i => ?_)
  have hcomm : permOf h d e hy * permOf h d e ha = permOf h d e ha * permOf h d e hy := by
    rw [← permOf_mul h d e hy ha (mul_mem hy ha), ← permOf_mul h d e ha hy (mul_mem ha hy)]
    congr 1
  have h2 := congrArg (fun f : Perm (Fin n) => f i) hcomm
  simp only [Perm.mul_apply] at h2
  rw [mem_fixFin, mem_fixFin]
  change permOf h d e ha i = i ↔ permOf h d e ha (permOf h d e hy i) = permOf h d e hy i
  constructor
  · intro hi
    rw [← h2, hi]
  · intro hi
    have h3 : permOf h d e hy (permOf h d e ha i) = permOf h d e hy i := by rw [h2, hi]
    exact (permOf h d e hy).injective h3

theorem exists_lift_commuting (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {a' : G} (ha' : a' ∈ centralizer ({z} : Set G))
    {c : Perm (Fin n)} (hc : c * permOf h d e ha' = permOf h d e ha' * c) :
    ∃ (s : G) (hs : s ∈ centralizer ({z} : Set G)), permOf h d e hs = c ∧ s * a' = a' * s := by
  have hbij := rhoSwap_bijective h d T.card T.cent T.outer T.sq e
  obtain ⟨s, hs⟩ := hbij.2 c
  have hsC : (s : G) ∈ centralizer ({z} : Set G) :=
    (sup_le (le_centralizer_single h d) (zpowers_le.2 T.cent)) s.2
  have hperm : permOf h d e hsC = c := by
    rw [← hs, rhoSwap_apply]
    rfl
  refine ⟨s, hsC, hperm, ?_⟩
  refine comm_of_permOf_comm h d T.card e hsC ha' ?_
  rw [hperm]
  exact hc

end Perm

end CFSG.OddStandard.AltStdSec
