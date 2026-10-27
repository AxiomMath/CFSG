module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigMod
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigPerm

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv Equiv.Perm AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {P : Subgroup G} {x : G}

theorem comm_mem_oddJunk_of_even (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L P x) {t m : G} (ht : t ∈ P) (hm : m ∈ centralizer ({x} : Set G))
    (hmN : m ∈ normalizer (L : Set G)) (hme : sign (rho θ hn ⟨m, hmN⟩) = 1) :
    t * m * t⁻¹ * m⁻¹ ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨l, hl, k, hk, rfl⟩ := exists_mul_of_sign_eq_one hS θ hn d hm hmN hme
  obtain ⟨hYle, hYn, -, -, hYmul⟩ :=
    oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic
  obtain ⟨y, hy, q, hq, rfl⟩ := hYmul k hk
  have htl : t * l = l * t := (mem_centralizer_iff.1 (d.le ht) l hl).symm
  have hPc : IsCyclic P := d.cyclic
  have htq : Commute t q :=
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := P)).is_comm.comm ⟨t, ht⟩ ⟨q, hq⟩)
  have hqt : q * t⁻¹ = t⁻¹ * q := htq.symm.inv_right.eq
  have hc : t * y * t⁻¹ * y⁻¹ ∈
      oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) :=
    mul_mem (hYn t (cyc_le_inf_cent d ht) y hy) (inv_mem hy)
  have hcK : t * y * t⁻¹ * y⁻¹ ∈ centralizer (L : Set G) := (Subgroup.mem_inf.1 (hYle hc)).1
  have hlc : l * (t * y * t⁻¹ * y⁻¹) = (t * y * t⁻¹ * y⁻¹) * l :=
    mem_centralizer_iff.1 hcK l hl
  have e : t * (l * (y * q)) * t⁻¹ * (l * (y * q))⁻¹ = l * (t * y * t⁻¹ * y⁻¹) * l⁻¹ := by
    calc t * (l * (y * q)) * t⁻¹ * (l * (y * q))⁻¹
        = (t * l) * y * (q * t⁻¹) * q⁻¹ * y⁻¹ * l⁻¹ := by group
      _ = (l * t) * y * (t⁻¹ * q) * q⁻¹ * y⁻¹ * l⁻¹ := by rw [htl, hqt]
      _ = l * (t * y * t⁻¹ * y⁻¹) * l⁻¹ := by group
  rw [e, hlc, mul_inv_cancel_right]
  exact hc

theorem sq_comm_mem_oddJunk (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L P x) {t y : G} (ht : t ∈ P) (hy : y ∈ centralizer ({x} : Set G)) :
    t * y ^ 2 * t⁻¹ * (y ^ 2)⁻¹ ∈
      oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hyN : y ∈ normalizer (L : Set G) := cent_le_normalizer hS d hy
  have hy2N : y ^ 2 ∈ normalizer (L : Set G) := pow_mem hyN 2
  refine comm_mem_oddJunk_of_even hS θ hn d ht (pow_mem hy 2) hy2N ?_
  have : (⟨y ^ 2, hy2N⟩ : normalizer (L : Set G)) = ⟨y, hyN⟩ ^ 2 := rfl
  rw [this, map_pow, map_pow]
  exact Int.units_sq _

theorem comm_mem_oddJunk_of_outer (hS : StandardSetting G L)
    (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (d : Cyc L P x) {u t c : G}
    (hu : u ∈ centralizer ({x} : Set G))
    (hus : sign (rho θ hn ⟨u, cent_le_normalizer hS d hu⟩) = -1) (ht : t ∈ P)
    (htu : t * u = u * t) (hc : c ∈ centralizer ({x} : Set G)) :
    t * c * t⁻¹ * c⁻¹ ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hcN := cent_le_normalizer hS d hc
  rcases Int.units_eq_one_or (sign (rho θ hn ⟨c, hcN⟩)) with h1 | h1
  · exact comm_mem_oddJunk_of_even hS θ hn d ht hc hcN h1
  · have huc : u⁻¹ * c ∈ centralizer ({x} : Set G) := mul_mem (inv_mem hu) hc
    have hucN : u⁻¹ * c ∈ normalizer (L : Set G) := cent_le_normalizer hS d huc
    have he : sign (rho θ hn ⟨u⁻¹ * c, hucN⟩) = 1 := by
      have : (⟨u⁻¹ * c, hucN⟩ : normalizer (L : Set G)) =
          (⟨u, cent_le_normalizer hS d hu⟩ : normalizer (L : Set G))⁻¹ * ⟨c, hcN⟩ := rfl
      rw [this, map_mul, map_inv, map_mul, map_inv, hus, h1]
      decide
    have h2 := oddJunk_conj_mem hS d hu (comm_mem_oddJunk_of_even hS θ hn d ht huc hucN he)
    have hutu : u * t * u⁻¹ = t := by rw [← htu]; group
    have e : t * c * t⁻¹ * c⁻¹ = u * (t * (u⁻¹ * c) * t⁻¹ * (u⁻¹ * c)⁻¹) * u⁻¹ := by
      calc t * c * t⁻¹ * c⁻¹ = (u * t * u⁻¹) * c * t⁻¹ * c⁻¹ := by rw [hutu]
        _ = u * (t * (u⁻¹ * c) * t⁻¹ * (u⁻¹ * c)⁻¹) * u⁻¹ := by group
    rw [e]
    exact h2

theorem exists_lift_rho_of_commute (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {x : G}
    (hx : x ∈ normalizer (L : Set G)) {D : Perm (Fin n)} (hD : D ∈ alternatingGroup (Fin n))
    (hDσ : D * rho θ hn ⟨x, hx⟩ = rho θ hn ⟨x, hx⟩ * D) :
    ∃ l ∈ L, l * x = x * l ∧ ∃ hlN : l ∈ normalizer (L : Set G), rho θ hn ⟨l, hlN⟩ = D := by
  set l : L := θ.symm ⟨D, hD⟩ with hl
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hρl : rho θ hn ⟨l, hlN⟩ = D := by
    rw [rho_of_mem θ hn l hlN, hl, MulEquiv.apply_symm_apply]
  refine ⟨l, l.2, ?_, hlN, hρl⟩
  set w : G := (l : G) * x * (l : G)⁻¹ * x⁻¹ with hw
  have hwN : w ∈ normalizer (L : Set G) :=
    mul_mem (mul_mem (mul_mem hlN hx) (inv_mem hlN)) (inv_mem hx)
  have hwK : w ∈ centralizer (L : Set G) := by
    refine (rho_eq_one_iff θ hn ⟨w, hwN⟩).1 ?_
    have : (⟨w, hwN⟩ : normalizer (L : Set G)) =
        ⟨l, hlN⟩ * ⟨x, hx⟩ * (⟨l, hlN⟩ : normalizer (L : Set G))⁻¹ * ⟨x, hx⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hρl, hDσ]
    group
  have hwL : w ∈ L := by
    have h1 : x * (l : G)⁻¹ * x⁻¹ ∈ L := (mem_normalizer_iff.1 hx _).1 (inv_mem l.2)
    have : w = (l : G) * (x * (l : G)⁻¹ * x⁻¹) := by rw [hw]; group
    rw [this]
    exact mul_mem l.2 h1
  have hw1 : w = 1 := eq_one_of_mem_of_mem_centralizer θ (by omega) hwL hwK
  have h2 : (l : G) * x * (l : G)⁻¹ = x := mul_inv_eq_one.1 hw1
  calc (l : G) * x = ((l : G) * x * (l : G)⁻¹) * l := by group
    _ = x * l := by rw [h2]

theorem false_of_odd_commutators (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (h9 : 9 ≤ n)
    {u : G} (hu : u ∈ normalizer (L : Set G)) (hx : x ∈ normalizer (L : Set G)) (hux : u ^ 2 = x)
    (hx2 : x ^ 2 = 1) (hxK : x ∉ centralizer (L : Set G)) (Y : Subgroup G)
    (hY : Odd (Nat.card Y))
    (hcomm : (∀ l ∈ L, l * x = x * l → u * l * u⁻¹ * l⁻¹ ∈ Y) ∨
      (sign (rho θ hn ⟨u, hu⟩) = 1 ∧
        ∀ l ∈ L, l * x = x * l → u * l ^ 2 * u⁻¹ * (l ^ 2)⁻¹ ∈ Y)) : False := by
  set ρ := rho θ hn with hρ
  have hcσ : ρ ⟨u, hu⟩ ^ 2 = ρ ⟨x, hx⟩ := by
    rw [← map_pow]
    congr 1
    exact Subtype.ext hux
  have hσ2 : ρ ⟨x, hx⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hσ1 : ρ ⟨x, hx⟩ ≠ 1 := fun h1 => hxK ((rho_eq_one_iff θ hn _).1 h1)
  set V : Subgroup (Perm (Fin n)) := (Y.subgroupOf (normalizer (L : Set G))).map ρ with hV
  have hVodd : Odd (Nat.card V) := by
    have h1 : Nat.card V ∣ Nat.card (Y.subgroupOf (normalizer (L : Set G))) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Y.subgroupOf (normalizer (L : Set G))) ∣ Nat.card Y :=
      Subgroup.card_comap_dvd_of_injective Y _ (Subgroup.subtype_injective _)
    exact Odd.of_dvd_nat hY (h1.trans h2)
  have hmemV : ∀ (w : G) (hw : w ∈ normalizer (L : Set G)), w ∈ Y → ρ ⟨w, hw⟩ ∈ V :=
    fun w hw hwY => ⟨⟨w, hw⟩, hwY, rfl⟩
  refine no_sq_root_mod_odd' (α := Fin n) (by simpa using h9) hcσ hσ2 hσ1 V hVodd ?_
  rcases hcomm with h | ⟨hs, h⟩
  · left
    intro D hD hDσ
    obtain ⟨l, hl, hlx, hlN, rfl⟩ := exists_lift_rho_of_commute θ hn hx hD hDσ
    have hmem : u * l * u⁻¹ * l⁻¹ ∈ normalizer (L : Set G) :=
      mul_mem (mul_mem (mul_mem hu hlN) (inv_mem hu)) (inv_mem hlN)
    have e : ρ ⟨u, hu⟩ * ρ ⟨l, hlN⟩ * (ρ ⟨u, hu⟩)⁻¹ * (ρ ⟨l, hlN⟩)⁻¹ =
        ρ ⟨u * l * u⁻¹ * l⁻¹, hmem⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hmemV _ hmem (h l hl hlx)
  · right
    refine ⟨hs, fun D hD hDσ => ?_⟩
    obtain ⟨l, hl, hlx, hlN, rfl⟩ := exists_lift_rho_of_commute θ hn hx hD hDσ
    have hmem : u * l ^ 2 * u⁻¹ * (l ^ 2)⁻¹ ∈ normalizer (L : Set G) :=
      mul_mem (mul_mem (mul_mem hu (pow_mem hlN 2)) (inv_mem hu)) (inv_mem (pow_mem hlN 2))
    have e : ρ ⟨u, hu⟩ * ρ ⟨l, hlN⟩ ^ 2 * (ρ ⟨u, hu⟩)⁻¹ * (ρ ⟨l, hlN⟩ ^ 2)⁻¹ =
        ρ ⟨u * l ^ 2 * u⁻¹ * (l ^ 2)⁻¹, hmem⟩ := by
      rw [← map_pow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hmemV _ hmem (h l hl hlx)

end CFSG.OddStandard.AltStdCycTwo
