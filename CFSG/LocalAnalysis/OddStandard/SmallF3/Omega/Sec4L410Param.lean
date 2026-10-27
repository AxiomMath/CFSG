module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4CombCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L44

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma vecWeight_zero' {n : ℕ} : vecWeight (0 : Fin n → ZMod 2) = 0 := by
  simp [vecWeight]

private lemma ne_zero_of_vecWeight_ne_zero {v : Fin 7 → ZMod 2} (h : vecWeight v ≠ 0) :
    v ≠ 0 :=
  fun hv => h (by rw [hv]; exact vecWeight_zero')

private lemma zpowers_eq_one_or_of_orderOf_two {t : G} (ht : orderOf t = 2) {p : G}
    (hp : p ∈ Subgroup.zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private lemma conj_mem_conjClassIn {M : Subgroup G} {x y k : G} (hk : k ∈ M)
    (h : y ∈ conjClassIn M x) : k * y * k⁻¹ ∈ conjClassIn M x := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨k * m, M.mul_mem hk hm, by group⟩

private lemma weightClosed_of_conjInvariant {M H B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ B H (alternatingGroup (Fin 7)))
    (hHM : H ≤ M) {P : G → Prop}
    (hPconj : ∀ k ∈ H, ∀ y, P y → P (k * y * k⁻¹))
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hP : P (φ v)) :
    ∀ w : Fin 7 → ZMod 2, IsEvenVec w → vecWeight w = vecWeight v → P (φ w) := by
  intro w hw hwt
  obtain ⟨σ, hσ, hσv⟩ := exists_alternating_permVec hv hw hwt.symm
  obtain ⟨k, hkH, hkσ⟩ := hperm.2.2.2.2 σ hσ
  have hkφ : k * φ v * k⁻¹ = φ w := by rw [hkσ v hv, hσv]
  have h := hPconj k hkH (φ v) hP
  rwa [hkφ] at h

theorem sec4_Delta_param [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (h : Sec4AData t L S z A B φ)
    (hBn : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B, m * b * m⁻¹ ∈ B) :
    ∃ T : Set (Fin 7 → ZMod 2), (∀ v ∈ T, IsEvenVec v ∧ v ≠ 0) ∧
      (∀ v ∈ T, ∀ w : Fin 7 → ZMod 2, IsEvenVec w → vecWeight w = vecWeight v → w ∈ T) ∧
      (∀ v, IsEvenVec v → v ≠ 0 →
        (v ∈ T ↔ t * φ v ∈ conjClassIn (normalizer (A : Set G)) t)) ∧
      Nat.card (conjClassIn (normalizer (A : Set G)) t) = 1 + Nat.card T := by
  classical
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (h.bdata.isMax.1 hb)).2
  have htC : t ∈ centralizer (L : Set G) :=
    sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting
  have htL : t ∉ L := sec4_t_not_mem hctx.toSec4Setting
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hnorm : L ⊓ normalizer (A : Set G) = L ⊓ normalizer (B : Set G) :=
    sec4_inf_normalizer_eq hLt h.A_eq h.B_eq
  have hHM : (L ⊓ normalizer (B : Set G)) ≤ normalizer (A : Set G) := by
    intro k hk; rw [← hnorm] at hk; exact hk.2
  let T : Set (Fin 7 → ZMod 2) :=
    {v | IsEvenVec v ∧ v ≠ 0 ∧ t * φ v ∈ conjClassIn (normalizer (A : Set G)) t}
  have hPconj : ∀ k ∈ (L ⊓ normalizer (B : Set G)), ∀ y,
      t * y ∈ conjClassIn (normalizer (A : Set G)) t →
        t * (k * y * k⁻¹) ∈ conjClassIn (normalizer (A : Set G)) t := by
    intro k hk y hy
    have hkt : k * t * k⁻¹ = t := by
      have hcomm : t * k = k * t :=
        (Subgroup.mem_centralizer_iff.mp (hLt hk.1)) t (Set.mem_singleton t)
      rw [← hcomm]; group
    have h1 : k * (t * y) * k⁻¹ ∈ conjClassIn (normalizer (A : Set G)) t :=
      conj_mem_conjClassIn (hHM hk) hy
    have h2 : k * (t * y) * k⁻¹ = t * (k * y * k⁻¹) := by
      calc k * (t * y) * k⁻¹ = (k * t * k⁻¹) * (k * y * k⁻¹) := by group
        _ = t * (k * y * k⁻¹) := by rw [hkt]
    rwa [h2] at h1
  let f : (Fin 7 → ZMod 2) → G := fun v => t * φ v
  have htA : t ∈ A := by rw [h.A_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hBA : B ≤ A := by rw [h.A_eq]; exact le_sup_left
  have hΔeq : conjClassIn (normalizer (A : Set G)) t = insert t (f '' T) := by
    ext δ
    constructor
    · intro hδ
      rw [conjClassIn] at hδ
      obtain ⟨m, hm, rfl⟩ := hδ
      by_cases hδt : m * t * m⁻¹ = t
      · exact Set.mem_insert_iff.mpr (Or.inl hδt)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        have hδA : m * t * m⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hm t).mp htA
        have hδsup : m * t * m⁻¹ ∈ B ⊔ zpowers t := by rwa [h.A_eq] at hδA
        have hcommBt : ∀ b ∈ B, ∀ p ∈ zpowers t, b * p = p * b := by
          intro b hb p hp
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
          have hbt : Commute b t := (Subgroup.mem_centralizer_iff.mp htC) b (hBL hb)
          exact (hbt.zpow_right k).eq
        obtain ⟨b, hbB, p, hp, hδbp⟩ :=
          (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcommBt).mp hδsup
        rcases zpowers_eq_one_or_of_orderOf_two hctx.involution hp with hp1 | hpt
        · exfalso
          have hδb : m * t * m⁻¹ ∈ B := by rw [hδbp, hp1, mul_one]; exact hbB
          have htb : t ∈ B := by
            have h := hBn m⁻¹ ((normalizer (A : Set G)).inv_mem hm) (m * t * m⁻¹) hδb
            rw [inv_inv, show m⁻¹ * (m * t * m⁻¹) * m = t by group] at h
            exact h
          exact htL (hBL htb)
        · obtain ⟨v, hv, hφvb⟩ := (h.bdata.perm.2.2.1 b).mp hbB
          have hbtc : b * t = t * b :=
            (Subgroup.mem_centralizer_iff.mp htC) b (hBL hbB)
          have hδtb : m * t * m⁻¹ = t * b := by rw [hδbp, hpt, hbtc]
          have hv0 : v ≠ 0 := by
            intro hvz
            exact hδt (by
              rw [hδtb, ← hφvb, hvz, IsPermModuleVia.map_zero h.bdata.perm, mul_one])
          refine ⟨v, ⟨hv, hv0, ?_⟩, ?_⟩
          · exact ⟨m, hm, by rw [hφvb, hδtb]⟩
          · show f v = m * t * m⁻¹
            show t * φ v = m * t * m⁻¹
            rw [hφvb, hδtb]
    · intro hδ
      rcases Set.mem_insert_iff.mp hδ with hδ | hδ
      · rw [hδ]; exact ⟨1, Subgroup.one_mem _, by group⟩
      · obtain ⟨v, hvT, hfv⟩ := hδ
        rw [← hfv]
        exact hvT.2.2
  have ht_notin : t ∉ f '' T := by
    rintro ⟨v, hvT, hfv⟩
    have hφ1 : φ v = 1 := by
      have h : t * φ v = t := hfv
      exact mul_left_cancel (by rw [h, mul_one])
    have hv_eq : v = 0 := h.bdata.perm.2.1 v 0 hvT.1 (by unfold IsEvenVec; simp)
      (by rw [hφ1, IsPermModuleVia.map_zero h.bdata.perm])
    exact hvT.2.1 hv_eq
  have hf_inj : Set.InjOn f T := by
    intro v hvT w hwT hvw
    exact h.bdata.perm.2.1 v w hvT.1 hwT.1 (mul_left_cancel hvw)
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro v hvT
    exact ⟨hvT.1, hvT.2.1⟩
  · intro v hvT w hw hwt
    refine ⟨hw, ?_, ?_⟩
    · have hvpos : vecWeight v ≠ 0 := fun h => hvT.2.1 (eq_zero_of_vecWeight_eq_zero h)
      exact ne_zero_of_vecWeight_ne_zero (by rw [hwt]; exact hvpos)
    · exact weightClosed_of_conjInvariant h.bdata.perm hHM hPconj hvT.1 hvT.2.2 w hw hwt
  · intro v hv hv0
    constructor
    · intro hvT; exact hvT.2.2
    · intro hp; exact ⟨hv, hv0, hp⟩
  · calc Nat.card (conjClassIn (normalizer (A : Set G)) t)
        = (insert t (f '' T)).ncard := by rw [Nat.card_coe_set_eq, hΔeq]
      _ = (f '' T).ncard + 1 := Set.ncard_insert_of_notMem ht_notin
      _ = T.ncard + 1 := by rw [Set.InjOn.ncard_image hf_inj]
      _ = 1 + Nat.card T := by rw [Nat.card_coe_set_eq]; omega

theorem sec4_Gamma_param [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (h : Sec4AData t L S z A B φ)
    (hBn : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B, m * b * m⁻¹ ∈ B) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hv0 : v ≠ 0) :
    ∃ T : Set (Fin 7 → ZMod 2), v ∈ T ∧ (∀ w ∈ T, IsEvenVec w ∧ w ≠ 0) ∧
      (∀ w ∈ T, ∀ w' : Fin 7 → ZMod 2, IsEvenVec w' → vecWeight w' = vecWeight w → w' ∈ T) ∧
      (∀ w, IsEvenVec w → w ≠ 0 →
        (w ∈ T ↔ φ w ∈ conjClassIn (normalizer (A : Set G)) (φ v))) ∧
      Nat.card (conjClassIn (normalizer (A : Set G)) (φ v)) = Nat.card T := by
  classical
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (h.bdata.isMax.1 hb)).2
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hnorm : L ⊓ normalizer (A : Set G) = L ⊓ normalizer (B : Set G) :=
    sec4_inf_normalizer_eq hLt h.A_eq h.B_eq
  have hHM : (L ⊓ normalizer (B : Set G)) ≤ normalizer (A : Set G) := by
    intro k hk; rw [← hnorm] at hk; exact hk.2
  let T : Set (Fin 7 → ZMod 2) :=
    {w | IsEvenVec w ∧ w ≠ 0 ∧ φ w ∈ conjClassIn (normalizer (A : Set G)) (φ v)}
  have hφvB : φ v ∈ B := IsPermModuleVia.mem h.bdata.perm hv
  have hφv1 : φ v ≠ 1 := by
    intro h1
    apply hv0
    exact h.bdata.perm.2.1 v 0 hv (by unfold IsEvenVec; simp)
      (by rw [h1, IsPermModuleVia.map_zero h.bdata.perm])
  have hPconj : ∀ k ∈ (L ⊓ normalizer (B : Set G)), ∀ y,
      y ∈ conjClassIn (normalizer (A : Set G)) (φ v) →
        k * y * k⁻¹ ∈ conjClassIn (normalizer (A : Set G)) (φ v) :=
    fun k hk y hy => conj_mem_conjClassIn (hHM hk) hy
  have hTcl : ∀ w ∈ T, ∀ w', IsEvenVec w' → vecWeight w' = vecWeight w → w' ∈ T := by
    intro w hwT w' hw' hwt
    refine ⟨hw', ?_, ?_⟩
    · have hwpos : vecWeight w ≠ 0 := fun h => hwT.2.1 (eq_zero_of_vecWeight_eq_zero h)
      exact ne_zero_of_vecWeight_ne_zero (by rw [hwt]; exact hwpos)
    · exact weightClosed_of_conjInvariant h.bdata.perm hHM hPconj hwT.1 hwT.2.2 w' hw' hwt
  have hΓeq : conjClassIn (normalizer (A : Set G)) (φ v) = φ '' T := by
    ext x
    constructor
    · intro hx
      rw [conjClassIn] at hx
      obtain ⟨m, hm, hxm⟩ := hx
      subst hxm
      have hxB : m * φ v * m⁻¹ ∈ B := hBn m hm (φ v) hφvB
      obtain ⟨w, hw, hφw⟩ := (h.bdata.perm.2.2.1 (m * φ v * m⁻¹)).mp hxB
      have hw0 : w ≠ 0 := by
        intro hwz
        apply hφv1
        have h2 : m * φ v * m⁻¹ = 1 := by
          rw [← hφw, hwz, IsPermModuleVia.map_zero h.bdata.perm]
        calc φ v = m⁻¹ * (m * φ v * m⁻¹) * m := by group
          _ = m⁻¹ * 1 * m := by rw [h2]
          _ = 1 := by group
      have hmem : φ w ∈ conjClassIn (normalizer (A : Set G)) (φ v) := by
        rw [hφw]; exact ⟨m, hm, rfl⟩
      exact ⟨w, ⟨hw, hw0, hmem⟩, hφw⟩
    · rintro ⟨w, hwT, rfl⟩
      exact hwT.2.2
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hv, hv0, ⟨1, Subgroup.one_mem _, by group⟩⟩
  · intro w hwT; exact ⟨hwT.1, hwT.2.1⟩
  · exact hTcl
  · intro w hw hw0
    constructor
    · intro hwT; exact hwT.2.2
    · intro hp; exact ⟨hw, hw0, hp⟩
  · calc Nat.card (conjClassIn (normalizer (A : Set G)) (φ v))
        = (φ '' T).ncard := by rw [Nat.card_coe_set_eq, hΓeq]
      _ = T.ncard := Set.InjOn.ncard_image
        (fun a ha b hb heq => h.bdata.perm.2.1 a b ha.1 hb.1 heq)
      _ = Nat.card T := (Nat.card_coe_set_eq T).symm

theorem sec4_Delta_card [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (h : Sec4AData t L S z A B φ)
    (h47 : ∃ h : G, h⁻¹ * t * h = t * z)
    (h46 : conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t)
    (hBn : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B, m * b * m⁻¹ ∈ B) :
    Nat.card (conjClassIn (normalizer (A : Set G)) t) = 36 ∨
      Nat.card (conjClassIn (normalizer (A : Set G)) t) = 43 ∨
      Nat.card (conjClassIn (normalizer (A : Set G)) t) = 57 ∨
      Nat.card (conjClassIn (normalizer (A : Set G)) t) = 64 := by
  classical
  obtain ⟨T, hTne, hTcl, hTiff, hTcard⟩ := sec4_Delta_param hctx h hBn
  obtain ⟨v₄, hv₄, hw₄, hφv₄⟩ := h.z_eq
  have hv₄0 : v₄ ≠ 0 := by
    intro h0; rw [h0] at hw₄; simp [vecWeight] at hw₄
  have htA : t ∈ A := by rw [h.A_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hBA : B ≤ A := by rw [h.A_eq]; exact le_sup_left
  have hzA : z ∈ A := by rw [← hφv₄]; exact hBA (IsPermModuleVia.mem h.bdata.perm hv₄)
  have htφ : t * φ v₄ ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hφv₄]
    obtain ⟨h, hh⟩ := h47
    have htop : t * z ∈ conjClassIn ⊤ t := ⟨h⁻¹, trivial, by rw [inv_inv]; exact hh.symm⟩
    have hmem : t * z ∈ conjClassIn ⊤ t ∩ (A : Set G) := ⟨htop, A.mul_mem htA hzA⟩
    rwa [h46] at hmem
  have hv₄T : v₄ ∈ T := (hTiff v₄ hv₄ hv₄0).mpr htφ
  have hcard := card_weightClosed_of_four hTne hTcl ⟨v₄, hv₄T, hw₄⟩
  rw [hTcard]
  rcases hcard with h | h | h | h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; omega

theorem sec4_Gamma_card [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (h : Sec4AData t L S z A B φ)
    (h48 : conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z)
    (hBn : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B, m * b * m⁻¹ ∈ B) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hv6 : vecWeight v = 6) :
    Nat.card (conjClassIn (normalizer (A : Set G)) (φ v)) = 7 ∨
      Nat.card (conjClassIn (normalizer (A : Set G)) (φ v)) = 28 := by
  classical
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (h.bdata.isMax.1 hb)).2
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0] at hv6; simp [vecWeight] at hv6
  obtain ⟨T, hvT, hTne, hTcl, hTiff, hTcard⟩ := sec4_Gamma_param hctx h hBn hv hv0
  have hno : ∀ w ∈ T, vecWeight w ≠ 4 := by
    intro w hwT hw4
    obtain ⟨v₄, hv₄, hw₄, hφv₄⟩ := h.z_eq
    have hv₄0 : v₄ ≠ 0 := by
      intro h0
      rw [h0] at hw₄
      simp [vecWeight] at hw₄
    have hv₄T : v₄ ∈ T := hTcl w hwT v₄ hv₄ (by rw [hw₄, hw4])
    have hv₄Γ : φ v₄ ∈ conjClassIn (normalizer (A : Set G)) (φ v) :=
      (hTiff v₄ hv₄ hv₄0).mp hv₄T
    have hzΓ : z ∈ conjClassIn (normalizer (A : Set G)) (φ v) := hφv₄ ▸ hv₄Γ
    obtain ⟨m, hm, hzm⟩ := hzΓ
    have hφvC : φ v ∈ centralizer ({t} : Set G) :=
      hLt (hBL (IsPermModuleVia.mem h.bdata.perm hv))
    have hφvtop : φ v ∈ conjClassIn ⊤ z := by
      refine ⟨m⁻¹, trivial, ?_⟩
      rw [hzm]; group
    have hφv48 : φ v ∈ conjClassIn L z := by
      have hmem : φ v ∈ conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) :=
        ⟨hφvtop, hφvC⟩
      rwa [h48] at hmem
    obtain ⟨l, hl, hlz⟩ := hφv48
    have hI4 : IsI4PlusIn L (φ v) := by
      have h := hctx.pocket.conj_of_mem hl
      rwa [← hlz] at h
    have := (h.bdata.type4 v hv hv0).mpr hI4
    omega
  have hcard := card_weightClosed_of_six hTne hTcl ⟨v, hvT, hv6⟩ hno
  rw [hTcard]
  rcases hcard with h | h
  · left; omega
  · right; omega

end CFSG.OddStandard.SmallF3.Omega
