module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup

variable {G : Type} [Group G]

section Sup

def supZ (K : Subgroup G) (z : G) (hz : z * z = 1) (hc : ∀ k ∈ K, z * k = k * z) :
    Subgroup G where
  carrier := {x | ∃ k ∈ K, x = k ∨ x = k * z}
  mul_mem' := by
    rintro x y ⟨k₁, hk₁, hx⟩ ⟨k₂, hk₂, hy⟩
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact Or.inl rfl
    · exact Or.inr (mul_assoc _ _ _).symm
    · refine Or.inr ?_
      rw [mul_assoc, hc k₂ hk₂, ← mul_assoc]
    · refine Or.inl ?_
      calc k₁ * z * (k₂ * z) = k₁ * (z * k₂) * z := by group
        _ = k₁ * k₂ * (z * z) := by rw [hc k₂ hk₂]; group
        _ = k₁ * k₂ := by rw [hz, mul_one]
  one_mem' := ⟨1, K.one_mem, Or.inl rfl⟩
  inv_mem' := by
    rintro x ⟨k, hk, hx⟩
    refine ⟨k⁻¹, K.inv_mem hk, ?_⟩
    rcases hx with hx | hx <;> rw [hx]
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
      rw [mul_inv_rev, hzi, hc _ (K.inv_mem hk)]

theorem mem_sup_zpowers_iff {K : Subgroup G} {z : G} (hz : z * z = 1)
    (hc : ∀ k ∈ K, z * k = k * z) {x : G} :
    x ∈ K ⊔ zpowers z ↔ ∃ k ∈ K, x = k ∨ x = k * z := by
  constructor
  · intro hx
    have hle : K ⊔ zpowers z ≤ supZ K z hz hc := by
      refine sup_le (fun k hk => ⟨k, hk, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, K.one_mem, Or.inr (one_mul z).symm⟩
    exact hle hx
  · rintro ⟨k, hk, rfl | rfl⟩
    · exact mem_sup_left hk
    · exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers z))

end Sup

theorem z_mem_egV {B : Subgroup G} {z : G} : z ∈ egV B z := mem_sup_right (mem_zpowers z)

theorem B_le_egV {B : Subgroup G} {z : G} : B ≤ egV B z := le_sup_left

theorem mem_egLam {B : Subgroup G} {z t : G} :
    t ∈ egLam B z ↔ t ∈ egM B z ∧ ∀ b ∈ B, b * t = t * b := by
  simp only [egLam, mem_inf, mem_centralizer_iff, SetLike.mem_coe]

theorem mem_normalizer_of_comm {B : Subgroup G} {g : G} (hg : ∀ b ∈ B, g * b = b * g) :
    g ∈ normalizer (B : Set G) := by
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : g * x * g⁻¹ = x := by rw [hg x hx, mul_inv_cancel_right]
    rw [hx']
    exact hx
  · have h1 : g * (g * x * g⁻¹) = g * x := (hg _ hx).trans (by group)
    have h2 : g * x * g⁻¹ = x := mul_left_cancel h1
    rw [← h2]
    exact hx

@[expose] def phiB (z w : G) : G := z * (w⁻¹ * z * w)

theorem conj_mem_egLam_of {B : Subgroup G} {z g : G} (hgM : g ∈ egM B z)
    (hgB : ∀ b ∈ B, g⁻¹ * b * g ∈ B) {t : G} (ht : t ∈ egLam B z) : g * t * g⁻¹ ∈ egLam B z := by
  obtain ⟨htM, htc⟩ := mem_egLam.1 ht
  refine mem_egLam.2 ⟨mul_mem (mul_mem hgM htM) (inv_mem hgM), fun b hb => ?_⟩
  have hc := htc _ (hgB b hb)
  calc b * (g * t * g⁻¹) = g * ((g⁻¹ * b * g) * t) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * b * g)) * g⁻¹ := by rw [hc]
    _ = g * t * g⁻¹ * b := by group

variable [Finite G] {L B : Subgroup G} {z : G}

section Local

variable (hs : LocalSetting G L z)
include hs

theorem z_mul_self : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [hs.order_z, pow_two] at h

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (z_mul_self hs)

theorem z_comm {l : G} (hl : l ∈ L) : z * l = l * z :=
  (mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl).symm

theorem z_not_mem_L : z ∉ L := by
  simpa using hs.conj_not_mem 1

theorem exists_of_comm {x : G} (hx : x * z = z * x) : ∃ l ∈ L, x = l ∨ x = l * z := by
  have hx' : x ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hx
  rw [hs.centralizer_eq] at hx'
  exact (mem_sup_zpowers_iff (z_mul_self hs) (fun k hk => z_comm hs hk)).1 hx'

theorem mul_self_ne (x : G) : x * x ≠ z := by
  intro h
  have hxz : x * z = z * x := by rw [← h, mul_assoc]
  obtain ⟨l, hl, rfl | rfl⟩ := exists_of_comm hs hxz
  · exact z_not_mem_L hs (h ▸ L.mul_mem hl hl)
  · apply z_not_mem_L hs
    have e : l * z * (l * z) = l * l := by
      calc l * z * (l * z) = l * (z * l) * z := by group
        _ = l * l * (z * z) := by rw [z_comm hs hl]; group
        _ = l * l := by rw [z_mul_self hs, mul_one]
    rw [← h, e]
    exact L.mul_mem hl hl

theorem z_mul_phiB (w : G) : z * phiB z w = w⁻¹ * z * w := by
  rw [phiB, ← mul_assoc, z_mul_self hs, one_mul]

theorem phiB_eq_one_iff {w : G} : phiB z w = 1 ↔ w * z = z * w := by
  constructor
  · intro h
    have h1 : w⁻¹ * z * w = z := by rw [← z_mul_phiB hs w, h, mul_one]
    calc w * z = w * (w⁻¹ * z * w) := by rw [h1]
      _ = z * w := by group
  · intro h
    have h1 : w⁻¹ * z * w = z := by rw [mul_assoc, ← h, inv_mul_cancel_left]
    rw [phiB, h1, z_mul_self hs]

theorem phiB_conj {h : G} (hh : h ∈ L) (w : G) :
    phiB z (h * w * h⁻¹) = h * phiB z w * h⁻¹ := by
  have hzh := z_comm hs hh
  have h1 : h⁻¹ * z * h = z := by rw [mul_assoc, hzh, inv_mul_cancel_left]
  calc phiB z (h * w * h⁻¹) = z * (h * w⁻¹ * (h⁻¹ * z * h) * w * h⁻¹) := by
        simp only [phiB]; group
    _ = (z * h) * (w⁻¹ * z * w) * h⁻¹ := by rw [h1]; group
    _ = h * phiB z w * h⁻¹ := by rw [hzh]; simp only [phiB]; group

variable (hBL : B ≤ L)
include hBL

theorem mem_egV_iff {x : G} : x ∈ egV B z ↔ ∃ b ∈ B, x = b ∨ x = b * z :=
  mem_sup_zpowers_iff (z_mul_self hs) (fun _ hb => z_comm hs (hBL hb))

private theorem conj_mem_egV_of {g : G} (hgz : g * z = z * g)
    (hgB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {x : G} (hx : x ∈ egV B z) : g * x * g⁻¹ ∈ egV B z := by
  obtain ⟨b, hb, hx' | hx'⟩ := (mem_egV_iff hs hBL).1 hx
  · rw [hx']
    exact B_le_egV (hgB b hb)
  · rw [hx']
    have hgz' : g * z * g⁻¹ = z := by rw [hgz, mul_inv_cancel_right]
    have e : g * (b * z) * g⁻¹ = g * b * g⁻¹ * z := by
      calc g * (b * z) * g⁻¹ = g * b * g⁻¹ * (g * z * g⁻¹) := by group
        _ = g * b * g⁻¹ * z := by rw [hgz']
    rw [e]
    exact mul_mem (B_le_egV (hgB b hb)) z_mem_egV

theorem mem_egM_of {g : G} (hgz : g * z = z * g) (hgB : g ∈ normalizer (B : Set G)) :
    g ∈ egM B z := by
  have hgB' : ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun b hb => (mem_normalizer_iff.1 hgB b).1 hb
  have hgiB : ∀ b ∈ B, g⁻¹ * b * g⁻¹⁻¹ ∈ B := fun b hb =>
    (mem_normalizer_iff.1 (inv_mem hgB) b).1 hb
  have hgiz : g⁻¹ * z = z * g⁻¹ := by
    calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hgz]
      _ = z * g⁻¹ := by group
  show g ∈ normalizer (egV B z : Set G)
  refine mem_normalizer_iff.2 fun x =>
    ⟨fun hx => conj_mem_egV_of hs hBL hgz hgB' hx, fun hx => ?_⟩
  have := conj_mem_egV_of hs hBL hgiz hgiB hx
  simpa [mul_assoc] using this

theorem z_mem_egM : z ∈ egM B z :=
  mem_egM_of hs hBL rfl (mem_normalizer_of_comm fun _ hb => z_comm hs (hBL hb))

theorem egNL_le_egM : egNL L B ≤ egM B z := fun _ hh =>
  mem_egM_of hs hBL (z_comm hs (mem_inf.1 hh).2).symm (mem_inf.1 hh).1

theorem conj_z_eq {n : G} (hn : n ∈ egM B z) : ∃ b ∈ B, n * z * n⁻¹ = z * b := by
  have h : n * z * n⁻¹ ∈ egV B z := (mem_normalizer_iff.1 hn z).1 z_mem_egV
  obtain ⟨b, hb, h | h⟩ := (mem_egV_iff hs hBL).1 h
  · exact (hs.conj_not_mem n (by rw [h]; exact hBL hb)).elim
  · exact ⟨b, hb, by rw [h, z_comm hs (hBL hb)]⟩

theorem phiB_mem {w : G} (hw : w ∈ egM B z) : phiB z w ∈ B := by
  obtain ⟨b, hb, h⟩ := conj_z_eq hs hBL (inv_mem hw)
  rw [inv_inv] at h
  rw [phiB, h, ← mul_assoc, z_mul_self hs, one_mul]
  exact hb

theorem phiB_mul (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {w w' : G} (hw : w ∈ egLam B z)
    (hw' : w' ∈ egLam B z) : phiB z (w * w') = phiB z w * phiB z w' := by
  have hm := phiB_mem hs hBL (mem_egLam.1 hw).1
  have hm' := phiB_mem hs hBL (mem_egLam.1 hw').1
  have hc : phiB z w * w' = w' * phiB z w := (mem_egLam.1 hw').2 _ hm
  calc phiB z (w * w') = z * (w'⁻¹ * (w⁻¹ * z * w) * w') := by simp only [phiB]; group
    _ = z * (w'⁻¹ * (z * phiB z w) * w') := by rw [z_mul_phiB hs w]
    _ = z * (w'⁻¹ * z * w') * (w'⁻¹ * (phiB z w * w')) := by group
    _ = phiB z w' * phiB z w := by rw [hc]; simp only [phiB]; group
    _ = phiB z w * phiB z w' := hBab _ hm' _ hm

theorem conj_mem_egLam {h : G} (hh : h ∈ egNL L B) {t : G} (ht : t ∈ egLam B z) :
    h * t * h⁻¹ ∈ egLam B z := by
  refine conj_mem_egLam_of (egNL_le_egM hs hBL hh) (fun b hb => ?_) ht
  have := (mem_normalizer_iff.1 (inv_mem (mem_inf.1 hh).1) b).1 hb
  rwa [inv_inv] at this

theorem egV_le_egLam (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : egV B z ≤ egLam B z := by
  have hz : z ∈ egLam B z :=
    mem_egLam.2 ⟨z_mem_egM hs hBL, fun b hb => (z_comm hs (hBL hb)).symm⟩
  refine sup_le (fun b hbB => mem_egLam.2 ⟨mem_egM_of hs hBL (z_comm hs (hBL hbB)).symm
    (le_normalizer hbB), fun b' hb' => hBab b' hb' b hbB⟩) ?_
  rw [zpowers_le]
  exact hz

theorem mem_egV_of_comm (hb : OctadBasics L B) {w : G} (hw : w ∈ egLam B z)
    (hwz : w * z = z * w) : w ∈ egV B z := by
  have hwc := (mem_egLam.1 hw).2
  obtain ⟨l, hl, hw' | hw'⟩ := exists_of_comm hs hwz
  · rw [hw'] at hwc ⊢
    exact B_le_egV (hb.cent l hl fun b hbB => (hwc b hbB).symm)
  · rw [hw'] at hwc ⊢
    have hlB : l ∈ B := by
      refine hb.cent l hl fun b hbB => ?_
      have h1 := hwc b hbB
      have hzb := z_comm hs (hBL hbB)
      have e : b * l * z = l * b * z := by
        calc b * l * z = b * (l * z) := by group
          _ = l * z * b := h1
          _ = l * (z * b) := by group
          _ = l * b * z := by rw [hzb]; group
      exact (mul_right_cancel e).symm
    exact mul_mem (B_le_egV hlB) z_mem_egV

theorem phiB_eq_one_of_mem {u : G} (hu : u ∈ B) : phiB z u = 1 :=
  (phiB_eq_one_iff hs).2 (z_comm hs (hBL hu)).symm

variable (hb : OctadBasics L B) (hcase : ¬ egM B z ≤ centralizer ({z} : Set G))
include hb hcase

theorem exists_conj_eq {b : G} (hbB : b ∈ B) : ∃ n ∈ egM B z, n * z * n⁻¹ = z * b := by
  by_cases hb1 : b = 1
  · exact ⟨1, one_mem _, by rw [hb1]; group⟩
  obtain ⟨m, hm, hmz⟩ : ∃ m ∈ egM B z, m ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hcase fun m hm => hcon m hm
  obtain ⟨b₀, hb₀, hmb⟩ := conj_z_eq hs hBL hm
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    apply hmz
    rw [mem_centralizer_singleton_iff]
    calc m * z = m * z * m⁻¹ * m := by group
      _ = z * m := by rw [hmb, mul_one]
  obtain ⟨h, hh, hhb⟩ := hb.trans b₀ hb₀ b hbB hb₀1 hb1
  refine ⟨h * m, mul_mem (egNL_le_egM hs hBL hh) hm, ?_⟩
  calc h * m * z * (h * m)⁻¹ = h * (m * z * m⁻¹) * h⁻¹ := by group
    _ = h * z * b₀ * h⁻¹ := by rw [hmb]; group
    _ = z * (h * b₀ * h⁻¹) := by rw [← z_comm hs (mem_inf.1 hh).2]; group
    _ = z * b := by rw [hhb]

theorem conj_mem_B {n : G} (hn : n ∈ egM B z) {b : G} (hbB : b ∈ B) : n * b * n⁻¹ ∈ B := by
  have h : n * b * n⁻¹ ∈ egV B z := (mem_normalizer_iff.1 hn b).1 (B_le_egV hbB)
  obtain ⟨b', hb', h | h⟩ := (mem_egV_iff hs hBL).1 h
  · rw [h]; exact hb'
  · exfalso
    obtain ⟨n', -, hn'⟩ := exists_conj_eq hs hBL hb hcase hb'
    apply hs.conj_not_mem (n⁻¹ * n')
    have e : (n⁻¹ * n') * z * (n⁻¹ * n')⁻¹ = b := by
      calc (n⁻¹ * n') * z * (n⁻¹ * n')⁻¹ = n⁻¹ * (n' * z * n'⁻¹) * n := by group
        _ = n⁻¹ * (n * b * n⁻¹) * n := by rw [hn', h, z_comm hs (hBL hb')]
        _ = b := by group
    rw [e]
    exact hBL hbB

theorem egM_le_normalizer : egM B z ≤ normalizer (B : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun b => ⟨fun hbB => conj_mem_B hs hBL hb hcase hn hbB,
    fun h => ?_⟩
  have := conj_mem_B hs hBL hb hcase (inv_mem hn) h
  simpa [mul_assoc] using this

theorem conj_mem_egLam_of_egM {n : G} (hn : n ∈ egM B z) {t : G} (ht : t ∈ egLam B z) :
    n * t * n⁻¹ ∈ egLam B z := by
  refine conj_mem_egLam_of hn (fun b hbB => ?_) ht
  have := conj_mem_B hs hBL hb hcase (inv_mem hn) hbB
  rwa [inv_inv] at this

theorem mul_self_mem {w : G} (hw : w ∈ egLam B z) : w * w ∈ B := by
  have hww : w * w ∈ egLam B z := mul_mem hw hw
  have h1 : phiB z (w * w) = 1 := by
    rw [phiB_mul hs hBL hb.elem.1 hw hw]
    exact hb.elem.2 _ (phiB_mem hs hBL (mem_egLam.1 hw).1)
  obtain ⟨b, hbB, h | h⟩ :=
    (mem_egV_iff hs hBL).1 (mem_egV_of_comm hs hBL hb hww ((phiB_eq_one_iff hs).1 h1))
  · rw [h]; exact hbB
  · exfalso
    obtain ⟨n, -, hn⟩ := exists_conj_eq hs hBL hb hcase hbB
    apply mul_self_ne hs (n⁻¹ * w * n)
    calc n⁻¹ * w * n * (n⁻¹ * w * n) = n⁻¹ * (w * w) * n := by group
      _ = n⁻¹ * (n * z * n⁻¹) * n := by rw [h, hn, z_comm hs (hBL hbB)]
      _ = z := by group

end Local

end CFSG.EvenSporadicStandard.M24Std.Octad
