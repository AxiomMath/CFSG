module

public import CFSG.Certificates.Kernel.MaxD2.Basic
public import Certificates.Data.Kernel.MaxD2.Block
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep)
open CFSG.AGLEmbedding.MaxD2 (dcoset conjStab card_dcoset_mul disjoint_dcoset dcoset_subset)

theorem rowBitK_sound {n : Nat} {B : Nat → Nat} (h : rowBitK n B = true) :
    ∀ p < n, r32 B p ≤ 1 := fun p hp =>
  Nat.ble_eq.mp ((PK.allN_iff.1 h) p hp)

theorem blockK_sound {n w s G : Nat} {B : Nat → Nat} (h : blockK n w B G s = true) :
    ∀ p < n, r32 B (pg w (mask w) G p) = Nat.xor (r32 B p) s := fun p hp =>
  Nat.eq_of_beq_eq_true ((PK.allN_iff.1 h) p hp)

theorem blockK_perm {n w s G : Nat} {B : Nat → Nat} {σ : Equiv.Perm (Fin n)}
    (hσ : TabRep (unpack n w G) σ) (h : blockK n w B G s = true) :
    ∀ p : Fin n, r32 B (σ p) = Nat.xor (r32 B p) s := fun p => by
  rw [← hσ.apply p, get_u p.2]
  exact blockK_sound h p p.2

theorem notPowK_sound {n w m c x : Nat} (h : notPowK n w m c x = true) :
    ∀ k < m, c ≠ pw n w x (k + 1) := fun k hk e => by
  have h1 := bnot_e ((PK.allN_iff.1 h) k hk)
  rw [e, Nat.beq_refl] at h1
  exact absurd h1 (by decide)

theorem movesK_sound {n w m g gi x : Nat} (h : movesK n w m g gi x = true) :
    ∀ k < m, pcomp n w (mask w) (pcomp n w (mask w) g x) gi ≠ pw n w x (k + 1) :=
  notPowK_sound h

theorem tab_pcomp {n w p q : Nat} (hp : Cn n w p) (hq : Cn n w q) {P Q : Equiv.Perm (Fin n)}
    (hP : TabRep (unpack n w p) P) (hQ : TabRep (unpack n w q) Q) :
    TabRep (unpack n w (pcomp n w (mask w) p q)) (P * Q) := by
  rw [← comp_u hp hq]
  exact hP.comp hQ

theorem tab_pw {n w x : Nat} (hn : szOK n w = true) (hx : Cn n w x) {X : Equiv.Perm (Fin n)}
    (hX : TabRep (unpack n w x) X) (e : Nat) : TabRep (unpack n w (pw n w x e)) (X ^ e) := by
  rw [← powT_u hn hx]
  exact CFSG.AGLEmbedding.FusD2.powT_rep hX e

theorem movesK_perm {n w m g gi x : Nat} (hn : szOK n w = true) (hg : Cn n w g)
    (hgi : Cn n w gi) (hx : Cn n w x) {G X : Equiv.Perm (Fin n)} (hG : TabRep (unpack n w g) G)
    (hGi : TabRep (unpack n w gi) G⁻¹) (hX : TabRep (unpack n w x) X)
    (h : movesK n w m g gi x = true) : ∀ k < m, G * X * G⁻¹ ≠ X ^ (k + 1) := fun k hk e => by
  have t1 := tab_pcomp (cc hg hx) hgi (tab_pcomp hg hx hG hX) hGi
  rw [e] at t1
  exact movesK_sound h k hk (u_inj (cc (cc hg hx) hgi) (pw_canon hn hx _)
    (t1.tab_eq (tab_pw hn hx hX (k + 1))))

theorem powNe_perm {n w c e : Nat} (hn : szOK n w = true) (hc : Cn n w c)
    {C : Equiv.Perm (Fin n)} (hC : TabRep (unpack n w c) C)
    (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (pw n w c e) (pidn n w)) = true) :
    C ^ e ≠ 1 := fun e1 => by
  have t1 := tab_pw hn hc hC e
  rw [e1] at t1
  have t2 : TabRep (unpack n w (pidn n w)) (1 : Equiv.Perm (Fin n)) := by
    rw [← id_u hn]
    exact TabRep.idTab
  have := u_inj (pw_canon hn hc e) (pidn_canon hn) (t1.tab_eq t2)
  have h1 := bnot_e h
  rw [this, Nat.beq_refl] at h1
  exact absurd h1 (by decide)

section Group

variable {Q : Type*} [Group Q]

theorem two_mul_card_le_of_not_mem [Finite Q] {H K S : Subgroup Q} (hHK : H ≤ K) (hHS : H ≤ S)
    {k : Q} (hk : k ∈ K) (hkS : k ∉ S) : 2 * Nat.card H ≤ Nat.card K := by
  have hLK : K ⊓ S ≤ K := inf_le_left
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hLK
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    omega
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hd
    have heq := Subgroup.eq_of_le_of_card_ge hLK hd.le
    exact hkS (heq.symm ▸ hk : k ∈ K ⊓ S).2
  have hHL : Nat.card H ≤ Nat.card (K ⊓ S : Subgroup Q) :=
    Subgroup.card_le_of_le (le_inf hHK hHS)
  rw [hd]
  calc 2 * Nat.card H ≤ 2 * Nat.card (K ⊓ S : Subgroup Q) := by omega
    _ ≤ Nat.card (K ⊓ S : Subgroup Q) * d := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)

@[expose] def setStab {α : Type*} (O : Set α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ p, g p ∈ O ↔ p ∈ O}
  mul_mem' {a b} ha hb p := by
    rw [Equiv.Perm.mul_apply, ha, hb]
  one_mem' p := Iff.rfl
  inv_mem' {g} hg p := by
    have e : g (g⁻¹ p) = p := Equiv.apply_symm_apply g p
    have h := hg (g⁻¹ p)
    rw [e] at h
    exact h.symm

theorem two_mul_card_le_of_block {α : Type*} [Finite α] {K : Subgroup (Equiv.Perm α)}
    {A : Set (Equiv.Perm α)} (O : Set α) (hA : ∀ g ∈ A, ∀ p, g p ∈ O ↔ p ∈ O)
    (hAK : Subgroup.closure A ≤ K) {t : Equiv.Perm α} (htK : t ∈ K)
    (ht : ∀ p, t p ∈ O ↔ p ∉ O) {p₀ : α} (hp₀ : p₀ ∈ O) :
    2 * Nat.card (Subgroup.closure A) ≤ Nat.card K := by
  refine two_mul_card_le_of_not_mem hAK ((Subgroup.closure_le _).2 hA) htK
    (S := setStab O) fun hS => ?_
  have h1 := (hS p₀).2 hp₀
  exact (ht p₀).1 h1 hp₀

theorem sum_dcoset_le [Finite Q] {G N : Subgroup Q} (hNG : N ≤ G) (g : ℕ → Q) (r : ℕ)
    (hgG : ∀ i ≤ r, g i ∈ G)
    (hdisj : ∀ i ≤ r, ∀ j ≤ r, i < j → ∀ a ∈ N, (g i)⁻¹ * a * g j ∉ N) :
    ∑ i ∈ Finset.range (r + 1), Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) ≤
      Nat.card G := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let Df : ℕ → Finset Q := fun i => (dcoset N (g i)).toFinset
  have hcard : ∀ i, (Df i).card =
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) := by
    intro i
    have h1 := card_dcoset_mul N (g i)
    have hc : 0 < Nat.card (conjStab N (g i)) := Nat.card_pos
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact (Nat.div_eq_of_eq_mul_left hc h1.symm).symm
  have hdisjf : ∀ i ∈ Finset.range (r + 1), ∀ j ∈ Finset.range (r + 1), i ≠ j →
      Disjoint (Df i) (Df j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    simp only [Df, Set.disjoint_toFinset]
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_dcoset (hdisj i (by omega) j (by omega) h)
    · exact (disjoint_dcoset (hdisj j (by omega) i (by omega) h)).symm
  let Gf : Finset Q := (G : Set Q).toFinset
  have hGf : Gf.card = Nat.card G := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have hsub : (Finset.range (r + 1)).biUnion Df ⊆ Gf := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [Finset.mem_range] at hi
    simp only [Df, Set.mem_toFinset] at hxi
    simpa [Gf] using dcoset_subset hNG (hgG i (by omega)) hxi
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisjf, hGf] at hle
  calc _ = ∑ i ∈ Finset.range (r + 1), (Df i).card :=
        Finset.sum_congr rfl fun i _ => (hcard i).symm
    _ ≤ Nat.card G := hle

theorem exists_mul_zpow_of_mem_closure {R : Subgroup Q} {t : Q}
    (ht : t ∈ Subgroup.normalizer (R : Set Q)) {a : Q}
    (ha : a ∈ Subgroup.closure ((R : Set Q) ∪ {t})) : ∃ r ∈ R, ∃ j : ℤ, a = r * t ^ j := by
  have hz : ∀ j : ℤ, t ^ j ∈ Subgroup.normalizer (R : Set Q) := fun j =>
    Subgroup.zpow_mem _ ht j
  have hconj : ∀ j : ℤ, ∀ s ∈ R, t ^ j * s * (t ^ j)⁻¹ ∈ R := fun j s hs =>
    (Subgroup.mem_normalizer_iff.1 (hz j) s).1 hs
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨1, R.one_mem, 1, by simp [hx]⟩
  | one => exact ⟨1, R.one_mem, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr, i, rfl⟩ := hx
    obtain ⟨s, hs, j, rfl⟩ := hy
    refine ⟨r * (t ^ i * s * (t ^ i)⁻¹), R.mul_mem hr (hconj i s hs), i + j, ?_⟩
    rw [zpow_add]
    group
  | inv x _ hx =>
    obtain ⟨r, hr, i, rfl⟩ := hx
    refine ⟨t ^ (-i) * r⁻¹ * (t ^ (-i))⁻¹, hconj (-i) _ (R.inv_mem hr), -i, ?_⟩
    group

theorem conj_mem_mul_of_mem_closure {R : Subgroup Q} {t : Q}
    (ht : t ∈ Subgroup.normalizer (R : Set Q)) {a : Q}
    (ha : a ∈ Subgroup.closure ((R : Set Q) ∪ {t})) : a⁻¹ * t * a * t⁻¹ ∈ R := by
  obtain ⟨r, hr, j, rfl⟩ := exists_mul_zpow_of_mem_closure ht ha
  have hz : t ^ (-j) ∈ Subgroup.normalizer (R : Set Q) := Subgroup.zpow_mem _ ht (-j)
  have h1 : t * r * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 ht r).1 hr
  have h2 : r⁻¹ * (t * r * t⁻¹) ∈ R := R.mul_mem (R.inv_mem hr) h1
  have h3 := (Subgroup.mem_normalizer_iff.1 hz _).1 h2
  have e : (r * t ^ j)⁻¹ * t * (r * t ^ j) * t⁻¹ =
      t ^ (-j) * (r⁻¹ * (t * r * t⁻¹)) * (t ^ (-j))⁻¹ := by
    group
  rw [e]
  exact h3

theorem centralizer_eq_zpowers_of_dcosets {U M R : Subgroup Q} {t w : Q} (htU : t ∈ U)
    (ht : t ∈ Subgroup.normalizer (R : Set Q)) (hM : M ≤ Subgroup.closure ((R : Set Q) ∪ {t}))
    (hcover : ∀ y ∈ U, y ∈ M ∨ y ∈ dcoset M w)
    (hfix : ∀ r ∈ R, t * r = r * t → r = 1)
    (hw : ∀ r ∈ R, w * (r * t) * w⁻¹ * t⁻¹ ∉ R) :
    U ⊓ Subgroup.centralizer {t} = Subgroup.zpowers t := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgU, hgC⟩ := hg
    have hgt : t * g = g * t := (Subgroup.mem_centralizer_singleton_iff.1 hgC).symm
    rcases hcover g hgU with hgM | ⟨a, ha, b, hb, rfl⟩
    · obtain ⟨r, hr, j, rfl⟩ := exists_mul_zpow_of_mem_closure ht (hM hgM)
      have hrt : t * r = r * t := by
        have e : t * r * t ^ j = r * t * t ^ j := by
          calc t * r * t ^ j = t * (r * t ^ j) := by group
            _ = r * t ^ j * t := hgt
            _ = r * t * t ^ j := by rw [mul_assoc, mul_assoc, ← (Commute.self_zpow t j).eq]
        exact mul_right_cancel e
      rw [hfix r hr hrt, one_mul]
      exact Subgroup.zpow_mem_zpowers t j
    · exfalso
      have hb' : b⁻¹ ∈ Subgroup.closure ((R : Set Q) ∪ {t}) := hM (M.inv_mem hb)
      obtain hs := conj_mem_mul_of_mem_closure ht (hM ha)
      have hr := conj_mem_mul_of_mem_closure ht hb'
      refine hw _ hr ?_
      have e : w * ((b⁻¹)⁻¹ * t * b⁻¹ * t⁻¹ * t) * w⁻¹ * t⁻¹ = a⁻¹ * t * a * t⁻¹ := by
        have e2 : w * (b * t * b⁻¹) * w⁻¹ = a⁻¹ * t * a := by
          calc w * (b * t * b⁻¹) * w⁻¹ = a⁻¹ * ((a * w * b) * t * (a * w * b)⁻¹) * a := by group
            _ = a⁻¹ * (t * (a * w * b) * (a * w * b)⁻¹) * a := by rw [← hgt]
            _ = a⁻¹ * t * a := by group
        calc w * ((b⁻¹)⁻¹ * t * b⁻¹ * t⁻¹ * t) * w⁻¹ * t⁻¹ = w * (b * t * b⁻¹) * w⁻¹ * t⁻¹ := by
              group
          _ = a⁻¹ * t * a * t⁻¹ := by rw [e2]
      rw [e]
      exact hs
  · rw [Subgroup.zpowers_le]
    exact ⟨htU, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem normalizer_inf_le_of_reps {G N : Subgroup Q} {Y : Set Q} (g : ℕ → Q) (r : ℕ)
    (hg0 : g 0 = 1) (hN : N ≤ Subgroup.normalizer Y)
    (hcover : ∀ y ∈ G, ∃ i ≤ r, y ∈ dcoset N (g i))
    (hmove : ∀ i, 1 ≤ i → i ≤ r → g i ∉ Subgroup.normalizer Y) :
    Subgroup.normalizer Y ⊓ G ≤ N := by
  rintro y ⟨hyY, hyG⟩
  obtain ⟨i, hi, a, ha, b, hb, rfl⟩ := hcover y hyG
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [hg0, mul_one]
    exact N.mul_mem ha hb
  · exfalso
    refine hmove i hi0 hi ?_
    have e : g i = a⁻¹ * (a * g i * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hN ha)) hyY)
      (Subgroup.inv_mem _ (hN hb))

theorem not_mem_normalizer_zpowers [Finite Q] {z g : Q} {m : ℕ} (hz : z ≠ 1)
    (hm : z ^ (m + 1) = 1) (h : ∀ k < m, g * z * g⁻¹ ≠ z ^ (k + 1)) :
    g ∉ Subgroup.normalizer (Subgroup.zpowers z : Set Q) := fun hg => by
  have hc : g * z * g⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_zpowers z)
  have hpos : 0 < orderOf z := orderOf_pos z
  have hle : orderOf z ≤ m + 1 := orderOf_le_of_pow_eq_one (by omega) hm
  obtain ⟨j, hj, e⟩ := CFSG.AGLEmbedding.MaxD2.exists_pow_lt_of_mem_zpowers hc hpos
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero] at e
    apply hz
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, ← e]
    group
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact h k (by omega) e.symm

end Group

end CFSG.KS.MaxD2

end
