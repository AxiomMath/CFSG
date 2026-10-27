module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecWreathJ
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.OddStandard.AltStdSec.Wreath
open scoped Pointwise

section Perm

variable {G : Type} [Group G] {K : Subgroup G} {n : ℕ}

theorem commute_rho_iff (e : K ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {w : G}
    (hw : w ∈ normalizer (K : Set G)) (a : ↥K) :
    ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
      centralizer ({rho e hn ⟨w, hw⟩} : Set (Equiv.Perm (Fin n))) ↔ w * (a : G) * w⁻¹ = a := by
  have hrc := rho_conj e hn ⟨w, hw⟩ (e a)
  rw [MulEquiv.symm_apply_apply] at hrc
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have h1 : rho e hn ⟨w, hw⟩ * ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
        (rho e hn ⟨w, hw⟩)⁻¹ = ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
      rw [← hc]
      exact mul_inv_cancel_right _ _
    rw [h1] at hrc
    have h2 : e a = e ⟨w * (a : G) * w⁻¹, (mem_normalizer_iff.mp hw _).mp a.2⟩ :=
      Subtype.ext hrc
    have h3 := e.injective h2
    exact (congrArg (Subtype.val : ↥K → G) h3).symm
  · intro hwa
    have h2 : (⟨w * (a : G) * w⁻¹, (mem_normalizer_iff.mp hw _).mp a.2⟩ : ↥K) = a :=
      Subtype.ext hwa
    rw [h2] at hrc
    exact (mul_inv_eq_iff_eq_mul.1 hrc).symm

theorem card_centralizer_perm_dvd_two_mul (e : K ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    {w : G} (hw : w ∈ normalizer (K : Set G)) :
    Nat.card (centralizer ({rho e hn ⟨w, hw⟩} : Set (Equiv.Perm (Fin n)))) ∣
      2 * Nat.card (K ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  classical
  set π := rho e hn ⟨w, hw⟩ with hπ
  have h1 := card_dvd_two_mul_inf_alternatingGroup (centralizer ({π} : Set (Equiv.Perm (Fin n))))
  refine h1.trans (Nat.mul_dvd_mul_left 2 (dvd_of_eq ?_))
  let φ : ↥(K ⊓ centralizer ({w} : Set G)) →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (Subgroup.inclusion (inf_le_left : K ⊓ centralizer ({w} : Set G) ≤ K)))
  have hφ : Function.Injective φ := by
    intro a b hab
    have h2 : e ⟨a, a.2.1⟩ = e ⟨b, b.2.1⟩ := Subtype.ext hab
    have h3 := e.injective h2
    exact Subtype.ext (congrArg (Subtype.val : ↥K → G) h3)
  have hrange : φ.range =
      centralizer ({π} : Set (Equiv.Perm (Fin n))) ⊓ alternatingGroup (Fin n) := by
    ext σ
    constructor
    · rintro ⟨a, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (e ⟨a, a.2.1⟩).2⟩
      have hwa : w * (a : G) * w⁻¹ = a := by
        have := mem_centralizer_singleton_iff.1 a.2.2
        calc w * (a : G) * w⁻¹ = a * w * w⁻¹ := by rw [← this]
          _ = a := by group
      exact (commute_rho_iff e hn hw ⟨a, a.2.1⟩).2 hwa
    · intro hσ
      obtain ⟨hσC, hσA⟩ := Subgroup.mem_inf.1 hσ
      set b : ↥K := e.symm ⟨σ, hσA⟩ with hb
      have hbe : e b = ⟨σ, hσA⟩ := by simp [hb]
      have hbw : w * (b : G) * w⁻¹ = b := by
        refine (commute_rho_iff e hn hw b).1 ?_
        rw [hbe]
        exact hσC
      have hbC : (b : G) ∈ centralizer ({w} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc (b : G) * w = (w * (b : G) * w⁻¹) * w := by rw [hbw]
          _ = w * b := by group
      refine ⟨⟨b, Subgroup.mem_inf.2 ⟨b.2, hbC⟩⟩, ?_⟩
      show ((e ⟨b, b.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = σ
      rw [show (⟨(b : G), b.2⟩ : ↥K) = b from rfl, hbe]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

end Perm

section Fixes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}
  {H : Subgroup G}

private theorem padicValNat_two_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat 2 a ≤ padicValNat 2 b :=
  (padicValNat_dvd_iff_le hb).1 (pow_padicValNat_dvd.trans h)

omit [Finite G] in
private theorem zpow_eq_one_or_self_of_sq {w : G} (hw2 : w * w = 1) (k : ℤ) :
    w ^ k = 1 ∨ w ^ k = w := by
  have hw2' : w ^ 2 = 1 := by rw [sq]; exact hw2
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    simp [hw2']
  · right
    rw [zpow_add, zpow_mul, zpow_one]
    simp [hw2']

theorem false_of_fixes_pair (hn : 11 ≤ n) (hH : WreathPair L z n H) {w : G} (hw2 : w * w = 1)
    (hwD : ∀ a ∈ H, ∀ b ∈ cjSub z H, w ≠ a * b) (hwH : cjSub w H = H)
    (hwH' : cjSub w (cjSub z H) = cjSub z H)
    (hCw : Nat.card (centralizer ({w} : Set G)) = 2 * n.factorial) : False := by
  classical
  obtain ⟨e⟩ := hH.iso
  set H' : Subgroup G := cjSub z H with hH'def
  have hw1 : w ≠ 1 := fun h1 => hwD 1 H.one_mem 1 H'.one_mem (by simp [h1])
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hwN : w ∈ normalizer (H : Set G) := mem_normalizer_of_cjSub_eq hwH
  have hwN' : w ∈ normalizer (H' : Set G) := mem_normalizer_of_cjSub_eq hwH'
  let e' : ↥H' ≃* alternatingGroup (Fin n) :=
    (Subgroup.equivMapOfInjective H (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective).symm.trans e
  set X₁ : Subgroup G := H ⊓ centralizer ({w} : Set G) with hX₁
  set X₂ : Subgroup G := H' ⊓ centralizer ({w} : Set G) with hX₂
  have hn8 : 8 ≤ n := by omega
  set π₁ := rho e hn8 ⟨w, hwN⟩ with hπ₁
  set π₂ := rho e' hn8 ⟨w, hwN'⟩ with hπ₂
  have hπ₁2 : π₁ * π₁ = 1 := by
    rw [hπ₁, ← map_mul]
    have : (⟨w, hwN⟩ * ⟨w, hwN⟩ : normalizer (H : Set G)) = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hπ₂2 : π₂ * π₂ = 1 := by
    rw [hπ₂, ← map_mul]
    have : (⟨w, hwN'⟩ * ⟨w, hwN'⟩ : normalizer (H' : Set G)) = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hfc3 := padicValNat_card_centralizer_add hn π₁ π₂ hπ₁2 hπ₂2
  have hd₁ := card_centralizer_perm_dvd_two_mul e hn8 hwN
  have hd₂ := card_centralizer_perm_dvd_two_mul e' hn8 hwN'
  have hX₁pos : Nat.card X₁ ≠ 0 := Nat.card_pos.ne'
  have hX₂pos : Nat.card X₂ ≠ 0 := Nat.card_pos.ne'
  have hv₁ : padicValNat 2 (Nat.card (centralizer ({π₁} : Set (Equiv.Perm (Fin n))))) ≤
      1 + padicValNat 2 (Nat.card X₁) := by
    have := padicValNat_two_le_of_dvd (mul_ne_zero two_ne_zero hX₁pos) hd₁
    rwa [padicValNat.mul two_ne_zero hX₁pos, padicValNat_self] at this
  have hv₂ : padicValNat 2 (Nat.card (centralizer ({π₂} : Set (Equiv.Perm (Fin n))))) ≤
      1 + padicValNat 2 (Nat.card X₂) := by
    have := padicValNat_two_le_of_dvd (mul_ne_zero two_ne_zero hX₂pos) hd₂
    rwa [padicValNat.mul two_ne_zero hX₂pos, padicValNat_self] at this
  have hcomm12 : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := fun a ha b hb => hH.comm' ha.1 hb.1
  have hnorm : X₂ ≤ normalizer (X₁ : Set G) := fun b hb => by
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro a ha
    exact hcomm12 a ha b hb
  have hdisj : Disjoint X₁ X₂ := by
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    exact hH.eq_one_of_mem_inf (by omega) hx1.1 hx2.1
  have hY : Nat.card (X₁ ⊔ X₂ : Subgroup G) = Nat.card X₁ * Nat.card X₂ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X₁ X₂ hnorm hdisj
  set Y : Subgroup G := X₁ ⊔ X₂ with hYdef
  have hYC : Y ≤ centralizer ({w} : Set G) := sup_le inf_le_right inf_le_right
  have hwY : zpowers w ≤ normalizer (Y : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (s := (Y : Set G)))
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hYC hy)
  have hdisj2 : Disjoint Y (zpowers w) := by
    rw [Subgroup.disjoint_def]
    intro x hxY hxw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxw
    rcases zpow_eq_one_or_self_of_sq hw2 k with hk | hk
    · exact hk
    · exfalso
      rw [hk] at hxY
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left X₁ X₂ hnorm
      have : w ∈ (X₁ : Set G) * (X₂ : Set G) := by rw [← hset]; exact hxY
      obtain ⟨a, ha, b, hb, hab⟩ := this
      exact hwD a ha.1 b hb.1 hab.symm
  have hcardw : Nat.card (zpowers w) = 2 := by rw [Nat.card_zpowers, hord]
  have hsup : Nat.card (Y ⊔ zpowers w : Subgroup G) = Nat.card Y * Nat.card (zpowers w) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y (zpowers w) hwY hdisj2
  have hle : Y ⊔ zpowers w ≤ centralizer ({w} : Set G) :=
    sup_le hYC (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hsup, hY, hcardw, hCw] at hdvd
  have hdvd' : Nat.card X₁ * Nat.card X₂ ∣ n.factorial := by
    rw [mul_comm 2 n.factorial] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
  have hv₃ : padicValNat 2 (Nat.card X₁) + padicValNat 2 (Nat.card X₂) ≤
      padicValNat 2 n.factorial := by
    have := padicValNat_two_le_of_dvd (Nat.factorial_ne_zero n) hdvd'
    rwa [padicValNat.mul hX₁pos hX₂pos] at this
  omega

omit [Finite G] in
theorem card_centralizer_conj (z g : G) :
    Nat.card (centralizer ({g⁻¹ * z * g} : Set G)) = Nat.card (centralizer ({z} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (fun x => ?_))
  show x ∈ centralizer ({g⁻¹ * z * g} : Set G) ↔
    (MulAut.conj g) x ∈ centralizer ({z} : Set G)
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h1
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [h1]
      _ = z * (g * x * g⁻¹) := by group
  · intro h1
    calc x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * z * g * x := by group

theorem false_of_conj_fixes (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hn : 11 ≤ n) (hH : WreathPair L z n H) (g : G)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 2 * n.factorial)
    (hwH : cjSub (g⁻¹ * z * g) H = H)
    (hwH' : cjSub (g⁻¹ * z * g) (cjSub z H) = cjSub z H) : False := by
  have hz2 := d.mul_self
  have hw2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  by_cases hD : ∃ a ∈ H, ∃ b ∈ cjSub z H, g⁻¹ * z * g = a * b
  · obtain ⟨a, ha, b, ⟨b₀, hb₀, rfl⟩, hab⟩ := hD
    obtain ⟨e⟩ := hH.iso
    have hc : WConfig H z := hH.wconfig (by omega) hz2
    have hJ : J (g⁻¹ * z * g) :=
      hc.J_of_mem_prodSub e (by omega) (le_refl H)
        ⟨a, ha, b₀, hb₀, by simpa [Phi, MulAut.conj_apply] using hab⟩ hw2
    exact not_J_z h d hQ2 ((J_conj g⁻¹).1 (by rw [inv_inv]; exact hJ))
  · push Not at hD
    exact false_of_fixes_pair hn hH hw2 (fun a ha b hb => hD a ha b hb) hwH hwH'
      (by rw [card_centralizer_conj, hCz])

end Fixes

end CFSG.OddStandard.AltStdSec
