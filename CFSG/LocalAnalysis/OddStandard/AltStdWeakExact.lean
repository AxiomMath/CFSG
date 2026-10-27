module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupConsAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakShape

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

section Count

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem card_mul_card_le_of_weakShape (h : WeakShape t A m) (hm : 5 ≤ m) :
    Nat.card (centralizer (A : Set X) ⊓ centralizer ({t} : Set X) : Subgroup X) * Nat.card A ≤
      Nat.card (centralizer ({t} : Set X)) := by
  set D := centralizer (A : Set X) ⊓ centralizer ({t} : Set X) with hD
  obtain ⟨e⟩ := h.iso
  have hZ : center A = ⊥ := center_eq_bot_of_alt (by omega) e
  have hDA : ∀ x ∈ D, x ∈ A → x = 1 := by
    intro x hxD hxA
    have : (⟨x, hxA⟩ : A) ∈ center A := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 hxD.1 y y.2)
    rw [hZ, mem_bot] at this
    exact congrArg Subtype.val this
  let f : D × A → centralizer ({t} : Set X) :=
    fun p => ⟨(p.1 : X) * p.2, mul_mem p.1.2.2 (h.le_cent p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨d, a⟩ ⟨d', a'⟩ hda
    have h1 : (d : X) * a = d' * a' := congrArg Subtype.val hda
    have h2 : (d' : X)⁻¹ * d = a' * (a : X)⁻¹ := by
      calc (d' : X)⁻¹ * d = (d' : X)⁻¹ * (d * a) * (a : X)⁻¹ := by group
        _ = (d' : X)⁻¹ * (d' * a') * (a : X)⁻¹ := by rw [h1]
        _ = a' * (a : X)⁻¹ := by group
    have h3 : (d' : X)⁻¹ * d = 1 :=
      hDA _ (mul_mem (inv_mem d'.2) d.2) (by rw [h2]; exact mul_mem a'.2 (inv_mem a.2))
    have hdd : (d : X) = d' := by
      calc (d : X) = d' * ((d' : X)⁻¹ * d) := by group
        _ = d' := by rw [h3, mul_one]
    have haa : (a : X) = a' := by
      rw [hdd] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hdd) (Subtype.ext haa)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem WeakShape.exactShape_of_card_centralizer_le (h : WeakShape t A m) (hm : 5 ≤ m)
    (hC : Nat.card (centralizer ({t} : Set X)) ≤ 2 * m.factorial) : ExactShape t A m := by
  obtain ⟨e⟩ := h.iso
  have hcA : Nat.card A = m.factorial / 2 := card_eq_of_equiv_alt (by omega) e
  have h1 := card_mul_card_le_of_weakShape h hm
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h3 : 0 < m.factorial / 2 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) h2) (by norm_num)
  have h4 : 2 * m.factorial = 4 * (m.factorial / 2) := by
    obtain ⟨c, hc⟩ := h2
    rw [hc, Nat.mul_div_cancel_left c (by norm_num)]
    ring
  rw [hcA] at h1
  exact h.exactShape_of_card_le_four
    (Nat.le_of_mul_le_mul_right (h1.trans (hC.trans h4.le)) h3)

end Count

section Alt

theorem exists_even_commuting_involution {N : ℕ} {τ : Perm (Fin N)} (hτ : τ * τ = 1)
    {a c : Fin N} (ha : τ a ≠ a) (hc : τ c ≠ c) (hac : c ≠ a) (hacτ : c ≠ τ a) :
    ∃ g : Perm (Fin N), g ∈ alternatingGroup (Fin N) ∧ g * τ = τ * g ∧ g ≠ 1 ∧ g ≠ τ ∧
      g * g = 1 ∧ ∀ x, g x ≠ x → τ x ≠ x := by
  have hτ2 := perm_involution_apply_apply hτ
  have hab : a ≠ τ a := ha.symm
  have hcd : c ≠ τ c := hc.symm
  have had : a ≠ τ c := fun h => hacτ (by rw [h, hτ2])
  have hbd : τ a ≠ τ c := fun h => hac (τ.injective h).symm
  have hdisj : (swap a c).Disjoint (swap (τ a) (τ c)) := by
    apply Perm.disjoint_swap_swap
    simp [hac.symm, hab, had, hacτ, hcd, hbd]
  have h1 : τ * swap a c = swap (τ a) (τ c) * τ := mul_swap_eq_swap_mul τ a c
  have h2 : τ * swap (τ a) (τ c) = swap a c * τ := by
    rw [mul_swap_eq_swap_mul, hτ2, hτ2]
  refine ⟨swap a c * swap (τ a) (τ c), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hac.symm, Perm.sign_swap hbd]
    decide
  · calc swap a c * swap (τ a) (τ c) * τ = swap a c * (swap (τ a) (τ c) * τ) := mul_assoc _ _ _
      _ = swap a c * (τ * swap a c) := by rw [h1]
      _ = (swap a c * τ) * swap a c := (mul_assoc _ _ _).symm
      _ = (τ * swap (τ a) (τ c)) * swap a c := by rw [h2]
      _ = τ * (swap (τ a) (τ c) * swap a c) := mul_assoc _ _ _
      _ = τ * (swap a c * swap (τ a) (τ c)) := by rw [hdisj.commute.eq]
  · intro h
    have h' : (swap a c * swap (τ a) (τ c)) a = a := by rw [h]; rfl
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left] at h'
    exact hac h'
  · intro h
    have h' : (swap a c * swap (τ a) (τ c)) a = τ a := by rw [h]
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left] at h'
    exact hacτ h'
  · calc swap a c * swap (τ a) (τ c) * (swap a c * swap (τ a) (τ c))
        = swap a c * (swap (τ a) (τ c) * swap a c) * swap (τ a) (τ c) := by group
      _ = swap a c * (swap a c * swap (τ a) (τ c)) * swap (τ a) (τ c) := by
          rw [hdisj.commute.eq]
      _ = (swap a c * swap a c) * (swap (τ a) (τ c) * swap (τ a) (τ c)) := by group
      _ = 1 := by rw [swap_mul_self, swap_mul_self, one_mul]
  · intro x hx hτx
    apply hx
    have hxa : x ≠ a := fun h => ha (by rw [← h]; exact hτx)
    have hxb : x ≠ τ a := fun h => perm_involution_ne_self_of_image hτ ha (by rw [← h]; exact hτx)
    have hxc : x ≠ c := fun h => hc (by rw [← h]; exact hτx)
    have hxd : x ≠ τ c := fun h => perm_involution_ne_self_of_image hτ hc (by rw [← h]; exact hτx)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxd, swap_apply_of_ne_of_ne hxa hxc]

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem card_centralizer_le_of_alt {W : Subgroup X} [W.Normal] {N : ℕ} (h : WeakShape t A m)
    (hm : 7 ≤ m) (hAW : A ≤ W) (hCW : centralizer (W : Set X) = ⊥)
    (hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)))
    (eW : W ≃* alternatingGroup (Fin N)) :
    Nat.card (centralizer ({t} : Set X)) ≤ 2 * m.factorial := by
  classical
  obtain ⟨eA⟩ := h.iso
  have hcA : Nat.card A = m.factorial / 2 := card_eq_of_equiv_alt (by omega) eA
  have hNm : m ≤ N := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : Nat.card A ≤ Nat.card (Perm (Fin N)) :=
      (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hAW)).trans
        ((Nat.card_congr eW.toEquiv ▸ Subgroup.card_le_card_group (alternatingGroup (Fin N))))
    rw [hcA, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    have h2 : N.factorial ≤ (m - 1).factorial := Nat.factorial_le (by omega)
    have h3 : 2 * (m - 1).factorial + 2 ≤ m.factorial := by
      have := Nat.mul_factorial_pred (show m ≠ 0 by omega)
      have h5 := Nat.factorial_pos (m - 1)
      nlinarith
    have h4 : (m - 1).factorial < m.factorial / 2 := by omega
    omega
  have hN5 : 5 ≤ N := by omega
  have hN6 : N ≠ 6 := by omega
  obtain ⟨ι, hι, hιW⟩ := lookup_exists_perm_embedding W hCW hN5 hN6 eW
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.order, sq] at this
    exact this
  have hτ2 : ι t * ι t = 1 := by rw [← map_mul, ht2, map_one]
  have hτ1 : ι t ≠ 1 := by
    intro h1
    have : t = 1 := hι (by rw [h1, map_one])
    have h2 := h.order
    rw [this, orderOf_one] at h2
    omega
  set τ := ι t with hτdef
  have hmemA : ∀ a ∈ A, ι a ∈ alternatingGroup (Fin N) := by
    intro a ha
    rw [show ι a = _ from hιW ⟨a, hAW ha⟩]
    exact (eW ⟨a, hAW ha⟩).2
  have hcommA : ∀ a ∈ A, ι a * τ = τ * ι a := by
    intro a ha
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (h.le_cent ha)]
  have hA'A : A.map ι ≤ alternatingGroup (Fin N) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hmemA a ha
  have hA'c : A.map ι ≤ centralizer ({τ} : Set (Perm (Fin N))) := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hcommA a ha)
  have hCWt : (W ⊓ centralizer ({t} : Set X)).map ι =
      alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · rw [show ι y = _ from hιW ⟨y, hy.1⟩]
        exact (eW ⟨y, hy.1⟩).2
      · rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy.2]
    · rintro ⟨hx, hxc⟩
      obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hx
      refine ⟨w, ⟨w.2, mem_centralizer_singleton_iff.2 ?_⟩, hw⟩
      apply hι
      rw [map_mul, map_mul, hw]
      exact mem_centralizer_singleton_iff.1 hxc
  have hAcomp : CFSG.IsComponent
      ((A.map ι).subgroupOf
        (alternatingGroup (Fin N) ⊓ centralizer ({τ} : Set (Perm (Fin N))))) := by
    have h1 : CFSG.Assembly.IsComponentOf A (W ⊓ centralizer ({t} : Set X)) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp
        (le_inf hAW h.le_cent) inf_le_right
    have h2 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hι).2 h1
    rw [hCWt] at h2
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (le_inf hA'A hA'c)).1 h2
  obtain ⟨hF5, hsupp, ⟨eP⟩⟩ := component_eq_alt_fixed hτ2 hA'A hA'c hAcomp
  have hFcard : m = Fintype.card {x : Fin N // τ x = x} := by
    have hk2 : 2 ≤ Fintype.card {x : Fin N // τ x = x} := by omega
    have : Nontrivial {x : Fin N // τ x = x} := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have h1 : Nat.card A = Nat.card (alternatingGroup {x : Fin N // τ x = x}) :=
      Nat.card_congr ((A.equivMapOfInjective ι hι).trans eP).toEquiv
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := {x : Fin N // τ x = x}),
      hcA] at h1
    have h2 : m.factorial = (Fintype.card {x : Fin N // τ x = x}).factorial :=
      (Nat.div_left_inj (Nat.dvd_factorial (by norm_num) (by omega))
        (Nat.dvd_factorial (by norm_num) hk2)).1 h1
    exact (Nat.factorial_inj (by omega)).1 h2
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    simpa using congrArg (fun p : Perm (Fin N) => p x) hτ2
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra hcon
    exact hτ1 (Equiv.ext fun x => by_contra fun hx => hcon ⟨x, hx⟩)
  have hcyc : ∀ c, τ c ≠ c → c = a ∨ c = τ a := by
    intro c hc
    by_contra hne
    rw [not_or] at hne
    obtain ⟨g, hgA, hgτ, hg1, hgτ', hgg, hgsupp⟩ :=
      exists_even_commuting_involution hτ2 ha hc hne.1 hne.2
    obtain ⟨w, hw⟩ := lookup_exists_of_mem_alt eW ι hιW hgA
    have hwt : (w : X) * t = t * w := hι (by rw [map_mul, map_mul, hw]; exact hgτ)
    have hwA : (w : X) ∈ centralizer (A : Set X) := by
      rw [mem_centralizer_iff]
      intro a' ha'
      apply hι
      rw [map_mul, map_mul, hw]
      have hd : Perm.Disjoint (ι a') g := by
        intro x
        by_cases hgx : g x = x
        · exact Or.inr hgx
        · exact Or.inl (hsupp (ι a') ⟨a', ha', rfl⟩ x (hgsupp x hgx))
      exact hd.commute.eq
    have hmem : (w : X) ∈ zpowers t := by
      refine h.two_mem _ ⟨hwA, mem_centralizer_singleton_iff.2 hwt⟩ 1 ?_
      apply hι
      rw [map_pow, hw, pow_one, sq, hgg, map_one]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hgk : g = τ ^ k := by rw [← hw, ← hk, map_zpow]
    rcases lookup_zpow_eq_one_or_self hτ2 k with h1 | h1
    · exact hg1 (hgk.trans h1)
    · exact hgτ' (hgk.trans h1)
  have hswap : τ = swap a (τ a) := eq_swap_of_unique_cycle hτ2 ha hcyc
  have hcardF : Fintype.card {x : Fin N // τ x = x} + 2 = N := by
    have h1 := Fintype.card_subtype_compl (fun x : Fin N => τ x = x)
    have h2 : Fintype.card {x : Fin N // ¬ τ x = x} = 2 := by
      rw [Fintype.card_subtype]
      have : (Finset.univ.filter fun x : Fin N => ¬ τ x = x) = {a, τ a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · exact hcyc x
        · rintro (hx | hx)
          · rw [hx]
            exact ha
          · rw [hx, hττ a]
            exact fun h' => ha h'.symm
      rw [this, Finset.card_pair]
      exact fun h => ha h.symm
    rw [Fintype.card_fin] at h1
    have h3 := Fintype.card_subtype_le (fun x : Fin N => τ x = x)
    rw [Fintype.card_fin] at h3
    omega

  have hinj : Nat.card (centralizer ({t} : Set X)) ≤
      Nat.card (centralizer ({τ} : Set (Perm (Fin N)))) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨ι c, ?_⟩) ?_
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.1 c.2]
    · intro c c' hcc
      exact Subtype.ext (hι (congrArg Subtype.val hcc))
  have hτswap : τ.IsSwap := ⟨a, τ a, Ne.symm ha, hswap⟩
  have hcent : Nat.card (centralizer ({τ} : Set (Perm (Fin N)))) = (N - 2).factorial * 2 := by
    rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.1 hτswap]
    simp
  have hNm2 : N - 2 = m := by omega
  rw [hcent, hNm2] at hinj
  linarith

end Alt

end CFSG.OddStandard.AltStdSec
