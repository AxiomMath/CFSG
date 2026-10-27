module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Count

variable {X : Type*} [Group X] [Finite X]

theorem card_modEq_fix_sub {K : Subgroup X} {y : X} (hy5 : y ^ 5 = 1)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hyK' : ∀ k ∈ K, y⁻¹ * k * y ∈ K) :
    Nat.card K ≡ Nat.card ↥(K ⊓ centralizer ({y} : Set X)) [MOD 5] := by
  classical
  let σ : Equiv.Perm ↥K :=
    { toFun := fun x => ⟨y * x * y⁻¹, hyK x x.2⟩
      invFun := fun x => ⟨y⁻¹ * x * y, hyK' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  have hσk : ∀ (k : ℕ) (x : ↥K), (((σ ^ k) x : ↥K) : X) = y ^ k * x * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show y ^ k * (y * (x : X) * y⁻¹) * (y ^ k)⁻¹ = y ^ (k + 1) * x * (y ^ (k + 1))⁻¹
      rw [pow_succ]; group
  have hσ5 : σ ^ 5 = 1 := by
    ext x
    rw [hσk, hy5]
    simp
  have hmod := card_modEq_fixed σ hσ5
  set C : Subgroup X := K ⊓ centralizer ({y} : Set X) with hC
  have hfixset : Function.fixedPoints σ = ((C.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    ext x
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, SetLike.mem_coe, mem_subgroupOf, hC,
      mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      have h2 : y * (x : X) * y⁻¹ = x := this
      calc (x : X) * y = (y * x * y⁻¹) * y := by rw [h2]
        _ = y * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      show y * (x : X) * y⁻¹ = x
      calc y * (x : X) * y⁻¹ = (x * y) * y⁻¹ := by rw [hx]
        _ = x := by group
  rw [hfixset] at hmod
  have hcc : Nat.card ↥(C.subgroupOf K) = Nat.card ↥C :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : C ≤ K)).toEquiv
  have hmod' : Nat.card ↥K ≡ Nat.card ↥(C.subgroupOf K) [MOD 5] := hmod
  rw [hcc] at hmod'
  exact hmod'

theorem eq_two_or_32 {n : ℕ} (hd : n ∣ 32) (hm : 32 ≡ n [MOD 5]) : n = 2 ∨ n = 32 := by
  obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show n ∣ 2 ^ 5 by simpa using hd)
  rw [hk2] at hm ⊢
  clear hd hk2
  interval_cases k
  · exfalso; revert hm; decide
  · left; norm_num
  · exfalso; revert hm; decide
  · exfalso; revert hm; decide
  · exfalso; revert hm; decide
  · right; norm_num

end Count

section Main

variable {X : Type*} [Group X] [Finite X]

theorem eq_rootGroup_of_five {t : X} (hR : RootFactsFor X t) {E : Subgroup X}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htE : t ∈ E)
    (htc : ∀ e ∈ E, e * t = t * e) (hcard : Nat.card E = 32)
    (hnorm : ∀ w : X, w * t = t * w → ∀ e ∈ E, w * e * w⁻¹ ∈ E)
    (hcent : ∀ l : X, (∀ e ∈ E, l * e = e * l) → l = 1 ∨ l = t) :
    E = rootGroup X t := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ({t} : Set X) with hCdef
  set R : Subgroup X := rootGroup X t with hRdef
  have hCcard : Nat.card C = 1920 := hR.card_cent
  have hRcard : Nat.card R = 32 := hR.card_E
  have ht_ord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hroot : ∃ r : X, r * r = t := by
    by_contra hno
    simp only [not_exists] at hno
    have hbot : R = ⊥ := by
      rw [eq_bot_iff, hRdef, rootGroup, closure_le]
      intro x hx
      exact absurd hx (hno x)
    rw [hbot, Subgroup.card_bot] at hRcard
    omega
  obtain ⟨r0, hr0⟩ := hroot
  have htR : t ∈ R := by
    have : r0 ∈ R := subset_closure hr0
    rw [← hr0]; exact mul_mem this this
  have hEC : E ≤ C := fun e he => mem_centralizer_singleton_iff.2 (htc e he)
  have hRC : R ≤ C := by
    rw [hRdef, rootGroup, closure_le]
    intro r hr
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hr' : r * r = t := hr
    calc r * t = r * (r * r) := by rw [hr']
      _ = (r * r) * r := by group
      _ = t * r := by rw [hr']
  have hnormR : ∀ w : X, w * t = t * w → ∀ g ∈ R, w * g * w⁻¹ ∈ R := by
    intro w hw g hg
    have hroot_conj : ∀ r : X, r * r = t → (w * r * w⁻¹) * (w * r * w⁻¹) = t := by
      intro r hr
      calc (w * r * w⁻¹) * (w * r * w⁻¹) = w * (r * r) * w⁻¹ := by group
        _ = w * t * w⁻¹ := by rw [hr]
        _ = t := by rw [hw]; group
    have hg' : g ∈ closure {x : X | x * x = t} := hg
    clear hg
    induction hg' using Subgroup.closure_induction with
    | mem x hx => exact subset_closure (hroot_conj x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx
  have h5C : 5 ∣ Nat.card C := by rw [hCcard]; norm_num
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 5 h5C
  set y : X := (y' : X) with hy
  have hyC : y ∈ C := y'.2
  have hy5 : orderOf y = 5 := by rw [hy, Subgroup.orderOf_coe]; exact hy'
  have hy5' : y ^ 5 = 1 := by have := pow_orderOf_eq_one y; rwa [hy5] at this
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hyC
  have hyi : y⁻¹ * t = t * y⁻¹ :=
    mem_centralizer_singleton_iff.1 (inv_mem hyC : y⁻¹ ∈ C)
  have hyE : ∀ k ∈ E, y * k * y⁻¹ ∈ E := hnorm y hyt
  have hyE' : ∀ k ∈ E, y⁻¹ * k * y ∈ E := fun k hk => by simpa using hnorm y⁻¹ hyi k hk
  have hyR : ∀ k ∈ R, y * k * y⁻¹ ∈ R := hnormR y hyt
  have hyR' : ∀ k ∈ R, y⁻¹ * k * y ∈ R := fun k hk => by simpa using hnormR y⁻¹ hyi k hk
  have hfE := card_modEq_fix_sub (K := E) hy5' hyE hyE'
  rw [hcard] at hfE
  have hfE_dvd : Nat.card ↥(E ⊓ centralizer ({y} : Set X)) ∣ 32 := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le inf_le_left
  have hfE_2 : Nat.card ↥(E ⊓ centralizer ({y} : Set X)) = 2 := by
    rcases eq_two_or_32 hfE_dvd hfE with h | h
    · exact h
    · exfalso
      have htop : E ⊓ centralizer ({y} : Set X) = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      have hcomm : ∀ e ∈ E, y * e = e * y := fun e he => by
        have : e ∈ E ⊓ centralizer ({y} : Set X) := by rw [htop]; exact he
        exact (mem_centralizer_singleton_iff.1 this.2).symm
      rcases hcent y hcomm with h1 | h1
      · rw [h1, orderOf_one] at hy5; omega
      · rw [h1, ht_ord] at hy5; omega
  set K : Subgroup X := E ⊓ R with hK
  have hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun k hk => ⟨hyE k hk.1, hyR k hk.2⟩
  have hyK' : ∀ k ∈ K, y⁻¹ * k * y ∈ K := fun k hk => ⟨hyE' k hk.1, hyR' k hk.2⟩
  have hKt : t ∈ K := ⟨htE, htR⟩
  have hfK := card_modEq_fix_sub (K := K) hy5' hyK hyK'
  have hfK_le : Nat.card ↥(K ⊓ centralizer ({y} : Set X)) ≤ 2 := by
    rw [← hfE_2]
    exact Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  have hfK_ge : 2 ≤ Nat.card ↥(K ⊓ centralizer ({y} : Set X)) := by
    have hz : zpowers t ≤ K ⊓ centralizer ({y} : Set X) := by
      rw [zpowers_le]
      exact ⟨hKt, mem_centralizer_singleton_iff.2 hyt.symm⟩
    have := Subgroup.card_le_of_le hz
    rwa [Nat.card_zpowers, ht_ord] at this
  have hfK2 : Nat.card ↥(K ⊓ centralizer ({y} : Set X)) = 2 := le_antisymm hfK_le hfK_ge
  rw [hfK2] at hfK
  have hKd : Nat.card K ∣ 32 := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le inf_le_left
  have hK_cases : Nat.card K = 2 ∨ Nat.card K = 32 :=
    eq_two_or_32 hKd ((show 32 ≡ 2 [MOD 5] by decide).trans hfK.symm)

  have hEn : (E.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hg : (g : X) * t = t * g := mem_centralizer_singleton_iff.1 g.2
    simpa using hnorm g hg n hn
  have hEc : Nat.card ↥(E.subgroupOf C) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hcard
  have hRc' : Nat.card ↥(R.subgroupOf C) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv).trans hRcard
  have hE2 : IsPGroup 2 ↥(E.subgroupOf C) := IsPGroup.of_card (n := 5) (by rw [hEc]; norm_num)
  have hR2 : IsPGroup 2 ↥(R.subgroupOf C) := IsPGroup.of_card (n := 5) (by rw [hRc']; norm_num)
  have hP2 : IsPGroup 2 ↥(R.subgroupOf C ⊔ E.subgroupOf C) :=
    hR2.to_sup_of_normal_right' hE2 (by rw [normalizer_eq_top_iff.2 hEn]; exact le_top)
  have hPdvd : Nat.card ↥(R.subgroupOf C ⊔ E.subgroupOf C) ∣ 1920 := by
    have := Subgroup.card_subgroup_dvd_card (R.subgroupOf C ⊔ E.subgroupOf C)
    rwa [show Nat.card ↥C = 1920 from hCcard] at this
  have hP128 : Nat.card ↥(R.subgroupOf C ⊔ E.subgroupOf C) ≤ 128 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hP2
    rw [ha] at hPdvd ⊢
    by_contra hlt
    have h8 : 8 ≤ a := by
      by_contra h8
      exact hlt (calc 2 ^ a ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 128 := by norm_num)
    have h256 : 256 ∣ 2 ^ a := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ∣ 2 ^ a := Nat.pow_dvd_pow 2 h8
    have := h256.trans hPdvd
    omega
  have := hEn
  have e1 : (E.subgroupOf C).relIndex (R.subgroupOf C ⊔ E.subgroupOf C) =
      (E.subgroupOf C).relIndex (R.subgroupOf C) :=
    Subgroup.relIndex_sup_right (R.subgroupOf C) (E.subgroupOf C)
  have e2 := Subgroup.relIndex_mul_card (H := E.subgroupOf C) (K := R.subgroupOf C ⊔ E.subgroupOf C)
  have e3 := Subgroup.relIndex_mul_card (H := E.subgroupOf C) (K := R.subgroupOf C)
  rw [inf_of_le_left le_sup_right, hEc, e1] at e2
  rw [hRc'] at e3
  have hKC : K ≤ C := inf_le_left.trans hEC
  have hKeq : K.subgroupOf C = E.subgroupOf C ⊓ R.subgroupOf C := by
    ext g
    simp [mem_subgroupOf, hK, mem_inf]
  have hKcard' : Nat.card ↥(E.subgroupOf C ⊓ R.subgroupOf C) = Nat.card ↥K := by
    rw [← hKeq]; exact Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv
  rw [hKcard'] at e3
  have hK32 : Nat.card K = 32 := by
    rcases hK_cases with h2 | h32
    · exfalso
      rw [h2] at e3
      omega
    · exact h32
  have hKE : K = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hK32])
  have hKR : K = R := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hRcard, hK32])
  exact hKE.symm.trans hKR

end Main

section Outer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem OuterE.eq_map_rootGroup_of_class (h : OuterE G L z t T E) (hW : WFacts L t E)
    (hRC : RootFactsClass ↥L) :
    ∃ htL : t ∈ L, orderOf (⟨t, htL⟩ : ↥L) = 2 ∧ (∃ g : ↥L, g * g = ⟨t, htL⟩) ∧
      E = (rootGroup ↥L ⟨t, htL⟩).map L.subtype := by
  have htE : t ∈ E := h.econfig.t_mem
  have htL : t ∈ L := hW.E_le htE
  set t' : ↥L := ⟨t, htL⟩ with ht'
  have ht2 : t * t = 1 := h.cfg.t_sq
  have ht2' : orderOf t' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h11 : t' * t' = 1 := Subtype.ext ht2
    exact orderOf_eq_prime (by rw [pow_two]; exact h11) (fun h1 => h.cfg.t_ne
      (congrArg Subtype.val h1))
  have hsq : ∃ g : ↥L, g * g = t' := by
    obtain ⟨g, hg, hg4⟩ := h.cfg.t_fourth
    exact ⟨⟨g * g, mul_mem hg hg⟩, Subtype.ext hg4⟩
  have hRf := hRC t' ht2' hsq
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => h.cfg.t_central e (h.E_le_T he)
  have hEL : E ≤ L := hW.E_le
  have hE' : E.subgroupOf L = rootGroup ↥L t' := by
    refine eq_rootGroup_of_five hRf (Subtype.ext ht2)
      (fun h1 => h.cfg.t_ne (congrArg Subtype.val h1)) (mem_subgroupOf.2 htE)
      (fun e he => Subtype.ext (htc e he)) ?_ ?_ ?_
    · exact (Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv).trans hW.card_E
    · intro w hw e he
      have hw' : (w : G) * t = t * w := congrArg Subtype.val hw
      exact mem_subgroupOf.2 (hW.normal w w.2 hw' e (mem_subgroupOf.1 he))
    · intro l hl
      have := hW.cent l l.2 (fun e he =>
        congrArg Subtype.val (hl ⟨e, hEL he⟩ (mem_subgroupOf.2 he)))
      rcases this with h1 | h1
      · left; exact Subtype.ext h1
      · right; exact Subtype.ext h1
  refine ⟨htL, ht2', hsq, ?_⟩
  calc E = (E.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hEL).symm
    _ = (rootGroup ↥L t').map L.subtype := by rw [hE']

theorem OuterE.exists_eLabelling (h : OuterE G L z t T E) (hW : WFacts L t E)
    (hRC : RootFactsClass ↥L) {mulE : ℕ → ℕ → ℕ} {tI : ℕ} (hU : ULabelClass ↥L mulE tI) :
    ∃ eltE : ℕ → G, ELabelling E t mulE tI eltE := by
  obtain ⟨htL, ht2', hsq, hEeq⟩ := h.eq_map_rootGroup_of_class hW hRC
  obtain ⟨eltE, hlab⟩ := hU ⟨t, htL⟩ ht2' hsq
  have := hlab.map L.subtype L.subtype_injective
  rw [← hEeq] at this
  exact ⟨_, this⟩

end Outer

end CFSG.EvenSporadicStandard.Fin76b
