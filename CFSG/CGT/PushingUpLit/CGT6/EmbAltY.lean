module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatFam
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement Nat

variable {V : Type} [CommGroup V] [Finite V]

private theorem altY_two_pow_lt_factorial {m : ℕ} (hm : 15 ≤ m) : 2 ^ (3 * m - 5) < m ! := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h1 : 3 * (m + 1) - 5 = (3 * m - 5) + 3 := by omega
    rw [h1, pow_add, Nat.factorial_succ]
    have h2 : 2 ^ 3 ≤ m + 1 := by omega
    calc 2 ^ (3 * m - 5) * 2 ^ 3 < m ! * 2 ^ 3 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ m ! * (m + 1) := Nat.mul_le_mul_left _ h2
      _ = (m + 1) * m ! := Nat.mul_comm _ _

private theorem altY_order_ne {m k : ℕ} (hm : 7 ≤ m) (hk : 2 ≤ k)
    (h : m ! = 2 * (2 ^ k * ((2 ^ k) ^ 2 - 1))) : False := by
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq16 : 16 ≤ (2 ^ k) ^ 2 := by nlinarith
  have hQodd : ¬ 2 ∣ (2 ^ k) ^ 2 - 1 := by
    have h2 : 2 ∣ (2 ^ k) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    omega
  have hQne : (2 ^ k) ^ 2 - 1 ≠ 0 := by omega
  have hv : padicValNat 2 (m !) = k + 1 := by
    rw [h, padicValNat.mul (by norm_num) (mul_ne_zero (by positivity) hQne),
      padicValNat.mul (by positivity) hQne, padicValNat.self (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hQodd]
    ring
  have hlt : padicValNat 2 (m !) < m := padicValNat_factorial_lt_of_ne_zero 2 (by omega)
  have hkm : k + 2 ≤ m := by omega
  have hbig : m ! ≤ 2 ^ (3 * k + 1) := by
    rw [h]
    have h1 : (2 ^ k) ^ 2 - 1 ≤ 2 ^ (2 * k) := by
      rw [← pow_mul, mul_comm k 2]
      exact Nat.sub_le _ _
    calc 2 * (2 ^ k * ((2 ^ k) ^ 2 - 1)) ≤ 2 * (2 ^ k * 2 ^ (2 * k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = 2 ^ (3 * k + 1) := by ring
  by_cases h15 : 15 ≤ m
  · have h2 := altY_two_pow_lt_factorial h15
    have h3 : 2 ^ (3 * k + 1) ≤ 2 ^ (3 * m - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hm14 : m ≤ 14 := by omega
    have hk12 : k ≤ 12 := by omega
    clear hbig hv hlt hQodd hQne
    interval_cases m <;> interval_cases k <;> (revert h; decide)

theorem card_alt_ne_card_sl2 {m k : ℕ} (hm : 7 ≤ m) (hk : 2 ≤ k) :
    Nat.card (alternatingGroup (Fin m)) ≠ 2 ^ k * (2 ^ (2 * k) - 1) := by
  intro h
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin,
    show 2 * k = k * 2 by omega, pow_mul] at h
  apply altY_order_ne hm hk
  have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
  omega

private theorem altY_center_eq_bot {Γ : Type*} [Group Γ] {m : ℕ} (hm : 4 ≤ m)
    (e : Γ ≃* alternatingGroup (Fin m)) : Subgroup.center Γ = ⊥ := by
  have h1 : (Subgroup.center Γ).map e.toMonoidHom = Subgroup.center (alternatingGroup (Fin m)) :=
    Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (by simpa using hm)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

private theorem altY_not_sl (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    [Group.IsPerfect ↥Y] (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ} (hn1 : 1 ≤ n)
    (hsl : IsNaturalSLTwoModule ↥(yuHol Y) n) {m : ℕ} (hm : 7 ≤ m)
    (e : ↥Y ≃* alternatingGroup (Fin m)) : False := by
  have hn2 : 2 ≤ n := by
    by_contra h
    obtain rfl : n = 1 := by omega
    exact CFSG.CGT.PushingUp.not_isNaturalSLTwoModule_one hshort hsl
  obtain ⟨φY, -⟩ := hsl
  have hZ := altY_center_eq_bot (by omega) e
  have hθs := yuTheta_surjective Y φY hV
  have hRc := yuTheta_ker_le_center Y φY hV hshort
  have hker : (yuTheta Y φY).ker = ⊥ := eq_bot_iff.mpr (hRc.trans hZ.le)
  have hθi : Function.Injective (yuTheta Y φY) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have h1 := Nat.card_congr (Equiv.ofBijective _ ⟨hθi, hθs⟩)
  rw [Nat.card_congr e.toEquiv] at h1
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card 2 n (by omega), Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  apply altY_order_ne hm hn2
  have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
  omega

theorem altY_setup (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    [Group.IsPerfect ↥Y] (hZ : Subgroup.center ↥Y = ⊥) (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (halt : IsNaturalAltModule ↥(yuHol Y) n) :
    ∃ (θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)))
      (β : ↥(commV Y) →* ↥(G6.coreMod (2 * n + 1))), Function.Surjective β ∧
      β.ker = (commV Y ⊓ fixV Y).subgroupOf (commV Y) ∧
      ∀ (x : ↥Y) (p : ↥(commV Y)) (hp : (x : MulAut V) p ∈ commV Y),
        β ⟨(x : MulAut V) p, hp⟩ = altAct (2 * n + 1) (θ x) (β p) := by
  classical
  obtain ⟨φY, ψ, hsum, hsurj, hker, hequiv⟩ := halt
  have hθs := yuTheta_surjective Y φY hV
  have hRc := yuTheta_ker_le_center Y φY hV hshort
  have hker1 : (yuTheta Y φY).ker = ⊥ := eq_bot_iff.mpr (hRc.trans hZ.le)
  have hθi : Function.Injective (yuTheta Y φY) := (MonoidHom.ker_eq_bot_iff _).mp hker1
  let θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)) :=
    MulEquiv.ofBijective (yuTheta Y φY) ⟨hθi, hθs⟩
  let ρ : ↥Y →* MulAut V := Y.subtype
  let θ' : ↥Y →* Equiv.Perm (Fin (2 * n + 1)) :=
    (alternatingGroup (Fin (2 * n + 1))).subtype.comp (yuTheta Y φY)
  let A₀ : Subgroup V := commV Y ⊓ fixV Y
  have hB : ∀ g : ↥Y, ∀ b ∈ commV Y, ρ g b ∈ commV Y := fun g b hb =>
    apply_mem_commV_self Y g.2 hb
  have hshortU := shortU_eq_range Y φY hV hshort
  let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
    (yuInc Y).codRestrict (shortU ↥(yuHol Y)) (yuInc_mem_shortU Y hV)
  let β : ↥(commV Y) →* ↥(G6.coreMod (2 * n + 1)) :=
    (ψ.comp ι).codRestrict (G6.coreMod (2 * n + 1)) (fun u => (G6.mem_coreMod).2 (hsum _))
  have hβs : Function.Surjective β := by
    intro w
    obtain ⟨x, hx⟩ := hsurj (Multiplicative.toAdd (w : G6.PermMod (2 * n + 1)))
      (G6.mem_coreMod.mp w.2)
    obtain ⟨u, hu⟩ : (x : ↥(yuHol Y)) ∈ (yuInc Y).range := hshortU ▸ x.2
    refine ⟨u, Subtype.ext ?_⟩
    show ψ (ι u) = (w : G6.PermMod (2 * n + 1))
    have : ι u = x := Subtype.ext hu
    rw [this, hx]
    rfl
  have hβk : β.ker = A₀.subgroupOf (commV Y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (ψ.comp ι) u = 1 := congrArg Subtype.val h
      have h2 : ι u ∈ ψ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      have h3 : yuInc Y u ∈ Subgroup.center ↥(yuHol Y) := h2.2
      refine ⟨u.2, fun g hg => ?_⟩
      exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h3
    · rintro ⟨-, hu⟩
      apply Subtype.ext
      show ψ (ι u) = 1
      have h2 : ι u ∈ ψ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        refine ⟨yuInc_mem_shortU Y hV u, Subgroup.mem_center_iff.mpr ?_⟩
        intro x
        have h4 := conj_yuInc Y x u
        have h5 : (⟨x.1.right u, apply_mem_commV_self Y x.2.2 u.2⟩ : ↥(commV Y)) = u :=
          Subtype.ext (hu x.1.right x.2.2)
        rw [h5] at h4
        exact mul_inv_eq_iff_eq_mul.mp h4
      exact h2
  have hβe : ∀ (g : ↥Y) (b : ↥(commV Y)), β ⟨ρ g b, hB g b b.2⟩ =
      G6.coreAct (2 * n + 1) (θ' g) (β b) := by
    intro g b
    have hu : yuInc Y b ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV b
    have hu' : yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y) :=
      (shortU_normal (L := ↥(yuHol Y))).conj_mem _ hu _
    have h1 := hequiv (yuSec Y g : ↥(yuHol Y)) (yuInc Y b) hu hu'
    have h2 : (⟨yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹, hu'⟩ : ↥(shortU ↥(yuHol Y))) =
        ι ⟨ρ g b, hB g b b.2⟩ := by
      apply Subtype.ext
      exact conj_yuInc Y (yuSec Y g) b
    rw [h2] at h1
    apply Subtype.ext
    show ψ (ι ⟨ρ g b, hB g b b.2⟩) = G6.permAct (2 * n + 1) (θ' g) (ψ (ι b))
    rw [h1]
    apply Multiplicative.toAdd.injective
    funext i
    rfl
  exact ⟨θ, β, hβs, hβk, fun x p hp => hβe x p⟩

omit [Finite V] in
private theorem altY_cube (hV : ∀ v : V, v ^ 2 = 1) {j : MulAut V} (hj : j ^ 3 = 1) {u : V}
    (he : j (j u * u⁻¹) = j u * u⁻¹) : j u = u := by
  set e := j u * u⁻¹ with he_def
  have h1 : j u = e * u := by rw [he_def, inv_mul_cancel_right]
  have hee : e * e = 1 := by rw [← pow_two]; exact hV e
  have h2 : j (j u) = u := by
    calc j (j u) = j (e * u) := by rw [← h1]
      _ = j e * j u := map_mul j _ _
      _ = e * (e * u) := by rw [he, h1]
      _ = (e * e) * u := (mul_assoc _ _ _).symm
      _ = u := by rw [hee, one_mul]
  have h3 : j (j (j u)) = u := by
    have := congrArg (fun f : MulAut V => f u) hj
    simpa [pow_succ, MulAut.mul_apply] using this
  calc j u = j (j (j u)) := by rw [h2]
    _ = u := h3

omit [Finite V] in
private theorem altY_stab_fix (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} {m : ℕ}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (p : Fin m) (u : V)
    (h : ∀ x : ↥Y, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) ((x : MulAut V) u * u⁻¹) = (x : MulAut V) u * u⁻¹) :
    ∀ x : ↥Y, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) u = u := by
  classical
  let s : Finset (Fin m) := {p}ᶜ
  let κ : alternatingGroup ↥s →* ↥Y :=
    θ.symm.toMonoidHom.comp (alternatingGroup.ofSubtype s)
  have hκθ : ∀ g, θ (κ g) = alternatingGroup.ofSubtype s g := fun g => by
    simp [κ]
  have hκp : ∀ g, ((θ (κ g) : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p := by
    intro g
    rw [hκθ, alternatingGroup.coe_ofSubtype]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [s])
  have hall : ∀ g : alternatingGroup ↥s, (κ g : MulAut V) u = u := by
    intro g
    have hg : g ∈ Subgroup.closure
        {g : alternatingGroup ↥s | Equiv.Perm.IsThreeCycle (g : Equiv.Perm ↥s)} := by
      rw [alternatingGroup.closure_isThreeCycles_eq_top]
      trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      have h3 : g ^ 3 = 1 := by
        have ho : orderOf g = 3 := by
          have := hg.orderOf
          rwa [Subgroup.orderOf_coe] at this
        rw [← ho]
        exact pow_orderOf_eq_one g
      have hj3 : (κ g : MulAut V) ^ 3 = 1 := by
        have : κ g ^ 3 = 1 := by rw [← map_pow, h3, map_one]
        have h4 := congrArg (fun y : ↥Y => (y : MulAut V)) this
        simpa using h4
      exact altY_cube hV hj3 (h (κ g) (hκp g))
    | one => simp
    | mul a b _ _ ha hb =>
      rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, hb, ha]
    | inv a _ ha =>
      rw [map_inv, Subgroup.coe_inv]
      conv_lhs => rw [← ha]
      exact MulAut.inv_apply_self V _ _
  intro x hx
  have hmem : θ x ∈ (alternatingGroup.ofSubtype s).range := by
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro a ha
    simp only [s, Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact (Equiv.Perm.mem_support.mp ha) hx
  obtain ⟨g, hg⟩ := hmem
  have hκx : κ g = x := by
    apply θ.injective
    rw [hκθ, hg]
  rw [← hκx]
  exact hall g

section PermModule

variable {m : ℕ}

private abbrev altYe (i : Fin m) : G6.PermMod m := Multiplicative.ofAdd (Pi.single i 1)

private theorem altYe_apply (a i : Fin m) :
    Multiplicative.toAdd (altYe a) i = (Pi.single a 1 : Fin m → ZMod 2) i := rfl

private theorem altY_permAct_e (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    G6.permAct m σ (altYe a) = altYe (σ a) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, altYe_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem altY_prod_e (x : G6.PermMod m) :
    x = ∏ i : Fin m, altYe i ^ (Multiplicative.toAdd x i).val := by
  apply Multiplicative.toAdd.injective
  funext j
  simp only [toAdd_prod, toAdd_pow, Finset.sum_apply, Pi.smul_apply, toAdd_ofAdd]
  simp [Pi.single_apply]

private theorem altY_hom_ext {M : Type*} [Group M] {f g : G6.PermMod m →* M}
    (h : ∀ i : Fin m, f (altYe i) = g (altYe i)) : f = g := by
  ext x
  have hx : x ∈ f.eqLocus g := by
    rw [altY_prod_e x]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (h i) _
  exact hx

private def altYwt (u : G6.PermMod m) : ZMod 2 := ∑ i, Multiplicative.toAdd u i

private def altYc (m : ℕ) (a : ZMod 2) : G6.PermMod m := Multiplicative.ofAdd fun _ => a

private theorem altYwt_mul (u v : G6.PermMod m) : altYwt (u * v) = altYwt u + altYwt v := by
  simp [altYwt, Finset.sum_add_distrib]

private theorem altYwt_permAct (σ : Equiv.Perm (Fin m)) (u : G6.PermMod m) :
    altYwt (G6.permAct m σ u) = altYwt u := by
  simp only [altYwt, G6.permAct_apply]
  exact Equiv.sum_comp σ⁻¹ fun i => Multiplicative.toAdd u i

private theorem altYc_add (a b : ZMod 2) : altYc m (a + b) = altYc m a * altYc m b := rfl

private theorem altYwt_c (hm : Odd m) (a : ZMod 2) : altYwt (altYc m a) = a := by
  have h : ((m : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hm
  simp [altYwt, altYc, h]

private theorem altYproj_mem (hm : Odd m) (u : G6.PermMod m) :
    u * altYc m (altYwt u) ∈ G6.coreMod m := by
  rw [G6.mem_coreMod]
  change altYwt (u * altYc m (altYwt u)) = 0
  rw [altYwt_mul, altYwt_c hm, CharTwo.add_self_eq_zero]

private def altYproj (hm : Odd m) : G6.PermMod m →* ↥(G6.coreMod m) :=
  MonoidHom.mk' (fun u => ⟨u * altYc m (altYwt u), altYproj_mem hm u⟩) fun u v => by
    apply Subtype.ext
    simp only [altYwt_mul, altYc_add, Subgroup.coe_mul]
    exact mul_mul_mul_comm _ _ _ _

private theorem altYproj_coe (hm : Odd m) (u : G6.PermMod m) :
    ((altYproj hm u : ↥(G6.coreMod m)) : G6.PermMod m) = u * altYc m (altYwt u) := rfl

private theorem altYproj_of_mem (hm : Odd m) {u : G6.PermMod m} (hu : u ∈ G6.coreMod m) :
    altYproj hm u = ⟨u, hu⟩ := by
  apply Subtype.ext
  have h0 : altYwt u = 0 := hu
  rw [altYproj_coe, h0]
  show u * altYc m 0 = u
  exact mul_one u

private theorem altYproj_permAct (hm : Odd m) (σ : Equiv.Perm (Fin m)) (u : G6.PermMod m) :
    altYproj hm (G6.permAct m σ u) = G6.coreAct m σ (altYproj hm u) := by
  apply Subtype.ext
  rw [G6.coreAct_coe, altYproj_coe, altYproj_coe, map_mul, altYwt_permAct]
  rfl

end PermModule

omit [Finite V] in
theorem commV_inf_fixV_eq_bot_of_quot (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    [Group.IsPerfect ↥Y] {m : ℕ} (hodd : Odd m) (hm : 3 ≤ m)
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (β : ↥(commV Y) →* ↥(G6.coreMod m))
    (hβs : Function.Surjective β) (hβk : β.ker = (commV Y ⊓ fixV Y).subgroupOf (commV Y))
    (hβe : ∀ (x : ↥Y) (p : ↥(commV Y)) (hp : (x : MulAut V) p ∈ commV Y),
      β ⟨(x : MulAut V) p, hp⟩ = altAct m (θ x) (β p)) :
    commV Y ⊓ fixV Y = ⊥ := by
  classical
  let p : Fin m := ⟨0, by omega⟩
  let π := altYproj hodd
  obtain ⟨u₀, hu₀⟩ := hβs (π (altYe p))
  have hπ : ∀ x : ↥Y, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      altAct m (θ x) (π (altYe p)) = π (altYe p) := by
    intro x hx
    show G6.coreAct m _ (π (altYe p)) = _
    rw [← altYproj_permAct, altY_permAct_e, hx]
  have hJ0 : ∀ x : ↥Y, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) ((x : MulAut V) (u₀ : V) * (u₀ : V)⁻¹) =
        (x : MulAut V) (u₀ : V) * (u₀ : V)⁻¹ := by
    intro x hx
    have hmem : (x : MulAut V) (u₀ : V) ∈ commV Y := apply_mem_commV_self Y x.2 u₀.2
    have h1 : β ⟨(x : MulAut V) u₀, hmem⟩ = β u₀ := by
      rw [hβe x u₀ hmem, hu₀, hπ x hx]
    have h2 : (⟨(x : MulAut V) u₀, hmem⟩ * u₀⁻¹ : ↥(commV Y)) ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul_inv, h1]
      exact mul_inv_cancel _
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact (mem_fixV.mp h2.2) x x.2
  have hstab := altY_stab_fix hV θ p (u₀ : V) hJ0
  obtain ⟨Φ, hΦp, hΦr, hΦe⟩ := exists_orbitFamHom hV hm θ p (v := (u₀ : V)) hstab
  have hspan : orbitSpan Y (u₀ : V) ≤ commV Y := by
    unfold orbitSpan
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_commV_self Y hx u₀.2
  have hΦU : ∀ y, Φ y ∈ commV Y := fun y => hspan (hΦr ▸ ⟨y, rfl⟩)
  let Φ' : G6.PermMod m →* ↥(commV Y) := Φ.codRestrict (commV Y) hΦU
  have htrans : ∀ i : Fin m,
      ∃ x : ↥Y, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = i := by
    intro i
    have := alternatingGroup.isPretransitive_of_three_le_card (Fin m) (by simp; omega)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin m)) p i
    exact ⟨θ.symm g, by simpa using (show (g : Equiv.Perm (Fin m)) p = i from hg)⟩
  have hT : ∀ y : G6.PermMod m, β (Φ' y) = π y := by
    have hcomp : β.comp Φ' = π := by
      apply altY_hom_ext
      intro i
      obtain ⟨x, hx⟩ := htrans i
      have e1 : altYe i =
          G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) (altYe p) := by
        rw [altY_permAct_e, hx]
      have e2 : Φ' (altYe i) =
          ⟨(x : MulAut V) (u₀ : V), apply_mem_commV_self Y x.2 u₀.2⟩ := by
        apply Subtype.ext
        show Φ (altYe i) = _
        rw [e1, ← hΦe x, hΦp]
      show β (Φ' (altYe i)) = π (altYe i)
      rw [e2, hβe x u₀, hu₀, e1, altYproj_permAct]
      rfl
    intro y
    exact DFunLike.congr_fun hcomp y
  let Φc : ↥(G6.coreMod m) →* V := Φ.comp (G6.coreMod m).subtype
  have hΦce : ∀ (x : ↥Y) (w : ↥(G6.coreMod m)), (x : MulAut V) (Φc w) =
      Φc (G6.coreAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) w) :=
    fun x w => hΦe x w
  let N₁ : Subgroup V := Φc.range
  have hN : ∀ (g : ↥Y) (b : ↥(commV Y)), (g : MulAut V) (b : V) * (b : V)⁻¹ ∈ N₁ := by
    intro g b
    set w : ↥(G6.coreMod m) := β b with hw
    have hbw : β (Φ' (w : G6.PermMod m)) = β b := by
      rw [hT, altYproj_of_mem hodd w.2]
    have hc : b * (Φ' (w : G6.PermMod m))⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul_inv, hbw]
      exact mul_inv_cancel _
    rw [hβk, Subgroup.mem_subgroupOf] at hc
    set c : V := (b : V) * (Φc w)⁻¹ with hc_def
    have hcf : ∀ y ∈ Y, (y : MulAut V) c = c := mem_fixV.mp hc.2
    have hb : (b : V) = c * Φc w := by
      rw [hc_def, inv_mul_cancel_right]
    have hgb : (g : MulAut V) (b : V) =
        c * Φc (G6.coreAct m ((θ g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) w) := by
      conv_lhs => rw [hb]
      rw [map_mul, hcf g g.2, hΦce g]
    refine ⟨G6.coreAct m ((θ g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) w * w⁻¹, ?_⟩
    refine (map_mul_inv Φc _ w).trans ?_
    rw [hgb]
    conv_rhs => rw [hb]
    rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  have hUN : commV Y ≤ N₁ := commV_le_of_perfect Y N₁ hN
  rw [eq_bot_iff]
  intro c hc
  have hcU : c ∈ commV Y := hc.1
  obtain ⟨y, hyc⟩ := hUN hcU
  have hker : β ⟨c, hcU⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    exact hc
  have e3 : (⟨c, hcU⟩ : ↥(commV Y)) = Φ' (y : G6.PermMod m) := Subtype.ext hyc.symm
  rw [e3, hT, altYproj_of_mem hodd y.2] at hker
  have hy1 : y = 1 := hker
  rw [Subgroup.mem_bot, ← hyc, hy1, map_one]

theorem natSection_of_classX_alt (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : Nonempty (↥Y ≃* alternatingGroup (Fin m))) :
    ∃ θ : ↥Y ≃* alternatingGroup (Fin m), IsNatSectionWith (altAct m) θ (commV Y) ⊥ := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨e⟩ := hY
  obtain ⟨hshort, ⟨n, hn1, halt⟩ | ⟨n, hn1, hsl⟩⟩ := hX
  · obtain ⟨θ, β, hβs, hβk, hβe⟩ := altY_setup hV (altY_center_eq_bot (by omega) e) hshort halt
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcard := Nat.card_congr (e.symm.trans θ).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at hcard
    have h2m : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
    have h2n : 2 ∣ (2 * n + 1)! := Nat.dvd_factorial (by norm_num) (by omega)
    have hfac : m ! = (2 * n + 1)! := by omega
    obtain rfl : m = 2 * n + 1 := (Nat.factorial_inj (by omega)).mp hfac
    have hC := commV_inf_fixV_eq_bot_of_quot hV hodd (by omega) θ β hβs hβk hβe
    refine ⟨θ, fun x hx p hp => apply_mem_commV_self Y hx hp, β, hβs, ?_, hβe⟩
    rw [hβk, hC]
  · exact (altY_not_sl hV hshort hn1 hsl hm e).elim

end CFSG.CGT.PushingUpLit.CGT6
