module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecShape
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Gen

theorem closure_eq_top_of_simple {A : Type*} [Group A] [IsSimpleGroup A] {S : Set A}
    (hS : ∀ a x, x ∈ S → a * x * a⁻¹ ∈ S) (hne : ∃ x ∈ S, x ≠ 1) : closure S = ⊤ := by
  have hle : normalClosure S ≤ closure S := by
    change closure (Group.conjugatesOfSet S) ≤ closure S
    apply Subgroup.closure_mono
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    exact hS c x hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure S) with h | h
  · obtain ⟨x, hx, hx1⟩ := hne
    have := subset_normalClosure hx
    rw [h, SetLike.mem_coe, mem_bot] at this
    exact absurd this hx1
  · exact top_le_iff.1 (h ▸ hle)

variable {G : Type*} [Group G]

theorem pow_eq_one_of_mul_pow {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) (hc : a * b = b * a) {k : ℕ} (hk : (a * b) ^ k = 1) : b ^ k = 1 := by
  have h1 : a ^ k * b ^ k = 1 := by rw [← Commute.mul_pow hc k]; exact hk
  have h2 : b ^ k = (a ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : b ^ k ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨by rw [h2]; exact inv_mem (pow_mem ha k), pow_mem hb k⟩
  rw [hAB] at h3
  exact h3

theorem eq_one_of_odd_of_sq {b : G} (hodd : Odd (orderOf b)) (h2 : b ^ 2 = 1) : b = 1 := by
  have h := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hodd; exact absurd hodd (by decide)

theorem eq_one_of_pow_four_of_odd {b : G} (h4 : b ^ 4 = 1) {k : ℕ} (hk : Odd k) (hb : b ^ k = 1) :
    b = 1 := by
  have h1 : orderOf b ∣ Nat.gcd 4 k :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4) (orderOf_dvd_of_pow_eq_one hb)
  have h2 : Nat.gcd 4 k = 1 := by
    have : Nat.Coprime 2 k := (Nat.coprime_two_left).2 hk
    have : Nat.Coprime (2 ^ 2) k := Nat.Coprime.pow_left 2 this
    simpa using this
  rw [h2, Nat.dvd_one] at h1
  exact orderOf_eq_one_iff.1 h1

end Gen

section Incl

variable {G : Type} [Group G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

theorem altSub_compl_le : altSub (fourSet (m + 3))ᶜ ≤ fixSub (fourSet (m + 3)) := by
  intro σ hσ i hi
  exact (mem_altSub.1 hσ).2 i (by simpa using hi)

theorem card_fourSet_compl (hm : 1 ≤ m) : ((fourSet (m + 3))ᶜ).card = m - 1 := by
  rw [Finset.card_compl, Fintype.card_fin, card_fourSet (by omega)]
  omega

@[expose] noncomputable def secL : Subgroup (secQ (secP O R)) :=
  (secIncl O hR _ altSub_compl_le).range

@[expose] noncomputable def secLEquiv : secL O hR ≃* alternatingGroup (Fin (m - 1)) :=
  (MonoidHom.ofInjective (secIncl_injective O hR _ altSub_compl_le)).symm.trans
    ((altSubEquiv _).trans
      (Equiv.altCongrHom (finCongr (card_fourSet_compl (by have := hR.three_le; omega)))))

@[expose] noncomputable def secS : Subgroup (secQ (secP O R)) :=
  (secIncl O hR (fixSub (fourSet (m + 3))) le_rfl).range

theorem secIncl_congr {K K' : Subgroup (Perm (Fin (m + 3)))} (hK : K ≤ fixSub (fourSet (m + 3)))
    (hK' : K' ≤ fixSub (fourSet (m + 3))) {σ : K} {σ' : K'} (h : (σ : Perm (Fin (m + 3))) = σ') :
    secIncl O hR K hK σ = secIncl O hR K' hK' σ' := by
  rw [secIncl_apply, secIncl_apply]
  exact congrArg QuotientGroup.mk (Subtype.ext (congrArg O.φ h))

theorem comm_of_secIncl_comm (K : Subgroup (Perm (Fin (m + 3))))
    (hK : K ≤ fixSub (fourSet (m + 3))) {a b : K}
    (h : secIncl O hR K hK a * secIncl O hR K hK b = secIncl O hR K hK b * secIncl O hR K hK a) :
    a * b = b * a := by
  apply secIncl_injective O hR K hK
  rw [map_mul, map_mul, h]

theorem mk_eq_secIncl {h : ↥(centralizer (secP O R : Set G))} {r s : Perm (Fin (m + 3))}
    (hr : r ∈ R) (hs : s ∈ fixSub (fourSet (m + 3))) (hrs : (h : G) = O.φ r * O.φ s) :
    (QuotientGroup.mk h : secQ (secP O R)) = secIncl O hR _ le_rfl ⟨s, hs⟩ := by
  rw [secIncl_apply]
  apply QuotientGroup.eq.2
  change (h : G)⁻¹ * O.φ s ∈ secP O R
  rw [hrs]
  refine ⟨r⁻¹, inv_mem hr, ?_⟩
  have hcomm : O.φ r * O.φ s = O.φ s * O.φ r := O.φ_comm_iff.2 (hR.comm_fixSub hr hs)
  rw [map_inv, hcomm]
  group

theorem secL_inf_oddCore [Finite G] (hm : 6 ≤ m) :
    secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) = ⊥ :=
  inf_oddCore_eq_bot_of_alt (by omega) (secLEquiv O hR)

theorem conj_mem_altSub_compl {s σ : Perm (Fin (m + 3))} (hs : s ∈ fixSub (fourSet (m + 3)))
    (hσ : σ ∈ altSub (fourSet (m + 3))ᶜ) : s * σ * s⁻¹ ∈ altSub (fourSet (m + 3))ᶜ := by
  have hN : s ∈ normalizer ((altSub (fourSet (m + 3))ᶜ : Subgroup (Perm (Fin (m + 3)))) :
      Set (Perm (Fin (m + 3)))) := by
    refine mem_normalizer_altSub (fun i => ?_)
    simp only [Finset.mem_compl]
    constructor
    · intro hi h
      have h1 : s (s i) = s i := hs _ (by simpa using h)
      have := s.injective h1
      rw [this] at h
      exact hi (by simpa using h)
    · intro hi h
      have h1 : s i = i := hs i (by simpa using h)
      rw [h1] at hi
      exact hi (by simpa using h)
  exact (mem_normalizer_iff.1 hN σ).1 hσ

theorem secS_inf_oddCore [Finite G] (hm : 6 ≤ m) :
    secS O hR ⊓ CFSG.oddCore (secQ (secP O R)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨s, rfl⟩, hxO⟩ := Subgroup.mem_inf.1 hx
  rw [mem_bot]
  have hcomm : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, (s : Perm (Fin (m + 3))) * l = l * s := by
    intro l hl
    set x := secIncl O hR _ le_rfl s with hx
    set lh := secIncl O hR _ le_rfl (⟨l, altSub_compl_le hl⟩ : fixSub (fourSet (m + 3)))
      with hlh
    have h1 : x * lh * x⁻¹ * lh⁻¹ ∈ secL O hR := by
      refine ⟨⟨(s : Perm (Fin (m + 3))) * l * (s : Perm (Fin (m + 3)))⁻¹ * l⁻¹,
        mul_mem (conj_mem_altSub_compl s.2 hl) (inv_mem hl)⟩, ?_⟩
      rw [hx, hlh, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
      exact secIncl_congr O hR _ _ rfl
    have h2 : x * lh * x⁻¹ * lh⁻¹ ∈ CFSG.oddCore (secQ (secP O R)) := by
      have h3 : lh * x⁻¹ * lh⁻¹ ∈ CFSG.oddCore (secQ (secP O R)) :=
        (inferInstance : (CFSG.oddCore (secQ (secP O R))).Normal).conj_mem _ (inv_mem hxO) lh
      have := mul_mem hxO h3
      simpa only [mul_assoc] using this
    have h4 : x * lh * x⁻¹ * lh⁻¹ ∈ secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) := ⟨h1, h2⟩
    rw [secL_inf_oddCore O hR hm, mem_bot] at h4
    have h5 : x * lh = lh * x := by
      calc x * lh = x * lh * x⁻¹ * lh⁻¹ * (lh * x) := by group
        _ = lh * x := by rw [h4, one_mul]
    have := comm_of_secIncl_comm O hR _ le_rfl h5
    exact congrArg Subtype.val this
  have hcard : 4 ≤ ((fourSet (m + 3))ᶜ).card := by
    rw [card_fourSet_compl (by omega)]; omega
  have hfix := (mem_centralizer_altSub_iff hcard).1 (mem_centralizer_iff.2 fun l hl => (hcomm l hl).symm)
  have hs1 : s = 1 := by
    apply Subtype.ext
    refine Equiv.ext fun i => ?_
    by_cases hi : i ∈ fourSet (m + 3)
    · exact s.2 i hi
    · exact hfix i (by simpa using hi)
  rw [hs1, map_one]

end Incl

section Inv

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

omit [Finite G] in
theorem swap_mem_fixSub {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3)) (hb : b ∉ fourSet (m + 3)) :
    swap a b ∈ fixSub (fourSet (m + 3)) := fun _ hi =>
  swap_apply_of_ne_of_ne (fun h => ha (h ▸ hi)) (fun h => hb (h ▸ hi))

omit [Finite G] in
theorem exists_conj_tau (hm : 3 ≤ m) {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3))
    (hb : b ∉ fourSet (m + 3)) (hab : a ≠ b) :
    ∃ γ ∈ fixSub (fourSet (m + 3)), γ * OverData.tau m * γ⁻¹ = swap a b := by
  have hp : (⟨m + 1, by omega⟩ : Fin (m + 3)) ∈ (fourSet (m + 3))ᶜ := by
    simp [mem_fourSet]; omega
  have hq : (⟨m + 2, by omega⟩ : Fin (m + 3)) ∈ (fourSet (m + 3))ᶜ := by
    simp [mem_fourSet]; omega
  have ha' : a ∈ (fourSet (m + 3))ᶜ := Finset.mem_compl.2 ha
  have hb' : b ∈ (fourSet (m + 3))ᶜ := Finset.mem_compl.2 hb
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_swap (α := ↥(fourSet (m + 3))ᶜ)
    (w := ⟨⟨m + 1, by omega⟩, hp⟩) (x := ⟨⟨m + 2, by omega⟩, hq⟩) (y := ⟨a, ha'⟩) (z := ⟨b, hb'⟩)
    (by simp [Fin.ext_iff]) (fun h => hab (congrArg Subtype.val h)))
  refine ⟨Perm.ofSubtype c, (fixSubHom (fourSet (m + 3)) c).2, ?_⟩
  have hτ : OverData.tau m = Perm.ofSubtype (swap (⟨⟨m + 1, by omega⟩, hp⟩ :
      ↥(fourSet (m + 3))ᶜ) ⟨⟨m + 2, by omega⟩, hq⟩) := by
    rw [Perm.ofSubtype_swap_eq]; rfl
  rw [hτ, ← map_inv, ← map_mul, ← map_mul, hc, Perm.ofSubtype_swap_eq]

noncomputable abbrev secSwap {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3)) (hb : b ∉ fourSet (m + 3)) :
    secQ (secP O R) :=
  secIncl O hR _ le_rfl ⟨swap a b, swap_mem_fixSub ha hb⟩

omit [Finite G] in
theorem secSwap_mul_self {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3))
    (hb : b ∉ fourSet (m + 3)) : secSwap O hR ha hb * secSwap O hR ha hb = 1 := by
  rw [← map_mul]
  have : (⟨swap a b, swap_mem_fixSub ha hb⟩ * ⟨swap a b, swap_mem_fixSub ha hb⟩ :
      fixSub (fourSet (m + 3))) = 1 := Subtype.ext (swap_mul_self a b)
  rw [this, map_one]

theorem eq_one_of_comm_secSwap (hm : 10 ≤ m) {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3))
    (hb : b ∉ fourSet (m + 3)) (hab : a ≠ b) {x : secQ (secP O R)}
    (hx : x ∈ CFSG.oddCore (secQ (secP O R)))
    (hc : x * secSwap O hR ha hb = secSwap O hR ha hb * x) : x = 1 := by
  obtain ⟨γ, hγ, hγτ⟩ := exists_conj_tau (by omega) ha hb hab
  obtain ⟨o, rfl⟩ := QuotientGroup.mk_surjective x
  set dd : ↥(centralizer (secP O R : Set G)) :=
    ⟨O.φ (swap a b), fixSub_comm_secP O hR (swap_mem_fixSub ha hb)⟩ with hdd
  have h1 : (QuotientGroup.mk dd : secQ (secP O R)) = QuotientGroup.mk (o * dd * o⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change secSwap O hR ha hb = QuotientGroup.mk o * secSwap O hR ha hb * (QuotientGroup.mk o)⁻¹
    rw [hc]
    group
  have h2 := QuotientGroup.eq.1 h1
  have hp : (O.φ (swap a b))⁻¹ * ((o : G) * O.φ (swap a b) * (o : G)⁻¹) ∈ secP O R := h2
  have h3 : IsConj z (O.φ (swap a b)) := O.hconj _ ⟨a, b, hab, rfl⟩
  have hconj : IsConj z (O.φ (γ * OverData.tau m * γ⁻¹) *
      ((O.φ (swap a b))⁻¹ * ((o : G) * O.φ (swap a b) * (o : G)⁻¹))) := by
    rw [hγτ, mul_inv_cancel_left]
    exact h3.trans (isConj_iff.2 ⟨o, rfl⟩)
  have hp1 := eq_one_of_isConj_d_mul O hR hm hγ hp hconj
  have h4 : (o : G) * O.φ (swap a b) * (o : G)⁻¹ = O.φ (swap a b) := by
    calc (o : G) * O.φ (swap a b) * (o : G)⁻¹ = O.φ (swap a b) *
        ((O.φ (swap a b))⁻¹ * ((o : G) * O.φ (swap a b) * (o : G)⁻¹)) := by group
      _ = O.φ (swap a b) := by rw [hp1, mul_one]
  have hod : (o : G) ∈ centralizer ({O.φ (γ * OverData.tau m * γ⁻¹)} : Set G) := by
    rw [hγτ, mem_centralizer_singleton_iff]
    calc (o : G) * O.φ (swap a b) = (o : G) * O.φ (swap a b) * (o : G)⁻¹ * o := by group
      _ = O.φ (swap a b) * o := by rw [h4]
  obtain ⟨r, hr, s, hs, hrs⟩ := exists_of_cent_d O hR o.2 hod
  have hmk := mk_eq_secIncl O hR hr hs hrs
  have hmem : (QuotientGroup.mk o : secQ (secP O R)) ∈
      secS O hR ⊓ CFSG.oddCore (secQ (secP O R)) :=
    Subgroup.mem_inf.2 ⟨⟨⟨s, hs⟩, hmk.symm⟩, hx⟩
  rw [secS_inf_oddCore O hR (by omega)] at hmem
  exact hmem

theorem conj_secSwap_eq_inv (hm : 10 ≤ m) {a b : Fin (m + 3)} (ha : a ∉ fourSet (m + 3))
    (hb : b ∉ fourSet (m + 3)) (hab : a ≠ b) {x : secQ (secP O R)}
    (hx : x ∈ CFSG.oddCore (secQ (secP O R))) :
    secSwap O hR ha hb * x * (secSwap O hR ha hb)⁻¹ = x⁻¹ := by
  set d := secSwap O hR ha hb with hd
  set f : MulAut ↥(CFSG.oddCore (secQ (secP O R))) := MulAut.conjNormal d with hf
  have hfpf : MonoidHom.FixedPointFree f := by
    intro y hy
    have h1 : d * (y : secQ (secP O R)) * d⁻¹ = y := by
      have := congrArg Subtype.val hy
      rwa [hf, MulAut.conjNormal_apply] at this
    have h2 : (y : secQ (secP O R)) * d = d * y := by
      calc (y : secQ (secP O R)) * d = d * y * d⁻¹ * d := by rw [h1]
        _ = d * y := by group
    exact Subtype.ext (eq_one_of_comm_secSwap O hR hm ha hb hab y.2 h2)
  have hinv : Function.Involutive f := by
    intro y
    apply Subtype.ext
    rw [hf, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    have hdd : d * d = 1 := secSwap_mul_self O hR ha hb
    calc d * (d * (y : secQ (secP O R)) * d⁻¹) * d⁻¹ = (d * d) * y * (d * d)⁻¹ := by group
      _ = y := by rw [hdd]; group
  have := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) ⟨x, hx⟩
  have h3 := congrArg Subtype.val this
  rwa [hf, MulAut.conjNormal_apply] at h3

theorem conj_ofSubtype_eq (hm : 10 ≤ m) (y : Perm ↥(fourSet (m + 3))ᶜ) {x : secQ (secP O R)}
    (hx : x ∈ CFSG.oddCore (secQ (secP O R))) :
    secIncl O hR _ le_rfl (fixSubHom _ y) * x * (secIncl O hR _ le_rfl (fixSubHom _ y))⁻¹ =
      if Perm.sign y = 1 then x else x⁻¹ := by
  induction y using Perm.swap_induction_on generalizing x with
  | one => simp
  | swap_mul f a b hab ih =>
    have ha : (a : Fin (m + 3)) ∉ fourSet (m + 3) := Finset.mem_compl.1 a.2
    have hb : (b : Fin (m + 3)) ∉ fourSet (m + 3) := Finset.mem_compl.1 b.2
    have hab' : (a : Fin (m + 3)) ≠ b := fun h => hab (Subtype.ext h)
    have hd : secIncl O hR _ le_rfl (fixSubHom _ (swap a b)) = secSwap O hR ha hb :=
      secIncl_congr O hR _ _ (by
        change Perm.ofSubtype (swap a b) = swap (a : Fin (m + 3)) b
        exact Perm.ofSubtype_swap_eq a b)
    rw [map_mul, map_mul, hd, Perm.sign_mul, Perm.sign_swap hab]
    set F := secIncl O hR _ le_rfl (fixSubHom _ f) with hF
    have e : secSwap O hR ha hb * F * x * (secSwap O hR ha hb * F)⁻¹ =
        secSwap O hR ha hb * (F * x * F⁻¹) * (secSwap O hR ha hb)⁻¹ := by group
    rw [e, ih hx]
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or (Perm.sign f) with h | h
    · simp only [h, mul_one, hne, ↓reduceIte]
      exact conj_secSwap_eq_inv O hR hm ha hb hab' hx
    · rw [h, show (-1 : ℤˣ) * -1 = 1 by decide]
      simp only [hne, ↓reduceIte]
      calc secSwap O hR ha hb * x⁻¹ * (secSwap O hR ha hb)⁻¹ =
          (secSwap O hR ha hb * x * (secSwap O hR ha hb)⁻¹)⁻¹ := by group
        _ = x := by rw [conj_secSwap_eq_inv O hR hm ha hb hab' hx, inv_inv]

theorem secL_comm_oddCore (hm : 10 ≤ m) {l : Perm (Fin (m + 3))}
    (hl : l ∈ altSub (fourSet (m + 3))ᶜ) {x : secQ (secP O R)}
    (hx : x ∈ CFSG.oddCore (secQ (secP O R))) :
    secIncl O hR _ altSub_compl_le ⟨l, hl⟩ * x = x * secIncl O hR _ altSub_compl_le ⟨l, hl⟩ := by
  obtain ⟨y, hy⟩ := (fixSubHom_bijective (fourSet (m + 3))).2 ⟨l, altSub_compl_le hl⟩
  have hsign : Perm.sign y = 1 := by
    have h1 : Perm.sign (Perm.ofSubtype y) = Perm.sign y := Perm.sign_ofSubtype y
    have h2 : (Perm.ofSubtype y : Perm (Fin (m + 3))) = l := congrArg Subtype.val hy
    rw [← h1, h2]
    exact (mem_altSub.1 hl).1
  have h := conj_ofSubtype_eq O hR hm y hx
  simp only [hsign, ↓reduceIte] at h
  rw [hy] at h
  have he : secIncl O hR _ altSub_compl_le ⟨l, hl⟩ =
      secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩ := secIncl_congr O hR _ _ rfl
  rw [he]
  calc secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩ * x =
      secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩ * x *
        (secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩)⁻¹ *
          secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩ := by group
    _ = x * secIncl O hR _ le_rfl ⟨l, altSub_compl_le hl⟩ := by rw [h]

end Inv

section Elts

variable {G : Type*} [Group G]

theorem mul_mul_self_of_comm {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem orderOf_conj' (a x : G) : orderOf (a * x * a⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective x
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Elts

section Dt

variable {m : ℕ}

theorem fin_ne {N : ℕ} {i j : Fin N} (h : (i : ℕ) ≠ j) : i ≠ j := fun h' => h (congrArg Fin.val h')

theorem fin_ne_mk {N : ℕ} {i : Fin N} {k : ℕ} {hk : k < N} (h : (i : ℕ) ≠ k) :
    i ≠ ⟨k, hk⟩ := fun h' => h (congrArg Fin.val h')

theorem dt_mem_altSub_fourTail (hm : 7 ≤ m) :
    swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩ ∈ altSub (fourTail m) := by
  rw [mem_altSub]
  refine ⟨by
    rw [Perm.sign_mul, Perm.sign_swap (fin_ne (by simp)), Perm.sign_swap (fin_ne (by simp))]
    rfl, fun i hi => ?_⟩
  rw [mem_fourTail] at hi
  have h67 : swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩ i = i :=
    swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))
  rw [Perm.mul_apply, h67]
  exact swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))

theorem fourTail_subset_compl' : fourTail m ⊆ (fourSet (m + 3))ᶜ := fourTail_subset_compl

theorem dt_mul_self (hm : 7 ≤ m) :
    (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩) *
      (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩) = 1 :=
  mul_mul_self_of_comm (swap_mul_self _ _) (swap_mul_self _ _)
    (swap_mul_swap_comm_of_ne (fin_ne (by simp)) (fin_ne (by simp)) (fin_ne (by simp))
      (fin_ne (by simp)))

theorem dt_apply_four (hm : 7 ≤ m) :
    (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩) (⟨4, by omega⟩ : Fin (m + 3)) =
      (⟨5, by omega⟩ : Fin (m + 3)) := by
  have h : swap (⟨6, by omega⟩ : Fin (m + 3)) ⟨7, by omega⟩ ⟨4, by omega⟩ = ⟨4, by omega⟩ :=
    swap_apply_of_ne_of_ne (fin_ne_mk (by simp)) (fin_ne_mk (by simp))
  rw [Perm.mul_apply, h, swap_apply_left]

end Dt

section Norm

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

omit [Finite G] in
theorem closure_involutions_secL (hm : 7 ≤ m) :
    closure {u : ↥(secL O hR) | u * u = 1} = ⊤ := by
  have : IsSimpleGroup ↥(secL O hR) := isSimpleGroup_of_alt (by omega) (secLEquiv O hR)
  have hdt := altSub_mono fourTail_subset_compl' (dt_mem_altSub_fourTail hm)
  apply closure_eq_top_of_simple
  · intro a x hx
    change x * x = 1 at hx
    change a * x * a⁻¹ * (a * x * a⁻¹) = 1
    calc a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = 1 := by rw [hx]; group
  · refine ⟨⟨secIncl O hR _ altSub_compl_le ⟨_, hdt⟩, ⟨_, rfl⟩⟩, ?_, ?_⟩
    · apply Subtype.ext
      change secIncl O hR _ altSub_compl_le ⟨_, hdt⟩ * secIncl O hR _ altSub_compl_le ⟨_, hdt⟩ = 1
      rw [← map_mul]
      have : (⟨_, hdt⟩ * ⟨_, hdt⟩ : altSub (fourSet (m + 3))ᶜ) = 1 :=
        Subtype.ext (dt_mul_self hm)
      rw [this, map_one]
    · intro h
      have h1 : secIncl O hR _ altSub_compl_le ⟨_, hdt⟩ = secIncl O hR _ altSub_compl_le 1 := by
        rw [map_one]; exact congrArg Subtype.val h
      have h2 := congrArg Subtype.val (secIncl_injective O hR _ _ h1)
      have h3 := DFunLike.congr_fun h2 ⟨4, by omega⟩
      rw [dt_apply_four hm] at h3
      simp at h3

theorem conj_mem_secL_of_normal (hm : 10 ≤ m)
    (hN : ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))).Normal)
    (g : secQ (secP O R)) {x : secQ (secP O R)} (hx : x ∈ secL O hR) :
    g * x * g⁻¹ ∈ secL O hR := by
  have key : ∀ y ∈ secL O hR, y * y = 1 → g * y * g⁻¹ ∈ secL O hR := by
    intro y hy hy2
    have h1 : QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))) (g * y * g⁻¹) ∈
        (secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R)))) := by
      rw [map_mul, map_mul, map_inv]
      exact hN.conj_mem _ ⟨y, hy, rfl⟩ _
    obtain ⟨l, hl, hle⟩ := h1
    have ho : l⁻¹ * (g * y * g⁻¹) ∈ CFSG.oddCore (secQ (secP O R)) := QuotientGroup.eq.1 hle
    have hlo : l * (l⁻¹ * (g * y * g⁻¹)) = (l⁻¹ * (g * y * g⁻¹)) * l := by
      obtain ⟨⟨l', hl'⟩, rfl⟩ := hl
      exact secL_comm_oddCore O hR hm hl' ho
    have hsq : (l * (l⁻¹ * (g * y * g⁻¹))) ^ 2 = 1 := by
      rw [mul_inv_cancel_left, pow_two]
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    have ho2 := pow_eq_one_of_mul_pow (secL_inf_oddCore O hR (by omega)) hl ho hlo hsq
    have ho1 := eq_one_of_odd_of_sq (orderOf_odd_of_mem_oddCore ho) ho2
    have : g * y * g⁻¹ = l := by
      calc g * y * g⁻¹ = l * (l⁻¹ * (g * y * g⁻¹)) := by group
        _ = l := by rw [ho1, mul_one]
    rw [this]
    exact hl
  have hmem : (⟨x, hx⟩ : ↥(secL O hR)) ∈ closure {u : ↥(secL O hR) | u * u = 1} := by
    rw [closure_involutions_secL O hR (by omega)]; exact mem_top _
  refine closure_induction
    (p := fun (u : ↥(secL O hR)) _ => g * (u : secQ (secP O R)) * g⁻¹ ∈ secL O hR)
    (fun u hu => key u u.2 (congrArg Subtype.val hu)) ?_ ?_ ?_ hmem
  · simp
  · intro u v _ _ hu hv
    have e : g * ((u * v : ↥(secL O hR)) : secQ (secP O R)) * g⁻¹ =
        (g * (u : secQ (secP O R)) * g⁻¹) * (g * (v : secQ (secP O R)) * g⁻¹) := by
      rw [Subgroup.coe_mul]; group
    rw [e]
    exact mul_mem hu hv
  · intro u _ hu
    have e : g * ((u⁻¹ : ↥(secL O hR)) : secQ (secP O R)) * g⁻¹ =
        (g * (u : secQ (secP O R)) * g⁻¹)⁻¹ := by
      rw [Subgroup.coe_inv]; group
    rw [e]
    exact inv_mem hu

end Norm

section Tri

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

omit [Finite G] in
theorem secT_eq_secIncl :
    secT O hR = secIncl O hR _ le_rfl ⟨OverData.tau m, hR.tau_mem_fixSub⟩ := by
  rw [secT, secIncl_apply]
  exact congrArg QuotientGroup.mk (Subtype.ext O.φ_tau.symm)

theorem secT_notMem_center (hm : 6 ≤ m) :
    (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) ∉
      center (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) := by
  intro hc
  have ha : (⟨m, by omega⟩ : Fin (m + 3)) ∉ fourSet (m + 3) := by rw [mem_fourSet]; simp; omega
  have hb : (⟨m + 1, by omega⟩ : Fin (m + 3)) ∉ fourSet (m + 3) := by
    rw [mem_fourSet]; simp; omega
  have hsF := swap_mem_fixSub ha hb
  set sw : fixSub (fourSet (m + 3)) := ⟨_, hsF⟩ with hsw
  set tt : fixSub (fourSet (m + 3)) := ⟨OverData.tau m, hR.tau_mem_fixSub⟩ with htt
  set σ := secIncl O hR _ le_rfl sw with hσ
  have h1 := (mem_center_iff.1 hc) (QuotientGroup.mk σ)
  have h2 : σ * secT O hR * σ⁻¹ * (secT O hR)⁻¹ ∈ CFSG.oddCore (secQ (secP O R)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
    group
  set c := swap (⟨m, by omega⟩ : Fin (m + 3)) ⟨m + 1, by omega⟩ * OverData.tau m *
    (swap (⟨m, by omega⟩ : Fin (m + 3)) ⟨m + 1, by omega⟩)⁻¹ * (OverData.tau m)⁻¹ with hcdef
  have hcF : c ∈ fixSub (fourSet (m + 3)) :=
    mul_mem (mul_mem (mul_mem hsF hR.tau_mem_fixSub) (inv_mem hsF)) (inv_mem hR.tau_mem_fixSub)
  have hcA : c ∈ altSub (fourSet (m + 3))ᶜ := by
    rw [mem_altSub]
    refine ⟨?_, fun i hi => hcF i (by simpa using hi)⟩
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, Perm.sign_swap (fin_ne_mk (by simp)),
      OverData.tau, Perm.sign_swap (fin_ne_mk (by simp))]
    decide
  have h3 : σ * secT O hR * σ⁻¹ * (secT O hR)⁻¹ = secIncl O hR _ altSub_compl_le ⟨c, hcA⟩ := by
    rw [secT_eq_secIncl O hR, hσ, ← htt, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact secIncl_congr O hR _ _ rfl
  have h4 : secIncl O hR _ altSub_compl_le ⟨c, hcA⟩ ∈
      secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) :=
    Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, h3 ▸ h2⟩
  rw [secL_inf_oddCore O hR hm, mem_bot] at h4
  have h5 := congrArg Subtype.val (secIncl_injective O hR _ _ (h4.trans (map_one _).symm))
  have h6 := DFunLike.congr_fun h5 ⟨m + 2, by omega⟩
  simp [hcdef, OverData.tau, swap_apply_def, Fin.ext_iff] at h6

theorem normal_of_sym (hm : 10 ≤ m)
    (h : SymOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) (m - 3)) :
    ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))).Normal := by
  obtain ⟨e, -⟩ := h
  apply Subgroup.normal_of_index_eq_two
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R)))).domRestrict (secL O hR)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have hb1 : QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))) (b : secQ (secP O R)) = 1 := hb
    have : (b : secQ (secP O R)) ∈ secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) :=
      Subgroup.mem_inf.2 ⟨b.2, (QuotientGroup.eq_one_iff _).1 hb1⟩
    rw [secL_inf_oddCore O hR (by omega)] at this
    exact Subtype.ext this
  have e1 := ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective _ _ hinj
  have hcardL : Nat.card ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) =
      Nat.card (alternatingGroup (Fin (m - 1))) :=
    (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr (secLEquiv O hR).toEquiv)
  have hcardX : Nat.card (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) =
      Nat.card (Perm (Fin (m - 1))) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin]
    congr 1
    omega
  have : Nontrivial (Fin (m - 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (m - 1))
  have h3 := Subgroup.card_mul_index
    ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R)))))
  rw [hcardL, hcardX, ← h2] at h3
  have hpos : 0 < Nat.card (alternatingGroup (Fin (m - 1))) := Nat.card_pos
  have h4 : Nat.card (alternatingGroup (Fin (m - 1))) *
      ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))).index =
      Nat.card (alternatingGroup (Fin (m - 1))) * 2 := by
    rw [h3, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h4

theorem conj_mem_secL_of_not (htri : ExactShapeTrichotomy)
    (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G))) (hm : 12 ≤ m)
    (hW : ¬ WreathOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))
      ((secB O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) (m - 3))
    (hHN : m - 3 = 10 → ¬ HNOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))))
    (g : secQ (secP O R)) {x : secQ (secP O R)} (hx : x ∈ secL O hR) :
    g * x * g⁻¹ ∈ secL O hR := by
  have hKX : CFSG.SectionRank.IsKGroupCat (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) :=
    (hK.quotient _).quotient _
  have hOX : CFSG.oddCore (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) = ⊥ :=
    ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _
  rcases htri _ _ _ (m - 3) (by omega) hKX hOX (exactShape_secQ O hR (by omega)) with
    h1 | h2 | h3 | h4
  · exact absurd h1 (secT_notMem_center O hR (by omega))
  · exact absurd h2 hW
  · exact conj_mem_secL_of_normal O hR (by omega) (normal_of_sym O hR (by omega) h3) g hx
  · exact absurd h4.2 (hHN h4.1)

omit [Finite G] in
include hR in
theorem L0_inf_secP : (altSub (fourSet (m + 3))ᶜ).map O.φ ⊓ secP O R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨l, hl, rfl⟩, ⟨r, hr, hrl⟩⟩ := Subgroup.mem_inf.1 hx
  have := O.φ_injective hrl
  subst this
  rw [eq_one_of_mem_R_of_mem_fixSub hR hr (altSub_compl_le hl), map_one]
  exact one_mem _

theorem closure_odd_altSub (hm : 7 ≤ m) :
    closure {u : ↥(altSub (fourSet (m + 3))ᶜ) | Odd (orderOf (u : Perm (Fin (m + 3))))} = ⊤ := by
  have : IsSimpleGroup ↥(altSub (fourSet (m + 3))ᶜ) :=
    isSimpleGroup_of_alt (by rw [card_fourSet_compl (by omega)]; omega) (altSubEquiv _)
  apply closure_eq_top_of_simple
  · intro a x hx
    change Odd (orderOf ((a * x * a⁻¹ : ↥(altSub (fourSet (m + 3))ᶜ)) : Perm (Fin (m + 3))))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, orderOf_conj']
    exact hx
  · have h3 : (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same (fin_ne_mk (by simp)) (fin_ne_mk (by simp))
        (fin_ne_mk (by simp))
    have hmem : swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩ ∈ altSub (fourSet (m + 3))ᶜ := by
      rw [mem_altSub]
      refine ⟨h3.sign, fun i hi => ?_⟩
      have hi' : (i : ℕ) < 4 := by simpa [mem_fourSet] using hi
      have h46 : swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩ i = i :=
        swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))
      rw [Perm.mul_apply, h46]
      exact swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change Odd (orderOf (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
        swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩))
      rw [h3.orderOf]
      decide
    · intro h
      exact h3.ne_one (congrArg Subtype.val h)

omit [Finite G] in
@[expose] def L0Normal (O : OverData G z m) (R : Subgroup (Perm (Fin (m + 3)))) : Prop :=
  ∀ g ∈ centralizer (secP O R : Set G), ∀ l ∈ altSub (fourSet (m + 3))ᶜ,
    ∃ l' ∈ altSub (fourSet (m + 3))ᶜ, g * O.φ l * g⁻¹ = O.φ l'

omit [Finite G] in
include hR in
theorem l0Normal_of_secL
    (hsecL : ∀ (g : secQ (secP O R)) {x : secQ (secP O R)}, x ∈ secL O hR →
      g * x * g⁻¹ ∈ secL O hR) (hm : 7 ≤ m) : L0Normal O R := by
  intro g hg l hl
  have key : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, Odd (orderOf l) →
      ∃ l' ∈ altSub (fourSet (m + 3))ᶜ, g * O.φ l * g⁻¹ = O.φ l' := by
    intro l hl hodd
    obtain ⟨⟨l', hl'⟩, hl'e⟩ := hsecL (QuotientGroup.mk ⟨g, hg⟩)
      (x := secIncl O hR _ altSub_compl_le ⟨l, hl⟩) ⟨_, rfl⟩
    set gg : ↥(centralizer (secP O R : Set G)) := ⟨g, hg⟩ with hgg
    set ll : ↥(centralizer (secP O R : Set G)) :=
      ⟨O.φ l, fixSub_comm_secP O hR (altSub_compl_le hl)⟩ with hll
    set ll' : ↥(centralizer (secP O R : Set G)) :=
      ⟨O.φ l', fixSub_comm_secP O hR (altSub_compl_le hl')⟩ with hll'
    have h1 : (QuotientGroup.mk ll' : secQ (secP O R)) = QuotientGroup.mk (gg * ll * gg⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hl'e
    have h2 := QuotientGroup.eq.1 h1
    have hp : (O.φ l')⁻¹ * (g * O.φ l * g⁻¹) ∈ secP O R := h2
    obtain ⟨r, hr, hre⟩ := hp
    have he : g * O.φ l * g⁻¹ = O.φ l' * O.φ r := by rw [hre]; group
    have hk : (O.φ l' * O.φ r) ^ orderOf l = 1 := by
      rw [← he, conj_pow, ← map_pow, pow_orderOf_eq_one, map_one, mul_one, mul_inv_cancel]
    have hcomm : O.φ l' * O.φ r = O.φ r * O.φ l' :=
      O.φ_comm_iff.2 (hR.comm_fixSub hr (altSub_compl_le hl')).symm
    have hr1 := pow_eq_one_of_mul_pow (L0_inf_secP O hR) ⟨l', hl', rfl⟩ ⟨r, hr, rfl⟩ hcomm hk
    have hr4 : (O.φ r) ^ 4 = 1 := by rw [← map_pow, hR.pow_four r hr, map_one]
    have hr' := eq_one_of_pow_four_of_odd hr4 hodd hr1
    exact ⟨l', hl', by rw [he, hr', mul_one]⟩
  have hmem : (⟨l, hl⟩ : ↥(altSub (fourSet (m + 3))ᶜ)) ∈
      closure {u : ↥(altSub (fourSet (m + 3))ᶜ) | Odd (orderOf (u : Perm (Fin (m + 3))))} := by
    rw [closure_odd_altSub (by omega)]
    exact mem_top _
  refine closure_induction
    (p := fun (u : ↥(altSub (fourSet (m + 3))ᶜ)) _ =>
      ∃ l' ∈ altSub (fourSet (m + 3))ᶜ, g * O.φ u * g⁻¹ = O.φ l')
    (fun u hu => key u u.2 hu) ?_ ?_ ?_ hmem
  · exact ⟨1, one_mem _, by simp⟩
  · rintro u v _ _ ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    rw [Subgroup.coe_mul, map_mul, map_mul, ← hae, ← hbe]
    group
  · rintro u _ ⟨a, ha, hae⟩
    refine ⟨a⁻¹, inv_mem ha, ?_⟩
    rw [Subgroup.coe_inv, map_inv, map_inv, ← hae]
    group

end Tri

section Inst

variable {m : ℕ}

theorem secR_klein (hm : 3 ≤ m) : SecR m (kleinR (N := m + 3) (by omega)) where
  le := kleinR_le _
  comm := kleinR_comm _
  trans := kleinR_transitive _
  three_le := hm
  pow_four := fun r hr => by
    refine closure_induction (p := fun x _ => x ^ 4 = 1) ?_ ?_ ?_ ?_ hr
    · rintro x (rfl | rfl)
      · rw [kleinA, ← map_pow, show (swap (0 : Fin 4) 1 * swap 2 3) ^ 4 = 1 by decide, map_one]
      · rw [kleinB, ← map_pow, show (swap (0 : Fin 4) 2 * swap 1 3) ^ 4 = 1 by decide, map_one]
    · exact one_pow 4
    · intro x y hx hy ihx ihy
      rw [Commute.mul_pow (kleinR_comm _ x hx y hy), ihx, ihy, one_mul]
    · intro x _ ih
      rw [inv_pow, ih, inv_one]

theorem secR_cyc (hm : 3 ≤ m) : SecR m (cycR (N := m + 3) (by omega)) where
  le := cycR_le _
  comm := cycR_comm _
  trans := cycR_transitive _
  three_le := hm
  pow_four := fun r hr => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    have hc4 : cycC (N := m + 3) (by omega) ^ 4 = 1 := by
      rw [cycC, ← map_pow,
        show (swap (0 : Fin 4) 3 * swap 0 1 * swap 0 2) ^ 4 = 1 by decide, map_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc4, one_zpow]

end Inst

end CFSG.OddStandard.AltStdSec
