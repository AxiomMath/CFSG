module

public import CFSG.Walter.W67.CentralExt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCls2

public section

namespace CFSG.QuasithinUnique.AppC

open Equiv
open scoped commutatorElement

@[expose] def zA : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def cA : Perm (Fin 5) := swap 1 2 * swap 2 3

theorem zA_sign : Perm.sign zA = 1 := by decide +kernel

theorem cA_sign : Perm.sign cA = 1 := by decide +kernel

theorem zA_sq : zA * zA = 1 := by decide +kernel

theorem zA_ne_one : zA ≠ 1 := by decide +kernel

theorem zB_ne_one : cA * zA * cA⁻¹ ≠ 1 := by decide +kernel

theorem zB_ne_zA : cA * zA * cA⁻¹ ≠ zA := by decide +kernel

theorem zC_eq : (zA * (cA * zA * cA⁻¹))⁻¹ * (cA * (cA * zA * cA⁻¹) * cA⁻¹) = 1 := by
  decide +kernel

theorem alt5_commutator_eq_top : commutator (alternatingGroup (Fin 5)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with
    h | h
  · exfalso
    let a : alternatingGroup (Fin 5) :=
      ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩
    let b : alternatingGroup (Fin 5) :=
      ⟨swap 0 1 * swap 1 3, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩
    have h1 : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 5)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    revert h2
    decide +kernel
  · exact h

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide +kernel

theorem card_eq_four_of_two_involutions (H : Subgroup (alternatingGroup (Fin 5)))
    (hH : ∀ x ∈ H, x * x = 1) {a b : alternatingGroup (Fin 5)} (ha : a ∈ H) (hb : b ∈ H)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : b ≠ a) : Nat.card H = 4 := by
  have hp : IsPGroup 2 H := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hH x x.2)⟩
  have hdvd : Nat.card H ∣ 60 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [card_alt5] at this
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h8 : 8 ∣ 60 := by
      refine (pow_dvd_pow 2 hcon : 2 ^ 3 ∣ 2 ^ n).trans ?_
      rw [← hn]; exact hdvd
    omega
  interval_cases n
  · exfalso
    have : H = ⊥ := by
      rw [← Subgroup.card_eq_one]; simpa using hn
    rw [this] at ha
    exact ha1 (Subgroup.mem_bot.1 ha)
  · exfalso
    have hord : orderOf a = 2 := by
      refine orderOf_eq_prime ?_ ha1
      rw [pow_two]; exact hH a ha
    have hz : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.2 ha
    have hcard : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, hord]
    have heq : Subgroup.zpowers a = H := by
      refine Subgroup.eq_of_le_of_card_ge hz ?_
      rw [hcard]; simpa using hn.le
    rw [← heq] at hb
    rcases eq_one_or_of_mem_zpowers (by rw [pow_two]; exact hH a ha) hb with h | h
    · exact hb1 h
    · exact hab h
  · simpa using hn

theorem central_cover_trivial {Λ : Type*} [Group Λ] [Finite Λ]
    (hL : ∀ (N : Subgroup Λ) [N.Normal], IsPGroup 2 (Λ ⧸ N) → N = ⊤)
    (α : Λ →* alternatingGroup (Fin 5)) (hα : Function.Surjective α)
    (U : Subgroup Λ) [U.Normal] (hUQ : U ≤ α.ker) (hQ2 : ∀ q ∈ α.ker, q * q = 1)
    (hcomm : ∀ q ∈ α.ker, ∀ g : Λ, q * g * q⁻¹ * g⁻¹ ∈ U)
    (ℓ : Λ) (hℓ : ℓ * ℓ = 1)
    (hαℓ : ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = zA) : α.ker ≤ U := by
  classical
  let mk : Λ →* Λ ⧸ U := QuotientGroup.mk' U
  let ᾱ : Λ ⧸ U →* alternatingGroup (Fin 5) := QuotientGroup.lift U α (fun u hu => hUQ hu)
  have hᾱmk : ∀ g, ᾱ (mk g) = α g := fun g => rfl
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective U
  have hᾱ : Function.Surjective ᾱ := fun a => by
    obtain ⟨g, hg⟩ := hα a
    exact ⟨mk g, by rw [hᾱmk, hg]⟩
  have hKmk : ∀ z ∈ ᾱ.ker, ∃ q ∈ α.ker, mk q = z := by
    intro z hz
    obtain ⟨q, rfl⟩ := hmk_surj z
    exact ⟨q, hz, rfl⟩
  have hK2 : ∀ z ∈ ᾱ.ker, z * z = 1 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hKmk z hz
    rw [← map_mul, hQ2 q hq, map_one]
  have hKc : ∀ z ∈ ᾱ.ker, ∀ y : Λ ⧸ U, y * z = z * y := by
    intro z hz y
    obtain ⟨q, hq, rfl⟩ := hKmk z hz
    obtain ⟨g, rfl⟩ := hmk_surj y
    rw [← map_mul, ← map_mul]
    change ((g * q : Λ) : Λ ⧸ U) = ((q * g : Λ) : Λ ⧸ U)
    rw [QuotientGroup.eq_iff_div_mem]
    have h1 := inv_mem (hcomm q hq g)
    have e : g * q / (q * g) = (q * g * q⁻¹ * g⁻¹)⁻¹ := by rw [div_eq_mul_inv]; group
    rw [e]
    exact h1
  have hKcenter : ᾱ.ker ≤ Subgroup.center (Λ ⧸ U) := fun z hz =>
    Subgroup.mem_center_iff.2 fun y => hKc z hz y
  have hperf : commutator (Λ ⧸ U) = ⊤ := by
    set C := commutator (Λ ⧸ U) with hC
    have hCtop : C.map ᾱ = commutator (alternatingGroup (Fin 5)) := by
      rw [hC, commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hᾱ]
    rw [alt5_commutator_eq_top] at hCtop
    have hCK : ∀ y : Λ ⧸ U, ∃ z ∈ ᾱ.ker, ∃ c ∈ C, y = z * c := by
      intro y
      have hy : ᾱ y ∈ C.map ᾱ := by rw [hCtop]; trivial
      obtain ⟨c, hc, hcy⟩ := hy
      refine ⟨y * c⁻¹, ?_, c, hc, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, mul_inv_cancel]
    let N : Subgroup Λ := C.comap mk
    have hN : N.Normal := Subgroup.Normal.comap inferInstance mk
    have hNtop : N = ⊤ := by
      apply hL N
      intro x'
      induction x' using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨z, hz, c, hc, hy⟩ := hCK (mk g)
        obtain ⟨q, hq, rfl⟩ := hKmk z hz
        have h1 : (g : Λ ⧸ N) = (q : Λ ⧸ N) := by
          rw [QuotientGroup.eq]
          show mk (g⁻¹ * q) ∈ C
          have e : mk (g⁻¹ * q) = c⁻¹ := by
            rw [map_mul, map_inv, hy]
            group
          rw [e]
          exact inv_mem hc
        refine ⟨1, ?_⟩
        have hq2 : q ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two]; exact hQ2 q hq
        rw [h1, ← QuotientGroup.mk_pow, hq2, QuotientGroup.mk_one]
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨g, rfl⟩ := hmk_surj y
    have : g ∈ N := by rw [hNtop]; trivial
    exact this
  have hcA : cA ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 cA_sign
  obtain ⟨g, hg⟩ := hα ⟨cA, hcA⟩
  set ℓ₂ : Λ := g * ℓ * g⁻¹ with hℓ₂def
  set ℓ₃ : Λ := g * ℓ₂ * g⁻¹ with hℓ₃def
  have hℓ₂ : ℓ₂ * ℓ₂ = 1 := by
    calc ℓ₂ * ℓ₂ = g * (ℓ * ℓ) * g⁻¹ := by rw [hℓ₂def]; group
      _ = 1 := by rw [hℓ]; group
  have hℓ₃ : ℓ₃ * ℓ₃ = 1 := by
    calc ℓ₃ * ℓ₃ = g * (ℓ₂ * ℓ₂) * g⁻¹ := by rw [hℓ₃def]; group
      _ = 1 := by rw [hℓ₂]; group
  have hα₂ : ((α ℓ₂ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = cA * zA * cA⁻¹ := by
    rw [hℓ₂def, map_mul, map_mul, map_inv, hg]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαℓ]
  have hα₃ : ((α ℓ₃ : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      cA * (cA * zA * cA⁻¹) * cA⁻¹ := by
    rw [hℓ₃def, map_mul, map_mul, map_inv, hg]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα₂]
  set a : Λ ⧸ U := mk ℓ with ha_def
  set b : Λ ⧸ U := mk ℓ₂ with hb_def
  set c : Λ ⧸ U := mk ℓ₃ with hc_def
  have ha : a * a = 1 := by rw [ha_def, ← map_mul, hℓ, map_one]
  have hb : b * b = 1 := by rw [hb_def, ← map_mul, hℓ₂, map_one]
  have hc : c * c = 1 := by rw [hc_def, ← map_mul, hℓ₃, map_one]
  set k : Λ ⧸ U := (a * b)⁻¹ * c with hk_def
  have hk : k ∈ ᾱ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [hk_def, map_mul, map_inv, ha_def, hb_def, hc_def, hᾱmk, Subgroup.coe_mul,
      Subgroup.coe_inv, hαℓ, hα₂, hα₃]
    exact zC_eq
  have hkc : ∀ y, y * k = k * y := hKc k hk
  have hk2 : k * k = 1 := hK2 k hk
  have hcab : c = a * b * k := by rw [hk_def]; group
  have hab2 : (a * b) * (a * b) = 1 := by
    have h2 : c * c = (a * b) * (a * b) * (k * k) := by
      calc c * c = a * b * k * (a * b * k) := by rw [← hcab]
        _ = a * b * (k * (a * b)) * k := by group
        _ = a * b * ((a * b) * k) * k := by rw [← hkc (a * b)]
        _ = (a * b) * (a * b) * (k * k) := by group
    rw [hc, hk2, mul_one] at h2
    exact h2.symm
  have hcomm_ab : a * b = b * a := by
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
    exact h1.symm
  let s : Set (Λ ⧸ U) := (ᾱ.ker : Set (Λ ⧸ U)) ∪ {a, b}
  have hscomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx
    · exact (hKc x hx y).symm
    · rcases hy with hy | hy
      · exact hKc y hy x
      · rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · rfl
          · rw [Set.mem_singleton_iff.1 hy]; exact hcomm_ab
        · rw [Set.mem_singleton_iff.1 hx]
          rcases hy with rfl | hy
          · exact hcomm_ab.symm
          · rw [Set.mem_singleton_iff.1 hy]
  have hRc : IsMulCommutative (Subgroup.closure s) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hscomm x hx y hy)
  have hR2 : ∀ r ∈ Subgroup.closure s, r * r = 1 := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hK2 x hx
      · rcases hx with rfl | hx
        · exact ha
        · rw [Set.mem_singleton_iff.1 hx]; exact hb
    | one => simp
    | mul x y hxR hyR hx hy =>
      have hcomm := hRc.is_comm.comm ⟨x, hxR⟩ ⟨y, hyR⟩
      have hxy : x * y = y * x := congrArg Subtype.val hcomm
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx, hy, one_mul]
    | inv x hxR hx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx, inv_one]
  have hRp : IsPGroup 2 (Subgroup.closure s) := fun r =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hR2 r r.2)⟩
  have hKR : ᾱ.ker ≤ Subgroup.closure s := fun z hz => Subgroup.subset_closure (Or.inl hz)
  have haR : a ∈ Subgroup.closure s := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hbR : b ∈ Subgroup.closure s := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hH2 : ∀ x ∈ (Subgroup.closure s).map ᾱ, x * x = 1 := by
    rintro x ⟨r, hr, rfl⟩
    rw [← map_mul, hR2 r hr, map_one]
  have hHa : ᾱ a ∈ (Subgroup.closure s).map ᾱ := ⟨a, haR, rfl⟩
  have hHb : ᾱ b ∈ (Subgroup.closure s).map ᾱ := ⟨b, hbR, rfl⟩
  have hαa : ((ᾱ a : alternatingGroup (Fin 5)) : Perm (Fin 5)) = zA := by
    rw [ha_def, hᾱmk, hαℓ]
  have hαb : ((ᾱ b : alternatingGroup (Fin 5)) : Perm (Fin 5)) = cA * zA * cA⁻¹ := by
    rw [hb_def, hᾱmk, hα₂]
  have hH4 : Nat.card ((Subgroup.closure s).map ᾱ) = 4 := by
    refine card_eq_four_of_two_involutions _ hH2 hHa hHb ?_ ?_ ?_
    · intro h
      have := congrArg Subtype.val h
      rw [hαa] at this
      exact zA_ne_one this
    · intro h
      have := congrArg Subtype.val h
      rw [hαb] at this
      exact zB_ne_one this
    · intro h
      have := congrArg Subtype.val h
      rw [hαb, hαa] at this
      exact zB_ne_zA this
  have hE : Nat.card (Λ ⧸ U) = Nat.card ᾱ.ker * 60 := by
    have h := Subgroup.card_ker_mul_card_range ᾱ
    rw [MonoidHom.range_eq_top.2 hᾱ, Subgroup.card_top, card_alt5] at h
    exact h.symm
  have hRcard : Nat.card (Subgroup.closure s) = Nat.card ᾱ.ker * 4 := by
    have h := Subgroup.card_ker_mul_card_range (ᾱ.domRestrict (Subgroup.closure s))
    rw [MonoidHom.domRestrict_range, hH4] at h
    have hker : Nat.card (ᾱ.domRestrict (Subgroup.closure s)).ker = Nat.card ᾱ.ker := by
      rw [MonoidHom.ker_domRestrict]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR).toEquiv
    rw [hker] at h
    exact h.symm
  have hidx : (Subgroup.closure s).index = 15 := by
    have h := Subgroup.card_mul_index (Subgroup.closure s)
    rw [hRcard, hE, mul_assoc] at h
    have hpos : 0 < Nat.card ᾱ.ker := Nat.card_pos
    have h2 := Nat.eq_of_mul_eq_mul_left hpos h
    omega
  have hodd : ¬ 2 ∣ (Subgroup.closure s).index := by rw [hidx]; decide
  have hKp : IsPGroup 2 ᾱ.ker := fun z => ⟨1, Subtype.ext (by simpa [pow_two] using hK2 z z.2)⟩
  have hinf := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup (hRp.toSylow hodd) hRc
    hKcenter hKp
  rw [hperf, inf_top_eq] at hinf
  intro q hq
  have hmq : mk q ∈ ᾱ.ker := hq
  rw [hinf, Subgroup.mem_bot] at hmq
  exact (QuotientGroup.eq_one_iff q).1 hmq

end CFSG.QuasithinUnique.AppC
