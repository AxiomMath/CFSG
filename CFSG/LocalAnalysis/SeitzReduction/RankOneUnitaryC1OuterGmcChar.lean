module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsF
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem gmc_exists_comm_eq_of_card_le {G : Type} [Group G] [Finite G] {H A : Subgroup G} {x : G}
    (h : ∀ w ∈ H, w * x * w⁻¹ * x⁻¹ ∈ A)
    (hcard : Nat.card ((centralizer ({x} : Set G)).subgroupOf H) * Nat.card A ≤ Nat.card H)
    {a : G} (ha : a ∈ A) : ∃ w ∈ H, w * x * w⁻¹ * x⁻¹ = a := by
  classical
  set C : Subgroup H := (centralizer ({x} : Set G)).subgroupOf H with hC
  let F : H ⧸ C → A := Quotient.lift
    (fun w : H => (⟨(w : G) * x * (w : G)⁻¹ * x⁻¹, h w w.2⟩ : A)) (by
      intro w w' hww'
      have hmem : w⁻¹ * w' ∈ C := QuotientGroup.leftRel_apply.mp hww'
      rw [hC, mem_subgroupOf, mem_centralizer_iff] at hmem
      have hc := hmem x (Set.mem_singleton x)
      simp only [coe_mul, coe_inv] at hc
      apply Subtype.ext
      have e : (w' : G) * x * (w' : G)⁻¹ = (w : G) * x * (w : G)⁻¹ := by
        calc (w' : G) * x * (w' : G)⁻¹ =
              (w : G) * (((w : G)⁻¹ * (w' : G)) * x) * ((w : G)⁻¹ * (w' : G))⁻¹ * (w : G)⁻¹ := by
                group
          _ = (w : G) * (x * ((w : G)⁻¹ * (w' : G))) * ((w : G)⁻¹ * (w' : G))⁻¹ * (w : G)⁻¹ := by
                rw [hc]
          _ = (w : G) * x * (w : G)⁻¹ := by group
      show (w : G) * x * (w : G)⁻¹ * x⁻¹ = (w' : G) * x * (w' : G)⁻¹ * x⁻¹
      rw [e])
  have hF : Function.Injective F := by
    intro p p' hpp'
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective p'
    have e : (w : G) * x * (w : G)⁻¹ * x⁻¹ = (w' : G) * x * (w' : G)⁻¹ * x⁻¹ :=
      congrArg Subtype.val hpp'
    apply QuotientGroup.eq.mpr
    rw [hC, mem_subgroupOf, mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simp only [coe_mul, coe_inv]
    have e2 : (w : G) * x * (w : G)⁻¹ = (w' : G) * x * (w' : G)⁻¹ := mul_right_cancel e
    calc x * ((w : G)⁻¹ * (w' : G)) = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w' : G) := by group
      _ = (w : G)⁻¹ * ((w' : G) * x * (w' : G)⁻¹) * (w' : G) := by rw [e2]
      _ = (w : G)⁻¹ * (w' : G) * x := by group
  have hle : Nat.card A ≤ Nat.card (H ⧸ C) := by
    have h1 := C.card_mul_index
    rw [Subgroup.index] at h1
    have hpos : 0 < Nat.card C := Nat.card_pos
    have h2 : Nat.card C * Nat.card A ≤ Nat.card C * Nat.card (H ⧸ C) := by
      rw [h1]
      exact hcard
    exact Nat.le_of_mul_le_mul_left h2 hpos
  obtain ⟨p, hp⟩ := (hF.bijective_of_nat_card_le hle).2 ⟨a, ha⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨w, w.2, congrArg Subtype.val hp⟩

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem gmc_mem_W_of_comm_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {W : Subgroup G}
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W))
    {y : G} (hyT : y ∈ T) (hyS : y ∉ szT₁ L T ⊔ zpowers t) {d : G} (hd : d ∈ szT₁ L T)
    (hdy : d * y * d⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T)) : d ∈ W := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, hA₁comm, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hTA : ∀ n ∈ T, ∀ a ∈ szA₁ (szT₁ L T), n * a * n⁻¹ ∈ szA₁ (szT₁ L T) := fun n hn a ha =>
    U3RootCoords.conj_mem_szA₁_of_mem_normalizer (hTN₁ hn) ha
  have hpow : ∀ n : ℕ, d * y ^ n * d⁻¹ * (y ^ n)⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show d * y ^ (n + 1) * d⁻¹ * (y ^ (n + 1))⁻¹ =
        (d * y ^ n * d⁻¹ * (y ^ n)⁻¹) * (y ^ n * (d * y * d⁻¹ * y⁻¹) * (y ^ n)⁻¹) by
          rw [pow_succ]; group]
      exact mul_mem ih (hTA _ (pow_mem hyT n) _ hdy)
  obtain ⟨j, hj1, hj2⟩ := StrongClosureMod.exists_pow_not_mem h.isPGroup hyT hyS
  have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (pow_mem hyT _) hwT hj2
    (by rw [hw2]; exact one_mem _) hj1 hwS
  have hpj := hpow (2 ^ j)
  have hy'T : y ^ 2 ^ j ∈ T := pow_mem hyT _
  generalize y ^ 2 ^ j = y' at hM hpj hy'T
  have hdk : d * (y' * w⁻¹) * d⁻¹ * (y' * w⁻¹)⁻¹ ∈ szA₁ (szT₁ L T) := by
    obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
    rw [← haz]
    have hdz : Commute d z :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ d hd)
    have h1 : z * d⁻¹ = d⁻¹ * z := hdz.inv_left.eq.symm
    have e : d * (a * z) * d⁻¹ * (a * z)⁻¹ = d * a * d⁻¹ * a⁻¹ := by
      calc d * (a * z) * d⁻¹ * (a * z)⁻¹ = d * a * (z * d⁻¹) * z⁻¹ * a⁻¹ := by group
        _ = d * a * (d⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [h1]
        _ = d * a * d⁻¹ * a⁻¹ := by group
    rw [e, hA₁comm]
    have := commutator_mem_commutator hd ha
    rwa [commutatorElement_def] at this
  have hdw : d * w * d⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
    have hkT : y' * w⁻¹ ∈ T := mul_mem hy'T (inv_mem hwT)
    have h1 : (y' * w⁻¹) * (d * w * d⁻¹ * w⁻¹) * (y' * w⁻¹)⁻¹ ∈ szA₁ (szT₁ L T) := by
      have e : (y' * w⁻¹) * (d * w * d⁻¹ * w⁻¹) * (y' * w⁻¹)⁻¹ =
          (d * (y' * w⁻¹) * d⁻¹ * (y' * w⁻¹)⁻¹)⁻¹ * (d * y' * d⁻¹ * y'⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem hdk) hpj
    have h2 := hTA _ (inv_mem hkT) _ h1
    rwa [show (y' * w⁻¹)⁻¹ * ((y' * w⁻¹) * (d * w * d⁻¹ * w⁻¹) * (y' * w⁻¹)⁻¹) *
      (y' * w⁻¹)⁻¹⁻¹ = d * w * d⁻¹ * w⁻¹ by group] at h2
  refine (hWiff d hd).mp ?_
  have e : d⁻¹ * (w * d * w⁻¹) = d⁻¹ * (d * w * d⁻¹ * w⁻¹)⁻¹ * d := by group
  rw [e]
  have h5 := mem_centralizer_iff.mp (mem_szA₁.mp (inv_mem hdw)).2 d hd
  rw [mul_assoc, ← h5, ← mul_assoc, inv_mul_cancel, one_mul]
  exact inv_mem hdw

end U3Start

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmc_exists_conj_tw {x : G} (hxv : x * (t * w)⁻¹ ∈ U₁) (hx2 : x ^ 2 = 1) :
    ∃ u ∈ U₁, u * (t * w) * u⁻¹ = x := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W', hW'T₁, hAW', hW'card, -, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hvv : (t * w) * (t * w) = 1 := by rw [← sq]; exact hW.tw_sq
  have hvinv : (t * w)⁻¹ = t * w := inv_eq_of_mul_eq_one_right hvv
  have hvN : ∀ u ∈ U₁, (t * w) * u * (t * w)⁻¹ ∈ U₁ := fun u hu =>
    (mem_normalizer_iff.mp (hL.T_le hW.tw_mem) u).mp hu
  have hXW : ∀ c ∈ U₁, (t * w) * c * (t * w)⁻¹ = c⁻¹ → c ∈ W' ⊔ V := by
    intro c hcU hinv
    refine hL.gms_mem_sup_of_comm_mem_szA₁ hS hW.tw_mem (fun r hr => hW.tw_inv hr) hW'iff hcU ?_
    have e : c * (t * w) * c⁻¹ * (t * w)⁻¹ = c * ((t * w) * c * (t * w)⁻¹)⁻¹ := by group
    rw [e, hinv, inv_inv, ← sq]
    exact hL.muOne_sq_mem_szA₁ hS hc hW.mu hK hμ hcU
  have hW'V : Nat.card (W' ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 3 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := W') (fun y hy => hL.muOne_T₁_le_normalizer hS (hW'T₁ hy))
    have hinf : 2 ^ f ≤ Nat.card (V ⊓ W' : Subgroup G) := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le (le_inf hS.conf.le hAW')
    rw [hS.conf.card, hW'card, sup_comm] at h1
    have h2 : Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
      calc Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤
            Nat.card (W' ⊔ V : Subgroup G) * Nat.card (V ⊓ W' : Subgroup G) :=
            Nat.mul_le_mul_left _ hinf
        _ = (2 ^ f) ^ 3 * 2 ^ f := by rw [h1]; ring
    exact Nat.le_of_mul_le_mul_right h2 hq0
  have hφ : ∀ u ∈ U₁, u * (t * w) * u⁻¹ * (t * w)⁻¹ ∈ W' ⊔ V := by
    intro u hu
    refine hXW _ ?_ ?_
    · rw [show u * (t * w) * u⁻¹ * (t * w)⁻¹ = u * ((t * w) * u⁻¹ * (t * w)⁻¹) by group]
      exact mul_mem hu (hvN _ (inv_mem hu))
    · have e1 : (t * w) * (u * (t * w) * u⁻¹ * (t * w)⁻¹) * (t * w)⁻¹ =
          (t * w) * u * (t * w) * u⁻¹ * ((t * w)⁻¹ * (t * w)⁻¹) := by group
      have e2 : (u * (t * w) * u⁻¹ * (t * w)⁻¹)⁻¹ = (t * w) * u * (t * w)⁻¹ * u⁻¹ := by group
      rw [e1, e2, hvinv, hvv, mul_one]
  have hcard : Nat.card ((centralizer ({t * w} : Set G)).subgroupOf U₁) *
      Nat.card (W' ⊔ V : Subgroup G) ≤ Nat.card U₁ := by
    have h1 : Nat.card ((centralizer ({t * w} : Set G)).subgroupOf U₁) = (2 ^ f) ^ 2 := by
      rw [← hW.card_F, ← card_map_of_injective U₁.subtype_injective, subgroupOf_map_subtype,
        inf_comm]
    rw [h1, hL.muOne_card_U₁ hS]
    calc (2 ^ f) ^ 2 * Nat.card (W' ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 3 :=
          Nat.mul_le_mul_left _ hW'V
      _ = (2 ^ f) ^ 5 := by ring
  have hcx : x * (t * w)⁻¹ ∈ W' ⊔ V := by
    refine hXW _ hxv ?_
    have hxx : x * x = 1 := by rw [← sq]; exact hx2
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have e1 : (t * w) * (x * (t * w)⁻¹) * (t * w)⁻¹ = (t * w) * x * ((t * w)⁻¹ * (t * w)⁻¹) := by
      group
    have e2 : (x * (t * w)⁻¹)⁻¹ = (t * w) * x⁻¹ := by group
    rw [e1, e2, hvinv, hvv, mul_one, hxinv]
  obtain ⟨u, hu, hu'⟩ := gmc_exists_comm_eq_of_card_le hφ hcard hcx
  refine ⟨u, hu, ?_⟩
  calc u * (t * w) * u⁻¹ = (u * (t * w) * u⁻¹ * (t * w)⁻¹) * (t * w) := by group
    _ = x := by rw [hu']; group

theorem gmc_conj_mul_tw_not_mem (g : G) : g * t * g⁻¹ * (t * w)⁻¹ ∉ U₁ := by
  intro hx
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [show (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ by rw [sq, sq]; group,
      hW.step.start.sq_eq_one]
    group
  obtain ⟨u, -, hu⟩ := hW.gmc_exists_conj_tw hx hx2
  apply u3C1GmsNotConjInput_holds G L f t T R₂ D d V U U₁ w s P hW (u⁻¹ * g)
  calc u⁻¹ * g * t * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * t * g⁻¹) * u := by group
    _ = t * w := by rw [← hu]; group

theorem gmc_false_of_conj_mem_U₁ {c : G} (hx : c * t * c⁻¹ ∈ U₁)
    (hC : ∀ u ∈ U₁, u * (c * t * c⁻¹) = (c * t * c⁻¹) * u → c⁻¹ * u * c ∈ T) : False := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨hT₁card, hA₁card, -, -, hinvT, hA₁2, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨W, -, -, hWcard, -, -, -, hWiff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.w_mem hW.w_sq hW.w_not_mem
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set C := (centralizer ({c * t * c⁻¹} : Set G)).subgroupOf U₁ with hCdef
  have hbound := card_le_card_centralizer_mul_card_of_comm_mem (H := U₁)
    (A := szA₁ (szT₁ L T)) (x := c * t * c⁻¹) fun u hu => hcommA u hu _ hx
  rw [hL.muOne_card_U₁ hS, hA₁card] at hbound
  have hCcard : (2 ^ f) ^ 4 ≤ Nat.card C := by
    have h2 : (2 ^ f) ^ 4 * 2 ^ f ≤ Nat.card C * 2 ^ f := by rw [← pow_succ]; exact hbound
    exact Nat.le_of_mul_le_mul_right h2 hq0
  set D : Subgroup G := (C.map U₁.subtype).map (MulAut.conj c⁻¹).toMonoidHom with hDdef
  have hDcard : Nat.card D = Nat.card C := by
    rw [hDdef, card_map_of_injective (MulAut.conj c⁻¹).injective,
      card_map_of_injective U₁.subtype_injective]
  have hDmem : ∀ a ∈ D, c * a * c⁻¹ ∈ U₁ ∧
      c * a * c⁻¹ * (c * t * c⁻¹) = (c * t * c⁻¹) * (c * a * c⁻¹) := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hu' := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hu)
    have e : c * ((MulAut.conj c⁻¹).toMonoidHom (U₁.subtype u)) * c⁻¹ = (u : G) := by
      simp; group
    rw [e]
    exact ⟨u.2, hu'⟩
  have hDT : D ≤ T := by
    intro a ha
    obtain ⟨haU, hax⟩ := hDmem a ha
    have := hC _ haU hax
    rwa [show c⁻¹ * (c * a * c⁻¹) * c = a by group] at this
  by_cases hDH : D ≤ szT₁ L T ⊔ zpowers t
  ·
    have h1 := Subgroup.card_le_of_le hDH
    rw [h.card_szT₁_sup_of_card_sylow hS2, hDcard] at h1
    have h2 : 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := by
      calc 2 * (2 ^ f) ^ 3 < 2 ^ f * (2 ^ f) ^ 3 :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = (2 ^ f) ^ 4 := by ring
    omega
  · obtain ⟨y, hyD, hyH⟩ : ∃ y ∈ D, y ∉ szT₁ L T ⊔ zpowers t := by
      by_contra hcon
      push Not at hcon
      exact hDH hcon
    have hyT := hDT hyD
    have hT₁D : szT₁ L T ⊓ D ≤ W := by
      intro a ha
      obtain ⟨haT₁, haD⟩ := mem_inf.mp ha
      refine h.gmc_mem_W_of_comm_mem hS2 hW.w_mem hW.w_sq hW.w_not_mem hWiff hyT hyH haT₁ ?_
      have hT : a * y * a⁻¹ * y⁻¹ ∈ szT₁ L T := by
        have h1 : y * a⁻¹ * y⁻¹ ∈ szT₁ L T :=
          (mem_normalizer_iff.mp (hTN₁ hyT) _).mp (inv_mem haT₁)
        rw [show a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) by group]
        exact mul_mem haT₁ h1
      refine hinvT _ hT ?_
      have h1 := hcommA _ (hDmem a haD).1 _ (hDmem y hyD).1
      have h2 := hA₁2 _ h1
      rw [show c * a * c⁻¹ * (c * y * c⁻¹) * (c * a * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ =
        c * (a * y * a⁻¹ * y⁻¹) * c⁻¹ by group, conj_pow] at h2
      calc (a * y * a⁻¹ * y⁻¹) ^ 2 = c⁻¹ * (c * (a * y * a⁻¹ * y⁻¹) ^ 2 * c⁻¹) * c := by group
        _ = 1 := by rw [h2]; group
    have hTD := Subgroup.card_le_of_le hT₁D
    rw [hWcard] at hTD
    have e1 := relIndex_mul_card (H := szT₁ L T) (K := D)
    have e2 := relIndex_mul_card (H := szT₁ L T) (K := T)
    rw [inf_of_le_left (szT₁_le_left L T), hT₁card] at e2
    have hne : (szT₁ L T).relIndex T ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e2
      exact (Nat.card_pos (α := T)).ne' e2.symm
    have r := Subgroup.relIndex_le_of_le_right hDT hne
    have hr4 : (szT₁ L T).relIndex T ≤ 4 * f := by
      have h3 : (szT₁ L T).relIndex T * (2 ^ f) ^ 3 ≤ 4 * f * (2 ^ f) ^ 3 := by
        rw [e2]; exact hW.card_T_le
      exact Nat.le_of_mul_le_mul_right h3 (pow_pos hq0 3)
    have h4f : 4 * f * (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := by
      have hfq : f < 2 ^ f := Nat.lt_two_pow_self
      have h1 : 4 * f < 2 ^ f * 2 ^ f :=
        calc 4 * f < 4 * 2 ^ f := by omega
          _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq4
      calc 4 * f * (2 ^ f) ^ 2 < 2 ^ f * 2 ^ f * (2 ^ f) ^ 2 :=
            Nat.mul_lt_mul_of_pos_right h1 (pow_pos hq0 2)
        _ = (2 ^ f) ^ 4 := by ring
    have hDle : Nat.card D ≤ 4 * f * (2 ^ f) ^ 2 := by
      rw [← e1]
      exact Nat.mul_le_mul (r.trans hr4) hTD
    omega

theorem gmc_conj_not_mem_U₁ (g : G) : g * t * g⁻¹ ∉ U₁ := by
  intro hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hW.step.start
  have hU₁2 : IsPGroup 2 U₁ :=
    hW.isPGroup.to_le ((hW.level.U₁_le.trans le_sup_left).trans hW.le)
  set B : Subgroup G := (U₁ ⊓ centralizer ({g * t * g⁻¹} : Set G)).map
    (MulAut.conj g⁻¹).toMonoidHom with hBdef
  have hBt : B ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hux := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * u * g * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [hux]
      _ = t * (g⁻¹ * u * g) := by group
  have hBp : IsPGroup 2 B := (hU₁2.to_le inf_le_left).map _
  obtain ⟨a, haC, ha⟩ := exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer hBt hBp
  have hat : a * t = t * a := mem_centralizer_singleton_iff.mp haC
  have hca : g * a * t * (g * a)⁻¹ = g * t * g⁻¹ := by
    rw [show g * a * t * (g * a)⁻¹ = g * (a * t) * a⁻¹ * g⁻¹ by group, hat]
    group
  refine hW.gmc_false_of_conj_mem_U₁ (c := g * a) (by rw [hca]; exact hx) fun u hu hux => ?_
  rw [hca] at hux
  have hb : g⁻¹ * u * g ∈ B :=
    ⟨u, mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr hux⟩, by simp⟩
  have h1 := ha _ hb
  rwa [show a⁻¹ * (g⁻¹ * u * g) * a = (g * a)⁻¹ * u * (g * a) by group] at h1

theorem gmc_exists_sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T := by
  by_contra hns
  obtain ⟨z, hzN, hzS, P', hP'2, hSP', hzP'⟩ :=
    exists_normalizer_not_mem_of_not_isSylow hW.isPGroup_S₂ hns
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have hcT : ∀ τ ∈ T, z * τ * z⁻¹ ∈ swapS₂ P U T := fun τ hτ =>
    (mem_normalizer_iff.mp hzN τ).mp (hW.le_S₂ (mem_sup_right hτ))
  have hSUP' : U ⊔ T ≤ P' := hW.le_S₂.trans hSP'
  have hmapT : ∀ τ ∈ T, z * τ * z⁻¹ ∈ T.map (MulAut.conj z).toMonoidHom := fun τ hτ =>
    ⟨τ, hτ, by simp⟩
  by_cases hxS : z * t * z⁻¹ ∈ U ⊔ T
  swap
  · exact hW.false_of_conj_not_mem hcT hxS
  have hx2 : (z * t * z⁻¹) ^ 2 = 1 := by
    rw [show (z * t * z⁻¹) ^ 2 = z * t ^ 2 * z⁻¹ by rw [sq, sq]; group, h.sq_eq_one]; group
  rcases hW.mem_cases hxS with h1 | h1 | h1 | ⟨n, h1⟩
  ·
    exact hW.gmc_conj_not_mem_U₁ z h1
  ·
    exact hzS (hW.le_S₂ (hL.muOne_mem_sup_of_conj hS hc hW.mu hK hμ hP'2 hSUP' hzP' h1))
  ·
    have hzTS : ∀ τ ∈ T, z * τ * z⁻¹ ∈ U ⊔ T := by
      intro τ hτ
      by_contra hh
      have hhS₂ := hcT τ hτ
      obtain ⟨-, hhw⟩ := hW.conj_of_not_mem hhS₂ hh
      have hhx : (z * τ * z⁻¹) * (z * t * z⁻¹) = (z * t * z⁻¹) * (z * τ * z⁻¹) :=
        hW.commute_of_mem_map (hmapT τ hτ)
      have h2 : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ ∈ U₁ := by
        rw [show (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ =
          ((z * τ * z⁻¹) * (z * t * z⁻¹ * w⁻¹) * (z * τ * z⁻¹)⁻¹) *
            ((z * τ * z⁻¹) * w * (z * τ * z⁻¹)⁻¹ * t⁻¹) by group]
        exact mul_mem (hW.conj_U₁ hhS₂ h1) hhw
      have hconj : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ = z * t * z⁻¹ := by
        rw [hhx]; group
      rw [hconj] at h2
      have htw : t * w⁻¹ ∉ U₁ := fun h' => hW.w_not_mem (by
        have h3 := hL.muOne_mem_T₁_of_mem_T hS h' (mul_mem hW.t_mem (inv_mem hW.w_mem))
        rw [show w = (t * w⁻¹)⁻¹ * t by group]
        exact mul_mem (inv_mem (mem_sup_left h3)) (mem_sup_right (mem_zpowers t)))
      apply htw
      rw [show t * w⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ * (z * t * z⁻¹ * w⁻¹) by group]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨c₁, hc₁T, hc₁⟩ := hL.muOneCent_exists_conj_eq hS hc hW.mu hK hμ hW.w_mem hW.w_sq
      hW.w_not_mem hW.w_cent hzTS h1
    have hc₁S : c₁ ∈ swapS₂ P U T := hW.le_S₂ (mem_sup_left (hL.U₁_le (hW.T₁_le_U₁ hc₁T)))
    have hy : s⁻¹ * c₁ * z ∈ T := by
      refine U3C1OuterLevelData.norm_mem_T_of_commute hS hP'2
        ((le_sup_right : T ≤ U ⊔ T).trans hSUP')
        (mul_mem (mul_mem (inv_mem (hSP' hW.s_mem_S₂)) (hSP' hc₁S)) hzP') ?_
      have e : (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ = t := by
        rw [show (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ =
          s⁻¹ * (c₁ * (z * t * z⁻¹) * c₁⁻¹) * s by group, hc₁, ← hW.conj_t]
        group
      calc (s⁻¹ * c₁ * z) * t =
            (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ * (s⁻¹ * c₁ * z) := by group
        _ = t * (s⁻¹ * c₁ * z) := by rw [e]
    apply hzS
    rw [show z = c₁⁻¹ * s * (s⁻¹ * c₁ * z) by group]
    exact mul_mem (mul_mem (inv_mem hc₁S) hW.s_mem_S₂) (hW.le_S₂ (mem_sup_right hy))
  ·
    have hxv : z * t * z⁻¹ * (t * w)⁻¹ ∈ U₁ := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exfalso
        rw [← two_mul, pow_mul, hx2, one_pow, one_mul] at h1
        have h1' : t * w ∈ U₁ := by simpa using inv_mem h1
        exact hW.tw_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS h1' hW.tw_mem))
      · rwa [pow_succ, pow_mul, hx2, one_pow, one_mul] at h1
    exact hW.gmc_conj_mul_tw_not_mem z hxv

theorem gmc_mem_normalizer_U₁ {z : G} {P' : Subgroup G} (hP'2 : IsPGroup 2 P')
    (hSP' : swapS₂ P U T ≤ P') (hzP' : z ∈ P') :
    z ∈ normalizer (U₁ : Set G) := by
  obtain ⟨S, hS⟩ := hW.gmc_exists_sylow
  have hle : P' = swapS₂ P U T := by
    have := S.is_maximal' hP'2 (by rw [hS]; exact hSP')
    rwa [hS] at this
  rw [hle] at hzP'
  refine mem_normalizer_iff.mpr fun u => ⟨fun hu => hW.conj_U₁ hzP' hu, fun hu => ?_⟩
  have := hW.conj_U₁ (inv_mem hzP') hu
  rwa [show z⁻¹ * (z * u * z⁻¹) * z⁻¹⁻¹ = u by group] at this

end U3C1OuterSwapHigh

theorem u3C1GmsCharInput_holds : U3C1GmsCharInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW _ _ ⟨_, hP'2, hSP', hzP'⟩ =>
    hW.gmc_mem_normalizer_U₁ hP'2 hSP' hzP'

end CFSG.SeitzReduction.RankOne
