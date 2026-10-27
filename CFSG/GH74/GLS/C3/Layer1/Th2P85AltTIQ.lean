module

public import CFSG.GH74.GLS.C3.Layer1.BkL114TI

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2

section TIMQ

variable {M : Type} [Group M] [Finite M]

theorem ti_data_MQ {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) (hAM : AModel (n + 4))
    (H : Subgroup (M ⧸ pPrimeCore 2 M)) (e : ↥H ≃* alternatingGroup (Fin (n + 4)))
    (hH : H.IsSubnormal) {S Q Kb : Subgroup M} (hS : IsSylowOf 2 S ⊤)
    (hScard : Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2)
    (hKe : ((Kb.map (piO M)).subgroupOf H).map e.toMonoidHom = stdAlt n)
    (hQS : Q ≤ S)
    (hQK : ∀ q ∈ Q, ∀ k ∈ Kb, piO M q * piO M k = piO M k * piO M q)
    {x v : M} (hxQ : x ∈ Q) (hx : orderOf x = 2) (hv : orderOf v = 2) (hvS : v ∈ S)
    (hvc : ∀ s ∈ S, s * v = v * s) (hxv : ¬ IsConj x v) (hxz : IsConj x (x * v)) :
    ∃ E : Subgroup M, E ≤ S ∧ x ∈ E ∧ v ∈ E ∧ Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a * a = 1) ∧ (∀ s ∈ S, ∀ y ∈ E, s * y * s⁻¹ ∈ E) ∧
      (∀ y ∈ S, (y * y = 1 ∧ y ≠ 1 ∧ y * v = v * y ∧ IsConj x y ∧ IsConj x (y * v)) ↔
        (y ∈ E ∧ y ≠ 1 ∧ y ≠ v)) ∧
      (∀ y ∈ E, y ≠ 1 → y ≠ v → ∃ c : M, c * v = v * c ∧ c * x * c⁻¹ = y) ∧
      (∃ s ∈ S, s * s = 1 ∧ s ∉ E) ∧
      (∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : 4 ≤ n := by omega
  have hn11 : n + 4 ≤ 11 := by omega
  have hodd : Odd (Nat.card (pPrimeCore 2 M)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hnodvd : ¬ 2 ∣ Nat.card (pPrimeCore 2 M) := fun hd =>
    absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hd) (by norm_num)
  obtain ⟨hSH, hSπcard⟩ := map_le_of_sylow H e hH hS hScard
  let toH : ↥S →* ↥H :=
    ((piO M).comp S.subtype).codRestrict H (fun s => hSH ⟨s.1, s.2, rfl⟩)
  let Ψ : ↥S →* alternatingGroup (Fin (n + 4)) := e.toMonoidHom.comp toH
  have htoH : ∀ s : S, ((toH s : ↥H) : M ⧸ pPrimeCore 2 M) = piO M s.1 := fun s => rfl
  have hΨs : ∀ s : S, e.symm (Ψ s) = toH s := fun s => e.symm_apply_apply (toH s)
  have hinj0 := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 2)
    (N := pPrimeCore 2 M) hnodvd hS.isPGroup
  have hΨinj : Function.Injective Ψ := by
    intro s₁ s₂ h12
    have h1 : toH s₁ = toH s₂ := e.injective h12
    have h2 : piO M s₁.1 = piO M s₂.1 := congrArg Subtype.val h1
    exact hinj0 h2
  have hord : ∀ s : S, orderOf s.1 = 2 → orderOf (Ψ s) = 2 := by
    intro s hs
    have h1 : orderOf (toH s) = 2 := by
      rw [← Subgroup.orderOf_coe, htoH]
      exact orderOf_piO_of_orderOf_two hs
    show orderOf (e (toH s)) = 2
    rw [MulEquiv.orderOf_eq]
    exact h1
  have hnm : ∀ s : S, orderOf s.1 = 2 →
      numMoved (Ψ s : Equiv.Perm (Fin (n + 4))) = 4 ∨ numMoved (Ψ s : Equiv.Perm (Fin (n + 4))) = 8 :=
    fun s hs => numMoved_eq_of_involution_alternating (n + 4) hn11 (Ψ s) (hord s hs)
  have hconj : ∀ s t : S, orderOf s.1 = 2 → orderOf t.1 = 2 →
      numMoved (Ψ s : Equiv.Perm (Fin (n + 4))) = numMoved (Ψ t : Equiv.Perm (Fin (n + 4))) →
        IsConj s.1 t.1 := by
    intro s t hs ht hst
    have h1 : IsConj (Ψ s) (Ψ t) :=
      isConj_alternating_of_numMoved_eq (n + 4) _ _ (hord s hs) (hord t ht) hst
    have h2 : IsConj (toH s) (toH t) := by
      have h2' : IsConj (e.symm (Ψ s)) (e.symm (Ψ t)) := e.symm.toMonoidHom.map_isConj h1
      rwa [hΨs, hΨs] at h2'
    have h3 : IsConj (piO M s.1) (piO M t.1) := H.subtype.map_isConj h2
    exact isConj_of_isConj_mk (pPrimeCore 2 M) hodd hs ht h3
  let x₀ : ↥S := ⟨x, hQS hxQ⟩
  let v₀ : ↥S := ⟨v, hvS⟩
  have hx4 : numMoved (Ψ x₀ : Equiv.Perm (Fin (n + 4))) = 4 := by
    have hle : numMoved (Ψ x₀ : Equiv.Perm (Fin (n + 4))) ≤ 4 := by
      apply numMoved_le_four_of_commute hn4
      intro τ hτ
      rw [← hKe] at hτ
      obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hτ
      obtain ⟨k, hk, hkκ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hκ)
      have hc : toH x₀ * κ = κ * toH x₀ := by
        apply Subtype.ext
        show piO M x * (κ : M ⧸ pPrimeCore 2 M) = (κ : M ⧸ pPrimeCore 2 M) * piO M x
        rw [← hkκ]
        exact hQK x hxQ k hk
      have h2 : e (toH x₀) * e κ = e κ * e (toH x₀) := by
        rw [← map_mul, ← map_mul, hc]
      exact congrArg Subtype.val h2
    rcases hnm x₀ hx with h | h
    · exact h
    · omega
  have hv8 : numMoved (Ψ v₀ : Equiv.Perm (Fin (n + 4))) = 8 := by
    rcases hnm v₀ hv with h | h
    · exfalso
      exact hxv (hconj x₀ v₀ hx hv (hx4.trans h.symm))
    · exact h
  have hcls4 : ∀ u : S, orderOf u.1 = 2 →
      (IsConj x u.1 ↔ numMoved (Ψ u : Equiv.Perm (Fin (n + 4))) = 4) := by
    intro u hu
    constructor
    · intro hxu
      rcases hnm u hu with h | h
      · exact h
      · exfalso
        apply hxv
        have h2 : IsConj u.1 v := hconj u v₀ hu hv (h.trans hv8.symm)
        exact hxu.trans h2
    · intro h4
      exact (hconj u x₀ hu hx (h4.trans hx4.symm)).symm
  let SA : Subgroup (alternatingGroup (Fin (n + 4))) :=
    ((S.map (piO M)).subgroupOf H).map e.toMonoidHom
  have hSAcard : Nat.card SA =
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hSπcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hSAsyl : IsSylowOf 2 SA ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top]
    exact hSAcard
  have hΨSA : ∀ s : S, Ψ s ∈ SA := fun s =>
    ⟨toH s, Subgroup.mem_subgroupOf.2 ⟨s.1, s.2, rfl⟩, rfl⟩
  have hSAΨ : ∀ y ∈ SA, ∃ s : S, Ψ s = y := by
    rintro y ⟨ŝ, hŝ, rfl⟩
    obtain ⟨s0, hs0, hs0e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hŝ)
    refine ⟨⟨s0, hs0⟩, ?_⟩
    show e (toH ⟨s0, hs0⟩) = e ŝ
    congr 1
    exact Subtype.ext hs0e
  have hvcSA : ∀ y ∈ SA, y * Ψ v₀ = Ψ v₀ * y := by
    intro y hy
    obtain ⟨s, rfl⟩ := hSAΨ y hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc s.1 s.2)
  obtain ⟨E', hE'S, hvE', hE'card, hE'comm, hE'sq, hE'norm, hE'F, hE'conv, hE'trans, hE'Z, hE'ex⟩ :=
    hAM SA (Ψ v₀) hSAsyl (hΨSA v₀) hvcSA (hord v₀ hv) hv8
  let E : Subgroup M := (E'.comap Ψ).map S.subtype
  have hmemE : ∀ y : M, y ∈ E ↔ ∃ hy : y ∈ S, Ψ ⟨y, hy⟩ ∈ E' := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hy, hΨy⟩
      exact ⟨⟨y, hy⟩, hΨy, rfl⟩
  have hmemE' : ∀ s : S, s.1 ∈ E ↔ Ψ s ∈ E' := by
    intro s
    rw [hmemE]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨s.2, h⟩⟩
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hxsq : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, sq] at h
    exact h
  have hΨ1 : ∀ s : S, Ψ s = 1 ↔ s = 1 := fun s => by
    rw [← map_one Ψ]
    exact hΨinj.eq_iff
  have hxv_ord : orderOf (x * v) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hxz
    rw [← hc, orderOf_conj_eq, hx]
  have hΨxv : numMoved (Ψ (x₀ * v₀) : Equiv.Perm (Fin (n + 4))) = 4 :=
    (hcls4 (x₀ * v₀) hxv_ord).1 hxz
  have hxE : x ∈ E := by
    have h1 : Ψ x₀ ∈ E' := by
      refine hE'F (Ψ x₀) ?_ ?_ (hvcSA _ (hΨSA x₀)) hx4 ?_
      · rw [← map_mul]
        have : x₀ * x₀ = 1 := Subtype.ext hxsq
        rw [this, map_one]
      · intro h1
        have := (hΨ1 x₀).1 h1
        exact hx1 (congrArg Subtype.val this)
      · rw [← map_mul]
        exact hΨxv
    exact (hmemE' x₀).2 h1
  have hvE : v ∈ E := (hmemE' v₀).2 hvE'
  have hES : E ≤ S := fun y hy => ((hmemE y).1 hy).1
  have hEcard : Nat.card E = 8 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, ← hE'card]
    refine Nat.card_congr (Equiv.ofBijective
      (fun s : ↥(E'.comap Ψ) => (⟨Ψ s.1, s.2⟩ : ↥E')) ⟨?_, ?_⟩)
    · intro s t hst
      exact Subtype.ext (hΨinj (congrArg Subtype.val hst))
    · rintro ⟨y, hy⟩
      obtain ⟨s, hs⟩ := hSAΨ y (hE'S hy)
      exact ⟨⟨s, by simpa [hs] using hy⟩, Subtype.ext hs⟩
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haS, haE⟩ := (hmemE a).1 ha
    obtain ⟨hbS, hbE⟩ := (hmemE b).1 hb
    have h1 := hE'comm _ haE _ hbE
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hΨinj h1)
  have hEsq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    obtain ⟨haS, haE⟩ := (hmemE a).1 ha
    have h1 := hE'sq _ haE
    rw [← map_mul, ← map_one Ψ] at h1
    exact congrArg Subtype.val (hΨinj h1)
  have hESnorm : ∀ s ∈ S, ∀ y ∈ E, s * y * s⁻¹ ∈ E := by
    intro s hs y hy
    obtain ⟨hyS, hyE⟩ := (hmemE y).1 hy
    have hsyS : s * y * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hyS) (S.inv_mem hs)
    rw [hmemE]
    refine ⟨hsyS, ?_⟩
    have h1 := hE'norm (Ψ ⟨s, hs⟩) (hvcSA _ (hΨSA _)) _ hyE
    have e1 : (⟨s * y * s⁻¹, hsyS⟩ : ↥S) = ⟨s, hs⟩ * ⟨y, hyS⟩ * ⟨s, hs⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    exact h1
  have hiff : ∀ y ∈ S, (y * y = 1 ∧ y ≠ 1 ∧ y * v = v * y ∧ IsConj x y ∧ IsConj x (y * v)) ↔
      (y ∈ E ∧ y ≠ 1 ∧ y ≠ v) := by
    intro y hyS
    let y₀ : ↥S := ⟨y, hyS⟩
    constructor
    · rintro ⟨hy2, hy1, hyc, hxy, hxyv⟩
      have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
      have hyv : y ≠ v := fun h => hxv (h ▸ hxy)
      have hyvord : orderOf (y * v) = 2 := by
        obtain ⟨c, hc⟩ := isConj_iff.1 hxyv
        rw [← hc, orderOf_conj_eq, hx]
      have hy4 : numMoved (Ψ y₀ : Equiv.Perm (Fin (n + 4))) = 4 := (hcls4 y₀ hyord).1 hxy
      have hyv4 : numMoved (Ψ (y₀ * v₀) : Equiv.Perm (Fin (n + 4))) = 4 :=
        (hcls4 (y₀ * v₀) hyvord).1 hxyv
      have hΨy : Ψ y₀ ∈ E' := by
        refine hE'F (Ψ y₀) ?_ ?_ (hvcSA _ (hΨSA y₀)) hy4 ?_
        · rw [← map_mul]
          have : y₀ * y₀ = 1 := Subtype.ext hy2
          rw [this, map_one]
        · intro h1
          exact hy1 (congrArg Subtype.val ((hΨ1 y₀).1 h1))
        · rw [← map_mul]
          exact hyv4
      exact ⟨(hmemE' y₀).2 hΨy, hy1, hyv⟩
    · rintro ⟨hyE, hy1, hyv⟩
      have hΨyE : Ψ y₀ ∈ E' := (hmemE' y₀).1 hyE
      have hne1 : Ψ y₀ ≠ 1 := fun h1 => hy1 (congrArg Subtype.val ((hΨ1 y₀).1 h1))
      have hnev : Ψ y₀ ≠ Ψ v₀ := fun h1 => hyv (congrArg Subtype.val (hΨinj h1))
      obtain ⟨h4, h4v⟩ := hE'conv (Ψ y₀) hΨyE hne1 hnev
      have hy2 : y * y = 1 := hEsq y hyE
      have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
      have hyvc : y * v = v * y := hvc y hyS
      have hyvord : orderOf (y * v) = 2 := by
        have hyvE : y * v ∈ E := E.mul_mem hyE hvE
        refine orderOf_eq_prime (by rw [sq]; exact hEsq _ hyvE) ?_
        intro h1
        apply hyv
        have : y = v⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact inv_eq_of_mul_eq_one_right (hEsq v hvE)
      refine ⟨hy2, hy1, hyvc, ?_, ?_⟩
      · exact (hcls4 y₀ hyord).2 h4
      · have : numMoved (Ψ (y₀ * v₀) : Equiv.Perm (Fin (n + 4))) = 4 := by
          rw [map_mul]
          exact h4v
        exact (hcls4 (y₀ * v₀) hyvord).2 this
  have htrans : ∀ y ∈ E, y ≠ 1 → y ≠ v → ∃ c : M, c * v = v * c ∧ c * x * c⁻¹ = y := by
    intro y hyE hy1 hyv
    obtain ⟨hyS, hΨy⟩ := (hmemE y).1 hyE
    let y₀ : ↥S := ⟨y, hyS⟩
    have hΨx : Ψ x₀ ∈ E' := (hmemE' x₀).1 hxE
    have hxne1 : Ψ x₀ ≠ 1 := fun h1 => hx1 (congrArg Subtype.val ((hΨ1 x₀).1 h1))
    have hxnev : Ψ x₀ ≠ Ψ v₀ := fun h1 => by
      have hxveq : x = v := congrArg Subtype.val (hΨinj h1)
      exact hxv (isConj_iff.2 ⟨1, by rw [hxveq]; group⟩)
    have hne1 : Ψ y₀ ≠ 1 := fun h1 => hy1 (congrArg Subtype.val ((hΨ1 y₀).1 h1))
    have hnev : Ψ y₀ ≠ Ψ v₀ := fun h1 => hyv (congrArg Subtype.val (hΨinj h1))
    obtain ⟨c, hcv, hcx⟩ := hE'trans (Ψ x₀) hΨx (Ψ y₀) ((hmemE' y₀).1 hyE) hxne1 hxnev hne1 hnev
    have hcv' : ((e.symm c : ↥H) : M ⧸ pPrimeCore 2 M) * piO M v =
        piO M v * ((e.symm c : ↥H) : M ⧸ pPrimeCore 2 M) := by
      have h1 := congrArg e.symm hcv
      rw [map_mul, map_mul, hΨs] at h1
      exact congrArg Subtype.val h1
    obtain ⟨c₁, hc₁v, hc₁π⟩ := exists_lift_centralizer hv hcv'
    have hcπ : piO M (c₁ * x * c₁⁻¹) = piO M y := by
      have h1 := congrArg e.symm hcx
      rw [map_mul, map_mul, map_inv, hΨs, hΨs] at h1
      have h2 := congrArg Subtype.val h1
      rw [map_mul, map_mul, map_inv, hc₁π]
      exact h2
    have hyord : orderOf y = 2 := by
      refine orderOf_eq_prime (by rw [sq]; exact hEsq y hyE) hy1
    have hcxord : orderOf (c₁ * x * c₁⁻¹) = 2 := by rw [orderOf_conj_eq, hx]
    have hcxv : (c₁ * x * c₁⁻¹) * v = v * (c₁ * x * c₁⁻¹) := by
      have hxvc : x * v = v * x := hvc x (hQS hxQ)
      have hc₁v' : c₁⁻¹ * v = v * c₁⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul]
        calc v = (v * c₁) * c₁⁻¹ := by group
          _ = (c₁ * v) * c₁⁻¹ := by rw [hc₁v]
          _ = c₁ * (v * c₁⁻¹) := by group
      calc (c₁ * x * c₁⁻¹) * v = c₁ * x * (c₁⁻¹ * v) := by group
        _ = c₁ * x * (v * c₁⁻¹) := by rw [hc₁v']
        _ = c₁ * (x * v) * c₁⁻¹ := by group
        _ = c₁ * (v * x) * c₁⁻¹ := by rw [hxvc]
        _ = (c₁ * v) * x * c₁⁻¹ := by group
        _ = (v * c₁) * x * c₁⁻¹ := by rw [hc₁v]
        _ = v * (c₁ * x * c₁⁻¹) := by group
    obtain ⟨g, hgv, hgy⟩ := exists_centralizer_conj_of_mk_eq (v := v) (s := y) (u := c₁ * x * c₁⁻¹)
      hyord hcxord (hvc y hyS) hcxv hcπ.symm
    refine ⟨g * c₁, ?_, ?_⟩
    · calc g * c₁ * v = g * (c₁ * v) := by group
        _ = g * (v * c₁) := by rw [hc₁v]
        _ = (g * v) * c₁ := by group
        _ = (v * g) * c₁ := by rw [hgv]
        _ = v * (g * c₁) := by group
    · calc g * c₁ * x * (g * c₁)⁻¹ = g * (c₁ * x * c₁⁻¹) * g⁻¹ := by group
        _ = y := hgy
  obtain ⟨s₁, hs₁S, hs₁sq, hs₁E⟩ : ∃ s ∈ S, s * s = 1 ∧ s ∉ E := by
    obtain ⟨y, hySA, hysq, hyE⟩ := hE'ex
    obtain ⟨s, rfl⟩ := hSAΨ y hySA
    refine ⟨s.1, s.2, ?_, fun h1 => hyE ((hmemE' s).1 h1)⟩
    have : Ψ (s * s) = Ψ 1 := by rw [map_mul, hysq, map_one]
    exact congrArg Subtype.val (hΨinj this)
  refine ⟨E, hES, hxE, hvE, hEcard, hEcomm, hEsq, hESnorm, hiff, htrans,
    ⟨s₁, hs₁S, hs₁sq, hs₁E⟩, ?_⟩
  intro s hs hsc hsq hs1
  let s₀ : ↥S := ⟨s, hs⟩
  have hs0 : Ψ s₀ = Ψ v₀ := by
    refine hE'Z (Ψ s₀) (hΨSA s₀) ?_ ?_ ?_
    · intro t ht
      obtain ⟨t₀, rfl⟩ := hSAΨ t ht
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hsc t₀.1 t₀.2)
    · rw [← map_mul]
      have : s₀ * s₀ = 1 := Subtype.ext hsq
      rw [this, map_one]
    · intro h1
      exact hs1 (congrArg Subtype.val ((hΨ1 s₀).1 h1))
  exact congrArg Subtype.val (hΨinj hs0)

end TIMQ

end CFSG.GH74.GLS.C3.Layer1.Bk
