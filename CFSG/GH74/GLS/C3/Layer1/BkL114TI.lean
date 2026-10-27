module

public import CFSG.GH74.GLS.C3.Layer1.BkL114WCent
public import CFSG.GH74.GLS.C3.Layer1.BkL114Epw
public import CFSG.GH74.GLS.C3.Layer2.L4End
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2

section TIM

variable {M : Type} [Group M] [Finite M]

theorem exists_centralizer_conj_of_mk_eq {v s u : M} (hs : orderOf s = 2) (hu : orderOf u = 2)
    (hsv : s * v = v * s) (huv : u * v = v * u) (hsu : piO M s = piO M u) :
    ∃ g : M, g * v = v * g ∧ g * u * g⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Cv : Subgroup M := centralizer ({v} : Set M)
  let W : Subgroup ↥Cv := ((pPrimeCore 2 M).subgroupOf Cv)
  have hWn : ∀ c ∈ (⊤ : Subgroup ↥Cv), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c _ w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact Subgroup.Normal.conj_mem inferInstance (w : M) hw (c : M)
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card (pPrimeCore 2 M) := by
      have := Subgroup.card_dvd_of_le (show W.map Cv.subtype ≤ pPrimeCore 2 M from
        fun y ⟨w, hw, hwy⟩ => hwy ▸ (Subgroup.mem_subgroupOf.1 hw))
      rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective Cv)] at this
    exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card)
  let s' : ↥Cv := ⟨s, mem_centralizer_singleton_iff.2 hsv⟩
  let u' : ↥Cv := ⟨u, mem_centralizer_singleton_iff.2 huv⟩
  have hs' : orderOf s' = 2 := (Subgroup.orderOf_mk s _).trans hs
  have hu' : orderOf u' = 2 := (Subgroup.orderOf_mk u _).trans hu
  have hP : ∀ {y : ↥Cv}, orderOf y = 2 → IsPGroup 2 ↥(zpowers y) := by
    intro y hy
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy]
    norm_num
  have hsu' : s'⁻¹ * u' ∈ W := by
    rw [Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq).1 hsu
  obtain ⟨g, hg⟩ := exists_conj_of_coset (C := ⊤) (W := W) (B₁ := zpowers s') (B₂ := zpowers u')
    hWn hWodd (Subgroup.mem_top _) (mem_zpowers _) (hP hs') (mem_zpowers _) (hP hu') hsu'
  refine ⟨(g : M), mem_centralizer_singleton_iff.1 g.2, ?_⟩
  exact congrArg Subtype.val hg

theorem exists_lift_centralizer {v : M} (hv : orderOf v = 2) {c : M ⧸ pPrimeCore 2 M}
    (hc : c * piO M v = piO M v * c) : ∃ c₁ : M, c₁ * v = v * c₁ ∧ piO M c₁ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 M) := fun hd =>
    absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hd) (by norm_num)
  have hQ2g : IsPGroup 2 ↥(zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv]
    norm_num
  have hcen := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hodd hQ2g
  have hcomm : Commute (piO M v) c := hc.symm
  have hc' : c ∈ centralizer ((((zpowers v).map (QuotientGroup.mk' (pPrimeCore 2 M)) :
      Subgroup (M ⧸ pPrimeCore 2 M)) : Set (M ⧸ pPrimeCore 2 M))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have := (hcomm.zpow_left j).eq
    simpa [map_zpow] using this
  rw [hcen] at hc'
  obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 hc'
  refine ⟨d, ?_, hdc⟩
  have := mem_centralizer_iff.1 hd v (mem_zpowers _)
  exact this.symm

theorem ti_data_M {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) (hAM : AModel (n + 4))
    (H : Subgroup (M ⧸ pPrimeCore 2 M)) (e : ↥H ≃* alternatingGroup (Fin (n + 4)))
    (hH : H.IsSubnormal) {S Q Kb : Subgroup M} (hS : IsSylowOf 2 S ⊤)
    (hScard : Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2)
    (hKe : ((Kb.map (piO M)).subgroupOf H).map e.toMonoidHom = stdAlt n)
    (hQS : Q ≤ S)
    (hQK : ∀ q ∈ Q, ∀ k ∈ Kb, piO M q * piO M k = piO M k * piO M q)
    {x v : M} (hxQ : x ∈ Q) (hx : orderOf x = 2) (hv : orderOf v = 2) (hvS : v ∈ S)
    (hvc : ∀ s ∈ S, s * v = v * s) (hxv : ¬ IsConj x v) (hxz : IsConj x (x * v))
    (hO : ∀ o ∈ pPrimeCore 2 M, o * x = x * o → ∀ s ∈ S, o * s = s * o)
    (hnormH : ∀ g : M, g * x = x * g →
      H.map (MulAut.conj (piO M g)).toMonoidHom = H) :
    ∃ E : Subgroup M, E ≤ S ∧ x ∈ E ∧ v ∈ E ∧ Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a * a = 1) ∧ (∀ s ∈ S, ∀ y ∈ E, s * y * s⁻¹ ∈ E) ∧
      (∀ y ∈ S, (y * y = 1 ∧ y ≠ 1 ∧ y * v = v * y ∧ IsConj x y ∧ IsConj x (y * v)) ↔
        (y ∈ E ∧ y ≠ 1 ∧ y ≠ v)) ∧
      (∀ y ∈ E, y ≠ 1 → y ≠ v → ∃ c : M, c * v = v * c ∧ c * x * c⁻¹ = y) ∧
      (∀ g : M, g * x = x * g → g * v = v * g → ∀ y ∈ E, g * y * g⁻¹ ∈ E) ∧
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
  have hcent : ∀ g : M, g * x = x * g → g * v = v * g → ∀ y ∈ E, g * y * g⁻¹ ∈ E := by
    intro g hgx hgv y hyE
    by_cases hy1 : y = 1
    · subst hy1
      simp
    by_cases hyv : y = v
    · subst hyv
      have : g * y * g⁻¹ = y := by
        calc g * y * g⁻¹ = (g * y) * g⁻¹ := rfl
          _ = (y * g) * g⁻¹ := by rw [hgv]
          _ = y := by group
      rw [this]
      exact hvE
    obtain ⟨hyS, hΨy⟩ := (hmemE y).1 hyE
    let y₀ : ↥S := ⟨y, hyS⟩
    have hHn := hnormH g hgx
    let φ : ↥H ≃* ↥H :=
      ((MulAut.conj (piO M g)).subgroupMap H).trans (MulEquiv.subgroupCongr hHn)
    have hφ : ∀ h : ↥H, ((φ h : ↥H) : M ⧸ pPrimeCore 2 M) =
        piO M g * (h : M ⧸ pPrimeCore 2 M) * (piO M g)⁻¹ := fun h => rfl
    let φA : MulAut (alternatingGroup (Fin (n + 4))) := (e.symm.trans φ).trans e
    obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
      (by omega : n + 4 = 5 ∨ 7 ≤ n + 4) φA
    have hφAs : ∀ s : S, φA (Ψ s) = e (φ (toH s)) := by
      intro s
      show e (φ (e.symm (Ψ s))) = _
      rw [hΨs]
    have hφv : φ (toH v₀) = toH v₀ := by
      apply Subtype.ext
      rw [hφ]
      show piO M g * piO M v * (piO M g)⁻¹ = piO M v
      rw [← map_inv, ← map_mul, ← map_mul, hgv]
      group
    have hφAv : φA (Ψ v₀) = Ψ v₀ := by
      rw [hφAs]
      show e (φ (toH v₀)) = e (toH v₀)
      rw [hφv]
    have hy'1 : φA (Ψ y₀) ≠ 1 := by
      intro h1
      have : Ψ y₀ = 1 := by
        have := φA.injective (h1.trans (map_one φA).symm)
        exact this
      exact hy1 (congrArg Subtype.val ((hΨ1 y₀).1 this))
    have hne1 : Ψ y₀ ≠ 1 := fun h1 => hy1 (congrArg Subtype.val ((hΨ1 y₀).1 h1))
    have hnev : Ψ y₀ ≠ Ψ v₀ := fun h1 => hyv (congrArg Subtype.val (hΨinj h1))
    obtain ⟨h4, h4v⟩ := hE'conv (Ψ y₀) ((hmemE' y₀).1 hyE) hne1 hnev
    have hy'E' : φA (Ψ y₀) ∈ E' := by
      refine hE'F (φA (Ψ y₀)) ?_ hy'1 ?_ ?_ ?_
      · rw [← map_mul, hE'sq _ ((hmemE' y₀).1 hyE), map_one]
      · calc φA (Ψ y₀) * Ψ v₀ = φA (Ψ y₀) * φA (Ψ v₀) := by rw [hφAv]
          _ = φA (Ψ y₀ * Ψ v₀) := by rw [map_mul]
          _ = φA (Ψ v₀ * Ψ y₀) := by rw [hvcSA _ (hΨSA y₀)]
          _ = Ψ v₀ * φA (Ψ y₀) := by rw [map_mul, hφAv]
      · rw [hσ (Ψ y₀)]
        exact (numMoved_conj _ σ).trans h4
      · have : φA (Ψ y₀) * Ψ v₀ = φA (Ψ y₀ * Ψ v₀) := by rw [map_mul, hφAv]
        rw [this, hσ]
        exact (numMoved_conj _ σ).trans h4v
    obtain ⟨s', hs'⟩ := hSAΨ _ (hE'S hy'E')
    have hs'E : s'.1 ∈ E := (hmemE' s').2 (by rw [hs']; exact hy'E')
    have hpi : piO M s'.1 = piO M (g * y * g⁻¹) := by
      have h1 : toH s' = φ (toH y₀) := by
        rw [← hΨs s', hs']
        show e.symm (φA (Ψ y₀)) = _
        simp only [φA, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hΨs]
      have h2 := congrArg Subtype.val h1
      rw [htoH, hφ] at h2
      rw [h2, htoH, map_mul, map_mul, map_inv]
    have hoO : s'.1⁻¹ * (g * y * g⁻¹) ∈ pPrimeCore 2 M := (QuotientGroup.eq).1 hpi
    have hox : (s'.1⁻¹ * (g * y * g⁻¹)) * x = x * (s'.1⁻¹ * (g * y * g⁻¹)) := by
      have hxy : y * x = x * y := hEcomm y hyE x hxE
      have hxs : s'.1 * x = x * s'.1 := hEcomm _ hs'E x hxE
      have hgy : (g * y * g⁻¹) * x = x * (g * y * g⁻¹) := by
        have hgx' : g * x * g⁻¹ = x := by
          calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hgx]
            _ = x := by group
        calc (g * y * g⁻¹) * x = g * y * (g⁻¹ * x) := by group
          _ = g * y * (g⁻¹ * x * g * g⁻¹) := by group
          _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * (y * x) * g⁻¹ := by
            congr 3
            calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
              _ = g⁻¹ * (g * x) := by rw [hgx]
              _ = x := by group
          _ = g * (x * y) * g⁻¹ := by rw [hxy]
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          _ = x * (g * y * g⁻¹) := by rw [hgx']
      have hsx' : s'.1⁻¹ * x = x * s'.1⁻¹ := by
        calc s'.1⁻¹ * x = s'.1⁻¹ * x * (s'.1 * s'.1⁻¹) := by group
          _ = s'.1⁻¹ * (x * s'.1) * s'.1⁻¹ := by group
          _ = s'.1⁻¹ * (s'.1 * x) * s'.1⁻¹ := by rw [hxs]
          _ = x * s'.1⁻¹ := by group
      calc (s'.1⁻¹ * (g * y * g⁻¹)) * x = s'.1⁻¹ * ((g * y * g⁻¹) * x) := by group
        _ = s'.1⁻¹ * (x * (g * y * g⁻¹)) := by rw [hgy]
        _ = (s'.1⁻¹ * x) * (g * y * g⁻¹) := by group
        _ = (x * s'.1⁻¹) * (g * y * g⁻¹) := by rw [hsx']
        _ = x * (s'.1⁻¹ * (g * y * g⁻¹)) := by group
    have hos : (s'.1⁻¹ * (g * y * g⁻¹)) * s'.1 = s'.1 * (s'.1⁻¹ * (g * y * g⁻¹)) :=
      hO _ hoO hox s'.1 s'.2
    set o : M := s'.1⁻¹ * (g * y * g⁻¹) with ho
    have hgy2 : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
      have := hEsq y hyE
      calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hs'sq : s'.1 * s'.1 = 1 := hEsq _ hs'E
    have hgyo : g * y * g⁻¹ = s'.1 * o := by rw [ho]; group
    have ho2 : o * o = 1 := by
      have h1 : (s'.1 * o) * (s'.1 * o) = 1 := by rw [← hgyo]; exact hgy2
      have hoc : o * s'.1 = s'.1 * o := hos
      calc o * o = (s'.1 * s'.1) * (o * o) := by rw [hs'sq, one_mul]
        _ = s'.1 * (s'.1 * o) * o := by group
        _ = s'.1 * (o * s'.1) * o := by rw [← hoc]
        _ = (s'.1 * o) * (s'.1 * o) := by group
        _ = 1 := h1
    have ho1 : o = 1 := by
      have hdvd2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ho2)
      have hdvd : orderOf o ∣ Nat.card (pPrimeCore 2 M) := by
        have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 M) hoO
        exact this
      have hg1 : orderOf o ∣ Nat.gcd 2 (Nat.card (pPrimeCore 2 M)) := Nat.dvd_gcd hdvd2 hdvd
      rw [pPrimeCore_coprime_card] at hg1
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg1)
    rw [hgyo, ho1, mul_one]
    exact hs'E
  obtain ⟨s₁, hs₁S, hs₁sq, hs₁E⟩ : ∃ s ∈ S, s * s = 1 ∧ s ∉ E := by
    obtain ⟨y, hySA, hysq, hyE⟩ := hE'ex
    obtain ⟨s, rfl⟩ := hSAΨ y hySA
    refine ⟨s.1, s.2, ?_, fun h1 => hyE ((hmemE' s).1 h1)⟩
    have : Ψ (s * s) = Ψ 1 := by rw [map_mul, hysq, map_one]
    exact congrArg Subtype.val (hΨinj this)
  refine ⟨E, hES, hxE, hvE, hEcard, hEcomm, hEsq, hESnorm, hiff, htrans, hcent,
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

end TIM

section GLevel4

theorem stdAlt_ne_bot {n : ℕ} (hn : 4 ≤ n) : stdAlt n ≠ ⊥ := by
  intro hbot
  let i : Fin (n + 4) := ⟨0, by omega⟩
  let p : Fin (n + 4) := ⟨1, by omega⟩
  let q : Fin (n + 4) := ⟨2, by omega⟩
  have hip : i ≠ p := by simp [i, p]
  have hiq : i ≠ q := by simp [i, q]
  have hpq : p ≠ q := by simp [p, q]
  have hmem := threeCycle_mem_stdAlt i p q (by simp [i]; omega) (by simp [p]; omega)
    (by simp [q]; omega) hip hiq hpq
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun a : alternatingGroup (Fin (n + 4)) => (a : Equiv.Perm (Fin (n + 4))) i) hmem
  simp only [Subgroup.coe_one, Equiv.Perm.coe_one, id_eq] at h1
  have h2 : (Equiv.swap i p * Equiv.swap i q) i = q := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hiq.symm hpq.symm]
  rw [h2] at h1
  exact hiq h1.symm

theorem normalizes_H {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n = 5 ∨ n = 7) {x : G}
    {K : Subgroup G} {H : Subgroup (NWbar x)} {e : ↥H ≃* alternatingGroup (Fin (n + 4))}
    (hHsub : H.IsSubnormal) (hKH : toNWbar x K ≤ H)
    (hKe : ((toNWbar x K).subgroupOf H).map e.toMonoidHom = stdAlt n) (g : NWbar x)
    (hg : (toNWbar x K).map (MulAut.conj g).toMonoidHom ≤ toNWbar x K) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have h5 : 5 ≤ Nat.card (Fin (n + 4)) := by simp; omega
  have : IsSimpleGroup (alternatingGroup (Fin (n + 4))) := alternatingGroup.isSimpleGroup h5
  have : IsSimpleGroup ↥H := e.isSimpleGroup
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := fun y =>
    ⟨g⁻¹ * y * g, by simp [MulAut.conj_apply]; group⟩
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hH'sub : (H.map (MulAut.conj g).toMonoidHom).IsSubnormal :=
    Subgroup.IsSubnormal.map hsurj hHsub
  have hKeq : (toNWbar x K).map (MulAut.conj g).toMonoidHom = toNWbar x K :=
    Subgroup.eq_of_le_of_card_ge hg (by rw [Subgroup.card_map_of_injective hinj])
  have hKH' : toNWbar x K ≤ H.map (MulAut.conj g).toMonoidHom := by
    rw [← hKeq]
    exact Subgroup.map_mono hKH
  have hsub := hH'sub.subgroupOf (K := H)
  have hK1 : (toNWbar x K).subgroupOf H ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at hKe
    exact stdAlt_ne_bot (by omega) hKe.symm
  have hle : (toNWbar x K).subgroupOf H ≤ (H.map (MulAut.conj g).toMonoidHom).subgroupOf H :=
    fun k hk => Subgroup.mem_subgroupOf.2 (hKH' (Subgroup.mem_subgroupOf.1 hk))
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsub with hbot | htop
  · exact absurd (le_bot_iff.1 (hbot ▸ hle)) hK1
  · have hHH' : H ≤ H.map (MulAut.conj g).toMonoidHom := fun h hh => by
      have : (⟨h, hh⟩ : ↥H) ∈ (H.map (MulAut.conj g).toMonoidHom).subgroupOf H := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    exact (Subgroup.eq_of_le_of_card_ge hHH'
      (by rw [Subgroup.card_map_of_injective hinj])).symm

theorem O_cent_mem_W {G : Type} [Group G] [Finite G] (x : G) (o : ↥(NW x))
    (ho : o ∈ pPrimeCore 2 ↥(NW x)) (hox : (o : G) * x = x * (o : G)) :
    (o : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : centralizer ({x} : Set G) ≤ NW x := centralizer_le_NW x
  let D : Subgroup ↥(centralizer ({x} : Set G)) :=
    (pPrimeCore 2 ↥(NW x)).comap (Subgroup.inclusion hCN)
  have hDn : D.Normal := Subgroup.Normal.comap inferInstance _
  have hDcop : Nat.Coprime 2 (Nat.card D) := by
    have hinj : Function.Injective (Subgroup.inclusion hCN) := Subgroup.inclusion_injective hCN
    have h1 : D.map (Subgroup.inclusion hCN) ≤ pPrimeCore 2 ↥(NW x) := Subgroup.map_comap_le _ _
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective hinj] at h2
    exact Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
  have hle := le_pPrimeCore_of_normal_coprime hDn hDcop
  have hoC : (o : G) ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hox
  have hoD : (⟨o, hoC⟩ : ↥(centralizer ({x} : Set G))) ∈ D := ho
  exact ⟨⟨o, hoC⟩, hle hoD, rfl⟩

end GLevel4

section TIG

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem centralizer_v_le_NW (hZD : CFSG.GH74.Uniqueness.S_ZD)
    (hn : n = 5 ∨ n = 7) (hAM : AModel (n + 4)) (h : IsAConfigW n x K T Q S a)
    (hS : S = T ⊔ zpowers a) (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x)
    {H : Subgroup (NWbar x)} {e : ↥H ≃* alternatingGroup (Fin (n + 4))} (hHsub : H.IsSubnormal)
    (hKH : toNWbar x K ≤ H) (hKe : ((toNWbar x K).subgroupOf H).map e.toMonoidHom = stdAlt n) :
    centralizer ({x * (a * x * a⁻¹)} : Set G) ≤ NW x ∧
      ∀ t ∈ NW x, orderOf t = 2 → (∃ c ∈ NW x, c * x * c⁻¹ = t) ∨
        (∃ c ∈ NW x, c * (x * (a * x * a⁻¹)) * c⁻¹ = t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvdef⟩ : ∃ v : G, v = x * (a * x * a⁻¹) := ⟨_, rfl⟩
  rw [← hvdef]
  have hvord : orderOf v = 2 := hvdef ▸ v_orderOf h hS hz
  have hvT : v ∈ T := hvdef ▸ v_mem_T h hz
  have hvc : ∀ s ∈ S, s * v = v * s := hvdef ▸ v_central_S h hS hz
  have hnc : ¬ IsConj x v := hvdef ▸ not_isConj_x_v h hS hz
  have hxord : orderOf x = 2 := h.x_order
  have hCN : centralizer ({x} : Set G) ≤ NW x := centralizer_le_NW x
  have hxN : x ∈ NW x := hCN (mem_centralizer_singleton_iff.2 rfl)
  have hSN : S ≤ NW x := by
    rw [hS]
    exact sup_le (h.T_le_C.trans hCN) (zpowers_le.2 haN)
  have hTS : T ≤ S := h.T_lt_S.le
  have hvS : v ∈ S := hTS hvT
  have hvN : v ∈ NW x := hSN hvS
  have hSyl : IsSylowOf 2 (S.subgroupOf (NW x)) ⊤ := by
    have h1 : IsSylowOf 2 S (NW x) := h.sylowS.of_le hSN le_top
    have h2 : IsSylowOf 2 ((S.subgroupOf (NW x)).map (NW x).subtype)
        ((⊤ : Subgroup ↥(NW x)).map (NW x).subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hSN, Subgroup.map_top, Subgroup.range_subtype]
      exact h1
    exact (isSylowOf_map_subtype_iff (NW x)).1 h2
  have hScard : Nat.card ↥(S.subgroupOf (NW x)) ≤
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact card_S_le hn h hS
  have hQS : Q.subgroupOf (NW x) ≤ S.subgroupOf (NW x) := fun q hq =>
    Subgroup.mem_subgroupOf.2 (hTS (h.Q_le_T (Subgroup.mem_subgroupOf.1 hq)))
  have hQK : ∀ q ∈ Q.subgroupOf (NW x), ∀ k ∈ K.subgroupOf (NW x),
      piO ↥(NW x) q * piO ↥(NW x) k = piO ↥(NW x) k * piO ↥(NW x) q := by
    intro q hq k hk
    have hc := commutator_mem_W h (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hq)
    have hmem := mem_pPrimeCore_of_mem_W hc
    have hcomm : (⟨⁅(k : G), (q : G)⁆, W_le_NW x hc⟩ : ↥(NW x)) = ⁅k, q⁆ := rfl
    rw [hcomm] at hmem
    exact (piO_comm_of_commutator_mem hmem).symm
  have hxQ : (⟨x, hxN⟩ : ↥(NW x)) ∈ Q.subgroupOf (NW x) := h.x_mem_Q
  have hx' : orderOf (⟨x, hxN⟩ : ↥(NW x)) = 2 := (Subgroup.orderOf_mk x hxN).trans hxord
  have hv' : orderOf (⟨v, hvN⟩ : ↥(NW x)) = 2 := (Subgroup.orderOf_mk v hvN).trans hvord
  have hvS' : (⟨v, hvN⟩ : ↥(NW x)) ∈ S.subgroupOf (NW x) := hvS
  have hvc' : ∀ s ∈ S.subgroupOf (NW x), s * (⟨v, hvN⟩ : ↥(NW x)) = ⟨v, hvN⟩ * s := fun s hs =>
    Subtype.ext (hvc (s : G) (Subgroup.mem_subgroupOf.1 hs))
  have hnc' : ¬ IsConj (⟨x, hxN⟩ : ↥(NW x)) ⟨v, hvN⟩ := fun hc =>
    hnc ((NW x).subtype.map_isConj hc)
  have hxxv : x * v = a * x * a⁻¹ := by
    have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
    rw [hvdef]
    calc x * (x * (a * x * a⁻¹)) = (x * x) * (a * x * a⁻¹) := by group
      _ = a * x * a⁻¹ := by rw [hxx, one_mul]
  have hxz' : IsConj (⟨x, hxN⟩ : ↥(NW x)) (⟨x, hxN⟩ * ⟨v, hvN⟩) :=
    isConj_iff.2 ⟨⟨a, haN⟩, Subtype.ext hxxv.symm⟩
  have hO : ∀ o ∈ pPrimeCore 2 ↥(NW x), o * (⟨x, hxN⟩ : ↥(NW x)) = ⟨x, hxN⟩ * o →
      ∀ s ∈ S.subgroupOf (NW x), o * s = s * o := by
    intro o ho hox s hs
    have hox' : (o : G) * x = x * (o : G) := congrArg Subtype.val hox
    have hoW := O_cent_mem_W x o ho hox'
    have := W_centralizes_S (e := e) hn h hS haN hHsub (s : G) (Subgroup.mem_subgroupOf.1 hs) (o : G) hoW
    exact Subtype.ext this.symm
  have hnormH : ∀ g : ↥(NW x), g * (⟨x, hxN⟩ : ↥(NW x)) = ⟨x, hxN⟩ * g →
      H.map (MulAut.conj (piO ↥(NW x) g)).toMonoidHom = H := by
    intro g hgx
    have hgx' : (g : G) * x = x * (g : G) := congrArg Subtype.val hgx
    have hgC : (g : G) ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hgx'
    refine normalizes_H hn hHsub hKH hKe _ ?_
    rintro _ ⟨kb, hkb, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hkb
    refine Subgroup.mem_map.2 ⟨g * k * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact h.normalInC (g : G) hgC (k : G) (Subgroup.mem_subgroupOf.1 hk)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
  have hfus := (n_level hn H e hHsub hSyl hScard hKe hQS (fun q hq => by
      have hqe := ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 Q).1 h.elemQ).2
        (q : G) (Subgroup.mem_subgroupOf.1 hq)
      exact Subtype.ext (by simpa [sq] using hqe)) hQK hxQ hx' hv' hvS' hvc' hnc').1
  have hfusN : ∀ t ∈ NW x, orderOf t = 2 →
      (∃ c ∈ NW x, c * x * c⁻¹ = t) ∨ (∃ c ∈ NW x, c * v * c⁻¹ = t) := by
    intro t htN ht2
    have ht2' : orderOf (⟨t, htN⟩ : ↥(NW x)) = 2 := (Subgroup.orderOf_mk t htN).trans ht2
    have hsq : (⟨t, htN⟩ : ↥(NW x)) * ⟨t, htN⟩ = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one t
      rw [ht2, sq] at this
      exact this
    obtain ⟨c, hc⟩ := exists_conj_mem_of_isSylowOf hSyl hsq
    have hu2 : orderOf (c * (⟨t, htN⟩ : ↥(NW x)) * c⁻¹) = 2 := by
      rw [orderOf_conj_eq, ht2']
    have key : ∀ y : G, ∀ hyN : y ∈ NW x,
        IsConj (c * (⟨t, htN⟩ : ↥(NW x)) * c⁻¹) (⟨y, hyN⟩ : ↥(NW x)) →
          ∃ c' ∈ NW x, c' * y * c'⁻¹ = t := by
      intro y hyN hcj
      obtain ⟨d, hd⟩ := isConj_iff.1 hcj
      refine ⟨(((d * c)⁻¹ : ↥(NW x)) : G), ((d * c)⁻¹ : ↥(NW x)).2, ?_⟩
      have h1 := congrArg Subtype.val hd
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
      rw [← h1]
      group
    rcases hfus _ hc hu2 with hcx | hcv
    · exact Or.inl (key x hxN hcx)
    · exact Or.inr (key v hvN hcv)
  have hF1 : ∀ t ∈ NW x, orderOf t = 2 → IsConj x t → ∃ c ∈ NW x, c * x * c⁻¹ = t := by
    intro t htN ht2 hxt
    rcases hfusN t htN ht2 with h1 | ⟨c, hcN, hc⟩
    · exact h1
    · exfalso
      apply hnc
      obtain ⟨d, hd⟩ := isConj_iff.1 hxt
      refine isConj_iff.2 ⟨c⁻¹ * d, ?_⟩
      calc c⁻¹ * d * x * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * x * d⁻¹) * c := by group
        _ = c⁻¹ * t * c := by rw [hd]
        _ = v := by rw [← hc]; group
  have hF2 : ∀ g : G, g * x * g⁻¹ ∈ NW x → g ∈ NW x := by
    intro g hg
    have hord : orderOf (g * x * g⁻¹) = 2 := by rw [orderOf_conj_eq, hxord]
    obtain ⟨m, hmN, hm⟩ := hF1 _ hg hord (isConj_iff.2 ⟨g, rfl⟩)
    have hmg : m⁻¹ * g ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : g * x * g⁻¹ = m * x * m⁻¹ := hm.symm
      calc m⁻¹ * g * x = m⁻¹ * (g * x * g⁻¹) * g := by group
        _ = m⁻¹ * (m * x * m⁻¹) * g := by rw [h1]
        _ = x * (m⁻¹ * g) := by group
    have h2 := hCN hmg
    have h3 : g = m * (m⁻¹ * g) := by group
    rw [h3]
    exact (NW x).mul_mem hmN h2
  obtain ⟨EM, hEMS, hxEM, hvEM, hEMcard, hEMcomm, hEMsq, hEMnorm, hEMiff, hEMtrans, hEMcent,
      ⟨s₁, hs₁S, hs₁sq, hs₁E⟩, hEMZ⟩ :=
    ti_data_M (by omega) hAM H e hHsub hSyl hScard hKe hQS hQK hxQ hx' hv' hvS' hvc' hnc' hxz' hO hnormH
  set Cv : Subgroup G := centralizer ({v} : Set G) with hCv
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * v = v * g := fun g => mem_centralizer_singleton_iff
  have hSCv : S ≤ Cv := fun s hs => (hmemCv s).2 (hvc s hs)
  have hxS : x ∈ S := hTS h.x_mem_T
  have haS : a ∈ S := by
    rw [hS]
    exact Subgroup.mem_sup_right (mem_zpowers a)
  have hxCv : x ∈ Cv := hSCv hxS
  have haCv : a ∈ Cv := hSCv haS
  let EG : Subgroup G := EM.map (NW x).subtype
  have hmemEG : ∀ y : G, y ∈ EG ↔ ∃ hyN : y ∈ NW x, (⟨y, hyN⟩ : ↥(NW x)) ∈ EM := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨hyN, hm⟩
      exact ⟨⟨y, hyN⟩, hm, rfl⟩
  have hEGS : EG ≤ S := by
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hEMS hm)
  have hEGCv : EG ≤ Cv := hEGS.trans hSCv
  have hEGcard : Nat.card EG = 8 := by
    rw [Subgroup.card_map_of_injective (NW x).subtype_injective]
    exact hEMcard
  let v' : ↥Cv := ⟨v, (hmemCv v).2 rfl⟩
  let x' : ↥Cv := ⟨x, hxCv⟩
  let a' : ↥Cv := ⟨a, haCv⟩
  let Zs : Set ↥Cv := {z | ∃ g : ↥Cv, g * x' * g⁻¹ = z}
  let S' : Subgroup ↥Cv := S.subgroupOf Cv
  let E' : Subgroup ↥Cv := EG.subgroupOf Cv
  have hxsq : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hvsq : v * v = 1 := by
    have h1 := pow_orderOf_eq_one v
    rw [hvord, sq] at h1
    exact h1
  have hx1 : x ≠ 1 := h.x_ne_one
  have hv1 : v ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hvord
    omega
  have hx'sq : x' * x' = 1 := Subtype.ext hxsq
  have hx'v : x' * v' = a' * x' * a'⁻¹ := Subtype.ext hxxv
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hZmv : ∀ z ∈ Zs, z * v' ∈ Zs := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * a', ?_⟩
    calc g * a' * x' * (g * a')⁻¹ = g * (a' * x' * a'⁻¹) * g⁻¹ := by group
      _ = g * (x' * v') * g⁻¹ := by rw [hx'v]
      _ = g * x' * (v' * g⁻¹) := by group
      _ = g * x' * (g⁻¹ * v') := by rw [← hv'c g⁻¹]
      _ = g * x' * g⁻¹ * v' := by group
  have hTI : L4.TIData v' Zs S' E' x' := by
    refine ⟨?_, ?_, hv'c, ?_, ?_, ?_, ?_, hZmv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.ext hvsq
    · exact fun h1 => hv1 (congrArg Subtype.val h1)
    · rintro _ ⟨g, rfl⟩
      calc g * x' * g⁻¹ * (g * x' * g⁻¹) = g * (x' * x') * g⁻¹ := by group
        _ = 1 := by rw [hx'sq]; group
    · rintro _ ⟨g, rfl⟩ h1
      have h2 : x' = 1 := by
        calc x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      exact hx1 (congrArg Subtype.val h2)
    · rintro ⟨g, hg⟩
      exact hnc (isConj_iff.2 ⟨g, congrArg Subtype.val hg⟩)
    · rintro _ ⟨g', rfl⟩ g
      exact ⟨g * g', by group⟩
    · show IsSylowOf 2 (S.subgroupOf Cv) ⊤
      rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
        Subgroup.range_subtype, inf_eq_left.2 hSCv]
      exact h.sylowS.of_le hSCv le_top
    · exact fun y hy => Subgroup.mem_subgroupOf.2 (hEGS (Subgroup.mem_subgroupOf.1 hy))
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGCv).toEquiv).trans hEGcard
    · intro a ha b hb
      obtain ⟨ha1, ha2⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 ha)
      obtain ⟨hb1, hb2⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 hb)
      exact Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) (hEMcomm _ ha2 _ hb2))
    · intro a ha
      obtain ⟨ha1, ha2⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 ha)
      exact Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) (hEMsq _ ha2))
    · exact Subgroup.mem_subgroupOf.2 ((hmemEG v).2 ⟨hvN, hvEM⟩)
    · intro s hs y hy
      obtain ⟨hy1, hy2⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 hy)
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have hsN : (s : G) ∈ NW x := hSN hsS
      have := hEMnorm ⟨(s : G), hsN⟩ hsS _ hy2
      refine Subgroup.mem_subgroupOf.2 ((hmemEG _).2 ⟨(NW x).mul_mem ((NW x).mul_mem hsN hy1)
        ((NW x).inv_mem hsN), ?_⟩)
      exact this
    ·
      intro y hy
      have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.1 hy
      have hyN : (y : G) ∈ NW x := hSN hyS
      let yM : ↥(NW x) := ⟨(y : G), hyN⟩
      have hyMS : yM ∈ S.subgroupOf (NW x) := hyS
      constructor
      · rintro ⟨g, hg⟩
        have hgy : (g : G) * x * (g : G)⁻¹ = (y : G) := congrArg Subtype.val hg
        have hy2 : orderOf (y : G) = 2 := by rw [← hgy, orderOf_conj_eq, hxord]
        have hyG2 : (y : G) * (y : G) = 1 := by
          have h1 := pow_orderOf_eq_one (y : G)
          rw [hy2, sq] at h1
          exact h1
        have hyG1 : (y : G) ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hy2
          omega
        have hyc : (y : G) * v = v * (y : G) := mem_centralizer_singleton_iff.1 y.2
        have hxy : IsConj x (y : G) := isConj_iff.2 ⟨g, hgy⟩
        have hyvG : (y : G) * v = ((g : G) * a) * x * ((g : G) * a)⁻¹ := by
          have hgv : (g : G) * v = v * (g : G) := mem_centralizer_singleton_iff.1 g.2
          have hgv' : (g : G)⁻¹ * v = v * (g : G)⁻¹ := by
            rw [inv_mul_eq_iff_eq_mul]
            calc v = (v * (g : G)) * (g : G)⁻¹ := by group
              _ = ((g : G) * v) * (g : G)⁻¹ := by rw [hgv]
              _ = (g : G) * (v * (g : G)⁻¹) := by group
          rw [← hgy]
          calc (g : G) * x * (g : G)⁻¹ * v = (g : G) * x * ((g : G)⁻¹ * v) := by group
            _ = (g : G) * x * (v * (g : G)⁻¹) := by rw [hgv']
            _ = (g : G) * (x * v) * (g : G)⁻¹ := by group
            _ = (g : G) * (a * x * a⁻¹) * (g : G)⁻¹ := by rw [hxxv]
            _ = ((g : G) * a) * x * ((g : G) * a)⁻¹ := by group
        have hyv2 : orderOf ((y : G) * v) = 2 := by rw [hyvG, orderOf_conj_eq, hxord]
        have hyvN : (y : G) * v ∈ NW x := (NW x).mul_mem hyN hvN
        obtain ⟨c₁, hc₁N, hc₁⟩ := hF1 _ hyN hy2 hxy
        obtain ⟨c₂, hc₂N, hc₂⟩ := hF1 _ hyvN hyv2 (isConj_iff.2 ⟨(g : G) * a, hyvG.symm⟩)
        have hxyM : IsConj (⟨x, hxN⟩ : ↥(NW x)) yM := isConj_iff.2 ⟨⟨c₁, hc₁N⟩, Subtype.ext hc₁⟩
        have hxyvM : IsConj (⟨x, hxN⟩ : ↥(NW x)) (yM * ⟨v, hvN⟩) :=
          isConj_iff.2 ⟨⟨c₂, hc₂N⟩, Subtype.ext hc₂⟩
        have hyM2 : yM * yM = 1 := Subtype.ext hyG2
        have hyM1 : yM ≠ 1 := fun h1 => hyG1 (congrArg Subtype.val h1)
        have hyMv : yM * ⟨v, hvN⟩ = ⟨v, hvN⟩ * yM := Subtype.ext hyc
        obtain ⟨hyE, -, hyv⟩ := (hEMiff yM hyMS).1 ⟨hyM2, hyM1, hyMv, hxyM, hxyvM⟩
        refine ⟨Subgroup.mem_subgroupOf.2 ((hmemEG _).2 ⟨hyN, hyE⟩), ?_, ?_⟩
        · intro h1
          exact hyG1 (congrArg Subtype.val h1)
        · intro h1
          exact hyv (Subtype.ext (congrArg (fun m : ↥Cv => (m : G)) h1))
      · rintro ⟨hyE, hy1, hyv⟩
        obtain ⟨_, hyEM⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 hyE)
        have hyM1 : yM ≠ 1 := fun h1 => hy1 (Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) h1))
        have hyMv : yM ≠ ⟨v, hvN⟩ := fun h1 => hyv (Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) h1))
        obtain ⟨c, hcv, hcx⟩ := hEMtrans yM hyEM hyM1 hyMv
        have hcCv : (c : G) ∈ Cv := (hmemCv _).2 (congrArg (fun m : ↥(NW x) => (m : G)) hcv)
        exact ⟨⟨(c : G), hcCv⟩, Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) hcx)⟩
    · exact ⟨1, by simp⟩
    · exact Subgroup.mem_subgroupOf.2 ((hmemEG x).2 ⟨hxN, hxEM⟩)
    · exact fun z hz => hz
    · intro g hg y hy
      have hgx : (g : G) * x = x * (g : G) := congrArg Subtype.val hg
      have hgN : (g : G) ∈ NW x := hCN (mem_centralizer_singleton_iff.2 hgx)
      have hgv : (g : G) * v = v * (g : G) := mem_centralizer_singleton_iff.1 g.2
      obtain ⟨hy1, hy2⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 hy)
      have := hEMcent ⟨(g : G), hgN⟩ (Subtype.ext hgx) (Subtype.ext hgv) _ hy2
      refine Subgroup.mem_subgroupOf.2 ((hmemEG _).2 ⟨(NW x).mul_mem ((NW x).mul_mem hgN hy1)
        ((NW x).inv_mem hgN), ?_⟩)
      exact this
  have hS128 : Nat.card S' ≤ 128 := by
    have h1 : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSCv).toEquiv
    rw [h1]
    have h2 := card_S_le hn h hS
    rcases hn with rfl | rfl
    · rw [alt_two_part_five] at h2
      omega
    · rw [alt_two_part_seven] at h2
      omega
  have hex : ∃ s ∈ S', s * s = 1 ∧ s ∉ E' :=
    ⟨⟨s₁, hSCv hs₁S⟩, hs₁S, Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) hs₁sq), fun hmem => hs₁E (by
      obtain ⟨_, hm⟩ := (hmemEG _).1 (Subgroup.mem_subgroupOf.1 hmem)
      exact hm)⟩
  have hZS : ∀ s ∈ S', (∀ t ∈ S', s * t = t * s) → s * s = 1 → s ≠ 1 → s = v' := by
    intro s hs hsc hsq hs1
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have hsN : (s : G) ∈ NW x := hSN hsS
    have := hEMZ ⟨(s : G), hsN⟩ hsS (fun t ht => Subtype.ext (by
        have h1 := hsc ⟨(t : G), hSCv (Subgroup.mem_subgroupOf.1 ht)⟩ (Subgroup.mem_subgroupOf.2 ?_)
        · exact congrArg (fun m : ↥Cv => (m : G)) h1
        · exact Subgroup.mem_subgroupOf.1 ht))
      (Subtype.ext (congrArg (fun m : ↥Cv => (m : G)) hsq))
      (fun h1 => hs1 (Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) h1)))
    exact Subtype.ext (congrArg (fun m : ↥(NW x) => (m : G)) this)
  have hNT := L4.normalizer_eq_top hZD hTI hS128 hex hZS
  refine ⟨fun c hc => ?_, hfusN⟩
  have hcn : (⟨c, hc⟩ : ↥Cv) ∈ normalizer (E' : Set ↥Cv) := by
    rw [hNT]
    exact Subgroup.mem_top _
  have hx'E' : x' ∈ E' := Subgroup.mem_subgroupOf.2 ((hmemEG x).2 ⟨hxN, hxEM⟩)
  have h3 := (mem_normalizer_iff.1 hcn x').1 hx'E'
  have h4 : c * x * c⁻¹ ∈ EG := Subgroup.mem_subgroupOf.1 h3
  exact hF2 c (hSN (hEGS h4))

end TIG

end CFSG.GH74.GLS.C3.Layer1.Bk
