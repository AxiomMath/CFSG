module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Six

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G] {M : Subgroup G} {𝒳 : Set (Subgroup G)}

theorem exists_third (hr : 3 ≤ Nat.card ↥𝒳) (Y₀ Y₁ : Subgroup G) :
    ∃ Y₂ ∈ 𝒳, Y₂ ≠ Y₀ ∧ Y₂ ≠ Y₁ := by
  by_contra hcon
  push Not at hcon
  have hsub : 𝒳 ⊆ ({Y₀, Y₁} : Set (Subgroup G)) := by
    intro Y hY
    by_cases h0 : Y = Y₀
    · exact Or.inl h0
    · exact Or.inr (hcon Y hY h0)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({Y₀, Y₁} : Set (Subgroup G)).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  rw [← Nat.card_coe_set_eq] at h1
  omega


namespace Fam

variable (F : Fam M 𝒳)
include F

theorem inf_V {Y Y' : Subgroup G} (hY : Y ∈ 𝒳) (hY' : Y' ∈ 𝒳) (hne : Y ≠ Y') {x : G}
    (hx : x ∈ pCoreOf 2 Y) (hx' : x ∈ pCoreOf 2 Y') : x = 1 := by
  obtain ⟨a', ha'⟩ := F.blk Y' hY'
  exact Blk3.eq_one_of_centralizes ha' hx' fun y hy =>
    F.comm Y hY Y' hY' hne x ((pCoreOf_le_self Y) hx) y hy

theorem sq_sup {Y Y' : Subgroup G} (hY : Y ∈ 𝒳) (hY' : Y' ∈ 𝒳) {u : G}
    (hu : u ∈ pCoreOf 2 Y ⊔ pCoreOf 2 Y') : u * u = 1 := by
  obtain ⟨a, ha⟩ := F.blk Y hY
  obtain ⟨a', ha'⟩ := F.blk Y' hY'
  by_cases hne : Y = Y'
  · subst hne
    rw [sup_idem] at hu
    exact ha.sq u hu
  · have hc : ∀ p ∈ pCoreOf 2 Y, ∀ q ∈ pCoreOf 2 Y', p * q = q * p := fun p hp q hq =>
      F.comm Y hY Y' hY' hne p ((pCoreOf_le_self Y) hp) q ((pCoreOf_le_self Y') hq)
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hc).1 hu
    have c1 := hc p hp q hq
    calc p * q * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [← c1]
      _ = (p * p) * (q * q) := by group
      _ = 1 := by rw [ha.sq p hp, ha'.sq q hq, one_mul]

theorem centralizes_third {Y₀ Y₁ Y₂ : Subgroup G} (hY₀ : Y₀ ∈ 𝒳) (hY₁ : Y₁ ∈ 𝒳) (hY₂ : Y₂ ∈ 𝒳)
    (h0 : Y₂ ≠ Y₀) (h1 : Y₂ ≠ Y₁) {u : G} (hu : u ∈ pCoreOf 2 Y₀ ⊔ pCoreOf 2 Y₁) :
    ∀ x ∈ Y₂, u * x = x * u := by
  have hle : pCoreOf 2 Y₀ ⊔ pCoreOf 2 Y₁ ≤ Subgroup.centralizer (Y₂ : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact F.comm Y₂ hY₂ Y₀ hY₀ h0 y hy z ((pCoreOf_le_self Y₀) hz)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact F.comm Y₂ hY₂ Y₁ hY₁ h1 y hy z ((pCoreOf_le_self Y₁) hz)
  intro x hx
  exact (Subgroup.mem_centralizer_iff.1 (hle hu) x hx).symm

theorem exists_klein [Finite G] (hr : 3 ≤ Nat.card ↥𝒳) {v : G} (hvM : v ∈ M) (hv1 : v ≠ 1)
    (hv2 : v * v = 1) :
    ∃ U : Subgroup G, IsKleinFour ↥U ∧ U ≤ M ∧ (∀ u ∈ U, u * v = v * u) ∧
      (∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M) := by
  have key : ∃ Y₀ ∈ 𝒳, ∃ Y₁ ∈ 𝒳, Y₀ ≠ Y₁ ∧ ∃ U : Subgroup G, IsKleinFour ↥U ∧
      U ≤ pCoreOf 2 Y₀ ⊔ pCoreOf 2 Y₁ ∧ ∀ u ∈ U, u * v = v * u := by
    by_cases hmove : ∃ Y₀ ∈ 𝒳, conjSub v Y₀ ≠ Y₀
    ·
      obtain ⟨Y₀, hY₀, hne⟩ := hmove
      have hY₁ : conjSub v Y₀ ∈ 𝒳 := F.perm v hvM Y₀ hY₀
      obtain ⟨a₀, ha₀⟩ := F.blk Y₀ hY₀
      have hvv : conjSub v (conjSub v Y₀) = Y₀ := by
        rw [conjSub_conjSub, hv2, conjSub_one]
      have hV₁ : pCoreOf 2 (conjSub v Y₀) = conjSub v (pCoreOf 2 Y₀) := pCoreOf_conjSub v Y₀
      have hwv : ∀ w ∈ pCoreOf 2 Y₀, v * w * v⁻¹ ∈ pCoreOf 2 (conjSub v Y₀) := fun w hw => by
        rw [hV₁]
        exact conj_mem_conjSub hw
      have hcomm : ∀ w ∈ pCoreOf 2 Y₀, ∀ w' ∈ pCoreOf 2 Y₀,
          w' * (v * w * v⁻¹) = (v * w * v⁻¹) * w' :=
        fun w hw w' hw' => F.comm Y₀ hY₀ _ hY₁ hne.symm w' ((pCoreOf_le_self Y₀) hw') _
          ((pCoreOf_le_self _) (hwv w hw))
      let φ : ↥(pCoreOf 2 Y₀) →* G := MonoidHom.mk'
        (fun w => (w : G) * (v * (w : G) * v⁻¹)) (by
          intro w w'
          have h1 := hcomm w w.2 w' w'.2
          show (w : G) * w' * (v * ((w : G) * w') * v⁻¹) =
            ((w : G) * (v * (w : G) * v⁻¹)) * ((w' : G) * (v * (w' : G) * v⁻¹))
          calc (w : G) * w' * (v * ((w : G) * w') * v⁻¹)
              = (w : G) * (w' * (v * (w : G) * v⁻¹)) * (v * (w' : G) * v⁻¹) := by group
            _ = (w : G) * ((v * (w : G) * v⁻¹) * w') * (v * (w' : G) * v⁻¹) := by rw [h1]
            _ = ((w : G) * (v * (w : G) * v⁻¹)) * ((w' : G) * (v * (w' : G) * v⁻¹)) := by group)
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_one]
        intro w hw
        have hw' : (w : G) * (v * (w : G) * v⁻¹) = 1 := hw
        have h1 : (w : G) = (v * (w : G) * v⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hw'
        have h2 : (w : G) ∈ pCoreOf 2 (conjSub v Y₀) := by
          rw [h1]
          exact (pCoreOf 2 (conjSub v Y₀)).inv_mem (hwv w w.2)
        exact Subtype.ext (F.inf_V hY₀ hY₁ hne.symm w.2 h2)
      refine ⟨Y₀, hY₀, conjSub v Y₀, hY₁, hne.symm, φ.range, ?_, ?_, ?_⟩
      · have hcard : Nat.card φ.range = 4 := by
          rw [← ha₀.card]
          exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
        refine isKleinFour_of_card_four hcard ?_
        rintro _ ⟨w, rfl⟩
        have h1 := hcomm w w.2 w w.2
        show ((w : G) * (v * (w : G) * v⁻¹)) * ((w : G) * (v * (w : G) * v⁻¹)) = 1
        have hww : (w : G) * w = 1 := ha₀.sq w w.2
        have hvw : (v * (w : G) * v⁻¹) * (v * (w : G) * v⁻¹) = 1 := by
          calc (v * (w : G) * v⁻¹) * (v * (w : G) * v⁻¹) = v * ((w : G) * w) * v⁻¹ := by group
            _ = 1 := by rw [hww]; group
        calc ((w : G) * (v * (w : G) * v⁻¹)) * ((w : G) * (v * (w : G) * v⁻¹))
            = (w : G) * ((v * (w : G) * v⁻¹) * w) * (v * (w : G) * v⁻¹) := by group
          _ = (w : G) * (w * (v * (w : G) * v⁻¹)) * (v * (w : G) * v⁻¹) := by rw [← h1]
          _ = ((w : G) * w) * ((v * (w : G) * v⁻¹) * (v * (w : G) * v⁻¹)) := by group
          _ = 1 := by rw [hww, hvw, one_mul]
      · rintro _ ⟨w, rfl⟩
        exact (pCoreOf 2 Y₀ ⊔ pCoreOf 2 (conjSub v Y₀)).mul_mem
          (Subgroup.mem_sup_left w.2) (Subgroup.mem_sup_right (hwv w w.2))
      · rintro _ ⟨w, rfl⟩
        have h1 := hcomm w w.2 w w.2
        have hvw : v * ((w : G) * (v * (w : G) * v⁻¹)) * v⁻¹ = (w : G) * (v * (w : G) * v⁻¹) := by
          calc v * ((w : G) * (v * (w : G) * v⁻¹)) * v⁻¹
              = (v * (w : G) * v⁻¹) * ((v * v) * (w : G) * (v⁻¹ * v⁻¹)) := by group
            _ = (v * (w : G) * v⁻¹) * (w : G) := by
                have hvinv : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hv2, inv_one]
                rw [hv2, hvinv]
                group
            _ = (w : G) * (v * (w : G) * v⁻¹) := h1.symm
        exact (mul_inv_eq_iff_eq_mul.1 hvw).symm
    ·
      push Not at hmove
      obtain ⟨Y₀, hY₀, Y₁, hY₁, hne⟩ := F.two
      have hord : orderOf v = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
      have hS : IsPGroup 2 ↥(Subgroup.zpowers v) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
      have hfix : ∀ Y ∈ 𝒳, ∃ c ∈ pCoreOf 2 Y, c ≠ 1 ∧ v * c * v⁻¹ = c := by
        intro Y hY
        obtain ⟨a, ha⟩ := F.blk Y hY
        have hN : Subgroup.zpowers v ≤ Subgroup.normalizer (Y : Set G) :=
          Subgroup.zpowers_le.2 (mem_normalizer_iff_conjSub.2 (hmove Y hY))
        exact Blk3.exists_fixed ha hS (fun s hs w hw =>
          conj_mem_pCoreOf (mem_normalizer_iff_conjSub.1 (hN hs)) hw) (Subgroup.mem_zpowers v)
      obtain ⟨c₀, hc₀, hc₀1, hc₀v⟩ := hfix Y₀ hY₀
      obtain ⟨c₁, hc₁, hc₁1, hc₁v⟩ := hfix Y₁ hY₁
      obtain ⟨a₀, ha₀⟩ := F.blk Y₀ hY₀
      obtain ⟨a₁, ha₁⟩ := F.blk Y₁ hY₁
      have hc₀2 : c₀ * c₀ = 1 := ha₀.sq c₀ hc₀
      have hc₁2 : c₁ * c₁ = 1 := ha₁.sq c₁ hc₁
      have ho₀ : orderOf c₀ = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hc₀2) hc₀1
      have ho₁ : orderOf c₁ = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hc₁2) hc₁1
      have hcomm : ∀ p ∈ Subgroup.zpowers c₀, ∀ q ∈ Subgroup.zpowers c₁, p * q = q * p := by
        intro p hp q hq
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
        exact (Commute.zpow_zpow (show Commute c₀ c₁ from
          F.comm Y₀ hY₀ Y₁ hY₁ hne c₀ ((pCoreOf_le_self Y₀) hc₀) c₁
            ((pCoreOf_le_self Y₁) hc₁)) i j).eq
      have hz₀ : Subgroup.zpowers c₀ ≤ pCoreOf 2 Y₀ := Subgroup.zpowers_le.2 hc₀
      have hz₁ : Subgroup.zpowers c₁ ≤ pCoreOf 2 Y₁ := Subgroup.zpowers_le.2 hc₁
      have hcard : Nat.card ↥(Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁) = 4 := by
        rw [card_sup_of_commute hcomm (fun x hx hx' => F.inf_V hY₀ hY₁ hne (hz₀ hx) (hz₁ hx')),
          Nat.card_zpowers, Nat.card_zpowers, ho₀, ho₁]
      have hle : Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁ ≤ pCoreOf 2 Y₀ ⊔ pCoreOf 2 Y₁ :=
        sup_le_sup hz₀ hz₁
      refine ⟨Y₀, hY₀, Y₁, hY₁, hne, Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁,
        isKleinFour_of_card_four hcard (fun x hx => F.sq_sup hY₀ hY₁ (hle hx)), hle, ?_⟩
      have hcv : ∀ c : G, v * c * v⁻¹ = c → c ∈ Subgroup.centralizer ({v} : Set G) := fun c h => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.1 h).symm
      have hU : Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁ ≤ Subgroup.centralizer ({v} : Set G) :=
        sup_le (Subgroup.zpowers_le.2 (hcv c₀ hc₀v)) (Subgroup.zpowers_le.2 (hcv c₁ hc₁v))
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.1 (hU hu)
  obtain ⟨Y₀, hY₀, Y₁, hY₁, hne, U, hU, hUle, hUv⟩ := key
  obtain ⟨Y₂, hY₂, h20, h21⟩ := exists_third hr Y₀ Y₁
  refine ⟨U, hU, ?_, hUv, ?_⟩
  · exact hUle.trans (sup_le ((pCoreOf_le_self Y₀).trans (F.le Y₀ hY₀))
      ((pCoreOf_le_self Y₁).trans (F.le Y₁ hY₁)))
  · intro u hu hu1
    exact F.cent u hu1 (klein_sq hU hu)
      ⟨Y₂, hY₂, F.centralizes_third hY₀ hY₁ hY₂ h20 h21 (hUle hu)⟩

theorem alpha [Finite G] (hr : 3 ≤ Nat.card ↥𝒳) {x : G} (hx : x ∉ M) {Y Y' : Subgroup G}
    (hY : Y ∈ 𝒳) (hY' : Y' ∈ 𝒳) {v : G} (hvW : v ∈ conjSub x (pCoreOf 2 Y ⊔ pCoreOf 2 Y'))
    (hvM : v ∈ M) : v = 1 := by
  by_contra hv1
  have F' := F.conj x
  have hvW' : v ∈ pCoreOf 2 (conjSub x Y) ⊔ pCoreOf 2 (conjSub x Y') := by
    rw [pCoreOf_conjSub, pCoreOf_conjSub]
    have e : conjSub x (pCoreOf 2 Y ⊔ pCoreOf 2 Y') =
        conjSub x (pCoreOf 2 Y) ⊔ conjSub x (pCoreOf 2 Y') := Subgroup.map_sup _ _ _
    rwa [e] at hvW
  have hZ : conjSub x Y ∈ conjSub x '' 𝒳 := ⟨Y, hY, rfl⟩
  have hZ' : conjSub x Y' ∈ conjSub x '' 𝒳 := ⟨Y', hY', rfl⟩
  have hv2 : v * v = 1 := F'.sq_sup hZ hZ' hvW'
  have hr' : 3 ≤ Nat.card ↥(conjSub x '' 𝒳) := by
    have h1 : (conjSub x '' 𝒳).ncard = 𝒳.ncard :=
      Set.ncard_image_of_injective _ (conjSub_injective x)
    rw [Nat.card_coe_set_eq, h1, ← Nat.card_coe_set_eq]
    exact hr
  obtain ⟨Z₂, hZ₂, hZ20, hZ21⟩ := exists_third hr' (conjSub x Y) (conjSub x Y')
  have hCv : Subgroup.centralizer ({v} : Set G) ≤ conjSub x M :=
    F'.cent v hv1 hv2 ⟨Z₂, hZ₂, F'.centralizes_third hZ hZ' hZ₂ hZ20 hZ21 hvW'⟩
  obtain ⟨U, hU, hUM, hUv, hUC⟩ := F.exists_klein hr hvM hv1 hv2
  have hUN : U ≤ conjSub x M := fun u hu =>
    hCv (Subgroup.mem_centralizer_singleton_iff.2 (hUv u hu))
  have h34 := F'.lemma34_big hr' hUN hU (g := x⁻¹) (fun u hu hu1 => by
    rw [conjSub_inv_conjSub]
    exact hUC u hu hu1)
  apply hx
  have := mem_conjSub_iff.1 h34
  simpa using this

end Fam

end CFSG.CGT.PushingUpLit.A4.L34
