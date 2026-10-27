module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwoBurnside
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineFourQuot

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    (∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) →
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ →
    (∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) →
    ¬ ∀ v ∈ T, v ^ 2 = 1 → v ∉ szT₁ L T ⊔ zpowers t →
      ∃ g ∈ normalizer (szA₁ (szT₁ L T) : Set G) ⊓ normalizer (R₂ : Set G) ⊓
        normalizer (U₁ : Set G), g⁻¹ * t * g = v

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem exists_comm_mem_t (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    {x : G} (hx : x ∈ U₁) (hxt : t * x * t⁻¹ * x⁻¹ ∈ R₂) :
    ∃ y ∈ U₁, (y * t * y⁻¹ * t⁻¹)⁻¹ * x ∈ R₂ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have hxt' : x * t * x⁻¹ * t⁻¹ ∈ R₂ := by
    have := inv_mem hxt
    rwa [show (t * x * t⁻¹ * x⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ by group] at this
  exact hU.exists_inv_comm_mul_mem hR (hU.mem_sup_of_comm_mem hR htt hx hxt')

section Certificates

theorem exists_comm_mem_of_outer_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {x : G} (hx : x ∈ U₁) (hxv : v * x * v⁻¹ * x⁻¹ ∈ R₂) :
    ∃ w ∈ U₁, (w * v * w⁻¹ * v⁻¹)⁻¹ * x ∈ R₂ := by
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hvR : v ∈ normalizer (R₂ : Set G) := hNR (hTA hvT)
  have htR : t ∈ normalizer (R₂ : Set G) := hNR (hTA htT)
  have hvU : v ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR hvT
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hNc : ∀ n ∈ R₂, ∀ x ∈ U₁, n * x = x * n := fun n hn x hx =>
    mem_centralizer_iff.mp (hU.le_centralizer hx) n hn
  have hM2 : ∀ x ∈ U₁, x * x ∈ R₂ := fun x hx => by rw [← sq]; exact hU.sq_mem x hx
  have htM : ∀ x ∈ U₁, t * x * t⁻¹ ∈ U₁ := fun x hx => (mem_normalizer_iff.mp htU x).mp hx
  have hvM : ∀ x ∈ U₁, v * x * v⁻¹ ∈ U₁ := fun x hx => (mem_normalizer_iff.mp hvU x).mp hx
  have htN : ∀ n ∈ R₂, t * n * t⁻¹ ∈ R₂ := fun n hn => (mem_normalizer_iff.mp htR n).mp hn
  have hvN : ∀ n ∈ R₂, v * n * v⁻¹ ∈ R₂ := fun n hn => (mem_normalizer_iff.mp hvR n).mp hn
  have hkerτ : ∀ x ∈ U₁, x * t * x⁻¹ * t⁻¹ ∈ R₂ → x ∈ szT₁ L T ⊔ R₂ :=
    fun x hx hxt => hU.mem_sup_of_comm_mem hR htt hx hxt
  have hsurjτ : ∀ y ∈ szT₁ L T ⊔ R₂, ∃ z ∈ U₁, (z * t * z⁻¹ * t⁻¹)⁻¹ * y ∈ R₂ :=
    fun y hy => hU.exists_inv_comm_mul_mem hR hy
  have hfreeH : ∀ y ∈ szT₁ L T ⊔ R₂, y * v * y⁻¹ * v⁻¹ ∈ R₂ →
      ∃ w ∈ szT₁ L T ⊔ R₂, (w * v * w⁻¹ * v⁻¹)⁻¹ * y ∈ R₂ := by
    intro y hy hyv
    obtain ⟨w₀, hw₀, r, hr, rfl⟩ := hR.mem_sup_iff.mp hy
    have hνr : r * v * r⁻¹ * v⁻¹ ∈ R₂ := by
      simpa [mul_assoc] using mul_mem hr (hvN _ (inv_mem hr))
    have hνw₀ : w₀ * v * w₀⁻¹ * v⁻¹ ∈ szT₁ L T ⊓ R₂ := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := mul_mem hw₀ ((mem_normalizer_iff.mp (hTN₁ hvT) _).mp (inv_mem hw₀))
        simpa [mul_assoc] using this
      · have e : w₀ * v * w₀⁻¹ * v⁻¹ =
            (w₀ * (r * v * r⁻¹ * v⁻¹) * w₀⁻¹)⁻¹ * ((w₀ * r) * v * (w₀ * r)⁻¹ * v⁻¹) := by group
        rw [e]
        exact mul_mem (inv_mem (by
          rw [hR.commT₁ _ hw₀ _ hνr, mul_inv_cancel_right]; exact hνr)) hyv
    rw [hR.inf] at hνw₀
    obtain ⟨w₁, hw₁, hw₁eq⟩ := h.exists_eq_comm_of_outer_of_card_sylow hS2 hvT hv2 hvS hw₀ hνw₀
    refine ⟨w₁, mem_sup_left hw₁, ?_⟩
    rw [← hw₁eq, inv_mul_cancel_left]
    exact hr
  have hxv' : x * v * x⁻¹ * v⁻¹ ∈ R₂ := by
    have := inv_mem hxv
    rwa [show (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ by group] at this
  exact exists_comm_mem_of_free_layers (H := szT₁ L T ⊔ R₂) le_sup_right
    (sup_le (le_sup_left.trans hU.le) (le_sup_right.trans hU.le)) hNc hU.comm_mem hM2 htM hvM
    htN hvN htt hvv hvt.symm hkerτ hsurjτ hfreeH hx hxv'

theorem mem_cases_of_four (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hfour : ∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t) {s : G}
    (hs : s ∈ U₁ ⊔ T) : s ∈ U₁ ∨ t⁻¹ * s ∈ U₁ ∨ v⁻¹ * s ∈ U₁ ∨ (t * v)⁻¹ * s ∈ U₁ := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hTU := hU.le_normalizer h hS2 hR
  have hconj : ∀ c ∈ T, ∀ u ∈ U₁, c⁻¹ * u * c ∈ U₁ := fun c hc u hu =>
    (mem_normalizer_iff''.mp (hTU hc) u).mp hu
  obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU hs
  by_cases hcS : c ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hcS
    have hyU : y ∈ U₁ := hU.le (mem_sup_left hy)
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left
      rw [← hyz, hz1, mul_one]
      exact mul_mem hu hyU
    · right; left
      rw [← hyz, hz1, show t⁻¹ * (u * (y * t)) = t⁻¹ * (u * y) * t by group]
      exact hconj t htT _ (mul_mem hu hyU)
  · have hv2' : v ^ 2 ∈ szT₁ L T ⊔ zpowers t := by rw [hv2]; exact one_mem _
    have hcv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hc hvT (hfour c hc) hv2' hcS hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hcv
    have hyU : y ∈ U₁ := hU.le (mem_sup_left hy)
    have hc' : c = y * z * v := by rw [hyz]; group
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · right; right; left
      rw [hc', hz1, show v⁻¹ * (u * (y * 1 * v)) = v⁻¹ * (u * y) * v by group]
      exact hconj v hvT _ (mul_mem hu hyU)
    · right; right; right
      rw [hc', hz1, show (t * v)⁻¹ * (u * (y * t * v)) = v⁻¹ * (t⁻¹ * (u * y) * t) * v by group]
      exact hconj v hvT _ (hconj t htT _ (mul_mem hu hyU))

theorem fourData_of_four (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hfour : ∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) : SixNineFour.FourData R₂ U₁ (U₁ ⊔ T) t v f := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hTR : T ≤ normalizer (R₂ : Set G) := fun s hs => hNR (hTA hs)
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  obtain ⟨htvT, htv2, htvS⟩ := h.mul_outer_of_card_sylow hS2 hvT hv2 hvS
  have hnotU : ∀ w ∈ T, w ∉ szT₁ L T ⊔ zpowers t → w ∉ U₁ := fun w hwT hwS hwU => by
    have : w ∈ szT₁ L T := by rw [← hU.inf_eq h hR]; exact mem_inf.mpr ⟨hwU, hwT⟩
    exact hwS (mem_sup_left this)
  exact
    { sylow := hS
      le := le_sup_right.trans hU.le
      le_S := le_sup_left
      normR := sup_le (hU.le_centralizer.trans (centralizer_le_normalizer _)) hTR
      normU := sup_le Subgroup.le_normalizer (hU.le_normalizer h hS2 hR)
      comm := hU.comm_mem
      sq := hU.sq_mem
      card := by
        rw [hU.card, hR.card, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
      commS := fun x hx y hy => by
        have := hU.commutator_le h hS2 hR (commutator_mem_commutator hx hy)
        rwa [commutatorElement_def] at this
      t_mem := mem_sup_right htT
      v_mem := mem_sup_right hvT
      t_sq := h.sq_eq_one
      v_sq := hv2
      tv_comm := hvt.symm
      t_not_mem := hU.t_not_mem
      v_not_mem := hnotU v hvT hvS
      tv_not_mem := hnotU _ htvT htvS
      cases := fun s hs => hU.mem_cases_of_four h hS2 hR hfour hvT hv2 hvS hs
      free := by
        rintro w (rfl | rfl | rfl) x hx hxw
        · exact hU.exists_comm_mem_t hR hx hxw
        · exact hU.exists_comm_mem_of_outer_of_card_sylow h hS2 hR hvT hv2 hvS hx hxw
        · exact hU.exists_comm_mem_of_outer_of_card_sylow h hS2 hR htvT htv2 htvS hx hxw }

theorem exists_normalizer_conj_of_four (hG : Goldschmidt1974) (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁)
    (hfour : ∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {g : G} (hg : g ∈ normalizer (R₂ : Set G))
    (hgt : g⁻¹ * t * g = v) :
    ∃ n ∈ normalizer (szA₁ (szT₁ L T) : Set G) ⊓ normalizer (R₂ : Set G) ⊓
      normalizer (U₁ : Set G), n⁻¹ * t * n = v := by
  have hD := hU.fourData_of_four h hS2 hR hS hfour hvT hv2 hvS
  obtain ⟨n, hn, hnv⟩ := hD.exists_mem_normalizer hG h.two_le hg hgt
  obtain ⟨hnR, hnU⟩ := mem_inf.mp hn
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hvR : v ∈ normalizer (R₂ : Set G) := hNR (hTA hvT)
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  obtain ⟨-, hvA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hvT hv2 hvS
  obtain ⟨d, k, hdL, hd⟩ := h.exists_u3RTorus_of_card_sylow hS2
  have hdR : d ∈ normalizer (R₂ : Set G) :=
    hNR (h.inf_normalizer_le_normalizer_szA ⟨hdL, hd.mem_normalizer_T₁⟩)
  obtain ⟨hcL, hcN, hcA⟩ :=
    h.comm_mem_of_outer_of_card_sylow hS2 hvT hv2 hvS hdL hd.mem_normalizer_T₁
  have hc := h.mem_centralizer_of_mem_borel_of_card_sylow hS2 hR hcL hcN hcA
  have hvC : v ∉ centralizer (R₂ : Set G) := fun hvC =>
    hD.v_not_mem (hC (mem_inf.mpr ⟨mem_sup_right hvT, hvC⟩))
  obtain ⟨hker, himg⟩ :=
    hR.free_of_not_mem_centralizer hvt hvR hvA hd.comm_t hdR hd.trans hc hvC
  set r := v⁻¹ * (n⁻¹ * t * n) with hr
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hr2 : r * r = 1 := by rw [← sq]; exact hU.sq_R₂ r hnv
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hvr : v * r = n⁻¹ * t * n := by rw [hr]; group
  have hvr2 : v * r * (v * r) = 1 := by
    rw [hvr, show n⁻¹ * t * n * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n by group, htt, mul_one,
      inv_mul_cancel]
  have hrv : v * r * v⁻¹ = r := by
    rw [hvinv]
    calc v * r * v = (v * r * (v * r)) * r⁻¹ := by group
      _ = r := by rw [hvr2, one_mul, hrinv]
  have hrA : r ∈ szA₁ (szT₁ L T) := hker r hnv hrv
  obtain ⟨s, hs, hsv⟩ := himg r hrA
  have e1 : n⁻¹ * t * n = s * v * s⁻¹ := by
    calc n⁻¹ * t * n = v * r := hvr.symm
      _ = r * v := hvA r hrA
      _ = s * v * s⁻¹ := by rw [← hsv]; group
  have hm : (n * s)⁻¹ * t * (n * s) = v := by
    rw [show (n * s)⁻¹ * t * (n * s) = s⁻¹ * (n⁻¹ * t * n) * s by group, e1]
    group
  have hmR : n * s ∈ normalizer (R₂ : Set G) := mul_mem hnR (Subgroup.le_normalizer hs)
  refine ⟨n * s, mem_inf.mpr ⟨mem_inf.mpr ⟨?_, hmR⟩,
    mul_mem hnU (Subgroup.le_normalizer (hU.le (mem_sup_right hs)))⟩, hm⟩
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun a ha => ?_
  have haR : (n * s)⁻¹ * a * (n * s) ∈ R₂ := (mem_normalizer_iff''.mp hmR a).mp (hR.le ha)
  have hat : a * t = t * a := hR.szA₁_comm_t ha
  refine hker _ haR ?_
  have hva : v * ((n * s)⁻¹ * a * (n * s)) = ((n * s)⁻¹ * a * (n * s)) * v := by
    rw [← hm]
    calc (n * s)⁻¹ * t * (n * s) * ((n * s)⁻¹ * a * (n * s)) = (n * s)⁻¹ * (t * a) * (n * s) := by
          group
      _ = (n * s)⁻¹ * (a * t) * (n * s) := by rw [hat]
      _ = (n * s)⁻¹ * a * (n * s) * ((n * s)⁻¹ * t * (n * s)) := by group
  rw [hva, mul_inv_cancel_right]

end Certificates

end U3U1Data

section Certificates

theorem u3SixNineFourInput_of_rank (hrank : U3SixNineRankInput) : U3SixNineFourInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU hncyc hS hC hfour hall
  apply hrank G L f t T R₂ U₁ h hS2 hR hU hncyc hS hC hfour
  intro v hvT hv2 hvS
  obtain ⟨g, hg, hgt⟩ := hall v hvT hv2 hvS
  exact hU.exists_normalizer_conj_of_four goldschmidt1974_of_milestone h hS2 hR hS hC hfour hvT
    hv2 hvS (mem_inf.mp hg).2 hgt

end Certificates

end CFSG.SeitzReduction.RankOne
