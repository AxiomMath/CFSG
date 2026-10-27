module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A03
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive
public import CFSG.ClassicalInvolution.Asc77.AscS24BDefs
public import CFSG.ClassicalInvolution.Asc77.AscS24BFrame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngC

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem exists_conj_xy (hs : Hyp23Setting Ω K K' z) {u : G} (hu : u ∈ K ⊔ K') (hu1 : u ≠ 1)
    (huz : u ≠ z) (hu2 : u * u = 1) {L L' : Subgroup G} (hL : L ∈ twinSet Ω K)
    (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G} (hR₁ : IsSylow2In R₁ L)
    (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G} (hx : x ∈ R₁) (hy : y ∈ R₂)
    (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ K ⊔ K', c * u * c⁻¹ = x * y := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hLΩ : L ∈ Ω := hL.1
  have hL'Ω : L' ∈ Ω := hL'.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hs.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet hs.hz hL'

  have hM : K ⊔ K' = L ⊔ L' := by
    have hLm : L ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL
    have hL'm : L' ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL'
    rcases hLm with rfl | rfl <;> rcases hL'm with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact sup_comm _ _
    · exact absurd rfl hne
  have huM : u ∈ L ⊔ L' := hM ▸ hu
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hLΩ hL'Ω hne.symm hzL hzL'
  have hLC : L ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hLC hL'C

  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    T7A.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr huM)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  have hu'2 : (a * b) * (a * b) = 1 := by
    rw [hab]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu'2
  have haL : a ∈ L := hR₁.1 ha
  have hbL' : b ∈ L' := hR₂.1 hb
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hLΩ hL'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzL.unique (a * a) (L.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzL.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzL'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = z := by
        rw [← hab]
        rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
        · left; rw [h1, h2, one_mul]
        · right; rw [h1, h2, one_mul]
        · right; rw [h1, h2, mul_one]
        · left; rw [h1, h2]; exact hzL.sq
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rcases hu'z with h' | h'
      · exact hu1 (by rw [hu, h']; group)
      · exact huz (by
          rw [hu, h']
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group)
    · exact h
  have hbb : b * b = z := by
    have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzL.sq
  have hx2 : x * x = z := T7B.mul_self_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hy2 : y * y = z := T7B.mul_self_eq_of_orderOf_four hzL' (hR₂.1 hy) oy

  obtain ⟨k, hkL, hk⟩ := T7B.exists_conj_of_sq_eq hs.stand.modU hLΩ hzL haL (hR₁.1 hx) haa hx2
  set b₁ := k * b * k⁻¹ with hb₁
  have hb₁L' : b₁ ∈ L' := (Subgroup.mem_normalizer_iff.mp (hLN hkL) b).mp hbL'
  have hb₁2 : b₁ * b₁ = z := by
    have e : b₁ * b₁ = k * (b * b) * k⁻¹ := by rw [hb₁]; group
    rw [e, hbb]
    have := hzL.commute_of_mem hkL
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  have hxb₁ : x * b₁ = b₁ * x := by
    rw [← hk, hb₁]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hcab]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  have hxy : x * y = y * x := hc x hx y hy

  obtain ⟨ℓ, hℓL', hℓ⟩ := T7B.exists_conj_of_sq_eq hs.stand.modU hL'Ω hzL' hb₁L' (hR₂.1 hy) hb₁2 hy2

  obtain ⟨ℓ', hℓ'L', hℓ'b, hℓ'x⟩ := T7B.exists_centralizing_conj hΩ hLΩ hL'Ω hne hzL hzL'
    (hR₁.1 hx) (T7B.isPGroup_zpowers_of_orderOf_four ox) hℓL' hxb₁ hxy hℓ

  have hLM : L ≤ K ⊔ K' := hM ▸ le_sup_left
  have hL'M : L' ≤ K ⊔ K' := hM ▸ le_sup_right
  refine ⟨ℓ' * k * m, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL'M hℓ'L') (hLM hkL))
    (hM ▸ hmM), ?_⟩
  have hℓ'x' : ℓ' * x * ℓ'⁻¹ = x := by
    rw [hℓ'x]
    group
  calc ℓ' * k * m * u * (ℓ' * k * m)⁻¹ = ℓ' * k * (m * u * m⁻¹) * k⁻¹ * ℓ'⁻¹ := by group
    _ = ℓ' * k * (a * b) * k⁻¹ * ℓ'⁻¹ := by rw [hab]
    _ = ℓ' * ((k * a * k⁻¹) * (k * b * k⁻¹)) * ℓ'⁻¹ := by group
    _ = ℓ' * (x * b₁) * ℓ'⁻¹ := by rw [hk]
    _ = (ℓ' * x * ℓ'⁻¹) * (ℓ' * b₁ * ℓ'⁻¹) := by group
    _ = x * y := by rw [hℓ'x', hℓ'b]

theorem exists_conj_of_involution (hs : Hyp23Setting Ω K K' z) {u₁ u₂ : G}
    (h₁ : u₁ ∈ K ⊔ K') (h₁1 : u₁ ≠ 1) (h₁z : u₁ ≠ z) (h₁2 : u₁ * u₁ = 1)
    (h₂ : u₂ ∈ K ⊔ K') (h₂1 : u₂ ≠ 1) (h₂z : u₂ ≠ z) (h₂2 : u₂ * u₂ = 1) :
    ∃ c ∈ K ⊔ K', c * u₁ * c⁻¹ = u₂ := by
  have hst := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', hc, hu⟩ :=
    T7A.exists_sylow_pair_of_mem hΩ hK hK'Ω hs.hne hs.hz hzK' h₁ h₁2 h₁1
  obtain ⟨x, hx, ox⟩ := Q3T7P25.exists_orderOf_eq_four_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨y, hy, oy⟩ := Q3T7P25.exists_orderOf_eq_four_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK'Ω hR')
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hK hs.hz
  obtain ⟨c₁, hc₁, e₁⟩ := exists_conj_xy hs h₁ h₁1 h₁z h₁2 hKt hs.hK' hs.hne hR hR' hc hx hy ox oy
  obtain ⟨c₂, hc₂, e₂⟩ := exists_conj_xy hs h₂ h₂1 h₂z h₂2 hKt hs.hK' hs.hne hR hR' hc hx hy ox oy
  refine ⟨c₂⁻¹ * c₁, (K ⊔ K').mul_mem ((K ⊔ K').inv_mem hc₂) hc₁, ?_⟩
  calc c₂⁻¹ * c₁ * u₁ * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * u₁ * c₁⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₂ * u₂ * c₂⁻¹) * c₂ := by rw [e₁, e₂]
    _ = u₂ := by group

theorem conj_mem_sup (hs : Hyp23Setting Ω K K' z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G} (hx : x ∈ K ⊔ K') :
    c * x * c⁻¹ ∈ K ⊔ K' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7K.conj_mem_sup_of hs.stand.hyp hs.stand.mem hs.hz
    hs.hK' hs.hne hs.twinSet_eq hc hx

end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C2
open CFSG.ClassicalInvolution.Asc77.T7C2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_g0 [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
    {z u : G} (hs : Hyp23Setting Ω K K' z) (hd : Hyp24Data Ω K K' W S R R' z u) :
    ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hd.hR'.1 hd.hR'.2.1
  obtain ⟨b, hbKW, ob⟩ := T7C.exists_orderOf_four_mem_inf hΩ hd.hW hd.hWS hK hRsyl
    hd.hR.2.2 hz
  obtain ⟨b', hb'KW, ob'⟩ := T7C.exists_orderOf_four_mem_inf hΩ hd.hW hd.hWS hK' hR'syl
    hd.hR'.2.2 hz'
  have hbR : b ∈ R := by
    have : K ⊓ (S : Subgroup G) = R :=
      hRsyl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hd.hR.2.1 hd.hR.2.2)
    rw [← this]
    exact ⟨hbKW.1, hd.hWS hbKW.2⟩
  have hb'R' : b' ∈ R' := by
    have : K' ⊓ (S : Subgroup G) = R' :=
      hR'syl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hd.hR'.2.1 hd.hR'.2.2)
    rw [← this]
    exact ⟨hb'KW.1, hd.hWS hb'KW.2⟩
  obtain ⟨huK, huW, hu2, hu1, huz⟩ := hd.hu
  rcases T7E.involution_cases hs hRsyl hR'syl hd.hR.2.2 hd.hR'.2.2 hbR hb'R' ob ob' huK
    (hd.hWS huW) hu2 hu1 huz (hWab u huW b hbKW.2) (hWab u huW b' hb'KW.2) with h | h
  · exact T7D.c24_2_of_frame hs hd hbKW hb'KW ob ob' h
  · have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hbKW.1 ob
    have hbinv : b⁻¹ = z * b :=
      (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz.sq])).symm
    refine T7D.c24_2_of_frame hs hd (b := b⁻¹) ⟨K.inv_mem hbKW.1, W.inv_mem hbKW.2⟩ hb'KW
      (by rw [orderOf_inv]; exact ob) ob' ?_
    rw [h, hbinv, mul_assoc]
end T7C2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C2
open CFSG.ClassicalInvolution.Asc77.T7C2
variable {G : Type} [Group G]
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem fixed_of_frame (c : Q3CL.Thompson.Ctx Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {ε : G} (hε : ε ∈ W)
    (h₁ : F.ρ.r * ε * F.ρ.r⁻¹ = ε) (h₂ : F.ρ'.r * ε * F.ρ'.r⁻¹ = ε)
    (h₃ : F.ρ₃.r * ε * F.ρ₃.r⁻¹ = ε) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) :
    r * ε * r⁻¹ = ε := by
  have ha := T7D.imgQ_mem F.ρ
  have ha' := T7D.imgQ_mem F.ρ'
  have ha₃ := T7D.imgQ_mem F.ρ₃
  have hmem : ∀ σ : Thompson.Rep Ω W, σ.r * ε * σ.r⁻¹ = ε →
      T7D.imgQ σ ∈ Thompson.muStab Ω W ε := fun σ h =>
    (c.mem_muStab_iff hε σ.hR σ.hr (q := T7D.imgQ σ) rfl).mpr h
  have hΔ : ∀ x ∈ Thompson.muDelta Ω W, x ∈ Thompson.muStab Ω W ε := fun x hx => by
    have hx' := S4.mem_closure_frame he ha ha' ha₃ hab hcomm hac hx
    refine (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr ?_ hx'
    rintro y (rfl | rfl | rfl)
    · exact hmem F.ρ h₁
    · exact hmem F.ρ' h₂
    · exact hmem F.ρ₃ h₃
  by_cases hrW : r ∈ W
  · have hWab := Q3CL.Thompson.commutes_of_mem_WSet c.hΩ c.hW
    rw [mul_inv_eq_iff_eq_mul]
    exact hWab r hrW ε hε
  · have hrq : Thompson.piG W r ∈ muGroup Ω W :=
      Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (Thompson.le_MGrp_of_mem_D hR hr))
    have hx : (⟨Thompson.piG W r, hrq⟩ : ↥(muGroup Ω W)) ∈ Thompson.muDelta Ω W :=
      ⟨R, hR, r, hr, hrW, rfl⟩
    exact (c.mem_muStab_iff hε hR hr (q := ⟨Thompson.piG W r, hrq⟩) rfl).mp (hΔ _ hx)

theorem exists_two_gen_W [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    ∃ a b : G, a ∈ W ∧ b ∈ W ∧ Subgroup.closure ({a, b} : Set G) = W := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, -, -, hFR, -, -, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have hm1 : m = 1 := by
    have h1 := Q3CL.Thompson.D_card hΩ hW F.ρ.hR
    have h2 : Nat.card ↥(F.ρ.R ⊓ W) = 4 * m := by rw [← h₁, Nat.card_zpowers, o₁]
    rw [h2, hFR, h8] at h1
    omega
  subst hm1
  have c12 : Commute x₁ x₂ := hWab x₁ m₁ x₂ m₂
  have c13 : Commute x₁ x₃ := hWab x₁ m₁ x₃ m₃
  have c23 : Commute x₂ x₃ := hWab x₂ m₂ x₃ m₃
  have o₂' : x₂ ^ 4 = 1 := by simpa [o₂] using pow_orderOf_eq_one x₂
  have o₃' : x₃ ^ 4 = 1 := by simpa [o₃] using pow_orderOf_eq_one x₃
  obtain ⟨hfr, hft, hfs⟩ := e_fixed c12 c13 c23 o₂' o₃' r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃
  have hεW : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W := W.mul_mem (W.mul_mem m₁ (W.inv_mem m₂)) (W.pow_mem m₃ 2)
  have hfix : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (x₁ * x₂⁻¹ * x₃ ^ 2) * r⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := fun R₀ hR₀ r hr =>
    fixed_of_frame c he F hab hcomm hac hεW hfr hft hfs hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hfW : n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr hεW
    have hfixc : ∀ σ : Thompson.Rep Ω W,
        σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by
      intro σ
      have hmemD : n⁻¹ * σ.r * n ∈ conjSub n⁻¹ σ.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ.r * n) * n⁻¹ = σ.r := by group
        rw [h1]
        exact σ.hr
      have := hfix _ (Q3CL.Thompson.conjSub_mem_D hΩ σ.hR hn') _ hmemD
      calc σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹
          = n * ((n⁻¹ * σ.r * n) * (x₁ * x₂⁻¹ * x₃ ^ 2) * (n⁻¹ * σ.r * n)⁻¹) * n⁻¹ := by group
        _ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by rw [this]
    rcases A3Mod.fixed_eq_one_or c12 c13 c23 o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂
        s₃ (hgen hfW) (hfixc F.ρ) (hfixc F.ρ') (hfixc F.ρ₃) with h | h
    · have h0 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := conj_eq_one_iff.mp h
      rw [h0]
      group
    · rw [h, pow_one]
  have hmemC : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    mem_centerIn_of_forall (Subgroup.le_normalizer hεW) hcent
  have hmem : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    ⟨hεW, hmemC⟩
  rw [hd.hZ] at hmem
  have hε1 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := Subgroup.mem_bot.mp hmem
  have hx₂ : x₂ = x₃ ^ 2 * x₁ := by
    calc x₂ = x₃ ^ 2 * (x₁ * x₂⁻¹ * x₃ ^ 2)⁻¹ * x₁ := by group
      _ = x₃ ^ 2 * x₁ := by rw [hε1, inv_one, mul_one]
  refine ⟨x₁, x₃, m₁, m₃, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact m₁
    · exact m₃
  · refine hgen.trans ?_
    rw [Subgroup.closure_le]
    have hx₁ : x₁ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    have hx₃ : x₃ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    rintro y (rfl | rfl | rfl)
    · exact hx₁
    · rw [hx₂]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx₃ 2) hx₁
    · exact hx₃
end Frame
end T7C2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C2
open CFSG.ClassicalInvolution.Asc77.T7C2
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem genLE_four_of_le_MGrp [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) {H : Subgroup G} (hH : H ≤ (S : Subgroup G)) :
    GenLE H 4 := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hW : W ∈ WSet Ω := hd.hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨a, b, ha, hb, hgen⟩ := exists_two_gen_W hs hd h8
  obtain ⟨e⟩ := hd.hS4
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    hSM.trans (Thompson.MGrp_le_normalizer Ω W)
  let ι : ↥(S : Subgroup G) →* ↥(Subgroup.normalizer (W : Set G)) := Subgroup.inclusion hSN
  have hψ : ∀ x : ↥(S : Subgroup G), (Thompson.piN W).comp ι x ∈ muGroup Ω W := by
    intro x
    have h1 : (Thompson.piN W).comp ι x = Thompson.piG W (x : G) :=
      (Thompson.piG_of_mem (hSN x.2)).symm
    rw [h1]
    exact Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (hSM x.2))
  let ψ : ↥(S : Subgroup G) →* ↥(muGroup Ω W) :=
    ((Thompson.piN W).comp ι).codRestrict (muGroup Ω W) hψ
  let φ : ↥(S : Subgroup G) →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp ψ
  have hker : φ.ker ≤ W.subgroupOf (S : Subgroup G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ψ x = 1 := e.injective (hx.trans (map_one e).symm)
    have h2 : Thompson.piN W (ι x) = 1 := congrArg Subtype.val h1
    have h3 : ((ι x : ↥(Subgroup.normalizer (W : Set G))) : G) ∈ W ⊔ OCW W :=
      (Thompson.piN_eq_one_iff W (ι x)).mp h2
    rw [Subgroup.mem_subgroupOf]
    exact Thompson.inf_sup_OCW_le (Thompson.isPGroup_of_mem_WSet hW) S.isPGroup' ⟨x.2, h3⟩
  have hA : ∀ B : Subgroup ↥(S : Subgroup G), B ≤ W.subgroupOf (S : Subgroup G) →
      GenLE B 2 := by
    intro B hB
    apply GenLE.of_map_injective (Subgroup.subtype_injective (S : Subgroup G))
    refine genLE_two_of_closure_pair ha hb (hWab a ha b hb) hgen ?_
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB hx)
  have h4 := genLE_four_of_ker S.isPGroup' φ (W.subgroupOf (S : Subgroup G)) hA hker
    (H.subgroupOf (S : Subgroup G))
  exact GenLE.of_subgroupOf hH h4

theorem twoSubgroupsFourGenerated_of_le_MGrp [IsSimpleGroup G] {K K' W : Subgroup G}
    {S : Sylow 2 G} {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) : TwoSubgroupsFourGenerated G := by
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow Q S
  have hle : conjSub g P ≤ (S : Subgroup G) := hg ▸ conjSub_mono hPQ
  have h4 := GenLE.conj (genLE_four_of_le_MGrp hs hd h8 hSM hle) g⁻¹
  have hP' : (conjSub g P).map (MulAut.conj g⁻¹).toMonoidHom = P := conjSub_inv_conjSub g P
  rw [hP'] at h4
  exact h4
end Main
end T7C2

theorem T7C2.c24_5_proved : C24_5 := by
  intro G _ _ _ Ω K K' W S R R' z u hyp h8
  by_cases hSM : (S : Subgroup G) ≤ MGrp Ω W
  · exact Or.inr (Or.inr (T7C2.twoSubgroupsFourGenerated_of_le_MGrp hyp.std.setting hyp.data h8
      hSM))
  · exact Or.inl hSM

@[expose] def C24_9_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 → ¬ (S : Subgroup G) ≤ MGrp Ω W → False
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7X
open CFSG.ClassicalInvolution.Asc77.T7X
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

structure Frame24 (Ω : Set (Subgroup G)) (W : Subgroup G) : Type where
  c : Q3CL.Thompson.Ctx Ω W
  F : T7E.Frame4 Ω W
  φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)
  hφ : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (φ x).IsSwap
  hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ'
  hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ
  hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ
  x₁ : G
  x₂ : G
  x₃ : G
  m : ℕ
  hm : 0 < m
  h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W
  h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W
  h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W
  r₁ : F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹
  r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂
  r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁
  t₁ : F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁
  t₂ : F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹
  t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂
  s₁ : F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃
  s₂ : F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃
  s₃ : F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹
  o₁ : orderOf x₁ = 4 * m
  o₂ : orderOf x₂ = 4 * m
  o₃ : orderOf x₃ = 4 * m
  z₁ : x₁ ^ (2 * m) = F.z
  z₂ : x₂ ^ (2 * m) = F.z
  z₃ : x₃ ^ (2 * m) = F.j
  hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G)

theorem exists_frame24 [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) :
    ∃ D : Frame24 Ω W, D.F.ρ.K = K ∧ D.F.ρ'.K = K' ∧ D.F.ρ.R = R ∧ D.F.ρ'.R = R' ∧
      D.F.z = z := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, hFK, hFK', hFR, hFR', hFz, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  refine ⟨{
    c := c, F := F, φ := e, hφ := he, hab := hab, hcomm := hcomm, hac := hac,
    x₁ := x₁, x₂ := x₂, x₃ := x₃, m := m, hm := hm, h₁ := h₁, h₂ := h₂, h₃ := h₃,
    r₁ := r₁, r₂ := r₂, r₃ := r₃, t₁ := t₁, t₂ := t₂, t₃ := t₃, s₁ := s₁, s₂ := s₂, s₃ := s₃,
    o₁ := o₁, o₂ := o₂, o₃ := o₃, z₁ := z₁, z₂ := z₂, z₃ := z₃,
    hgen := F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃ },
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals assumption
end Frame
end T7X
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B

@[expose] def H3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting Ω K K' z → Hyp24Data Ω K K' W S R R' z u → Nat.card ↥R = 8 →
    ∀ D : T7X.Frame24 Ω W, D.F.ρ.K = K → D.F.ρ'.K = K' → D.F.ρ.R = R → D.F.ρ'.R = R' →
      ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
        R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ D.F.ρ₃.K →
        T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1

@[expose] def NoGraph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting Ω K K' z → Hyp24Data Ω K K' W S R R' z u → Nat.card ↥R = 8 →
      ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G)
end S24B
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7X
open CFSG.ClassicalInvolution.Asc77.T7X
namespace Frame24
open CFSG.ClassicalInvolution.Asc77.T7X.Frame24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : Asc77.T7X.Frame24 Ω W)
omit [Finite G] in

theorem x₁_mem : D.x₁ ∈ W := (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).2
omit [Finite G] in

theorem x₂_mem : D.x₂ ∈ W := (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).2
omit [Finite G] in

theorem x₃_mem : D.x₃ ∈ W := (D.h₃ ▸ Subgroup.mem_zpowers D.x₃ : D.x₃ ∈ D.F.ρ₃.R ⊓ W).2

theorem comm12 : Commute D.x₁ D.x₂ :=
  Q3CL.Thompson.commutes_of_mem_WSet D.c.hΩ D.c.hW D.x₁ D.x₁_mem D.x₂ D.x₂_mem

theorem comm13 : Commute D.x₁ D.x₃ :=
  Q3CL.Thompson.commutes_of_mem_WSet D.c.hΩ D.c.hW D.x₁ D.x₁_mem D.x₃ D.x₃_mem

theorem comm23 : Commute D.x₂ D.x₃ :=
  Q3CL.Thompson.commutes_of_mem_WSet D.c.hΩ D.c.hW D.x₂ D.x₂_mem D.x₃ D.x₃_mem
omit [Finite G] in

theorem pow₂ : D.x₂ ^ (4 * D.m) = 1 := by simpa [D.o₂] using pow_orderOf_eq_one D.x₂
omit [Finite G] in

theorem pow₃ : D.x₃ ^ (4 * D.m) = 1 := by simpa [D.o₃] using pow_orderOf_eq_one D.x₃
omit [Finite G] in

theorem z_eq : D.x₁ ^ (2 * D.m) = D.x₂ ^ (2 * D.m) := D.z₁.trans D.z₂.symm
omit [Finite G] in

theorem zpow_four {x : G} (hx : x ^ (4 * D.m) = 1) (a : ℤ) : x ^ (a + 4 * (D.m : ℤ)) = x ^ a := by
  have h4 : x ^ (4 * (D.m : ℤ)) = 1 := by exact_mod_cast hx
  rw [zpow_add, h4, mul_one]
omit [Finite G] in

theorem zpow_shift {x : G} (hx : x ^ (4 * D.m) = 1) {a b : ℤ} (h : a + 4 * (D.m : ℤ) = b) :
    x ^ a = x ^ b := by
  rw [← h, zpow_four D hx]

theorem eps_pow_eq (D : Frame24 Ω W) :
    (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m =
      D.x₁ ^ (D.m : ℤ) * D.x₂ ^ (-(D.m : ℤ)) * D.x₃ ^ (2 * (D.m : ℤ)) := by
  rw [← zpow_natCast, A3Mod.pow_triple D.comm12 D.comm13 D.comm23]

theorem eps_pow_fixed_r :
    D.F.ρ.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_r D.comm12 D.comm13 D.r₁ D.r₂ D.r₃]
  have h : 2 * (D.m : ℤ) - (D.m : ℤ) = (D.m : ℤ) := by ring
  rw [h]

theorem eps_pow_fixed_t :
    D.F.ρ'.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ'.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_t D.comm23 D.t₁ D.t₂ D.t₃]
  have h : D.x₂ ^ (2 * (D.m : ℤ) - -(D.m : ℤ)) = D.x₂ ^ (-(D.m : ℤ)) :=
    (D.zpow_shift D.pow₂ (a := -(D.m : ℤ)) (b := 2 * (D.m : ℤ) - -(D.m : ℤ)) (by ring)).symm
  rw [h]

theorem eps_pow_fixed_s :
    D.F.ρ₃.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ₃.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_s D.comm13 D.comm23 D.s₁ D.s₂ D.s₃]
  have h : D.x₃ ^ ((D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ)) = D.x₃ ^ (2 * (D.m : ℤ)) :=
    D.zpow_shift D.pow₃ (a := (D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ)) (b := 2 * (D.m : ℤ))
      (by ring)
  rw [h]

theorem eps_pow_eq_one (hZ : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m = 1 := by
  have hεW : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ W :=
    W.pow_mem (W.mul_mem (W.mul_mem D.x₁_mem (W.inv_mem D.x₂_mem)) (W.pow_mem D.x₃_mem 2)) _
  have hfix : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * r⁻¹ = (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m :=
    fun R₀ hR₀ r hr => T7C2.fixed_of_frame D.c D.hφ D.F D.hab D.hcomm D.hac hεW
      D.eps_pow_fixed_r D.eps_pow_fixed_t D.eps_pow_fixed_s hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ = (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hfW : n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr hεW
    have hfixc : ∀ σ : Thompson.Rep Ω W,
        σ.r * (n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹) * σ.r⁻¹ =
          n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ := by
      intro σ
      have hmemD : n⁻¹ * σ.r * n ∈ conjSub n⁻¹ σ.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ.r * n) * n⁻¹ = σ.r := by group
        rw [h1]
        exact σ.hr
      have := hfix _ (Q3CL.Thompson.conjSub_mem_D D.c.hΩ σ.hR hn') _ hmemD
      calc σ.r * (n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹) * σ.r⁻¹
          = n * ((n⁻¹ * σ.r * n) * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m *
              (n⁻¹ * σ.r * n)⁻¹) * n⁻¹ := by group
        _ = n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ := by rw [this]
    rcases A3Mod.fixed_eq_one_or D.comm12 D.comm13 D.comm23 D.o₁ D.o₂ D.o₃ D.z_eq D.r₁ D.r₂ D.r₃
        D.t₁ D.t₂ D.t₃ D.s₁ D.s₂ D.s₃ (D.hgen hfW) (hfixc D.F.ρ) (hfixc D.F.ρ') (hfixc D.F.ρ₃)
      with h | h
    · have h0 : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m = 1 := conj_eq_one_iff.mp h
      rw [h0]
      group
    · exact h
  have hmemC : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ Asc77.centerIn (Subgroup.normalizer (W : Set G))
      :=
    T7C2.mem_centerIn_of_forall (Subgroup.le_normalizer hεW) hcent
  have hmem : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set
      G)) :=
    ⟨hεW, hmemC⟩
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem
end Frame24
end T7X
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure Ctx8 (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  hs : Hyp23Setting Ω K K' z
  hd : Hyp24Data Ω K K' W S R R' z u
  h8 : Nat.card ↥R = 8
  D : T7X.Frame24 Ω W
  hK : D.F.ρ.K = K
  hK' : D.F.ρ'.K = K'
  hR : D.F.ρ.R = R
  hR' : D.F.ρ'.R = R'
  hz : D.F.z = z

theorem Ctx8.nonempty [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    Nonempty (Ctx8 Ω K K' W S R R' z u) := by
  obtain ⟨D, hK, hK', hR, hR', hz⟩ := T7X.exists_frame24 hs hd
  exact ⟨⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩⟩
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)

theorem m_eq_one : C.D.m = 1 := by
  have h1 := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
  have h2 : Nat.card ↥(C.D.F.ρ.R ⊓ W) = 4 * C.D.m := by
    rw [← C.D.h₁, Nat.card_zpowers, C.D.o₁]
  have h3 : Nat.card ↥C.D.F.ρ.R = 8 := by rw [C.hR]; exact C.h8
  omega

theorem orderOf_x₁ : orderOf C.D.x₁ = 4 := by rw [C.D.o₁, C.m_eq_one]

theorem orderOf_x₂ : orderOf C.D.x₂ = 4 := by rw [C.D.o₂, C.m_eq_one]

theorem x₁_sq : C.D.x₁ ^ 2 = z := by
  have h := C.D.z₁
  rw [C.m_eq_one, C.hz] at h
  simpa using h

theorem x₂_sq : C.D.x₂ ^ 2 = z := by
  have h := C.D.z₂
  rw [C.m_eq_one, C.hz] at h
  simpa using h

theorem x₃_sq : C.D.x₃ ^ 2 = C.D.F.j := by
  have h := C.D.z₃
  rw [C.m_eq_one] at h
  simpa using h

theorem eps_eq_one : C.D.x₁ * C.D.x₂⁻¹ * C.D.x₃ ^ 2 = 1 := by
  have h := C.D.eps_pow_eq_one C.hd.hZ
  rw [C.m_eq_one, pow_one] at h
  exact h

theorem x₂_eq : C.D.x₂ = C.D.x₁ * C.D.x₃ ^ 2 := by
  have h := C.eps_eq_one
  have hc : Commute C.D.x₂⁻¹ (C.D.x₃ ^ 2) := (C.D.comm23.pow_right 2).inv_left
  calc C.D.x₂ = C.D.x₂ * (C.D.x₁ * C.D.x₂⁻¹ * C.D.x₃ ^ 2) := by rw [h, mul_one]
    _ = C.D.x₂ * C.D.x₁ * (C.D.x₂⁻¹ * C.D.x₃ ^ 2) := by group
    _ = C.D.x₂ * C.D.x₁ * (C.D.x₃ ^ 2 * C.D.x₂⁻¹) := by rw [hc.eq]
    _ = C.D.x₂ * C.D.x₁ * C.D.x₃ ^ 2 * C.D.x₂⁻¹ := by group
    _ = C.D.x₁ * C.D.x₃ ^ 2 := by
      rw [show C.D.x₂ * C.D.x₁ = C.D.x₁ * C.D.x₂ from C.D.comm12.eq.symm]
      have hc2 : Commute C.D.x₂ (C.D.x₃ ^ 2) := C.D.comm23.pow_right 2
      calc C.D.x₁ * C.D.x₂ * C.D.x₃ ^ 2 * C.D.x₂⁻¹
          = C.D.x₁ * (C.D.x₂ * C.D.x₃ ^ 2) * C.D.x₂⁻¹ := by group
        _ = C.D.x₁ * (C.D.x₃ ^ 2 * C.D.x₂) * C.D.x₂⁻¹ := by rw [hc2.eq]
        _ = C.D.x₁ * C.D.x₃ ^ 2 := by group

theorem j_eq : C.D.F.j = C.D.x₁⁻¹ * C.D.x₂ := by
  rw [← C.x₃_sq, C.x₂_eq]
  group

theorem x₁_mem_R : C.D.x₁ ∈ R :=
  (congrArg (fun X => C.D.x₁ ∈ X) C.hR).mp
    (C.D.h₁ ▸ Subgroup.mem_zpowers C.D.x₁ : C.D.x₁ ∈ C.D.F.ρ.R ⊓ W).1

theorem x₂_mem_R' : C.D.x₂ ∈ R' :=
  (congrArg (fun X => C.D.x₂ ∈ X) C.hR').mp
    (C.D.h₂ ▸ Subgroup.mem_zpowers C.D.x₂ : C.D.x₂ ∈ C.D.F.ρ'.R ⊓ W).1

theorem x₃_mem_R₃ : C.D.x₃ ∈ C.D.F.ρ₃.R :=
  (C.D.h₃ ▸ Subgroup.mem_zpowers C.D.x₃ : C.D.x₃ ∈ C.D.F.ρ₃.R ⊓ W).1

theorem x₁_mem_K : C.D.x₁ ∈ K := C.hd.hR.2.1 C.x₁_mem_R

theorem x₂_mem_K' : C.D.x₂ ∈ K' := C.hd.hR'.2.1 C.x₂_mem_R'

theorem x₃_mem_J : C.D.x₃ ∈ C.D.F.ρ₃.K := C.D.F.ρ₃.hRK.1 C.x₃_mem_R₃

theorem j_mem_sup : C.D.F.j ∈ K ⊔ K' := by
  rw [C.j_eq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left C.x₁_mem_K))
    (Subgroup.mem_sup_right C.x₂_mem_K')
include C in

theorem hzK : IsUniqueInvolution K z := C.hs.hz
include C in

theorem hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'

theorem hjJ : IsUniqueInvolution C.D.F.ρ₃.K C.D.F.j := C.D.F.hj

theorem z_ne_j : z ≠ C.D.F.j := by
  intro h
  have hJ : C.D.F.ρ₃.K ∈ twinSet Ω K := ⟨C.D.F.ρ₃.hK, z, C.hzK,
    (congrArg (IsUniqueInvolution C.D.F.ρ₃.K) h).mpr C.hjJ⟩
  rw [C.hs.twinSet_eq] at hJ
  rcases hJ with hJ | hJ
  · exact C.D.F.hne₁ (C.hK.trans hJ.symm)
  · exact C.D.F.hne₂ (C.hK'.trans hJ.symm)

theorem r_mem_R : C.D.F.ρ.r ∈ R := (congrArg (fun X => C.D.F.ρ.r ∈ X) C.hR).mp C.D.F.ρ.hr

theorem t_mem_R' : C.D.F.ρ'.r ∈ R' := (congrArg (fun X => C.D.F.ρ'.r ∈ X) C.hR').mp C.D.F.ρ'.hr

include C in

theorem R_ne_R' : R ≠ R' := by
  intro h
  have hst := C.hs.stand
  have h2 := hst.hyp.card_le_two_of_le_inf hst.mem C.hs.hK'.1 C.hs.hne.symm
    (C.D.F.ρ.hRK.2.1.to_le (le_of_eq C.hR.symm)) C.hd.hR.2.1 (h ▸ C.hd.hR'.2.1)
  rw [C.h8] at h2
  omega
include C in

theorem commutes_R_R' : Commutes R R' :=
  l6_7_proved G Ω C.hs.stand.hyp S R C.hd.hR.1 R' C.hd.hR'.1
    C.hd.hR.2.2 C.hd.hR'.2.2 C.R_ne_R'

end Ctx8
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
