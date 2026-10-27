module

public import CFSG.ClassicalInvolution.Q3.TL3T27

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_pSpan_of_comm {p : ℕ} [Fact p.Prime] {S : Set (Subgroup G)}
    (hp : ∀ L ∈ S, IsPGroup p L)
    (hc : ∀ L ∈ S, ∀ L' ∈ S, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) :
    IsPGroup p (pSpan S) := by
  set T := pSpan S with hT
  obtain ⟨S'⟩ : Nonempty (Sylow p ↥T) := inferInstance
  have hle : ∀ L ∈ S, L.subgroupOf T ≤ (S' : Subgroup ↥T) := by
    intro L hL
    have hLT : L ≤ T := le_pSpan hL
    have hTN : T ≤ Subgroup.normalizer (L : Set G) := pSpan_le fun L' hL' => by
      by_cases h : L' = L
      · rw [h]
        exact Subgroup.le_normalizer
      · exact le_normalizer_of_comm (hc L' hL' L hL h)
    have hN : (L.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff hLT).mpr
      fun l t hl ht => (Subgroup.mem_normalizer_iff.mp (hTN ht) l).mp hl
    have hpL : IsPGroup p ↥(L.subgroupOf T) :=
      (hp L hL).of_equiv (Subgroup.subgroupOfEquivOfLe hLT).symm
    exact hpL.le_sylow_of_normal S'
  have htop : T ≤ (S' : Subgroup ↥T).map T.subtype := pSpan_le fun L hL x hx =>
    ⟨⟨x, le_pSpan hL hx⟩, hle L hL (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  intro x
  obtain ⟨y, hy, hyx⟩ := htop x.2
  obtain ⟨k, hk⟩ := S'.isPGroup' ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have e : (y : ↥T) = x := Subtype.ext hyx
  have := congrArg (fun w : ↥(S' : Subgroup ↥T) => ((w : ↥T) : G)) hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [Subgroup.coe_pow, ← e]
  exact this

theorem comm_of_mem_oddCoreImg {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ L ∈ Ω, IsPGroup 2 L)
    (hQ : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    ∀ r ∈ oddCoreImg (pSpan P), ∀ y ∈ pSpan P, r * y = y * r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := pSpan P with hH
  set R := oddCoreImg H with hR
  have hRH : R ≤ H := oddCoreImg_le H
  have hRodd : Odd (Nat.card R) := odd_natCard_oddCoreImg H
  have hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := fun h hh r hr =>
    conj_mem_oddCoreImg (Subgroup.le_normalizer hh) hr
  have hR2 : ∀ c ∈ R, (∃ k : ℕ, c ^ 2 ^ k = 1) → c = 1 := by
    intro c hc ⟨k, hk⟩
    have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2' : orderOf c ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥R)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : Nat.Coprime (2 ^ k) (Nat.card R) := Nat.Coprime.pow_left k
      ((Nat.coprime_two_left).mpr hRodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2')
  have hcent : ∀ L ∈ P, ∀ r ∈ R, ∀ l ∈ L, r * l = l * r := by
    intro L hL r hr
    have hLΩ := hPΩ hL
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 L hLΩ
    have hRz : ∀ s ∈ R, s * z = z * s := by
      intro s hs
      obtain ⟨Q, hQn, hQ2, hzQ⟩ := hQ L hLΩ z hz
      set c := s * z * s⁻¹ * z⁻¹ with hc
      have hcR : c ∈ R := by
        have h1 : z * s⁻¹ * z⁻¹ ∈ R := hRn z (le_pSpan hL hz.mem) _ (R.inv_mem hs)
        have : c = s * (z * s⁻¹ * z⁻¹) := by rw [hc]; group
        rw [this]
        exact R.mul_mem hs h1
      have hcQ : c ∈ Q := Q.mul_mem (hQn.conj_mem z hzQ s) (Q.inv_mem hzQ)
      obtain ⟨k, hk⟩ := hQ2 ⟨c, hcQ⟩
      have hc1 : c = 1 := hR2 c hcR ⟨k, by
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this⟩
      calc s * z = s * z * s⁻¹ * z⁻¹ * z * s := by group
        _ = z * s := by rw [← hc, hc1, one_mul]
    set O : Set (Subgroup G) := {M | ∃ s ∈ R, conjSub s L = M} with hO
    have hOP : ∀ M ∈ O, M ∈ P := by
      rintro M ⟨s, hs, rfl⟩
      exact hinv L hL s (hRH hs)
    have hOz : ∀ M ∈ O, IsUniqueInvolution M z := by
      rintro M ⟨s, hs, rfl⟩
      have := hz.conj s
      have e : s * z * s⁻¹ = z := by rw [hRz s hs, mul_inv_cancel_right]
      rwa [e] at this
    have hT2 : IsPGroup 2 (pSpan O) := isPGroup_pSpan_of_comm
      (fun M hM => h2 M (hPΩ (hOP M hM)))
      fun M hM M' hM' hne => twin_comm hΩ h2 (hPΩ (hOP M hM)) (hPΩ (hOP M' hM')) hne
        (hOz M hM) (hOz M' hM')
    have hOR : ∀ s ∈ R, ∀ M ∈ O, conjSub s M ∈ O := by
      rintro s hs _ ⟨t, ht, rfl⟩
      exact ⟨s * t, R.mul_mem hs ht, by rw [conjSub_mul]⟩
    have hRT : ∀ s ∈ R, ∀ t ∈ pSpan O, s * t * s⁻¹ ∈ pSpan O := by
      intro s hs t ht
      have hR' : ∀ M ∈ O, conjSub s⁻¹ M ∈ O := fun M hM => hOR s⁻¹ (R.inv_mem hs) M hM
      exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_pSpan (hOR s hs) hR') t).mp ht
    have hLO : L ∈ O := ⟨1, R.one_mem, conjSub_one L⟩
    intro l hl
    have hlT : l ∈ pSpan O := le_pSpan hLO hl
    have hlH : l ∈ H := le_pSpan hL hl
    set c := r * l * r⁻¹ * l⁻¹ with hc
    have hcR : c ∈ R := by
      have h1 : l * r⁻¹ * l⁻¹ ∈ R := hRn l hlH _ (R.inv_mem hr)
      have : c = r * (l * r⁻¹ * l⁻¹) := by rw [hc]; group
      rw [this]
      exact R.mul_mem hr h1
    have hcT : c ∈ pSpan O := (pSpan O).mul_mem (hRT r hr l hlT) ((pSpan O).inv_mem hlT)
    obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
    have hc1 : c = 1 := hR2 c hcR ⟨k, by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this⟩
    calc r * l = r * l * r⁻¹ * l⁻¹ * l * r := by group
      _ = l * r := by rw [← hc, hc1, one_mul]
  intro r hr y hy
  have hle : H ≤ Subgroup.centralizer ({r} : Set G) := pSpan_le fun L hL x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent L hL r hr x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end CFSG.ClassicalInvolution.Q3.TC.Thin
