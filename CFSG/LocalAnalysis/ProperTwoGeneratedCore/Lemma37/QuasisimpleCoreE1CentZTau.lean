module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaRBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionTau

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem exists_mul_conj_mem_of_not_two_dvd {G : Type} [Group G] [Finite G] {H P : Subgroup G}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.relIndex H) {g : G}
    (hg : ∀ r ∈ P, g * r * g⁻¹ ∈ H) : ∃ h ∈ H, ∀ r ∈ P, h * g * r * (h * g)⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 H := IsPGroup.toSylow (P := P.subgroupOf H) hP.comap_subtype hidx
  have hD : IsPGroup 2 ((P.map (MulAut.conj g).toMonoidHom).subgroupOf H) :=
    (hP.map _).comap_subtype
  obtain ⟨k, -, hk⟩ := exists_conj_mem_sylow_of_le P' (X := ⊤) le_top le_top hD
  refine ⟨k, k.2, fun r hr => ?_⟩
  have hd : (⟨g * r * g⁻¹, hg r hr⟩ : H) ∈ (P.map (MulAut.conj g).toMonoidHom).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr ⟨r, hr, by simp [MulAut.conj_apply]⟩
  have h' : ((k * ⟨g * r * g⁻¹, hg r hr⟩ * k⁻¹ : H) : G) ∈ P := hk _ hd
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
  convert h' using 1
  group

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem mem_e1M0_of_odd {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) {k : ℕ}
    (hk : Odd k) (hgk : g ^ k = 1) : g ∈ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) :=
  mem_e1M0_of_pow_eq_one d.caseC3BCD.partC.center d.caseC3BCD.mem_iff
    (by rw [← CaseC3BCD.caseC3Word_forty (m := m) (y := y)]; exact hg) hk hgk

theorem e1RBar_le_normalizer_e1EBar : e1RBar (Subgroup.center J) u m y x ≤
    Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) :=
  d.caseC3BCD.e1RBar_le.trans d.map_le_normalizer_e1EBar

theorem centralizer_e1EBar_le_e1M0 :
    Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ≤
      e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) := by
  have hb := d.caseC3BCD
  obtain ⟨O, hOC, -, hdec, hiff, -, -⟩ := d.exists_oddCore_centralizer_e1EBar
  intro c hc
  obtain ⟨e, he, o, ho, rfl⟩ := hdec c hc
  refine (e1M0 _ _).mul_mem (hb.e1RBar_le_e1M0 (hb.e1EBar_le_e1RBar he)) ?_
  refine d.mem_e1M0_of_odd ?_ ((hiff o (hOC ho)).mp ho) (pow_orderOf_eq_one o)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hOC ho) _ hb.forty_mem_e1EBar).symm

theorem exists_of_mem_e1RBar_sup_centralizer {k : J ⧸ Subgroup.center J}
    (hk : k ∈ e1RBar (Subgroup.center J) u m y x ⊔
      Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) :
    ∃ r ∈ e1RBar (Subgroup.center J) u m y x, ∃ c ∈ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)), r * c = k := by
  have hle : e1RBar (Subgroup.center J) u m y x ≤ Subgroup.normalizer
      (Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) :
        Set (J ⧸ Subgroup.center J)) := fun r hr =>
    mem_normalizer_of_forall_conj_mem fun c hc =>
      conj_mem_centralizer_of_mem_normalizer (d.e1RBar_le_normalizer_e1EBar hr) hc
  have h : k ∈ ((e1RBar (Subgroup.center J) u m y x ⊔ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) :
        Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J)) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at h
  obtain ⟨r, hr, c, hc, hrc⟩ := h
  exact ⟨r, hr, c, hc, hrc⟩

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem exists_mem_e1NBar_not_mem_e1KBar :
    ∃ g ∈ e1NBar (Subgroup.center J) u m y x,
      g ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ∧
      g ∉ e1KBar (Subgroup.center J) u m y x := by
  have hb := d.caseC3BCD
  obtain ⟨τ, hτN, ⟨a, hτa⟩, -, hτmove⟩ := d.exists_tau htype
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set R := e1RBar (Subgroup.center J) u m y x with hR
  set C := Subgroup.centralizer (E : Set (J ⧸ Subgroup.center J)) with hC
  set zb := caseC3Word (Subgroup.center J) u m y x 40 with hzb
  have hτz : τ * zb * τ⁻¹ = zb :=
    conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hτN)
  have hτM := d.mem_e1M0_of_odd (d.normalizer_e1EBar_le hτN) (Odd.pow (by decide : Odd 3)) hτa
  have hHM : R ⊔ C ≤ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) :=
    sup_le hb.e1RBar_le_e1M0 d.centralizer_e1EBar_le_e1M0
  have hidx : ¬ 2 ∣ R.relIndex (R ⊔ C) := fun h2 => hb.not_two_dvd_relIndex S rfl
    (dvd_trans h2 (Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHM)))
  have hτR : ∀ r ∈ R, τ * r * τ⁻¹ ∈ R ⊔ C := by
    intro r hr
    have hn : τ * r * τ⁻¹ ∈ Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hτN (d.e1RBar_le_normalizer_e1EBar hr))
        (Subgroup.inv_mem _ hτN)
    obtain ⟨r', hr', hc⟩ := d.exists_mem_e1RBar_of_conj_mod_forty hn fun s hs => by
      have ht : τ⁻¹ * s * τ ∈ E := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hτN) s).mp hs
        rwa [inv_inv] at h
      rw [show τ * r * τ⁻¹ * s * (τ * r * τ⁻¹)⁻¹ = τ * (r * (τ⁻¹ * s * τ) * r⁻¹) * τ⁻¹ by group]
      rcases hb.conj_of_mem_e1RBar hr (hb.e1EBar_le_e1RBar ht) with h | h <;> rw [h]
      · left
        group
      · right
        rw [show τ * (τ⁻¹ * s * τ * zb) * τ⁻¹ = s * (τ * zb * τ⁻¹) by group, hτz]
    rw [show τ * r * τ⁻¹ = r' * (r'⁻¹ * (τ * r * τ⁻¹)) by group]
    exact Subgroup.mul_mem_sup hr' hc
  obtain ⟨h, hhH, hh⟩ := exists_mul_conj_mem_of_not_two_dvd hb.isPGroup_e1RBar hidx hτR
  have hhN : h ∈ Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) :=
    sup_le d.e1RBar_le_normalizer_e1EBar (Subgroup.centralizer_le_normalizer _) hhH
  refine ⟨h * τ, ⟨(e1M0 _ _).mul_mem (hHM hhH) hτM, mem_normalizer_of_forall_conj_mem hh⟩,
    Subgroup.mul_mem _ hhN hτN, fun hK => ?_⟩
  obtain ⟨-, hK'⟩ := (hb.mem_e1KBar_iff S rfl).mp hK
  obtain ⟨huE, -, -⟩ := d.mem_e1EBar_gens
  have huz : (u : J ⧸ Subgroup.center J) ≠ zb := by
    rw [hzb, ← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y)
      (x := x), Ne, hb.caseC3Word_inj]
    decide
  obtain ⟨hne1, hne2⟩ := hτmove _ huE hb.mk_ne_one.1 huz
  obtain ⟨r₀, hr₀, c₀, hc₀, rfl⟩ := d.exists_of_mem_e1RBar_sup_centralizer hhH
  have htE : τ * u * τ⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hτN _).mp huE
  have hzz : zb * zb = 1 := hb.forty_mul_self
  have key : r₀ * c₀ * τ * (u : J ⧸ Subgroup.center J) * (r₀ * c₀ * τ)⁻¹ =
      r₀ * c₀ * (τ * u * τ⁻¹) * (r₀ * c₀)⁻¹ := by group
  rcases hK' _ (hb.e1EBar_le_e1RBar huE) with h1 | h1 <;> rw [key] at h1 <;>
    rcases d.conj_mod_forty_of_mem_e1RBar hr₀ hc₀ htE with h2 | h2 <;> rw [h2] at h1
  · exact hne1 h1
  · refine hne2 ?_
    calc τ * (u : J ⧸ Subgroup.center J) * τ⁻¹ =
          τ * u * τ⁻¹ * caseC3Word (Subgroup.center J) u m y x 40 *
            caseC3Word (Subgroup.center J) u m y x 40 := by rw [mul_assoc _ _ zb, hzz, mul_one]
      _ = u * zb := by rw [h1]
  · exact hne2 h1
  · exact hne1 (mul_right_cancel h1)

theorem relIndex_e1KBar_eq_three :
    (e1KBar (Subgroup.center J) u m y x).relIndex (e1NBar (Subgroup.center J) u m y x) = 3 := by
  obtain ⟨g, hgN, -, hgK⟩ := d.exists_mem_e1NBar_not_mem_e1KBar htype
  rcases (Nat.dvd_prime Nat.prime_three).mp
      (d.caseC3BCD.relIndex_e1KBar_dvd_three htype S rfl) with h | h
  · exact absurd (Subgroup.relIndex_eq_one.mp h hgN) hgK
  · exact h

theorem pow_three_mem_e1KBar {n : J ⧸ Subgroup.center J}
    (hn : n ∈ e1NBar (Subgroup.center J) u m y x) : n ^ 3 ∈ e1KBar (Subgroup.center J) u m y x := by
  have := d.caseC3BCD.normal_e1KBar S rfl
  have hpow := Subgroup.pow_index_mem
    ((e1KBar (Subgroup.center J) u m y x).subgroupOf (e1NBar (Subgroup.center J) u m y x)) ⟨n, hn⟩
  rw [show ((e1KBar (Subgroup.center J) u m y x).subgroupOf
      (e1NBar (Subgroup.center J) u m y x)).index = 3 from d.relIndex_e1KBar_eq_three htype,
    Subgroup.mem_subgroupOf] at hpow
  simpa using hpow

theorem exists_tau_e1NBar :
    ∃ τ ∈ e1NBar (Subgroup.center J) u m y x,
      τ ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ∧
      (∃ a : ℕ, τ ^ 3 ^ a = 1) ∧ τ ∉ e1KBar (Subgroup.center J) u m y x ∧
      (∀ s ∈ e1RBar (Subgroup.center J) u m y x, s ≠ 1 →
        s ≠ caseC3Word (Subgroup.center J) u m y x 40 →
          τ * s * τ⁻¹ ≠ s ∧ τ * s * τ⁻¹ ≠ s * caseC3Word (Subgroup.center J) u m y x 40) ∧
      ∀ s ∈ e1RBar (Subgroup.center J) u m y x, τ ^ 3 * s = s * τ ^ 3 := by
  have hb := d.caseC3BCD
  obtain ⟨g, hgN, hgE, hgK⟩ := d.exists_mem_e1NBar_not_mem_e1KBar htype
  obtain ⟨a, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hτa : (g ^ r) ^ 3 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
  have hτN : g ^ r ∈ e1NBar (Subgroup.center J) u m y x := Subgroup.pow_mem _ hgN r
  have hτK : g ^ r ∉ e1KBar (Subgroup.center J) u m y x := by
    intro hτ
    have hcop : Nat.Coprime r 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
    obtain ⟨α, β, hαβ⟩ : IsCoprime ((r : ℕ) : ℤ) ((3 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (r : ℤ) * α + ((3 : ℕ) : ℤ) * β = 1 := by linear_combination hαβ
    have hg : g = (g ^ r) ^ α * (g ^ 3) ^ β :=
      calc g = g ^ ((r : ℤ) * α + ((3 : ℕ) : ℤ) * β) := by rw [h1, zpow_one]
        _ = (g ^ r) ^ α * (g ^ 3) ^ β := by
            rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact hgK (hg ▸ Subgroup.mul_mem _ (Subgroup.zpow_mem _ hτ α)
      (Subgroup.zpow_mem _ (d.pow_three_mem_e1KBar htype hgN) β))
  refine ⟨g ^ r, hτN, Subgroup.pow_mem _ hgE r, ⟨a, hτa⟩, hτK,
    fun s hs hs1 hsz => hb.conj_ne_of_not_mem_e1KBar_typeD htype S rfl hτN hτK hs hs1 hsz, ?_⟩
  exact hb.commute_pow_three_of_odd_typeD htype S rfl (Odd.pow (by decide : Odd 3)) hτa
    (CaseC3BCD.conj_mem_of_mem_e1NBar hτN)

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
