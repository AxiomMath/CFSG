module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu
public import CFSG.ClassicalInvolution.Uniform.USylow
public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm

section FAut

variable {G : Type} [Group G] [Finite G] {K R : Subgroup G} {π : OddQuot K →* A7}
  {zE : OddQuot K}

theorem epsG_eq_neg_one_of_isFAut (cov : IsDoubleCoverA7 π zE) (hR : IsSylow2In R K) {z : G}
    (hz : IsUniqueInvolution K z) {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (ha2 : a * a = 1) (hF : IsFAut R a) : epsG cov a = -1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hε : epsG cov a = 1 := (Int.units_eq_one_or _).resolve_right hne
  obtain ⟨k, hkK, hk⟩ := exists_mem_K_nuG_eq_one_of_epsG_eq_one cov ha hε
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hkaN : k⁻¹ * a ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) ha
  have hk1 := (nuG_eq_one_iff cov hkaN).mp hk
  obtain ⟨haNR, -, Q', R₀, hQ', hQq, hR₀, hcard⟩ := hF
  have hR2 : IsPGroup 2 ↥R := hR.2.1
  have hRK : R ≤ K := hR.1
  have hR₀R : R₀ = R := (hR₀.2.2 R le_rfl hR2 hR₀.1).symm
  have hQeq : Q' = R ⊓ Subgroup.centralizer ({a} : Set G) :=
    (hQ'.2.2 (R ⊓ Subgroup.centralizer ({a} : Set G)) le_rfl (hR2.to_le inf_le_left) hQ'.1).symm
  have haR : ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun r hr => by
    have h1 := conj_mem_conjSub (n := a) hr
    rwa [mem_normalizer_iff_conjSub_eq.mp haNR] at h1
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hN
  set α : MulAut ↥K := conjOn K a ha with hα
  set ᾱ : MulAut (OddQuot K) := oddQuotAut K α with hᾱ
  set kb : OddQuot K := QuotientGroup.mk (⟨k, hkK⟩ : ↥K) with hkb
  have hconj : ∀ e : OddQuot K, ᾱ e = kb * e * kb⁻¹ := by
    intro e
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
    have h1 : oddQuotAut K (conjOn K (k⁻¹ * a) hkaN) (x : OddQuot K) = (x : OddQuot K) := by
      rw [hk1]
      rfl
    rw [oddQuotAut_mk] at h1
    have e1 : α x = (⟨k, hkK⟩ : ↥K) * (conjOn K (k⁻¹ * a) hkaN x) * (⟨k, hkK⟩ : ↥K)⁻¹ := by
      apply Subtype.ext
      show a * (x : G) * a⁻¹ = k * (k⁻¹ * a * (x : G) * (k⁻¹ * a)⁻¹) * k⁻¹
      group
    show ((α x : ↥K) : OddQuot K) = _
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
  have hᾱ2 : ᾱ * ᾱ = 1 := oddQuotAut_mul_self K (conjOn_mul_self K ha ha2)
  have hkb2 : ∀ e : OddQuot K, kb * kb * e = e * (kb * kb) := by
    intro e
    have h1 : ᾱ (ᾱ e) = e := by
      have := congrArg (fun β : MulAut (OddQuot K) => β e) hᾱ2
      simpa using this
    rw [hconj, hconj] at h1
    calc kb * kb * e = (kb * (kb * e * kb⁻¹) * kb⁻¹) * (kb * kb) := by group
      _ = e * (kb * kb) := by rw [h1]
  have hπkb2 : π (kb * kb) = 1 := by
    have hc : π (kb * kb) ∈ Subgroup.center A7 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := cov.surjective g
      rw [← map_mul, ← map_mul, hkb2]
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    exact Subgroup.mem_bot.mp hc
  have hkb4 : kb ^ 4 = 1 := by
    have e4 : kb ^ 4 = (kb * kb) * (kb * kb) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rcases (cov.ker_iff _).mp hπkb2 with h | h
    · rw [e4, h, mul_one]
    · rw [e4, h]
      exact cov.sq_eq_one
  have hP : IsPGroup 2 ↥(Subgroup.zpowers kb) := fun g => ⟨2, by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    show (g : OddQuot K) ^ (2 ^ 2) = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num
    rw [hkb4, one_zpow]⟩
  set Q : Sylow 2 ↥K := Uniform.sylowOfIsSylow2In hR with hQ
  have hQcoe : (Q : Subgroup ↥K) = R.subgroupOf K := Uniform.coe_sylowOfIsSylow2In hR
  have hmk : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  set Q₁ : Sylow 2 (OddQuot K) := Q.mapSurjective hmk with hQ₁
  have hR₁def : (Q₁ : Subgroup (OddQuot K)) = (R.subgroupOf K).map (QuotientGroup.mk' N) := by
    rw [hQ₁, Sylow.coe_mapSurjective, hQcoe]
  have hαs : ∀ s : ↥K, s ∈ R.subgroupOf K → α s ∈ R.subgroupOf K := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact haR _ hs
  have hkbN : kb ∈ Subgroup.normalizer ((Q₁ : Subgroup (OddQuot K)) : Set (OddQuot K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have hmem : ∀ e' : OddQuot K, e' ∈ (Q₁ : Subgroup (OddQuot K)) →
        ᾱ e' ∈ (Q₁ : Subgroup (OddQuot K)) := by
      intro e' he'
      rw [hR₁def] at he' ⊢
      obtain ⟨s, hs, rfl⟩ := he'
      exact ⟨α s, hαs s hs, rfl⟩
    constructor
    · intro he
      rw [← hconj]
      exact hmem e he
    · intro he
      rw [← hconj] at he
      have h1 : ᾱ (ᾱ e) = e := by
        have := congrArg (fun β : MulAut (OddQuot K) => β e) hᾱ2
        simpa using this
      rw [← h1]
      exact hmem _ he
  have hkbQ : kb ∈ (Q₁ : Subgroup (OddQuot K)) := by
    have h1 := hP.inf_normalizer_sylow Q₁
    have h2 : kb ∈ Subgroup.zpowers kb ⊓ Subgroup.normalizer (Q₁ : Set (OddQuot K)) :=
      ⟨Subgroup.mem_zpowers kb, hkbN⟩
    rw [h1] at h2
    exact h2.2
  rw [hR₁def] at hkbQ
  obtain ⟨s, hs, hsk⟩ := hkbQ
  have hS2 : IsPGroup 2 ↥(R.subgroupOf K) := Q.isPGroup'
  have hinj := Uniform.injective_mk_oddCore_of_isPGroup K hS2
  have hsfix : α s = s := by
    have h1 : ᾱ (QuotientGroup.mk' N s) = QuotientGroup.mk' N s := by
      rw [hconj]
      show kb * (QuotientGroup.mk' N s) * kb⁻¹ = _
      rw [hsk]
      group
    have h2 : (QuotientGroup.mk' N) (α s) = (QuotientGroup.mk' N) s := h1
    have h3 := @hinj ⟨α s, hαs s hs⟩ ⟨s, hs⟩ h2
    exact congrArg Subtype.val h3
  have hsR : (s : G) ∈ R := Subgroup.mem_subgroupOf.mp hs
  have hsK : (s : G) ∈ K := s.2
  have hsa : a * (s : G) * a⁻¹ = s := congrArg Subtype.val hsfix
  have hsC : (s : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (s : G) * a = (a * (s : G) * a⁻¹) * a := by rw [hsa]
        _ = a * s := by group)
  have hsQ' : (s : G) ∈ Q' := by
    rw [hQeq]
    exact ⟨hsR, hsC⟩
  have hcomm : ∀ q ∈ Q', (s : G) * q = q * s := by
    intro q hq
    rw [hQeq] at hq
    have hqR : q ∈ R := hq.1
    have hqa : q * a = a * q := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    have hqK : q ∈ K := hRK hqR
    have hq'R : (⟨q, hqK⟩ : ↥K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hqR
    have hαq : α ⟨q, hqK⟩ = ⟨q, hqK⟩ := by
      apply Subtype.ext
      show a * q * a⁻¹ = q
      calc a * q * a⁻¹ = (q * a) * a⁻¹ := by rw [hqa]
        _ = q := by group
    have h1 : ᾱ ((⟨q, hqK⟩ : ↥K) : OddQuot K) = ((⟨q, hqK⟩ : ↥K) : OddQuot K) := by
      show ((α ⟨q, hqK⟩ : ↥K) : OddQuot K) = _
      rw [hαq]
    have h2 : kb * ((⟨q, hqK⟩ : ↥K) : OddQuot K) = ((⟨q, hqK⟩ : ↥K) : OddQuot K) * kb := by
      have h5 := hconj ((⟨q, hqK⟩ : ↥K) : OddQuot K)
      rw [h1] at h5
      calc kb * ((⟨q, hqK⟩ : ↥K) : OddQuot K)
          = (kb * ((⟨q, hqK⟩ : ↥K) : OddQuot K) * kb⁻¹) * kb := by group
        _ = ((⟨q, hqK⟩ : ↥K) : OddQuot K) * kb := by rw [← h5]
    have h3 : (⟨s, hs⟩ : ↥(R.subgroupOf K)) * ⟨⟨q, hqK⟩, hq'R⟩ =
        ⟨⟨q, hqK⟩, hq'R⟩ * ⟨s, hs⟩ := by
      apply hinj
      show (QuotientGroup.mk' N) (s * ⟨q, hqK⟩) = (QuotientGroup.mk' N) (⟨q, hqK⟩ * s)
      rw [map_mul, map_mul, hsk]
      exact h2
    exact congrArg Subtype.val (congrArg Subtype.val h3)
  have hsq : (s : G) * s = 1 := hQq.sq_eq_one_of_central hsQ' hcomm
  have hsz : (s : G) = 1 ∨ (s : G) = z := hz.unique s hsK hsq
  have hscen : ∀ x ∈ K, x * (s : G) = (s : G) * x := by
    intro x hx
    rcases hsz with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      have hmem : x * z * x⁻¹ ∈ K :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hz.mem) (Subgroup.inv_mem _ hx)
      have hsq' : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
        calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
          _ = 1 := by rw [hz.sq]; group
      have hxz : x * z * x⁻¹ = z := by
        rcases hz.unique _ hmem hsq' with h1 | h1
        · exfalso
          apply hz.ne_one
          calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
            _ = 1 := by rw [h1]; group
        · exact h1
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [hxz]
  have hkbc : ∀ e : OddQuot K, kb * e = e * kb := by
    intro e
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
    have h1 : (QuotientGroup.mk' N) (s * x) = (QuotientGroup.mk' N) (x * s) := by
      rw [show s * x = x * s from Subtype.ext (hscen x x.2).symm]
    rw [map_mul, map_mul, hsk] at h1
    exact h1
  have hacen : ∀ x ∈ R, x * a = a * x := by
    intro x hxR
    have hxK : x ∈ K := hRK hxR
    have hx'R : (⟨x, hxK⟩ : ↥K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxR
    have h1 : ᾱ ((⟨x, hxK⟩ : ↥K) : OddQuot K) = ((⟨x, hxK⟩ : ↥K) : OddQuot K) := by
      rw [hconj]
      calc kb * ((⟨x, hxK⟩ : ↥K) : OddQuot K) * kb⁻¹
          = (((⟨x, hxK⟩ : ↥K) : OddQuot K) * kb) * kb⁻¹ := by
            rw [hkbc ((⟨x, hxK⟩ : ↥K) : OddQuot K)]
        _ = _ := by group
    have h2 : (QuotientGroup.mk' N) (α ⟨x, hxK⟩) = (QuotientGroup.mk' N) ⟨x, hxK⟩ := h1
    have h3 := @hinj ⟨α ⟨x, hxK⟩, hαs _ hx'R⟩ ⟨⟨x, hxK⟩, hx'R⟩ h2
    have h4 : a * x * a⁻¹ = x := congrArg Subtype.val (congrArg Subtype.val h3)
    calc x * a = (a * x * a⁻¹) * a := by rw [h4]
      _ = a * x := by group
  have hRC : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hxR =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hacen x hxR)
  have hQR : Q' = R := by
    rw [hQeq]
    exact inf_eq_left.mpr hRC
  have hpos : 0 < Nat.card ↥R := Nat.card_pos
  rw [hR₀R, hQR] at hcard
  omega

end FAut

end CFSG.ClassicalInvolution.Hat2A7S
