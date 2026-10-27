module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25MixF
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77 Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {K R : Subgroup G}

theorem four_le_card_inf_centralizer (hw : A7Witness K)
    (hR : IsSylow2In R K) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1)
    (hRa : ∀ r ∈ R, a * r * a⁻¹ ∈ R) :
    4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨π, zE, cov, -⟩ := exists_cover_of_witness hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hN
  set α : MulAut ↥K := conjOn K a ha with hα
  set ᾱ : MulAut (OddQuot K) := oddQuotAut K α with hᾱ
  have hαα : α * α = 1 := conjOn_mul_self K ha ha2
  have hᾱᾱ : ᾱ * ᾱ = 1 := oddQuotAut_mul_self K hαα
  set σ : Perm (Fin 7) := cov.autPerm ᾱ with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul, hᾱᾱ, map_one]
  set Q : Sylow 2 ↥K := Uniform.sylowOfIsSylow2In hR with hQ
  have hQcoe : (Q : Subgroup ↥K) = R.subgroupOf K := Uniform.coe_sylowOfIsSylow2In hR
  have hmk : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  set Q₁ : Sylow 2 (OddQuot K) := Q.mapSurjective hmk with hQ₁
  set Q₂ : Sylow 2 A7 := Q₁.mapSurjective cov.surjective with hQ₂
  set R₁ : Subgroup (OddQuot K) := (Q₁ : Subgroup (OddQuot K)) with hR₁
  set D : Subgroup A7 := (Q₂ : Subgroup A7) with hD
  have hR₁def : R₁ = (R.subgroupOf K).map (QuotientGroup.mk' N) := by
    rw [hR₁, hQ₁, Sylow.coe_mapSurjective, hQcoe]
  have hDdef : D = R₁.map π := by rw [hD, hQ₂, Sylow.coe_mapSurjective]
  have hR₁card : Nat.card R₁ = 16 := by
    rw [hR₁, Sylow.card_eq_multiplicity Q₁, cov.card_E, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have hDcard : Nat.card D = 8 := by
    rw [hD, Sylow.card_eq_multiplicity Q₂, card_A7, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have hαs : ∀ s : ↥K, s ∈ R.subgroupOf K → α s ∈ R.subgroupOf K := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hRa _ hs
  have hN : ∀ d ∈ D, ∃ d' ∈ D, (d' : Perm (Fin 7)) = σ * d * σ⁻¹ := by
    intro d hd
    rw [hDdef] at hd
    obtain ⟨x, hxR₁, rfl⟩ := hd
    rw [hR₁def] at hxR₁
    obtain ⟨s, hs, rfl⟩ := hxR₁
    refine ⟨π (ᾱ ((QuotientGroup.mk' N) s)), ?_, cov.autPerm_spec ᾱ _⟩
    rw [hDdef, hR₁def]
    exact ⟨ᾱ ((QuotientGroup.mk' N) s), ⟨α s, hαs s hs, rfl⟩, rfl⟩
  have h4 := four_le_card_of_normalizes hDcard hσ2 hN
  set C : Subgroup A7 := D ⊓ evenCentralizer σ with hC
  let ρ' : ↥R₁ →* ↥D := (π.comp R₁.subtype).codRestrict D (fun x => by
    rw [hDdef]
    exact ⟨x.1, x.2, rfl⟩)
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨d, hd⟩
    rw [hDdef] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card ρ'.ker = 2 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ'
    rw [MonoidHom.range_eq_top_of_surjective ρ' hρ', Subgroup.card_top, hR₁card, hDcard] at h1
    omega
  set C' : Subgroup ↥D := C.subgroupOf D with hC'
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ D)).toEquiv
  have hcomap := QuaternionStructure.natCard_comap_eq ρ' hρ' C'
  rw [hker, hC'card] at hcomap
  set H₀ : Subgroup ↥R₁ := C'.comap ρ' with hH₀
  set HE : Subgroup (OddQuot K) := H₀.map R₁.subtype with hHE
  have hHEcard : 8 ≤ Nat.card HE := by
    rw [hHE, Subgroup.card_map_of_injective R₁.subtype_injective, hcomap]
    omega
  have hHE_fix : ∀ x ∈ HE, π (ᾱ x) = π x := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (ρ' y : A7) ∈ C := hy
    exact cov.map_apply_eq_of_mem_evenCentralizer ᾱ hy'.2
  have hfixcard := cov.card_le_two_mul_card_fixedIn ᾱ HE hHE_fix
  set T : Subgroup ↥K := (R ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf K with hT
  have hS2 : IsPGroup 2 ↥(R.subgroupOf K) := Q.isPGroup'
  have hinj := Uniform.injective_mk_oddCore_of_isPGroup K hS2
  have hfixle : fixedIn ᾱ HE ≤ T.map (QuotientGroup.mk' N) := by
    rintro x ⟨hxHE, hxα⟩
    obtain ⟨y, -, rfl⟩ := hxHE
    obtain ⟨s, hs, hsy⟩ := (Subgroup.ext_iff.mp hR₁def (y : OddQuot K)).mp y.2
    refine ⟨s, ?_, hsy⟩
    show s ∈ T
    have h1 : ᾱ ((QuotientGroup.mk' N) s) = (QuotientGroup.mk' N) s := by rw [hsy]; exact hxα
    have h2 : (QuotientGroup.mk' N) (α s) = (QuotientGroup.mk' N) s := h1
    have h3 := @hinj ⟨α s, hαs s hs⟩ ⟨s, hs⟩ h2
    have h4' : (α s : ↥K) = s := congrArg Subtype.val h3
    have h5 : a * (s : G) * a⁻¹ = s := congrArg Subtype.val h4'
    have hsC : (s : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (s : G) * a = (a * (s : G) * a⁻¹) * a := by rw [h5]
          _ = a * s := by group)
    rw [hT, Subgroup.mem_subgroupOf]
    exact ⟨Subgroup.mem_subgroupOf.mp hs, hsC⟩
  have hle1 := Subgroup.card_le_of_le hfixle
  have hle2 : Nat.card (T.map (QuotientGroup.mk' N)) ≤ Nat.card T :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have hTcard : Nat.card T = Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans hR.1 : R ⊓ Subgroup.centralizer ({a} : Set G) ≤ K)).toEquiv
  have hchain : Nat.card ↥(fixedIn ᾱ HE) ≤
      Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) := hle1.trans (hle2.trans hTcard.le)
  omega

end CFSG.ClassicalInvolution.Hat2A7
