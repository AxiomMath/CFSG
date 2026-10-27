module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAll
import CFSG.ClassicalInvolution.Asc77.AscT8BasicEng
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

section Component

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem dComp_eq_of_mem {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dComp Ω K) :
    dComp Ω M = dComp Ω K := by
  ext N
  constructor
  · intro hN
    exact Relation.ReflTransGen.trans hM hN
  · intro hN
    exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK hM) hN

theorem mem_dComp_of_mem_omegaNbr {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    J ∈ dComp Ω K :=
  Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩

theorem mem_sigmaNorm_iff (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω) {g : G} :
    g ∈ sigmaNorm Ω K ↔ conjSub g K ∈ dComp Ω K := by
  constructor
  · intro hg
    exact (hg K).mp Relation.ReflTransGen.refl
  · intro hgK M
    have heq : dComp Ω (conjSub g K) = dComp Ω K := dComp_eq_of_mem hK hgK
    constructor
    · intro hM
      have := mem_dComp_conjSub hΩ hM g
      rwa [heq] at this
    · intro hM
      have hM' : conjSub g M ∈ dComp Ω (conjSub g K) := by rwa [heq]
      have := mem_dComp_conjSub hΩ hM' g⁻¹
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem mem_sigmaNorm_of_mem_dComp (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) {g : G} (hg : conjSub g M ∈ dComp Ω K) : g ∈ sigmaNorm Ω K := by
  rw [mem_sigmaNorm_iff hΩ hK]
  have h1 : conjSub g K ∈ dComp Ω (conjSub g M) :=
    mem_dComp_conjSub hΩ (reflTransGen_dAdj_symm hK hM) g
  rwa [dComp_eq_of_mem hK hg] at h1

theorem normalizer_le_sigmaNorm (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.normalizer (K : Set G) ≤ sigmaNorm Ω K := fun g hg => by
  rw [mem_sigmaNorm_iff hΩ hK, mem_normalizer_iff_conjSub_eq.mp hg]
  exact Relation.ReflTransGen.refl

theorem normalizer_le_sigmaNorm_of_mem (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) : Subgroup.normalizer (M : Set G) ≤ sigmaNorm Ω K := fun g hg =>
  mem_sigmaNorm_of_mem_dComp hΩ hK hM (by rw [mem_normalizer_iff_conjSub_eq.mp hg]; exact hM)

theorem noTwins_of_mem (hΩ : ConjInvariant Ω) {K : Subgroup G}
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    {M : Subgroup G} (hM : M ∈ Ω) : ∀ M' ∈ twinSet Ω M, M' = M := by
  obtain ⟨c, rfl⟩ := htrans M hM
  intro K' hK'
  have h := twinSet_conj hΩ hK' c⁻¹
  rw [conjSub_inv_conjSub] at h
  calc K' = conjSub c (conjSub c⁻¹ K') := (conjSub_conjSub_inv c K').symm
    _ = conjSub c K := by rw [hnt _ h]

theorem centralizer_le_normalizer_of_noTwins (hΩ : ConjInvariant Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro c hc
  rw [mem_normalizer_iff_conjSub_eq]
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [mul_inv_eq_iff_eq_mul]
    exact hc
  have h1 : IsUniqueInvolution (conjSub c K) z := hcz ▸ hz.conj c
  exact hnt _ ⟨hΩ c K hK, z, hz, h1⟩

end Component

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_commutes_isSylow2In {K R R' : Subgroup G} (hR : IsSylow2In R K)
    (hR' : IsSylow2In R' K) (hc : Commutes R R') : R' = R := by
  exact eq_of_commutes_isSylow2InE hR hR' hc

omit [Finite G] in
theorem isSylow2In_of_sylow_le (S : Sylow 2 G) {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    IsSylow2In (S : Subgroup G) H :=
  ⟨hSH, S.isPGroup', fun _ _ hV'2 hle => S.is_maximal' hV'2 hle⟩

theorem exists_conj_into_sylow (S : Sylow 2 G) {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    {x : G} (hxH : x ∈ H) (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ y ∈ H, y * x * y⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx (Subgroup.zpowers_le.mpr hxH)
  obtain ⟨y, hyH, hyV⟩ := exists_conj_of_isSylow2In hV (isSylow2In_of_sylow_le S hSH)
  refine ⟨y, hyH, ?_⟩
  rw [← hyV]
  exact conj_mem_conjSub (hxV (Subgroup.mem_zpowers x))

variable {p f : ℕ} [Fact p.Prime]

theorem conjSub_eq_of_conjSub_eq (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {J T : Subgroup G}
    (hJ : J ∈ Ω) (hT : T ∈ RSet Ω) (hTJ : T ≤ J) {s : G} (hs : conjSub s T = T) :
    conjSub s J = J :=
  hΩ.eq_of_le_of_le (hΩ.conjInvariant s J hJ) hJ
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJ hT hTJ).2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hT; omega) (hs ▸ conjSub_mono hTJ) hTJ

theorem conjSub_mem_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} {S : Sylow 2 G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hfix : conjSub s R ≠ R) : conjSub s K ∈ omegaNbr Ω K := by
  exact conjSub_mem_omegaNbrE hΩ.conjInvariant
    (fun hM hR hRM => T3.isSylow2In_of_mem_RSet_of_le hp hΩ hM hR hRM)
    (fun hR => hΩ.eight_le_of_mem_RSet hp hR) (l6_7_proved p f hp hq G Ω hΩ S)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hKJ hz hAJ hA2 hA3 hAc)
    hK hR hRK hRS hz hs hfix

theorem sylow_le_sigmaNorm (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} {S : Sylow 2 G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) :
    (S : Subgroup G) ≤ sigmaNorm Ω K := by
  intro s hs
  rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
  by_cases hfix : conjSub s R = R
  · rw [conjSub_eq_of_conjSub_eq hp hΩ hK hR hRK hfix]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨hΩ.conjInvariant s K hK, Or.inl (conjSub_mem_omegaNbr hp hq hΩ hK hR hRK hRS hz hs hfix)⟩

end Sylow

section Group274

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def H274 (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) : Subgroup G :=
  sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
    Subgroup.centralizer ({z * s} : Set G))

theorem sigmaNorm_le_H274 (K : Subgroup G) (z : G) : sigmaNorm Ω K ≤ H274 Ω K z := le_sup_left

theorem centralizer_mul_le_H274 {K M : Subgroup G} {z s : G} (hM : M ∈ omegaNbr Ω K)
    (hs : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤ H274 Ω K z :=
  le_sup_of_le_right (le_iSup₂_of_le M hM (le_iSup₂_of_le s hs le_rfl))

theorem centralizer_mul_le_H274_of_mem_dComp (hΩ : ConjInvariant Ω) {K L₀ L₁ : Subgroup G}
    (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hL₀ : L₀ ∈ dComp Ω K) {z y₀ y₁ : G}
    (hz : IsUniqueInvolution K z) (hy₀ : IsUniqueInvolution L₀ y₀) (hL₁ : L₁ ∈ omegaNbr Ω L₀)
    (hy₁ : IsUniqueInvolution L₁ y₁) :
    Subgroup.centralizer ({y₀ * y₁} : Set G) ≤ H274 Ω K z := by
  have hL₀Ω : L₀ ∈ Ω := mem_of_mem_dComp' hK hL₀
  obtain ⟨c, hc⟩ := htrans L₀ hL₀Ω
  have hcN : c ∈ sigmaNorm Ω K := (mem_sigmaNorm_iff hΩ hK).mpr (hc ▸ hL₀)
  have hy₀' : y₀ = c * z * c⁻¹ := by
    have := hz.conj c
    rw [hc] at this
    exact hy₀.eq this
  have hM : conjSub c⁻¹ L₁ ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ hL₁ c⁻¹
    rwa [← hc, conjSub_inv_conjSub] at this
  have hs : IsUniqueInvolution (conjSub c⁻¹ L₁) (c⁻¹ * y₁ * c) := by
    have := hy₁.conj c⁻¹
    rwa [inv_inv] at this
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : c⁻¹ * x * c ∈ Subgroup.centralizer ({z * (c⁻¹ * y₁ * c)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : z * (c⁻¹ * y₁ * c) = c⁻¹ * (y₀ * y₁) * c := by rw [hy₀']; group
    rw [e]
    calc c⁻¹ * x * c * (c⁻¹ * (y₀ * y₁) * c) = c⁻¹ * (x * (y₀ * y₁)) * c := by group
      _ = c⁻¹ * ((y₀ * y₁) * x) * c := by rw [hx]
      _ = c⁻¹ * (y₀ * y₁) * c * (c⁻¹ * x * c) := by group
  have hxH : c⁻¹ * x * c ∈ H274 Ω K z := centralizer_mul_le_H274 hM hs hx'
  have hcH : c ∈ H274 Ω K z := sigmaNorm_le_H274 K z hcN
  have hxe : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [hxe]
  exact (H274 Ω K z).mul_mem ((H274 Ω K z).mul_mem hcH hxH) ((H274 Ω K z).inv_mem hcH)

end Group274

end T8

end CFSG.ClassicalInvolution.Asc77
