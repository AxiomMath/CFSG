module

public import CFSG.ClassicalInvolution.Uniform.USylow
public import CFSG.ClassicalInvolution.Uniform.UStand
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {t : MemberType} {G : Type} [Group G] [Finite G]

theorem hypOmegaGenU_of_modU (hc : t.Cert) {Ω : Set (Subgroup G)} (h : HypOmegaModU t Ω) :
    HypOmegaGen Ω where
  conjInvariant := h.conjInvariant
  omega1 K hK := by
    obtain ⟨z, hz⟩ := h.classical K hK
    obtain ⟨P, hP⟩ := exists_isSylow2In K
    exact ⟨⟨z, hz.isUniqueInvolution hc⟩, P, hP, hz.not_isMulCommutative_sylow hc hP⟩
  omega2 K hK := by
    obtain ⟨z, hz⟩ := h.classical K hK
    by_cases hs : t.IsSolvableType
    · exact Or.inr (hz.nonempty_equiv_sl2Three hs)
    · have := hz.perfect hs
      exact Or.inl closure_twoElements_eq
  omega3 K hK J hJ P Q hP hQ := by
    obtain ⟨z, hz⟩ := h.classical K hK
    obtain ⟨w, hw⟩ := h.classical J hJ
    exact hz.natCard_isSylow2In_eq_of_members hw hP hQ
  omega4 := h.omega4
  omega5 := h.omega5

theorem hypOmegaGen_of_mod_via_U {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (h : HypOmegaMod p f Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 p f) ((hypOmegaModU_iff_hypOmegaMod hp2 hq).mpr h)

theorem hypOmegaGen_conjClass (hc : t.Cert) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMemberU t K₀ z₀) (hint : IsIntrinsicU t K₀ z₀)
    (h5 : AscHypOmega.Omega5At (Generic.CoreAssembly.conjClass K₀) K₀ z₀) :
    HypOmegaGen (Generic.CoreAssembly.conjClass K₀) :=
  hypOmegaGenU_of_modU hc (hypOmegaModU_conjClass hc h₀ hint h5)

theorem omega5At_of_twoElementsNormalize {K : Subgroup G} {z : G}
    (h₀ : IsClassicalMemberU t K z) (h : Hat2A7R.TwoElementsNormalize K z) :
    AscHypOmega.Omega5At (Generic.CoreAssembly.conjClass K) K z := by
  intro J hJ _ v hvJ hvnc hv2 hvz
  obtain ⟨a, rfl⟩ := Generic.CoreAssembly.single_class K J hJ
  set k : G := a⁻¹ * v * a with hk
  have hkK : k ∈ K := by
    have := mem_conjSub_iff.mp hvJ
    exact this
  have hvk : a * k * a⁻¹ = v := by rw [hk]; group
  have hk2 : IsPGroup 2 (Subgroup.zpowers k) := by
    have := AscHypOmega.isPGroup_zpowers_conj hv2 a⁻¹
    rw [inv_inv] at this
    exact this
  have hkz : k ∉ Subgroup.zpowers z := by
    intro hkz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkz
    apply hvnc
    intro w hw
    have hw' : a⁻¹ * w * a ∈ K := mem_conjSub_iff.mp hw
    have hcomm : k * (a⁻¹ * w * a) = (a⁻¹ * w * a) * k := by
      rw [← hn]
      have hzc : ∀ y ∈ K, z * y = y * z := fun y hy => h₀.comm_of_mem hy
      have hc : Commute z (a⁻¹ * w * a) := hzc _ hw'
      exact (hc.zpow_left n).eq
    calc v * w = a * (k * (a⁻¹ * w * a)) * a⁻¹ := by rw [hk]; group
      _ = a * ((a⁻¹ * w * a) * k) * a⁻¹ := by rw [hcomm]
      _ = w * v := by rw [hk]; group
  have hC : a * k * a⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [hvk, Subgroup.mem_centralizer_singleton_iff]
    exact hvz
  have := h k hkK hk2 hkz a hC
  rwa [hvk] at this

theorem hypOmegaGen_conjClass_of_twoElementsNormalize (hc : t.Cert) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMemberU t K₀ z₀) (hint : IsIntrinsicU t K₀ z₀)
    (h3 : Hat2A7R.TwoElementsNormalize K₀ z₀) :
    HypOmegaGen (Generic.CoreAssembly.conjClass K₀) :=
  hypOmegaGen_conjClass hc h₀ hint (omega5At_of_twoElementsNormalize h₀ h3)

end CFSG.ClassicalInvolution.Uniform
