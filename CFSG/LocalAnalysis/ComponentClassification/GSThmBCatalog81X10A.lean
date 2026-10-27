module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10La
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X10

theorem psp_order_lt {q q' : ℕ} (hq : 2 ≤ q) (h : q < q') :
    q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) < q' ^ 4 * ((q' ^ 2 - 1) * (q' ^ 4 - 1)) := by
  have h1 : q ^ 4 < q' ^ 4 := Nat.pow_lt_pow_left h (by norm_num)
  have h2 : q ^ 2 - 1 ≤ q' ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) 1
  have h3 : q ^ 4 - 1 ≤ q' ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 4) 1
  have h4 : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) := by
    have : 4 ≤ q ^ 2 := by nlinarith
    have : 16 ≤ q ^ 4 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  exact mul_lt_mul h1 (Nat.mul_le_mul h2 h3) h4 (Nat.zero_le _)

theorem lieModel_of_sec8Socle {K₀ : Type} [Group K₀] [Finite K₀] {p f p' f' : ℕ} (hp2 : p ≠ 2)
    (hp2' : p' ≠ 2) (hf' : 1 ≤ f') (hp' : p'.Prime) (hK : Blueprint.LieModel K₀ .PSp 2 p f)
    (hq : 3 < p ^ f) (hK' : IsSec8Socle K₀ p' f') :
    Blueprint.LieModel K₀ .PSp 2 p' f' ∧ p' ^ f' = p ^ f := by
  have h1 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hK
  rcases hK' with hK' | ⟨rfl, rfl, ⟨e⟩⟩
  · refine ⟨hK', ?_⟩
    have h2 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2' hK'
    have hq' : 2 ≤ p' ^ f' :=
      hp'.two_le.trans ((pow_one p').symm.le.trans (Nat.pow_le_pow_right hp'.pos hf'))
    have heq := h2.symm.trans h1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h3 := psp_order_lt hq' h
      rw [heq] at h3
      exact lt_irrefl _ h3
    · have h3 := psp_order_lt (by omega) h
      rw [← heq] at h3
      exact lt_irrefl _ h3
  · exfalso
    have h8 : Nat.card K₀ = 20160 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h8] at h1
    have h4 : 4 ≤ p ^ f := hq
    have hA : 256 ≤ (p ^ f) ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left h4 4
    have hB : 15 ≤ (p ^ f) ^ 2 - 1 := Nat.le_sub_of_add_le (by nlinarith)
    have hC : 255 ≤ (p ^ f) ^ 4 - 1 := Nat.le_sub_of_add_le (by omega)
    have hD : 256 * (15 * 255) ≤ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
      Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
    rw [← h1] at hD
    norm_num at hD

end X10

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem conj_c_z (F : d.Facts) : h.x * d.g * d.z * (h.x * d.g)⁻¹ = d.z := by
  have h1 : d.g * d.z * d.g⁻¹ = d.z := by
    calc d.g * d.z * d.g⁻¹ = d.g * (d.g⁻¹ * d.z * d.g) * d.g⁻¹ := by rw [F.z_g]
      _ = d.z := by group
  have h2 : h.x * d.z * h.x⁻¹ = d.z := by
    calc h.x * d.z * h.x⁻¹ = h.x * (h.x⁻¹ * d.z * h.x) * h.x⁻¹ := by rw [d.x_inv_z_x]
      _ = d.z := by group
  rw [show h.x * d.g * d.z * (h.x * d.g)⁻¹ = h.x * (d.g * d.z * d.g⁻¹) * h.x⁻¹ by group, h1, h2]

theorem conj_c_az (I : In81) (F : d.Facts) :
    h.x * d.g * (h.a * d.z) * (h.x * d.g)⁻¹ = d.tau * d.z := by
  rw [Eight.conj_mul_distrib_right, conj_c_a I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F,
    conj_c_z F]

theorem z_mem_K : d.z ∈ h.K := H₁.kloc.fixedLayer_le_K (h.toHyp52.D_le_JB d.z_D)

end Data

end L81Hyp

end Hyp59

namespace X10

@[expose] def AzComp (K : Type) [Field K] {H : Type} [Group H] [Finite H] {h : Hyp59 H}
    {H₁ : h.L81Hyp}
    (d : H₁.Data) (J : Subgroup H) : Prop :=
  J ≤ conjugate h.K (h.x * d.g) ⊓ centralizer {h.a * d.z} ∧
    IsPComponent 2 (J.subgroupOf (conjugate h.K (h.x * d.g) ⊓ centralizer {h.a * d.z})) ∧
    h.a * d.z ∈ J ∧ Nonempty (J ⧸ pPrimeCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 2) K)

theorem isPComponent_map_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C M : Subgroup G} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) : IsPComponent 2 ((M.map f).subgroupOf (C.map f)) := by
  let ψ : C ≃* C.map f := C.equivMapOfInjective f hf
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hM
  convert h using 1
  ext ⟨x, hx⟩
  rw [mem_subgroupOf, mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hMC hm⟩, hm, rfl⟩
  · rintro ⟨⟨c, hc⟩, hcM, hceq⟩
    refine ⟨c, hcM, ?_⟩
    have := congrArg Subtype.val hceq
    exact this

theorem gs81Step10A
    (I : In81) {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp} {d : H₁.Data}
    (F : d.Facts) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f) (hq : 3 < p ^ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (J₁ J₂ : Subgroup H), Nat.card K = p ^ f ∧
      J₁ ≠ J₂ ∧ AzComp K d J₁ ∧ AzComp K d J₂ := by
  obtain ⟨p', f', c, hp', hp2', hf', hK', -, hcz, hct, -⟩ := d.exists_e6Conf I.cf1 I.cf2
    CatFactsSp4.cfSec8JOrder cf81L0
  obtain ⟨hKp', hqq⟩ := lieModel_of_sec8Socle hp2 hp2' hf' hp' hK hq hK'
  have hc : c.Props := ConfA.props_of_facts ((hp'.odd_of_ne_two hp2').pow) c
    (ConfK.facts_psp hp' hp2' hf' hKp' c.a c.adm)
  have hτK := d.tau_K
  have hzK := d.z_mem_K
  have hτ : MulAut.conj ((⟨d.tau, hτK⟩ : h.K) : h.K ⧸ pPrimeCore 2 h.K) = c.tau := by
    rw [hct]
    exact (H₁.kloc.rho_of_mem_K hτK).symm
  have hz : MulAut.conj ((⟨d.z, hzK⟩ : h.K) : h.K ⧸ pPrimeCore 2 h.K) = c.z := by
    rw [hcz]
    exact (H₁.kloc.rho_of_mem_K hzK).symm
  have h5 : 5 ≤ p' ^ f' := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
    omega
  obtain ⟨K, _, _, E₁, E₂, hKc, hne, hE₁, hE₂⟩ :=
    tauZ_twoComponents hp' hp2' hf' h5 hKp' c hc hτ hz
  have hzQ : d.z ∈ h.Q ⊓ h.M3 := ⟨h.toHyp52.sec8_D_le_Q d.z_D, H₁.kloc.D_le_M3 d.z_D⟩
  have hτz := F.tau_comm d.z hzQ
  set t : h.K := ⟨d.tau, hτK⟩ * ⟨d.z, hzK⟩ with htdef
  have htH : (t : H) = d.tau * d.z := rfl
  have ht2 : t * t = 1 := Subtype.ext (by
    show d.tau * d.z * (d.tau * d.z) = 1
    calc d.tau * d.z * (d.tau * d.z) = d.tau * (d.z * d.tau) * d.z := by group
      _ = d.tau * (d.tau * d.z) * d.z := by rw [hτz]
      _ = 1 := by rw [← mul_assoc, d.tau_sq, one_mul, d.z_mul_self])
  have hEt : ∀ E : Subgroup (h.K ⧸ pPrimeCore 2 h.K),
      IsSL2Comp K (((⟨d.tau, hτK⟩ : h.K) : h.K ⧸ pPrimeCore 2 h.K) *
        ((⟨d.z, hzK⟩ : h.K) : h.K ⧸ pPrimeCore 2 h.K)) E →
      IsSL2Comp K (QuotientGroup.mk' (pPrimeCore 2 h.K) t) E := fun E hE => hE
  obtain ⟨M₁, hM₁C, hM₁p, htM₁, hM₁E, ⟨eM₁⟩⟩ := exists_lift_SL2Comp ht2 (hEt E₁ hE₁)
  obtain ⟨M₂, hM₂C, hM₂p, htM₂, hM₂E, ⟨eM₂⟩⟩ := exists_lift_SL2Comp ht2 (hEt E₂ hE₂)
  have hMne : M₁ ≠ M₂ := fun h12 => hne (by rw [← hM₁E, ← hM₂E, h12])
  set c' := h.x * d.g with hc'
  have hcaz : c' * (h.a * d.z) * c'⁻¹ = d.tau * d.z := Hyp59.L81Hyp.Data.conj_c_az I F
  have haz : c'⁻¹ * (d.tau * d.z) * c' = h.a * d.z := by rw [← hcaz]; group
  let φ : h.K →* H := (MulAut.conj c'⁻¹).toMonoidHom.comp h.K.subtype
  have hφ : ∀ k : h.K, φ k = c'⁻¹ * (k : H) * c' := fun k => by
    show c'⁻¹ * (k : H) * c'⁻¹⁻¹ = _
    rw [inv_inv]
  have hφinj : Function.Injective φ := fun x y hxy => by
    rw [hφ, hφ] at hxy
    exact Subtype.ext (by simpa using hxy)
  have hCmap : (centralizer ({t} : Set h.K)).map φ =
      conjugate h.K c' ⊓ centralizer {h.a * d.z} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : (k : H) * (d.tau * d.z) = d.tau * d.z * (k : H) := by
        have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)
        simpa [htH] using this
      refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
      · rw [mem_conjugate_iff, hφ, show c' * (c'⁻¹ * (k : H) * c') * c'⁻¹ = (k : H) by group]
        exact k.2
      · rw [hφ, ← haz]
        calc c'⁻¹ * (k : H) * c' * (c'⁻¹ * (d.tau * d.z) * c') =
              c'⁻¹ * ((k : H) * (d.tau * d.z)) * c' := by group
          _ = c'⁻¹ * (d.tau * d.z * (k : H)) * c' := by rw [hk']
          _ = c'⁻¹ * (d.tau * d.z) * c' * (c'⁻¹ * (k : H) * c') := by group
    · rintro ⟨hxL, hxc⟩
      have hxK : c' * x * c'⁻¹ ∈ h.K := mem_conjugate_iff.mp hxL
      have hxc' : x * (h.a * d.z) = h.a * d.z * x := mem_centralizer_singleton_iff.mp hxc
      refine ⟨⟨c' * x * c'⁻¹, hxK⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), ?_⟩
      · show c' * x * c'⁻¹ * (d.tau * d.z) = d.tau * d.z * (c' * x * c'⁻¹)
        rw [← hcaz]
        calc c' * x * c'⁻¹ * (c' * (h.a * d.z) * c'⁻¹) = c' * (x * (h.a * d.z)) * c'⁻¹ := by
              group
          _ = c' * (h.a * d.z * x) * c'⁻¹ := by rw [hxc']
          _ = c' * (h.a * d.z) * c'⁻¹ * (c' * x * c'⁻¹) := by group
      · rw [hφ]
        group
  have hJ : ∀ M : Subgroup h.K, M ≤ centralizer {t} →
      IsPComponent 2 (M.subgroupOf (centralizer {t})) → t ∈ M →
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
      AzComp K d (M.map φ) := by
    intro M hMC hMp htM ⟨eM⟩
    refine ⟨hCmap ▸ map_mono hMC, hCmap ▸ isPComponent_map_injective φ hφinj hMC hMp, ?_, ?_⟩
    · have := mem_map_of_mem φ htM
      rwa [hφ, htH, haz] at this
    · let e : M ≃* M.map φ := M.equivMapOfInjective φ hφinj
      exact ⟨(QuotientGroup.congr (pPrimeCore 2 M) (pPrimeCore 2 (M.map φ)) e
        (pPrimeCore_map_iso 2 e)).symm.trans eM⟩
  refine ⟨K, inferInstance, inferInstance, M₁.map φ, M₂.map φ, hKc.trans hqq, ?_,
    hJ M₁ hM₁C hM₁p htM₁ ⟨eM₁⟩, hJ M₂ hM₂C hM₂p htM₂ ⟨eM₂⟩⟩
  intro h12
  exact hMne (map_injective hφinj h12)

end X10

end CFSG.ComponentClassification.GSThmB
