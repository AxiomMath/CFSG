module

public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_4
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.ABGLocalTools Subgroup CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_rightConjugate_iff' {H : Subgroup G} {g y : G} :
    y ∈ rightConjugate H g ↔ g * y * g⁻¹ ∈ H := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem sylow_le_commutator_normalizer_zpowers {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hxo : orderOf x = p) (hxP : x ∈ (P : Subgroup G))
    (hxc : ∀ y ∈ (P : Subgroup G), y * x = x * y)
    (hwc : ∀ Q : Sylow p G, x ∈ (Q : Subgroup G) → ∀ g : G,
      (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G) →
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hG : commutator G = ⊤) :
    (P : Subgroup G) ≤ ⁅normalizer ((zpowers x : Subgroup G) : Set G),
      normalizer ((zpowers x : Subgroup G) : Set G)⁆ := by
  set N : Subgroup G := normalizer ((zpowers x : Subgroup G) : Set G) with hN
  have hPN : (P : Subgroup G) ≤ N := by
    intro y hy
    rw [hN, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    show y * x * y⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hxc y hy
  have hNPN : normalizer ((P : Subgroup G) : Set G) ≤ N := by
    intro n hn
    rw [hN, mem_normalizer_iff_map_conj_eq]
    refine hwc P hxP n ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzP : z ∈ (P : Subgroup G) := zpowers_le.mpr hxP hz
    exact (mem_normalizer_iff.mp hn z).mp hzP
  set K₀ : Subgroup G := ⁅N, N⁆ with hK₀
  have hK₀N : ∀ n ∈ N, ∀ w ∈ K₀, n⁻¹ * w * n ∈ K₀ := by
    intro n hn w hw
    rw [hK₀, ← map_subtype_commutator] at hw ⊢
    obtain ⟨c, hc, rfl⟩ := hw
    refine ⟨(⟨n, hn⟩ : N)⁻¹ * c * ⟨n, hn⟩, ?_, by simp⟩
    have : (commutator N).Normal := inferInstance
    simpa using this.conj_mem c hc (⟨n, hn⟩ : N)⁻¹
  have hPder : ∀ w ∈ (commutator (P : Subgroup G)).map (P : Subgroup G).subtype, w ∈ K₀ := by
    intro w hw
    rw [map_subtype_commutator] at hw
    exact Subgroup.commutator_mono hPN hPN hw
  have hD : huppertIV34GrunKernelSubgroup (P : Subgroup G) ≤ K₀ := by
    rw [huppertIV34GrunKernelSubgroup_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (⟨hyP, hy⟩ | ⟨g, hyP, hyg⟩)
    ·
      rw [map_subtype_commutator] at hy
      exact Subgroup.commutator_mono hNPN hNPN hy
    ·
      rw [mem_rightConjugate_iff'] at hyg
      set w : G := g * y * g⁻¹ with hw
      have hwP : w ∈ (P : Subgroup G) := by
        obtain ⟨c, -, hc⟩ := hyg
        have hc' : (P : Subgroup G).subtype c = w := hc
        exact hc' ▸ c.2
      have hxw : w * x = x * w := hxc w hwP
      have hxy : y * x = x * y := hxc y hyP
      set x₂ : G := g⁻¹ * x * g with hx₂
      have hx₂y : y * x₂ = x₂ * y := by
        have : y = g⁻¹ * w * g := by rw [hw]; group
        rw [this, hx₂]
        calc g⁻¹ * w * g * (g⁻¹ * x * g) = g⁻¹ * (w * x) * g := by group
          _ = g⁻¹ * (x * w) * g := by rw [hxw]
          _ = g⁻¹ * x * g * (g⁻¹ * w * g) := by group
      set C : Subgroup G := centralizer ({y} : Set G) with hC
      have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr hxy.symm
      have hx₂C : x₂ ∈ C := mem_centralizer_singleton_iff.mpr hx₂y.symm
      have hxp : IsPGroup p (zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
      have hx₂p : IsPGroup p (zpowers x₂) := by
        have := hxp.map (MulAut.conj g⁻¹).toMonoidHom
        rw [MonoidHom.map_zpowers] at this
        have h : (MulAut.conj g⁻¹).toMonoidHom x = x₂ := by simp [hx₂]
        rwa [h] at this
      obtain ⟨T₁, hT₁⟩ := (hxp.comap_subtype (K := C)).exists_le_sylow
      obtain ⟨T₂, hT₂⟩ := (hx₂p.comap_subtype (K := C)).exists_le_sylow
      set S₁ : Subgroup G := (T₁ : Subgroup ↥C).map C.subtype
      set S₂ : Subgroup G := (T₂ : Subgroup ↥C).map C.subtype
      have hS₁ : IsSylowOf p S₁ C := ⟨T₁, rfl⟩
      have hS₂ : IsSylowOf p S₂ C := ⟨T₂, rfl⟩
      have hxS₁ : x ∈ S₁ := ⟨⟨x, hxC⟩, hT₁ (mem_zpowers _), rfl⟩
      have hx₂S₂ : x₂ ∈ S₂ := ⟨⟨x₂, hx₂C⟩, hT₂ (mem_zpowers _), rfl⟩
      obtain ⟨k, hkC, hk⟩ := hS₁.exists_mem_conj hS₂
      have hkS : k⁻¹ * x₂ * k ∈ S₁ := (hk x₂).mp hx₂S₂
      obtain ⟨Q, hQ⟩ := hS₁.isPGroup.exists_le_sylow
      have hxQ : x ∈ (Q : Subgroup G) := hQ hxS₁
      have hnx : (zpowers x).map (MulAut.conj (g * k)⁻¹).toMonoidHom ≤ (Q : Subgroup G) := by
        rw [MonoidHom.map_zpowers, zpowers_le]
        have : (MulAut.conj (g * k)⁻¹).toMonoidHom x = k⁻¹ * x₂ * k := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx₂]
          group
        rw [this]
        exact hQ hkS
      have hnN : (g * k)⁻¹ ∈ N := by
        rw [hN, mem_normalizer_iff_map_conj_eq]
        exact hwc Q hxQ _ hnx
      have hnN' : g * k ∈ N := by simpa using N.inv_mem hnN
      have hkC' : k * y = y * k := by
        have := mem_centralizer_singleton_iff.mp hkC
        exact this
      have hyn : y = (g * k)⁻¹ * w * (g * k) := by
        calc y = k⁻¹ * (k * y) * k⁻¹ * k := by group
          _ = k⁻¹ * (y * k) * k⁻¹ * k := by rw [hkC']
          _ = k⁻¹ * y * k := by group
          _ = (g * k)⁻¹ * w * (g * k) := by rw [hw]; group
      rw [hyn]
      exact hK₀N (g * k) hnN' w (hPder w hyg)
  intro y hy
  have hyG : y ∈ (P : Subgroup G) ⊓ commutator G := ⟨hy, by rw [hG]; trivial⟩
  rw [huppert_IV_3_4_first_grun P] at hyG
  exact hD hyG

end CFSG.LocalAnalysis.RankFourTheoremC
