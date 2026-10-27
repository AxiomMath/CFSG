module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcSyl
import CFSG.Assembly.ComponentTypeDefs
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement Pointwise

private theorem exists_mul_of_comm_sup' {Ω : Type} [Group Ω] {H K : Subgroup Ω}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : Ω} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hN : H ≤ Subgroup.normalizer (K : Set Ω) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : h * y * h⁻¹ = y := by rw [hc h hh y hy]; group
      rwa [this]
    · intro hy
      have h1 : h⁻¹ * (h * y * h⁻¹) = (h * y * h⁻¹) * h⁻¹ := hc h⁻¹ (H.inv_mem hh) _ hy
      have h2 : y = h * y * h⁻¹ := by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = (h * y * h⁻¹) * h⁻¹ * h := by rw [h1]
          _ = h * y * h⁻¹ := by group
      rwa [← h2] at hy
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hN
  have hx' : x ∈ (H : Set Ω) * (K : Set Ω) := by rw [← this]; exact hx
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨h, hh, k, hk, rfl⟩

private theorem map_conj_map' {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') (K : Subgroup Ω)
    (a : Ω) : (K.map (MulAut.conj a).toMonoidHom).map π =
      (K.map π).map (MulAut.conj (π a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp

private theorem le_of_map_le_of_perfect' {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω')
    {S P K : Subgroup Ω} (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hPS : P ≤ S)
    (hKS : K ≤ S) (hP : ⁅P, P⁆ = P) (h : P.map π ≤ K.map π) : P ≤ K := by
  have hf : ∀ g : ↥S, π.subgroupMap S g = 1 → g ∈ Subgroup.center ↥S := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 : (g : Ω) ∈ π.ker := congrArg Subtype.val hg
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hkc h1) s s.2)
  have hP' : ⁅P.subgroupOf S, P.subgroupOf S⁆ = P.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPS, hP]
  have h' : (P.subgroupOf S).map (π.subgroupMap S) ≤ (K.subgroupOf S).map (π.subgroupMap S) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.1
      (h (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.1 hp)))
    exact ⟨⟨k, hKS hk⟩, Subgroup.mem_subgroupOf.2 hk, Subtype.ext hkp⟩
  have key := S172X.le_of_map_le_of_perfect (π.subgroupMap S) hf hP' h'
  intro p hp
  exact Subgroup.mem_subgroupOf.1 (key (show (⟨p, hPS hp⟩ : ↥S) ∈ P.subgroupOf S from hp))

private theorem conj_le_of_mod {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') {S K : Subgroup Ω}
    (hS : S.Normal) (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hKS : K ≤ S)
    (hKperf : ⁅K, K⁆ = K) {n : Ω}
    (hn : π n ∈ Subgroup.normalizer ((K.map π : Subgroup Ω') : Set Ω')) :
    K.map (MulAut.conj n).toMonoidHom ≤ K := by
  have hK₂S : K.map (MulAut.conj n).toMonoidHom ≤ S := by
    rintro _ ⟨k, hk, rfl⟩
    exact hS.conj_mem k (hKS hk) n
  have hK₂perf : ⁅K.map (MulAut.conj n).toMonoidHom, K.map (MulAut.conj n).toMonoidHom⁆ =
      K.map (MulAut.conj n).toMonoidHom := by
    rw [← Subgroup.map_commutator, hKperf]
  refine le_of_map_le_of_perfect' π hkc hK₂S hKS hK₂perf ?_
  rw [map_conj_map']
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.1 hn).le

theorem uexc_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω Ω' : Type} [Group Ω] [Finite Ω]
    [Group Ω'] (π : Ω →* Ω') (hπ : Function.Surjective π) (hk2 : IsPGroup 2 π.ker)
    {S B K : Subgroup Ω} (hS : S.Normal) (hkS : π.ker ≤ S)
    (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hKS : K ≤ S) (hKperf : ⁅K, K⁆ = K)
    (hB : IsElemAbelian p B)
    (h : ∃ B'' U'' : Subgroup Ω', IsElemAbelian p B'' ∧ B'' ≤ S.map π ⊔ B.map π ∧
      B.map π ≤ B'' ∧ B.map π ≠ B'' ∧ U'' ≠ ⊥ ∧ IsPGroup 2 U'' ∧ U'' ≤ K.map π ∧
      B'' = (B'' ⊓ K.map π) ⊔ (B'' ⊓ Subgroup.normalizer (U'' : Set Ω')) ∧
      B'' ≤ Subgroup.normalizer ((K.map π : Subgroup Ω') : Set Ω')) :
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ U ≤ K ∧ B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω)) := by
  obtain ⟨B'', U'', hel, hle, hBle, hne, hU, hU2, hUK, hfac, hnK⟩ := h
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have hB''p : IsPGroup p B'' := isPGroup_of_isElemAbelian hel
  obtain ⟨B₁, hBB₁, hB₁p, hB₁map, hB₁ker⟩ := uexc_exists_lift hp hp2 π hπ hk2 hBp hB''p hBle
  have hinj : ∀ a ∈ B₁, ∀ b ∈ B₁, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ B₁ ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨B₁.mul_mem (B₁.inv_mem ha) hb, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    rw [hB₁ker, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.1 h1
  have hπB₁ : ∀ a ∈ B₁, π a ∈ B'' := fun a ha => by
    rw [← hB₁map]
    exact Subgroup.mem_map_of_mem π ha
  have hB₁el : IsElemAbelian p B₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      refine hinj _ (B₁.mul_mem a.2 b.2) _ (B₁.mul_mem b.2 a.2) ?_
      simp only [Subgroup.coe_mul, map_mul]
      exact isElemAbelian_commute hel (hπB₁ _ a.2) (hπB₁ _ b.2)
    · refine hinj _ (B₁.pow_mem ha p) _ B₁.one_mem ?_
      rw [map_pow, map_one]
      exact hel.2 _ (hπB₁ a ha)
  have hB₁le : B₁ ≤ S ⊔ B := by
    intro b hb
    have h1 : π b ∈ (S ⊔ B).map π := by
      rw [Subgroup.map_sup]
      exact hle (hπB₁ b hb)
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq] at h1
    exact sup_le le_rfl (hkS.trans le_sup_left) h1
  have hB₁ne : B ≠ B₁ := by
    intro heq
    apply hne
    rw [heq, hB₁map]
  have hU₁ne : K ⊓ U''.comap π ≠ ⊥ := by
    intro hbot
    apply hU
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨k, hkK, hku⟩ := Subgroup.mem_map.1 (hUK hu)
    have hk : k ∈ K ⊓ U''.comap π :=
      Subgroup.mem_inf.2 ⟨hkK, by rw [Subgroup.mem_comap, hku]; exact hu⟩
    rw [hbot, Subgroup.mem_bot] at hk
    rw [Subgroup.mem_bot, ← hku, hk, map_one]
  have hU₁2 : IsPGroup 2 (K ⊓ U''.comap π : Subgroup Ω) := by
    intro u
    obtain ⟨n, hn⟩ := hU2 ⟨π u, u.2.2⟩
    have hker : (u : Ω) ^ (2 ^ n) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := hk2 ⟨(u : Ω) ^ (2 ^ n), hker⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using this
  refine ⟨B₁, K ⊓ U''.comap π, hB₁el, hB₁le, hBB₁, hB₁ne, hU₁ne, hU₁2, inf_le_left, ?_⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro b hb
  have hπb : π b ∈ (B'' ⊓ K.map π) ⊔ (B'' ⊓ Subgroup.normalizer (U'' : Set Ω')) := by
    rw [← hfac]
    exact hπB₁ b hb
  obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_comm_sup' (H := B'' ⊓ K.map π)
    (K := B'' ⊓ Subgroup.normalizer (U'' : Set Ω'))
    (fun a ha b hb => isElemAbelian_commute hel (Subgroup.mem_inf.1 ha).1
      (Subgroup.mem_inf.1 hb).1) hπb
  obtain ⟨c, hcB₁, hcu⟩ := Subgroup.mem_map.1 (hB₁map.symm ▸ hu.1)
  obtain ⟨n, hnB₁, hnv⟩ := Subgroup.mem_map.1 (hB₁map.symm ▸ hv.1)
  have hbcn : b = c * n :=
    hinj b hb (c * n) (B₁.mul_mem hcB₁ hnB₁) (by rw [map_mul, hcu, hnv]; exact huv)
  have hcK : c ∈ K := by
    refine uexc_mem_of_mem_map hp hp2 π hk2 hKS hkc
      (hB₁p.to_le (Subgroup.zpowers_le.2 hcB₁)) ?_
    rw [hcu]
    exact hu.2
  have hnN : n ∈ Subgroup.normalizer (K : Set Ω) := by
    have hπn : π n ∈ Subgroup.normalizer ((K.map π : Subgroup Ω') : Set Ω') := hnK (hπB₁ n hnB₁)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_le_of_mod π hS hkc hKS hKperf hπn (Subgroup.mem_map_of_mem _ hy)
    · intro hy
      have hπn' : π n⁻¹ ∈ Subgroup.normalizer ((K.map π : Subgroup Ω') : Set Ω') := by
        rw [map_inv]
        exact Subgroup.inv_mem _ hπn
      have := conj_le_of_mod π hS hkc hKS hKperf hπn' (Subgroup.mem_map_of_mem _ hy)
      simpa [mul_assoc] using this
  have hnU : n ∈ Subgroup.normalizer ((K ⊓ U''.comap π : Subgroup Ω) : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 hnN y
    have hπnU : π n ∈ Subgroup.normalizer (U'' : Set Ω') := by
      rw [hnv]
      exact (Subgroup.mem_inf.1 hv).2
    have h2 := Subgroup.mem_normalizer_iff.1 hπnU (π y)
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    rw [h1, h2]
  rw [hbcn]
  exact Subgroup.mul_mem_sup ⟨hcB₁, hcK⟩ ⟨hnB₁, hnU⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
