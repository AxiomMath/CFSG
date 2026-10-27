module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.RadicalStructure
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.LA5Module
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

theorem perfect_commutator_cyclic_normal {M : Type*} [Group M] {P N : Subgroup M}
    [N.Normal] [IsCyclic N] (hP : ⁅P, P⁆ = P) : ⁅P, N⁆ = ⊥ := by
  have hperf : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  let φ : P →* MulAut N := (MulAut.conjNormal (H := N)).comp P.subtype
  let ψ : P →* (ZMod (Nat.card N))ˣ := (IsCyclic.mulAutMulEquiv N).toMonoidHom.comp φ
  have hker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker ψ
  rw [commutator_eq_bot_iff_le_centralizer]
  intro g hg
  rw [mem_centralizer_iff]
  intro n hn
  have h1 : ψ ⟨g, hg⟩ = 1 := hker (mem_top _)
  have h2 : φ ⟨g, hg⟩ = 1 := (IsCyclic.mulAutMulEquiv N).injective (by simpa [ψ] using h1)
  have h3 := congrArg (fun a : MulAut N => ((a ⟨n, hn⟩ : N) : M)) h2
  simp only [φ, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc n * g = (g * n * g⁻¹) * g := by rw [h3]
    _ = g * n := by group

theorem exists_normal_subgroup_card_five {X : Type*} [Group X] [Finite X] (S : Subgroup X)
    [S.Normal] (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h5 : 5 ∣ Nat.card S) {σ : X}
    (hσ : orderOf σ = 5) (hσS : ∀ k : ℕ, σ ^ k ∈ S → σ ^ k = 1) (hX : ¬ 125 ∣ Nat.card X) :
    ∃ Z : Subgroup X, Z.Normal ∧ Z ≤ S ∧ Nat.card Z = 5 := by
  let Z : Subgroup X :=
    { carrier := {x | x ∈ S ∧ x ^ 5 = 1}
      one_mem' := ⟨S.one_mem, one_pow 5⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨S.mul_mem ha.1 hb.1, ?_⟩
        have hcomm : Commute a b := hS a ha.1 b hb.1
        rw [hcomm.mul_pow 5, ha.2, hb.2, mul_one]
      inv_mem' := by
        intro a ha
        refine ⟨S.inv_mem ha.1, ?_⟩
        rw [inv_pow, ha.2, inv_one] }
  have hSnormal : S.Normal := inferInstance
  have hZN : Z.Normal :=
    ⟨fun z hz x => ⟨hSnormal.conj_mem z hz.1 x, by
        rw [conj_pow, hz.2, mul_one, mul_inv_cancel]⟩⟩
  have hZS : Z ≤ S := fun z hz => hz.1
  haveI : Z.Normal := hZN
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 5 h5
  have hsx : orderOf (s : X) = 5 := by
    rw [Subgroup.orderOf_coe s, hs]
  have hspow : (s : X) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (s : X)
    rwa [hsx] at this
  have hs_mem_Z : (s : X) ∈ Z := ⟨s.2, hspow⟩
  have hs_ne_one : (s : X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hsx
    exact (by norm_num : (1 : ℕ) ≠ 5) hsx
  have hZpg : IsPGroup 5 Z := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using g.2.2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZpg
  have hσne : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact (by norm_num : (1 : ℕ) ≠ 5) hσ
  have hK : Z ⊓ Subgroup.zpowers σ = ⊥ := by
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers σ) ∣ 5 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Z ⊓ Subgroup.zpowers σ ≤ Subgroup.zpowers σ)
      rwa [Nat.card_zpowers, hσ] at this
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ hdvd with h1 | h5'
    · exact Subgroup.eq_bot_of_card_eq (Z ⊓ Subgroup.zpowers σ) h1
    · exfalso
      have hKeq : Z ⊓ Subgroup.zpowers σ = Subgroup.zpowers σ :=
        Subgroup.eq_of_le_of_card_ge (H := Z ⊓ Subgroup.zpowers σ)
          (K := Subgroup.zpowers σ) inf_le_right (by rw [Nat.card_zpowers, hσ, h5'])
      have hσmem : σ ∈ Z ⊓ Subgroup.zpowers σ := by
        rw [hKeq]
        exact Subgroup.mem_zpowers σ
      exact hσne (by have := hσS 1 (by simpa using hZS hσmem.1); simpa using this)
  have hnormal : Subgroup.zpowers σ ≤ Subgroup.normalizer (Z : Set X) := by
    rw [Subgroup.normalizer_eq_top Z]
    exact le_top
  have hdisj : Disjoint Z (Subgroup.zpowers σ) := disjoint_iff.mpr hK
  have hsupcard : Nat.card ↥(Z ⊔ Subgroup.zpowers σ) = 5 ^ m * 5 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z
      (Subgroup.zpowers σ) hnormal hdisj, hm, Nat.card_zpowers, hσ]
  have hdvd : 5 ^ (m + 1) ∣ Nat.card X := by
    have h := Subgroup.card_subgroup_dvd_card (Z ⊔ Subgroup.zpowers σ)
    rw [hsupcard, ← pow_succ] at h
    exact h
  have hm_le_one : m ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have h3 : 3 ≤ m + 1 := by omega
    have h125 : 5 ^ 3 ∣ Nat.card X := (pow_dvd_pow 5 h3).trans hdvd
    have h125' : 125 ∣ Nat.card X := by
      have h53 : 5 ^ 3 = 125 := by norm_num
      rwa [h53] at h125
    exact hX h125'
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    have hcard1 : Nat.card Z = 1 := by rw [hm, hm0, pow_zero]
    haveI : Subsingleton Z := (Nat.card_eq_one_iff_unique.mp hcard1).1
    have hcontra : (s : X) = 1 := by
      have := congrArg Subtype.val (Subsingleton.elim (⟨(s : X), hs_mem_Z⟩ : Z) 1)
      simpa using this
    exact hs_ne_one hcontra
  have hm_eq : m = 1 := by omega
  refine ⟨Z, hZN, hZS, ?_⟩
  rw [hm, hm_eq, pow_one]

theorem not_five_dvd_card_solvableRadical {X : Type} [Group X] [Finite X] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {ρ : X →* (W ≃ₗ[ZMod 2] W)} {w : W}
    {P F : Subgroup X} {v : X} (h : WrData X ρ w P F v) :
    ¬ 5 ∣ Nat.card (CFSG.solvableRadical X) := by
  intro h5
  obtain ⟨_hvS, _hcomm_v, _hinv, hab, _hodd⟩ := radical_structure h
  obtain ⟨eF⟩ := h.F_iso
  obtain ⟨eP⟩ := h.P_iso
  obtain ⟨x, hx⟩ := exists_orderOf_eq_five_a5
  let σF : F := eF.symm x
  let σ : X := σF
  have hσFmem : σ ∈ F := σF.2
  have hσF : orderOf σF = 5 :=
    (orderOf_injective (eF.symm : alternatingGroup (Fin 5) →* F) eF.symm.injective x).trans hx
  have hσ : orderOf σ = 5 := by
    show orderOf (σF : X) = 5
    rw [Subgroup.orderOf_coe σF]
    exact hσF
  have hSsolv : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hFS : F ⊓ CFSG.solvableRadical X = ⊥ :=
    inf_eq_bot_of_equiv_a5 F eF (CFSG.solvableRadical X) hSsolv
  have hσS : ∀ k : ℕ, σ ^ k ∈ CFSG.solvableRadical X → σ ^ k = 1 := by
    intro k hk
    have hmemF : σ ^ k ∈ F := F.pow_mem hσFmem k
    have hmem : σ ^ k ∈ F ⊓ CFSG.solvableRadical X := ⟨hmemF, hk⟩
    rw [hFS] at hmem
    simpa using hmem
  have hX : ¬ 125 ∣ Nat.card X := by
    intro h125
    exact (by norm_num : ¬ (125 : ℕ) ∣ 348364800) (h125.trans h.card_dvd)
  obtain ⟨Z, hZN, hZS, hZcard⟩ :=
    exists_normal_subgroup_card_five (CFSG.solvableRadical X) hab h5 hσ hσS hX
  haveI : Z.Normal := hZN
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsCyclic Z := isCyclic_of_prime_card (p := 5) hZcard
  obtain ⟨ρ₀, hρ₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Z) 5 (by refine ⟨1, ?_⟩; rw [hZcard, mul_one])
  have hρ₀ne : ρ₀ ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at hρ₀ord
    exact (by norm_num : (1 : ℕ) ≠ 5) hρ₀ord
  have hρ₀powZ : ρ₀ ^ 5 = 1 := by
    have := pow_orderOf_eq_one ρ₀
    rwa [hρ₀ord] at this
  have hρ₀powX : (ρ₀ : X) ^ 5 = 1 := by
    have := congrArg (fun z : Z => (z : X)) hρ₀powZ
    simpa using this
  have hFperf : ⁅F, F⁆ = F := commutator_eq_self_of_equiv_a5 F eF
  let P' : Subgroup X := ⁅P, P⁆
  obtain ⟨eP'⟩ := commutator_equiv_a5_of_equiv_perm_five P eP
  have hP'perf : ⁅P', P'⁆ = P' := commutator_eq_self_of_equiv_a5 P' eP'
  have hFZbot : ⁅F, Z⁆ = ⊥ := perfect_commutator_cyclic_normal (P := F) (N := Z) hFperf
  have hP'Zbot : ⁅P', Z⁆ = ⊥ := perfect_commutator_cyclic_normal (P := P') (N := Z) hP'perf
  have hFZ : ∀ f ∈ F, ∀ z ∈ Z, f * z = z * f := by
    have hle : F ≤ Subgroup.centralizer (Z : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFZbot
    intro f hf z hz
    exact ((Subgroup.mem_centralizer_iff.mp (hle hf)) z hz).symm
  have hP'Z : ∀ p ∈ P', ∀ z ∈ Z, p * z = z * p := by
    have hle : P' ≤ Subgroup.centralizer (Z : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hP'Zbot
    intro p hp z hz
    exact ((Subgroup.mem_centralizer_iff.mp (hle hp)) z hz).symm
  let r : W ≃ₗ[ZMod 2] W := ρ (ρ₀ : X)
  have hr5 : r ^ 5 = 1 := by
    show (ρ (ρ₀ : X)) ^ 5 = 1
    rw [← map_pow, hρ₀powX, map_one]
  have hr1 : r ≠ 1 := by
    intro hr
    have h1 : (ρ₀ : X) = 1 := by
      apply h.ρ_injective
      rw [show ρ (ρ₀ : X) = 1 from hr, map_one]
    have h2 : ρ₀ = 1 := by
      apply Subtype.ext
      simpa using h1
    exact hρ₀ne h2
  let Fρ : Subgroup (W ≃ₗ[ZMod 2] W) := F.map ρ
  let Pρ : Subgroup (W ≃ₗ[ZMod 2] W) := P'.map ρ
  have heFρ : Fρ ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective F ρ h.ρ_injective).symm.trans eF
  have hePρ : Pρ ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective P' ρ h.ρ_injective).symm.trans eP'
  have hFρr : ∀ f ∈ Fρ, f * r = r * f := by
    intro f hf
    simp only [Fρ, Subgroup.mem_map] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    calc ρ g * ρ (ρ₀ : X) = ρ (g * (ρ₀ : X)) := (map_mul ρ g (ρ₀ : X)).symm
      _ = ρ ((ρ₀ : X) * g) := by rw [hFZ g hg (ρ₀ : X) ρ₀.2]
      _ = ρ (ρ₀ : X) * ρ g := map_mul ρ (ρ₀ : X) g
  have hPρr : ∀ p ∈ Pρ, p * r = r * p := by
    intro p hp
    simp only [Pρ, Subgroup.mem_map] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    calc ρ g * ρ (ρ₀ : X) = ρ (g * (ρ₀ : X)) := (map_mul ρ g (ρ₀ : X)).symm
      _ = ρ ((ρ₀ : X) * g) := by rw [hP'Z g hg (ρ₀ : X) ρ₀.2]
      _ = ρ (ρ₀ : X) * ρ g := map_mul ρ (ρ₀ : X) g
  have hFρfpf : ∀ f ∈ Fρ, orderOf f = 5 → ∀ x : W, f x = x → x = 0 := by
    intro f hf hford x hx
    simp only [Fρ, Subgroup.mem_map] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    have hgord : orderOf g = 5 := by
      rw [← orderOf_injective ρ h.ρ_injective g]
      exact hford
    exact h.F_fpf g hg hgord x hx
  have hPρw : ∀ p ∈ Pρ, p w = w := by
    intro p hp
    simp only [Pρ, Subgroup.mem_map] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    exact h.P_fix g (Subgroup.commutator_le_self P hg)
  exact no_order_five_commuting_a5_pair h.finrank_eq r hr5 hr1 Fρ Pρ heFρ hePρ
    hFρr hPρr hFρfpf w h.w_ne_zero hPρw

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
