module

public import CFSG.LieType.SeitzGeneration.QuasiHighLift
public import CFSG.LieType.SeitzGeneration.HyperCoverLinear
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LieType.SeitzGeneration.SpHyperScope
public import CFSG.LieType.SeitzGeneration.OrthHyperScope
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInner
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitary
public import CFSG.LieType.SeitzGeneration.ExcHigh.Leaves

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP

theorem not_dvd_card_of_isPGroup' {G : Type*} [Group G] [Finite G] {r p : ℕ} [Fact r.Prime]
    [hp : Fact p.Prime] (hrp : r ≠ p) (hG : IsPGroup r G) : ¬ p ∣ Nat.card G := by
  intro hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hG) g
  rw [hg] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    exact hp.out.one_lt.ne' hk
  · have hrd : r ∣ p := hk ▸ dvd_pow_self r hk0.ne'
    exact hrp ((Nat.prime_dvd_prime_iff_eq Fact.out hp.out).1 hrd)

theorem pow_eq_one_of_mem_innerImage {K : Type*} [Group K] {p : ℕ} {E : Subgroup (MulAut K)}
    (hE : ∀ f ∈ E, f ^ p = 1) {s : K ⧸ Subgroup.center K} (hs : s ∈ innerImage E) : s ^ p = 1 := by
  obtain ⟨k, hk, rfl⟩ := hs
  have h1 : MulAut.conj (k ^ p) = 1 := by rw [map_pow]; exact hE _ hk
  have h2 : k ^ p ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut K => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact h2

theorem seitzHyperGamma_eq_top_of_inner_equiv {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) {P : Type*} [Group P]
    (ι : K ⧸ Subgroup.center K ≃* P) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) {H₁ H₂ : Subgroup P}
    (hp₁ : ¬ p ∣ Nat.card H₁) (hp₂ : ¬ p ∣ Nat.card H₂)
    (hn₁ : ∀ e ∈ (innerImage E).map ι.toMonoidHom, ∀ s ∈ H₁, e * s * e⁻¹ ∈ H₁)
    (hn₂ : ∀ e ∈ (innerImage E).map ι.toMonoidHom, ∀ s ∈ H₂, e * s * e⁻¹ ∈ H₂)
    (hgen : H₁ ⊔ H₂ = ⊤) : seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : ∀ H : Subgroup P, Nat.card (H.map ι.symm.toMonoidHom) = Nat.card H := fun H =>
    Subgroup.card_map_of_injective ι.symm.injective
  have hnorm : ∀ H : Subgroup P,
      (∀ e ∈ (innerImage E).map ι.toMonoidHom, ∀ s ∈ H, e * s * e⁻¹ ∈ H) →
      ∀ e ∈ innerImage E, ∀ s ∈ H.map ι.symm.toMonoidHom,
        e * s * e⁻¹ ∈ H.map ι.symm.toMonoidHom := by
    rintro H hH e he _ ⟨u, hu, rfl⟩
    refine ⟨ι e * u * (ι e)⁻¹, hH _ ⟨e, he, rfl⟩ u hu, ?_⟩
    simp
  refine seitzHyperGamma_eq_top_of_inner hperf hE hE1 hinn
    {H₁.map ι.symm.toMonoidHom, H₂.map ι.symm.toMonoidHom} ?_ ?_ ?_
  · intro H hH
    rcases hH with rfl | hH
    · rw [hcard]; exact hp₁
    · rw [Set.mem_singleton_iff.1 hH, hcard]; exact hp₂
  · rintro H (rfl | hH)
    · exact hnorm H₁ hn₁
    · rw [Set.mem_singleton_iff.1 hH]
      exact hnorm H₂ hn₂
  · rw [iSup_insert, iSup_singleton, ← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _
      ι.symm.surjective]

section Linear

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem exists_p'Subgroups_psl {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) (hn : 0 < n)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)} (hE : IsPGroup p E)
    {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : ∀ x : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    ∃ H₁ H₂ : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F),
      ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ ∧
      (∀ e ∈ E, ∀ s ∈ H₁, e * s * e⁻¹ ∈ H₁) ∧ (∀ e ∈ E, ∀ s ∈ H₂, e * s * e⁻¹ ∈ H₂) ∧
      H₁ ⊔ H₂ = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) F) with hZ
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  set H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π with hH
  have hcardH : Nat.card H = Nat.card E * Nat.card Z := by
    let φ : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
    have hφ : Function.Surjective φ := fun e => by
      obtain ⟨g, hg⟩ := hπ (e : ProjectiveSpecialLinearGroup (Fin n) F)
      exact ⟨⟨g, by simp [hH, hg]⟩, Subtype.ext hg⟩
    have hker_le : π.ker ≤ H := fun z hz => by
      rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact E.one_mem
    have hφker : φ.ker = π.ker.subgroupOf H := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hN : Nat.card φ.ker = Nat.card Z := by
      rw [hφker, ← hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    rw [← Subgroup.card_ker_mul_card_of_surjective hφ, hN, mul_comm]
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hHF : (Nat.card H : F) ≠ 0 := by
    rw [hcardH, hk, Nat.cast_mul, Nat.cast_pow]
    exact mul_ne_zero (pow_ne_zero k hpF) (natCast_card_center_ne_zero hn)
  obtain ⟨W', hc, hW'H⟩ := exists_invariant_compl hHF (fun x hx => hWE x hx)
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  have hr : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hr⟩
  have hrp : ringChar F ≠ p := fun h => hpF (by rw [← h]; exact ringChar.Nat.cast_ringChar)
  have hp' : ∀ V : Submodule F (Fin n → F), ¬ p ∣ Nat.card ((unipRadSL V).map π) := fun V hd =>
    not_dvd_card_of_isPGroup' hrp (isPGroup_unipRadSL V) (hd.trans (Subgroup.card_map_dvd _ π))
  have hnorm : ∀ V : Submodule F (Fin n → F),
      (∀ x ∈ H, ∀ w ∈ V, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ V) →
      ∀ e ∈ E, ∀ s ∈ (unipRadSL V).map π, e * s * e⁻¹ ∈ (unipRadSL V).map π := by
    rintro V hV e he _ ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := hπ e
    have haH : a ∈ H := he
    have hmem := (Subgroup.mem_normalizer_iff.1 (le_normalizer_unipRadSL hV haH) u).1 hu
    exact ⟨a * u * a⁻¹, hmem, by simp⟩
  refine ⟨(unipRadSL W).map π, (unipRadSL W').map π, hp' W, hp' W',
    hnorm W (fun x hx => hWE x hx), hnorm W' hW'H, ?_⟩
  set L := (unipRadSL W).map π ⊔ (unipRadSL W').map π with hL
  have htop : L.comap π = ⊤ := eq_top_of_unip_isCompl hc hW0 hW'0
    (fun g hg => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨g, (mem_unipRadSL).2 hg, rfl⟩))
    (fun g hg => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨g, (mem_unipRadSL).2 hg, rfl⟩))
  rw [← Subgroup.map_comap_eq_self_of_surjective hπ L, htop, Subgroup.map_top_of_surjective _ hπ]

end Linear

theorem pow_eq_one_of_mem_map_innerImage {K P : Type*} [Group K] [Group P] {p : ℕ}
    {E : Subgroup (MulAut K)} (hE : ∀ f ∈ E, f ^ p = 1) (φ : K ⧸ Subgroup.center K →* P) :
    ∀ x ∈ (innerImage E).map φ, x ^ p = 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_pow, pow_eq_one_of_mem_innerImage hE hs, map_one]

theorem isPGroup_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hH : ∀ x ∈ H, x ^ p = 1) : IsPGroup p H :=
  fun x => ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hH x x.2, Subgroup.coe_one])⟩

theorem seitzHyperGamma_eq_top_of_linearReducible {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ Subgroup.center K ≃* Cat d) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    (hred : LinearReducible d p ((innerImage E).map e.toMonoidHom)) :
    seitzHyperGamma p E = ⊤ := by
  obtain ⟨n, F, _, _, e', hpF, W, hW0, hWt, hWE⟩ := hred
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hW0 (Submodule.eq_bot_of_subsingleton)
  have hEp := isPGroup_of_pow_eq_one
    (pow_eq_one_of_mem_map_innerImage (fun f hf => hE.2 f hf) (e.trans e').toMonoidHom)
  obtain ⟨H₁, H₂, hp₁, hp₂, hn₁, hn₂, hgen⟩ := exists_p'Subgroups_psl hp hpF hn hEp hW0 hWt
    (fun x hx w hw => hWE x (by
      obtain ⟨s, hs, hsx⟩ := hx
      exact ⟨e s, ⟨s, hs, rfl⟩, hsx⟩) w hw)
  exact seitzHyperGamma_eq_top_of_inner_equiv hperf hp (e.trans e') hE hE1 hinn hp₁ hp₂ hn₁ hn₂
    hgen

theorem exists_p'Subgroups_unitary {Kf : Type} [Field Kf] [Finite Kf] {σ : Kf ≃+* Kf} {n : ℕ}
    {P : Type} [Group P] {π : SUid σ n →* P} (hc : IsUnitaryCover σ π) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : Kf) ≠ 0) {E : Subgroup P} (hE : ∀ x ∈ E, x ^ p = 1)
    {W : Submodule Kf (Fin n → Kf)} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hstab : ∀ g : SUid σ n, π g ∈ E → ∀ w ∈ W, g • w ∈ W) :
    ∃ H₁ H₂ : Subgroup P, ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ ∧
      (∀ e ∈ E, ∀ s ∈ H₁, e * s * e⁻¹ ∈ H₁) ∧ (∀ e ∈ E, ∀ s ∈ H₂, e * s * e⁻¹ ∈ H₂) ∧
      H₁ ⊔ H₂ = ⊤ := by
  classical
  set Et : Subgroup (SUid σ n) := E.comap π with hEt
  have hEtcard : ((Nat.card Et : ℕ) : Kf) ≠ 0 :=
    natCast_card_comap_ne_zero (by have := hc.two_le; omega) π hc.ker_scalar hp hpK hE
  have hWs : ∀ g ∈ Et, ∀ w ∈ W, g • w ∈ W := fun g hg w hw => hstab g hg w hw
  obtain ⟨W', hW', hcompl, hW's⟩ := exists_opposite hc.involution hEtcard hW hWs
  have hp' : ∀ {X : Submodule Kf (Fin n → Kf)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      ¬ p ∣ Nat.card ((uRad σ X hX).map π) := fun hX hd =>
    not_dvd_card_uRad hp hp2 hpK (hd.trans (Subgroup.card_map_dvd _ π))
  have hnorm : ∀ {X : Submodule Kf (Fin n → Kf)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      (∀ g ∈ Et, ∀ w ∈ X, g • w ∈ X) →
      ∀ e ∈ E, ∀ v ∈ (uRad σ X hX).map π, e * v * e⁻¹ ∈ (uRad σ X hX).map π := by
    intro X hX hXs e he v hv
    obtain ⟨a, rfl⟩ := hc.surjective e
    obtain ⟨q', hq', rfl⟩ := hv
    have haEt : a ∈ Et := he
    exact ⟨a * q' * a⁻¹, uRad_conj_mem (fun w hw => hXs a haEt w hw)
      (fun w hw => hXs a⁻¹ (Et.inv_mem haEt) w hw) hq', by simp⟩
  refine ⟨(uRad σ W hW).map π, (uRad σ W' hW').map π, hp' hW, hp' hW', hnorm hW hWs,
    hnorm hW' hW's, ?_⟩
  set L := (uRad σ W hW).map π ⊔ (uRad σ W' hW').map π with hL
  have htop : L.comap π = ⊤ :=
    eq_top_of_uRad_of_opposite hc.involution hc.two_le hc.exists_norm hW0 hW hW' hcompl
      (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨q, hq, rfl⟩))
      (fun q hq => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨q, hq, rfl⟩))
  rw [← Subgroup.map_comap_eq_self_of_surjective hc.surjective L, htop,
    Subgroup.map_top_of_surjective _ hc.surjective]

theorem seitzHyperGamma_eq_top_of_uReducible {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (e : K ⧸ Subgroup.center K ≃* Cat d) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    (hred : UReducible d p ((innerImage E).map e.toMonoidHom)) :
    seitzHyperGamma p E = ⊤ := by
  obtain ⟨n, Kf, _, _, σ, π, hc, hpK, W, hW0, hWiso, hWstab⟩ := hred
  obtain ⟨H₁, H₂, hp₁, hp₂, hn₁, hn₂, hgen⟩ := exists_p'Subgroups_unitary hc hp hp2 hpK
    (pow_eq_one_of_mem_map_innerImage (fun f hf => hE.2 f hf) e.toMonoidHom) hW0 hWiso hWstab
  exact seitzHyperGamma_eq_top_of_inner_equiv hperf hp e hE hE1 hinn hp₁ hp₂ hn₁ hn₂ hgen

@[expose] def InnerReducible {K : Type*} [Group K] (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut K)) : Prop :=
  E ≤ (MulAut.conj : K →* MulAut K).range ∧ ∃ e : K ⧸ Subgroup.center K ≃* Cat d,
    LinearReducible d p ((innerImage E).map e.toMonoidHom) ∨
      UReducible d p ((innerImage E).map e.toMonoidHom)

theorem seitzHyperGamma_eq_top_of_innerReducible {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (h : InnerReducible d p E) : seitzHyperGamma p E = ⊤ := by
  obtain ⟨hinn, e, hL | hU⟩ := h
  · exact seitzHyperGamma_eq_top_of_linearReducible hperf hp e hE hE1 hinn hL
  · exact seitzHyperGamma_eq_top_of_uReducible hperf hp hp2 e hE hE1 hinn hU

section InnerImage

variable {K : Type*} [Group K]

theorem mem_center_of_conj_eq_one {k : K} (h : MulAut.conj k = 1) : k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut K => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem ker_conj : (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext k
  rw [MonoidHom.mem_ker]
  refine ⟨mem_center_of_conj_eq_one, fun hk => ?_⟩
  ext g
  rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.1 hk g), mul_inv_cancel_right]

theorem exists_hyperplane_of_innerImage {p : ℕ} {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) {F₀ : Subgroup (K ⧸ Subgroup.center K)}
    (hF₀ : F₀ ≤ innerImage E) (hrel : F₀.relIndex (innerImage E) = p) :
    ∃ F ≤ E, F.relIndex E = p ∧
      ∀ f ∈ F, ∃ k : K, MulAut.conj k = f ∧ (k : K ⧸ Subgroup.center K) ∈ F₀ := by
  set H := E.comap (MulAut.conj : K →* MulAut K) with hH
  set L := F₀.comap (QuotientGroup.mk' (Subgroup.center K)) with hL
  have hZH : Subgroup.center K ≤ H ⊓ L := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show MulAut.conj z ∈ E
      rw [show MulAut.conj z = 1 from by rw [← MonoidHom.mem_ker, ker_conj]; exact hz]
      exact E.one_mem
    · show QuotientGroup.mk' (Subgroup.center K) z ∈ F₀
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
      exact F₀.one_mem
  have hrel1 : ((H ⊓ L).map (MulAut.conj : K →* MulAut K)).relIndex
      (H.map (MulAut.conj : K →* MulAut K)) = (H ⊓ L).relIndex H := by
    rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ker_conj, sup_of_le_left hZH]
  have hrel2 : ((H ⊓ L).map (QuotientGroup.mk' (Subgroup.center K))).relIndex
      (H.map (QuotientGroup.mk' (Subgroup.center K))) = (H ⊓ L).relIndex H := by
    rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_of_le_left hZH]
  have hF₀eq : (H ⊓ L).map (QuotientGroup.mk' (Subgroup.center K)) = F₀ := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hF₀ hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hEeq : H.map (MulAut.conj : K →* MulAut K) = E := Subgroup.map_comap_eq_self hinn
  refine ⟨(H ⊓ L).map MulAut.conj, ?_, ?_, ?_⟩
  · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    exact hx
  · calc ((H ⊓ L).map (MulAut.conj : K →* MulAut K)).relIndex E
        = ((H ⊓ L).map (MulAut.conj : K →* MulAut K)).relIndex
            (H.map (MulAut.conj : K →* MulAut K)) := by rw [hEeq]
      _ = (H ⊓ L).relIndex H := hrel1
      _ = ((H ⊓ L).map (QuotientGroup.mk' (Subgroup.center K))).relIndex
            (H.map (QuotientGroup.mk' (Subgroup.center K))) := hrel2.symm
      _ = F₀.relIndex (innerImage E) := by rw [hF₀eq]; rfl
      _ = p := hrel
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact ⟨x, rfl, hx⟩

theorem isElemAbelian_innerImage {p : ℕ} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) :
    IsElemAbelian p (innerImage E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun s hs => pow_eq_one_of_mem_innerImage (fun f hf => hE.2 f hf) hs⟩
  obtain ⟨x, hx, hxa⟩ := a.2
  obtain ⟨y, hy, hyb⟩ := b.2
  have hc : MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hz : (y * x)⁻¹ * (x * y) ∈ Subgroup.center K := by
    rw [← ker_conj, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc, inv_mul_cancel]
  apply Subtype.ext
  show (a : K ⧸ Subgroup.center K) * b = b * a
  rw [← hxa, ← hyb, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq.2 hz).symm

theorem innerImage_ne_bot {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) (hE1 : E ≠ ⊥) : innerImage E ≠ ⊥ := by
  intro h
  apply hE1
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨k, rfl⟩ := hinn hf
  have hk : (k : K ⧸ Subgroup.center K) = 1 := by
    have : (k : K ⧸ Subgroup.center K) ∈ innerImage E := mk_mem_innerImage hf
    rwa [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, show MulAut.conj k = 1 from by
    rw [← MonoidHom.mem_ker, ker_conj]; exact (QuotientGroup.eq_one_iff k).1 hk]

end InnerImage

theorem le_hyperClosure_of_normalized' {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    {E : Subgroup P} (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) {Q : Subgroup P}
    (hnorm : ∀ e ∈ E, ∀ v ∈ Q, e * v * e⁻¹ ∈ Q) (hQp : ¬ p ∣ Nat.card Q) :
    Q ≤ Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧ ∃ F₀ : Subgroup P, F₀ ≤ E ∧
      F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p E := isElementaryAbelian_of_isElemAbelian hE
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hE1
  have hAV : E ≤ Subgroup.normalizer (Q : Set P) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
    have := hnorm e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
    (V := Q) hAV hQp
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  intro k hk
  rw [Subgroup.mem_inf] at hk
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, B.map E.subtype,
    Subgroup.map_subtype_le B, ?_, fun f hf => Subgroup.mem_centralizer_iff.1 hk.2 f hf⟩
  have hsub : (B.map E.subtype).subgroupOf E = B :=
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective B
  rw [Subgroup.relIndex, hsub]
  exact hB

theorem closure_hyperRSet_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {r p : ℕ} {A : Subgroup G}
    (h : (⊤ : Subgroup G') ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤
      (A.map e.toMonoidHom) r p)) :
    (⊤ : Subgroup G) ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ A r p) := by
  have hA : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp
  have hS : e.symm.toMonoidHom '' CFSG.LieType.Chevalley.hyperRSet ⊤ (A.map e.toMonoidHom) r p ⊆
      CFSG.LieType.Chevalley.hyperRSet ⊤ A r p := by
    rintro _ ⟨y, ⟨-, ⟨n, hn⟩, B, hB, hBi, hyB⟩, rfl⟩
    refine ⟨Subgroup.mem_top _, ⟨n, by rw [← map_pow, hn, map_one]⟩,
      B.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rw [← hA]
      exact Subgroup.map_mono hB
    · rw [← hA, Subgroup.relIndex_map_map_of_injective _ _ e.symm.injective, hBi]
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyB b hb]
  intro x _
  have hx := h (Subgroup.mem_top (e x))
  have hle : (Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (A.map e.toMonoidHom) r p)).map
      e.symm.toMonoidHom ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ A r p) := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hS
  exact hle (Subgroup.mem_map.2 ⟨e x, hx, (by simp : e.symm.toMonoidHom (e x) = x)⟩)

theorem seitzHyperGamma_eq_top_of_rGen {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    (h : (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (innerImage E) r p)) :
    seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine seitzHyperGamma_eq_top_of_quot hperf (isPGroup_of_isElemAbelian hE)
    (h.trans (Subgroup.closure_mono ?_))
  rintro s ⟨-, ⟨n, hn⟩, B, hB, hBi, hsB⟩
  refine ⟨Or.inr ⟨r ^ n, fun hd => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1
    (hp.dvd_of_dvd_pow hd)).symm, hn⟩, ?_⟩
  obtain ⟨F, hFE, hFrel, hF⟩ := exists_hyperplane_of_innerImage hinn hB hBi
  refine ⟨F, hFE, hFrel, fun f hf => ?_⟩
  obtain ⟨k, rfl, hk⟩ := hF f hf
  rw [quotAut_conj, Subgroup.mem_centralizer_iff.1 hsB _ hk, mul_inv_cancel_right]

theorem commutator_range_eq_of_perfect {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (φ : A →* B) : ⁅φ.range, φ.range⁆ = φ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem exists_hyperplane_eq_of_hom_pow {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : E, x ^ p = 1) {k : ℕ} (hk : 1 ≤ k) (hcard : Nat.card E = p ^ k) {F : Type*}
    [Field F] (χ ψ : E →* F) : ∃ H : Subgroup E, H.index = p ∧ ∀ x ∈ H, χ x = ψ x := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  let ρ : E →* Fˣ := χ.toHomUnits / ψ.toHomUnits
  have hρ : ∀ x, ρ x = 1 → χ x = ψ x := by
    intro x hx
    have h1 : (χ.toHomUnits x : F) = ψ.toHomUnits x := by
      have : χ.toHomUnits x / ψ.toHomUnits x = 1 := hx
      rw [div_eq_one] at this
      rw [this]
    simpa using h1
  have hrange : Nat.card ρ.range ≤ p := by
    have hle : ρ.range ≤ rootsOfUnity p F := by
      rintro _ ⟨x, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, hexp x, map_one]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F p)
  have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hdvd : ρ.ker.index ∣ p ^ k := hcard ▸ ρ.ker.index_dvd_card
  obtain ⟨j, hj, hjj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  interval_cases j
  · rw [pow_zero, Subgroup.index_eq_one] at hjj
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := k - 1)
      (by rw [hcard]; exact pow_dvd_pow p (by omega))
    refine ⟨H, ?_, fun x _ => hρ x (by rw [← MonoidHom.mem_ker, hjj]; exact Subgroup.mem_top x)⟩
    have h := H.card_mul_index
    rw [hH, hcard] at h
    have h' : p ^ (k - 1) * H.index = p ^ (k - 1) * p := by
      rw [h, ← pow_succ]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h'
  · exact ⟨ρ.ker, by rw [hjj, pow_one], fun x hx => hρ x hx⟩

@[expose] def InnerUDiag {K : Type*} [Group K] (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut K)) : Prop :=
  E ≤ (MulAut.conj : K →* MulAut K).range ∧ ∃ e : K ⧸ Subgroup.center K ≃* Cat d,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.UDiagLift d p ((innerImage E).map e.toMonoidHom)

section UnitaryDiag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel

theorem seitzHyperGamma_eq_top_of_innerUDiag {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (hUD : InnerUDiag d p E) : seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨hinn, e, ℓ, f, n, Kf, _, h, π, hπ, hker, hpq, hq, hcomm, hpow⟩ := hUD
  set E₀ : Subgroup (Cat d) := (innerImage E).map e.toMonoidHom with hE₀def
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hE₀ : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p (isElemAbelian_innerImage hE) _
  have hE₀1 : E₀ ≠ ⊥ := fun h0 =>
    innerImage_ne_bot hinn hE1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h0)
  haveI : Finite E₀ :=
    Finite.of_surjective (fun x : innerImage E => (⟨e x, ⟨x, x.2, rfl⟩⟩ : E₀)) (by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE₀).exists_card_eq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pow_zero] at hk
      exact absurd (Subgroup.eq_bot_of_card_eq _ hk) hE₀1
    · exact hpos
  set Eh : Subgroup (unitarySU ℓ f Kf (n + 1)) := E₀.comap π with hEh
  have hle : unitarySU ℓ f Kf (n + 1) ≤ primeFormUnitary h (idGram Kf (n + 1)) :=
    unitarySU_le_primeFormUnitary h
  let Gu : Subgroup (primeFormUnitary h (idGram Kf (n + 1))) := Eh.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ Gu, ∀ v ∈ Gu, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x y hx hy]
  have hGpow : ∀ u ∈ Gu, u ^ (ℓ ^ f + 1) = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hdvdK : ℓ ^ f + 1 ∣ Nat.card Kf - 1 := by
    have h1 : Nat.card Kf - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvdK
  haveI : NeZero (ℓ ^ f + 1) := ⟨by omega⟩
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hζ dvd_rfl Gu hGcomm hGpow
  let Pg : GL (Fin (n + 1)) Kf := (P : GL (Fin (n + 1)) Kf)
  let Dg : unitarySU ℓ f Kf (n + 1) → GL (Fin (n + 1)) Kf := fun x =>
    Pg⁻¹ * ((x : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg
  have hdiag : ∀ x : Eh,
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf).IsDiag :=
    fun x => hP (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : unitarySU ℓ f Kf (n + 1), Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → Eh →* Kf := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : Eh) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  let π' : Eh →* E₀ := (π.comp Eh.subtype).codRestrict E₀ fun x => x.2
  have hπ' : Function.Surjective π' := by
    rintro ⟨e', he'⟩
    obtain ⟨g, hg⟩ := hπ e'
    exact ⟨⟨g, show π g ∈ E₀ by rw [hg]; exact he'⟩, Subtype.ext hg⟩
  have hπ'v : ∀ x : Eh, ((π' x : E₀) : Cat d) = π x := fun _ => rfl
  have hscal : ∀ x : Eh, π' x = 1 → ∀ a b : Fin (n + 1), χ a x = χ b x := by
    intro x hx a b
    have hx' : (x : unitarySU ℓ f Kf (n + 1)) ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ'v, hx]
      rfl
    obtain ⟨c, hc⟩ := hker _ hx'
    have hD : ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = c • 1 := by
      have hPinv : ((Pg⁻¹ : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) *
          (Pg : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = 1 := Units.inv_mul _
      simp only [Dg, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPinv]
    show ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) a a =
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) b b
    rw [hD]
    simp
  have hexpE : ∀ x : E₀, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE₀.2 x x.2)
  have hhyper : ∀ i : Fin n, ∃ H : Subgroup E₀, H.index = p ∧ ∀ x : Eh, π' x ∈ H →
      χ i.castSucc x = χ i.succ x := by
    intro i
    let ρ : Eh →* Kfˣ := (χ i.castSucc).toHomUnits / (χ i.succ).toHomUnits
    have hkerρ : π'.ker ≤ ρ.ker := fun x hx =>
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
        _ _ x).2 (hscal x hx _ _)
    let ρb : E₀ →* Kfˣ := (QuotientGroup.lift π'.ker ρ hkerρ).comp
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm.toMonoidHom
    have hρb : ∀ x : Eh, ρb (π' x) = ρ x := by
      intro x
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x) =
          (x : Eh ⧸ π'.ker) := (MulEquiv.symm_apply_eq _).2 rfl
      show QuotientGroup.lift π'.ker ρ hkerρ
        ((QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x)) = ρ x
      rw [h1]
      rfl
    obtain ⟨H, hH, hHeq⟩ := exists_hyperplane_eq_of_hom_pow hp hexpE hk1 hk
      ((Units.coeHom Kf).comp ρb) 1
    refine ⟨H, hH, fun x hx => ?_⟩
    have h1 : ρb (π' x) = 1 := Units.ext (by simpa using hHeq _ hx)
    rw [hρb] at h1
    exact (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
      _ _ x).1 h1
  let φ := conjSU h P
  let ε : Su Kf ℓ f (n + 1) ≃* unitarySU ℓ f Kf (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su Kf ℓ f 2 →* unitarySU ℓ f Kf (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 Kf ℓ f n i)
  let g : Fin n → (Su Kf ℓ f 2 →* K ⧸ Subgroup.center K) := fun i =>
    e.symm.toMonoidHom.comp (π.comp (φ.toMonoidHom.comp (ι i)))
  have hq4 : 4 ≤ ℓ ^ f := by
    have h2 : 2 ≤ ℓ ^ f := le_trans h.prime.two_le (Nat.le_self_pow (by have := h.one_le; omega) ℓ)
    rcases (by omega : ℓ ^ f = 2 ∨ ℓ ^ f = 3 ∨ 4 ≤ ℓ ^ f) with h2' | h3 | h4
    · exact absurd h2' hq
    · rw [h3] at hpq
      have : p ∣ 2 ^ 2 := by norm_num; exact hpq
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
        hp2
    · exact h4
  haveI : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ f) Kf) :=
    CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two h.card_eq_sq hq4
  let ε₂ : Su Kf ℓ f 2 ≃* CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ f) Kf :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq 2)
  haveI : Group.IsPerfect (Su Kf ℓ f 2) :=
    Group.IsPerfect.ofSurjective (f := ε₂.symm.toMonoidHom) ε₂.symm.surjective
  refine seitzHyperGamma_eq_top_of_perfect hperf (Set.range fun i => (g i).range) ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact commutator_range_eq_of_perfect (g i)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨H, hH, hHc⟩ := hhyper i
    set F₀ : Subgroup (K ⧸ Subgroup.center K) := (H.map E₀.subtype).map e.symm.toMonoidHom
      with hF₀
    have hmapE : E₀.map e.symm.toMonoidHom = innerImage E := by
      rw [hE₀def, Subgroup.map_map]
      convert Subgroup.map_id (innerImage E)
      ext x
      simp
    have hF₀le : F₀ ≤ innerImage E := by
      rw [← hmapE]
      exact Subgroup.map_mono (Subgroup.map_subtype_le H)
    have hF₀rel : F₀.relIndex (innerImage E) = p := by
      rw [← hmapE, hF₀, Subgroup.relIndex_map_map_of_injective _ _ e.symm.injective,
        Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E₀.subtype_injective]
      exact hH
    obtain ⟨F, hFE, hFrel, hF⟩ := exists_hyperplane_of_innerImage hinn hF₀le hF₀rel
    refine ⟨F, hFE, hFrel, fun f' hf' s hs => ?_⟩
    obtain ⟨k', rfl, hk'⟩ := hF f' hf'
    obtain ⟨a, rfl⟩ := hs
    rw [quotAut_conj]
    obtain ⟨z, ⟨w, hwH, rfl⟩, hzk⟩ := hk'
    obtain ⟨x, rfl⟩ := hπ' w
    have hxχ := hHc x hwH
    have hcx : (x : unitarySU ℓ f Kf (n + 1)) * φ (ι i a) =
        φ (ι i a) * (x : unitarySU ℓ f Kf (n + 1)) := by
      set yb : unitarySU ℓ f Kf (n + 1) := ι i a with hyb
      have hA : (((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = blockMat (n + 1) i
            (((a : Su Kf ℓ f 2) : GL (Fin 2) Kf) : Matrix (Fin 2) (Fin 2) Kf) := rfl
      have hD : ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) =
          Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) Kf) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c) := ((hdiag x).diagonal_diag).symm
      have hYD : ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Dg x =
          Dg x * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hA, hD]
        exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp)
          (by simp) hxχ _
      have hxeq : ((x : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) = Pg * Dg x * Pg⁻¹ := by
        simp [Dg, mul_assoc]
      apply Subtype.ext
      show ((x : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) *
          (Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹) =
        Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹ *
          ((x : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf)
      rw [hxeq]
      calc Pg * Dg x * Pg⁻¹ * (Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹)
          = Pg * (Dg x * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf)) * Pg⁻¹ := by
            group
        _ = Pg * (((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Dg x) * Pg⁻¹ := by
            rw [hYD]
        _ = Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹ *
            (Pg * Dg x * Pg⁻¹) := by group
    have hc' : e.symm (π x) * g i a = g i a * e.symm (π x) := by
      show e.symm (π x) * e.symm (π (φ (ι i a))) = e.symm (π (φ (ι i a))) * e.symm (π x)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcx]
    rw [← hzk]
    show e.symm (π x) * g i a * (e.symm (π x))⁻¹ = g i a
    rw [hc', mul_inv_cancel_right]
  ·
    have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
      have h1 := iSup_range_blockEmb2 (K := Kf) (p := ℓ) (f := f) h.card_eq_sq hq n
      have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
      rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
      simpa [ι, MonoidHom.range_comp] using h2
    have hrange : ∀ i, (g i).range =
        (((ι i).range.map φ.toMonoidHom).map π).map e.symm.toMonoidHom := by
      intro i
      simp only [g, MonoidHom.range_comp, Subgroup.map_map]
    rw [iSup_range, show (⨆ i, (g i).range) = ((⨆ i, (ι i).range).map φ.toMonoidHom |>.map π).map
        e.symm.toMonoidHom by
      simp only [hrange, Subgroup.map_iSup], hgen,
      Subgroup.map_top_of_surjective _ φ.surjective, Subgroup.map_top_of_surjective _ hπ,
      Subgroup.map_top_of_surjective _ e.symm.surjective]

end UnitaryDiag

section LinearDiag

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_invariant_compl_gl [Finite F] {G : Subgroup (GL (Fin n) F)}
    (hG : (Nat.card G : F) ≠ 0) {W : Submodule F (Fin n → F)}
    (hW : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    ∃ W' : Submodule F (Fin n → F), IsCompl W W' ∧
      ∀ g ∈ G, ∀ w ∈ W', (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ W' := by
  have : NeZero (Nat.card G : F) := ⟨hG⟩
  let ρ : Representation F G (Fin n → F) :=
    { toFun := fun g => Matrix.toLin' ((g.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      map_one' := LinearMap.ext fun v => by simp
      map_mul' := fun a b => LinearMap.ext fun v => by
        simp [Matrix.toLin'_mul] }
  let σ : Subrepresentation ρ := ⟨W, fun g v hv => hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => σ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hσ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hσ'.2)
    exact this

theorem conj_gl_mem_thetaSpace {W : Submodule F (Fin n → F)} {g : GL (Fin n) F}
    (hg : ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    (hg' : ∀ w ∈ W, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    {φ : Matrix (Fin n) (Fin n) F} (hφ : φ ∈ thetaSpace W) :
    (g : Matrix (Fin n) (Fin n) F) * φ * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈
      thetaSpace W := by
  rw [mem_thetaSpace] at hφ ⊢
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hg _ (hφ.1 _)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hφ.2 _ (hg' w hw), Matrix.mulVec_zero]

@[expose] noncomputable def glConj (g : GL (Fin n) F) (s : SpecialLinearGroup (Fin n) F) :
    SpecialLinearGroup (Fin n) F :=
  ⟨(g : Matrix (Fin n) (Fin n) F) * s * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), by
    rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_glConj (g : GL (Fin n) F) (s : SpecialLinearGroup (Fin n) F) :
    ((glConj g s : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * s * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

end LinearDiag

@[expose] def DiagReducible {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (ι : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin n) F)
    (G : Subgroup (GL (Fin n) F)), (Nat.card G : F) ≠ 0 ∧ (p : F) ≠ 0 ∧
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) ∧
      ∀ f ∈ E, ∃ g ∈ G, ∀ s : SpecialLinearGroup (Fin n) F,
        ι (quotAut f (ι.symm (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
          s))) = QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) (glConj g s)

theorem seitzHyperGamma_eq_top_of_diagReducible {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) (h : DiagReducible p E) : seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨n, F, _, _, ι, G, hGc, hpF, W, hW0, hWt, hWG, hEG⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) F) with hZ
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨W', hc, hW'G⟩ := exists_invariant_compl_gl hGc hWG
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  have hr : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hr⟩
  have hrp : ringChar F ≠ p := fun h => hpF (by rw [← h]; exact ringChar.Nat.cast_ringChar)
  have hp' : ∀ V : Submodule F (Fin n → F), ¬ p ∣ Nat.card ((unipRadSL V).map π) := fun V hd =>
    not_dvd_card_of_isPGroup' hrp (isPGroup_unipRadSL V) (hd.trans (Subgroup.card_map_dvd _ π))
  let H : Submodule F (Fin n → F) → Subgroup (K ⧸ Subgroup.center K) := fun V =>
    ((unipRadSL V).map π).map ι.symm.toMonoidHom
  have hHcard : ∀ V, Nat.card (H V) = Nat.card ((unipRadSL V).map π) := fun V =>
    Subgroup.card_map_of_injective ι.symm.injective
  have hstab : ∀ V : Submodule F (Fin n → F),
      (∀ g ∈ G, ∀ w ∈ V, (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ V) →
      ∀ f ∈ E, ∀ s ∈ H V, quotAut f s ∈ H V := by
    rintro V hV f hf _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgs⟩ := hEG f hf
    refine ⟨π (glConj g u), ⟨glConj g u, ?_, rfl⟩, ?_⟩
    · have hu' : u ∈ unipRadSL V := hu
      rw [SetLike.mem_coe, mem_unipRadSL]
      rw [mem_unipRadSL] at hu'
      have e : ((glConj g u : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
          (g : Matrix (Fin n) (Fin n) F) * ((u : Matrix (Fin n) (Fin n) F) - 1) *
            ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [coe_glConj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul,
          mul_inv_cancel, Units.val_one]
      rw [e]
      exact conj_gl_mem_thetaSpace (hV g hg) (hV g⁻¹ (G.inv_mem hg)) hu'
    · show ι.symm (π (glConj g u)) = quotAut f (ι.symm (π u))
      rw [← hgs u, MulEquiv.symm_apply_apply]
  have hgen : (unipRadSL W).map π ⊔ (unipRadSL W').map π = ⊤ := by
    set L := (unipRadSL W).map π ⊔ (unipRadSL W').map π with hL
    have htop : L.comap π = ⊤ := eq_top_of_unip_isCompl hc hW0 hW'0
      (fun g hg => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨g, (mem_unipRadSL).2 hg, rfl⟩))
      (fun g hg => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨g, (mem_unipRadSL).2 hg, rfl⟩))
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ L, htop, Subgroup.map_top_of_surjective _ hπ]
  refine seitzHyperGamma_eq_top_of_p'Subgroups hperf hE hE1 {H W, H W'} ?_ ?_ ?_
  · intro V hV
    rcases hV with rfl | hV
    · rw [hHcard]; exact hp' W
    · rw [Set.mem_singleton_iff.1 hV, hHcard]; exact hp' W'
  · intro V hV
    rcases hV with rfl | hV
    · exact hstab W hWG
    · rw [Set.mem_singleton_iff.1 hV]
      exact hstab W' hW'G
  · rw [iSup_insert, iSup_singleton, ← Subgroup.map_sup, hgen,
      Subgroup.map_top_of_surjective _ ι.symm.surjective]

@[expose] def CoverScope {K : Type*} [Group K] (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut K)) : Prop :=
  InnerReducible d p E ∨ InnerUDiag d p E ∨ DiagReducible p E

theorem seitzHyperGamma_eq_top_of_coverScope {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (h : CoverScope d p E) : seitzHyperGamma p E = ⊤ := by
  rcases h with h | h | h
  · exact seitzHyperGamma_eq_top_of_innerReducible hperf hp hp2 hE hE1 h
  · exact seitzHyperGamma_eq_top_of_innerUDiag hperf hp hp2 hE hE1 h
  · exact seitzHyperGamma_eq_top_of_diagReducible hperf hp hE hE1 h

end CFSG.LieType.SeitzGeneration.QuasiHigh
