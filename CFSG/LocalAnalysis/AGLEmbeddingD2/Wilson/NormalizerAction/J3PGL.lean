module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3PGLAbstract
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3PGLElement
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverConsumers
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3Involution

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.RankThree.Asc83Table
open scoped commutatorElement

theorem centralizer_sup_center {X : Type*} [Group X] (a : X) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.center X : Subgroup X) : Set X) =
      Subgroup.centralizer ({a} : Set X) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h g (Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  · intro h g hg
    have hle : Subgroup.zpowers a ⊔ Subgroup.center X ≤ Subgroup.centralizer ({x} : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact h a rfl
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 hz x).symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    exact this

theorem card_normalizer_sup_center_le {X : Type*} [Group X] [Finite X] {a : X}
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    (hord : orderOf (a : X ⧸ Subgroup.center X) = 3)
    (hcQ : Nat.card (Subgroup.centralizer ({(a : X ⧸ Subgroup.center X)} :
      Set (X ⧸ Subgroup.center X))) = 1080) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.center X : Subgroup X) : Set X))
      ≤ 6480 := by
  set D : Subgroup X := Subgroup.zpowers a ⊔ Subgroup.center X with hD
  set N : Subgroup X := Subgroup.normalizer (D : Set X) with hN
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  have hZD : Subgroup.center X ≤ D := le_sup_right
  have hZN : Subgroup.center X ≤ N := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have := Subgroup.mem_center_iff.1 hz d
    have e : z * d * z⁻¹ = d := by rw [← this]; group
    rw [e]
  have hmapD : D.map π = Subgroup.zpowers (π a) := by
    rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers,
      (Subgroup.map_eq_bot_iff _).2 hker.ge, sup_bot_eq]
  have hcomap : (D.map π).comap π = D := Subgroup.comap_map_eq_self (hker.le.trans hZD)
  set ψ : ↥N →* X ⧸ Subgroup.center X := π.comp N.subtype with hψ
  have hkerψ : ψ.ker = (Subgroup.center X).subgroupOf N := by
    ext ⟨w, hw⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff w
  have hk3 : Nat.card ψ.ker = 3 := by
    rw [hkerψ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZ3]
  have hrange : ψ.range ≤ Subgroup.normalizer ((Subgroup.zpowers (π a) : Subgroup _) : Set _) := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    rw [← hmapD]
    exact Subgroup.le_normalizer_map π ⟨n, hn, rfl⟩
  have hbound := card_normalizer_zpowers_le (X := X ⧸ Subgroup.center X) (q := π a) hord
  have hcQ' : Nat.card (Subgroup.centralizer ({π a} : Set (X ⧸ Subgroup.center X))) = 1080 := hcQ
  have hr : Nat.card ψ.range ≤ 2160 := by
    calc Nat.card ψ.range ≤ Nat.card ↥(Subgroup.normalizer
          ((Subgroup.zpowers (π a) : Subgroup _) : Set _)) := Subgroup.card_le_of_le hrange
      _ ≤ 2 * 1080 := by rw [← hcQ']; exact hbound
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hk3] at this
  omega

section Main


set_option linter.unusedSectionVars false
set_option maxRecDepth 20000 in
theorem exists_pgl_u {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3)
    {F : Subgroup X} (hF : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81)
    {F₁ : Subgroup X} (hF₁F : F₁ ≤ F) (hF₁27 : Nat.card F₁ = 27)
    (hF₁inv : ∀ y ∈ normalizer (F : Set X), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁)
    {a : X} (haF : a ∈ F) (haF₁ : a ∉ F₁)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ (u : X) (I : Subgroup X), u ∈ normalizer (F : Set X) ∧ orderOf u = 8 ∧
      u ∈ normalizer ((zpowers a ⊔ center X : Subgroup X) : Set X) ∧
      u ∉ centralizer ({a} : Set X) ∧ I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      ((∃ τ ∈ normalizer ((zpowers a ⊔ center X : Subgroup X) : Set X),
        τ ∉ centralizer ({a} : Set X) ∧ τ ^ 2 = 1) → IsPGL29 (I ⊔ zpowers u) I) := by
  obtain ⟨k, hk, hFk, hnorm, hcard⟩ := j3_frame_card gammaWordFacts_holds hX hZ3 e hF hZF hF81
  subst hFk
  have hinvk : ∀ y ∈ Subgroup.closure (Set.range k), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁ :=
    fun y hy => hF₁inv y (hk.closure_le_normalizer hy)
  have hcen := hk.zpowers_xB3_eq_center hZ3
  have hF₁eq : F₁ = F1 k := by
    rcases hk.invariant_F0 F₁ hF₁F hinvk with h0 | h0 | h0 | h0
    · rw [h0] at hF₁27; simp at hF₁27
    · rw [h0, hcen, hZ3] at hF₁27; omega
    · exact h0
    · rw [h0, hk.card_F0] at hF₁27; omega
  have hZF₁ : center X ≤ F1 k := by
    rw [← hcen, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨v, rfl⟩ := hk.exists_phi haF
  have hv0 : v 0 ≠ 0 := fun h0 => haF₁ (hF₁eq ▸ hk.phi_mem_F1 h0)
  have ha_ne : hk.phi v ∉ center X := fun hmem => haF₁ (hF₁eq ▸ hZF₁ hmem)
  have ha3 : hk.phi v ^ 3 ∈ center X := by
    have h3 := (isElementaryAbelian_iff.1 hk.isElementaryAbelian_F0).2 _ haF
    rw [h3]; exact Subgroup.one_mem _
  obtain ⟨u, huk, hu8, huD, hune⟩ := hk.exists_u hcard v hv0
  obtain ⟨I, hIC, hIperf, heI, hImax, hC3240, hD9, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Cover hX hZ3 e ha_ne ha3 h5
  set a : X := hk.phi v with ha_def
  set D : Subgroup X := zpowers a ⊔ center X with hD
  have hCD : centralizer (D : Set X) = centralizer ({a} : Set X) := centralizer_sup_center a
  have hζc : xB k 3 ∈ center X := hk.zc
  have hDle : D.map (MulAut.conj u).toMonoidHom ≤ D := by
    rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      have : (MulAut.conj u).toMonoidHom a = u * a * u⁻¹ := rfl
      rw [this]
      have h2 : zpowers a ⊔ zpowers (xB k 3) ≤ zpowers a ⊔ center X :=
        sup_le_sup_left (Subgroup.zpowers_le.2 hζc) _
      exact h2 huD
    · rintro _ ⟨z, hz, rfl⟩
      have : (MulAut.conj u).toMonoidHom z = z := by
        show u * z * u⁻¹ = z
        rw [Subgroup.mem_center_iff.1 hz u]
        group
      rw [this]
      exact Subgroup.mem_sup_right hz
  have hDu : D.map (MulAut.conj u).toMonoidHom = D := map_conj_eq_of_le hDle
  have huN : u ∈ normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (mem_map_conj_iff_of_eq hDu).symm
  have huC : u ∉ centralizer ({a} : Set X) := by
    intro h
    apply hune
    have := Subgroup.mem_centralizer_singleton_iff.1 h
    calc u * a * u⁻¹ = (u * a) * u⁻¹ := rfl
      _ = (a * u) * u⁻¹ := by rw [this]
      _ = a := by group
  have hq3 : (a : X ⧸ center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
  have hq1 : (a : X ⧸ center X) ≠ 1 := fun h1 => ha_ne ((QuotientGroup.eq_one_iff _).1 h1)
  have hord : orderOf (a : X ⧸ center X) = 3 := orderOf_eq_prime hq3 hq1
  have hcQ := card_centralizer_of_equiv_J3 e hq3 hq1 h5
  have hN6480 := card_normalizer_sup_center_le (a := a) hZ3 hord hcQ
  refine ⟨u, I, hk.closure_le_normalizer huk, hu8, huN, huC, hIC, hIperf, heI, hImax, ?_⟩
  rintro ⟨τ, hτN, hτC, hτ2⟩
  refine isPGL29_of_normalizing (D := D) (I := I) (u := u) ?_ ?_ ?_ hDI ?_ hD9 hu8 huN ?_ ?_
    (Classical.choice heI) ⟨τ, hτN, ?_, hτ2⟩
  · rw [hCD]; exact hIC
  · exact hIperf
  · rw [hCD]; exact hImax
  · rw [hCD]; exact hCeq
  · rw [hCD]; exact huC
  · rw [hCD, hC3240]; exact hN6480
  · rw [hCD]; exact hτC


set_option maxRecDepth 20000 in
theorem exists_tau_X {X : Type} [Group X] [Finite X] (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {a : X} (ha : a ∉ center X) (ha3 : a ^ 3 ∈ center X)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ τ ∈ normalizer ((zpowers a ⊔ center X : Subgroup X) : Set X),
      τ ∉ centralizer ({a} : Set X) ∧ τ ^ 2 = 1 := by
  have hq3 : (a : X ⧸ center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
  have hq1 : (a : X ⧸ center X) ≠ 1 := fun h1 => ha ((QuotientGroup.eq_one_iff _).1 h1)
  have hcQ := card_centralizer_of_equiv_J3 e hq3 hq1 h5
  obtain ⟨τb, hτb2, hτbx⟩ := exists_involution_inverting e hq3 hq1 hcQ
  obtain ⟨τh, hτh⟩ := QuotientGroup.mk_surjective τb
  have hz2 : τh ^ 2 ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hτh]; exact hτb2
  have hz3 : ∀ z ∈ center X, z ^ 3 = 1 := by
    intro z hz
    have := pow_card_eq_one' (x := (⟨z, hz⟩ : center X))
    rw [hZ3] at this
    exact congrArg Subtype.val this
  set τ : X := τh ^ 3 with hτ
  have hτ2 : τ ^ 2 = 1 := by
    have := hz3 _ hz2
    rw [hτ, ← pow_mul]
    simpa [← pow_mul] using this
  have hτbar : (τ : X ⧸ center X) = τb := by
    rw [hτ, QuotientGroup.mk_pow, hτh]
    have : τb ^ 3 = τb := by
      calc τb ^ 3 = τb ^ 2 * τb := by rw [pow_succ]
        _ = τb := by rw [hτb2, one_mul]
    exact this
  have hτa : ((τ * a * τ⁻¹ : X) : X ⧸ center X) = ((a⁻¹ : X) : X ⧸ center X) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hτbar]
    exact hτbx
  have hzc : τ * a * τ⁻¹ * a ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hτa, QuotientGroup.mk_inv]
    exact inv_mul_cancel _
  have hD : τ * a * τ⁻¹ ∈ zpowers a ⊔ center X := by
    have : τ * a * τ⁻¹ = (τ * a * τ⁻¹ * a) * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzc)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  refine ⟨τ, ?_, ?_, hτ2⟩
  · have hDle : (zpowers a ⊔ center X).map (MulAut.conj τ).toMonoidHom ≤ zpowers a ⊔ center X := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact hD
      · rintro _ ⟨z, hz, rfl⟩
        have : (MulAut.conj τ).toMonoidHom z = z := by
          show τ * z * τ⁻¹ = z
          rw [Subgroup.mem_center_iff.1 hz τ]
          group
        rw [this]
        exact Subgroup.mem_sup_right hz
    have hDu := map_conj_eq_of_le hDle
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (mem_map_conj_iff_of_eq hDu).symm
  · intro h
    have hc := Subgroup.mem_centralizer_singleton_iff.1 h
    have h1 : (τ : X ⧸ center X) * (a : X ⧸ center X) = (a : X ⧸ center X) * τ := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    rw [hτbar] at h1
    have h2 : τb * (a : X ⧸ center X) * τb⁻¹ = (a : X ⧸ center X) := by
      rw [h1]; group
    rw [hτbx] at h2
    apply hq1
    have h3 : (a : X ⧸ center X) ^ 2 = 1 := by
      have := congrArg (fun y => y * (a : X ⧸ center X)) h2
      simp only [inv_mul_cancel] at this
      rw [pow_two]; exact this.symm
    calc (a : X ⧸ center X) = (a : X ⧸ center X) ^ 3 * ((a : X ⧸ center X) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hq3, h3]; simp

set_option maxRecDepth 20000 in
theorem exists_pgl29_u {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3)
    {F : Subgroup X} (hF : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81)
    {F₁ : Subgroup X} (hZF₁ : center X ≤ F₁) (hF₁F : F₁ ≤ F) (hF₁27 : Nat.card F₁ = 27)
    (hF₁inv : ∀ y ∈ normalizer (F : Set X), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁)
    {a : X} (haF : a ∈ F) (haF₁ : a ∉ F₁)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ (u : X) (I : Subgroup X), u ∈ normalizer (F : Set X) ∧ orderOf u = 8 ∧
      u ∈ normalizer ((zpowers a ⊔ center X : Subgroup X) : Set X) ∧
      u ∉ centralizer ({a} : Set X) ∧ I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      IsPGL29 (I ⊔ zpowers u) I := by
  have ha_ne : a ∉ center X := fun hmem => haF₁ (hZF₁ hmem)
  have ha3 : a ^ 3 ∈ center X := by
    have h3 := (isElementaryAbelian_iff.1 hF).2 _ ⟨a, haF, rfl⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h3
  obtain ⟨u, I, h1, h2, h3, h4, h5', h6, h7, h8, h9⟩ :=
    exists_pgl_u hX hZ3 e hF hZF hF81 hF₁F hF₁27 hF₁inv haF haF₁ h5
  exact ⟨u, I, h1, h2, h3, h4, h5', h6, h7, h8, h9 (exists_tau_X hZ3 e ha_ne ha3 h5)⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
