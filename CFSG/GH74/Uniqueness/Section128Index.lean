module

public import CFSG.GH74.Uniqueness.Section123

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec128

omit [Finite X] in
theorem ncard_conj_mul_card (H : Subgroup X) (x : X) :
    {y : X | ∃ g ∈ H, g⁻¹ * x * g = y}.ncard * Nat.card ↥(centralizer ({x} : Set X) ⊓ H) =
      Nat.card H := by
  classical
  let _ : MulAction H X :=
    MulAction.compHom X ((ConjAct.toConjAct : X ≃* ConjAct X).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (y : X), h • y = (h : X) * y * (h : X)⁻¹ := fun h y => by
    change ConjAct.toConjAct (h : X) • y = _
    rw [ConjAct.smul_def]
    simp
  have horbit : MulAction.orbit H x = {y : X | ∃ g ∈ H, g⁻¹ * x * g = y} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨(h : X)⁻¹, H.inv_mem h.2, by rw [hsmul, inv_inv]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g⁻¹, H.inv_mem hg⟩, by rw [hsmul]; simp⟩
  have hstab : Nat.card (MulAction.stabilizer H x) =
      Nat.card ↥(centralizer ({x} : Set X) ⊓ H) := by
    have e : MulAction.stabilizer H x = (centralizer ({x} : Set X) ⊓ H).subgroupOf H := by
      ext h
      rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h1
        refine ⟨?_, h.2⟩
        calc (h : X) * x = (h : X) * x * (h : X)⁻¹ * h := by group
          _ = x * h := by rw [h1]
      · rintro ⟨h1, -⟩
        rw [h1]; group
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h1 : (MulAction.stabilizer H x).index = (MulAction.orbit H x).ncard :=
    MulAction.index_stabilizer H x
  have h2 := (MulAction.stabilizer H x).card_mul_index
  rw [h1, horbit, hstab] at h2
  rw [mul_comm]
  exact h2

end Sec128

omit [Finite X] in
theorem IsProductDisconnected.ncard_orbit_mul_card_of_mem (hP : IsProductDisconnected Z M)
    (H : Subgroup X) {β : Subgroup X} (hβ : β ∈ omega M) :
    {γ : Subgroup X | ∃ g ∈ H, conjugate β g = γ}.ncard * Nat.card ↥(H ⊓ β) = Nat.card H := by
  classical
  set α : omega M := ⟨β, hβ⟩ with hα
  have hsmul : ∀ (g : H) (δ : omega M),
      ((g • δ : omega M) : Subgroup X) = conjugate (δ : Subgroup X) (g : X)⁻¹ := fun g δ => rfl
  have horbit : Subtype.val '' MulAction.orbit H α = {γ | ∃ g ∈ H, conjugate β g = γ} := by
    ext γ
    constructor
    · rintro ⟨δ, ⟨g, rfl⟩, rfl⟩
      exact ⟨(g : X)⁻¹, H.inv_mem g.2, (hsmul g α).symm⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(⟨g⁻¹, H.inv_mem hg⟩ : H) • α, ⟨_, rfl⟩, ?_⟩
      rw [hsmul]
      simp [hα]
  have hstab : MulAction.stabilizer H α = (H ⊓ β).subgroupOf H := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      have h2 : conjugate β (g : X)⁻¹ = β := by
        have := congrArg Subtype.val h1
        rwa [hsmul] at this
      have h3 : (g : X)⁻¹ ∈ β := (hP.conjugate_eq_iff_mem hβ).mp h2
      exact ⟨g.2, by simpa using β.inv_mem h3⟩
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      rw [hsmul]
      exact (hP.conjugate_eq_iff_mem hβ).mpr (β.inv_mem h1)
  have h1 : (MulAction.stabilizer H α).index = (MulAction.orbit H α).ncard :=
    MulAction.index_stabilizer H α
  have h2 := (MulAction.stabilizer H α).card_mul_index
  rw [h1, hstab] at h2
  have h3 : (MulAction.orbit H α).ncard = {γ | ∃ g ∈ H, conjugate β g = γ}.ncard := by
    rw [← horbit, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [h3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h2
  rw [mul_comm]
  exact h2

omit [Finite X] in
theorem IsProductDisconnected.ncard_orbit_mul_card (hP : IsProductDisconnected Z M)
    (H : Subgroup X) :
    {γ : Subgroup X | ∃ g ∈ H, conjugate M g = γ}.ncard * Nat.card ↥(H ⊓ M) = Nat.card H :=
  hP.ncard_orbit_mul_card_of_mem H (self_mem_omega M)

omit [Finite X] in
theorem IsProductDisconnected.ncard_omega_mul_card (hP : IsProductDisconnected Z M) :
    (omega M).ncard * Nat.card M = Nat.card X := by
  have h := hP.ncard_orbit_mul_card ⊤
  have e : {γ : Subgroup X | ∃ g ∈ (⊤ : Subgroup X), conjugate M g = γ} = omega M := by
    ext γ
    exact ⟨fun ⟨g, _, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, mem_top g, hg⟩⟩
  rwa [e, top_inf_eq, Subgroup.card_top] at h

theorem ZDSetup.ncard_omega_sub_one_mul_card
    (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) :
    ((omega M).ncard - 1) * Nat.card ↥(M ⊓ conjugate M t) = Nat.card M := by
  have hβ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have hβM : conjugate M t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr htM
  have h1 := S.prodDisc.ncard_orbit_mul_card_of_mem M hβ
  have horb : {γ : Subgroup X | ∃ g ∈ M, conjugate (conjugate M t) g = γ} = omega M \ {M} := by
    ext γ
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨conjugate_mem_omega hβ g, fun hγ => hβM ?_⟩
      have hγ' : conjugate (conjugate M t) g = M := hγ
      have hMg : conjugate M g⁻¹ = M :=
        (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (M.inv_mem hg)
      calc conjugate M t = conjugate (conjugate (conjugate M t) g) g⁻¹ := by
            rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
        _ = M := by rw [hγ', hMg]
    · rintro ⟨hγ, hγM⟩
      obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 M (self_mem_omega M) (conjugate M t) hβ hβM.symm M
        (self_mem_omega M) γ hγ (fun h => hγM h.symm)
      exact ⟨g, (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp hg1, hg2⟩
  rw [horb, Set.ncard_sdiff_singleton_of_mem (self_mem_omega M)] at h1
  exact h1

omit [Finite X] in
theorem Sec128.card_sup_mul_card_inf_of_normal (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

omit [Finite X] in
theorem Sec128.card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := Sec128.card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem ZDSetup.omegaFix_eq_orbit (S : ZDSetup X Z M) {u : X} (hu2 : orderOf u = 2)
    (huM : u ∈ M) (hFM : ¬ centralizer ({u} : Set X) ≤ M)
    (hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty) :
    omegaFix M ({u} : Set X) = {γ | ∃ g ∈ centralizer ({u} : Set X), conjugate M g = γ} ∧
      omegaFix M ({u} : Set X) = {γ | ∃ l ∈ cenHull Z u, conjugate M l = γ} := by
  have hMu : conjugate M u = M := (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr huM
  have h1 : omegaFix M ({u} : Set X) =
      {γ | ∃ g ∈ centralizer ({u} : Set X), conjugate M g = γ} := by
    ext β
    constructor
    · rintro ⟨hβ, hfix⟩
      exact S.exists_centralizer_conj hu2 (self_mem_omega M) hβ hMu (hfix u (Set.mem_singleton u))
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, rfl⟩, fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hgy : g * u = u * g := mem_centralizer_singleton_iff.mp hg
      rw [conjugate_conjugate, hgy, ← conjugate_conjugate, hMu]
  refine ⟨h1, ?_⟩
  rw [h1]
  exact S.cor713_alphaOrbit_eq hFM hne

theorem BenderSub.card_eq_mul
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : Nat.card F = Nat.card ↥(F ⊓ M) * ((2 ^ n) ^ i + 1) := by
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  have hidx : ((M ⊓ F).subgroupOf F).index = (2 ^ n) ^ i + 1 := by
    have h1 := Subgroup.index_map_eq ((M ⊓ F).subgroupOf F)
      (QuotientGroup.mk'_surjective (center ↥F))
      (by rw [QuotientGroup.ker_mk']; exact A2.center_le_of_benderSub S hB)
    rw [hT] at h1
    rw [← h1]
    exact hc.index_eq
  have h2 := ((M ⊓ F).subgroupOf F).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm] at h2
  exact h2.symm

theorem ZDSetup.ncard_omegaFix_and_card_centralizer
    (S : ZDSetup X Z M) {u : X}
    (hu2 : orderOf u = 2) (huM : u ∈ M) {m j e : ℕ} (hB : BenderSub Z M (cenHull Z u) m j e) :
    (omegaFix M ({u} : Set X)).ncard = (2 ^ m) ^ j + 1 ∧
      Nat.card ↥(centralizer ({u} : Set X)) =
        ((2 ^ m) ^ j + 1) * Nat.card ↥(centralizer ({u} : Set X) ⊓ M) := by
  have hLC : cenHull Z u ≤ centralizer ({u} : Set X) := Cor713.zHull_le _
  have hFM : ¬ centralizer ({u} : Set X) ≤ M := fun hle => hB.not_le (hLC.trans hle)
  have hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty := by
    obtain ⟨y, hyZ, hy⟩ := hB.nonempty
    exact ⟨y, hyZ, inf_le_inf_right M hLC hy⟩
  obtain ⟨hC, hL⟩ := S.omegaFix_eq_orbit hu2 huM hFM hne
  have h1 := S.prodDisc.ncard_orbit_mul_card (cenHull Z u)
  rw [← hL, BenderSub.card_eq_mul S hB] at h1
  have hΩ : (omegaFix M ({u} : Set X)).ncard = (2 ^ m) ^ j + 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  refine ⟨hΩ, ?_⟩
  have h2 := S.prodDisc.ncard_orbit_mul_card (centralizer ({u} : Set X))
  rw [← hC, hΩ] at h2
  exact h2.symm

namespace Sec128

theorem card_centralizer_z (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) :
    Nat.card M = (2 ^ n - 1) * Nat.card ↥(centralizer ({c.z} : Set X)) := by
  have h1 := ncard_conj_mul_card M c.z
  have horb : {y : X | ∃ g ∈ M, g⁻¹ * c.z * g = y} = Z ∩ (M : Set X) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨S.invariant.2 c.z c.hz g, M.mul_mem (M.mul_mem (M.inv_mem hg) c.hzM) hg⟩
    · rintro ⟨hyZ, hyM⟩
      exact S.prodDisc.exists_conj_mem S.invariant c.hz c.hzM hyZ hyM
  have hCM : centralizer ({c.z} : Set X) ⊓ M = centralizer ({c.z} : Set X) :=
    inf_eq_left.mpr (S.prodDisc.centralizer_le_of_mem c.hz c.hzM)
  rw [horb, A2.ncard_zM h, hCM] at h1
  exact h1.symm

omit [Finite X] in
theorem isPGroup_zpowers_of_two {u : X} (hu : orderOf u = 2) : IsPGroup 2 (zpowers u) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hu, pow_one]

theorem exists_conj_of_isConj (S : ZDSetup X Z M) {u v : X} (huM : u ∈ M) (hu2 : orderOf u = 2)
    (hvM : v ∈ M) (h : IsConj u v) : ∃ g ∈ M, g⁻¹ * u * g = v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hg' : g⁻¹⁻¹ * u * g⁻¹ ∈ M := by rw [inv_inv, hg]; exact hvM
  obtain ⟨m, hm, hmu⟩ := S.exists_mem_conj_of_isPGroup huM (isPGroup_zpowers_of_two hu2) hg'
  exact ⟨m, hm, by rw [hmu, inv_inv, hg]⟩

theorem qU_conj {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {g : X} (hg : g ∈ M) (u : X) :
    qU Z M (g⁻¹ * u * g) = qU Z M u := by
  unfold qU
  have hmap : (centralizer ({u} : Set X) ⊓ zHull Z M).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({g⁻¹ * u * g} : Set X) ⊓ zHull Z M := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have hsymm : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by
      rw [MulAut.conj_symm_apply, inv_inv]
    rw [hsymm]
    have hH : g * x * g⁻¹ ∈ zHull Z M ↔ x ∈ zHull Z M := by
      constructor
      · intro hx
        have := h.m_normal g⁻¹ (M.inv_mem hg) _ hx
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      · intro hx
        exact h.m_normal g hg x hx
    rw [hH]
    constructor
    · rintro ⟨hc, hx⟩
      refine ⟨?_, hx⟩
      calc x * (g⁻¹ * u * g) = g⁻¹ * ((g * x * g⁻¹) * u) * g := by group
        _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * u * g * x := by group
    · rintro ⟨hc, hx⟩
      refine ⟨?_, hx⟩
      calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hc]
        _ = u * (g * x * g⁻¹) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

end Sec128

end CFSG.GH74.Uniqueness
