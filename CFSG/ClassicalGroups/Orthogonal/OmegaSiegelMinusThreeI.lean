module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeCase
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelCopl

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

@[expose] def IsAxisPoint (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (a : N)
    (P : Submodule K V) : Prop :=
  finrank K P = 1 ∧ ∀ w : N, QN w = 0 → polar QN a w = 0 → w ∉ Submodule.span K' {a} →
    P ≤ movedSpace (rhoE ρ a w)

omit [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_polar_self (x : N) : polar QN x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

omit [Finite K] in
private theorem m3i_commute_of_inf_ne_bot
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : movedSpace s ⊓ movedSpace s' ≠ ⊥) : s * s' = s' * s := by
  have hQ := nondegenerate_polarBilin hnd
  obtain ⟨a, b, ha, hb, hab, hli, hmem, hne⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs
  obtain ⟨a', b', ha', hb', hab', hli', hmem', hne'⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs'
  have h1 := (mem_longRootGroup_isLongRootElement hnd hli hmem hne).2
  have h2 := (mem_longRootGroup_isLongRootElement hnd hli' hmem' hne').2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  refine longRootGroup_comm_of_common hQ ha hb hab ha' hb' hab'
    (hs.qf_eq_zero_of_mem_movedSpace hu1) hu0 ?_ ?_ hmem hmem'
  · rwa [h1] at hu1
  · rwa [h2] at hu2

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem m3i_pair_smul {u v : N} (h : LinearIndependent K' ![u, v]) {μ : K'}
    (hμ : μ ≠ 0) : LinearIndependent K' ![u, μ • v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have h' := h s (t * μ) (by rw [mul_smul]; exact hst)
  exact ⟨h'.1, (mul_eq_zero.mp h'.2).resolve_right hμ⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem m3i_smul_not_mem {u v : N} (h : LinearIndependent K' ![u, v]) {μ : K'}
    (hμ : μ ≠ 0) : μ • v ∉ Submodule.span K' {u} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨c, hc⟩
  have := (LinearIndependent.pair_iff.mp h) c (-μ) (by rw [neg_smul, hc]; exact add_neg_cancel _)
  exact hμ (neg_eq_zero.mp this.2)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_li_of_perp (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {e f s : N}
    (hef : polar QN e f = 1) (hsf : polar QN s f = 0) (hs0 : s ≠ 0) :
    LinearIndependent K' ![e, s] := by
  obtain ⟨z, hz⟩ : ∃ z, polar QN s z ≠ 0 := by
    by_contra! h
    exact hs0 (hnd s h)
  exact linearIndependent_pair_of_polar (by rw [hef]; exact one_ne_zero) hsf hz

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_nd (hs : OmegaSetting QN Qf ρ) :
    ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 :=
  fun x hx => hs.ndN.1 x fun y => hx y

omit [Finite K'] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_long (hs : OmegaSetting QN Qf ρ) {e f s : N}
    (he : QN e = 0) (hef : polar QN e f = 1) (hsQ : QN s = 0) (hs0 : s ≠ 0)
    (hes : polar QN e s = 0) (hfs : polar QN f s = 0) : IsLongRootElement Qf (rhoE ρ e s) :=
  hs.isLongRootElement_rhoE he hsQ hes
    (m3i_li_of_perp hs.m3i_nd hef (by rw [polar_comm]; exact hfs) hs0)

private def m3iFam (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (e f : N) :
    Set (Submodule K V) :=
  {A | ∃ w : N, QN w = 0 ∧ w ≠ 0 ∧ polar QN e w = 0 ∧ polar QN f w = 0 ∧
    A = movedSpace (rhoE ρ e w)}

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_fam_finrank (hs : OmegaSetting QN Qf ρ) {e f : N}
    (he : QN e = 0) (hef : polar QN e f = 1) {A : Submodule K V} (hA : A ∈ m3iFam ρ e f) :
    finrank K A = 2 := by
  obtain ⟨w, hw, hw0, hew, hfw, rfl⟩ := hA
  exact (hs.m3i_long he hef hw hw0 hew hfw).finrank_movedSpace hs.nd

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_fam_sing (hs : OmegaSetting QN Qf ρ) {e f : N}
    (he : QN e = 0) (hef : polar QN e f = 1) {A : Submodule K V} (hA : A ∈ m3iFam ρ e f) :
    ∀ x ∈ A, Qf x = 0 := by
  obtain ⟨w, hw, hw0, hew, hfw, rfl⟩ := hA
  intro x hx
  exact (hs.m3i_long he hef hw hw0 hew hfw).qf_eq_zero_of_mem_movedSpace hx

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_fam_inf_ne_bot (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥)
    {A A' : Submodule K V} (hA : A ∈ m3iFam ρ e f) (hA' : A' ∈ m3iFam ρ e f) (hne : A ≠ A') :
    A ⊓ A' ≠ ⊥ := by
  obtain ⟨w, hw, hw0, hew, hfw, rfl⟩ := hA
  obtain ⟨w', hw', hw'0, hew', hfw', rfl⟩ := hA'
  have he0 : e ≠ 0 := fun h => by
    have := hF.ef
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  by_cases hww' : polar QN w w' = 0
  · obtain ⟨c, rfl⟩ := hF.eq_smul_of_polar_eq_zero (by rw [polar_comm]; exact hew)
      (by rw [polar_comm]; exact hfw) (by rw [polar_comm]; exact hew')
      (by rw [polar_comm]; exact hfw') hw hw' hw0 hww'
    have hc0 : c ≠ 0 := fun h => hw'0 (by rw [h, zero_smul])
    have hc1 : c ≠ 1 := fun h => hne (by rw [h, one_smul])
    have hli := m3i_li_of_perp hs.m3i_nd hF.ef (by rw [polar_comm]; exact hfw) hw0
    have hsum : w + c • w = (1 + c) • w := by rw [add_smul, one_smul]
    have hc1' : 1 + c ≠ 0 := fun h => hc1 (CharTwo.add_eq_zero.mp h).symm
    refine hs.movedSpace_rhoE_inf_ne_bot hF.e_sing hw hw' hew hew' ?_ hli
      (m3i_pair_smul hli hc0) ?_
    · rw [polar_smul_right_eq, m3i_polar_self, mul_zero]
    · rw [hsum]
      exact m3i_pair_smul hli hc1'
  · exact hI e w w' ⟨hF.e_sing, he0, hw, hw', hew, hew', hww'⟩

omit [CharP K 2] [Finite K] in
private theorem m3i_finrank_inf_eq_one {A A' : Submodule K V} (h2 : finrank K A = 2)
    (h2' : finrank K A' = 2) (hne : A ≠ A') (hbot : A ⊓ A' ≠ ⊥) : finrank K ↥(A ⊓ A') = 1 := by
  have hpos : 1 ≤ finrank K ↥(A ⊓ A') := Submodule.one_le_finrank_iff.mpr hbot
  have hle : finrank K ↥(A ⊓ A') ≤ 2 := h2 ▸ Submodule.finrank_mono inf_le_left
  by_contra h1
  have h22 : finrank K ↥(A ⊓ A') = 2 := by omega
  apply hne
  have e1 : A ⊓ A' = A := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h22, h2])
  have e2 : A ⊓ A' = A' := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h22, h2'])
  exact e1.symm.trans e2

omit [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_reduce {e f x : N} (he : QN e = 0) (hef : polar QN e f = 1)
    (hex : polar QN e x = 0) :
    polar QN e (x + polar QN x f • e) = 0 ∧ polar QN f (x + polar QN x f • e) = 0 ∧
      eichler QN e (x + polar QN x f • e) = eichler QN e x := by
  refine ⟨?_, ?_, eichler_add_smul_self he x _⟩
  · rw [polar_add_right, polar_smul_right_eq, polar_self_eq_zero he, mul_zero, add_zero, hex]
  · rw [polar_add_right, polar_smul_right_eq, polar_comm QN f x, polar_comm QN f e, hef, mul_one]
    exact CharTwo.add_self_eq_zero _

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_reduce_sing {e w : N} (he : QN e = 0) (hw : QN w = 0)
    (hew : polar QN e w = 0) (c : K') : QN (w + c • e) = 0 := by
  rw [QuadraticMap.map_add QN, map_smul_eq_sq, he, hw, polar_smul_right_eq, polar_comm QN w e,
    hew]
  simp

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_triple_of_polar {a d u z : N} (hli : LinearIndependent K' ![a, d])
    (haz : polar QN a z = 0) (hdz : polar QN d z = 0) (huz : polar QN u z ≠ 0) :
    LinearIndependent K' ![a, d, u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h2 : g 2 * polar QN u z = 0 := by
    have h := congrArg (fun x => polar QN x z) hg
    simpa [polar_add_left, polar_smul_left_eq, haz, hdz] using h
  have hg2 : g 2 = 0 := (mul_eq_zero.mp h2).resolve_right huz
  rw [hg2, zero_smul, add_zero] at hg
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hli (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hg2

omit [FiniteDimensional K V] in
private theorem OmegaSetting.m3i_fam_two (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) :
    ∃ A ∈ m3iFam ρ e f, ∃ A' ∈ m3iFam ρ e f, A ≠ A' := by
  have hp0 : p ≠ 0 := fun h => by
    have := hF.pp'
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hp'0 : p' ≠ 0 := fun h => by
    have := hF.pp'
    rw [h, polar_zero_right] at this
    exact zero_ne_one this
  have hli2 : LinearIndependent K' ![e, p] :=
    m3i_li_of_perp hs.m3i_nd hF.ef (by rw [polar_comm]; exact hF.fp) hp0
  have hpp : polar QN p p = 0 := m3i_polar_self p
  have hp'p : polar QN p' p = 1 := by rw [polar_comm]; exact hF.pp'
  have hli3 : LinearIndependent K' ![e, p, p'] :=
    m3i_triple_of_polar hli2 hF.ep hpp (by rw [hp'p]; exact one_ne_zero)
  by_contra hno
  push Not at hno
  have hmem : ∀ (w : N), QN w = 0 → w ≠ 0 → polar QN e w = 0 → polar QN f w = 0 →
      movedSpace (rhoE ρ e w) ∈ m3iFam ρ e f := fun w h1 h2 h3 h4 => ⟨w, h1, h2, h3, h4, rfl⟩
  have hsm : ∀ (w : N) (μ : K'), QN w = 0 → w ≠ 0 → polar QN e w = 0 → polar QN f w = 0 →
      μ ≠ 0 → movedSpace (rhoE ρ e (μ • w)) ∈ m3iFam ρ e f := fun w μ h1 h2 h3 h4 hμ =>
    hmem _ (by rw [map_smul_eq_sq, h1, mul_zero]) (smul_ne_zero hμ h2)
      (by rw [polar_smul_right_eq, h3, mul_zero]) (by rw [polar_smul_right_eq, h4, mul_zero])
  have h0 : movedSpace (rhoE ρ e p) ∈ m3iFam ρ e f :=
    hmem p hF.p_sing hp0 hF.ep hF.fp
  refine hs.not_forall_movedSpace_rhoE_eq hF.e_sing hF.p_sing hF.p'_sing hF.ep hF.ep' hli3
    (movedSpace (rhoE ρ e p)) fun μ hμ => ⟨?_, ?_⟩
  · exact hno _ (hsm p μ hF.p_sing hp0 hF.ep hF.fp hμ) _ h0
  · exact hno _ (hsm p' μ hF.p'_sing hp'0 hF.ep' hF.fp' hμ) _ h0

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem m3i_rhoE_mem_of_forall_singular (Y : Subgroup (V ≃ₗ[K] V)) {u e₂ f₂ : N}
    {H : Submodule K' N} (he₂ : e₂ ∈ H) (hf₂ : f₂ ∈ H) (hQe₂ : QN e₂ = 0) (hQf₂ : QN f₂ = 0)
    (hef₂ : polar QN e₂ f₂ = 1) (hHu : ∀ w ∈ H, polar QN u w = 0)
    (hY : ∀ w ∈ H, QN w = 0 → rhoE ρ u w ∈ Y) {x : N} (hx : x ∈ H) : rhoE ρ u x ∈ Y := by
  obtain ⟨g, hg, hgx⟩ := eichler_mem_of_forall_singular (Q := QN)
    (Y := (Y.comap ρ).map (elementaryGroup QN).subtype) he₂ hf₂ hQe₂ hQf₂ hef₂ hHu
    (fun w hw hQw => ⟨⟨eichler QN u w, eichler_mem_elementaryGroup QN u w⟩, hY w hw hQw, rfl⟩) hx
  have : g = ⟨eichler QN u x, eichler_mem_elementaryGroup QN u x⟩ := Subtype.ext hgx
  rw [this] at hg
  exact hg

private theorem OmegaSetting.m3i_not_totally_singular (hs : OmegaSetting QN Qf ρ)
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) {U : Submodule K V}
    (hUs : ∀ x ∈ U, Qf x = 0) (hU3 : finrank K U = 3) (hUA : ∀ A ∈ m3iFam ρ e f, A ≤ U) :
    False := by
  let P₁ : HypPair QN := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  have hmem : ∀ x, polar QN e x = 0 → rhoE ρ e x ∈ sigmaGroup Qf U := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := m3i_reduce hF.e_sing hF.ef hx
    have key := m3i_rhoE_mem_of_forall_singular (ρ := ρ) (sigmaGroup Qf U) (u := e) (e₂ := p)
      (f₂ := p') (H := P₁.perp)
      (HypPair.mem_perp.mpr ⟨hF.ep, hF.fp⟩) (HypPair.mem_perp.mpr ⟨hF.ep', hF.fp'⟩)
      hF.p_sing hF.p'_sing hF.pp' (fun w hw => (HypPair.mem_perp.mp hw).1) (fun w hw hQw => ?_)
      (x := x + polar QN x f • e) (HypPair.mem_perp.mpr ⟨h1, h2⟩)
    · have : rhoE ρ e (x + polar QN x f • e) = rhoE ρ e x := by
        unfold rhoE
        congr 1
        exact Subtype.ext h3
      rwa [this] at key
    · by_cases hw0 : w = 0
      · rw [hw0, rhoE_zero_right]
        exact Subgroup.one_mem _
      · have hw' := HypPair.mem_perp.mp hw
        exact isLongRootElement_mem_sigmaGroup (hs.m3i_long hF.e_sing hF.ef hQw hw0 hw'.1 hw'.2)
          (hUA _ ⟨w, hQw, hw0, hw'.1, hw'.2, rfl⟩)
  have hR : ((rootGroup QN e).subgroupOf (elementaryGroup QN)).map ρ ≤ sigmaGroup Qf U := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hgx⟩ := mem_rootGroup.mp (Subgroup.mem_subgroupOf.mp hg)
    have : g = ⟨eichler QN e x, eichler_mem_elementaryGroup QN e x⟩ := Subtype.ext hgx.symm
    rw [this]
    exact hmem x hx
  have hcard1 : Nat.card ↥((rootGroup QN e).subgroupOf (elementaryGroup QN)) =
      Nat.card K' ^ 4 := by
    rw [← hF.natCard_rootGroup]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootGroup_le_elementaryGroup QN e)).toEquiv
  have hcard2 : Nat.card ↥(((rootGroup QN e).subgroupOf (elementaryGroup QN)).map ρ) =
      Nat.card K' ^ 4 := by
    rw [Subgroup.card_map_of_injective hs.inj, hcard1]
  have hcard3 : Nat.card ↥(sigmaGroup Qf U) = Nat.card K ^ 3 := natCard_sigmaGroup hs.nd hUs hU3
  have hq : 1 < Nat.card K' := Finite.one_lt_card
  have hfin : Finite ↥(sigmaGroup Qf U) :=
    Nat.finite_of_card_ne_zero (by rw [hcard3, ← hs.card]; positivity)
  have hle := Subgroup.card_le_of_le hR
  rw [hcard2, hcard3, ← hs.card] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hq (by norm_num)))

private theorem OmegaSetting.m3i_concurrent (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥) :
    ∃ P : Submodule K V, finrank K P = 1 ∧ ∀ A ∈ m3iFam ρ e f, P ≤ A := by
  have hF2 : ∀ {A : Submodule K V}, A ∈ m3iFam ρ e f → finrank K A = 2 := fun hA =>
    hs.m3i_fam_finrank hF.e_sing hF.ef hA
  obtain ⟨A₁, h₁, A₂, h₂, h12⟩ := hs.m3i_fam_two hF
  have hinf : ∀ {A A' : Submodule K V}, A ∈ m3iFam ρ e f → A' ∈ m3iFam ρ e f → A ≠ A' →
      finrank K ↥(A ⊓ A') = 1 := fun hA hA' hne =>
    m3i_finrank_inf_eq_one (hF2 hA) (hF2 hA') hne (hs.m3i_fam_inf_ne_bot hF hI hA hA' hne)
  rcases exists_point_le_or_exists_plane_ge ⟨A₁, h₁⟩ (fun A hA => hF2 hA)
    (fun A hA A' hA' hne => hinf hA hA' hne) with hconc | ⟨U, hU3, hU⟩
  · exact hconc
  by_cases hts : ∀ x ∈ U, Qf x = 0
  · exact (hs.m3i_not_totally_singular hF hts hU3 hU).elim
  have hr1 : finrank K ↥(A₁ ⊓ A₂) = 1 := hinf h₁ h₂ h12
  refine ⟨A₁ ⊓ A₂, hr1, fun A hA => ?_⟩
  by_contra hnot
  apply hts
  have hs₁ := hs.m3i_fam_sing hF.e_sing hF.ef h₁
  have hs₂ := hs.m3i_fam_sing hF.e_sing hF.ef h₂
  have hsA := hs.m3i_fam_sing hF.e_sing hF.ef hA
  have hrA : (A₁ ⊓ A₂) ⊓ A = ⊥ := by
    by_contra h
    apply hnot
    have h1 : 1 ≤ finrank K ↥((A₁ ⊓ A₂) ⊓ A) := Submodule.one_le_finrank_iff.mpr h
    have heq : (A₁ ⊓ A₂) ⊓ A = A₁ ⊓ A₂ :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
    rw [← heq]
    exact inf_le_right
  have hrA3 : finrank K ↥((A₁ ⊓ A₂) ⊔ A) = 3 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (A₁ ⊓ A₂) A
    rw [hrA, finrank_bot, hr1, hF2 hA] at this
    omega
  have hrU : (A₁ ⊓ A₂) ⊔ A ≤ U := sup_le (inf_le_left.trans (hU A₁ h₁)) (hU A hA)
  have hrAU : (A₁ ⊓ A₂) ⊔ A = U := Submodule.eq_of_le_of_finrank_eq hrU (by rw [hrA3, hU3])
  have h12sup : finrank K ↥(A₁ ⊔ A₂) = 3 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq A₁ A₂
    rw [hr1, hF2 h₁, hF2 h₂] at this
    omega
  have h12U : A₁ ⊔ A₂ = U :=
    Submodule.eq_of_le_of_finrank_eq (sup_le (hU A₁ h₁) (hU A₂ h₂)) (by rw [h12sup, hU3])
  intro x hx
  rw [← hrAU] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ := Submodule.mem_sup.mp (h12U ▸ hU A hA hz)
  have hpol : polar Qf y z = 0 := by
    rw [← hzz, polar_add_right, polar_eq_zero_of_totallySingular hs₁ hy.1 hz₁,
      polar_eq_zero_of_totallySingular hs₂ hy.2 hz₂, add_zero]
  rw [QuadraticMap.map_add Qf, hs₁ y hy.1, hsA z hz, hpol, add_zero, add_zero]

theorem OmegaSetting.caseI_exists_point (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥) :
    ∃ P, IsAxisPoint ρ e P := by
  obtain ⟨P, hP1, hP⟩ := hs.m3i_concurrent hF hI
  refine ⟨P, hP1, fun w hw hew hwe => ?_⟩
  have he0 : e ≠ 0 := fun h => by
    have := hF.ef
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  obtain ⟨h1, h2, h3⟩ := m3i_reduce hF.e_sing hF.ef hew
  have hne : w + polar QN w f • e ≠ 0 := by
    intro h
    apply hwe
    rw [Submodule.mem_span_singleton]
    exact ⟨-polar QN w f, by rw [neg_smul, ← eq_neg_of_add_eq_zero_left h]⟩
  have hrho : rhoE ρ e (w + polar QN w f • e) = rhoE ρ e w := by
    unfold rhoE
    congr 1
    exact Subtype.ext h3
  rw [← hrho]
  exact hP _ ⟨_, m3i_reduce_sing hF.e_sing hw hew _, hne, h1, h2, rfl⟩

theorem OmegaSetting.caseI_exists_point_of (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥)
    {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) : ∃ P, IsAxisPoint ρ a P := by
  obtain ⟨P, hP⟩ := hs.caseI_exists_point hF hI
  have he0 : e ≠ 0 := fun h => by
    have := hF.ef
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  let P₁ : HypPair QN := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  let P₂ : HypPair QN := ⟨p, p', hF.p_sing, hF.p'_sing, hF.pp'⟩
  have horth : P₁.Orth P₂ := ⟨hF.ep, hF.ep', hF.fp, hF.fp'⟩
  obtain ⟨g, hg, hge⟩ := exists_mem_elementaryGroup_apply_eq hs.ndN horth he0 ha0
    (hF.e_sing.trans ha.symm)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup QN := elementaryGroup_le_orthogonalGroup QN hg
  refine ⟨P.map (ρ ⟨g, hg⟩ : V →ₗ[K] V), ?_, fun w hw haw hwa => ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hP.1
  · have hgw : g (g⁻¹ w) = w := LinearEquiv.apply_inv_apply' g w
    have hQw' : QN (g⁻¹ w) = 0 := by rw [map_of_mem (inv_mem hgO), hw]
    have hew' : polar QN e (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hgO, hge, hgw, haw]
    have hnot : g⁻¹ w ∉ Submodule.span K' {e} := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hwa
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      have := congrArg g hc
      rwa [map_smul, hge, hgw] at this
    have h : movedSpace (rhoE ρ (g e) (g (g⁻¹ w))) =
        (movedSpace (rhoE ρ e (g⁻¹ w))).map (ρ ⟨g, hg⟩ : V →ₗ[K] V) :=
      movedSpace_rhoE_apply (ρ := ρ) ⟨g, hg⟩ e (g⁻¹ w)
    rw [hge, hgw] at h
    rw [h]
    exact Submodule.map_mono (hP.2 _ hQw' hew' hnot)

omit [Finite K'] [Finite K] in
theorem OmegaSetting.inf_eq_bot_of_collinear (hs : OmegaSetting QN Qf ρ) {a b : N}
    (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b = 0) (hli : LinearIndependent K' ![a, b])
    {P P' : Submodule K V} (hP : IsAxisPoint ρ a P) (hP' : IsAxisPoint ρ b P') : P ⊓ P' = ⊥ := by
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  obtain ⟨a', b', ha', hb', haa', hbb', hba', hab', ha'b'⟩ := exists_quadrangle hndN ha hb hab hli
  have hba : polar QN b a = 0 := by rw [polar_comm]; exact hab
  have ha'a : polar QN a' a = 1 := by rw [polar_comm]; exact haa'
  have hb'b : polar QN b' b = 1 := by rw [polar_comm]; exact hbb'
  have hb'a' : polar QN b' a' = 0 := by rw [polar_comm]; exact ha'b'
  have hl1 : LinearIndependent K' ![b, a'] := linearIndependent_pair_of_polar (z₁ := b') (z₂ := a)
    (by rw [hbb']; exact one_ne_zero) ha'b' (by rw [ha'a]; exact one_ne_zero)
  have hl2 : LinearIndependent K' ![a, b'] := linearIndependent_pair_of_polar (z₁ := a') (z₂ := b)
    (by rw [haa']; exact one_ne_zero) hb'a' (by rw [hb'b]; exact one_ne_zero)
  have hs1 : IsLongRootElement Qf (rhoE ρ b a') := hs.isLongRootElement_rhoE hb ha' hba' hl1
  have ht1 : IsLongRootElement Qf (rhoE ρ a b') := hs.isLongRootElement_rhoE ha hb' hab' hl2
  have hnc : rhoE ρ b a' * rhoE ρ a b' ≠ rhoE ρ a b' * rhoE ρ b a' := by
    intro h
    unfold rhoE at h
    rw [← map_mul, ← map_mul] at h
    exact eichler_mul_eichler_ne_of_quadrangle ha hb ha' hb' haa' hbb' hba' hab' ha'b'
      (congrArg Subtype.val (hs.inj h))
  have hbot : movedSpace (rhoE ρ a b') ⊓ movedSpace (rhoE ρ b a') = ⊥ := by
    by_contra hne
    refine hnc ?_
    exact (m3i_commute_of_inf_ne_bot hs.nd ht1 hs1 hne).symm
  have hb'a : b' ∉ Submodule.span K' {a} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have := hb'b
    rw [← hc, polar_smul_left_eq, hab, mul_zero] at this
    exact zero_ne_one this
  have ha'b : a' ∉ Submodule.span K' {b} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have := ha'a
    rw [← hc, polar_smul_left_eq, hba, mul_zero] at this
    exact zero_ne_one this
  exact eq_bot_iff.mpr (hbot ▸ inf_le_inf (hP.2 b' hb' hab' hb'a) (hP'.2 a' ha' hba' ha'b))

theorem OmegaSetting.caseI_single_axis (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥)
    {a b : N} (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b = 0)
    (hli : LinearIndependent K' ![a, b]) {μ : K'} (hμ : μ ≠ 0) :
    movedSpace (rhoE ρ a (μ • b)) = movedSpace (rhoE ρ a b) := by
  have ha0 : a ≠ 0 := by simpa using hli.ne_zero 0
  have hb0 : b ≠ 0 := by simpa using hli.ne_zero 1
  have hba : polar QN b a = 0 := by rw [polar_comm]; exact hab
  obtain ⟨Pa, hPa⟩ := hs.caseI_exists_point_of hF hI ha ha0
  obtain ⟨Pb, hPb⟩ := hs.caseI_exists_point_of hF hI hb hb0
  have hbot := hs.inf_eq_bot_of_collinear ha hb hab hli hPa hPb
  have hsup : finrank K ↥(Pa ⊔ Pb) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq Pa Pb
    rw [hbot, finrank_bot, hPa.1, hPb.1] at this
    omega
  have key : ∀ ν : K', ν ≠ 0 → movedSpace (rhoE ρ a (ν • b)) = Pa ⊔ Pb := by
    intro ν hν
    have hνb : QN (ν • b) = 0 := by rw [map_smul_eq_sq, hb, mul_zero]
    have haνb : polar QN a (ν • b) = 0 := by rw [polar_smul_right_eq, hab, mul_zero]
    have hνa : QN (ν • a) = 0 := by rw [map_smul_eq_sq, ha, mul_zero]
    have hbνa : polar QN b (ν • a) = 0 := by rw [polar_smul_right_eq, hba, mul_zero]
    have hlong : IsLongRootElement Qf (rhoE ρ a (ν • b)) :=
      hs.isLongRootElement_rhoE ha hνb haνb (m3i_pair_smul hli hν)
    have h2 : finrank K (movedSpace (rhoE ρ a (ν • b))) = 2 := hlong.finrank_movedSpace hs.nd
    have hPa_le : Pa ≤ movedSpace (rhoE ρ a (ν • b)) :=
      hPa.2 (ν • b) hνb haνb (m3i_smul_not_mem hli hν)
    have hPb_le : Pb ≤ movedSpace (rhoE ρ a (ν • b)) := by
      rw [rhoE_comm ha hνb haνb, rhoE_smul_left]
      exact hPb.2 (ν • a) hνa hbνa (m3i_smul_not_mem (LinearIndependent.pair_symm_iff.mpr hli) hν)
    exact (Submodule.eq_of_le_of_finrank_eq (sup_le hPa_le hPb_le) (by rw [hsup, h2])).symm
  have h1 := key 1 one_ne_zero
  rw [one_smul] at h1
  rw [key μ hμ, h1]

omit [Finite K'] [FiniteDimensional K' N] in
private theorem MinusThreeFrame.m3i_xu {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) :
    QN (p + u + p') = 0 ∧ polar QN e (p + u + p') = 0 ∧ polar QN f (p + u + p') = 0 ∧
      polar QN (p + u + p') p = 1 := by
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hpu : polar QN p u = 0 := by rw [polar_comm]; exact hup
  have hp'p : polar QN p' p = 1 := by rw [polar_comm]; exact hF.pp'
  have heu : polar QN e u = 0 := by rw [polar_comm]; exact hue
  have hfu : polar QN f u = 0 := by rw [polar_comm]; exact huf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add QN, QuadraticMap.map_add QN, polar_add_left, hF.p_sing, hF.p'_sing,
      hF.Qu, hpu, hF.pp', hup']
    linear_combination h2
  · rw [polar_add_right, polar_add_right, hF.ep, heu, hF.ep']
    simp
  · rw [polar_add_right, polar_add_right, hF.fp, hfu, hF.fp']
    simp
  · rw [polar_add_left, polar_add_left, m3i_polar_self, hup, hp'p]
    simp

omit [Finite K'] [FiniteDimensional K' N] in
private theorem MinusThreeFrame.m3i_xv {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) :
    QN (p + v + QN v • p') = 0 ∧ polar QN e (p + v + QN v • p') = 0 ∧
      polar QN f (p + v + QN v • p') = 0 ∧ polar QN (p + v + QN v • p') p = QN v := by
  obtain ⟨hve, hvf, hvp, hvp'⟩ := hF.v_perp
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hpv : polar QN p v = 0 := by rw [polar_comm]; exact hvp
  have hp'p : polar QN p' p = 1 := by rw [polar_comm]; exact hF.pp'
  have hev : polar QN e v = 0 := by rw [polar_comm]; exact hve
  have hfv : polar QN f v = 0 := by rw [polar_comm]; exact hvf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add QN, QuadraticMap.map_add QN, polar_add_left, polar_smul_right_eq,
      polar_smul_right_eq, map_smul_eq_sq, hF.p_sing, hF.p'_sing, hpv, hF.pp', hvp']
    linear_combination (QN v) * h2
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, hF.ep, hev, hF.ep']
    simp
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, hF.fp, hfv, hF.fp']
    simp
  · rw [polar_add_left, polar_add_left, polar_smul_left_eq, m3i_polar_self, hvp, hp'p]
    simp

omit [Finite K'] [FiniteDimensional K' N] in
private theorem MinusThreeFrame.m3i_mem_span {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {w : N} (hwe : polar QN e w = 0)
    (hwf : polar QN f w = 0) :
    w ∈ Submodule.span K' {p, p', p + u + p', p + v + QN v • p'} := by
  have hw := hF.span w
  simp only [Submodule.mem_span_insert, Submodule.mem_span_singleton] at hw
  obtain ⟨a₀, z₀, ⟨a₁, z₁, ⟨a₂, z₂, ⟨a₃, z₃, ⟨a₄, z₄, ⟨a₅, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩, h0⟩ := hw
  have hw' : w = a₀ • e + a₁ • f + (a₂ • p + a₃ • p' + (a₄ • u + a₅ • v)) := by
    rw [h0, h1, h2, h3, h4, ← h5]
    abel
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  obtain ⟨hve, hvf, hvp, hvp'⟩ := hF.v_perp
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hF.ef
  have hE : polar QN e w = a₁ := by
    rw [hw']
    simp only [polar_add_right, polar_smul_right_eq, m3i_polar_self, hF.ef, hF.ep, hF.ep',
      polar_comm QN e u, polar_comm QN e v, hue, hve]
    ring
  have hFF : polar QN f w = a₀ := by
    rw [hw']
    simp only [polar_add_right, polar_smul_right_eq, m3i_polar_self, hfe, hF.fp, hF.fp',
      polar_comm QN f u, polar_comm QN f v, huf, hvf]
    ring
  rw [hE] at hwe
  rw [hFF] at hwf
  rw [hw', hwe, hwf]
  have e1 : (0 : K') • e + (0 : K') • f + (a₂ • p + a₃ • p' + (a₄ • u + a₅ • v)) =
      (a₂ - a₄ - a₅) • p + (a₃ - a₄ - a₅ * QN v) • p' + a₄ • (p + u + p') +
        a₅ • (p + v + QN v • p') := by module
  rw [e1]
  have hmem : ∀ x : N, x ∈ ({p, p', p + u + p', p + v + QN v • p'} : Set N) →
      x ∈ Submodule.span K' {p, p', p + u + p', p + v + QN v • p'} := fun x hx =>
    Submodule.subset_span hx
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ (hmem p (by simp))
  · exact Submodule.smul_mem _ _ (hmem p' (by simp))
  · exact Submodule.smul_mem _ _ (hmem _ (by simp))
  · exact Submodule.smul_mem _ _ (hmem _ (by simp))

omit [Finite K'] [FiniteDimensional K' N] in
private theorem m3i_rootGroup_le {z z' : N} {Y : Subgroup (N ≃ₗ[K'] N)} (hz : QN z = 0)
    (hzz' : polar QN z z' = 1) {S : Set N} (hSz : ∀ x ∈ S, polar QN z x = 0)
    (hS : ∀ x ∈ S, ∀ c : K', eichler QN z (c • x) ∈ Y)
    (hspan : ∀ w, polar QN z w = 0 → polar QN z' w = 0 → w ∈ Submodule.span K' S) :
    rootGroup QN z ≤ Y := by
  have hind : ∀ x ∈ Submodule.span K' S,
      polar QN z x = 0 ∧ ∀ c : K', eichler QN z (c • x) ∈ Y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨hSz x hx, hS x hx⟩
    | zero =>
      refine ⟨by rw [polar_zero_right], fun c => ?_⟩
      rw [smul_zero, eichler_zero_right]
      exact Y.one_mem
    | add x y hx hy ihx ihy =>
      have h1 : ∀ c : K', polar QN z (c • x) = 0 := fun c => by
        rw [polar_smul_right_eq, ihx.1, mul_zero]
      have h2 : ∀ c : K', polar QN z (c • y) = 0 := fun c => by
        rw [polar_smul_right_eq, ihy.1, mul_zero]
      refine ⟨by rw [polar_add_right, ihx.1, ihy.1, add_zero], fun c => ?_⟩
      rw [smul_add, ← eichler_mul (h1 c) (h2 c)]
      exact Y.mul_mem (ihx.2 c) (ihy.2 c)
    | smul a x hx ih =>
      refine ⟨by rw [polar_smul_right_eq, ih.1, mul_zero], fun c => ?_⟩
      rw [← mul_smul]
      exact ih.2 (c * a)
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  obtain ⟨h1, h2, h3⟩ := m3i_reduce hz hzz' hw
  rw [← h3]
  have := (hind _ (hspan _ h1 h2)).2 1
  rwa [one_smul] at this

omit [Finite K'] [FiniteDimensional K' N] in
private theorem MinusThreeFrame.m3i_four {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) :
    ∃ T : Fin 4 → N, T 0 = p ∧
      (∀ j, QN (T j) = 0 ∧ T j ≠ 0 ∧ polar QN e (T j) = 0 ∧ polar QN f (T j) = 0) ∧
      (∀ j : Fin 4, j ≠ 0 → polar QN (T j) p ≠ 0) ∧
      ∀ w, polar QN e w = 0 → polar QN f w = 0 → w ∈ Submodule.span K' (Set.range T) := by
  obtain ⟨hxuQ, hxue, hxuf, hxup⟩ := hF.m3i_xu
  obtain ⟨hxvQ, hxve, hxvf, hxvp⟩ := hF.m3i_xv
  have hQv : QN v ≠ 0 := fun h => by
    have := (hF.aniso 0 1 (by rw [zero_smul, one_smul, zero_add, h])).2
    exact one_ne_zero this
  have hp0 : p ≠ 0 := fun h => by
    have := hF.pp'
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hp'0 : p' ≠ 0 := fun h => by
    have := hF.pp'
    rw [h, polar_zero_right] at this
    exact zero_ne_one this
  have hxu0 : p + u + p' ≠ 0 := fun h => by
    rw [h, polar_zero_left] at hxup
    exact zero_ne_one hxup
  have hxv0 : p + v + QN v • p' ≠ 0 := fun h => by
    rw [h, polar_zero_left] at hxvp
    exact hQv hxvp.symm
  refine ⟨![p, p', p + u + p', p + v + QN v • p'], rfl, fun j => ?_, fun j hj => ?_,
    fun w h1 h2 => ?_⟩
  · fin_cases j
    · exact ⟨hF.p_sing, hp0, hF.ep, hF.fp⟩
    · exact ⟨hF.p'_sing, hp'0, hF.ep', hF.fp'⟩
    · exact ⟨hxuQ, hxu0, hxue, hxuf⟩
    · exact ⟨hxvQ, hxv0, hxve, hxvf⟩
  · fin_cases j
    · exact absurd rfl hj
    · show polar QN p' p ≠ 0
      rw [polar_comm, hF.pp']
      exact one_ne_zero
    · show polar QN (p + u + p') p ≠ 0
      rw [hxup]
      exact one_ne_zero
    · show polar QN (p + v + QN v • p') p ≠ 0
      rw [hxvp]
      exact hQv
  · have := hF.m3i_mem_span h1 h2
    convert this using 2
    ext x
    simp [Set.range, Fin.exists_fin_succ, eq_comm]

omit [Finite K'] [FiniteDimensional K' N] in
private theorem MinusThreeFrame.m3i_gen {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {T : Fin 4 → N}
    (hT : ∀ j, polar QN e (T j) = 0 ∧ polar QN f (T j) = 0)
    (hspan : ∀ w, polar QN e w = 0 → polar QN f w = 0 → w ∈ Submodule.span K' (Set.range T)) :
    elementaryGroup QN ≤ Subgroup.closure
      {g | ∃ i : Fin 2 × Fin 4, ∃ c : K', g = eichler QN (![e, f] i.1) (c • T i.2)} := by
  set Y := Subgroup.closure
    {g | ∃ i : Fin 2 × Fin 4, ∃ c : K', g = eichler QN (![e, f] i.1) (c • T i.2)} with hY
  have hTY : ∀ (k : Fin 2) (j : Fin 4) (c : K'), eichler QN (![e, f] k) (c • T j) ∈ Y :=
    fun k j c => Subgroup.subset_closure ⟨(k, j), c, rfl⟩
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hF.ef
  have hRe : rootGroup QN e ≤ Y := m3i_rootGroup_le hF.e_sing hF.ef (S := Set.range T)
    (by rintro _ ⟨j, rfl⟩; exact (hT j).1) (by rintro _ ⟨j, rfl⟩ c; exact hTY 0 j c) hspan
  have hRf : rootGroup QN f ≤ Y := m3i_rootGroup_le hF.f_sing hfe (S := Set.range T)
    (by rintro _ ⟨j, rfl⟩; exact (hT j).2) (by rintro _ ⟨j, rfl⟩ c; exact hTY 1 j c)
    (fun w h1 h2 => hspan w h2 h1)
  exact (elementaryGroup_le_rootGroup_sup hnd hF.e_sing hF.f_sing hF.ef
    (by rw [polar_comm]; exact hF.u_perp.1) (by rw [polar_comm]; exact hF.u_perp.2.1)
    hF.Qu).trans (sup_le hRe hRf)

omit [CharP K 2] [Finite K] in
private theorem m3i_finrank_iSup_le {ι : Type*} [Fintype ι] (P : ι → Submodule K V)
    (hP : ∀ i, finrank K ↥(P i) ≤ 1) : finrank K ↥(⨆ i, P i) ≤ Fintype.card ι := by
  classical
  have key : ∀ s : Finset ι, finrank K ↥(s.sup P) ≤ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.sup_insert]
      have h1 := Submodule.finrank_add_le_finrank_add_finrank (P a) (s.sup P)
      have h2 := hP a
      omega
  have h := key Finset.univ
  rwa [Finset.sup_univ_eq_iSup, Finset.card_univ] at h

omit [Finite K'] [Finite K] in
private theorem OmegaSetting.m3i_movedSpace_le_sup (hs : OmegaSetting QN Qf ρ) {z w : N}
    (hz : QN z = 0) (hw : QN w = 0) (hzw : polar QN z w = 0)
    (hli : LinearIndependent K' ![z, w]) {Pz Pw : Submodule K V} (hPz : IsAxisPoint ρ z Pz)
    (hPw : IsAxisPoint ρ w Pw) : movedSpace (rhoE ρ z w) ≤ Pz ⊔ Pw := by
  have hwz : polar QN w z = 0 := by rw [polar_comm]; exact hzw
  have hsup : finrank K ↥(Pz ⊔ Pw) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq Pz Pw
    rw [hs.inf_eq_bot_of_collinear hz hw hzw hli hPz hPw, finrank_bot, hPz.1, hPw.1] at this
    omega
  have hzP : Pz ≤ movedSpace (rhoE ρ z w) :=
    hPz.2 w hw hzw (by simpa using m3i_smul_not_mem hli one_ne_zero)
  have hwP : Pw ≤ movedSpace (rhoE ρ z w) := by
    rw [rhoE_comm hz hw hzw]
    exact hPw.2 z hz hwz
      (by simpa using m3i_smul_not_mem (LinearIndependent.pair_symm_iff.mpr hli) one_ne_zero)
  have hle : finrank K ↥(movedSpace (rhoE ρ z w)) ≤ 2 :=
    (hs.isLongRootElement_rhoE hz hw hzw hli).finrank_movedSpace_le_two
  exact (Submodule.eq_of_le_of_finrank_le (sup_le hzP hwP) (by omega)).ge

private theorem OmegaSetting.m3i_eight_lines (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥)
    {T : Fin 4 → N}
    (hT : ∀ j, QN (T j) = 0 ∧ T j ≠ 0 ∧ polar QN e (T j) = 0 ∧ polar QN f (T j) = 0)
    (hspanT : ∀ w, polar QN e w = 0 → polar QN f w = 0 → w ∈ Submodule.span K' (Set.range T)) :
    (∀ (k : Fin 2) (j : Fin 4), QN (![e, f] k) = 0 ∧ QN (T j) = 0 ∧
      polar QN (![e, f] k) (T j) = 0 ∧ LinearIndependent K' ![![e, f] k, T j]) ∧
    (⊤ : Submodule K V) ≤ ⨆ i : Fin 2 × Fin 4, movedSpace (rhoE ρ (![e, f] i.1) (T i.2)) := by
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hF.ef
  have hspec : ∀ (k : Fin 2) (j : Fin 4), QN (![e, f] k) = 0 ∧ QN (T j) = 0 ∧
      polar QN (![e, f] k) (T j) = 0 ∧ LinearIndependent K' ![![e, f] k, T j] := by
    intro k j
    obtain ⟨h1, h2, h3, h4⟩ := hT j
    fin_cases k
    · exact ⟨hF.e_sing, h1, h3, m3i_li_of_perp hs.m3i_nd hF.ef (by rw [polar_comm]; exact h4) h2⟩
    · exact ⟨hF.f_sing, h1, h4, m3i_li_of_perp hs.m3i_nd hfe (by rw [polar_comm]; exact h3) h2⟩
  refine ⟨hspec, ?_⟩
  let A : Fin 2 × Fin 4 → Submodule K V := fun i => movedSpace (rhoE ρ (![e, f] i.1) (T i.2))
  have hA : ∀ (i : Fin 2 × Fin 4) (c : K'),
      movedSpace (rhoE ρ (![e, f] i.1) (c • T i.2)) ≤ A i := by
    intro i c
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, rhoE_zero_right]
      rintro _ ⟨x, rfl⟩
      simp
    · obtain ⟨h1, h2, h3, h4⟩ := hspec i.1 i.2
      exact (hs.caseI_single_axis hF hI h1 h2 h3 h4 hc).le
  have hgen := hF.m3i_gen hs.m3i_nd (fun j => ⟨(hT j).2.2.1, (hT j).2.2.2⟩) hspanT
  exact top_le_iSup_of_generate (ρ := ρ) htop (fun i : Fin 2 × Fin 4 => ![e, f] i.1)
    (fun i : Fin 2 × Fin 4 => T i.2) hgen (A := A) hA

theorem OmegaSetting.finrank_le_six_of_caseI (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (hI : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) ≠ ⊥) :
    finrank K V ≤ 6 := by
  obtain ⟨T, -, hT, -, hspanT⟩ := hF.m3i_four
  obtain ⟨hspec, htopA⟩ := hs.m3i_eight_lines htop hF hI hT hspanT
  choose Pz hPz using fun k : Fin 2 => hs.caseI_exists_point_of hF hI (hspec k 0).1
    (by simpa using (hspec k 0).2.2.2.ne_zero 0)
  choose PT hPT using fun j : Fin 4 => hs.caseI_exists_point_of hF hI (hT j).1 (hT j).2.1
  have hle : ∀ i : Fin 2 × Fin 4,
      movedSpace (rhoE ρ (![e, f] i.1) (T i.2)) ≤ Pz i.1 ⊔ PT i.2 := fun i => by
    obtain ⟨h1, h2, h3, h4⟩ := hspec i.1 i.2
    exact hs.m3i_movedSpace_le_sup h1 h2 h3 h4 (hPz i.1) (hPT i.2)
  have htopP : (⊤ : Submodule K V) ≤ ⨆ x : Fin 2 ⊕ Fin 4, Sum.elim Pz PT x := by
    refine htopA.trans (iSup_le fun i => (hle i).trans (sup_le ?_ ?_))
    · exact le_iSup (Sum.elim Pz PT) (Sum.inl i.1)
    · exact le_iSup (Sum.elim Pz PT) (Sum.inr i.2)
  have hcard := m3i_finrank_iSup_le (Sum.elim Pz PT) fun x => by
    rcases x with k | j
    · exact (hPz k).1.le
    · exact (hPT j).1.le
  have hmono := Submodule.finrank_mono htopP
  rw [finrank_top] at hmono
  simpa using hmono.trans hcard

theorem OmegaSetting.caseII_of_six_lt_finrank (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h6 : 6 < finrank K V) :
    ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥ :=
  (hs.flag_dichotomy hF).resolve_left fun hI => by
    have := hs.finrank_le_six_of_caseI htop hF hI
    omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
