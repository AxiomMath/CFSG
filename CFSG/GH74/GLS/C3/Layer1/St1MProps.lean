module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop81

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4

section MProps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thetaGA_mono {A B : Subgroup G} (h : A ≤ B) : thetaGA A ≤ thetaGA B :=
  iSup_le fun _ => iSup_le fun ha => iSup_le fun ha1 => pPrimeCoreOf_le_thetaGA (h ha) ha1

theorem thetaGA_le_of_common {A B C : Subgroup G} (hA : IsEStar A) (hr : 3 ≤ pRank 2 G)
    (hbal : IsBalancedWrt A) (hCA : C ≤ A) (hCB : C ≤ B) (hC4 : 4 ≤ Nat.card ↥C) :
    thetaGA A ≤ thetaGA B := by
  obtain ⟨hcop, hnorm, hcent⟩ := thetaGA_spec hA hr hbal
  have hgen := CFSG.Walter.le_iSup_inf_centralizer (E := C) (N := thetaGA A) Nat.prime_two
    ⟨⟨fun x y => Subtype.ext (hA.commute (hCA x.2) (hCA y.2))⟩⟩
    (fun x hx => hA.pow_two (hCA hx)) (by simpa using hC4) (hCA.trans hnorm)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop)
  refine hgen.trans (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  rw [hcent e (hCA he) he1]
  exact pPrimeCoreOf_le_thetaGA (hCB he) he1

omit [Finite G] in
theorem isEStar_cmap {A : Subgroup G} (hA : IsEStar A) (c : G) : IsEStar (cmap c A) := by
  have hequiv : ↥A ≃* ↥(cmap c A) := (MulAut.conj c).subgroupMap A
  exact ⟨isElementaryAbelian_two_of_mulEquiv hequiv hA.1, by
    rw [← hA.2]; exact (Nat.card_congr hequiv.toEquiv).symm⟩

omit [Finite G] in
theorem thetaGA_cmap
    (c : G) (A : Subgroup G) : thetaGA (cmap c A) = cmap c (thetaGA A) := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    rw [mem_cmap] at ha
    have ha1' : c⁻¹ * a * c ≠ 1 := fun h => ha1 (by
      have := congrArg (fun t => c * t * c⁻¹) h
      simpa [mul_assoc] using this)
    have hC : pPrimeCoreOf 2 (centralizer ({a} : Set G)) =
        cmap c (pPrimeCoreOf 2 (centralizer ({c⁻¹ * a * c} : Set G))) := by
      have := centralizer_conj_eq c (c⁻¹ * a * c)
      rw [show c * (c⁻¹ * a * c) * c⁻¹ = a by group] at this
      rw [this, pPrimeCoreOf_cmap]
    rw [hC]
    exact Subgroup.map_mono (pPrimeCoreOf_le_thetaGA ha ha1')
  · unfold thetaGA cmap
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha1 => ?_
    have hmem : c * a * c⁻¹ ∈ cmap c A := by
      rw [mem_cmap, show c⁻¹ * (c * a * c⁻¹) * c = a by group]
      exact ha
    have hne : c * a * c⁻¹ ≠ 1 := fun h => ha1 (by
      have := congrArg (fun t => c⁻¹ * t * c) h
      simpa [mul_assoc] using this)
    have hC := centralizer_conj_eq c a
    have := pPrimeCoreOf_le_thetaGA (A := cmap c A) hmem hne
    rw [hC, pPrimeCoreOf_cmap] at this
    exact this

omit [Finite G] in
theorem cmap_eq_of_mem_normalizer {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    cmap g Q = Q := by
  ext x
  rw [mem_cmap]
  have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
  rw [inv_inv] at h1
  exact h1.symm

omit [Finite G] in
theorem mem_normalizer_of_cmap_eq {H : Subgroup G} {g : G} (h : cmap g H = H) :
    g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2 : g * x * g⁻¹ ∈ H ↔ g⁻¹ * (g * x * g⁻¹) * g ∈ H := by
    have := (SetLike.ext_iff.mp h.symm) (g * x * g⁻¹)
    rwa [mem_cmap] at this
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2
  exact h2.symm

omit [Finite G] in
theorem normalizer_le_normalizer_thetaGA
    (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (thetaGA Q : Set G) := by
  intro g hg
  apply mem_normalizer_of_cmap_eq
  rw [← thetaGA_cmap, cmap_eq_of_mem_normalizer hg]

theorem exists_chain_member (hr : pRank 2 G = 4) {S U A : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hA : IsEStar A) (hAS : A ≤ S) (hU : IsNormalFourOf S U) :
    ∃ A' : Subgroup G, IsEStar A' ∧ U ≤ A' ∧ 4 ≤ Nat.card ↥(A ⊓ A') := by
  have hAcard : Nat.card ↥A = 16 := by rw [hA.2, hr]; norm_num
  by_cases hUA : U ≤ A
  · exact ⟨A, hA, hUA, by rw [inf_idem, hAcard]; norm_num⟩
  set A₀ : Subgroup G := A ⊓ centralizer (U : Set G) with hA₀
  have hrelS := (CFSG.GH74.Uniqueness.SU.SU1.ig10_20_ii Nat.prime_two hS hU.isNormalEp2).2.1
  have hrelA : (centralizer (U : Set G)).relIndex A ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hAS (CFSG.GH74.Uniqueness.SU.SU1.relIndex_ne_zero_of_finite _ _)).trans
      hrelS
  have hmul := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := A)
  have h0 : (centralizer (U : Set G)).relIndex A ≠ 0 :=
    CFSG.GH74.Uniqueness.SU.SU1.relIndex_ne_zero_of_finite _ _
  have hA₀card : 8 ≤ Nat.card ↥A₀ := by
    rw [hA₀, inf_comm]
    rw [hAcard] at hmul
    have : Nat.card ↥(centralizer (U : Set G) ⊓ A) * 2 ≥ 16 := by nlinarith [Nat.pos_of_ne_zero h0]
    omega
  have hA₀A : A₀ ≤ A := inf_le_left
  have hA₀el : Open.IsElemAbelian 2 A₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A₀).mp (hA.sub hA₀A)
  have hUel : Open.IsElemAbelian 2 U :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mp hU.1.1
  have hsup := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hA₀el hUel
    (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm)
  have hlt : A₀ < A₀ ⊔ U := by
    refine lt_of_le_of_ne le_sup_left fun h => hUA ?_
    have : U ≤ A₀ := h ▸ le_sup_right
    exact this.trans hA₀A
  obtain ⟨t, ht⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hsup
  have hA'el : CFSG.IsElementaryAbelian 2 ↥(A₀ ⊔ U) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hsup
  have htle : t ≤ pRank 2 G := le_pRank_group_of_elem hA'el ht
  have hcl := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [ht] at hcl
  have ht4 : 4 ≤ t := by
    by_contra hlt4
    have : 2 ^ t ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ht' : t = 4 := by omega
  refine ⟨A₀ ⊔ U, ⟨hA'el, by rw [ht, ht', hr]⟩, le_sup_right, ?_⟩
  have hle : A₀ ≤ A ⊓ (A₀ ⊔ U) := le_inf hA₀A le_sup_left
  have := Subgroup.card_le_of_le hle
  omega

theorem theta_eq_of_le (hr : pRank 2 G = 4) (T4 : St1Thm4 G) {S A B : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hA : IsEStar A) (hB : IsEStar B) (hAS : A ≤ S) (hBS : B ≤ S) :
    thetaGA B = thetaGA A := by
  have hr3 : 3 ≤ pRank 2 G := by omega
  have h3 : 3 ≤ pRank 2 ↥S :=
    (by rw [hr] at *; omega : 3 ≤ 4).trans (le_pRank_of_elem hAS hA.1 (k := 4) (by rw [hA.2, hr]))
  obtain ⟨U, hU⟩ := exists_normalFour hS h3
  obtain ⟨A', hA', hUA', hAA'⟩ := exists_chain_member hr hS hA hAS hU
  obtain ⟨B', hB', hUB', hBB'⟩ := exists_chain_member hr hS hB hBS hU
  have e1 : thetaGA A = thetaGA A' :=
    le_antisymm (thetaGA_le_of_common hA hr3 (T4 A hA) inf_le_left inf_le_right hAA')
      (thetaGA_le_of_common hA' hr3 (T4 A' hA') inf_le_right inf_le_left hAA')
  have e2 : thetaGA B = thetaGA B' :=
    le_antisymm (thetaGA_le_of_common hB hr3 (T4 B hB) inf_le_left inf_le_right hBB')
      (thetaGA_le_of_common hB' hr3 (T4 B' hB') inf_le_right inf_le_left hBB')
  have e3 : thetaGA A' = thetaGA B' :=
    le_antisymm (thetaGA_le_of_common hA' hr3 (T4 A' hA') hUA' hUB' hU.1.2.ge)
      (thetaGA_le_of_common hB' hr3 (T4 B' hB') hUB' hUA' hU.1.2.ge)
  exact (e2.trans e3.symm).trans e1.symm

theorem four_le_card_of_two_le_pRank {Q : Subgroup G} (h2 : 2 ≤ pRank 2 ↥Q) : 4 ≤ Nat.card ↥Q := by
  obtain ⟨E, hEQ, -, hEcard⟩ := exists_elemAbelian_card_pRank Q
  have h1 := Subgroup.card_le_of_le hEQ
  rw [hEcard] at h1
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ pRank 2 ↥Q := Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ Nat.card ↥Q := h1

theorem gammaK_two_le_of_theta
    (hr : pRank 2 G = 4) (T4 : St1Thm4 G) {S A B M : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hA : IsEStar A) (hB : IsEStar B) (hAS : A ≤ S) (hBS : B ≤ S)
    (hMN : normalizer (thetaGA A : Set G) ≤ M) : gammaK 2 B 2 ≤ M := by
  refine iSup₂_le fun Q hQB => iSup_le fun hQ2 => ?_
  have hr3 : 3 ≤ pRank 2 G := by omega
  have hth : thetaGA Q = thetaGA B :=
    le_antisymm (thetaGA_mono hQB)
      (thetaGA_le_of_common hB hr3 (T4 B hB) hQB le_rfl (four_le_card_of_two_le_pRank hQ2))
  refine (normalizer_le_normalizer_thetaGA Q).trans ?_
  rw [hth, theta_eq_of_le hr T4 hS hA hB hAS hBS]
  exact hMN

theorem gammaK_S_le_of_theta
    (hr : pRank 2 G = 4) (T4 : St1Thm4 G) {S A M : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hA : IsEStar A) (hAS : A ≤ S)
    (hMN : normalizer (thetaGA A : Set G) ≤ M) : gammaK 2 S (pRank 2 G) ≤ M := by
  refine iSup₂_le fun Q hQS => iSup_le fun hQr => ?_
  have hQrank : pRank 2 ↥Q = pRank 2 G := le_antisymm (Bg.pRank_subgroup_le one_lt_two Q) hQr
  obtain ⟨A₀, hA₀Q, hA₀⟩ := exists_isEStar_le hQrank
  intro g hg
  have hcA : IsEStar (cmap g A₀) := isEStar_cmap hA₀ g
  have hcQ : cmap g A₀ ≤ S := by
    have h1 : cmap g A₀ ≤ cmap g Q := Subgroup.map_mono hA₀Q
    rw [cmap_eq_of_mem_normalizer hg] at h1
    exact h1.trans hQS
  have e1 : thetaGA (cmap g A₀) = thetaGA A := theta_eq_of_le hr T4 hS hA hcA hAS hcQ
  have e2 : thetaGA A₀ = thetaGA A := theta_eq_of_le hr T4 hS hA hA₀ hAS (hA₀Q.trans hQS)
  have e3 : cmap g (thetaGA A) = thetaGA A :=
    calc cmap g (thetaGA A) = cmap g (thetaGA A₀) := by rw [e2]
      _ = thetaGA (cmap g A₀) := (thetaGA_cmap g A₀).symm
      _ = thetaGA A := e1
  exact hMN (mem_normalizer_of_cmap_eq e3)

theorem le_of_inf_normalizer_le {S S' : Subgroup G} (hS' : IsPGroup 2 ↥S') (hSS' : S ≤ S')
    (h : S' ⊓ normalizer (S : Set G) ≤ S) : S' ≤ S := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set IP : Subgroup ↥S' := S.subgroupOf S' with hIP
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hne
    intro x hx
    have hxIP : (⟨x, hx⟩ : ↥S') ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hxIP
  have hIPlt : IP < ⊤ := lt_of_le_of_ne le_top hIPne
  have : Group.IsNilpotent ↥S' := hS'.isNilpotent
  have hnc : NormalizerCondition ↥S' := Group.normalizerCondition_of_isNilpotent (G := ↥S')
  have hlt : IP < normalizer (IP : Set ↥S') := hnc IP hIPlt
  obtain ⟨x, hxN, hxnotIP⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ normalizer (S : Set G) := by
    have hxsub : x ∈ (normalizer (S : Set G)).subgroupOf S' := by
      rw [Subgroup.subgroupOf_normalizer_eq hSS']
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnotIP (Subgroup.mem_subgroupOf.mpr (h ⟨x.2, hxNorm⟩))

theorem isSylowOf_top_of_theta
    (hr : pRank 2 G = 4) (T4 : St1Thm4 G) {S A M : Subgroup G}
    (hSM : IsSylowOf 2 S M) (hA : IsEStar A) (hAS : A ≤ S)
    (hMN : normalizer (thetaGA A : Set G) ≤ M) : IsSylowOf 2 S ⊤ := by
  have hSp : IsPGroup 2 ↥S := hSM.isPGroup
  have hSrank : pRank 2 G ≤ pRank 2 ↥S := le_pRank_of_elem hAS hA.1 (k := pRank 2 G) hA.2
  have hNS : normalizer (S : Set G) ≤ M :=
    (le_iSup₂_of_le S le_rfl (le_iSup_of_le hSrank le_rfl) : normalizer (S : Set G) ≤
      gammaK 2 S (pRank 2 G)).trans (gammaK_S_le_of_theta hr T4 hSp hA hAS hMN)
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowOf_ge (N := ⊤) (K := S) le_top hSp
  have hH : S' ⊓ normalizer (S : Set G) = S :=
    hSM.eq_of_le (le_inf hSS' Subgroup.le_normalizer) (inf_le_right.trans hNS)
      hS'.isPGroup.to_inf_left
  have hS'S : S' ≤ S := le_of_inf_normalizer_le hS'.isPGroup hSS' hH.le
  rwa [le_antisymm hS'S hSS'] at hS'

end MProps

@[expose] def B_iv2_8_10a : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → St1Thm4 G →
    ∀ (A M S : Subgroup G), IsEStar A →
      (∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) →
        IsCoatom M → normalizer (thetaGA A : Set G) ≤ M → IsSylowOf 2 S M → A ≤ S →
          ∀ t ∈ M, orderOf t = 2 → pRank 2 ↥(centralizer ({t} : Set G) ⊓ M) = pRank 2 ↥M →
            t ∈ ⁅M, M⁆

end CFSG.GH74.GLS
