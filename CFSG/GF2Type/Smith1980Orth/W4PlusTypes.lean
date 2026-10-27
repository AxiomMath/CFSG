module

public import CFSG.GF2Type.Smith1980Orth.W4PlusP3
public import CFSG.GF2Type.Smith1980Orth.W4PlusInv
public import CFSG.GF2Type.Smith1980Orth.W4PlusSum
public import CFSG.GF2Type.Smith1980Orth.S3Good
public import CFSG.GF2Type.Smith1980Orth.S3Count
public import CFSG.GF2Type.Smith1980Orth.S3ThmACaseI
public import CFSG.GF2Type.Smith1980Orth.S3ThmAW4
public import CFSG.LargeExtraspecial.S14SMFOne
public import CFSG.LargeExtraspecial.S14SMKTransLift
public import CFSG.LargeExtraspecial.S3bThirteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem types_base_of_card (hw : S.width = 4) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z)) (ha₀ : D.g * S.z * D.g⁻¹ ∈ S.Qa k)
    (hΔ8 : 8 ≤ Nat.card (S.QG ⊓ S.Qa k : Subgroup G)) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) := by
  classical
  have haQ : D.g * S.z * D.g⁻¹ ∈ S.QG := D.good.H.conj_mem
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hax : D.g * S.z * D.g⁻¹ ≠ k * S.z * k⁻¹ := fun h => hxQ (h ▸ haQ)
  have hxa : k * S.z * k⁻¹ ∈ S.Qa D.g := S.mem_Qa_symm hax ha₀
  have hL : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∈ S.Lbar D.g := S.ρ_mem_Lbar ⟨hxa, hxM⟩
  obtain ⟨c, hc, hxc⟩ := D.exists_eq_mul_of_mem_Lbar hL
  obtain ⟨d, hd, hcd⟩ := D.exists_eichler_of_mem_Lbar_inf_Cbar D.QV_nondegenerate D.QV_aV
    D.LmodN_eq_pointRadical hc
  have hcomm : S.commQt (k * S.z * k⁻¹) =
      commSpace ((S.ρ ⟨k * S.z * k⁻¹, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    S.commQt_of_mem hxM
  have hΔle : S.clSub (S.QG ⊓ S.Qa k) ≤ S.commQt (k * S.z * k⁻¹) :=
    S14.SMK.clSub_Dl_le_commQt S hxM hxQ hxz
  have hΔcard : 8 ≤ Nat.card (S.clSub (S.QG ⊓ S.Qa k)) := by
    rw [S14.SMK.card_clSub_Dl S hxQ]
    exact hΔ8
  have haΔ : D.coord (aV D.good.ht, 0) ∈ S.clSub (S.QG ⊓ S.Qa k) := by
    rw [D.coord_apply_zero_right]
    exact S.cl_mem_clSub ⟨haQ, ha₀⟩ haQ
  have hzΔ : S.z ∉ S.QG ⊓ S.Qa k := S14.SMK.z_not_mem_Dl S hxQ
  have hq0 : ∀ {v : S.Qt}, v ∈ S.clSub (S.QG ⊓ S.Qa k) → S.q v = 0 := by
    intro v hv
    refine q_eq_zero_of_mem_commQt_of_mem_clSub hxM hx2 (hΔle hv) ?_
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
    exact S.cl_mem_clSub ⟨hy.1, (S.conjBy k).QG_le_M hy.2⟩ hyQ
  have h116 : ∀ y ∈ S.QG ⊓ S.Qa k, y ≠ 1 → ¬ IsConj S.z y →
      IsConj (k * S.z * k⁻¹ * S.z) y := by
    intro y hy hy1 hyc
    have hyx : Commute (k * S.z * k⁻¹) y := by
      have h := (S.conjBy k).mem_M_iff.mp ((S.conjBy k).QG_le_M hy.2)
      exact h.symm
    rcases S14.SMF.isConj_of_mem_J S hxM hxQ hy1 (S14.SMK.Dl_le_commutator S hxM hxQ hxz hy) hyx
      hy.2 with h | h
    · exact absurd h hyc
    · exact h
  have hIsSum : ∀ y₁ ∈ S.QG ⊓ S.Qa k, ∀ y₂ ∈ S.QG ⊓ S.Qa k, y₁ ≠ 1 → y₂ ≠ 1 →
      ¬ IsConj S.z y₁ → ¬ IsConj S.z y₂ →
        (D.IsSum2 (S.cl y₁) ↔ D.IsSum2 (S.cl y₂)) := by
    intro y₁ hy₁ y₂ hy₂ h1 h2 hc1 hc2
    obtain ⟨g', hg'⟩ := isConj_iff.mp (((h116 y₁ hy₁ h1 hc1).symm).trans (h116 y₂ hy₂ h2 hc2))
    have hz₁ : y₁ ≠ S.z := fun e => hzΔ (e ▸ hy₁)
    have hz₂ : y₂ ≠ S.z := fun e => hzΔ (e ▸ hy₂)
    obtain ⟨m, hm, hmy⟩ := S.lemma_3_13 (by omega) D.good.noAll hy₁.1 h1 hz₁
      (by rw [hg']; exact hy₂.1) (by rw [hg']; exact hz₂)
    have hcl : S.cl y₂ = ((S.ρ ⟨m, hm⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y₁) := by
      rw [S.ρ_cl ⟨m, hm⟩ hy₁.1]
      show S.cl y₂ = S.cl (m * y₁ * m⁻¹)
      rw [hmy, hg']
    have hmb : S.ρ ⟨m, hm⟩ ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hcl]
    exact (D.isSum2_apply hmb _).symm
  have hIsSum2_iff : ∀ {v : S.Qt}, v ∈ S.clSub (S.QG ⊓ S.Qa k) →
      finrank (ZMod 2) (D.span2 v) = 2 →
      (D.IsSum2 v ↔ ∀ w ∈ D.span2 v, D.QV w = 0) := by
    intro v hv h2
    obtain ⟨⟨u, v'⟩, rfl⟩ := D.coord.surjective v
    have hβ : polar D.QV u v' = 0 := by
      have h0 := hq0 hv
      rwa [D.q_coord, ← D.polar_QV] at h0
    exact D.isSum2_coord_iff h2 hβ
  have hlift : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa k), (finrank (ZMod 2) (D.span2 v) = 2 ∨
      ∃ w ∈ D.span2 v, D.QV w ≠ 0) →
      ∃ y ∈ S.QG ⊓ S.Qa k, y ≠ 1 ∧ ¬ IsConj S.z y ∧ S.cl y = v := by
    intro v hv hv'
    obtain ⟨y, hy, -, rfl⟩ := S.mem_clSub_iff.mp hv
    have hyz : y ≠ S.z := fun e => hzΔ (e ▸ hy)
    refine ⟨y, hy, fun e => ?_, fun hyc => ?_, rfl⟩
    · have h0 : D.span2 (S.cl y) = ⊥ := by
        rw [e, S.cl_one, show (0 : S.Qt) = D.coord (0, 0) by rw [Prod.mk_zero_zero, map_zero],
          D.span2_coord]
        simp
      rcases hv' with h | ⟨w, hw', hwQ⟩
      · rw [h0, finrank_bot] at h
        omega
      · rw [h0, Submodule.mem_bot] at hw'
        rw [hw', map_zero] at hwQ
        exact hwQ rfl
    · obtain ⟨h1, h2⟩ := D.span2_cl_of_isConj hy.1 hyz hyc
      rcases hv' with h | ⟨w, hw', hwQ⟩
      · omega
      · exact hwQ (h2 w hw')
  by_cases hdA : d ∈ (ZMod 2) ∙ aV D.good.ht
  ·
    have hc1 : c = 1 := by
      have he : eichler D.QV (aV D.good.ht) d = 1 :=
        (eichler_eq_one_iff D.QV_nondegenerate (aV_ne_zero D.good.H D.good.ht) D.QV_aV
          hd).mpr hdA
      refine D.eq_of_apply_eq_of_mem_Vt hc.2 (one_mem _) fun v hv => ?_
      rw [hcd ⟨v, hv⟩, he]
      rfl
    rcases hxc with h | h
    · exact absurd ((S.ρ_eq_one_iff _).mp (h.trans hc1)) hxQ
    · left
      rw [h, hc1, mul_one]
      exact Or.inl rfl
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (D.QV d) with hd0 | hd1
  · rcases hxc with h | h
    ·
      right
      rw [h]
      refine ⟨hc.2, ?_⟩
      have he : D.resC ⟨c, hc.2⟩ = eichler D.QV (aV D.good.ht) d :=
        LinearEquiv.ext fun v => Subtype.ext ((D.coe_resC_apply _ v).trans (hcd v))
      rw [he]
      exact (eichler_type_of_not_mem_span D.QV_nondegenerate (aV_ne_zero D.good.H D.good.ht)
        D.QV_aV hd hdA).2.1 hd0
    ·
      exfalso
      have hU : S.clSub (S.QG ⊓ S.Qa k) ≤
          commSpace ((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← h, ← hcomm]
        exact hΔle
      obtain ⟨y₁, hy₁, y₂, hy₂, hf₁, hf₂, hs₁, w, hw', hwQ⟩ :=
        D.exists_span2_of_t_mul_typeA hw hc.2 hd hd0 hdA hcd hU haΔ hΔcard
      obtain ⟨e₁, he₁, he₁1, he₁c, rfl⟩ := hlift y₁ hy₁ (Or.inl hf₁)
      obtain ⟨e₂, he₂, he₂1, he₂c, rfl⟩ := hlift y₂ hy₂ (Or.inl hf₂)
      have h1 : D.IsSum2 (S.cl e₁) := (hIsSum2_iff hy₁ hf₁).mpr hs₁
      have h2 : D.IsSum2 (S.cl e₂) := (hIsSum e₁ he₁ e₂ he₂ he₁1 he₂1 he₁c he₂c).mp h1
      exact hwQ ((hIsSum2_iff hy₂ hf₂).mp h2 w hw')
  · rcases hxc with h | h
    ·
      exfalso
      have hU : S.clSub (S.QG ⊓ S.Qa k) ≤ commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← h, ← hcomm]
        exact hΔle
      have hkU : ∀ y ∈ S.clSub (S.QG ⊓ S.Qa k),
          (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) y ∈ S.clSub (S.QG ⊓ S.Qa k) := fun y hy =>
        clSub_Dl_apply_mem hxM hxz D.k_mem_Mbar (by rw [h]; exact (D.Cbar_comm_k hc.2).symm) hy
      obtain ⟨y₁, hy₁, y₂, hy₂, hf₁, ⟨w, hw', hwQ⟩, hf₂⟩ :=
        D.exists_span2_of_typeC hc.2 hd hd1 hcd hU haΔ hkU hΔcard
      obtain ⟨e₁, he₁, he₁1, he₁c, rfl⟩ := hlift y₁ hy₁ (Or.inr ⟨w, hw', hwQ⟩)
      obtain ⟨e₂, he₂, he₂1, he₂c, rfl⟩ := hlift y₂ hy₂ (Or.inl hf₂)
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hd1
        exact zero_ne_one hd1
      have hda : aV D.good.ht ≠ d := by
        rintro rfl
        exact hdA (Submodule.mem_span_singleton_self _)
      have hli : LinearIndependent (ZMod 2) ![aV D.good.ht, d] :=
        OrthoF2.linearIndependent_pair_iff.mpr
          ⟨aV_ne_zero D.good.H D.good.ht, hd0, hda⟩
      have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) {aV D.good.ht, d}) = 2 :=
        OrthoF2.finrank_span_pair hli
      have hle : D.span2 (S.cl e₂) ≤ Submodule.span (ZMod 2) {aV D.good.ht, d} :=
        D.span2_le_of_mem_commSpace_eichler hc.2 hcd (hU hy₂)
      have heq : D.span2 (S.cl e₂) = Submodule.span (ZMod 2) {aV D.good.ht, d} :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hf₂, hdim])
      have hnot : ¬ ∀ w ∈ D.span2 (S.cl e₂), D.QV w = 0 := by
        intro h
        have h0 := h d (by rw [heq]; exact Submodule.subset_span (by simp))
        rw [h0] at hd1
        exact zero_ne_one hd1
      exact hnot ((hIsSum2_iff hy₂ hf₂).mp
        ((hIsSum e₁ he₁ e₂ he₂ he₁1 he₂1 he₁c he₂c).mp
          (D.isSum2_of_finrank_one hf₁ ⟨w, hw', hwQ⟩)))
    ·
      exfalso
      obtain ⟨y, hy, hyq⟩ := D.exists_q_ne_zero_of_t_mul_typeC hc.2 hd hd1 hcd
      have hy' : y ∈ S.commQt (k * S.z * k⁻¹) := by
        rw [hcomm, h]
        exact hy
      have hfix := S.commQt_le_fixQt hxM hx2 hy'
      rw [S14.SMK.fixQt_eq_of_not_isConj S hxM hxz] at hfix
      exact hyq (q_eq_zero_of_mem_commQt_of_mem_clSub hxM hx2 hy' hfix)

theorem types_of_base
    (hbase : ∀ {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M), k * S.z * k⁻¹ ∉ S.QG →
      ¬ IsConj S.z (k * S.z * k⁻¹ * S.z) → D.g * S.z * D.g⁻¹ ∈ S.Qa k →
        D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩))
    {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z))
    (hgood : ∃ a, IsConj S.z a ∧ a ∈ S.QG ⊓ S.Qa k) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) := by
  obtain ⟨a, haconj, haQ, haQk⟩ := hgood
  obtain ⟨h, rfl⟩ := isConj_iff.mp haconj
  have hxz' : k * S.z * k⁻¹ ≠ S.z := fun h' => hxQ (by
    rw [h']
    exact S.z_mem_QG)
  have haz : h * S.z * h⁻¹ ≠ S.z := by
    intro h'
    apply hxQ
    have hz : S.z ∈ S.Qa k := h' ▸ haQk
    have h1 := S.mem_Qa_symm (g₁ := 1) (g₂ := k) (by simpa using hxz'.symm) (by simpa using hz)
    rw [S.Qa_one] at h1
    exact h1
  obtain ⟨m, hm, hm1, hmh⟩ := D.exists_conj_eq_of_mem_M1 haQ haz
  obtain ⟨k', hk'⟩ : ∃ k' : G, k' = m⁻¹ * k := ⟨_, rfl⟩
  have hx' : k' * S.z * k'⁻¹ = m⁻¹ * (k * S.z * k⁻¹) * m := by rw [hk']; group
  have hx'M : k' * S.z * k'⁻¹ ∈ S.M := by
    rw [hx']
    exact (S.conj_mem_M_iff hm).mpr hxM
  have hx'Q : k' * S.z * k'⁻¹ ∉ S.QG := by
    intro hQ
    apply hxQ
    rw [hx'] at hQ
    have := S.conj_mem_QG hm hQ
    rwa [show m * (m⁻¹ * (k * S.z * k⁻¹) * m) * m⁻¹ = k * S.z * k⁻¹ by group] at this
  have hx'z : ¬ IsConj S.z (k' * S.z * k'⁻¹ * S.z) := by
    intro hc
    apply hxz
    have e : k' * S.z * k'⁻¹ * S.z = m⁻¹ * (k * S.z * k⁻¹ * S.z) * m := by
      rw [hx']
      have hzm : S.z * m = m * S.z := (S.z_comm hm).symm
      calc m⁻¹ * (k * S.z * k⁻¹) * m * S.z = m⁻¹ * (k * S.z * k⁻¹) * (m * S.z) := by group
        _ = m⁻¹ * (k * S.z * k⁻¹) * (S.z * m) := by rw [hzm]
        _ = m⁻¹ * (k * S.z * k⁻¹ * S.z) * m := by group
    rw [e] at hc
    exact hc.trans (isConj_iff.mpr ⟨m, by group⟩)
  have ha₀ : D.g * S.z * D.g⁻¹ ∈ S.Qa k' := by
    rw [hk', S.mem_Qa_mul_iff, inv_inv]
    rw [show m * (D.g * S.z * D.g⁻¹) * m⁻¹ = h * S.z * h⁻¹ from hmh]
    exact haQk
  have key := hbase hx'M hx'Q hx'z ha₀
  have hxe : (⟨k * S.z * k⁻¹, hxM⟩ : S.M) =
      ⟨m, hm⟩ * ⟨k' * S.z * k'⁻¹, hx'M⟩ * (⟨m, hm⟩ : S.M)⁻¹ := by
    refine Subtype.ext ?_
    show k * S.z * k⁻¹ = m * (k' * S.z * k'⁻¹) * m⁻¹
    rw [hx']
    group
  have hρ : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ =
      S.ρ ⟨m, hm⟩ * S.ρ ⟨k' * S.z * k'⁻¹, hx'M⟩ * (S.ρ ⟨m, hm⟩)⁻¹ := by
    rw [hxe, map_mul, map_mul, map_inv]
  rw [hρ]
  rcases key with h1 | h1
  · exact Or.inl (D.isTInv_conj_of_mem_M1 h1 hm1)
  · exact Or.inr (D.isUInv_conj_of_mem_M1 h1 hm1)

section Full

variable (D : S2Data S)

theorem types_base_of_width_eq_four (hw : S.width = 4) (DT : S2Data (S.conjBy D.g)) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z)) (ha₀ : D.g * S.z * D.g⁻¹ ∈ S.Qa k) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) := by
  have haQ : D.g * S.z * D.g⁻¹ ∈ S.QG := D.good.H.conj_mem
  have hxa : k * S.z * k⁻¹ ∈ S.Qa D.g :=
    S.mem_Qa_symm (fun h => hxQ (h ▸ haQ)) ha₀
  exact D.types_base_of_card hw hxM hxQ hxz ha₀
    (eight_le_card_QG_inf_Qa haQ D.good.H.conj_ne DT hxM hxQ hxa)

end Full

end S2Data

theorem OrthData.oTypes_of_width_eq_four' [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S) (hw : S.width = 4) (D : S2Data S) :
    D.OTypes := by
  intro x hx hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  have h34a := O.oe34a_of_width_eq_four I hAS4 hThmA hres hw
  have hw' : (S.conjBy D.g).width = 4 := by rw [Setting.width_conjBy]; exact hw
  obtain ⟨DT⟩ := exists_s2Data_of_width_eq_four I hAS4 hThmA hres (O.conjBy D.g) hw'
  refine D.types_of_base (fun {k'} hx'M hx'Q hx'z ha₀ =>
    D.types_base_of_width_eq_four hw DT hx'M hx'Q hx'z ha₀) hxM hxQ
    (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ)
    (exists_of_not_bad (O.not_bad_of_width_eq_four I hAS4 hThmA hres hw k) hxM hxQ)

end CFSG.GF2Type.Smith1980Orth
