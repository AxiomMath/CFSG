module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Fstar
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Gold
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueAssembly
public import CFSG.LieType.Multipliers.U43
import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.M24Std.CSide

theorem isSimpleGroup_X₀' : IsSimpleGroup CFSG.LieType.Multipliers.U43.X₀ := by
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    CFSG.LieType.Multipliers.U43.F9 3 1
    (by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num) 4
    (by norm_num) (by simp)
  rwa [pow_one] at h

theorem residue_cU43
    (hG : Goldschmidt74Cor4) :
    Ega81CaseU43 := by
  intro G _ _ L z _ _ hs A B C D hF he
  classical
  have h : CSide.Setup L A C z := ⟨hs, hF.pair.1, hF.sextet, hF.cData, hF.c_elem⟩
  have hty : SextetType L A := hF.pair.sextet
  obtain ⟨hAL, e0, hA⟩ := id hty
  have hσs := Sym6.tetE_surjective hA hAL
  have hσA := Sym6.le_ker_tetE hA
  have hσk := Sym6.card_ker_tetE hA hAL
  let H : Subgroup (egNL L A) := (alternatingGroup (Fin 6)).comap (Sym6.tetE hA)
  have hH : H.index = 2 := (Sym6.index_two_iff hA hAL H).2 rfl
  obtain ⟨φ, hφ, -⟩ := exists_hom_centralizer h (Sym6.tetE hA) hσs hσA hσk
  obtain ⟨-, -, hP, -⟩ := exists_sigma_centralizer h (Sym6.tetE hA) hσs hσA hσk
  have hφk : Nat.card φ.ker = 3 := by
    have c := natCard_eq_of_surjective φ hφ
    rw [hP, Nat.card_prod] at c
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 2
    have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h2, h6] at c
    omega
  set O : Subgroup (egQD C) := fusionOddCore (egQD C) with hOdef
  have hO : Odd (Nat.card O) := odd_natCard_fusionOddCore _
  have hX : ∀ N : Subgroup (egQD C ⧸ O), N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd'
    have h' := standardComponentOddCore_quotient_fusionOddCore_eq_bot (egQD C)
    exact le_bot_iff.1 (h' ▸ le_sSup ⟨hN, hodd'⟩)
  set E : Subgroup (egQD C ⧸ O) := egaLayer (egQD C ⧸ O) with hEdef
  have hEn : E.Normal := egaLayer_normal _
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ he
  let θ : E ≃* P := eX.trans CU43.psiEquiv
  have hEs : IsSimpleGroup E := by
    have := isSimpleGroup_X₀'
    exact eX.isSimpleGroup
  have hEcard : Nat.card E = 3265920 := by
    rw [Nat.card_congr eX.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]
  have hz2 : zt h * zt h = 1 := zt_mul_self h
  have hz1 : zt h ≠ 1 := fun h1 => by
    have := orderOf_zt h
    rw [h1, orderOf_one] at this
    omega
  have hC0 : centralizer (E : Set (egQD C ⧸ O)) = ⊥ :=
    centralizer_layer_eq_bot O hO hX hz2 hz1 φ hφ hφk hP E rfl hEs hEcard
  set ζ : egQD C ⧸ O := QuotientGroup.mk' O (zt h) with hζdef
  have hζ2 : ζ * ζ = 1 := by rw [hζdef, ← map_mul, hz2, map_one]
  have hdvd : Nat.card (centralizer ({ζ} : Set (egQD C ⧸ O))) ∣ 4320 := by
    have hcop : centralizer ({ζ} : Set (egQD C ⧸ O)) ≤
        (centralizer ({zt h} : Set (egQD C))).map (QuotientGroup.mk' O) :=
      CFSG.Walter.Suzuki.centralizer_mk_le_map O hO hz2
    exact (Subgroup.card_dvd_of_le hcop).trans ((Subgroup.card_map_dvd _ _).trans (hP ▸ dvd_rfl))
  have hidx : E.index = 2 := frame_index E θ hC0 hζ2 hdvd
  have hζE : ζ ∉ E := frame_not_mem E θ hC0 hζ2 hdvd
  have hCab := h.hC.comm
  let fx : egQD C → ℕ := fxFun (actC C hCab)
  have hfix : ∀ (g : G) (hg : g ∈ normalizer (C : Set G)),
      Nat.card (fixSub C g) = fx (qdMk C ⟨g, hg⟩) := by
    intro g hg
    have : fixSub C g = fixAut (actC C hCab (qdMk C ⟨g, hg⟩)) := by
      ext c
      show g * (c : G) * g⁻¹ = c ↔ (actC C hCab (qdMk C ⟨g, hg⟩)) c = c
      rw [show qdMk C ⟨g, hg⟩ = QuotientGroup.mk ⟨g, hg⟩ from rfl, actC_mk]
      constructor
      · intro h1
        exact Subtype.ext h1
      · intro h1
        exact congrArg Subtype.val h1
    rw [this]
    rfl
  obtain ⟨t₀, ht₀2, ht₀A, ht₀H⟩ := Sym6.exists_involution_not_mem hA hAL
  have ht₀notH : t₀ ∉ H := ht₀H H hH
  have hψC : ∀ n : egNL L A, psi h n ∈ centralizer ({zt h} : Set (egQD C)) := fun n =>
    mem_centralizer_singleton_iff.2 (psi_comm h n)
  have hψ2 : psi h t₀ * psi h t₀ = 1 := by rw [← map_mul, ht₀2, map_one]
  have hψ1 : psi h t₀ ≠ 1 := fun h1 => by
    rw [← MonoidHom.mem_ker, ker_psi h] at h1
    exact ht₀A (mem_subgroupOf.1 h1)
  have hgood : ∃ u : egQD C, (u = psi h t₀ ∨ u = psi h t₀ * zt h) ∧ u * u = 1 ∧ u ≠ 1 ∧
      QuotientGroup.mk' O u ∈ E := by
    by_cases hmem : QuotientGroup.mk' O (psi h t₀) ∈ E
    · exact ⟨psi h t₀, Or.inl rfl, hψ2, hψ1, hmem⟩
    · refine ⟨psi h t₀ * zt h, Or.inr rfl, ?_, ?_, ?_⟩
      · calc psi h t₀ * zt h * (psi h t₀ * zt h)
            = (psi h t₀ * psi h t₀) * (zt h * zt h) := by
              have hc : Commute (psi h t₀) (zt h) := psi_comm h t₀
              rw [mul_assoc, ← mul_assoc (zt h), hc.symm.eq, mul_assoc, ← mul_assoc]
          _ = 1 := by rw [hψ2, hz2, one_mul]
      · intro h1
        apply zt_not_mem_range h
        refine ⟨t₀⁻¹, ?_⟩
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_right h1).symm
      · rw [map_mul, Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false hmem hζE
  obtain ⟨u, hue, hu2, hu1, huE⟩ := hgood
  have hfxu : fx u ≤ 64 := by
    obtain ⟨⟨g, hg⟩, hgu⟩ := QuotientGroup.mk'_surjective
      (C.subgroupOf (normalizer (C : Set G))) u
    have hgu' : qdMk C ⟨g, hg⟩ = u := hgu
    have hdn : qdMk C ⟨g, hg⟩ = psi h t₀ ∨ qdMk C ⟨g, hg⟩ = psi h t₀ * zt h := by
      rw [hgu']
      exact hue
    have := (card_fixSub_le_of_involution h hty hH hg t₀ hdn (by rw [hgu']; exact hu2)
      (by rw [hgu']; exact hu1)).2 ht₀notH
    rwa [hfix g hg, hgu'] at this
  have hcore : CoreHyp O E fx u :=
    { odd := hO
      index := hidx
      conj := fun s s' hs hs' h2 h2' h1 h1' => inner_conj E θ hC0 hs hs' h2 h2' h1 h1'
      rank := fun B hBE h2 => card_le_sixteen_of_le E θ hC0 hBE h2
      noncentral := fun d hd hd2 S hS => not_le_centralizer_of_outer E θ hC0 hidx hd hd2 hS
      fx_conj := fxFun_conj _
      fx_pow := fxFun_le_pow _
      fx_mul := fun y y' => by
        have := fxFun_mul_le (actC C hCab) y y'
        rwa [show Nat.card C = 4096 from h.hC.card] at this
      u_sq := hu2
      u_ne := hu1
      u_mem := huE
      fx_u := hfxu }
  refine CSide.false_of_sylow_bound hG (m := 32) (by norm_num) h hty fun n hn2 hnA => ?_
  have hpsi2 : psi h n * psi h n = 1 := by rw [← map_mul, hn2, map_one]
  have hzp : IsPGroup 2 (zpowers (psi h n)) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf (psi h n) ∣ 2 ^ 1 from
        orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hpsi2))
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hSc := hcore.sylow_conditions S.isPGroup' S.not_dvd_index
  refine ⟨(S : Subgroup (egQD C)), S.isPGroup', S.not_dvd_index, hS (mem_zpowers _), hSc.1, ?_⟩
  intro D hDS hD2 hDbot
  obtain ⟨d, hdD, hd1, b, hb, hlt⟩ := hSc.2 D hDS hD2 hDbot
  exact ⟨d, hdD, hd1, b, fun g hg hgd => by rw [hfix g hg, hgd]; exact hb, hlt⟩

end CFSG.EvenSporadicStandard.M24Std
