module

public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.E6SignedGraphCollection
public import CFSG.LieType.Chevalley.E6SignedGraphStabilizer

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable (K : Type) [Field K]

@[expose] def inversionFixed
    (w : WeylGroup TwistTag.E6.tag) : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootSpan TwistTag.E6.tag K (inversionSet w) ⊓ fixedGroup K

variable {K}

theorem conjP_eq_twistHom (g : ModGL TwistTag.E6.tag K) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ =
      twistHom TwistTag.E6 K (RingHom.id K) g :=
  congrArg (fun φ : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag K => φ g)
    (conj_diagramMap_eq_twistHom TwistTag.E6 K)

theorem surjective_ringHom_id : Function.Surjective (RingHom.id K) := fun x => ⟨x, rfl⟩

theorem signTuple_mem_borelGroup :
    rootDiagUnit TwistTag.E6.tag (signTuple K) ∈ borelGroup TwistTag.E6.tag K :=
  torusGroup_le_borelGroup rootDiagUnit_signTuple_mem_torusGroup

theorem twistA_conj_mem_borelGroup
    {b : ModGL TwistTag.E6.tag K}
    (hb : b ∈ borelGroup TwistTag.E6.tag K) :
    twistA K * b * (twistA K)⁻¹ ∈ borelGroup TwistTag.E6.tag K := by
  rw [twistA_conj, conjP_eq_twistHom]
  exact mul_mem (mul_mem signTuple_mem_borelGroup
    (twistHom_mem_borelGroup surjective_ringHom_id hb)) (inv_mem signTuple_mem_borelGroup)

theorem twistA_conj_mem_torusGroup
    {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ torusGroup TwistTag.E6.tag K) :
    twistA K * h * (twistA K)⁻¹ ∈ torusGroup TwistTag.E6.tag K := by
  rw [twistA_conj, conjP_eq_twistHom]
  exact mul_mem (mul_mem rootDiagUnit_signTuple_mem_torusGroup
    (twistHom_mem_torusGroup' surjective_ringHom_id hh))
    (inv_mem rootDiagUnit_signTuple_mem_torusGroup)

theorem twistA_conj_mem_posUnipotent
    {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ posUnipotent TwistTag.E6.tag K) :
    twistA K * u * (twistA K)⁻¹ ∈ posUnipotent TwistTag.E6.tag K := by
  rw [twistA_conj, conjP_eq_twistHom]
  exact (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent
    rootDiagUnit_signTuple_mem_torusGroup) _).1
    (twistHom_mem_posUnipotent surjective_ringHom_id hu)

theorem twistA_conj_mem_rootSpan_inversionSet
    {w : WeylGroup TwistTag.E6.tag}
    (hw : weylTwist TwistTag.E6 w = w) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (inversionSet w)) :
    twistA K * u * (twistA K)⁻¹ ∈ rootSpan TwistTag.E6.tag K (inversionSet w) := by
  rw [twistA_conj, conjP_eq_twistHom]
  exact (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
    (fun α hα => (inversionSet_pos (w := w) hα).1) rootDiagUnit_signTuple_mem_torusGroup) _).1
    (twistHom_mem_rootSpan_inversionSet surjective_ringHom_id hw hu)

theorem twistA_conj_mem_bruhatCell
    {w : WeylGroup TwistTag.E6.tag} {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ bruhatCell TwistTag.E6.tag K w) :
    twistA K * x * (twistA K)⁻¹ ∈ bruhatCell TwistTag.E6.tag K (weylTwist TwistTag.E6 w) := by
  rw [twistA_conj, conjP_eq_twistHom]
  obtain ⟨b, hb, b', hb', e⟩ :=
    mem_bruhatCell.1 (twistHom_mem_bruhatCell surjective_ringHom_id hx)
  rw [← e]
  refine mem_bruhatCell.2 ⟨rootDiagUnit TwistTag.E6.tag (signTuple K) * b,
    mul_mem signTuple_mem_borelGroup hb, b' * (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹,
    mul_mem hb' (inv_mem signTuple_mem_borelGroup), ?_⟩
  group

theorem weylTwist_eq_of_mem_fixedGroup
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ fixedGroup K)
    {w : WeylGroup TwistTag.E6.tag} (hgw : g ∈ bruhatCell TwistTag.E6.tag K w) :
    weylTwist TwistTag.E6 w = w := by
  have h := twistA_conj_mem_bruhatCell hgw
  rw [conj_twistA_eq_of_mem hg] at h
  exact bruhatCell_injective (bruhatCell_eq_of_mem h hgw)

theorem twistA_conj_rootDiagUnit
    (l : Fin TwistTag.E6.tag.rank → Kˣ) :
    twistA K * rootDiagUnit TwistTag.E6.tag l * (twistA K)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => l (TwistTag.E6.perm.symm i)) := by
  rw [twistA_conj, diagramMap_mul_rootDiagUnit, mul_inv_cancel_right, rootDiagUnit_inv,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm (signTuple K), mul_inv_cancel_right]

theorem rootChar_inv_mul_eq_of_conj
    {w : WeylGroup TwistTag.E6.tag}
    {m : Fin TwistTag.E6.tag.rank → Kˣ}
    (h : rootDiagUnit TwistTag.E6.tag (signTuple K) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ =
      rootDiagUnit TwistTag.E6.tag m * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)
    (j : Fin TwistTag.E6.tag.rank) :
    (rootChar (signTuple K) (w⁻¹ • (Pi.single j 1 : E6Vec)))⁻¹ * signTuple K j = m j := by
  set α : E6Vec := w⁻¹ • (Pi.single j 1 : E6Vec) with hαdef
  have hα : IsRoot TwistTag.E6.tag α := IsRoot.smul (isRoot_single _ j) w⁻¹
  have hwα : w • α = Pi.single j 1 := smul_inv_smul w _
  obtain ⟨c, hc⟩ := mapsRootLines_canonicalRep (R := K) w α hα
  have h1 := conj_canonicalRep_rootVec (signTuple K) w hα hc
  rw [h, Units.val_mul, Module.End.mul_apply, hc, map_smul] at h1
  change (c : K) • rootDiag m (rootVec TwistTag.E6.tag K (w • α)) = _ at h1
  rw [hwα] at h1
  rw [rootDiag_rootVec m (isRoot_single _ j), smul_smul, smul_smul] at h1
  have h2 := eq_of_smul_rootVec_eq_smul (isRoot_single _ j) h1
  have hm : rootChar m (Pi.single j 1 : E6Vec) = m j := by
    simpa using rootChar_nsmul_single m j 1
  have hb : rootChar (signTuple K) (Pi.single j 1 : E6Vec) = signTuple K j := by
    simpa using rootChar_nsmul_single (signTuple K) j 1
  rw [hm, hb] at h2
  apply Units.ext
  rw [mul_comm] at h2
  exact (mul_right_cancel₀ c.ne_zero h2).symm

theorem neg_one_zpow_eq_one_iff (hK : ringChar K ≠ 2) (n : ℤ) :
    (-1 : Kˣ) ^ n = 1 ↔ Even n := by
  rcases Int.even_or_odd n with he | ho
  · exact iff_of_true he.neg_one_zpow he
  · refine iff_of_false ?_ (Int.not_even_iff_odd.2 ho)
    rw [ho.neg_one_zpow]
    intro h1
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h1)

theorem mem_weylGroup_of_mem_fixedGroup
    (hK : ringChar K ≠ 2) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ fixedGroup K) {w : WeylGroup TwistTag.E6.tag}
    (hgw : g ∈ bruhatCell TwistTag.E6.tag K w) : w ∈ weylGroup := by
  have hδ := weylTwist_eq_of_mem_fixedGroup hg hgw
  have hw : w ∈ relWeylTwist TwistTag.E6 := (mem_relWeylTwist TwistTag.E6).2 hδ
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w with hn
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := K) w).2.2 hgw
  simp only at hb hu hg
  obtain ⟨t, ht, hdt⟩ := exists_conj_canonicalRep (K := K) (signTuple K) w
  have hAn : twistA K * n * (twistA K)⁻¹ = t * n := by
    rw [twistA_conj, conjP_canonicalRep hw, hdt]
  have hfix := conj_twistA_eq_of_mem hg
  have e : twistA K * (b * n * u) * (twistA K)⁻¹ =
      (twistA K * b * (twistA K)⁻¹ * t) * n * (twistA K * u * (twistA K)⁻¹) := by
    calc twistA K * (b * n * u) * (twistA K)⁻¹ =
        (twistA K * b * (twistA K)⁻¹) * (twistA K * n * (twistA K)⁻¹) *
          (twistA K * u * (twistA K)⁻¹) := by group
      _ = _ := by rw [hAn]; group
  rw [e] at hfix
  have hinj := (bijOn_bruhatCell (K := K) w).2.1
    (Set.mk_mem_prod (mul_mem (twistA_conj_mem_borelGroup hb) (torusGroup_le_borelGroup ht))
      (twistA_conj_mem_rootSpan_inversionSet hδ hu)) (Set.mk_mem_prod hb hu) hfix
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨-, -, -, -, hHU, -, huniq, -⟩ := triangular_borel_structure.{0, 0} TwistTag.E6.tag K
  have hb' : b ∈ (torusGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) *
      (posUnipotent TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← hHU]
    exact hb
  obtain ⟨h, hh, u', hu', rfl⟩ := hb'
  have hnorm : t⁻¹ * (twistA K * u' * (twistA K)⁻¹) * t ∈ posUnipotent TwistTag.E6.tag K := by
    have h' := (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent
      (inv_mem ht)) _).1 (twistA_conj_mem_posUnipotent hu')
    rwa [inv_inv] at h'
  have e2 : twistA K * (h * u') * (twistA K)⁻¹ * t =
      (twistA K * h * (twistA K)⁻¹ * t) * (t⁻¹ * (twistA K * u' * (twistA K)⁻¹) * t) := by
    group
  rw [e2] at hinj
  have hAh := (huniq _ (mul_mem (twistA_conj_mem_torusGroup hh) ht) _ hh _ hnorm _ hu'
    hinj.1).1
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [twistA_conj_rootDiagUnit] at hAh
  have ht' : t = rootDiagUnit TwistTag.E6.tag
      (fun i => (l (TwistTag.E6.perm.symm i))⁻¹ * l i) := by
    rw [eq_inv_mul_of_mul_eq hAh, rootDiagUnit_inv, ← rootDiagUnit_mul]
    rfl
  rw [ht'] at hdt
  have h2 := rootChar_inv_mul_eq_of_conj hdt ⟨1, by decide⟩
  have h4 := rootChar_inv_mul_eq_of_conj hdt ⟨3, by decide⟩
  simp only [show TwistTag.E6.perm.symm ⟨1, by decide⟩ = ⟨1, by decide⟩ by decide,
    show TwistTag.E6.perm.symm ⟨3, by decide⟩ = ⟨3, by decide⟩ by decide, inv_mul_cancel,
    inv_mul_eq_one] at h2 h4
  rw [rootChar_signTuple, signTuple_apply_one] at h2
  rw [rootChar_signTuple, signTuple_of_ne (by decide)] at h4
  have hodd : Odd ((w⁻¹ • (Pi.single ⟨1, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) := by
    rcases Int.even_or_odd ((w⁻¹ • (Pi.single ⟨1, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) with
      he | ho
    · rw [he.neg_one_zpow] at h2
      exact absurd (by simpa using congrArg Units.val h2.symm)
        (Ring.neg_one_ne_one_of_char_ne_two hK)
    · exact ho
  have heven : Even ((w⁻¹ • (Pi.single ⟨3, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) :=
    (neg_one_zpow_eq_one_iff hK _).1 h4
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := E6_signed_graph_root_system_and_Weyl_stabilizer
  have hmem : w ∈ (weylGroup : Set (WeylGroup TwistTag.E6.tag)) := by
    rw [h8]
    exact ⟨hw, hodd, heven⟩
  exact hmem

theorem fixed_cell_bijOn
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    {d : ModGL TwistTag.E6.tag K} (hdΓ : d ∈ fixedGroup K)
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) (hdw : MapsRootLines d w) :
    Set.BijOn (fun p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K ×
        ModGL TwistTag.E6.tag K => p.1 * p.2.1 * d * p.2.2)
      ((posFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
        (torusFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (inversionFixed K w : Set (ModGL TwistTag.E6.tag K)))
      ((fixedGroup K : Set (ModGL TwistTag.E6.tag K)) ∩ bruhatCell TwistTag.E6.tag K w) := by
  have hδ : weylTwist TwistTag.E6 w = w := (mem_relWeylTwist TwistTag.E6).1 hw
  obtain ⟨w', k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hdN
  have hw' : w' = w := (mapsRootLines_mul_canonicalRep hk w').unique hdw
  subst hw'
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w' with hn
  obtain ⟨-, -, -, -, -, hUH, -, huniq', -⟩ := triangular_borel_structure.{0, 0} TwistTag.E6.tag K
  have hIB : rootSpan TwistTag.E6.tag K (inversionSet w') ≤ borelGroup TwistTag.E6.tag K :=
    (rootSpan_le_posUnipotent fun α h => inversionSet_pos (w := w') h).trans le_sup_right
  have hHadj : ∀ {x : ModGL TwistTag.E6.tag K}, x ∈ torusGroup TwistTag.E6.tag K →
      x ∈ adjointGroup TwistTag.E6.tag K := fun hx =>
    borelGroup_le_adjointGroup (t := TwistTag.E6) (torusGroup_le_borelGroup hx)
  refine ⟨fun p hp => ⟨?_, ?_⟩, fun p hp q hq hpq => ?_, fun g hg => ?_⟩
  · obtain ⟨hu, hh, hv⟩ := hp
    exact mul_mem (mul_mem (mul_mem (Subgroup.mem_inf.1 hu).2 (Subgroup.mem_inf.1 hh).2) hdΓ)
      (Subgroup.mem_inf.1 hv).2
  · obtain ⟨hu, hh, hv⟩ := hp
    refine mem_bruhatCell.2 ⟨p.1 * p.2.1 * k, mul_mem (mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hu).1)
      (torusGroup_le_borelGroup (Subgroup.mem_inf.1 hh).1)) (torusGroup_le_borelGroup hk), p.2.2,
      hIB (Subgroup.mem_inf.1 hv).1, ?_⟩
    simp only [mul_assoc, hn]
  · obtain ⟨hu, hh, hv⟩ := hp
    obtain ⟨hu', hh', hv'⟩ := hq
    have e : (p.1 * p.2.1 * k) * n * p.2.2 = (q.1 * q.2.1 * k) * n * q.2.2 := by
      simp only [mul_assoc] at hpq ⊢
      exact hpq
    have h1 := (bijOn_bruhatCell (K := K) w').2.1
      (Set.mk_mem_prod (mul_mem (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hu).1)
        (torusGroup_le_borelGroup (Subgroup.mem_inf.1 hh).1)) (torusGroup_le_borelGroup hk))
        (Subgroup.mem_inf.1 hv).1)
      (Set.mk_mem_prod (mul_mem (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hu').1)
        (torusGroup_le_borelGroup (Subgroup.mem_inf.1 hh').1)) (torusGroup_le_borelGroup hk))
        (Subgroup.mem_inf.1 hv').1) e
    simp only [Prod.mk.injEq] at h1
    have h2 := huniq' _ (Subgroup.mem_inf.1 hh).1 _ (Subgroup.mem_inf.1 hh').1 _
      (Subgroup.mem_inf.1 hu).1 _ (Subgroup.mem_inf.1 hu').1 (mul_right_cancel h1.1)
    exact Prod.ext h2.1 (Prod.ext h2.2 h1.2)
  · obtain ⟨hgΓ, hgw⟩ := hg
    obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, rfl⟩ := (bijOn_bruhatCell (K := K) w').2.2 hgw
    simp only at hb hv hgΓ
    have hfix := conj_twistA_eq_of_mem hgΓ
    have hdfix := conj_twistA_eq_of_mem hdΓ
    have e : twistA K * (b * n * v) * (twistA K)⁻¹ =
        (twistA K * (b * k⁻¹) * (twistA K)⁻¹ * k) * n * (twistA K * v * (twistA K)⁻¹) := by
      calc twistA K * (b * n * v) * (twistA K)⁻¹ =
          (twistA K * (b * k⁻¹) * (twistA K)⁻¹) * (twistA K * (k * n) * (twistA K)⁻¹) *
            (twistA K * v * (twistA K)⁻¹) := by group
        _ = _ := by rw [hdfix]; group
    rw [e] at hfix
    have hbk : b * k⁻¹ ∈ borelGroup TwistTag.E6.tag K :=
      mul_mem hb (inv_mem (torusGroup_le_borelGroup hk))
    have h1 := (bijOn_bruhatCell (K := K) w').2.1
      (Set.mk_mem_prod (mul_mem (twistA_conj_mem_borelGroup hbk) (torusGroup_le_borelGroup hk))
        (twistA_conj_mem_rootSpan_inversionSet hδ hv)) (Set.mk_mem_prod hb hv) hfix
    simp only [Prod.mk.injEq] at h1
    have hb'fix : twistA K * (b * k⁻¹) * (twistA K)⁻¹ = b * k⁻¹ := eq_mul_inv_of_mul_eq h1.1
    have hb'' : b * k⁻¹ ∈ (posUnipotent TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) *
        (torusGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) := by
      rw [← hUH]
      exact hbk
    obtain ⟨u, hu, h, hh, huh⟩ := hb''
    have e3 : (twistA K * u * (twistA K)⁻¹) * (twistA K * h * (twistA K)⁻¹) = u * h := by
      calc (twistA K * u * (twistA K)⁻¹) * (twistA K * h * (twistA K)⁻¹) =
          twistA K * (u * h) * (twistA K)⁻¹ := by group
        _ = u * h := by
          simp only at huh
          rw [huh]
          exact hb'fix
    obtain ⟨hAu, hAh⟩ := huniq' _ (twistA_conj_mem_torusGroup hh) _ hh _
      (twistA_conj_mem_posUnipotent hu) _ hu e3
    refine ⟨(u, h, v), ⟨Subgroup.mem_inf.2 ⟨hu, mem_fixedGroup.2
        ⟨rootSpan_le_adjointGroup K _ hu, (mul_inv_eq_iff_eq_mul.1 hAu).symm⟩⟩,
      Subgroup.mem_inf.2 ⟨hh, mem_fixedGroup.2 ⟨hHadj hh, (mul_inv_eq_iff_eq_mul.1 hAh).symm⟩⟩,
      Subgroup.mem_inf.2 ⟨hv, mem_fixedGroup.2 ⟨rootSpan_le_adjointGroup K _ hv,
        (mul_inv_eq_iff_eq_mul.1 h1.2).symm⟩⟩⟩, ?_⟩
    simp only at huh ⊢
    calc u * h * (k * n) * v = u * h * k * n * v := by group
      _ = b * n * v := by rw [huh]; group

end CFSG.LieType.Chevalley.E6SignedGraph
