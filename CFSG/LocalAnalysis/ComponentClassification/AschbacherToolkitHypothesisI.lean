module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitDihedralExtension
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open

@[expose] def HypothesisI (L : Type*) [Group L] [Finite L] : Prop :=
  ∀ α : MulAut L, orderOf α = 2 →
    twoRank L = 1 ∨ ∃ x : L, α x = x ∧ x ∉ Subgroup.center L ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1

variable {L : Type} [Group L] [Finite L]

theorem exists_orderOf_eq_two_of_isPGroup {H : Subgroup L} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    ∃ s ∈ H, orderOf s = 2 := by
  obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hH ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 2 ∣ orderOf p := by
    have h1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hp1'
    · rw [hj]
      exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  exact ⟨p ^ (orderOf p / 2), H.pow_mem hp _, orderOf_pow_orderOf_div (orderOf_pos p).ne' hdvd⟩

theorem center_inf_isCyclic (P : Subgroup L) (hP : IsPGroup 2 P)
    (hZ : pRank 2 (Subgroup.center L) ≤ 1) :
    IsCyclic (Subgroup.center L ⊓ P : Subgroup L) := by
  set Z := Subgroup.center L ⊓ P with hZdef
  have hZ2 : IsPGroup 2 Z := hP.to_le inf_le_right
  have hrank : twoRank Z ≤ 1 := by
    apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have h := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) (H := Subgroup.center L)
      (E := E.map Z.subtype) ((Subgroup.map_subtype_le E).trans inf_le_left)
      (CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map E hE Z.subtype)
      (by rw [Subgroup.card_map_of_injective Z.subtype_injective, hcard])
    omega
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.2.1 b).symm }
  exact CFSG.TwoRankLowerBound.Helpers.abelian_rank_one_two_group_isCyclic Z hZ2 hrank

theorem lemma_2_9 (L : Type) [Group L] [Finite L] (hL : IsQuasisimple L)
    (hZ : pRank 2 (Subgroup.center L) ≤ 1) : HypothesisI L := by
  intro α hα
  by_cases hex : ∃ x : L, α x = x ∧ x ∉ Subgroup.center L ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1
  · exact Or.inr hex
  left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := ⟨hL.1⟩
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨P, hPα⟩ := exists_invariant_sylow_two α hα2
  set Z : Subgroup L := Subgroup.center L ⊓ (P : Subgroup L) with hZdef
  have hZc : Z ≤ Subgroup.center L := inf_le_left
  have hZP : Z ≤ (P : Subgroup L) := inf_le_right
  have : Z.Normal := Subgroup.normal_of_le_center hZc
  have hcenα : (Subgroup.center L).map (α : L →* L) = Subgroup.center L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  have hZα : Z.map (α : L →* L) = Z := by
    rw [hZdef, Subgroup.map_inf_eq _ _ _ α.injective, hcenα, hPα]
  have hZcyc : IsCyclic Z := center_inf_isCyclic P P.isPGroup' hZ
  have hfix : ∀ p ∈ (P : Subgroup L), α p = p → p ∈ Z := by
    intro p hp hαp
    refine ⟨?_, hp⟩
    by_contra hpc
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    exact hex ⟨p, hαp, hpc, k, congrArg Subtype.val hk⟩
  set π := QuotientGroup.mk' Z with hπ
  set Pb : Subgroup (L ⧸ Z) := (P : Subgroup L).map π with hPb
  have hPbα := map_mk_congr_eq α Z hZα P hPα
  have hβ₁2 := restrictAut_sq (QuotientGroup.congr Z Z α hZα) (quotient_congr_sq α hα2 Z hZα)
    Pb hPbα
  have hβ₁fix := card_fixedSubgroup_quotient_le_two α hα2 Z P hZc hZP hZα hZcyc hfix hPbα
  have hPb2 : IsPGroup 2 Pb := P.isPGroup'.map π
  let Sb : Sylow 2 (L ⧸ Z) := P.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hcomap : Pb.comap π = P := by
    rw [hPb, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZP]
  have hZstar : ∀ t ∈ (P : Subgroup L), orderOf (π t) = 2 →
      (∀ g : L ⧸ Z, g⁻¹ * π t * g ∈ Pb → g⁻¹ * π t * g = π t) → False := by
    intro t htP hto hiso
    have htPb : π t ∈ Pb := ⟨t, htP, rfl⟩
    have htSb : π t ∈ (Sb : Subgroup (L ⧸ Z)) := htPb
    have hcent : (⟨π t, htSb⟩ : (Sb : Subgroup (L ⧸ Z))) ∈
        Subgroup.center (Sb : Subgroup (L ⧸ Z)) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨q, hq⟩
      apply Subtype.ext
      have hq' : q ∈ Pb := hq
      have hmem : q⁻¹⁻¹ * π t * q⁻¹ ∈ Pb := by
        rw [inv_inv]
        exact Pb.mul_mem (Pb.mul_mem hq' htPb) (Pb.inv_mem hq')
      have h := hiso q⁻¹ hmem
      rw [inv_inv] at h
      change q * π t = π t * q
      calc q * π t = (q * π t * q⁻¹) * q := by group
        _ = π t * q := by rw [h]
    obtain ⟨-, hcen⟩ := CFSG.Milestones.glauberman_zStar_central_sylow_involution Sb
      ⟨π t, htSb⟩ hcent (by rw [Subgroup.orderOf_mk]; exact hto) (fun g hg => hiso g hg)
    have htZ := mem_center_of_isolated_image hL Z t hto hcen
    have h1 : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ⟨htZ, htP⟩
    rw [h1, orderOf_one] at hto
    omega
  have hnotA : ¬ AtMostOneInvolution Pb := by
    intro hA
    by_cases hbot : Pb = ⊥
    · apply sylow_not_le_center hL P
      intro p hp
      have hp' : π p ∈ Pb := ⟨p, hp, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hp'
      exact hZc ((QuotientGroup.eq_one_iff p).mp hp')
    · obtain ⟨s, hs, hso⟩ := exists_orderOf_eq_two_of_isPGroup hPb2 hbot
      obtain ⟨t, htP, rfl⟩ := hs
      have htP' : t ∈ (P : Subgroup L) := htP
      have htPb : π t ∈ Pb := ⟨t, htP', rfl⟩
      apply hZstar t htP' hso
      intro g hg
      have hgo : orderOf (g⁻¹ * π t * g) = 2 := by
        rw [show g⁻¹ * π t * g = MulAut.conj g⁻¹ (π t) by simp, MulEquiv.orderOf_eq]
        exact hso
      have h := hA ⟨g⁻¹ * π t * g, hg⟩ ⟨π t, htPb⟩
        (by rw [Subgroup.orderOf_mk]; exact hgo) (by rw [Subgroup.orderOf_mk]; exact hso)
      exact congrArg Subtype.val h
  have hB : HasDihedralGenerators Pb :=
    (involutory_automorphism_shape hPb2 _ hβ₁2 hβ₁fix).resolve_left hnotA
  let f : (P : Subgroup L) →* Pb := π.subgroupMap (P : Subgroup L)
  have hf : Function.Surjective f := π.subgroupMap_surjective _
  have hfker : f.ker = Z.subgroupOf (P : Subgroup L) := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : π p = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (p : L)).mp h'
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (p : L)).mpr h
  have hfkerc : f.ker ≤ Subgroup.center (P : Subgroup L) := by
    rw [hfker]
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hp) q)
  have hext := dihedral_central_extension_card_le f hf hfkerc hB
  have h8 := central_sylow_commutator P hZc (P.isPGroup'.to_le hZP)
  rw [show commutator L = ⊤ from hL.1, inf_top_eq] at h8
  have hZD : f.ker ≤ commutator (P : Subgroup L) := by
    rw [hfker]
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    have hpZ : (p : L) ∈ Z ⊓ (commutator (P : Subgroup L)).map (P : Subgroup L).subtype :=
      h8 ▸ hp
    obtain ⟨-, q, hq, hqp⟩ := hpZ
    rwa [← Subtype.ext hqp]
  have hZcard : Nat.card Z ≤ 2 := by
    rw [inf_of_le_left hZD, hfker] at hext
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv] at hext
  have hβ₂2 := restrictAut_sq α hα2 _ hPα
  have hβ₂fix : Nat.card (fixedSubgroup (restrictAut α (P : Subgroup L) hPα)) ≤ 2 := by
    have hle : (fixedSubgroup (restrictAut α (P : Subgroup L) hPα)).map
        (P : Subgroup L).subtype ≤ Z := by
      rintro _ ⟨p, hp, rfl⟩
      exact hfix p p.2 (congrArg Subtype.val ((mem_fixedSubgroup).mp hp))
    calc Nat.card (fixedSubgroup (restrictAut α (P : Subgroup L) hPα))
        = Nat.card ((fixedSubgroup (restrictAut α (P : Subgroup L) hPα)).map
            (P : Subgroup L).subtype) :=
          (Subgroup.card_map_of_injective (P : Subgroup L).subtype_injective).symm
      _ ≤ Nat.card Z := Subgroup.card_le_of_le hle
      _ ≤ 2 := hZcard
  have hPne : (P : Subgroup L) ≠ ⊥ := fun hbot =>
    sylow_not_le_center hL P (hbot ▸ bot_le)
  rcases involutory_automorphism_shape P.isPGroup' _ hβ₂2 hβ₂fix with hPA | hPB
  · exact twoRank_eq_one_of_sylow P hPA hPne
  exfalso
  obtain ⟨x, y, hgen, hy2, hyx, hy⟩ := hPB
  have hcardPb : 4 ≤ Nat.card Pb := by
    rw [AtMostOneInvolution] at hnotA
    push Not at hnotA
    obtain ⟨s, t, hs, ht, hst⟩ := hnotA
    have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; omega
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
    have h3 : 3 ≤ Nat.card Pb := by
      have hsub : ({1, s, t} : Set Pb) ⊆ Set.univ := Set.subset_univ _
      have hncard : Set.ncard ({1, s, t} : Set Pb) = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hst]
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hs1.symm, ht1.symm⟩
      calc 3 = Set.ncard ({1, s, t} : Set Pb) := hncard.symm
        _ ≤ Set.ncard (Set.univ : Set Pb) := Set.ncard_le_ncard hsub
        _ = Nat.card Pb := Set.ncard_univ _
    obtain ⟨n, hn⟩ := hPb2.exists_card_eq
    rw [hn] at h3 ⊢
    by_contra hlt
    have : n ≤ 1 := by
      by_contra hn1
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hZne : Z ≠ ⊥ := by
    have : Nontrivial (P : Subgroup L) := by
      obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
      exact ⟨⟨⟨p, hp⟩, 1, hp1⟩⟩
    obtain ⟨p, hp1, hpfix⟩ := exists_fixed_ne_one P.isPGroup' _ hβ₂2
    intro hbot
    have hpZ : (p : L) ∈ Z := hfix p p.2 (by
      have := congrArg Subtype.val hpfix
      rwa [restrictAut_apply] at this)
    rw [hbot, Subgroup.mem_bot] at hpZ
    exact hp1 (Subtype.ext hpZ)
  have hZ2 : Nat.card Z = 2 := by
    have h1 : Nat.card Z ≠ 1 := fun h => hZne (Subgroup.card_eq_one.mp h)
    have h0 : 0 < Nat.card Z := Nat.card_pos
    omega
  have hcardP : Nat.card (P : Subgroup L) = 2 * Nat.card Pb := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, hfker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ2] at h
    exact h.symm
  have hP8 : 8 ≤ Nat.card (P : Subgroup L) := by omega
  obtain ⟨z, hzZ, hzo⟩ := exists_orderOf_eq_two_of_isPGroup (P.isPGroup'.to_le hZP) hZne
  have hZz : ∀ w ∈ Z, w = 1 ∨ w = z := by
    intro w hw
    have hzpow : Subgroup.zpowers z = Z := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
      rw [hZ2, Nat.card_zpowers, hzo]
    rw [← hzpow] at hw
    exact CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hzo hw
  have hzP : z ∈ (P : Subgroup L) := hZP hzZ
  have hzc : (⟨z, hzP⟩ : (P : Subgroup L)) ∈ Subgroup.center (P : Subgroup L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hzZ) q)
  obtain ⟨u, hu2, huniq⟩ := dihedral_central_involution_sqrt P.isPGroup' x y hgen hy2 hyx hy
    hP8 ⟨z, hzP⟩ hzc (by rw [Subgroup.orderOf_mk]; exact hzo)
  have hu2' : (u : L) ^ 2 = z := congrArg Subtype.val hu2
  have hπu2 : π u ^ 2 = 1 := by
    rw [← map_pow, hu2']
    exact (QuotientGroup.eq_one_iff z).mpr hzZ
  have huZ : (u : L) ∉ Z := by
    intro huZ
    rcases hZz _ huZ with h | h
    · rw [h, one_pow] at hu2'
      rw [← hu2', orderOf_one] at hzo
      omega
    · rw [h, ← hzo, pow_orderOf_eq_one] at hu2'
      rw [← hu2', orderOf_one] at hzo
      omega
  have hπu1 : π u ≠ 1 := fun h => huZ ((QuotientGroup.eq_one_iff (u : L)).mp h)
  have hπuo : orderOf (π u) = 2 := orderOf_eq_prime hπu2 hπu1
  apply hZstar u u.2 hπuo
  intro g hg
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective Z g
  have hmem : g'⁻¹ * u * g' ∈ (P : Subgroup L) := by
    have h1 : π (g'⁻¹ * u * g') ∈ Pb := by simpa only [map_mul, map_inv] using hg
    have h2 : g'⁻¹ * u * g' ∈ Pb.comap π := h1
    rwa [hcomap] at h2
  have hsq : (⟨g'⁻¹ * u * g', hmem⟩ : (P : Subgroup L)) ^ 2 = ⟨z, hzP⟩ := by
    apply Subtype.ext
    change (g'⁻¹ * u * g') ^ 2 = z
    calc (g'⁻¹ * u * g') ^ 2 = g'⁻¹ * (u : L) ^ 2 * g' := by rw [sq, sq]; group
      _ = g'⁻¹ * z * g' := by rw [hu2']
      _ = z := by rw [Subgroup.mem_center_iff.mp (hZc hzZ) g'⁻¹]; group
  have himage : π (g'⁻¹ * u * g') = π u := by
    rcases huniq _ hsq with h | h
    · rw [show g'⁻¹ * (u : L) * g' = u from congrArg Subtype.val h]
    · rw [show g'⁻¹ * (u : L) * g' = (u : L)⁻¹ from congrArg Subtype.val h, map_inv]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hπu2)
  simpa only [map_mul, map_inv] using himage

end CFSG.ComponentClassification.AschbacherToolkit
