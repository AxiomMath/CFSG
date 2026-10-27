module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open Matrix

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem subgroupOf_map_subtype_eq'' {M : Subgroup X} (L : Subgroup M) :
    (L.map M.subtype).subgroupOf M = L := by
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]

omit [Finite X] in
theorem mem_normalizer_centralizer {B : Subgroup X} {s : X}
    (hs : s ∈ normalizer (B : Set X)) : s ∈ normalizer (centralizer (B : Set X) : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [mem_centralizer_iff] at hh ⊢
    intro b hb
    have hb' : s⁻¹ * b * s⁻¹⁻¹ ∈ B := (mem_normalizer_iff.mp (inv_mem hs) b).mp hb
    have h1 := hh _ hb'
    calc b * (s * h * s⁻¹) = s * ((s⁻¹ * b * s⁻¹⁻¹) * h) * s⁻¹ := by group
      _ = s * (h * (s⁻¹ * b * s⁻¹⁻¹)) * s⁻¹ := by rw [h1]
      _ = s * h * s⁻¹ * b := by group
  · intro hh
    rw [mem_centralizer_iff] at hh ⊢
    intro b hb
    have hb' : s * b * s⁻¹ ∈ B := (mem_normalizer_iff.mp hs b).mp hb
    have h1 := hh _ hb'
    calc b * h = s⁻¹ * ((s * b * s⁻¹) * (s * h * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * h * s⁻¹) * (s * b * s⁻¹)) * s := by rw [h1]
      _ = h * b := by group

theorem exists_fourCube_model {S T N : Subgroup X} (hS : ∃ P : Sylow 2 X, (P : Subgroup X) = S)
    (hN : N = normalizer (T : Set X)) (hTS : T ≤ S) (hSN : S ≤ N)
    (eT : ↥T ≃* Multiplicative (Fin 3 → ZMod 4)) (hCT : centralizer (T : Set X) ≤ T ⊔ oddIn N)
    (f : ↥N →* GL (Fin 3) (ZMod 2)) (hfs : Function.Surjective f)
    (hfk : f.ker = (T ⊔ oddIn N).subgroupOf N) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (T' : Subgroup L),
      Nonempty (↥T' ≃* Multiplicative (Fin 3 → ZMod 4)) ∧ centralizer (T' : Set L) = T' ∧
      (∃ ψ : L →* GL (Fin 3) (ZMod 2), Function.Surjective ψ ∧ ψ.ker = T') ∧
      ∃ Q : Sylow 2 L, Nonempty (↥S ≃* ↥(Q : Subgroup L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup ↥N := pPrimeCore 2 ↥N with hOdef
  set π : ↥N →* ↥N ⧸ O := QuotientGroup.mk' O with hπ
  have hTN : T ≤ N := hN ▸ le_normalizer
  set T₀ : Subgroup ↥N := T.subgroupOf N with hT₀
  set S₀ : Subgroup ↥N := S.subgroupOf N with hS₀
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨P, hPS⟩ := hS
  have hS2 : IsPGroup 2 S := by
    rw [← hPS]
    exact P.isPGroup'
  have hS₀2 : IsPGroup 2 S₀ := hS2.of_equiv (subgroupOfEquivOfLe hSN).symm
  have hT₀S₀ : T₀ ≤ S₀ := subgroupOf_mono _ hTS
  have hT₀2 : IsPGroup 2 T₀ := hS₀2.to_le hT₀S₀
  have hS₀O : Disjoint S₀ O := by
    rw [disjoint_iff]
    exact eq_bot_of_le_two_group_of_le_odd hS₀2 hOodd inf_le_left inf_le_right
  have hT₀O : Disjoint T₀ O := hS₀O.mono_left hT₀S₀
  have hkerπ : π.ker = O := QuotientGroup.ker_mk' O
  have hinjS : Function.Injective (π.domRestrict S₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, hkerπ, subgroupOf_eq_bot]
    exact hS₀O.symm
  have hinjT : Function.Injective (π.domRestrict T₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, hkerπ, subgroupOf_eq_bot]
    exact hT₀O.symm
  have hOπ : O.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨o, ho, rfl⟩
    exact (QuotientGroup.eq_one_iff o).mpr ho
  set T' : Subgroup (↥N ⧸ O) := T₀.map π with hT'
  have eT' : ↥T' ≃* Multiplicative (Fin 3 → ZMod 4) :=
    ((MonoidHom.ofInjective hinjT).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range T₀ π))).symm.trans
      ((subgroupOfEquivOfLe hTN).trans eT)
  have hsupT : (T ⊔ oddIn N).subgroupOf N = T₀ ⊔ O := by
    unfold oddIn
    rw [subgroupOf_sup hTN (map_subtype_le _), subgroupOf_map_subtype_eq'']
  have hOker : O ≤ f.ker := by
    rw [hfk, hsupT]
    exact le_sup_right
  set ψ : ↥N ⧸ O →* GL (Fin 3) (ZMod 2) := QuotientGroup.lift O f hOker with hψ
  have hψs : Function.Surjective ψ := by
    intro g
    obtain ⟨n, rfl⟩ := hfs g
    exact ⟨π n, QuotientGroup.lift_mk' O hOker n⟩
  have hsupπ : (T₀ ⊔ O).map π = T' := by
    rw [Subgroup.map_sup, hOπ, sup_bot_eq]
  have hψk : ψ.ker = T' := by
    rw [hψ, QuotientGroup.ker_lift, hfk, hsupT]
    exact hsupπ
  have hTab : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := by
    intro u hu v hv
    have h1 : eT (⟨u, hu⟩ * ⟨v, hv⟩) = eT (⟨v, hv⟩ * ⟨u, hu⟩) := by
      rw [map_mul, map_mul, mul_comm]
    have h2 := congrArg Subtype.val (eT.injective h1)
    simpa using h2
  have hT'comm : ∀ u ∈ T', ∀ v ∈ T', u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hTab _ hu _ hv))
  have hT₀n : (T₀ ⊔ O).Normal := by
    have : T₀.Normal := by
      constructor
      intro t ht n
      have hnN : (n : X) ∈ normalizer (T : Set X) := hN ▸ n.2
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnN t).mp (mem_subgroupOf.mp ht))
    infer_instance
  have hT₀syl : IsSylowTwoIn T₀ (T₀ ⊔ O) := by
    refine isSylowTwoIn_of_not_dvd le_sup_left hT₀2 ?_
    have e1 := relIndex_mul_card (H := T₀) (K := T₀ ⊔ O)
    rw [inf_eq_left.mpr le_sup_left] at e1
    have hON : ∀ t : ↥N, t ∈ normalizer (O : Set ↥N) := fun t => by
      rw [normalizer_eq_top]
      exact mem_top t
    have e2 := card_sup_mul_inf_eq_mul_of_normalizes (H := T₀) (K := O) (fun t _ => hON t)
    rw [disjoint_iff.mp hT₀O, card_bot, mul_one, ← e1] at e2
    have hTpos : 0 < Nat.card T₀ := Nat.card_pos
    have e3 : T₀.relIndex (T₀ ⊔ O) = Nat.card O := by
      apply Nat.eq_of_mul_eq_mul_right hTpos
      rw [e2, mul_comm]
    rw [e3]
    exact fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hCT' : centralizer (T' : Set (↥N ⧸ O)) = T' := by
    apply le_antisymm
    · intro yb hyb
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O yb
      have hyN : y ∈ normalizer ((T₀ ⊔ O : Subgroup ↥N) : Set ↥N) := by
        rw [normalizer_eq_top]
        exact mem_top y
      obtain ⟨m, hm, k, hk, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hT₀syl hyN
      have hπm : π m ∈ T' := by
        rw [← hsupπ]
        exact ⟨m, hm, rfl⟩
      have hπk : π k ∈ centralizer (T' : Set (↥N ⧸ O)) := by
        have h1 : π k = (π m)⁻¹ * π (m * k) := by rw [map_mul, inv_mul_cancel_left]
        rw [h1]
        refine mul_mem ?_ hyb
        rw [mem_centralizer_iff]
        intro v hv
        exact (hT'comm v hv _ (inv_mem hπm))
      have hkC : ∀ t ∈ T₀, k * t = t * k := by
        intro t ht
        have hkt : k⁻¹ * t * k ∈ T₀ := by
          have := (mem_normalizer_iff.mp (inv_mem hk) t).mp ht
          rwa [inv_inv] at this
        have hct := mem_centralizer_iff.mp hπk (π t) ⟨t, ht, rfl⟩
        have h1 : t⁻¹ * (k⁻¹ * t * k) ∈ O := by
          rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
          calc (π t)⁻¹ * ((π k)⁻¹ * π t * π k) = (π t)⁻¹ * ((π k)⁻¹ * (π t * π k)) := by group
            _ = (π t)⁻¹ * ((π k)⁻¹ * (π k * π t)) := by rw [hct]
            _ = 1 := by group
        have h2 : t⁻¹ * (k⁻¹ * t * k) ∈ T₀ := mul_mem (inv_mem ht) hkt
        have h3 : t⁻¹ * (k⁻¹ * t * k) = 1 := by
          have := disjoint_iff.mp hT₀O
          rw [eq_bot_iff] at this
          exact (mem_bot.mp (this (mem_inf.mpr ⟨h2, h1⟩)))
        calc k * t = k * t * (t⁻¹ * (k⁻¹ * t * k)) := by rw [h3, mul_one]
          _ = t * k := by group
      have hk' : (k : X) ∈ centralizer (T : Set X) := by
        rw [mem_centralizer_iff]
        intro t ht
        have h1 := hkC ⟨t, hTN ht⟩ (show (⟨t, hTN ht⟩ : ↥N) ∈ T₀ from ht)
        have h2 := congrArg Subtype.val h1
        simpa using h2.symm
      have hkTO : k ∈ T₀ ⊔ O := by
        rw [← hsupT]
        exact mem_subgroupOf.mpr (hCT hk')
      rw [← hsupπ]
      exact ⟨m * k, mul_mem hm hkTO, rfl⟩
    · intro u hu
      rw [mem_centralizer_iff]
      intro v hv
      exact hT'comm v hv u hu
  have hQ2 : IsPGroup 2 (S₀.map π) := hS₀2.map π
  have hQidx : ¬ 2 ∣ (S₀.map π).index := by
    rw [index_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O), index_top,
      mul_one]
    intro h2
    have h3 : (S₀ ⊔ π.ker).index ∣ S₀.index := index_dvd_of_le le_sup_left
    have h4 : S₀.index ∣ S.index := relIndex_dvd_index_of_le hSN
    have h5 := P.not_dvd_index
    rw [hPS] at h5
    exact h5 (h2.trans (h3.trans h4))
  refine ⟨↥N ⧸ O, inferInstance, inferInstance, T', ⟨eT'⟩, hCT', ⟨ψ, hψs, hψk⟩,
    hQ2.toSylow hQidx, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hSN).symm.trans ((MonoidHom.ofInjective hinjS).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range, IsPGroup.toSylow_coe])))

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34EndInvolutions_of_localData
    (hcls : L34CyclicInvolutionClassFact)
    {G : Type} [Group G] [Finite G] {a b : G} {J P Z : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hP : IsSylowTwoIn P J) (hZP : P ⊓ zStarIn J = Z)
    (hZc : IsCyclic ↥Z) (hZ4 : Nat.card Z = 4)
    (haZ : a ∈ Z) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hbP : b ∈ P) (hbb : b * b = 1) (hba : b ≠ a)
    (hbconj : ∃ g : G, b = g⁻¹ * a * g) :
    ∀ u ∈ P, u * u = 1 → u ≠ 1 → ∃ g : G, u = g⁻¹ * a * g := by
  obtain ⟨g, hg⟩ := hbconj
  have hbPJ : b ∈ J := hP.1 hbP
  have hb1 : b ≠ 1 := by
    rintro h
    apply ha1
    calc a = g * b * g⁻¹ := by rw [hg]; group
      _ = 1 := by rw [h]; group
  have hZc' : IsCyclic ↥(P ⊓ zStarIn J) := by rwa [hZP]
  have hZ4' : Nat.card ↥(P ⊓ zStarIn J) = 4 := by rwa [hZP]
  have hbZnot : b ∉ zStarIn J := by
    intro hbZstar
    have hbZ : b ∈ Z := by
      have h : b ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨hbP, hbZstar⟩
      rwa [hZP] at h
    have hb_eq : b = a :=
      eq_of_mul_self_eq_one_of_isCyclic (Q := Z) hZc hbZ haZ hbb haa hb1 ha1
    exact hba hb_eq
  intro u huP huu hu1
  have huJ : u ∈ J := hP.1 huP
  by_cases huZstar : u ∈ zStarIn J
  · have huZ : u ∈ Z := by
      have h : u ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨huP, huZstar⟩
      rwa [hZP] at h
    have hua : u = a :=
      eq_of_mul_self_eq_one_of_isCyclic (Q := Z) hZc huZ haZ huu haa hu1 ha1
    exact ⟨1, by simp [hua]⟩
  · obtain ⟨j, hjJ, hj⟩ := hcls G J P hJ hL34 hP hZc' hZ4' u huJ b hbPJ huu hbb
      huZstar hbZnot
    refine ⟨g * j⁻¹, ?_⟩
    have hu_eq : u = j * b * j⁻¹ := by
      calc u = j * (j⁻¹ * u * j) * j⁻¹ := by group
        _ = j * b * j⁻¹ := by rw [hj]
    calc u = j * b * j⁻¹ := hu_eq
      _ = j * (g⁻¹ * a * g) * j⁻¹ := by rw [hg]
      _ = (g * j⁻¹)⁻¹ * a * (g * j⁻¹) := by group

theorem l34EndInvolutions_of_inputs (hcls : L34CyclicInvolutionClassFact) {G : Type} [Group G]
    [Finite G] {a x : G} {J S : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hZ : S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (hE2 : ∃ g : G, g⁻¹ * a * g ∈ S ⊓ J ∧ g⁻¹ * a * g ≠ a) :
    ∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g := by
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have ha2 : orderOf a = 2 := hU3.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  obtain ⟨g, hgSJ, hga⟩ := hE2
  have hbP : g⁻¹ * a * g ∈ P := hgSJ
  have hbb : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
    rw [show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  have hba : g⁻¹ * a * g ≠ a := hga
  simpa only [hPdef] using
    l34EndInvolutions_of_localData hcls hJper hL34 hP hZP hZc hZ4 haZ haa ha1 hbP hbb hba
      ⟨g, rfl⟩

theorem l34EndStructureRestStep_of_inputs (hcls : L34CyclicInvolutionClassFact)
    (hE3 : L34EndGL32Step) (hE4 : L34EndTStep) (hE6 : L34EndGraphStep) :
    L34EndStructureRestStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hE2
  have hInv := l34EndInvolutions_of_inputs hcls hset hZ hZc hZ4 hE2
  obtain ⟨B, hBSJ, hB8, hBZ, hSB, hBcen, hBaut⟩ :=
    hE3 G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hInv
  rcases hE4 G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hInv B hBSJ hB8 hBZ hSB hBcen
      hBaut _ rfl with ⟨⟨eT⟩, hCT, f, hfs, hfk⟩ | ⟨c, hcS, hc2, hcK, hTc⟩
  · have hSN : S ≤ normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
      fun s hs => inf_mem_normalizer (le_normalizer hs) (mem_normalizer_centralizer (hSB hs))
    exact exists_fourCube_model hSyl rfl inf_le_left hSN eT hCT f hfs hfk
  · exact (hE6 G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hInv B hBSJ hB8 hBZ hSB
      hBcen hBaut c hcS hc2 hcK hTc).elim

end CFSG.ComponentClassification.GrSLit
