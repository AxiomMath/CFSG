module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenP
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenD
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Sporadic.HeldB.OuterCentQS

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier Subgroup

theorem pPrimeCore_heOuterD :
    CFSG.pPrimeCore 2 heOuterD = center heOuterD := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  apply le_antisymm
  · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      (CFSG.pPrimeCore 2 heOuterD) with h | h
    · exact h
    · exfalso
      have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := heOuterD)
      rw [h, Subgroup.card_top, card_heOuterD] at hc
      norm_num at hc
  · refine le_sSup ?_
    rw [Set.mem_ofPred_eq]
    exact ⟨inferInstance, by rw [card_center_heOuterD]; norm_num⟩

theorem map_subtype_normalizer {G : Type*} [Group G] {H : Subgroup G} (F : Subgroup H) :
    (normalizer (F : Set H)).map H.subtype =
      H ⊓ normalizer ((F.map H.subtype : Subgroup G) : Set G) := by
  have h1 : F = (F.map H.subtype).comap H.subtype :=
    (comap_map_eq_self_of_injective H.subtype_injective F).symm
  have h2 : F.map H.subtype ≤ H.subtype.range := by
    rw [range_subtype]
    exact map_subtype_le F
  conv_lhs => rw [h1, ← comap_normalizer_eq_of_le_range h2]
  rw [map_comap_eq, range_subtype]

theorem sq_eq_one_of_four {G : Type*} [Group G] {F : Subgroup G}
    (φ : F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : ∀ f ∈ F, f ^ 2 = 1 := by
  intro f hf
  have hsq : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by decide
  have := congrArg (fun z : F => (z : G)) (φ.injective (by rw [map_pow, hsq, map_one] :
    φ (⟨f, hf⟩ ^ 2) = φ 1))
  simpa using this

theorem card_of_four {G : Type*} [Group G] {F : Subgroup G}
    (φ : F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : Nat.card F = 4 := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem genAt_u
    (hy : heAutU ∈ heAutGroup) : GenAt heP (heConjR ⟨heAutU, hy⟩) := by
  intro m hL e F hFL hF hD
  have hK := map_layerOfFixed_heConjR (⟨heAutU, hy⟩ : heAutGroup)
  set L := Sol78.layerOfFixed (heConjR ⟨heAutU, hy⟩) with hLdef
  obtain ⟨hDC, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  obtain ⟨φF⟩ := hF
  have hF4 := card_of_four φF
  have hF2 := sq_eq_one_of_four φF
  have hLC : L.map heP.subtype = layerIn heOuterC := by
    rw [hK, heOuterC_eq]
  have hFK : F.map heP.subtype ≤ layerIn heOuterC := hLC ▸ map_mono hFL
  have hCD : layerIn heOuterC = heOuterD := by
    have hKD : layerIn heOuterC ≤ heOuterD := by
      rw [hDC, ← layerIn_perfect heOuterC]
      exact commutator_mono (layerIn_le _) (layerIn_le _)
    have hKn : ((layerIn heOuterC).subgroupOf heOuterD).Normal := ⟨fun k hk d => by
      rw [mem_subgroupOf] at hk ⊢
      exact conj_mem_layerIn heOuterC (heOuterD_le_C d.2) hk⟩
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      ((layerIn heOuterC).subgroupOf heOuterD) with h | h
    · exfalso
      have hab : ⁅layerIn heOuterC, layerIn heOuterC⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [mem_centralizer_iff]
        intro z hz
        have hc := Subgroup.mem_center_iff.1
          (h (show (⟨x, hKD hx⟩ : heOuterD) ∈ (layerIn heOuterC).subgroupOf heOuterD from hx))
          ⟨z, hKD hz⟩
        exact congrArg Subtype.val hc
      have hbot : layerIn heOuterC = ⊥ := (layerIn_perfect heOuterC).symm.trans hab
      rw [hbot, le_bot_iff, map_eq_bot_iff_of_injective _ heP.subtype_injective] at hFK
      rw [hFK, card_bot] at hF4
      norm_num at hF4
    · refine le_antisymm hKD fun d hd => ?_
      have : (⟨d, hd⟩ : heOuterD) ∈ (layerIn heOuterC).subgroupOf heOuterD := h ▸ mem_top _
      exact mem_subgroupOf.1 this
  have hLD : L.map heP.subtype = heOuterD := hLC.trans hCD
  set ι : L →* Equiv.Perm (Fin 8330) := heP.subtype.comp L.subtype with hι
  have hιi : Function.Injective ι := heP.subtype_injective.comp L.subtype_injective
  have hιr : ι.range = heOuterD := by
    rw [hι, MonoidHom.range_comp, range_subtype, hLD]
  let ψD : L ≃* heOuterD := (MonoidHom.ofInjective hιi).trans (MulEquiv.subgroupCongr hιr)
  have hOZ : CFSG.pPrimeCore 2 L = center L := by
    apply Subgroup.map_injective (f := ψD.toMonoidHom) ψD.injective
    have h2 : (center L).map ψD.toMonoidHom = center heOuterD := Subgroup.map_center_eq ψD
    rw [pPrimeCore_map_iso 2 ψD, pPrimeCore_heOuterD, h2]
  have hZ3 : Nat.card (center L) = 3 := by
    rw [← card_center_heOuterD]
    exact Nat.card_congr (Subgroup.centerCongr ψD).toEquiv
  have hL7560 : Nat.card L = 7560 := by
    rw [← card_heOuterD]
    exact Nat.card_congr ψD.toEquiv
  obtain ⟨S, hS4, hSfix⟩ := hD
  have hm4 := four_le_of_card S hS4
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hq2520 : m.factorial / 2 = 2520 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 L)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hOZ, hZ3,
      hL7560] at h1
    omega
  have hm7 : m = 7 := by
    have h6 : ¬ m ≤ 6 := fun h => by
      have h1 : m.factorial / 2 ≤ Nat.factorial 6 / 2 := Nat.div_le_div_right (Nat.factorial_le h)
      have h720 : Nat.factorial 6 / 2 = 360 := by decide
      omega
    have h8 : ¬ 8 ≤ m := fun h => by
      have h1 : Nat.factorial 8 / 2 ≤ m.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le h)
      have h40 : Nat.factorial 8 / 2 = 20160 := by decide
      omega
    omega
  subst hm7
  set f : L →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 2 L)) with hfdef
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : ∀ x, x ∈ f.ker ↔ x ∈ CFSG.pPrimeCore 2 L := fun x => by
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker3 : ∀ z ∈ f.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hfker, hOZ] at hz
    have h := pow_card_eq_one' (G := center L) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  have hkerZ : f.ker ≤ center L := fun z hz => by rw [hfker, hOZ] at hz; exact hz
  have hFQ : Nat.card (F.subgroupOf L) = 4 := by
    rw [← hF4]
    exact Nat.card_congr (subgroupOfEquivOfLe hFL).toEquiv
  have hFQ2 : ∀ x ∈ F.subgroupOf L, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hF2 _ (mem_subgroupOf.1 hx))
  obtain ⟨hF₀4, hF₀2, hF₀D⟩ := heGenF0_four
  have hF₀r : heGenF0 ≤ ι.range := hιr ▸ hF₀D
  have hF₀Q : Nat.card (heGenF0.comap ι) = 4 := by
    rw [← hF₀4, ← card_map_of_injective hιi, map_comap_eq_self hF₀r]
  have hF₀Q2 : ∀ x ∈ heGenF0.comap ι, x ^ 2 = 1 := fun x hx =>
    hιi (by rw [map_pow, hF₀2 (ι x) (mem_comap.1 hx), map_one])
  obtain ⟨hc3, hcF, hcD, hcd⟩ := heGenC_facts
  have hcR : heGenC ∈ ι.range := hιr.symm ▸ hcD
  obtain ⟨cQ, hcQ⟩ := hcR
  have hcQ3 : cQ ^ 3 = 1 := hιi (by rw [map_pow, hcQ, hc3, map_one])
  have hcQ1 : f cQ ≠ 1 := by
    intro h1
    have hz : cQ ∈ center L := hkerZ h1
    have hdR : heOuterDGen 0 ∈ ι.range := hιr.symm ▸ heOuterDGen_mem_D 0 (by norm_num)
    obtain ⟨d, hd⟩ := hdR
    apply hcd
    have := congrArg ι (Subgroup.mem_center_iff.1 hz d)
    rw [map_mul, map_mul, hd, hcQ] at this
    exact this.symm
  have hcQF : ∀ x ∈ heGenF0.comap ι, cQ * x = x * cQ := fun x hx =>
    hιi (by rw [map_mul, map_mul, hcQ, hcF (ι x) (mem_comap.1 hx)])
  have hFS : ∀ x ∈ F.subgroupOf L, ∀ ω ∉ S,
      ((f x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ω = ω :=
    fun x hx ω hω => hSfix x (mem_subgroupOf.1 hx) ω hω
  obtain ⟨a, ha⟩ := exists_conj_of_tripleCover f hf hker3 hkerZ hFQ hFQ2 hF₀Q hF₀Q2 hcQ3 hcQ1
    hcQF hS4 hFS
  have hFmap : F.map heP.subtype = heGenF0.map (MulAut.conj (ι a)).toMonoidHom := by
    have h1 : (F.subgroupOf L).map ι = F.map heP.subtype := by
      rw [hι, ← map_map, subgroupOf_map_subtype, inf_of_le_left hFL]
    rw [← h1, ← ha, map_map]
    conv_rhs => rw [← map_comap_eq_self hF₀r, map_map]
    congr 1
  have hb : ι a ∈ heOuterD := hιr ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩
  apply Subgroup.map_injective (f := heP.subtype) heP.subtype_injective
  rw [Subgroup.map_sup, hLD, map_subtype_normalizer, hFmap, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact heOuterD_sup_normalizer_conj hb

end CFSG.ComponentClassification.SolMax.HeGen
