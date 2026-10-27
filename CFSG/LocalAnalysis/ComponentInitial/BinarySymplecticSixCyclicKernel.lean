module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup CFSG.Assembly.LowTwoRank SymplecticFlag
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (exists_eq_spInner_mul_fieldAut
  spInner_eq_conj)
open CFSG.ComponentClassification.StandardRecognition
  (glauberman_zStar_central_sylow_involution_univ)

@[expose] def projEquiv : StatedSp 3 (ZMod 2) ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
  MulEquiv.ofBijective (proj 3 (ZMod 2))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj]
      exact statedScalars_subgroupOf_eq_bot (Nat.card_zmod 2) 3,
    SymplecticHigher.proj_surjective⟩

theorem projEquiv_apply (g : StatedSp 3 (ZMod 2)) : projEquiv g = proj 3 (ZMod 2) g :=
  rfl

theorem exists_eq_conj_statedSp (α : MulAut (StatedSp 3 (ZMod 2))) :
    ∃ g : StatedSp 3 (ZMod 2), α = MulAut.conj g := by
  set β : MulAut (StatedProj (StatedSp 3 (ZMod 2))) := (projEquiv.symm.trans α).trans projEquiv
    with hβ
  have hE := (SymplecticHigher.automorphism_generation (r := 3) (K := ZMod 2) le_rfl).1
  obtain ⟨g, φ, hg⟩ :=
    exists_eq_spInner_mul_fieldAut (r := 3) (K := ZMod 2) (hE ▸ Subgroup.mem_top β)
  have hφ : φ = 1 := RingEquiv.toRingHom_injective (Subsingleton.elim _ _)
  rw [hφ, map_one, mul_one, spInner_eq_conj] at hg
  refine ⟨g, MulEquiv.ext fun x => projEquiv.injective ?_⟩
  have h := congrArg (fun γ : MulAut (StatedProj (StatedSp 3 (ZMod 2))) => γ (projEquiv x)) hg
  simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rfl

theorem exists_eq_conj_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) (α : MulAut Q) : ∃ q : Q, α = MulAut.conj q := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel hQ
  obtain ⟨g, hg⟩ := exists_eq_conj_statedSp ((e.symm.trans α).trans e)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h := congrArg (fun γ : MulAut (StatedSp 3 (ZMod 2)) => γ (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

section Product

variable {G : Type*} [Group G]

theorem map_conj_eq_of_normal {L H : Subgroup G} (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    {h : G} (hh : h ∈ H) : L.map (MulAut.conj h).toMonoidHom = L := by
  have hmem : ∀ {k : G}, k ∈ H → ∀ x ∈ L, k * x * k⁻¹ ∈ L := fun {k} hk x hx => by
    have := hLn.conj_mem ⟨x, hLH hx⟩ (mem_subgroupOf.2 hx) ⟨k, hk⟩
    rwa [mem_subgroupOf] at this
  refine le_antisymm ?_ fun x hx => ⟨h⁻¹ * x * h, by simpa using hmem (inv_mem hh) x hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmem hh x hx
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

@[expose] def conjRestrict (L : Subgroup G) (h : G) (hL : L.map (MulAut.conj h).toMonoidHom = L) :
    MulAut L :=
  ((MulAut.conj h).subgroupMap L).trans (MulEquiv.subgroupCongr hL)

theorem coe_conjRestrict (L : Subgroup G) (h : G) (hL : L.map (MulAut.conj h).toMonoidHom = L)
    (x : L) : (conjRestrict L h hL x : G) = h * x * h⁻¹ :=
  rfl

theorem sup_eq_of_inner {L H T : Subgroup G} (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hinner : ∀ α : MulAut L, ∃ l : L, α = MulAut.conj l)
    (hT : centralizer (L : Set G) ⊓ H = T) : L ⊔ T = H := by
  refine le_antisymm (sup_le hLH (hT ▸ inf_le_right)) fun h hh => ?_
  obtain ⟨l, hl⟩ := hinner (conjRestrict L h (map_conj_eq_of_normal hLH hLn hh))
  have hc : (l : G)⁻¹ * h ∈ T := by
    rw [← hT]
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_,
      H.mul_mem (H.inv_mem (hLH l.2)) hh⟩
    have h1 := congrArg (fun y : L => (y : G)) (MulEquiv.congr_fun hl ⟨x, hx⟩)
    simp only [coe_conjRestrict, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * ((l : G)⁻¹ * h) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * h := by group
      _ = (l : G)⁻¹ * (h * x * h⁻¹) * h := by rw [h1]
      _ = (l : G)⁻¹ * h * x := by group
  have : h = l * ((l : G)⁻¹ * h) := by group
  rw [this]
  exact mul_mem (mem_sup_left l.2) (mem_sup_right hc)

end Product

theorem centralizer_eq_top_of_isolated {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {z : G} (hz : orderOf z = 2)
    (hiso : ∀ g : G, g⁻¹ * z * g ∈ centralizer ({z} : Set G) → g⁻¹ * z * g = z) :
    centralizer ({z} : Set G) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({z} : Set G) with hHdef
  have hzH : z ∈ H := mem_centralizer_singleton_iff.2 rfl
  let P : Sylow 2 H := default
  have hzP : (⟨z, hzH⟩ : H) ∈ (P : Subgroup H) := by
    have hcen : (⟨z, hzH⟩ : H) ∈ center H := mem_center_iff.2 fun h =>
      Subtype.ext (mem_centralizer_singleton_iff.1 h.2)
    have hp : IsPGroup 2 (zpowers (⟨z, hzH⟩ : H)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, orderOf_mk, hz, pow_one])
    have : (zpowers (⟨z, hzH⟩ : H)).Normal :=
      (normal_of_le_center (zpowers_le.2 hcen))
    exact hp.le_sylow_of_normal P (mem_zpowers _)
  set PG := (P : Subgroup H).map H.subtype with hPG
  have hPGH : PG ≤ H := map_subtype_le _
  have hzPG : z ∈ PG := ⟨_, hzP, rfl⟩
  obtain ⟨S, hPS⟩ := (P.isPGroup'.map H.subtype).exists_le_sylow
  have hnorm : ∀ n : G, n ∈ normalizer (PG : Set G) → n ∈ H := by
    intro n hn
    have h1 : n * z * n⁻¹ ∈ PG := (mem_normalizer_iff.1 hn z).1 hzPG
    have h2 := hiso n⁻¹ (by rw [inv_inv]; exact hPGH h1)
    rw [inv_inv] at h2
    rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h2]
  have hSeq : PG = S := by
    by_contra hne
    have hlt : PG.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hPS fun x hx => ?_
      have : (⟨x, hx⟩ : S) ∈ PG.subgroupOf S := htop ▸ mem_top _
      exact this
    obtain ⟨n, hn, hnU⟩ := IsConcreteLE.exists_of_lt
      (p_group_normalizer_condition S.isPGroup' hlt)
    set Q : Subgroup G :=
      (normalizer ((PG.subgroupOf S : Subgroup S) : Set S)).map (S : Subgroup G).subtype
    have hQH : Q ≤ H := by
      rintro _ ⟨m, hm, rfl⟩
      refine hnorm m (mem_normalizer_iff.2 fun y => ?_)
      constructor
      · intro hy
        have hyS : y ∈ (S : Subgroup G) := hPS hy
        have := (mem_normalizer_iff.1 hm ⟨y, hyS⟩).1 (mem_subgroupOf.2 hy)
        rwa [mem_subgroupOf] at this
      · intro hy
        have hyS : y ∈ (S : Subgroup G) := by
          have := hPS hy
          have h' : (m : G)⁻¹ * (m * y * (m : G)⁻¹) * m ∈ (S : Subgroup G) :=
            mul_mem (mul_mem (inv_mem m.2) this) m.2
          simpa [mul_assoc] using h'
        have := (mem_normalizer_iff.1 hm ⟨y, hyS⟩).2 (mem_subgroupOf.2 hy)
        rwa [mem_subgroupOf] at this
    have hQp : IsPGroup 2 (Q.subgroupOf H) :=
      (S.isPGroup'.to_le (map_subtype_le _)).comap_subtype
    have hPQ : (P : Subgroup H) ≤ Q.subgroupOf H := by
      intro x hx
      rw [mem_subgroupOf]
      have hxS : (x : G) ∈ (S : Subgroup G) := hPS ⟨x, hx, rfl⟩
      refine ⟨⟨x, hxS⟩, le_normalizer (mem_subgroupOf.2 ⟨x, hx, rfl⟩), rfl⟩
    have hPeq := P.is_maximal' hQp hPQ
    apply hnU
    have hnQ : (n : G) ∈ Q := ⟨n, hn, rfl⟩
    have : (⟨n, hQH hnQ⟩ : H) ∈ (P : Subgroup H) := by
      rw [← hPeq]
      exact mem_subgroupOf.2 hnQ
    exact mem_subgroupOf.2 ⟨_, this, rfl⟩
  have hSH : (S : Subgroup G) ≤ H := hSeq ▸ hPGH
  have hzS : z ∈ (S : Subgroup G) := hSeq ▸ hzPG
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ center (S : Subgroup G) :=
    mem_center_iff.2 fun s => Subtype.ext (mem_centralizer_singleton_iff.1 (hSH s.2))
  obtain ⟨hfac, -⟩ := glauberman_zStar_central_sylow_involution_univ S ⟨z, hzS⟩ hzZ
    (by rw [orderOf_mk, hz]) fun g hg => hiso g (hSH hg)
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
  rw [hG, mem_bot] at hk
  rw [hk, mul_one]
  exact hc

section Decomposition

variable {G : Type*} [Group G]

theorem mem_sup_of_le_centralizer {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G))
    {x : G} : x ∈ L ⊔ T ↔ ∃ l ∈ L, ∃ s ∈ T, l * s = x := by
  have hc : ∀ {l s : G}, l ∈ L → s ∈ T → l * s = s * l := fun hl hs =>
    mem_centralizer_iff.1 (hT hs) _ hl
  constructor
  · intro hx
    let K : Subgroup G :=
      { carrier := {x | ∃ l ∈ L, ∃ s ∈ T, l * s = x}
        mul_mem' := by
          rintro _ _ ⟨l, hl, s, hs, rfl⟩ ⟨l', hl', s', hs', rfl⟩
          refine ⟨l * l', mul_mem hl hl', s * s', mul_mem hs hs', ?_⟩
          calc l * l' * (s * s') = l * (l' * s) * s' := by group
            _ = l * (s * l') * s' := by rw [hc hl' hs]
            _ = l * s * (l' * s') := by group
        one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
        inv_mem' := by
          rintro _ ⟨l, hl, s, hs, rfl⟩
          refine ⟨l⁻¹, inv_mem hl, s⁻¹, inv_mem hs, ?_⟩
          rw [mul_inv_rev, ← mul_inv_rev, ← mul_inv_rev, hc hl hs] }
    have hK : L ⊔ T ≤ K := sup_le (fun l hl => ⟨l, hl, 1, one_mem _, mul_one l⟩)
      (fun s hs => ⟨1, one_mem _, s, hs, one_mul s⟩)
    exact hK hx
  · rintro ⟨l, hl, s, hs, rfl⟩
    exact mul_mem_sup hl hs

theorem commute_of_le_centralizer {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G))
    (l : L) (t : T) : Commute (L.subtype l) (T.subtype t) :=
  mem_centralizer_iff.1 (hT t.2) l l.2

@[expose] def mulProd {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) : L × T →* G :=
  L.subtype.noncommCoprod T.subtype (commute_of_le_centralizer hT)

theorem mulProd_apply {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (p : L × T) :
    mulProd hT p = (p.1 : G) * p.2 :=
  rfl

theorem mulProd_injective {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G))
    (hLT : L ⊓ T = ⊥) : Function.Injective (mulProd hT) := by
  rintro ⟨l, s⟩ ⟨l', s'⟩ h
  rw [mulProd_apply, mulProd_apply] at h
  have h1 : (l' : G)⁻¹ * l = s' * (s : G)⁻¹ := by
    calc (l' : G)⁻¹ * l = (l' : G)⁻¹ * (l * s) * (s : G)⁻¹ := by group
      _ = (l' : G)⁻¹ * (l' * s') * (s : G)⁻¹ := by rw [h]
      _ = s' * (s : G)⁻¹ := by group
  have hmem : (l' : G)⁻¹ * l ∈ L ⊓ T :=
    Subgroup.mem_inf.2 ⟨L.mul_mem (L.inv_mem l'.2) l.2, h1 ▸ T.mul_mem s'.2 (T.inv_mem s.2)⟩
  rw [hLT, mem_bot, inv_mul_eq_one] at hmem
  have hl : l = l' := Subtype.ext hmem.symm
  subst hl
  have hs : s = s' := Subtype.ext (mul_left_cancel h)
  rw [hs]

theorem range_mulProd {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) :
    (mulProd hT).range = L ⊔ T := by
  ext x
  rw [MonoidHom.mem_range, mem_sup_of_le_centralizer hT]
  constructor
  · rintro ⟨⟨l, s⟩, rfl⟩
    exact ⟨l, l.2, s, s.2, rfl⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    exact ⟨(⟨l, hl⟩, ⟨s, hs⟩), rfl⟩

theorem card_sup_eq_mul {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (hLT : L ⊓ T = ⊥) :
    Nat.card (L ⊔ T : Subgroup G) = Nat.card L * Nat.card T := by
  rw [← range_mulProd hT, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective (mulProd_injective hT hLT)).toEquiv).symm

@[expose] noncomputable def projL {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G))
    (hLT : L ⊓ T = ⊥) : (L ⊔ T : Subgroup G) →* L :=
  (MonoidHom.fst L T).comp ((MonoidHom.ofInjective (mulProd_injective hT hLT)).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr (range_mulProd hT).symm).toMonoidHom)

theorem mulProd_projL {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (hLT : L ⊓ T = ⊥)
    (x : (L ⊔ T : Subgroup G)) :
    ∃ s ∈ T, (x : G) = projL hT hLT x * s := by
  set e := MonoidHom.ofInjective (mulProd_injective hT hLT)
  set x' : (mulProd hT).range := MulEquiv.subgroupCongr (range_mulProd hT).symm x
  have h : mulProd hT (e.symm x') = (x' : G) := by
    have := MonoidHom.ofInjective_apply (mulProd_injective hT hLT) (x := e.symm x')
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(e.symm x').2, (e.symm x').2.2, ?_⟩
  rw [mulProd_apply] at h
  exact h.symm

theorem projL_eq_of_mul {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (hLT : L ⊓ T = ⊥)
    (x : (L ⊔ T : Subgroup G)) {l s : G} (hl : l ∈ L) (hs : s ∈ T) (hx : (x : G) = l * s) :
    (projL hT hLT x : G) = l := by
  obtain ⟨s', hs', hx'⟩ := mulProd_projL hT hLT x
  have := mulProd_injective hT hLT
    (a₁ := (projL hT hLT x, ⟨s', hs'⟩)) (a₂ := (⟨l, hl⟩, ⟨s, hs⟩))
    (by rw [mulProd_apply, mulProd_apply]; exact hx'.symm.trans hx)
  exact congrArg (fun p : L × T => (p.1 : G)) this

theorem projL_eq_one_iff {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (hLT : L ⊓ T = ⊥)
    (x : (L ⊔ T : Subgroup G)) : projL hT hLT x = 1 ↔ (x : G) ∈ T := by
  constructor
  · intro h
    obtain ⟨s, hs, hx⟩ := mulProd_projL hT hLT x
    rw [h, OneMemClass.coe_one, one_mul] at hx
    exact hx ▸ hs
  · intro hx
    exact Subtype.ext (projL_eq_of_mul hT hLT x (one_mem L) hx (one_mul _).symm)

theorem projL_of_mem {L T : Subgroup G} (hT : T ≤ centralizer (L : Set G)) (hLT : L ⊓ T = ⊥)
    (x : (L ⊔ T : Subgroup G)) (hx : (x : G) ∈ L) : (projL hT hLT x : G) = x :=
  projL_eq_of_mul hT hLT x hx (one_mem T) (mul_one _).symm

end Decomposition

theorem standard_binary_symplectic_six_initial {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype ≤
        centralizer (L : Set G) ∧
      L ⊔ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype =
        centralizer ({z} : Set G) ∧
      L ⊓ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = ⊥ ∧
      (∀ s ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype,
        orderOf s = 2 → s = z) ∧
      IsCyclic ((T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype) ∧
      ∃ g : G, g⁻¹ * z * g ∈ centralizer ({z} : Set G) ∧ g⁻¹ * z * g ≠ z := by
  obtain ⟨t, htT, htz⟩ := hzT
  rw [Subgroup.coe_subtype] at htz
  subst htz
  have ht : orderOf t = 2 := by rwa [orderOf_coe] at hz
  obtain ⟨-, huniq, hLH, hLnH, -, -, hCT, -, hLT⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hL T hT htT ht hH
  set TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    with hTG
  have hsup : L ⊔ TG = centralizer ({(t : G)} : Set G) :=
    sup_eq_of_inner hLH hLnH (exists_eq_conj_of_lieModel hmodel) hCT
  refine ⟨map_subtype_le _, hsup, by rw [hLT, hZ, Subgroup.map_bot], ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ hs2
    rw [Subgroup.coe_subtype] at hs2 ⊢
    rw [huniq s hs (by rwa [orderOf_coe] at hs2)]
  · exact (equivMapOfInjective _ _ (subtype_injective _)).isCyclic.1 hT
  · by_contra hcon
    have hiso : ∀ g : G, g⁻¹ * (t : G) * g ∈ centralizer ({(t : G)} : Set G) →
        g⁻¹ * (t : G) * g = t := fun g hg => by
      by_contra hne
      exact hcon ⟨g, hg, hne⟩
    have htop := centralizer_eq_top_of_isolated hG hz hiso
    apply hLn
    refine ⟨fun n hn g => ?_⟩
    have hgH : g ∈ centralizer ({(t : G)} : Set G) := htop ▸ mem_top g
    have h := map_conj_eq_of_normal hLH hLnH hgH
    rw [← h]
    exact ⟨n, hn, rfl⟩

section Kernel

variable {G : Type*} [Group G]

theorem orderOf_inv_mul_mul (g z : G) : orderOf (g⁻¹ * z * g) = orderOf z := by
  have h : g⁻¹ * z * g = MulAut.conj g⁻¹ z := by rw [MulAut.conj_apply, inv_inv]
  rw [h, MulEquiv.orderOf_eq]

theorem card_le_two_of_le_isCyclic [Finite G] {C M : Subgroup G} (hC : IsCyclic C) (hMC : M ≤ C)
    (hM : ∀ x ∈ M, x ^ 2 = 1) : Nat.card M ≤ 2 := by
  have : IsCyclic (M.subgroupOf C) := Subgroup.isCyclic _
  have : IsCyclic M := (subgroupOfEquivOfLe hMC).isCyclic.1 this
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := M)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hx]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one
    (Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hM x x.2)))

theorem inf_map_conj_eq_bot [Finite G] {T : Subgroup G} {z : G}
    (huniq : ∀ s ∈ T, orderOf s = 2 → s = z) (hT2 : IsPGroup 2 T) {g : G}
    (hne : g⁻¹ * z * g ≠ z) : T ⊓ T.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hM
  set M := T ⊓ T.map (MulAut.conj g⁻¹).toMonoidHom
  have hMp : IsPGroup 2 M := hT2.to_le inf_le_left
  have h2 : 2 ∣ Nat.card M := by
    rcases hMp.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).1 h) hM
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw2 : orderOf (w : G) = 2 := by rw [orderOf_coe, hw]
  have hwz : (w : G) = z := huniq _ (Subgroup.mem_inf.1 w.2).1 hw2
  obtain ⟨t, htT, htw⟩ := mem_map.1 (Subgroup.mem_inf.1 w.2).2
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at htw
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_inv_mul_mul g t, htw, hw2]
  rw [huniq t htT ht2, hwz] at htw
  exact hne htw

end Kernel

theorem standard_binary_symplectic_six_sylow_eq {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTC, hsup, hinf, huniq, hcyc, g, hgH, hgne⟩ :=
    standard_binary_symplectic_six_initial hG hL hLn hZ hmodel T hT hzT hz hH
  set TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    with hTG
  have hTG2 : IsPGroup 2 TG := T.isPGroup'.map _
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hzL : z ∈ centralizer (L : Set G) := hTC hzT
  set y := g⁻¹ * z * g with hy
  have hy2 : orderOf y = 2 := by rw [hy, orderOf_inv_mul_mul, hz]
  obtain ⟨u, huL, s, hsT, hus⟩ := (mem_sup_of_le_centralizer hTC).1 (hsup ▸ hgH)
  have hcomm : u * s = s * u := mem_centralizer_iff.1 (hTC hsT) u huL
  have hy2' : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2] at h
  have hsq : u ^ 2 * s ^ 2 = 1 := by
    rw [← hy2', ← hus, pow_two, pow_two, pow_two]
    calc u * u * (s * s) = u * (u * s) * s := by group
      _ = u * (s * u) * s := by rw [hcomm]
      _ = u * s * (u * s) := by group
  have hu2 : u ^ 2 = 1 := by
    have hmem : u ^ 2 ∈ L ⊓ TG := Subgroup.mem_inf.2 ⟨L.pow_mem huL 2, by
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact TG.inv_mem (TG.pow_mem hsT 2)⟩
    rwa [hinf, mem_bot] at hmem
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [one_mul] at hus
    exact hgne (huniq y (hus ▸ hsT) hy2)
  obtain ⟨V, _, _, _, b, hb, hnd, hV, ⟨φ₀⟩⟩ := exists_model_of_lieModel hmodel
  obtain ⟨W', hW', hd', huA⟩ := exists_radical_mem_of_model hb hnd hV φ₀ huL hu2
  set A₀ := pullSub φ₀ (pointwiseStabilizer b W') with hA₀
  obtain ⟨hA₀e, hA₀c, hA₀C, -⟩ := pullSub_radical hb hnd hV φ₀ hW' hd'
  have hA₀L : A₀ ≤ L := pullSub_le φ₀ _
  have hA₀comm : ∀ a ∈ A₀, ∀ a' ∈ A₀, a * a' = a' * a := fun a ha a' ha' =>
    mul_comm_of_isElementaryAbelian hA₀e ha ha'
  have hTGcomm : ∀ t ∈ TG, ∀ t' ∈ TG, t * t' = t' * t := by
    have : IsMulCommutative TG := IsCyclic.isMulCommutative
    exact fun t ht t' ht' => congrArg Subtype.val (this.is_comm.comm ⟨t, ht⟩ ⟨t', ht'⟩)
  have hTA₀ : TG ≤ centralizer (A₀ : Set G) := fun t ht =>
    mem_centralizer_iff.2 fun a ha => mem_centralizer_iff.1 (hTC ht) a (hA₀L ha)
  set K := A₀ ⊔ TG with hK
  have hKy : K ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 ?_)
      (fun t ht => mem_centralizer_singleton_iff.2 ?_)
    · rw [← hus]
      calc a * (u * s) = a * u * s := by group
        _ = u * a * s := by rw [hA₀comm a ha u huA]
        _ = u * (a * s) := by group
        _ = u * (s * a) := by rw [mem_centralizer_iff.1 (hTC hsT) a (hA₀L ha)]
        _ = u * s * a := by group
    · rw [← hus]
      calc t * (u * s) = t * u * s := by group
        _ = u * t * s := by rw [mem_centralizer_iff.1 (hTC ht) u huL]
        _ = u * (t * s) := by group
        _ = u * (s * t) := by rw [hTGcomm t ht s hsT]
        _ = u * s * t := by group
  set c := MulAut.conj g with hc
  have hcy : c y = z := by rw [hc, MulAut.conj_apply, hy]; group
  have hKc : K.map c.toMonoidHom ≤ L ⊔ TG := by
    rw [hsup]
    rintro _ ⟨x, hx, rfl⟩
    have := mem_centralizer_singleton_iff.1 (hKy hx)
    rw [mem_centralizer_singleton_iff, ← hcy, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, this]
  set pr := projL hTC hinf with hpr
  set f : K.map c.toMonoidHom →* L := pr.comp (inclusion hKc) with hf
  set P := A₀ ⊔ zpowers z with hP
  have hzTG : zpowers z ≤ TG := zpowers_le.2 hzT
  have hPK : P ≤ K := sup_le_sup_left hzTG _
  have : IsElementaryAbelian 2 A₀ := hA₀e
  have : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hPe : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.sup_of_le_centralizer (hzTG.trans hTA₀)
  have hA₀z : A₀ ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hA₀L hzTG
  have hPcard : Nat.card P = 128 := by
    rw [hP, card_sup_eq_mul (hzTG.trans hTA₀) hA₀z, hA₀c, Nat.card_zpowers, hz]
  set Pc : Subgroup (K.map c.toMonoidHom) := (P.map c.toMonoidHom).subgroupOf (K.map c.toMonoidHom)
    with hPc
  set E₀ : Subgroup G := (Pc.map f).map L.subtype with hE₀
  have hPc_card : Nat.card Pc = 128 := by
    rw [hPc, Nat.card_congr (subgroupOfEquivOfLe (map_mono hPK)).toEquiv,
      card_map_of_injective c.injective, hPcard]
  have hPcsq : ∀ x ∈ P.map c.toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, pow_two, mul_self_of_isElementaryAbelian hPe hp, map_one]
  set fP : Pc →* L := f.comp Pc.subtype with hfP
  set ι : Pc →* G := (K.map c.toMonoidHom).subtype.comp Pc.subtype with hι
  have hιinj : Function.Injective ι := (subtype_injective _).comp (subtype_injective _)
  have hker : fP.ker.map ι ≤ TG ⊓ P.map c.toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : pr (inclusion hKc (x : K.map c.toMonoidHom)) = 1 := hx
      exact (projL_eq_one_iff hTC hinf _).1 h1
    · exact x.2
  have hkercard : Nat.card fP.ker ≤ 2 := by
    rw [← card_map_of_injective hιinj]
    exact (Nat.card_mono (Set.toFinite _) hker).trans
      (card_le_two_of_le_isCyclic hcyc inf_le_left fun x hx => hPcsq x (Subgroup.mem_inf.1 hx).2)
  have hcardP : Nat.card Pc = Nat.card fP.range * Nat.card fP.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fP.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange fP).toEquiv]
  have hE₀eq : E₀ = fP.range.map L.subtype := by
    rw [hE₀, hfP, MonoidHom.range_comp, Subgroup.range_subtype]
  have hE₀card : 64 ≤ Nat.card E₀ := by
    rw [hE₀eq, card_map_of_injective (subtype_injective L)]
    have := hcardP ▸ hPc_card
    by_contra hlt
    have h1 : Nat.card fP.range * Nat.card fP.ker ≤ 63 * 2 :=
      Nat.mul_le_mul (by omega) hkercard
    omega
  have hE₀L : E₀ ≤ L := map_subtype_le _
  have : IsElementaryAbelian 2 (P.map c.toMonoidHom) := IsElementaryAbelian.map _
  have : IsElementaryAbelian 2 Pc := IsElementaryAbelian.subgroupOf (map_mono hPK)
  have hE₀e : IsElementaryAbelian 2 E₀ := by
    rw [hE₀, Subgroup.map_map]
    exact IsElementaryAbelian.map _
  obtain ⟨h64, hW''⟩ := elementary_le_of_model hb hnd hV φ₀ hE₀L hE₀e
  obtain ⟨W'', hW''i, hd'', hE₀W⟩ := hW'' (le_antisymm h64 hE₀card)
  obtain ⟨-, -, hE₀C, -⟩ := pullSub_radical hb hnd hV φ₀ hW''i hd''
  rw [← hE₀W] at hE₀C
  have hKcomm : ∀ x ∈ K, ∀ x' ∈ K, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_le_centralizer hTA₀).1 hx
    obtain ⟨a', ha', t', ht', rfl⟩ := (mem_sup_of_le_centralizer hTA₀).1 hx'
    have h1 : t * a' = a' * t := (mem_centralizer_iff.1 (hTA₀ ht) a' ha').symm
    have h2 : t' * a = a * t' := (mem_centralizer_iff.1 (hTA₀ ht') a ha).symm
    calc a * t * (a' * t') = a * (t * a') * t' := by group
      _ = a * (a' * t) * t' := by rw [h1]
      _ = a * a' * (t * t') := by group
      _ = a' * a * (t * t') := by rw [hA₀comm a ha a' ha']
      _ = a' * a * (t' * t) := by rw [hTGcomm t ht t' ht']
      _ = a' * (a * t') * t := by group
      _ = a' * (t' * a) * t := by rw [h2]
      _ = a' * t' * (a * t) := by group
  have hKccomm : ∀ k k' : K.map c.toMonoidHom, k * k' = k' * k := by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, x', hx', rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hKcomm x hx x' hx']
  have hfcomm : ∀ k k' : K.map c.toMonoidHom, (f k : G) * f k' = f k' * f k := fun k k' => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hKccomm k k']
  have hfE : ∀ k : K.map c.toMonoidHom, (f k : G) ∈ E₀ := by
    intro k
    have hkC : (f k : G) ∈ centralizer (E₀ : Set G) ⊓ L := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 ?_, (f k).2⟩
      rintro _ ⟨_, ⟨k', -, rfl⟩, rfl⟩
      exact hfcomm _ _
    rw [hE₀C] at hkC
    exact hkC
  have hTGsq : ∀ t ∈ TG, t ^ 2 = 1 := by
    intro t ht
    have htK : c t ∈ K.map c.toMonoidHom := ⟨t, mem_sup_right ht, rfl⟩
    have h1 := hfE ⟨c t, htK⟩
    have h2 : (f ⟨c t, htK⟩ : G) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_self_of_isElementaryAbelian hE₀e h1
    have h3 : f (⟨c t, htK⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by rw [SubgroupClass.coe_pow, h2, OneMemClass.coe_one])
    have h4 : c (t ^ 2) ∈ TG := by
      have h4' := (projL_eq_one_iff hTC hinf (inclusion hKc (⟨c t, htK⟩ ^ 2))).1 h3
      rw [Subgroup.coe_inclusion, SubgroupClass.coe_pow] at h4'
      rw [map_pow]
      exact h4'
    have h5 : t ^ 2 ∈ TG ⊓ TG.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨TG.pow_mem ht 2, ⟨c (t ^ 2), h4, ?_⟩⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc, MulAut.conj_apply]
      group
    rwa [inf_map_conj_eq_bot huniq hTG2 hgne, mem_bot] at h5
  refine le_antisymm (fun t ht => ?_) hzTG
  by_cases h1 : t = 1
  · rw [h1]
    exact one_mem _
  · rw [huniq t ht (orderOf_eq_prime (hTGsq t ht) h1)]
    exact mem_zpowers z

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
