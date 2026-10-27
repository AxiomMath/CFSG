module

public import CFSG.CGT.Stroth77.Section1NonSplitW4
public import CFSG.CGT.Stroth77.Section1NonSplitLemmas
public import CFSG.CGT.Stroth77.Section1SplitIso
public import CFSG.CGT.Stroth77.Section1Structure
public import CFSG.Holt.H78.Prelim
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools

public section

namespace CFSG.CGT.Stroth77

open Subgroup GL5
open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)
open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator

attribute [local instance] trSAspCommGroup

theorem pResidual_two_eq_top_stroth15 {G : Type*} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : CFSG.Quasithin.pResidual 2 G = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h2 : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := hp x
      rw [h, mem_bot] at hk
      exact ⟨k, hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nontrivial (center G) := h2.center_nontrivial
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz] at hc
      obtain ⟨x, y, hxy⟩ := hc
      exact hxy (Subsingleton.elim x y)
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (mem_center_iff.mp (hz ▸ mem_top a : a ∈ center G) b).symm
  · rw [h]

theorem spPhi_sixteen : spPhi 16 = spW := by decide

theorem stroth15_of_stroth10
    {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G) {E : Subgroup G} (hE : IsE 4 ↥E)
    {N : Subgroup G} (hNE : N = Subgroup.normalizer (E : Set G))
    (θ : (↥N ⧸ CFSG.oddCore ↥N) →* Equiv.Perm (Fin 6)) (hθ : Function.Surjective θ)
    (hθker : θ.ker = (E.subgroupOf N).map (QuotientGroup.mk' (CFSG.oddCore ↥N)))
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hψ : ∀ g (v : Multiplicative (altHeart 6)), g * (ψ v : _) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : _))
    {K : Subgroup (↥N ⧸ CFSG.oddCore ↥N)} (h1 : θ.ker ⊓ K = ⊥) (h2 : θ.ker ⊔ K = ⊤) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (CFSG.oddCore ↥N)) := odd_natCard_oddCore_stroth ↥N
  obtain ⟨e, -, he2⟩ := exists_mulEquiv_Msp_of_compl θ hθ ψ hψ h1 h2
  obtain ⟨T, hT⟩ := Tsp_isSylow
  obtain ⟨l, hl, hπl, P, hP⟩ := exists_lift_of_sylow e T
  set lT : ↥Tsp →* ↥N := l.comp (MulEquiv.subgroupCongr hT.symm).toMonoidHom with hlTdef
  have hlTinj : Function.Injective lT := hl.comp (MulEquiv.subgroupCongr hT.symm).injective
  have hπlT : ∀ m : ↥Tsp, (QuotientGroup.mk' (CFSG.oddCore ↥N)) (lT m) = e m := fun m => hπl _
  have hlTrange : lT.range = (P : Subgroup ↥N) := by
    rw [hP, hlTdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (MulEquiv.subgroupCongr hT.symm).surjective, ← MonoidHom.range_eq_map]
  set ι : ↥Tsp →* G := N.subtype.comp lT with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp hlTinj
  have hιN : ∀ {m : Msp} (hm : m ∈ Tsp), ιe ι m ∈ N := fun hm => by
    rw [ιe_apply hm]; exact (lT ⟨_, hm⟩).2
  have hιlT : ∀ {m : Msp} (hm : m ∈ Tsp), (⟨ιe ι m, hιN hm⟩ : ↥N) = lT ⟨m, hm⟩ := fun hm =>
    Subtype.ext (show ιe ι _ = ((lT ⟨_, hm⟩ : ↥N) : G) by rw [ιe_apply hm]; rfl)
  have hπι : ∀ {m : Msp} (hm : m ∈ Tsp),
      (QuotientGroup.mk' (CFSG.oddCore ↥N)) ⟨ιe ι m, hιN hm⟩ = e m := fun hm => by
    rw [hιlT hm, hπlT]
  have hrangeN : ∀ {g : G}, g ∈ ι.range → g ∈ N := by
    rintro _ ⟨m, rfl⟩; exact (lT m).2
  have hπinj : ∀ {x y : ↥N}, x ∈ lT.range → y ∈ lT.range →
      (QuotientGroup.mk' (CFSG.oddCore ↥N)) x = (QuotientGroup.mk' (CFSG.oddCore ↥N)) y →
        x = y := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩ h
    rw [hπlT, hπlT] at h
    exact congrArg lT (Subtype.ext (e.injective h))
  have hker_e : ∀ m : Msp, e m ∈ θ.ker ↔ m ∈ Qsp := by
    intro m
    rw [MonoidHom.mem_ker, he2, mem_Qsp]
    rfl
  have hEN : E ≤ N := hNE ▸ Subgroup.le_normalizer
  have hEp : IsPGroup 2 (E.subgroupOf N) :=
    (isPGroup_of_isE hE).comap_of_injective N.subtype Subtype.val_injective
  have hEnorm : (E.subgroupOf N).Normal := by subst hNE; exact Subgroup.normal_in_normalizer
  have hEP : E.subgroupOf N ≤ lT.range := by
    rw [hlTrange]; exact hEp.le_sylow_of_normal P
  have hEeq : E = trS ι Esp := by
    ext x
    constructor
    · intro hx
      have hxN : (⟨x, hEN hx⟩ : ↥N) ∈ E.subgroupOf N := mem_subgroupOf.2 hx
      obtain ⟨m, hm⟩ := hEP hxN
      have hmQ : (m : Msp) ∈ Qsp := by
        rw [← hker_e, ← hπlT, hm, hθker]
        exact ⟨_, hxN, rfl⟩
      refine mem_trS.2 ⟨m, Esp_eq_Qsp ▸ hmQ, m.2, ?_⟩
      rw [ιe_apply m.2]
      exact congrArg Subtype.val hm
    · intro hx
      obtain ⟨m, hmE, hmT, rfl⟩ := mem_trS.1 hx
      have hem : e m ∈ θ.ker := (hker_e m).2 (Esp_eq_Qsp ▸ hmE)
      rw [hθker] at hem
      obtain ⟨y, hyE, hy⟩ := hem
      have := hπinj (hEP hyE) ⟨⟨m, hmT⟩, rfl⟩ (by rw [hy, hπlT])
      have hyx : (y : G) = ιe ι m := by rw [this, ιe_apply hmT]; rfl
      rw [← hyx]
      exact mem_subgroupOf.1 hyE
  have hTp : IsPGroup 2 ↥Tsp := hT ▸ T.2
  have hSp : IsPGroup 2 ι.range := hTp.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have hcardN : Nat.card N = 2 ^ 8 * (45 * Nat.card (CFSG.oddCore ↥N)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥N),
      ← Nat.card_congr e.toEquiv,
      card_Msp]
    ring
  have hm45 : ¬ 2 ∣ 45 * Nat.card (CFSG.oddCore ↥N) := by
    rw [Nat.two_dvd_ne_zero]
    exact Nat.odd_iff.mp (Odd.mul (by decide) hOodd)
  have hrange_le : ι.range ≤ N := fun _ hg => hrangeN hg
  have hS : ∃ Q : Sylow 2 G, (Q : Subgroup G) = ι.range := by
    refine CFSG.EvenSmallLie.OmegaEight.Child8.exists_sylow_eq_of_normalizer_le hSp
      (fun Q hQ hle hQN => CFSG.EvenSmallLie.OmegaEight.Child8.eq_of_card_of_le
        (by rw [card_range hι]; norm_num) hcardN hm45 hQ hle hQN) ?_
    intro g hg
    have hgA := normalizer_range_le_normalizer_trS_Asp hι hg
    have hgAE := mem_normalizer_trS_AEsp hι hg
    have := mem_normalizer_trS_Esp hι hgA hgAE
    rw [← hEeq] at this
    rw [hNE]; exact this
  obtain ⟨Q, hQ⟩ := hS
  have hAN : trS ι Asp ≤ N := (trS_le_range (ι := ι) Asp).trans hrange_le
  have hρ : ∃ gρ : normalizer (trS ι Asp : Set G), code (basisA ι) (Mconj gρ) = rhoC := by
    set AN := (trS ι Asp).subgroupOf N with hANdef
    have hAN2 : IsPGroup 2 AN :=
      (hSp.to_le (trS_le_range (ι := ι) Asp)).comap_of_injective N.subtype
      Subtype.val_injective
    have hFr := CFSG.Holt.H78.map_normalizer_eq_of_odd (CFSG.oddCore ↥N) hOodd hAN2
    have hmapA : ∀ y, y ∈ AN.map (QuotientGroup.mk' (CFSG.oddCore ↥N)) ↔
        ∃ m, m ∈ Asp ∧ e m = y := by
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨m, hmA, hmT, hm⟩ := mem_trS.1 (mem_subgroupOf.1 hx)
        refine ⟨m, hmA, ?_⟩
        rw [← hπι hmT]
        exact congrArg (QuotientGroup.mk' (CFSG.oddCore ↥N)) (Subtype.ext hm)
      · rintro ⟨m, hmA, rfl⟩
        exact ⟨⟨ιe ι m, hιN (Asp_le_Tsp hmA)⟩,
          mem_subgroupOf.2 (ιe_mem_trS hmA (Asp_le_Tsp hmA)), hπι (Asp_le_Tsp hmA)⟩
    have hρbar : e spRho ∈ normalizer ((AN.map (QuotientGroup.mk' (CFSG.oddCore ↥N)) :
        Subgroup (↥N ⧸ CFSG.oddCore ↥N)) : Set (↥N ⧸ CFSG.oddCore ↥N)) := by
      refine mem_normalizer_fintype fun y hy => ?_
      obtain ⟨m, hmA, rfl⟩ := (hmapA y).1 hy
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (hmapA _).2 ⟨_, (mem_normalizer_iff.1 spRho_mem_normalizer_Asp m).1 hmA, rfl⟩
    rw [← hFr] at hρbar
    obtain ⟨n, hnN, hn⟩ := hρbar
    have hnG : (n : G) ∈ normalizer (trS ι Asp : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      have hn' := mem_normalizer_iff.1 hnN
      constructor
      · intro hx
        have := (hn' ⟨x, hAN hx⟩).1 (mem_subgroupOf.2 hx)
        exact mem_subgroupOf.1 this
      · intro hx
        have hxN : x ∈ N := by
          have h1 := hAN hx
          have : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n := by group
          rw [this]
          exact mul_mem (mul_mem (inv_mem n.2) h1) n.2
        have := (hn' ⟨x, hxN⟩).2 (mem_subgroupOf.2 hx)
        exact mem_subgroupOf.1 this
    have key : ∀ {b : Msp} (hb : b ∈ Asp) {r : Nat}, spRho * b * spRho⁻¹ = spPhi r →
        (n : G) * ιe ι b * (n : G)⁻¹ = ιe ι (spPhi r) := by
      intro b hb r hr
      have hbT : b ∈ Tsp := Asp_le_Tsp hb
      have hx : (n : G) * ιe ι b * (n : G)⁻¹ ∈ trS ι Asp :=
        (mem_normalizer_iff.1 hnG _).1 (ιe_mem_trS hb hbT)
      obtain ⟨m, -, hmT, hm⟩ := mem_trS.1 hx
      have hxr : n * ⟨ιe ι b, hιN hbT⟩ * n⁻¹ ∈ lT.range :=
        ⟨⟨m, hmT⟩, Subtype.ext (show ((lT ⟨m, hmT⟩ : ↥N) : G) = (n : G) * ιe ι b * (n : G)⁻¹ by
          rw [← hm, ιe_apply hmT]; rfl)⟩
      have hyr : (⟨ιe ι (spPhi r), hιN (spPhi_mem_Tsp r)⟩ : ↥N) ∈ lT.range :=
        ⟨⟨_, spPhi_mem_Tsp r⟩, (hιlT (spPhi_mem_Tsp r)).symm⟩
      have hπeq : QuotientGroup.mk' (CFSG.oddCore ↥N) (n * ⟨ιe ι b, hιN hbT⟩ * n⁻¹) =
          QuotientGroup.mk' (CFSG.oddCore ↥N) ⟨ιe ι (spPhi r), hιN (spPhi_mem_Tsp r)⟩ := by
        rw [map_mul, map_mul, map_inv, hn, hπι hbT, hπι (spPhi_mem_Tsp r), ← map_inv, ← map_mul,
          ← map_mul, hr]
      exact congrArg Subtype.val (hπinj hxr hyr hπeq)
    obtain ⟨h0, h1, h2, h3, h4⟩ := act_spRho
    exact ⟨⟨n, hnG⟩, code_Mconj_eq hι _ (by decide) (key spX1_mem_Asp h0) (key spY1_mem_Asp h1)
      (key spX_mem_Asp h2) (key spY_mem_Asp h3) (key spW_mem_Asp h4)⟩
  set w := ιe ι spW with hw
  have hwA : w ∈ trS ι Asp := ιe_mem_trS spW_mem_Asp spW_mem_Tsp
  have hw2 : orderOf w = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact trS_Asp_sq hwA) ?_
    intro h1
    have := ιe_injective hι spW_mem_Tsp (one_mem _) (h1.trans ιe_one.symm)
    exact absurd this (by decide)
  set S1 := trS ι S1sp with hS1
  have hS1S : S1 ≤ (Q : Subgroup G) := hQ ▸ trS_le_range _
  have hS1card : Nat.card S1 = 128 := (card_trS hι S1sp_le_Tsp).trans card_S1sp
  have hindex : S1.relIndex (Q : Subgroup G) = 2 := by
    have h := relIndex_mul_card (H := S1) (K := (Q : Subgroup G))
    rw [inf_of_le_left hS1S, hS1card] at h
    have hQc : Nat.card (Q : Subgroup G) = 256 := by rw [hQ]; exact card_range hι
    omega
  have hQu : ∀ x : G, x⁻¹ * w * x ∉ S1 := by
    intro x hx
    obtain ⟨z, hzS1, hzT, hz⟩ := mem_trS.1 hx
    have hz2 : z * z = 1 := by
      refine ιe_injective hι (mul_mem hzT hzT) (one_mem _) ?_
      rw [ιe_mul hzT hzT, hz, ιe_one]
      calc x⁻¹ * w * x * (x⁻¹ * w * x) = x⁻¹ * (w * w) * x := by group
        _ = 1 := by rw [trS_Asp_sq hwA]; group
    obtain ⟨m, r, hr, hmz⟩ := exists_conj_mem_spW4 hzS1 hz2
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥N) (e m)
    set zN : ↥N := ⟨ιe ι z, hιN hzT⟩ with hzN
    set aN : ↥N := ⟨ιe ι (spPhi r), hιN (spPhi_mem_Tsp r)⟩ with haN
    have hπ1 : (QuotientGroup.mk' (CFSG.oddCore ↥N)) (h * zN * h⁻¹) =
        (QuotientGroup.mk' (CFSG.oddCore ↥N)) aN := by
      rw [map_mul, map_mul, map_inv]
      change QuotientGroup.mk' (CFSG.oddCore ↥N) h * (QuotientGroup.mk' (CFSG.oddCore ↥N)) zN *
        (QuotientGroup.mk' (CFSG.oddCore ↥N) h)⁻¹ = (QuotientGroup.mk' (CFSG.oddCore ↥N)) aN
      rw [hh, hzN, haN, hπι hzT, hπι (spPhi_mem_Tsp r), ← map_inv, ← map_mul, ← map_mul, hmz]
    have hi : h * zN * h⁻¹ * (h * zN * h⁻¹) = 1 := by
      have : zN * zN = 1 := Subtype.ext (by
        simp only [hzN, Subgroup.coe_mul, Subgroup.coe_one]
        rw [← ιe_mul hzT hzT, hz2, ιe_one])
      calc h * zN * h⁻¹ * (h * zN * h⁻¹) = h * (zN * zN) * h⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hj : aN * aN = 1 := Subtype.ext (trS_Asp_sq
      (ιe_mem_trS (spPhi_mem_Asp r) (spPhi_mem_Tsp r)))
    have hij : (h * zN * h⁻¹)⁻¹ * aN ∈ (CFSG.oddCore ↥N) := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (CFSG.oddCore ↥N)) ((h * zN * h⁻¹)⁻¹ * aN) = 1
      rw [map_mul, map_inv, hπ1, inv_mul_cancel]
    obtain ⟨c, hcO, hc⟩ := exists_conj_eq_of_involutions hOodd hi hj hij
    set a := ιe ι (spPhi r) with ha
    have haA : a ∈ trS ι Asp := ιe_mem_trS (spPhi_mem_Asp r) (spPhi_mem_Tsp r)
    have hka : a = (x * (h : G)⁻¹ * c)⁻¹ * w * (x * (h : G)⁻¹ * c) := by
      have := congrArg Subtype.val hc
      simp only [haN, hzN, Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [ha, this, hz]
      group
    obtain ⟨n, hn, hnw⟩ := exists_normalizer_conj_of_unique Q (hQ ▸ trS_le_range (ι := ι) Asp)
      (fun x hx y hy => trS_Asp_comm hx hy)
      (fun B => (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ Nat.card B = 32)
      ⟨fun x hx y hy => trS_Asp_comm hx hy, card_trS_Asp hι⟩
      (fun B g hB => ⟨by
        rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        rw [← map_mul, ← map_mul, hB.1 u hu v hv], by
        rw [card_map_of_injective (MulAut.conj g).injective]; exact hB.2⟩)
      (fun B hB hPr => eq_trS_Asp hι B (hQ ▸ hB) hPr.1 hPr.2)
      hwA haA hka
    obtain ⟨r', hr', hr'eq⟩ := exists_conj_spPhi hι ⟨Q, hQ⟩ hρ ⟨n, hn⟩ hr
    have hw' : w = ιe ι (spPhi r') := by
      rw [← hr'eq]
      change w = n * a * n⁻¹
      rw [hnw]; group
    have h16 : Φ (basisA ι) 16 = Φ (basisA ι) r' := Subtype.ext (by
      rw [coe_Φ_basisA, coe_Φ_basisA, spPhi_sixteen, ← hw'])
    have := Φ_inj (sq_trS_Asp ι) (closure_basisA ι) (card_trS_Asp hι) (by decide)
      (by omega) h16
    omega
  have hres := CFSG.Quasithin.thompson_transfer_lemma Q hS1S hindex hw2 hQu
  apply hres
  rw [pResidual_two_eq_top_stroth15 hG ⟨ιe ι spUV, ιe ι spX, fun h => by
    have := ιe_injective hι (mul_mem spUV_mem_Tsp spX_mem_Tsp) (mul_mem spX_mem_Tsp spUV_mem_Tsp)
      (by rw [ιe_mul spUV_mem_Tsp spX_mem_Tsp, ιe_mul spX_mem_Tsp spUV_mem_Tsp, h])
    exact absurd this (by decide)⟩]
  exact mem_top _

theorem stroth15
    {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G) {E : Subgroup G}
    (hE : IsE 4 ↥E)
    (φ : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : φ.ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)))
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E) :
    ¬ ∃ K : Subgroup (↥(Subgroup.normalizer (E : Set G)) ⧸
      CFSG.oddCore ↥(Subgroup.normalizer (E : Set G))),
      (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) ⊓ K = ⊥ ∧
      (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) ⊔ K = ⊤ := by
  rintro ⟨K, h1, h2⟩
  obtain ⟨-, θ, hθ, hθker, ψ, hψ⟩ := stroth10_holds hE φ hφ hker hsyl
  rw [← hθker] at h1 h2
  exact stroth15_of_stroth10 hG hE rfl θ hθ hθker ψ hψ h1 h2

end CFSG.CGT.Stroth77
