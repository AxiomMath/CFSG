module

public import CFSG.LocalAnalysis.GH72.Sec6
public import CFSG.LocalAnalysis.GH72.Sec4Conj
public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.Sec4C
public import CFSG.LocalAnalysis.GH72.MaxInvariant
public import CFSG.LocalAnalysis.GH72.Sec4A

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem centralizer_mk_le_bar_C {K : Subgroup G} {t : G} (htK : t ∈ K) (ht : t * t = 1) :
    centralizer ({QuotientGroup.mk' (CFSG.oddCore K) ⟨t, htK⟩} : Set (Bar K)) ≤
      bar K (K ⊓ C t) := by
  intro u hu
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore K) u
  rw [mem_centralizer_singleton_iff] at hu
  set τ : K := ⟨t, htK⟩
  have hq : QuotientGroup.mk' (CFSG.oddCore K) (k⁻¹ * (τ * k * τ⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hu]
    group
  have hq' : k⁻¹ * (τ * k * τ⁻¹) ∈ CFSG.oddCore K := by
    rw [← QuotientGroup.ker_mk' (CFSG.oddCore K), MonoidHom.mem_ker]
    exact hq
  have hmem : (k : G)⁻¹ * (t * k * t⁻¹) ∈ O K := ⟨_, hq', rfl⟩
  obtain ⟨o, ho, hfix⟩ := exists_fixed_mem_coset (card_O_odd K) ht (le_normalizer_O K htK) hmem
  obtain ⟨o', ho', hoo⟩ := ho
  have hoo' : (o' : G) = o := hoo
  refine ⟨k * o', ?_, ?_⟩
  · show k * o' ∈ (K ⊓ C t).subgroupOf K
    rw [mem_subgroupOf, coe_mul, hoo']
    refine mem_inf.mpr ⟨K.mul_mem k.2 (hoo' ▸ o'.2), mem_centralizer_singleton_iff.mpr ?_⟩
    calc (k : G) * o * t = t * (k * o) * t⁻¹ * t := by rw [hfix]
      _ = t * (k * o) := by group
  · have h1 : QuotientGroup.mk' (CFSG.oddCore K) o' = 1 := (QuotientGroup.eq_one_iff _).mpr ho'
    rw [map_mul, h1, mul_one]

theorem O_inf_C_le_O_of_isIsolatedIn {K : Subgroup G} {t : G} (ht : IsIsolatedIn K t) :
    O (K ⊓ C t) ≤ O K := by
  have hOK : O (K ⊓ C t) ≤ K := (G4c.O_le _).trans inf_le_left
  have hodd : Odd (Nat.card (O K ⊔ O (K ⊓ C t) : Subgroup G)) :=
    G4c.odd_card_sup (card_O_odd K) (card_O_odd _) (hOK.trans (le_normalizer_O K))
  have hnorm : K ≤ normalizer ((O K ⊔ O (K ⊓ C t) : Subgroup G) : Set G) := by
    intro k hk
    obtain ⟨c, hc, hck⟩ := ht.exists_mem_C hk
    have h1 : c ∈ normalizer ((O K ⊔ O (K ⊓ C t) : Subgroup G) : Set G) :=
      mem_normalizer_sup_of (le_normalizer_O K (mem_inf.mp hc).1) (le_normalizer_O _ hc)
    have h2 : c⁻¹ * k ∈ normalizer ((O K ⊔ O (K ⊓ C t) : Subgroup G) : Set G) :=
      le_normalizer (mem_sup_left hck)
    have h3 := mul_mem h1 h2
    rwa [mul_inv_cancel_left] at h3
  exact le_sup_right.trans (G4c.le_O_of_le_normalizer (sup_le (G4c.O_le K) hOK) hnorm hodd)

theorem O_le_O_of_O2_le {H J : Subgroup G} (h₁ : O2 H ≤ J) (h₂ : J ≤ H) : O J ≤ O H := by
  have hJ2 : O J ≤ O2 H := G4c.le_O2_of_odd ((G4c.O_le J).trans h₂) (card_O_odd J)
  have hO2 : O J ≤ O (O2 H) :=
    G4c.le_O_of_le_normalizer hJ2 (h₁.trans (le_normalizer_O J)) (card_O_odd J)
  exact hO2.trans (G4c.O_le_O (G4c.O2_le H) (G4c.le_normalizer_O2 H))

omit [Finite G] in
theorem exists_isSylowOf_two_ge {K Q : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ R : Subgroup G, IsSylowOf 2 R K ∧ Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun q hq =>
    ⟨⟨q, hQK hq⟩, hP (show (⟨q, hQK hq⟩ : K) ∈ Q.comap K.subtype from hq), rfl⟩⟩

theorem odd_index_of_isSylowOf_top_le {X : Type} [Group X] [Finite X] {P L : Subgroup X}
    (hP : IsSylowOf 2 P ⊤) (hPL : P ≤ L) : Odd L.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : ¬ 2 ∣ P.index := by
    have h := (isSylowOf_iff.mp hP).2.2
    rwa [relIndex_top_right] at h
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => hdvd (h2.trans (index_dvd_of_le hPL)))

theorem le_O_of_le_O_C_of_normal {K E : Subgroup G} {L₁ L₂ : Subgroup (Bar K)}
    (hL₁ : L₁.Normal) (hL₂ : L₂.Normal) (hL₁₂ : L₂ ≤ centralizer (L₁ : Set (Bar K)))
    (hO₁ : CFSG.oddCore L₁ = ⊥) (hO₂ : CFSG.oddCore L₂ = ⊥) (hidx : Odd (L₁ ⊔ L₂).index)
    {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hx : x * x = 1) (hy : y * y = 1)
    (hxL : QuotientGroup.mk' (CFSG.oddCore K) ⟨x, hxK⟩ ∈ L₁)
    (hyL : QuotientGroup.mk' (CFSG.oddCore K) ⟨y, hyK⟩ ∈ L₂)
    (hEK : E ≤ K) (hE : Odd (Nat.card E)) (hEx : E ≤ O (C x)) (hEy : E ≤ O (C y)) :
    E ≤ O K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {z : G} (hzK : z ∈ K), z * z = 1 → ∀ {L' : Subgroup (Bar K)}, L'.Normal →
      CFSG.oddCore L' = ⊥ →
      L' ≤ centralizer ({QuotientGroup.mk' (CFSG.oddCore K) ⟨z, hzK⟩} : Set (Bar K)) →
      bar K (O (K ⊓ C z)) ≤ centralizer (L' : Set (Bar K)) := by
    intro z hzK hz L' hL' hO hL'z
    refine le_centralizer_of_odd_of_le_normalizer hO ?_ ?_ (G4c.odd_card_bar (card_O_odd _))
    · rw [normalizer_eq_top_iff.mpr hL']
      exact le_top
    · exact hL'z.trans ((centralizer_mk_le_bar_C hzK hz).trans
        (G4c.bar_le_normalizer (le_normalizer_O _)))
  have hE' : ∀ {z : G}, E ≤ O (C z) → bar K E ≤ bar K (O (K ⊓ C z)) := fun hEz =>
    G4c.bar_mono ((le_inf hEz (le_inf hEK (hEz.trans (G4c.O_le _)))).trans
      (O_inf_le_O_of_le inf_le_right))
  have h₂ : bar K E ≤ centralizer (L₂ : Set (Bar K)) :=
    (hE' hEx).trans (key hxK hx hL₂ hO₂ fun l hl => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hL₁₂ hl) _ hxL).symm)
  have h₁ : bar K E ≤ centralizer (L₁ : Set (Bar K)) :=
    (hE' hEy).trans (key hyK hy hL₁ hO₁ fun l hl => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hL₁₂ hyL) l hl))
  have hEc : bar K E ≤ centralizer ((L₁ ⊔ L₂ : Subgroup (Bar K)) : Set (Bar K)) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp h₁) (le_centralizer_iff.mp h₂))
  have := hL₁
  have := hL₂
  have hT : IsPGroup 2 (centralizer ((L₁ ⊔ L₂ : Subgroup (Bar K)) : Set (Bar K))) := by
    refine G4c.isPGroup_of_forall_le_centralizer (G4c.oddCore_bar_eq_bot K) normal_centralizer
      fun Q _ hQ => centralizer_le ?_
    exact CFSG.pSubgroup_le_of_not_dvd_index Nat.prime_two inferInstance hidx.not_two_dvd_nat hQ
  have h := G4c.inf_eq_bot_of_odd_of_isPGroup (G4c.odd_card_bar (H := K) hE) hT
  rw [inf_eq_left.mpr hEc] at h
  exact (G4c.bar_eq_bot_iff hEK).mp h

end Generic

section Fusion

variable {G : Type*} [Group G]

theorem HasProductFusion.map_mulEquiv {S₁ S₂ : Subgroup G} (h : HasProductFusion S₁ S₂)
    (φ : G ≃* G) : HasProductFusion (S₁.map φ.toMonoidHom) (S₂.map φ.toMonoidHom) := by
  have hsup : S₁.map φ.toMonoidHom ⊔ S₂.map φ.toMonoidHom = (S₁ ⊔ S₂).map φ.toMonoidHom :=
    (Subgroup.map_sup _ _ _).symm
  have hc : ∀ {x y : G}, IsConj (φ.symm x) (φ.symm y) → IsConj x y := fun hxy => by
    simpa using φ.toMonoidHom.map_isConj hxy
  have hc' : ∀ {x y : G}, IsConj x y → IsConj (φ.symm x) (φ.symm y) := fun hxy =>
    φ.symm.toMonoidHom.map_isConj hxy
  have ho : ∀ x : G, orderOf (φ.symm x) = orderOf x := fun x => MulEquiv.orderOf_eq φ.symm x
  refine ⟨fun x hx y hy hx2 hy2 => ?_, fun x hx y hy hx2 hy2 => ?_,
    fun x hx y hy hx₁ hx₂ hy₁ hy₂ hx2 hy2 => ?_, fun x hx y hy hx2 hxy => ?_⟩
  · rw [mem_map_equiv] at hx hy
    exact hc (h.conj₁ _ hx _ hy (by rwa [ho]) (by rwa [ho]))
  · rw [mem_map_equiv] at hx hy
    exact hc (h.conj₂ _ hx _ hy (by rwa [ho]) (by rwa [ho]))
  · rw [hsup, mem_map_equiv] at hx hy
    rw [mem_map_equiv] at hx₁ hx₂ hy₁ hy₂
    exact hc (h.conj₃ _ hx _ hy hx₁ hx₂ hy₁ hy₂ (by rwa [ho]) (by rwa [ho]))
  · rw [hsup, mem_map_equiv] at hx hy
    simpa only [mem_map_equiv] using h.separate _ hx _ hy (by rwa [ho]) (hc' hxy)

end Fusion

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

omit [Finite G] in
private theorem coe_smul_sylow (g : G) (P : Sylow 2 G) :
    ((g • P : Sylow 2 G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rfl

theorem exists_setting_conj (g : G) : ∃ 𝔗 : Sec4Setting G,
    (𝔗.S : Subgroup G) = (𝔖.S : Subgroup G).map (MulAut.conj g).toMonoidHom ∧
    𝔗.S₁ = 𝔖.S₁.map (MulAut.conj g).toMonoidHom ∧
    𝔗.S₂ = 𝔖.S₂.map (MulAut.conj g).toMonoidHom := by
  have hd : DDDecomp ((g • 𝔖.S : Sylow 2 G) : Subgroup G)
      (𝔖.S₁.map (MulAut.conj g).toMonoidHom) (𝔖.S₂.map (MulAut.conj g).toMonoidHom) := by
    rw [coe_smul_sylow]
    exact 𝔖.decomp.map_conj g
  have hz : ∀ {z : G} {T : Subgroup G}, z ∈ T ∧ orderOf z = 2 ∧ T ≤ C z →
      g * z * g⁻¹ ∈ T.map (MulAut.conj g).toMonoidHom ∧ orderOf (g * z * g⁻¹) = 2 ∧
        T.map (MulAut.conj g).toMonoidHom ≤ C (g * z * g⁻¹) := by
    rintro z T ⟨hzT, hz2, hTz⟩
    refine ⟨⟨z, hzT, rfl⟩, by rw [orderOf_conj_eq]; exact hz2, ?_⟩
    rw [← G4c.map_cj_C]
    exact map_mono hTz
  exact ⟨⟨⟨g • 𝔖.S, _, _, hd, 𝔖.noIndexTwo⟩, 𝔖.mc, 𝔖.fusion.map_mulEquiv (MulAut.conj g), _, _,
    hz 𝔖.hz₁, hz 𝔖.hz₂⟩, coe_smul_sylow g 𝔖.S, rfl, rfl⟩

variable {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem exists_setting_isSylowOf {H : Subgroup G} (hAH : A ≤ H) : ∃ 𝔗 : Sec4Setting G,
    A ≤ 𝔗.S ∧ IsSylowOf 2 ((𝔗.S : Subgroup G) ⊓ H) H ∧ 𝔗.X A = 𝔖.X A ∧ 𝔗.Y A = 𝔖.Y A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  obtain ⟨R, hR, hAR⟩ := exists_isSylowOf_two_ge hAH hA2
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow 𝔖.S hR.isPGroup
  obtain ⟨𝔗, hT, hT₁, hT₂⟩ := 𝔖.exists_setting_conj g⁻¹
  have hRT : R ≤ 𝔗.S := by
    rw [hT]
    exact G4c.map_cj_le_iff.mp hg
  have hAT : A ≤ 𝔗.S := hAR.trans hRT
  have hAT' : A ≤ (𝔖.S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom := hT ▸ hAT
  have hTH : (𝔗.S : Subgroup G) ⊓ H = R :=
    hR.eq_of_le (le_inf hRT hR.le) inf_le_right (𝔗.S.isPGroup'.to_le inf_le_left)
  obtain ⟨hX, hY⟩ := (𝔖.remark_4_6 hAS hA).1 g⁻¹ hAT'
  refine ⟨𝔗, hAT, hTH ▸ hR, ?_, ?_⟩
  · change A ⊓ 𝔗.S₁ = _
    rw [hT₁]
    exact hX
  · change A ⊓ 𝔗.S₂ = _
    rw [hT₂]
    exact hY

theorem xyGenerated_of_le_O
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) (hM : Covers H (𝔖.M₀ A) (O (𝔖.M A)))
    (hN : Covers H (𝔖.N₀ A) (O (𝔖.N A))) {D : Subgroup G} (hD : Odd (Nat.card D))
    (hAD : A ≤ normalizer (D : Set G)) (hDO : D ≤ O H) : XYGenerated (𝔖.X A) (𝔖.Y A) D := by
  have hXA : 𝔖.X A ≤ A := inf_le_left
  have hYA : 𝔖.Y A ≤ A := inf_le_left
  refine le_antisymm ?_ (iSup_le fun x => iSup_le fun _ => iSup_le fun _ => iSup_le fun y =>
    iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left)
  refine (le_iSup_inf_centralizer hD (𝔖.isKleinFour_X hAS hA) (hXA.trans hAD)).trans ?_
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
  have hYn : 𝔖.Y A ≤ normalizer ((D ⊓ C x : Subgroup G) : Set G) := fun y hy =>
    inf_normalizer_le_normalizer_inf ⟨hAD (hYA hy), le_normalizer
      (mem_centralizer_singleton_iff.mpr (hA.comm (hYA hy) (hXA hx)))⟩
  refine (le_iSup_inf_centralizer (G4c.odd_card_of_le inf_le_left hD) (𝔖.isKleinFour_Y hAS hA)
    hYn).trans ?_
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun hy1 => ?_
  refine le_trans ?_ (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 (le_iSup_of_le y
    (le_iSup_of_le hy (le_iSup_of_le hy1 le_rfl))))))
  have h₁ := (h413 H hH).1 hM x hx hx1 (hAH (hXA hx))
  have h₂ := (h413 H hH).2 hN y hy hy1 (hAH (hYA hy))
  have hDO' : D ⊓ C x ⊓ C y ≤ O H := inf_le_left.trans (inf_le_left.trans hDO)
  exact le_inf (le_inf (inf_le_left.trans inf_le_left)
    ((le_inf hDO' (inf_le_left.trans inf_le_right)).trans h₁)) ((le_inf hDO' inf_le_right).trans h₂)

theorem le_O_of_isIsolatedIn
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    {K : Subgroup G} (hAK : A ≤ K) {t : G} (ht : IsIsolatedIn K t) {E : Subgroup G}
    (hEK : E ≤ K) (hE : Odd (Nat.card E)) (hAE : A ≤ normalizer (E : Set G))
    {x y : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1)
    (hEx : E ≤ O (C x)) (hEy : E ≤ O (C y)) : E ≤ O K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  obtain ⟨R, hR, hAR⟩ := exists_isSylowOf_two_ge hAK hA2
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht.2.1, pow_one])
  obtain ⟨c, hcK, hcR⟩ := exists_mem_conj_mem_of_isSylowOf hR ht.1 ht2
  have ha : IsIsolatedIn K (c * t * c⁻¹) := by
    have h := ht.map_conj c
    rwa [G4c.map_cj_eq_of_mem_normalizer (le_normalizer hcK)] at h
  set a := c * t * c⁻¹ with ha_def
  have haA : a ∈ A := by
    have hcomm : a ∈ (R ⊓ centralizer (A : Set G) : Subgroup G) := by
      refine mem_inf.mpr ⟨hcR, mem_centralizer_iff.mpr fun b hb => ?_⟩
      have h1 : b * a * b⁻¹ * a⁻¹ ∈ O K := ha.conj_mul_inv_mem_O (hAK hb)
      have h2 : b * a * b⁻¹ * a⁻¹ ∈ R :=
        mul_mem (mul_mem (mul_mem (hAR hb) hcR) (inv_mem (hAR hb))) (inv_mem hcR)
      have h3 : b * a * b⁻¹ * a⁻¹ ∈ O K ⊓ R := mem_inf.mpr ⟨h1, h2⟩
      rw [G4c.inf_eq_bot_of_odd_of_isPGroup (card_O_odd K) hR.isPGroup, mem_bot] at h3
      calc b * a = b * a * b⁻¹ * a⁻¹ * (a * b) := by group
        _ = a * b := by rw [h3, one_mul]
    have hAc : A ≤ centralizer (A : Set G) := fun b hb =>
      mem_centralizer_iff.mpr fun b' hb' => hA.comm hb' hb
    have heq := (𝔖.decomp.isSylowOf_centralizer_e16 hAS hA).eq_of_le (le_inf hAR hAc)
      inf_le_right (hR.isPGroup.to_le inf_le_left)
    exact heq ▸ hcomm
  have ha1 : a ≠ 1 := fun h => by
    have h2 := ha.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hcomm : ⁅E, zpowers a⁆ ≤ O K := by
    rw [commutator_le]
    intro e he z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    rw [← zpow_mod_orderOf, ha.2.1, Nat.cast_two]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [h, zpow_zero, commutatorElement_one_right]
      exact one_mem _
    · rw [h, zpow_one, commutatorElement_def]
      exact ha.conj_mul_inv_mem_O (hEK he)
  have hCa : E ⊓ C a ≤ O (C a) := by
    by_cases haY : a ∈ 𝔖.Y A
    · have haX : a ∉ 𝔖.X A := fun haX => ha1 (by
        have h := mem_inf.mpr ⟨haX, haY⟩
        rwa [𝔖.X_inf_Y, mem_bot] at h)
      exact (inf_le_inf_right _ hEy).trans (h410.2 y hy hy1 a haA haX)
    · exact (inf_le_inf_right _ hEx).trans (h410.1 x hx hx1 a haA haY)
  have hCa' : E ⊓ C a ≤ O K :=
    ((le_inf hCa (inf_le_inf_right _ hEK)).trans (O_inf_le_O_of_le inf_le_right)).trans
      (O_inf_C_le_O_of_isIsolatedIn ha)
  exact (le_inf_centralizer_sup_commutator hE ha.2.1 (hAE haA)).trans (sup_le hCa' hcomm)

theorem inf_O_C_le_O
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h44 : ∀ 𝔗 : Sec4Setting G, ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S₁ ⊓ J) ⊔ (𝔗.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔗.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔗.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔗.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔗.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h44J : ∀ 𝔗 : Sec4Setting G, ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → A ≤ 𝔗.S → IsE16 A →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S : Subgroup G) ⊓ H) H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔗.S₂ ⊓ (O2 H ⊔ A))) (O2 H ⊔ A))
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) {D : Subgroup G} (hDH : D ≤ H)
    (hD : Odd (Nat.card D)) (hAD : A ≤ normalizer (D : Set G))
    {x y : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) :
    D ⊓ O (C x) ⊓ O (C y) ≤ O H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxA : x ∈ A := (inf_le_left : 𝔖.X A ≤ A) hx
  have hyA : y ∈ A := (inf_le_left : 𝔖.Y A ≤ A) hy
  set E := D ⊓ O (C x) ⊓ O (C y) with hE_def
  have hED : E ≤ D := inf_le_left.trans inf_le_left
  have hEodd : Odd (Nat.card E) := G4c.odd_card_of_le hED hD
  have hEx : E ≤ O (C x) := inf_le_left.trans inf_le_right
  have hEy : E ≤ O (C y) := inf_le_right
  have hAE : A ≤ normalizer (E : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf ⟨hAD ha,
      le_normalizer_O _ (mem_centralizer_singleton_iff.mpr (hA.comm ha hxA))⟩,
      le_normalizer_O _ (mem_centralizer_singleton_iff.mpr (hA.comm ha hyA))⟩
  by_cases hisoH : ∃ t, IsIsolatedIn H t
  · obtain ⟨t, ht⟩ := hisoH
    exact 𝔖.le_O_of_isIsolatedIn hAS hA h410 hAH ht (hED.trans hDH) hEodd hAE hx hx1 hy hy1
      hEx hEy
  push Not at hisoH
  obtain ⟨𝔗, hAT, hsyl, hTX, hTY⟩ := 𝔖.exists_setting_isSylowOf hAS hA hAH
  set J := O2 H ⊔ A with hJ
  have hJH : J ≤ H := sup_le (G4c.O2_le H) hAH
  have hJne : J ≠ ⊤ := fun h => hH (top_le_iff.mp (h ▸ hJH))
  have hAJ : A ≤ J := le_sup_right
  have hEJ : E ≤ J := (G4c.le_O2_of_odd (hED.trans hDH) hEodd).trans le_sup_left
  refine le_trans ?_ (O_le_O_of_O2_le le_sup_left hJH)
  by_cases hisoJ : ∃ t, IsIsolatedIn J t
  · obtain ⟨t, ht⟩ := hisoJ
    exact 𝔖.le_O_of_isIsolatedIn hAS hA h410 hAJ ht hEJ hEodd hAE hx hx1 hy hy1 hEx hEy
  push Not at hisoJ
  have hsylJ := h44J 𝔗 H hH hisoH A hAH hAT hA hsyl
  obtain ⟨L₁, L₂, -, -, -, hL₁₂, -, -, hL₁, hL₂, -, -, hS₁L, hS₂L, hn₁, hn₂⟩ :=
    h44 𝔗 J hJne hisoJ A hAJ hA J (sup_le (G4c.O2_le J) hAJ) le_rfl hsylJ
  have hbar : bar J J = ⊤ := bar_self
  rw [hbar] at hS₁L hS₂L hn₁ hn₂
  have hn₁' : L₁.Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp ((normal_subgroupOf_iff_le_normalizer le_top).mp hn₁))
  have hn₂' : L₂.Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp ((normal_subgroupOf_iff_le_normalizer le_top).mp hn₂))
  have hxT : x ∈ 𝔗.S₁ := by
    have h : x ∈ 𝔗.X A := by rw [hTX]; exact hx
    exact (mem_inf.mp h).2
  have hyT : y ∈ 𝔗.S₂ := by
    have h : y ∈ 𝔗.Y A := by rw [hTY]; exact hy
    exact (mem_inf.mp h).2
  have hxJ : x ∈ J := hAJ hxA
  have hyJ : y ∈ J := hAJ hyA
  have hxL : QuotientGroup.mk' (CFSG.oddCore J) ⟨x, hxJ⟩ ∈ L₁ :=
    hS₁L (mem_inf.mpr ⟨mk_mem_bar hxJ hxT, mem_top _⟩)
  have hyL : QuotientGroup.mk' (CFSG.oddCore J) ⟨y, hyJ⟩ ∈ L₂ :=
    hS₂L (mem_inf.mpr ⟨mk_mem_bar hyJ hyT, mem_top _⟩)
  have hidx : Odd (L₁ ⊔ L₂).index := by
    have hT := isSylowOf_bar (H := J) le_rfl hsylJ
    rw [hbar] at hT
    refine odd_index_of_isSylowOf_top_le hT ?_
    rw [bar_sup inf_le_right inf_le_right]
    exact sup_le_sup ((le_inf (bar_mono inf_le_left) le_top).trans hS₁L)
      ((le_inf (bar_mono inf_le_left) le_top).trans hS₂L)
  exact le_O_of_le_O_C_of_normal hn₁' hn₂' hL₁₂ (oddCore_eq_bot_of_isL2PGL2OrA7OrV4 hL₁)
    (oddCore_eq_bot_of_isL2PGL2OrA7OrV4 hL₂) hidx hxJ hyJ (hA.mul_self hxA) (hA.mul_self hyA)
    hxL hyL hEJ hEodd hEx hEy

theorem lemma_4_14_of
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (h44 : ∀ 𝔗 : Sec4Setting G, ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S₁ ⊓ J) ⊔ (𝔗.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔗.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔗.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔗.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔗.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h44J : ∀ 𝔗 : Sec4Setting G, ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → A ≤ 𝔗.S → IsE16 A →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S : Subgroup G) ⊓ H) H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔗.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔗.S₂ ⊓ (O2 H ⊔ A))) (O2 H ⊔ A))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hM : Covers H (𝔖.M₀ A) (O (𝔖.M A))) (hN : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    (D : Subgroup G) (hDH : D ≤ H) (hD : Odd (Nat.card D)) (hAD : A ≤ normalizer (D : Set G)) :
    XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H :=
  ⟨fun hgen => hgen.le.trans (iSup_le fun _ => iSup_le fun hx => iSup_le fun hx1 =>
      iSup_le fun _ => iSup_le fun hy => iSup_le fun hy1 =>
        𝔖.inf_O_C_le_O hAS hA h410 h44 h44J hH hAH hDH hD hAD hx hx1 hy hy1),
    𝔖.xyGenerated_of_le_O hAS hA h413 hH hAH hM hN hD hAD⟩

end Sec4Setting

end CFSG.GH72
