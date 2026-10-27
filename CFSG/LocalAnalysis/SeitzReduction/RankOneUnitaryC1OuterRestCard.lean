module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem U3C1OuterStepHyp.outerRest_transitive {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G} {V : Subgroup G}
    {k : ℕ} (H : U3C1OuterStepHyp G L f t T R₂ D d V k) (hk : 2 ≤ k) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G),
      outerRestPt t k y = b := by
  have hc := H.conf
  have h := H.start
  have hS2 := H.card_sylow
  obtain ⟨y₀, hy₀, r₀, hr₀, hr₀sq, hy₀t⟩ := H.move
  have hdD := H.cartan.mem
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d (H.cartan.le hdD)
  have hdY : d ∈ normalizer (szR (szT₁ L T) V t : Set G) :=
    mem_normalizer_szR_of (H.cartan.le_normalizer hdD) (hc.D_le hdD) hdt
  have hpt₀ : outerRestPt t k y₀ = r₀ ^ 2 ^ k := by
    rw [outerRestPt_def, hy₀t, mul_inv_cancel_right]
  have hne : outerRestPt t k y₀ ≠ 1 := by
    rw [hpt₀]
    intro h1
    obtain ⟨s, hs, hs2⟩ := hc.outerRest_exists_sq h hS2 hr₀ h1
    exact hr₀sq s hs hs2
  intro b hb
  by_cases hb1 : b = 1
  · exact ⟨1, one_mem _, by rw [hb1, outerRestPt_def]; group⟩
  obtain ⟨n, hn⟩ := H.cartan.trans _ (hc.outerRestPt_mem h hS2 hk hy₀) b hb hne hb1
  have hdnY : (d ^ n)⁻¹ ∈ normalizer (szR (szT₁ L T) V t : Set G) := inv_mem (pow_mem hdY n)
  have hdnt : (d ^ n)⁻¹ * t = t * (d ^ n)⁻¹ := (Commute.pow_left hdt n).inv_left.eq
  refine ⟨(d ^ n)⁻¹ * y₀, mul_mem hdnY hy₀, ?_⟩
  rw [hc.outerRestPt_mul h hS2 hk hdnY hy₀, U3C1OuterConf.outerRestPt_of_comm hdnt, mul_one,
    inv_inv, hn]

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outerRest_card_le_card (h : U3Start G L f t T) {Q : Subgroup G}
    (hQC : Q ≤ centralizer ({t} : Set G)) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  obtain ⟨a, -, ha⟩ := exists_conj_mem_of_isSylowOf hTsyl hQC hQ
  have hle : Q.map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using ha x hx
  have h1 := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1

theorem outerRest_card_sup_zpowers_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szT₁ L T ⊔ zpowers t : Subgroup G) ≤ 2 * (2 ^ f) ^ 3 := by
  obtain ⟨hT₁card, -⟩ := h.facts_of_card_sylow hS2
  have htN : zpowers t ≤ normalizer (szT₁ L T : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ h.mem_centralizer_szT₁)
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
  have ht2 : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h.sq_eq_one)
  have hpos : 0 < Nat.card (zpowers t ⊓ szT₁ L T : Subgroup G) := Nat.card_pos
  calc Nat.card (szT₁ L T ⊔ zpowers t : Subgroup G) =
        Nat.card (zpowers t ⊔ szT₁ L T : Subgroup G) := by rw [sup_comm]
    _ ≤ Nat.card (zpowers t ⊔ szT₁ L T : Subgroup G) *
        Nat.card (zpowers t ⊓ szT₁ L T : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card (zpowers t) * Nat.card (szT₁ L T) := hprod
    _ ≤ 2 * (2 ^ f) ^ 3 := by rw [hT₁card]; exact Nat.mul_le_mul_right _ ht2

end U3Start

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRest_inf_eq (hc : U3C1OuterConf G L f t T R₂ D V k) :
    szT₁ L T ⊓ V = szA₁ (szT₁ L T) := by
  refine le_antisymm (fun x hx => ?_) (le_inf (szA₁_le _) hc.le)
  obtain ⟨hxT, hxV⟩ := mem_inf.mp hx
  exact mem_inf.mpr ⟨hxT, mem_centralizer_iff.mpr fun y hy =>
    mem_centralizer_iff.mp (hc.le_centralizer hxV) y hy⟩

theorem outerRest_card_sup (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szT₁ L T ⊔ V : Subgroup G) = (2 ^ f) ^ (k + 3) := by
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hT₁NV : szT₁ L T ≤ normalizer (V : Set G) := fun y hy =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
      have e := mem_centralizer_iff.mp (hc.le_centralizer hr) y hy
      rw [show y⁻¹ * r * y = r by rw [mul_assoc, ← e, inv_mul_cancel_left]]
      exact hr
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hT₁NV
  rw [hc.outerRest_inf_eq, hc.card, hT₁card, hA₁card] at hprod
  have h2 : Nat.card (szT₁ L T ⊔ V : Subgroup G) * 2 ^ f = (2 ^ f) ^ (k + 3) * 2 ^ f := by
    rw [hprod]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h2

theorem outerRest_t_not_mem (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) : t ∉ szT₁ L T ⊔ V := by
  intro htH
  obtain ⟨a, -, b, hb, hab⟩ := hc.exists_pow_four_ne h hS2 hk
  have hb4 : b ^ 4 ≠ 1 := by simpa using (hab 0).1
  apply hb4
  have e1 : t * b * t⁻¹ = b := by rw [hc.commute_of_mem_sup htH hb, mul_inv_cancel_right]
  have e3 : b⁻¹ = b := by rw [← hc.inv b hb, e1]
  have e2 : b ^ 2 = 1 := by
    rw [sq]
    calc b * b = b * b⁻¹ := by rw [e3]
      _ = 1 := mul_inv_cancel b
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2, one_pow]

theorem outerRest_card_szR (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) : Nat.card (szR (szT₁ L T) V t) = 2 * (2 ^ f) ^ (k + 3) := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
  have htN : zpowers t ≤ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    zpowers_le.mpr (h.sup_le_normalizer_sup_szT₁ hS2 hVc hc.T_le (mem_sup_left htT))
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
  have hinf : zpowers t ⊓ (szT₁ L T ⊔ V) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxH⟩ := mem_inf.mp hx
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hxt with rfl | rfl
    · exact one_mem _
    · exact absurd hxH (hc.outerRest_t_not_mem h hS2 hk)
  have ht2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, h.inv]
  rw [hinf, card_bot, mul_one, hc.outerRest_card_sup h hS2, ht2] at hprod
  have e : szR (szT₁ L T) V t = zpowers t ⊔ (szT₁ L T ⊔ V) := by rw [szR, sup_comm]
  rw [e, hprod]

theorem outerRest_exists_of_pt_eq_one
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) (h1 : outerRestPt t k n = 1) :
    ∃ s ∈ V, s⁻¹ * n * t = t * (s⁻¹ * n) := by
  obtain ⟨s, hs, hs2⟩ := hc.outerRest_exists_sq h hS2 (hc.outerRest_comm_t_mem h hS2 hk hn) h1
  refine ⟨s, hs, ?_⟩
  have e : n * t * n⁻¹ = s * t * s⁻¹ := by
    rw [hc.outerRest_conj_t hs, hs2]; group
  calc s⁻¹ * n * t = s⁻¹ * (n * t * n⁻¹) * n := by group
    _ = s⁻¹ * (s * t * s⁻¹) * n := by rw [e]
    _ = t * (s⁻¹ * n) := by group

theorem outerRest_u3C1U_inf_stab
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) :
    u3C1U L T V t ⊓ outerRestStab L T V t = szR (szT₁ L T) V t := by
  refine le_antisymm (fun x hx => ?_) (le_inf (hc.szR_le_u3C1U h hS2) (szR_le_outerRestStab h))
  obtain ⟨hxU, hxS⟩ := mem_inf.mp hx
  obtain ⟨hxY, h1⟩ := (hc.mem_outerRestStab_iff h hS2 hk).mp hxS
  obtain ⟨s, hs, hst⟩ := hc.outerRest_exists_of_pt_eq_one h hS2 hk hxY h1
  have hsU : s ∈ u3C1U L T V t := hc.szR_le_u3C1U h hS2 (le_szR_mid _ _ _ hs)
  have hc' : s⁻¹ * x ∈ u3C1U L T V t ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨mul_mem (inv_mem hsU) hxU, mem_centralizer_singleton_iff.mpr hst⟩
  rw [hc.u3C1U_inf_centralizer h hS2] at hc'
  rw [show x = s * (s⁻¹ * x) by group]
  exact mul_mem (le_szR_mid _ _ _ hs)
    ((sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))) hc')

theorem outerRest_card_u3C1U
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k)
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ u3C1U L T V t, outerRestPt t k x = b) :
    Nat.card (u3C1U L T V t) = 2 * (2 ^ f) ^ (k + 4) := by
  rw [(hc.outerRest_card_le h hS2 hk u3C1U_le_normalizer).2 htr,
    hc.outerRest_u3C1U_inf_stab h hS2 hk, hc.outerRest_card_szR h hS2 hk]
  ring

theorem outerRest_card_stab_le
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k)
    {Q : Subgroup G} (hQ : Q ≤ outerRestStab L T V t) (hQ2 : IsPGroup 2 Q) :
    Nat.card Q ≤ (2 ^ f) ^ k * Nat.card T := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hQY := hQ.trans (hc.outerRestStab_le h hS2 hk)
  have hVY : V ≤ normalizer (szR (szT₁ L T) V t : Set G) :=
    (le_szR_mid _ _ _).trans Subgroup.le_normalizer
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := f * (k + 1)) (by rw [hc.card, pow_mul])
  have hQV : Q ≤ normalizer (V : Set G) := fun x hx => (hc.normalizer_szR_le h hS2 hk (hQY hx)).2.1
  have hQ₁ : IsPGroup 2 (Q ⊔ V : Subgroup G) := IsPGroup.to_sup_of_normal_right' hQ2 hV2 hQV
  set C := (Q ⊔ V) ⊓ centralizer ({t} : Set G) with hCdef
  have hC2 : IsPGroup 2 C := hQ₁.to_le inf_le_left
  have hCT : Nat.card C ≤ Nat.card T := h.outerRest_card_le_card inf_le_right hC2
  have hCV : C ≤ normalizer (V : Set G) := fun x hx =>
    (hc.normalizer_szR_le h hS2 hk ((sup_le hQY hVY) (mem_inf.mp hx).1)).2.1
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hCV
  have hQle : Q ≤ C ⊔ V := by
    intro x hx
    obtain ⟨hxY, h1⟩ := (hc.mem_outerRestStab_iff h hS2 hk).mp (hQ hx)
    obtain ⟨s, hs, hst⟩ := hc.outerRest_exists_of_pt_eq_one h hS2 hk hxY h1
    have hc' : s⁻¹ * x ∈ C := mem_inf.mpr ⟨mul_mem (inv_mem (mem_sup_right hs)) (mem_sup_left hx),
      mem_centralizer_singleton_iff.mpr hst⟩
    rw [show x = s * (s⁻¹ * x) by group]
    exact mul_mem (mem_sup_right hs) (mem_sup_left hc')
  have hA₁le : szA₁ (szT₁ L T) ≤ C ⊓ V := fun b hb =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨mem_sup_right (hc.le hb), mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp h.mem_centralizer_szT₁ b (szA₁_le _ hb))⟩, hc.le hb⟩
  have h2 : 2 ^ f ≤ Nat.card (C ⊓ V : Subgroup G) := hA₁card ▸ Subgroup.card_le_of_le hA₁le
  have h3 : Nat.card Q ≤ Nat.card (C ⊔ V : Subgroup G) := Subgroup.card_le_of_le hQle
  have h4 : Nat.card Q * 2 ^ f ≤ (2 ^ f) ^ k * Nat.card T * 2 ^ f := by
    calc Nat.card Q * 2 ^ f ≤ Nat.card (C ⊔ V : Subgroup G) * Nat.card (C ⊓ V : Subgroup G) :=
          Nat.mul_le_mul h3 h2
      _ = Nat.card C * Nat.card V := hprod
      _ ≤ Nat.card T * (2 ^ f) ^ (k + 1) := by rw [hc.card]; exact Nat.mul_le_mul_right _ hCT
      _ = (2 ^ f) ^ k * Nat.card T * 2 ^ f := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

theorem outerRest_T_le (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    T ≤ normalizer (szR (szT₁ L T) V t : Set G) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  exact fun s hs => mem_normalizer_szR_of (hTN₁ hs) (hc.T_le hs)
    (mem_centralizer_singleton_iff.mp (h.le hs))

theorem outerRest_isSylowOf
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k)
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ u3C1U L T V t, outerRestPt t k x = b) :
    CFSG.ABGLocalTools.IsSylowOf 2 (u3C1U L T V t ⊔ T)
      (normalizer (szR (szT₁ L T) V t : Set G)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := hc.outerRest_card_u3C1U h hS2 hk htr
  have hTY := hc.outerRest_T_le h hS2
  have hYU := hc.le_normalizer_u3C1U_of_two_le h hS2 hk
  have hU2 : IsPGroup 2 (u3C1U L T V t) :=
    IsPGroup.of_card (n := 1 + f * (k + 4)) (by rw [hcard, ← pow_mul, pow_add, pow_one])
  have hTU2 : IsPGroup 2 (T ⊔ u3C1U L T V t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.isPGroup hU2 (hTY.trans hYU)
  rw [sup_comm] at hTU2
  obtain ⟨P, hP, hUTP⟩ := exists_isSylowOf_le_of_isPGroup (sup_le u3C1U_le_normalizer hTY) hTU2
  have hPcard := (hc.outerRest_card_le h hS2 hk hP.le).1
  have hPS := hc.outerRest_card_stab_le h hS2 hk (inf_le_right : P ⊓ outerRestStab L T V t ≤ _)
    (hP.isPGroup.to_le inf_le_left)
  have hce := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer (hTY.trans hYU)
  rw [hcard] at hce
  have he : Nat.card (T ⊓ u3C1U L T V t : Subgroup G) ≤ 2 * (2 ^ f) ^ 3 := by
    have hle : T ⊓ u3C1U L T V t ≤ szT₁ L T ⊔ zpowers t := by
      rw [← hc.u3C1U_inf_centralizer h hS2]
      exact fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, h.le (mem_inf.mp hx).1⟩
    exact (Subgroup.card_le_of_le hle).trans (h.outerRest_card_sup_zpowers_le hS2)
  have hepos : 0 < Nat.card (T ⊓ u3C1U L T V t : Subgroup G) := Nat.card_pos
  set q := 2 ^ f with hq
  set e := Nat.card (T ⊓ u3C1U L T V t : Subgroup G) with hedef
  have hle : Nat.card P * e ≤ Nat.card (u3C1U L T V t ⊔ T : Subgroup G) * e := by
    calc Nat.card P * e ≤ (q * (q ^ k * Nat.card T)) * e :=
          Nat.mul_le_mul_right _ (hPcard.trans (Nat.mul_le_mul_left _ hPS))
      _ ≤ (q * (q ^ k * Nat.card T)) * (2 * q ^ 3) := Nat.mul_le_mul_left _ he
      _ = Nat.card T * (2 * q ^ (k + 4)) := by ring
      _ = Nat.card (T ⊔ u3C1U L T V t : Subgroup G) * e := hce.symm
      _ = Nat.card (u3C1U L T V t ⊔ T : Subgroup G) * e := by rw [sup_comm]
  have hle' := Nat.le_of_mul_le_mul_right hle hepos
  have heq : u3C1U L T V t ⊔ T = P := Subgroup.eq_of_le_of_card_ge hUTP hle'
  rw [heq]
  exact hP

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
