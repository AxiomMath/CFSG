module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {t : G} {E : Subgroup G}
    (h : ∀ e ∈ E, t * e * t⁻¹ ∈ E) : t ∈ normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_le : E.map (MulAut.conj t) ≤ E := by
    rintro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using h e he
  refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

private lemma mem_sup_of_le_normalizer {G : Type} [Group G] {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hconj : ∀ a ∈ H, ∀ b ∈ K, a * b * a⁻¹ ∈ K :=
    Subgroup.le_normalizer_iff.mp hHK
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, a * b = x}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          exact ⟨a * c, H.mul_mem ha hc, (c⁻¹ * b * c) * d,
            K.mul_mem (by simpa using hconj c⁻¹ (H.inv_mem hc) b hb) hd, by group⟩
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, hconj a ha b⁻¹ (K.inv_mem hb),
            by group⟩ }
    have hHP : H ≤ P := fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩
    have hKP : K ≤ P := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
    exact SetLike.le_def.mp (sup_le hHP hKP) hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private lemma inf_centralizer_sup_eq {G : Type} [Group G] {t : G} {H K : Subgroup G}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hd : H ⊓ K = ⊥)
    (hH : ∀ a ∈ H, t * a * t⁻¹ ∈ H) (hK : ∀ a ∈ K, t * a * t⁻¹ ∈ K) :
    (H ⊔ K) ⊓ centralizer ({t} : Set G) =
      (H ⊓ centralizer ({t} : Set G)) ⊔ (K ⊓ centralizer ({t} : Set G)) := by
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    rw [hc a ha b hb]
    simpa using hb
  have huniq : ∀ (h₁ : G) (k₁ : G) (h₂ : G) (k₂ : G), h₁ ∈ H → k₁ ∈ K → h₂ ∈ H → k₂ ∈ K →
      h₁ * k₁ = h₂ * k₂ → h₁ = h₂ ∧ k₁ = k₂ := by
    intro h₁ k₁ h₂ k₂ hh₁ hk₁ hh₂ hk₂ heq
    have hinj := sec124_noncomm_injective hc hd
    have hp : ((⟨h₁, hh₁⟩, ⟨k₁, hk₁⟩) : ↥H × ↥K) = (⟨h₂, hh₂⟩, ⟨k₂, hk₂⟩) :=
      hinj (by simpa [MonoidHom.noncommCoprod_apply] using heq)
    exact ⟨congrArg (fun p : ↥H × ↥K => (p.1 : G)) hp,
      congrArg (fun p : ↥H × ↥K => (p.2 : G)) hp⟩
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨hxHK, hxt⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨h, hh, k, hk, hhk⟩ := (mem_sup_of_le_normalizer hHK).mp hxHK
    have hxt' : t * x * t⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hxt]
      group
    have hprod : (t * h * t⁻¹) * (t * k * t⁻¹) = h * k := by
      calc (t * h * t⁻¹) * (t * k * t⁻¹) = t * (h * k) * t⁻¹ := by group
        _ = t * x * t⁻¹ := by rw [hhk]
        _ = x := hxt'
        _ = h * k := hhk.symm
    have hone := huniq (t * h * t⁻¹) (t * k * t⁻¹) h k (hH h hh) (hK k hk) hh hk hprod
    have hh_cent : h ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hh'' := hone.1
      rw [mul_inv_eq_iff_eq_mul] at hh''
      exact hh''.symm
    have hk_cent : k ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hk'' := hone.2
      rw [mul_inv_eq_iff_eq_mul] at hk''
      exact hk''.symm
    rw [← hhk]
    exact Subgroup.mul_mem_sup ⟨hh, hh_cent⟩ ⟨hk, hk_cent⟩
  · exact le_inf (le_trans inf_le_left le_sup_left) inf_le_right
  · exact le_inf (le_trans inf_le_left le_sup_right) inf_le_right

private lemma zpowers_inf_eq_bot_of_notMem {G : Type} [Group G] {t : G} {C : Subgroup G}
    (ht : t ∉ C) (hcard : Nat.card ↥(zpowers t) = 2) : zpowers t ⊓ C = ⊥ := by
  haveI : Fact (Nat.card ↥(zpowers t)).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (C.subgroupOf (zpowers t)) with h | h
  · have hd : Disjoint C (zpowers t) := Subgroup.subgroupOf_eq_bot.mp h
    rw [Subgroup.disjoint_def] at hd
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact hd hx.2 hx.1
  · exact absurd ((Subgroup.subgroupOf_eq_top.mp h) (Subgroup.mem_zpowers t)) ht

theorem sec8t84_cent_E_card {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) (hCE : Asc82FinkCE) :
    (∃ m : ℕ, Odd m ∧ Nat.card ↥(centralizer (E : Set G)) = 2 ^ 8 * m) ∧
      ∃ n : ℕ, Odd n ∧
        Nat.card ↥(centralizer (E : Set G) ⊓ centralizer ({t} : Set G)) = 2 ^ 4 * n := by
  obtain ⟨hCeq, hOleC⟩ := hCE G t L S z g B E hE
  have htX : t ∈ normalizer (E : Set G) := mem_normalizer_of_conj_mem hE.t_norm
  have hEcard : Nat.card ↥E = 2 ^ 8 := hE.elem.2
  have hOodd : Odd (Nat.card ↥(oddCoreIn (normalizer (E : Set G)))) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (normalizer (E : Set G))
  have hcEO : ∀ a ∈ E, ∀ b ∈ oddCoreIn (normalizer (E : Set G)), a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hOleC hb) a ha
  have hEObot : E ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥ := by
    have hoddsub : Odd (Nat.card ↥(E ⊓ oddCoreIn (normalizer (E : Set G)))) :=
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le
        (inf_le_right : E ⊓ oddCoreIn (normalizer (E : Set G)) ≤ _))
    have hdvd : Nat.card ↥(E ⊓ oddCoreIn (normalizer (E : Set G))) ∣ 2 ^ 8 := by
      simpa [hEcard] using
        (Subgroup.card_dvd_of_le (inf_le_left : E ⊓ oddCoreIn (normalizer (E : Set G)) ≤ E))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k = 0 := by
      by_contra hkne
      have heven : Even (2 ^ k) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
        exact even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero j))
      exact (Nat.not_even_iff_odd.mpr (hk ▸ hoddsub)) heven
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  have htO : ∀ a ∈ oddCoreIn (normalizer (E : Set G)),
      t * a * t⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
    fun a ha => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn htX ha
  refine ⟨⟨Nat.card ↥(oddCoreIn (normalizer (E : Set G))), hOodd, ?_⟩, ?_⟩
  · rw [hCeq, sec124_card_sup hcEO hEObot, hEcard]
  · refine ⟨Nat.card ↥(oddCoreIn (normalizer (E : Set G)) ⊓ centralizer ({t} : Set G)),
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le
        (inf_le_left : oddCoreIn (normalizer (E : Set G)) ⊓ _ ≤ _)), ?_⟩
    have hdecomp : centralizer (E : Set G) ⊓ centralizer ({t} : Set G) =
        (E ⊓ centralizer ({t} : Set G)) ⊔
          (oddCoreIn (normalizer (E : Set G)) ⊓ centralizer ({t} : Set G)) := by
      rw [hCeq]
      exact inf_centralizer_sup_eq hcEO hEObot hE.t_norm htO
    have hBleE : B ≤ E := by rw [← hE.cent_t]; exact inf_le_left
    have hcBO : ∀ a ∈ B, ∀ b ∈ oddCoreIn (normalizer (E : Set G)) ⊓
        centralizer ({t} : Set G), a * b = b * a :=
      fun a ha b hb => hcEO a (hBleE ha) b hb.1
    have hdBot : B ⊓ (oddCoreIn (normalizer (E : Set G)) ⊓ centralizer ({t} : Set G)) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      have hxEO : x ∈ E ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨hBleE hx.1, hx.2.1⟩
      rw [hEObot] at hxEO
      exact hxEO
    rw [hdecomp, hE.cent_t, sec124_card_sup hcBO hdBot, hE.ctx.B_e16.2]

theorem sec8t84_K_inf_card {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) (hCE : Asc82FinkCE) :
    Nat.card ↥((zpowers t ⊔ centralizer (E : Set G)) ⊓
        (normalizer (E : Set G) ⊓ centralizer ({t} : Set G))) =
      2 * Nat.card ↥(centralizer (E : Set G) ⊓ centralizer ({t} : Set G)) := by
  obtain ⟨hCeq, -⟩ := hCE G t L S z g B E hE
  have htX : t ∈ normalizer (E : Set G) := mem_normalizer_of_conj_mem hE.t_norm
  have h2 : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact hE.ctx.involution
  have ht_notC : t ∉ centralizer (E : Set G) := by
    intro htC
    have hBbot : B = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro b hb
      obtain ⟨e, he, heq⟩ := hE.comm_onto b hb
      have het : e * t = t * e := Subgroup.mem_centralizer_iff.mp htC e he
      have h1 : e * t * e⁻¹ * t⁻¹ = 1 := by rw [het]; group
      rw [Subgroup.mem_bot, ← heq]
      exact h1
    have h16 : (2 : ℕ) ^ 4 = 1 := by
      rw [← hE.ctx.B_e16.2, hBbot, Subgroup.card_bot]
    exact absurd h16 (by norm_num)
  have hCbot : zpowers t ⊓ centralizer (E : Set G) = ⊥ :=
    zpowers_inf_eq_bot_of_notMem ht_notC h2
  have hzpY : zpowers t ≤ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨htX, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCX : centralizer (E : Set G) ≤ normalizer (E : Set G) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)
  have hXN_C : normalizer (E : Set G) ≤
      Subgroup.normalizer (centralizer (E : Set G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro e he
    have hmem : x⁻¹ * e * x ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hx) e).mp he
    have hcomm : (x⁻¹ * e * x) * c = c * (x⁻¹ * e * x) := hc _ hmem
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * c * x⁻¹) * e := by group
  have hzpN_C : zpowers t ≤ Subgroup.normalizer (centralizer (E : Set G) : Set G) :=
    Subgroup.zpowers_le.mpr (hXN_C htX)
  have hKY : (zpowers t ⊔ centralizer (E : Set G)) ⊓
      (normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) =
      zpowers t ⊔ (centralizer (E : Set G) ⊓ centralizer ({t} : Set G)) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · intro x hx
      obtain ⟨hxK, hxY⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, c, hc, hac⟩ := (mem_sup_of_le_normalizer hzpN_C).mp hxK
      have ha_cent : a ∈ centralizer ({t} : Set G) :=
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ha
      have hc_cent : c ∈ centralizer ({t} : Set G) := by
        have hceq : c = a⁻¹ * x := by rw [← hac]; group
        rw [hceq]
        exact mul_mem (inv_mem ha_cent) hxY.2
      rw [← hac]
      exact Subgroup.mul_mem_sup ha ⟨hc, hc_cent⟩
    · exact le_inf le_sup_left hzpY
    · apply le_inf
      · exact le_trans inf_le_left le_sup_right
      · apply le_inf
        · exact le_trans inf_le_left hCX
        · exact inf_le_right
  have hcZD : ∀ a ∈ zpowers t,
      ∀ b ∈ centralizer (E : Set G) ⊓ centralizer ({t} : Set G), a * b = b * a := by
    intro a ha b hb
    have hb_comm : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    have ht_cent_b : t ∈ centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hb_comm.symm
    have hle : zpowers t ≤ centralizer ({b} : Set G) := Subgroup.zpowers_le.mpr ht_cent_b
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hdZD : zpowers t ⊓ (centralizer (E : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxC : x ∈ zpowers t ⊓ centralizer (E : Set G) := ⟨hx.1, hx.2.1⟩
    rw [hCbot] at hxC
    exact hxC
  rw [hKY, sec124_card_sup hcZD hdZD, h2]

end CFSG.OddStandard.SmallF3.Omega
