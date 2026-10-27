module

public import CFSG.LieType.Ree.TitsQuotient
public import CFSG.LieType.Simplicity.ReeLarge

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag CFSG.LieType.BorelTits
open scoped commutatorElement

section GroupTheory

variable {G : Type*} [Group G]

theorem commutator_le_commutator_top_of_sup_zpowers {D : Subgroup G} [hD : D.Normal] {g : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) : commutator G ≤ ⁅D, ⊤⁆ := by
  set N := ⁅D, (⊤ : Subgroup G)⁆
  have hN : N.Normal := Subgroup.commutator_normal D ⊤
  have hcen : ∀ d ∈ D, ∀ w : G, Commute (QuotientGroup.mk' N d) (QuotientGroup.mk' N w) := by
    intro d hd w
    have hc : ⁅d, w⁆ ∈ N := Subgroup.commutator_mem_commutator hd (Subgroup.mem_top w)
    have h1 : QuotientGroup.mk' N ⁅d, w⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hdec : ∀ x : G, ∃ d ∈ D, ∃ k : ℤ, x = d * g ^ k := by
    intro x
    have hx : x ∈ D ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top x
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨d, hd, k, rfl⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨d₁, hd₁, a, rfl⟩ := hdec x
  obtain ⟨d₂, hd₂, b, rfl⟩ := hdec y
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  simp only [map_mul, map_zpow]
  have hg : Commute (QuotientGroup.mk' N g ^ a) (QuotientGroup.mk' N g ^ b) :=
    Commute.zpow_zpow_self _ a b
  have h1 := hcen d₁ hd₁ (d₂ * g ^ b)
  have h2 := hcen d₂ hd₂ (g ^ a)
  simp only [map_mul, map_zpow] at h1 h2
  exact (h1.mul_left (h2.symm.mul_right hg)).eq

theorem commutator_le_of_isNilpotent_quotient {N : Subgroup G} [N.Normal]
    (hnil : Group.IsNilpotent (G ⧸ N)) (h : commutator G ≤ ⁅commutator G, ⊤⁆) :
    commutator G ≤ N := by
  have hle : ∀ n, commutator G ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact h.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hnil
  have hmap : ((⊤ : Subgroup G).lowerCentralSeries n).map (QuotientGroup.mk' N) ≤ ⊥ := by
    rw [Subgroup.map_lowerCentralSeries, ← hn]
    exact Subgroup.lowerCentralSeries_mono n le_top
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hmap
  exact (hle n).trans hmap

theorem mul_inv_mem_of_sup_zpowers {D : Subgroup G} [D.Normal] {g : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) (hg2 : g ^ 2 ∈ D) {s : G} (hs : s ∉ D) : s * g⁻¹ ∈ D := by
  have hx : s ∈ D ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top s
  obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · exfalso
    apply hs
    refine mul_mem hd ?_
    rw [zpow_mul]
    exact zpow_mem (by exact_mod_cast hg2) j
  · have e : d * g ^ (2 * j + 1) * g⁻¹ = d * (g ^ 2) ^ j := by
      rw [zpow_add_one, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, zpow_mul]
      norm_cast
    rw [e]
    exact mul_mem hd (zpow_mem hg2 j)

theorem false_of_swapped_factors [Finite G] {D A B P : Subgroup G} [hD : D.Normal] {g x : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) (hgD : g ∉ D) (hg2 : g ^ 2 ∈ D)
    (hgp : IsPGroup 2 (Subgroup.zpowers g))
    (hAD : A ≤ D) (hBD : B ≤ D) (hA : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ ∈ A)
    (hB : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ ∈ B) (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = D)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ B)
    (hxA : x ∈ A) (S : Sylow 2 G) (hP : P ≠ ⊤)
    (hNx : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ P)
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBP : B ≤ P := by
    intro b hb
    apply hNx
    apply Subgroup.centralizer_le_normalizer
    have hc : x * b = b * x := by
      have h1 : ⁅x, b⁆ ∈ A ⊓ B := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have : b * x⁻¹ * b⁻¹ ∈ A := hA b (hBD hb) _ (inv_mem hxA)
          have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
          rw [e]
          exact mul_mem hxA this
        · rw [commutatorElement_def]
          exact mul_mem (hB x (hAD hxA) b hb) (inv_mem hb)
      rw [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute x b from hc) k).eq
  have hSD : ¬ (S : Subgroup G) ≤ D := by
    intro hle
    obtain ⟨Q, hQ⟩ := hgp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
    apply hgD
    have hgQ : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
    rw [← hc, Sylow.coe_subgroup_smul] at hgQ
    obtain ⟨y, hy, rfl⟩ := hgQ
    exact hD.conj_mem y (hle hy) c
  obtain ⟨s, hsS, hsD⟩ := Set.not_subset.1 hSD
  have hsP : s ∈ P := hNS (Subgroup.le_normalizer hsS)
  have hd : s * g⁻¹ ∈ D := mul_inv_mem_of_sup_zpowers h hg2 hsD
  have hAP : A ≤ P := by
    intro a ha
    set d := s * g⁻¹
    have hb : g * (d⁻¹ * a * d) * g⁻¹ ∈ B := by
      have h1 : d⁻¹ * a * d ∈ A := by
        have := hA d⁻¹ (inv_mem hd) a ha
        rwa [inv_inv] at this
      exact hgA _ h1
    have hb' : (g ^ 2)⁻¹ * (g * (d⁻¹ * a * d) * g⁻¹) * g ^ 2 ∈ B := by
      have := hB (g ^ 2)⁻¹ (inv_mem hg2) _ hb
      rwa [inv_inv] at this
    have e : a = s * ((g ^ 2)⁻¹ * (g * (d⁻¹ * a * d) * g⁻¹) * g ^ 2) * s⁻¹ := by
      simp only [d]
      group
    rw [e]
    exact mul_mem (mul_mem hsP (hBP hb')) (inv_mem hsP)
  have hDP : D ≤ P := hsup ▸ sup_le hAP hBP
  apply hP
  rw [eq_top_iff, ← h]
  refine sup_le hDP ?_
  rw [Subgroup.zpowers_le]
  have e : g = (s * g⁻¹)⁻¹ * s := by group
  rw [e]
  exact mul_mem (inv_mem (hDP hd)) hsP

end GroupTheory

section Tits

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeBorelPart_le_reeUnipPart_of_card_eq_two
    (hK : Nat.card K = 2) :
    reeBorelPart ReeTag.F4 K 0 ≤ reeUnipPart ReeTag.F4 K 0 := by
  intro b hb
  obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_of_mem_reeBorelPart (t := ReeTag.F4) (K := K) 0 hb
  have hc1 : c = 1 := Subtype.ext (eq_one_of_mem_H_of_card_eq_two hK hc)
  rw [hc1, mul_one]
  exact hs

theorem isPGroup_reeBorelPart_of_card_eq_two
    (hK : Nat.card K = 2) :
    IsPGroup 2 (reeBorelPart ReeTag.F4 K 0) := by
  have hS : IsPGroup ReeTag.F4.prime (reeUnipPart ReeTag.F4 K 0) :=
    ((nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U ReeTag.F4.prime).comap_of_injective _
      Subtype.val_injective
  exact hS.to_le (reeBorelPart_le_reeUnipPart_of_card_eq_two hK)

theorem eq_bot_or_sup_eq_top_of_card_eq_two
    (hK : Nat.card K = 2)
    (N : Subgroup (reeFixed ReeTag.F4 K 0)) [hN : N.Normal] :
    N = ⊥ ∨ N ⊔ reeBorelPart ReeTag.F4 K 0 = ⊤ := by
  by_cases hNB : N ≤ reeBorelPart ReeTag.F4 K 0
  · left
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxU := reeBorelPart_le_reeUnipPart_of_card_eq_two hK (hNB hx)
    have h := hNB (hN.conj_mem x hx (reeLongRep ReeTag.F4 K 0))
    exact Subtype.ext (eq_one_of_nrep_longWord_conj_mem_B hxU h)
  · exact .inr (sup_reeBorelPart_eq_top_F4 N hNB)

theorem isPGroup_quotient_of_sup_eq_top
    (hK : Nat.card K = 2)
    (N : Subgroup (reeFixed ReeTag.F4 K 0)) [N.Normal]
    (h : N ⊔ reeBorelPart ReeTag.F4 K 0 = ⊤) : IsPGroup 2 (reeFixed ReeTag.F4 K 0 ⧸ N) := by
  refine (isPGroup_reeBorelPart_of_card_eq_two hK).of_surjective
    ((QuotientGroup.mk' N).comp (reeBorelPart ReeTag.F4 K 0).subtype) ?_
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hg : g ∈ N ⊔ reeBorelPart ReeTag.F4 K 0 := h ▸ Subgroup.mem_top g
  obtain ⟨n, hn, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine ⟨⟨b, hb⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]

variable (K) in
structure TitsData
    where
  g₀ : reeFixed ReeTag.F4 K 0
  g₁ : reeFixed ReeTag.F4 K 0
  fixed₀ : ∀ y ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (0 : Fin 4)),
    ReeTag.F4.reeAut K 0 y = y → y = 1 ∨ y = g₀
  fixed₁ : ∀ y ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (1 : Fin 4)),
    ReeTag.F4.reeAut K 0 y = y → y ∈ Subgroup.zpowers (g₁ : adjointGroup ReeTag.F4.tag K)
  g₀_mul_self : g₀ * g₀ = 1
  g₀_ne_one : g₀ ≠ 1
  g₁_mem_U : (g₁ : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U
  g₀_mem : g₀ ∈ commutator (reeFixed ReeTag.F4 K 0)
  g₁_sq_mem : g₁ ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0)
  nonabelian : ∃ x ∈ commutator (reeFixed ReeTag.F4 K 0),
    ∃ y ∈ commutator (reeFixed ReeTag.F4 K 0), x * y ≠ y * x

namespace TitsData

variable
    (T : TitsData K)
include T

theorem commutator_sup_zpowers_eq_top
    (hK : Nat.card K = 2) :
    commutator (reeFixed ReeTag.F4 K 0) ⊔ Subgroup.zpowers T.g₁ = ⊤ := by
  set P := commutator (reeFixed ReeTag.F4 K 0) ⊔ Subgroup.zpowers T.g₁
  have hPn : ∀ g : reeFixed ReeTag.F4 K 0, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g x hx
    have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top g) (Subgroup.mem_top x))) hx
  set r₀ := ReeTag.F4.reeOrbitWord (0 : Fin 4)
  set r₁ := ReeTag.F4.reeOrbitWord (1 : Fin 4)
  have hL : [r₀, r₁, r₀, r₁, r₀, r₁, r₀, r₁].flatten = ReeTag.F4.longWord := by decide
  have hB : reeBorelPart ReeTag.F4 K 0 ≤ P := by
    intro b hb
    have hbU : (b : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U :=
      reeBorelPart_le_reeUnipPart_of_card_eq_two hK hb
    have key := fixed_mem_U_of_reduced_blocks (ReeTag.F4.reeAut K 0) ReeTag.F4.weylPerm
      (fun u hu => reeAut_mem_U 0 hu) (fun w u hu => reeAut_mem_Uminus 0 w hu)
      (fun w hw => by rw [reeAut_nrep, hw]) [r₀, r₁, r₀, r₁, r₀, r₁, r₀, r₁]
      (by
        intro ω hω
        have h01 : ω = r₀ ∨ ω = r₁ := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hω
          rcases hω with h | h | h | h | h | h | h | h <;> simp [h]
        rcases h01 with rfl | rfl
        · exact (mem_relWeylRee _).1 (reeOrbitWord_mem ReeTag.F4 (0 : Fin 4))
        · exact (mem_relWeylRee _).1 (reeOrbitWord_mem ReeTag.F4 (1 : Fin 4)))
      (by rw [hL]; exact ReeTag.F4.isReduced_longWord)
      (by rw [hL]; exact height_wordProd_smul_neg_of_negCheck ReeTag.F4.negCheck_longWord)
      (P.map (reeFixed ReeTag.F4 K 0).subtype)
      (by
        rintro g hg _ ⟨y, hy, rfl⟩
        exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hPn ⟨g, hg⟩ y hy, rfl⟩)
      (by
        intro ω hω y hy hF
        have h01 : ω = r₀ ∨ ω = r₁ := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hω
          rcases hω with h | h | h | h | h | h | h | h <;> simp [h]
        rcases h01 with rfl | rfl
        · rcases T.fixed₀ y hy hF with rfl | rfl
          · exact one_mem _
          · exact ⟨T.g₀, Subgroup.mem_sup_left T.g₀_mem, rfl⟩
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (T.fixed₁ y hy hF)
          exact ⟨T.g₁ ^ k, Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers _) k),
            by simp⟩)
    obtain ⟨y, hy, hyb⟩ := key b hbU b.2
    rwa [Subtype.ext hyb] at hy
  refine eq_top_of_reeBorelPart_le hB fun i => ?_
  obtain ⟨u, hu, huF, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, h⟩ := exists_nrep_blockElt_eq ReeTag.F4 K 0 i
  set r := nrepFixed ReeTag.F4 K 0 (reeOrbitWord_mem ReeTag.F4 i)
  have e : r = ⟨b₁, hb₁F⟩ * (r * ⟨u, huF⟩ * r⁻¹) * ⟨b₂, hb₂F⟩ := Subtype.ext h
  have huB : (⟨u, huF⟩ : reeFixed ReeTag.F4 K 0) ∈ reeBorelPart ReeTag.F4 K 0 :=
    (nativeData ReeTag.F4.tag K).U_le_B hu
  rw [e]
  exact mul_mem (mul_mem (hB hb₁) (hPn r _ (hB huB))) (hB hb₂)

theorem isPerfect
    (hK : Nat.card K = 2) :
    Group.IsPerfect (commutator (reeFixed ReeTag.F4 K 0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (commutator (reeFixed ReeTag.F4 K 0)).Normal := Subgroup.commutator_normal ⊤ ⊤
  have : (derivedSeries (reeFixed ReeTag.F4 K 0) 2).Normal := derivedSeries_normal _ 2
  have hD₂ : derivedSeries (reeFixed ReeTag.F4 K 0) 2 ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := T.nonabelian
    apply hxy
    have hc : ⁅x, y⁆ ∈ derivedSeries (reeFixed ReeTag.F4 K 0) 2 := by
      rw [derivedSeries_succ, derivedSeries_one]
      exact Subgroup.commutator_mem_commutator hx hy
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hsup := (eq_bot_or_sup_eq_top_of_card_eq_two hK _).resolve_left hD₂
  have hnil :
      Group.IsNilpotent (reeFixed ReeTag.F4 K 0 ⧸ derivedSeries (reeFixed ReeTag.F4 K 0) 2) :=
    (isPGroup_quotient_of_sup_eq_top hK _ hsup).isNilpotent
  have hle := commutator_le_of_isNilpotent_quotient hnil
    (commutator_le_commutator_top_of_sup_zpowers (T.commutator_sup_zpowers_eq_top hK))
  rw [derivedSeries_succ, derivedSeries_one] at hle
  rw [Subgroup.isPerfect_iff]
  exact le_antisymm (Subgroup.commutator_le_left _ _) hle

theorem le_of_normal
    (hK : Nat.card K = 2) (N : Subgroup (reeFixed ReeTag.F4 K 0)) [N.Normal] :
    N = ⊥ ∨ commutator (reeFixed ReeTag.F4 K 0) ≤ N := by
  rcases eq_bot_or_sup_eq_top_of_card_eq_two hK N with h | h
  · exact .inl h
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (reeFixed ReeTag.F4 K 0 ⧸ N) := by
    have := (isPGroup_quotient_of_sup_eq_top hK N h).isNilpotent
    infer_instance
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).1 hsolv
  have hperf := T.isPerfect hK
  have hDn :
      ∀ k, commutator (reeFixed ReeTag.F4 K 0) ≤ derivedSeries (reeFixed ReeTag.F4 K 0) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      have h1 := Subgroup.commutator_mono ih ih
      rw [Subgroup.isPerfect_iff.1 hperf] at h1
      exact h1
  have hmap := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' N) n
  rw [hn, le_bot_iff, ← le_bot_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot,
    QuotientGroup.ker_mk'] at hmap
  exact (hDn n).trans hmap

theorem eq_bot_or_eq_of_le
    (hK : Nat.card K = 2) (M : Subgroup (reeFixed ReeTag.F4 K 0))
    (hMD : M ≤ commutator (reeFixed ReeTag.F4 K 0))
    (hMn : ∀ d ∈ commutator (reeFixed ReeTag.F4 K 0), ∀ m ∈ M, d * m * d⁻¹ ∈ M) :
    M = ⊥ ∨ M = commutator (reeFixed ReeTag.F4 K 0) := by
  set D := commutator (reeFixed ReeTag.F4 K 0) with hDdef
  have : D.Normal := Subgroup.commutator_normal ⊤ ⊤
  by_cases hDt : D = ⊤
  · have hM : M.Normal := ⟨fun m hm g => hMn g (hDt ▸ Subgroup.mem_top g) m hm⟩
    rcases T.le_of_normal hK M with h | h
    · exact .inl h
    · exact .inr (le_antisymm hMD h)
  set g := T.g₁
  have hsup := T.commutator_sup_zpowers_eq_top hK
  have hgD : g ∉ D := fun hg => hDt (by
    rw [eq_top_iff, ← hsup]
    exact sup_le le_rfl (Subgroup.zpowers_le.2 hg))
  have hg2 : g ^ 2 ∈ D := T.g₁_sq_mem
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := by
    have hU : IsPGroup ReeTag.F4.prime (nativeData ReeTag.F4.tag K).U :=
      (nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U ReeTag.F4.prime
    obtain ⟨k, hk⟩ := hU ⟨_, T.g₁_mem_U⟩
    have hk' : g ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have h := congrArg Subtype.val hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h ⊢
      exact h
    intro v
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 v.2
    refine ⟨k, Subtype.ext ?_⟩
    change (v : reeFixed ReeTag.F4 K 0) ^ 2 ^ k = 1
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  set M' := M.map (MulAut.conj g).toMonoidHom with hM'def
  have hmemM' : ∀ y, y ∈ M' ↔ g⁻¹ * y * g ∈ M := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      change g⁻¹ * (g * m * g⁻¹) * g ∈ M
      have e : g⁻¹ * (g * m * g⁻¹) * g = m := by group
      rw [e]
      exact hm
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩
  have hgM : ∀ m ∈ M, g * m * g⁻¹ ∈ M' := fun m hm => ⟨m, hm, rfl⟩
  have hM'D : M' ≤ D := by
    rintro _ ⟨m, hm, rfl⟩
    exact this.conj_mem m (hMD hm) g
  have hM'n : ∀ d ∈ D, ∀ m ∈ M', d * m * d⁻¹ ∈ M' := by
    intro d hd m hm
    rw [hmemM'] at hm ⊢
    have hd' : g⁻¹ * d * g ∈ D := by
      have := this.conj_mem d hd g⁻¹
      rwa [inv_inv] at this
    have h1 := hMn _ hd' _ hm
    have e : g⁻¹ * (d * m * d⁻¹) * g = (g⁻¹ * d * g) * (g⁻¹ * m * g) * (g⁻¹ * d * g)⁻¹ := by
      group
    rw [e]
    exact h1
  have hgM' : ∀ m ∈ M', g * m * g⁻¹ ∈ M := by
    intro m hm
    rw [hmemM'] at hm
    have h1 := hMn (g ^ 2) hg2 _ hm
    have e : g * m * g⁻¹ = g ^ 2 * (g⁻¹ * m * g) * (g ^ 2)⁻¹ := by group
    rw [e]
    exact h1
  have hDnorm : ∀ N : Subgroup (reeFixed ReeTag.F4 K 0), (∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) →
      D ≤ Subgroup.normalizer (N : Set (reeFixed ReeTag.F4 K 0)) := by
    intro N hND d hd
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hND d hd n, fun h => ?_⟩
    have := hND d⁻¹ (inv_mem hd) _ h
    simpa [mul_assoc] using this
  have hnormal : ∀ N : Subgroup (reeFixed ReeTag.F4 K 0),
      (∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) → (∀ n ∈ N, g * n * g⁻¹ ∈ N) → N.Normal := by
    intro N hND hNg
    have hgN : g ∈ Subgroup.normalizer (N : Set (reeFixed ReeTag.F4 K 0)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨hNg n, fun h => ?_⟩
      have h1 := hND (g ^ 2)⁻¹ (inv_mem hg2) _ h
      have e2 : (g ^ 2)⁻¹ * (g * n * g⁻¹) * ((g ^ 2)⁻¹)⁻¹ = g⁻¹ * n * g := by group
      rw [e2] at h1
      have h2 := hNg _ h1
      have e3 : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
      rwa [e3] at h2
    have htop : Subgroup.normalizer (N : Set (reeFixed ReeTag.F4 K 0)) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le (hDnorm N hND) (Subgroup.zpowers_le.2 hgN)
    exact Subgroup.normalizer_eq_top_iff.1 htop
  have hconj_sup : ∀ c : reeFixed ReeTag.F4 K 0, ∀ X Y : Subgroup (reeFixed ReeTag.F4 K 0),
      (∀ m ∈ M, c * m * c⁻¹ ∈ X) → (∀ m ∈ M', c * m * c⁻¹ ∈ Y) →
        ∀ n ∈ M ⊔ M', c * n * c⁻¹ ∈ X ⊔ Y := by
    intro c X Y hX hY n hn
    have hle : M ⊔ M' ≤ (X ⊔ Y).comap (MulAut.conj c).toMonoidHom :=
      sup_le (fun m hm => Subgroup.mem_sup_left (hX m hm))
        (fun m hm => Subgroup.mem_sup_right (hY m hm))
    exact hle hn
  have hinfN : (M ⊓ M').Normal := hnormal _
    (fun d hd n hn => Subgroup.mem_inf.2 ⟨hMn d hd n (Subgroup.mem_inf.1 hn).1,
      hM'n d hd n (Subgroup.mem_inf.1 hn).2⟩)
    (fun n hn => Subgroup.mem_inf.2 ⟨hgM' n (Subgroup.mem_inf.1 hn).2,
      hgM n (Subgroup.mem_inf.1 hn).1⟩)
  have hsupN : (M ⊔ M').Normal := hnormal _
    (fun d hd n hn => hconj_sup d M M' (hMn d hd) (hM'n d hd) n hn)
    (fun n hn => by
      have := hconj_sup g M' M hgM hgM' n hn
      rwa [sup_comm] at this)
  rcases T.le_of_normal hK (M ⊓ M') with h1 | h1
  · rcases T.le_of_normal hK (M ⊔ M') with h2 | h2
    · exact .inl (eq_bot_iff.2 (le_sup_left.trans h2.le))
    exfalso
    have hsupD : M ⊔ M' = D := le_antisymm (sup_le hMD hM'D) h2
    have hcomm : ∀ m ∈ M, ∀ m' ∈ M', m * m' = m' * m := by
      intro m hm m' hm'
      have hc : ⁅m, m'⁆ ∈ M ⊓ M' := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have : m' * m⁻¹ * m'⁻¹ ∈ M := hMn m' (hM'D hm') _ (inv_mem hm)
          have e : m * m' * m⁻¹ * m'⁻¹ = m * (m' * m⁻¹ * m'⁻¹) := by group
          rw [e]
          exact mul_mem hm this
        · rw [commutatorElement_def]
          exact mul_mem (hM'n m (hMD hm) m' hm') (inv_mem hm')
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    have hg₀ : T.g₀ ∈ M' ⊔ M := by
      rw [sup_comm, hsupD]
      exact T.g₀_mem
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right M' M
      ((hM'D).trans (hDnorm M hMn)), Set.mem_mul] at hg₀
    obtain ⟨m', hm', m, hm, hmm⟩ := hg₀
    have hc := hcomm m hm m' hm'
    have hsq : m' * m' = (m * m)⁻¹ := by
      have h0 := T.g₀_mul_self
      rw [← hmm] at h0
      have e : m' * m * (m' * m) = (m' * m') * (m * m) := by
        calc m' * m * (m' * m) = m' * (m * m') * m := by group
          _ = m' * (m' * m) * m := by rw [hc]
          _ = (m' * m') * (m * m) := by group
      rw [e] at h0
      exact eq_inv_of_mul_eq_one_left h0
    have hm2 : m * m = 1 := by
      have hmem : m * m ∈ M ⊓ M' := Subgroup.mem_inf.2 ⟨mul_mem hm hm, by
        have := inv_mem (mul_mem hm' hm')
        rwa [hsq, inv_inv] at this⟩
      rwa [h1, Subgroup.mem_bot] at hmem
    have hm'2 : m' * m' = 1 := by rw [hsq, hm2, inv_one]
    have hpow2 : ∀ x : reeFixed ReeTag.F4 K 0, x * x = 1 → IsPGroup 2 (Subgroup.zpowers x) := by
      intro x hx v
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 v.2
      refine ⟨1, Subtype.ext ?_⟩
      change (v : reeFixed ReeTag.F4 K 0) ^ 2 ^ 1 = 1
      rw [← hj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      norm_num [sq, hx]
    by_cases hm1 : m = 1
    · have hm'1 : m' ≠ 1 := by
        rintro rfl
        apply T.g₀_ne_one
        rw [← hmm, hm1, one_mul]
      obtain ⟨S, P, hP, hN, -, -, hS⟩ := holds_reeFixed ReeTag.F4 K 0 (Subgroup.zpowers m')
        ((Subgroup.zpowers_eq_bot).not.2 hm'1) (hpow2 m' hm'2)
      exact false_of_swapped_factors hsup hgD hg2 hgp hM'D hMD hM'n hMn
        (by rw [inf_comm]; exact h1) (by rw [sup_comm]; exact hsupD) hgM' hm' S hP hN hS
    · obtain ⟨S, P, hP, hN, -, -, hS⟩ := holds_reeFixed ReeTag.F4 K 0 (Subgroup.zpowers m)
        ((Subgroup.zpowers_eq_bot).not.2 hm1) (hpow2 m hm2)
      exact false_of_swapped_factors hsup hgD hg2 hgp hMD hM'D hMn hM'n h1 hsupD hgM hm S hP
        hN hS
  · exact .inr (le_antisymm hMD (h1.trans inf_le_left))

theorem isQuasisimple
    (hK : Nat.card K = 2) :
    IsQuasisimple (commutator (reeFixed ReeTag.F4 K 0)) := by
  have : Nontrivial (commutator (reeFixed ReeTag.F4 K 0)) :=
    ⟨⟨⟨T.g₀, T.g₀_mem⟩, 1, fun h => T.g₀_ne_one (congrArg Subtype.val h)⟩⟩
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall (T.isPerfect hK) fun M hM => ?_
  rcases T.eq_bot_or_eq_of_le hK (M.map (commutator (reeFixed ReeTag.F4 K 0)).subtype)
      (Subgroup.map_subtype_le M)
      (by
        rintro d hd _ ⟨m, hm, rfl⟩
        exact ⟨⟨d, hd⟩ * m * ⟨d, hd⟩⁻¹, hM.conj_mem m hm ⟨d, hd⟩, rfl⟩) with h | h
  · left
    have hM : M = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have hm' : (m : reeFixed ReeTag.F4 K 0) ∈
          M.map (commutator (reeFixed ReeTag.F4 K 0)).subtype := ⟨m, hm, rfl⟩
      rw [h, Subgroup.mem_bot] at hm'
      exact (Subgroup.mem_bot).2 (Subtype.ext hm')
    rw [hM]
    exact bot_le
  · right
    rw [eq_top_iff]
    intro m _
    have hm' : (m : reeFixed ReeTag.F4 K 0) ∈
        M.map (commutator (reeFixed ReeTag.F4 K 0)).subtype := by
      rw [h]
      exact m.2
    obtain ⟨m₁, hm₁, he⟩ := hm'
    rwa [Subtype.ext he] at hm₁

end TitsData

end Tits

end CFSG.LieType.Simplicity
