module

public import CFSG.CGT.T75Q.F1
public import CFSG.CGT.T75Q.SylowFin
public import CFSG.CGT.T75P.SylowSplit
public import CFSG.CGT.T75P.Inputs

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Std82

variable (s : Std82 T T₁)

include s

theorem normalizer_eq_sup :
    Subgroup.normalizer (T : Set G) =
      hSub T (normIn T₁ T) ⊔ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨h, hh, c, hcC, rfl⟩ := s.hprod g hg
    exact Subgroup.mul_mem_sup hh hcC
  · refine sup_le s.hHN ?_
    intro c hc
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le s.hTH hc)

theorem relIndex_eq_card_C :
    (hSub T (normIn T₁ T)).relIndex (Subgroup.normalizer (T : Set G)) =
      Nat.card (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) := by
  have hfin : Finite G := s.finite
  have hcomm : ∀ a ∈ hSub T (normIn T₁ T), ∀ b ∈ Subgroup.centralizer
      (hSub T (normIn T₁ T) : Set G), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a ha
  have hcard := card_sup_of_commute hcomm s.hinf
  have h1 := Subgroup.relIndex_mul_card (H := hSub T (normIn T₁ T))
    (K := hSub T (normIn T₁ T) ⊔ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))
  rw [inf_of_le_left le_sup_left, hcard] at h1
  rw [s.normalizer_eq_sup]
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := hSub T (normIn T₁ T))) ?_
  rw [h1, mul_comm]

theorem relIndex_T_eq_card_C :
    T.relIndex (Subgroup.centralizer (T : Set G)) =
      Nat.card (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) := by
  rw [← relIndex_normalizer_eq_of_natural s.hTH s.hHN (hSub_data T T₁).2.2 s.hnat]
  exact s.relIndex_eq_card_C

theorem exists_classD_not_mem_ugen {c : G} (hcU : c ∈ Subgroup.centralizer (ugen T : Set G))
    (hc1 : c ≠ 1) : ∃ x ∈ classD T, x ∉ ugen T := by
  by_contra hall
  push Not at hall
  have hnorm : (ugen T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change n ∈ Subgroup.closure (gammaD T) at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      have h1 := classD_conj hx.1 g⁻¹
      have hx' : g * x * g⁻¹ ∈ classD T := by simpa using h1
      exact hall _ hx'
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact (ugen T).mul_mem iha ihb
    | inv a _ iha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact (ugen T).inv_mem iha
  have := s.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ugen T) with h | h
  · obtain ⟨t, ht, ht1⟩ := s.exists_ne_one
    have h2 := s.hTU ht
    rw [h, Subgroup.mem_bot] at h2
    exact ht1 h2
  · exact s.ne_top_of_centralizer hcU hc1 h

theorem false_of_rank_one (hEnd : EndHyp T (ugen T)) {S₁ : Subgroup G}
    (hS₁C : S₁ ≤ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hS₁2 : IsPGroup 2 S₁)
    (hS₁odd : ¬ 2 ∣ (S₁.subgroupOf
      (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))).index) (hne : S₁ ≠ ⊥)
    (hrank : ∀ α ∈ S₁, ∀ β ∈ S₁, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β) : False := by
  classical
  have hfin : Finite G := s.finite
  have : IsSimpleGroup G := s.simple
  set H := hSub T (normIn T₁ T) with hH
  set C : Subgroup G := Subgroup.centralizer (H : Set G) with hC
  have hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h := fun h hh c hc =>
    Subgroup.mem_centralizer_iff.1 hc h hh
  have hinf : H ⊓ C = ⊥ := s.hinf
  have hodd : ¬ 2 ∣ (H ⊔ C).index := by
    rw [← s.normalizer_eq_sup]
    have h := Nat.odd_iff.1 (odd_index_normalizer s.wc)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PH⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  let A : Subgroup G := (PH : Subgroup ↥H).map H.subtype
  have hAmem : ∀ x, x ∈ A ↔ ∃ y : ↥H, y ∈ (PH : Subgroup ↥H) ∧ (y : G) = x := by
    intro x
    simp [A, Subgroup.mem_map]
  have hAH : A ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (hAmem x).1 hx
    exact y.2
  have hAsub : A.subgroupOf H = (PH : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hA2 : IsPGroup 2 A := by
    intro x
    obtain ⟨y, hy, hyx⟩ := (hAmem x.1).1 x.2
    obtain ⟨n, hn⟩ := PH.isPGroup' ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(PH : Subgroup ↥H) => ((z : ↥H) : G)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hyx]
    exact this
  have hAodd : ¬ 2 ∣ (A.subgroupOf H).index := by
    rw [hAsub]
    exact PH.not_dvd_index
  obtain ⟨P, hP⟩ := exists_sylow_of_prod hcomm hinf hodd hAH hS₁C hA2 hAodd hS₁2 hS₁odd
  have hAS : ∀ a ∈ A, ∀ c ∈ S₁, a * c = c * a := fun a ha c hc => hcomm a (hAH ha) c (hS₁C hc)
  have hiAS : A ⊓ S₁ = ⊥ := eq_bot_iff.2 (hinf ▸ inf_le_inf hAH hS₁C)
  refine false_of_sylow_split s.hc.hy.nonab hP.symm hiAS hAS hne hrank ?_
  intro g c hcS hcc hc1 hx
  have hxP : g⁻¹ * c * g ∈ A ⊔ S₁ := hP ▸ hx
  obtain ⟨a, haA, s₁, hs₁, hxas⟩ := exists_mul_of_mem_sup hAS hxP
  by_contra hxS
  have haH : a ∈ H := hAH haA
  have hs₁C : s₁ ∈ C := hS₁C hs₁
  have hcC : c ∈ C := hS₁C hcS
  have hcU : c ∈ Subgroup.centralizer (ugen T : Set G) := by rw [← s.hCeq]; exact hcC
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hxS (by rw [hxas, one_mul]; exact hs₁)
  have hxx : (g⁻¹ * c * g) * (g⁻¹ * c * g) = 1 := by
    calc (g⁻¹ * c * g) * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hcc]; group
  have haa : a * a = 1 := by
    have h1 : a * a * (s₁ * s₁) = 1 := by
      calc a * a * (s₁ * s₁) = (a * s₁) * (a * s₁) := by
            have := hcomm a haH s₁ hs₁C
            calc a * a * (s₁ * s₁) = a * (a * s₁) * s₁ := by group
              _ = a * (s₁ * a) * s₁ := by rw [this]
              _ = (a * s₁) * (a * s₁) := by group
        _ = 1 := by rw [← hxas]; exact hxx
    have h2 : a * a = (s₁ * s₁)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a * a ∈ H ⊓ C :=
      ⟨H.mul_mem haH haH, by rw [h2]; exact C.inv_mem (C.mul_mem hs₁C hs₁C)⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  obtain ⟨d, hdT, hd1, had⟩ := exists_fixed_ne_one
    (two_dvd_card_of_ctx s.hc (by norm_num)) (s.hHN haH) (n := 1)
    (by rw [pow_one, pow_two]; exact haa)
  have hdH : d ∈ H := s.hTH hdT
  have hs₁d : s₁ * d = d * s₁ := (Subgroup.mem_centralizer_iff.1 hs₁C d hdH).symm
  have hxd : (g⁻¹ * c * g) * d = d * (g⁻¹ * c * g) := by
    rw [hxas]
    calc a * s₁ * d = a * (s₁ * d) := by group
      _ = a * (d * s₁) := by rw [hs₁d]
      _ = (a * d) * s₁ := by group
      _ = (d * a) * s₁ := by rw [had]
      _ = d * (a * s₁) := by group
  have hcgd : c * (g * d * g⁻¹) = (g * d * g⁻¹) * c := by
    calc c * (g * d * g⁻¹) = g * ((g⁻¹ * c * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * c * g)) * g⁻¹ := by rw [hxd]
      _ = (g * d * g⁻¹) * c := by group
  have hgdD : g * d * g⁻¹ ∈ classD T :=
    ⟨g⁻¹, d, hdT, hd1, by simp⟩
  have hgdU : g * d * g⁻¹ ∈ ugen T := hEnd.F1 c hcU hc1 _ hgdD hcgd
  have hdD : d ∈ classD T := mem_classD_of_mem hdT hd1
  have hd_g : d ∈ conjSubgroup g⁻¹ (ugen T) := mem_conjSubgroup.2 (by simpa using hgdU)
  have hd_1 : d ∈ conjSubgroup 1 (ugen T) := by
    rw [conjSubgroup_one]
    exact s.hTU hdT
  have hTIa := hEnd.TIa g⁻¹ 1 d hdD hd_g hd_1
  have hxC' : g⁻¹ * c * g ∈ Subgroup.centralizer (conjSubgroup g⁻¹ (ugen T) : Set G) := by
    have := mem_centralizer_conjSubgroup (g := g⁻¹) hcU
    simpa using this
  rw [hTIa, conjSubgroup_one] at hxC'
  have hxC : g⁻¹ * c * g ∈ C := by rw [hC, s.hCeq]; exact hxC'
  have haC : a ∈ C := by
    have : a = (g⁻¹ * c * g) * s₁⁻¹ := by rw [hxas]; group
    rw [this]
    exact C.mul_mem hxC (C.inv_mem hs₁C)
  have : a ∈ H ⊓ C := ⟨haH, haC⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact ha1 this

theorem false_of_sylow_C (hEnd : EndHyp T (ugen T)) {S₁ : Subgroup G}
    (hS₁C : S₁ ≤ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hS₁2 : IsPGroup 2 S₁)
    (hS₁odd : ¬ 2 ∣ (S₁.subgroupOf
      (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))).index) (hne : S₁ ≠ ⊥) : False := by
  have hfin : Finite G := s.finite
  by_cases hrank : ∀ α ∈ S₁, ∀ β ∈ S₁, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β
  · exact s.false_of_rank_one hEnd hS₁C hS₁2 hS₁odd hne hrank
  · push Not at hrank
    obtain ⟨α, hα, β, hβ, hα2, hβ2, hαβ, hα1, hβ1, hne'⟩ := hrank
    have hαC : α ∈ Subgroup.centralizer (ugen T : Set G) := by rw [← s.hCeq]; exact hS₁C hα
    have hβC : β ∈ Subgroup.centralizer (ugen T : Set G) := by rw [← s.hCeq]; exact hS₁C hβ
    obtain ⟨x, hx, hxY⟩ := s.exists_classD_not_mem_ugen hαC hα1
    exact endgame_false hEnd ⟨x, hx, hxY⟩ hαC hβC hα2 hβ2 hα1 hβ1 hne' hαβ

theorem odd_relIndex (hEnd : EndHyp T (ugen T)) :
    Odd (T.relIndex (Subgroup.centralizer (T : Set G))) := by
  classical
  by_contra hev
  have hfin : Finite G := s.finite
  set C : Subgroup G := Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) with hC
  have h2 : 2 ∣ Nat.card C := by
    rw [hC, ← s.relIndex_T_eq_card_C]
    rcases Nat.even_or_odd (T.relIndex (Subgroup.centralizer (T : Set G))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  let S₁ : Subgroup G := (P : Subgroup ↥C).map C.subtype
  have hS₁C : S₁ ≤ C := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hS₁2 : IsPGroup 2 S₁ := P.isPGroup'.map C.subtype
  have hsub : S₁.subgroupOf C = (P : Subgroup ↥C) :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hS₁odd : ¬ 2 ∣ (S₁.subgroupOf C).index := by
    rw [hsub]
    exact P.not_dvd_index
  have hne : S₁ ≠ ⊥ := by
    intro hbot
    have h1 : (P : Subgroup ↥C) = ⊥ := by
      rw [← hsub, hbot, Subgroup.bot_subgroupOf]
    have h3 := P.not_dvd_index
    rw [h1, Subgroup.index_bot] at h3
    exact h3 h2
  exact s.false_of_sylow_C hEnd hS₁C hS₁2 hS₁odd hne

end Std82

section Certified



theorem odd82_of_inputs (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) : Odd82 := by
  intro G _ T T₁ hy hq hT hnat
  have hc := sec6Ctx_of_natural h214 hInv hIso hy hq hT hnat
  have s : Std82 T T₁ := ⟨h1, h62, h63, h66, hc, hnat⟩
  exact s.odd_relIndex (s.endHyp h215 hL)

end Certified

end CFSG.CGT.T75Q
