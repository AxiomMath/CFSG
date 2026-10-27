module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Ctx

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

theorem centralizer_comm {c : G} (hc : c ∈ centralizer ({z} : Set G)) : c * z = z * c :=
  Subgroup.mem_centralizer_singleton_iff.1 hc

theorem z_mem_centralizer : z ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

@[expose] def IsPair (K₁ K₂ Ka Kb : Subgroup G) : Prop :=
  (Ka = K₁ ∧ Kb = K₂) ∨ (Ka = K₂ ∧ Kb = K₁)

theorem IsPair.left {K₁ K₂ Ka Kb : Subgroup G} (hp : IsPair K₁ K₂ Ka Kb) :
    Ka = K₁ ∨ Ka = K₂ := by
  rcases hp with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

theorem IsPair.right {K₁ K₂ Ka Kb : Subgroup G} (hp : IsPair K₁ K₂ Ka Kb) :
    Kb = K₁ ∨ Kb = K₂ := by
  rcases hp with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr h
  · exact Or.inl h

theorem IsPair.symm {K₁ K₂ Ka Kb : Subgroup G} (hp : IsPair K₁ K₂ Ka Kb) :
    IsPair K₁ K₂ Kb Ka := by
  rcases hp with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem isPair_of_comp {K₁ K₂ K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    ∃ K', IsPair K₁ K₂ K K' := by
  rcases hK with rfl | rfl
  · exact ⟨K₂, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨K₁, Or.inr ⟨rfl, rfl⟩⟩

namespace M4

theorem K_le_C (h : M4 O FA SD z S K₁ K₂) : K₁ ⊔ K₂ ≤ centralizer ({z} : Set G) :=
  sup_le h.K₁_le h.K₂_le

theorem n₂₁ (h : M4 O FA SD z S K₁ K₂) : K₂ ≤ normalizer (K₁ : Set G) := fun _ hb => (h.cs₁ hb).1

theorem n₁₂ (h : M4 O FA SD z S K₁ K₂) : K₁ ≤ normalizer (K₂ : Set G) := fun _ ha => (h.cs₂ ha).1

theorem mem_sup (h : M4 O FA SD z S K₁ K₂) {x : G} (hx : x ∈ K₁ ⊔ K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b :=
  mem_sup_of_le_normalizer h.n₁₂ hx

theorem conj_comp₁ (h : M4 O FA SD z S K₁ K₂) {x : G} (hx : x ∈ K₁ ⊔ K₂) {n : G} (hn : n ∈ K₁) :
    x * n * x⁻¹ ∈ K₁ :=
  (Subgroup.mem_normalizer_iff.1 ((sup_le Subgroup.le_normalizer h.n₂₁ : K₁ ⊔ K₂ ≤ _) hx) n).1 hn

theorem conj_comp₂ (h : M4 O FA SD z S K₁ K₂) {x : G} (hx : x ∈ K₁ ⊔ K₂) {n : G} (hn : n ∈ K₂) :
    x * n * x⁻¹ ∈ K₂ :=
  (Subgroup.mem_normalizer_iff.1 ((sup_le h.n₁₂ Subgroup.le_normalizer : K₁ ⊔ K₂ ≤ _) hx) n).1 hn

theorem Kb_le_secCent (h : M4 O FA SD z S K₁ K₂) {Ka Kb : Subgroup G} (hp : IsPair K₁ K₂ Ka Kb) :
    Kb ≤ secCent Ka (O Ka) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.cs₁
  · exact h.cs₂

theorem C_norm_K (h : M4 O FA SD z S K₁ K₂) {c : G} (hc : c ∈ centralizer ({z} : Set G))
    {k : G} (hk : k ∈ K₁ ⊔ K₂) : c * k * c⁻¹ ∈ K₁ ⊔ K₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_sup hk
  have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
  rw [e]
  rcases h.perm c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ha' : c * a * c⁻¹ ∈ K₁ := by
      have : a ∈ cj K₁ c := by rw [h1]; exact ha
      simpa using this
    have hb' : c * b * c⁻¹ ∈ K₂ := by
      have : b ∈ cj K₂ c := by rw [h2]; exact hb
      simpa using this
    exact mul_mem (mem_sup_left ha') (mem_sup_right hb')
  · have ha' : c * a * c⁻¹ ∈ K₂ := by
      have : a ∈ cj K₂ c := by rw [h2]; exact ha
      simpa using this
    have hb' : c * b * c⁻¹ ∈ K₁ := by
      have : b ∈ cj K₁ c := by rw [h1]; exact hb
      simpa using this
    exact mul_mem (mem_sup_right ha') (mem_sup_left hb')

theorem C_norm_K' (h : M4 O FA SD z S K₁ K₂) {c : G} (hc : c ∈ centralizer ({z} : Set G))
    {k : G} (hk : k ∈ K₁ ⊔ K₂) : c⁻¹ * k * c ∈ K₁ ⊔ K₂ := by
  have := h.C_norm_K (inv_mem hc) hk
  simpa using this

theorem C_norm_OK [Finite G] (h : M4 O FA SD z S K₁ K₂) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) {n : G}
    (hn : n ∈ O (K₁ ⊔ K₂)) : c * n * c⁻¹ ∈ O (K₁ ⊔ K₂) :=
  h.coreK.conj_mem (fun _ hx => h.C_norm_K hc hx) (fun _ hx => h.C_norm_K' hc hx) hn

theorem conj_core (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {x : G}
    (hx : x ∈ K₁ ⊔ K₂) {m : G} (hm : m ∈ O K) : x * m * x⁻¹ ∈ O K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_sup hx
  have e : a * b * m * (a * b)⁻¹ = a * (b * m * b⁻¹) * a⁻¹ := by group
  rw [e]
  rcases hK with rfl | rfl
  · have h1 : b * m * b⁻¹ ∈ O K := (Subgroup.mem_normalizer_iff.1 (h.cs₁ hb).2.1 m).1 hm
    exact (h.core K (Or.inl rfl)).normal a ha _ h1
  · have h1 : b * m * b⁻¹ ∈ O K := (h.core K (Or.inr rfl)).normal b hb m hm
    exact (Subgroup.mem_normalizer_iff.1 (h.cs₂ ha).2.1 _).1 h1

theorem comp_le (_h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    K ≤ K₁ ⊔ K₂ := by
  rcases hK with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem O_le_OK (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    O K ≤ O (K₁ ⊔ K₂) :=
  h.coreK.max (O K) ((h.core K hK).le.trans (h.comp_le hK))
    (fun _ hx _ hm => h.conj_core hK hx hm) (h.core K hK).odd

theorem inf_OK_le (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    K ⊓ O (K₁ ⊔ K₂) ≤ O K := by
  refine (h.core K hK).max _ inf_le_left (fun x hx m hm => ⟨K.mul_mem (K.mul_mem hx hm.1)
    (K.inv_mem hx), h.coreK.normal x (h.comp_le hK hx) m hm.2⟩) ?_
  exact Odd.of_dvd_nat h.coreK.odd (Subgroup.card_dvd_of_le inf_le_right)

theorem z_pgroup (h : M4 O FA SD z S K₁ K₂) : IsPGroup 2 ↥(zpowers z) :=
  isPGroup_zpowers_of_sq h.z_sq h.z_ne

theorem S_pgroup (h : M4 O FA SD z S K₁ K₂) : IsPGroup 2 ↥S := h.S_syl.2.1

theorem S_inf_OK [Finite G] (h : M4 O FA SD z S K₁ K₂) : S ⊓ O (K₁ ⊔ K₂) = ⊥ :=
  inf_eq_bot_of_pgroup_odd h.S_pgroup h.coreK.odd

theorem comm_of_S [Finite G] (h : M4 O FA SD z S K₁ K₂) {a b : G} (ha : a ∈ K₁) (hb : b ∈ K₂)
    (haS : a ∈ S) (hbS : b ∈ S) : a * b = b * a := by
  have hc : ⁅a, b⁆ ∈ O K₁ := (h.cs₁ hb).2.2 a ha
  have hOK : ⁅a, b⁆ ∈ O (K₁ ⊔ K₂) := h.O_le_OK (Or.inl rfl) hc
  have hS : ⁅a, b⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem haS hbS) (inv_mem haS)) (inv_mem hbS)
  have h1 : ⁅a, b⁆ ∈ S ⊓ O (K₁ ⊔ K₂) := ⟨hS, hOK⟩
  rw [h.S_inf_OK, Subgroup.mem_bot, commutatorElement_def] at h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem comm_of_S' [Finite G] (h : M4 O FA SD z S K₁ K₂) {Ka Kb : Subgroup G}
    (hp : IsPair K₁ K₂ Ka Kb) {a b : G} (ha : a ∈ Ka) (hb : b ∈ Kb) (haS : a ∈ S) (hbS : b ∈ S) :
    a * b = b * a := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.comm_of_S ha hb haS hbS
  · exact (h.comm_of_S hb ha hbS haS).symm

theorem z_mem_S [Finite G] (h : M4 O FA SD z S K₁ K₂) : z ∈ S := by
  obtain ⟨P', hP', hzP'⟩ := exists_syl2In_ge h.z_pgroup (zpowers_le.2 (z_mem_centralizer))
  obtain ⟨c, hc, hcP⟩ := h.S_syl.exists_conj hP'
  have hzP : z ∈ P' := hzP' (Subgroup.mem_zpowers z)
  rw [hcP, mem_cj] at hzP
  have : c * z * c⁻¹ = z := by rw [centralizer_comm hc]; group
  rwa [this] at hzP

theorem inv_ZsK [Finite G] (h : M4 O FA SD z S K₁ K₂) {w : G} (hw : w ∈ ZsM O (K₁ ⊔ K₂))
    (hw2 : w * w = 1) : w = 1 ∨ w = z := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  obtain ⟨W, hW, hwW⟩ := exists_syl2In_ge (isPGroup_zpowers_of_sq hw2 hw1)
    (zpowers_le.2 hw : zpowers w ≤ ZsM O (K₁ ⊔ K₂))
  obtain ⟨c, hc, hcW⟩ := h.hb.exists_conj hW
  have hcC : c ∈ centralizer ({z} : Set G) := h.K_le_C (hc.1)
  have hwW' : w ∈ W := hwW (Subgroup.mem_zpowers w)
  rw [hcW, cj_zpowers_of_comm h.z_sq (centralizer_comm hcC)] at hwW'
  rcases (mem_zpowers_of_sq h.z_sq).1 hwW' with h1 | h1
  · exact absurd h1 hw1
  · exact h1

theorem S_inf_Zs [Finite G] (h : M4 O FA SD z S K₁ K₂) : S ⊓ ZsM O (K₁ ⊔ K₂) = zpowers z := by
  apply le_antisymm
  · intro w hw
    obtain ⟨W, hW, hwW⟩ := exists_syl2In_ge (h.S_pgroup.to_inf_left (K := ZsM O (K₁ ⊔ K₂)))
      (inf_le_right : S ⊓ ZsM O (K₁ ⊔ K₂) ≤ ZsM O (K₁ ⊔ K₂))
    obtain ⟨c, hc, hcW⟩ := h.hb.exists_conj hW
    have hcC : c ∈ centralizer ({z} : Set G) := h.K_le_C (hc.1)
    have hwW' : w ∈ W := hwW hw
    rw [hcW, cj_zpowers_of_comm h.z_sq (centralizer_comm hcC)] at hwW'
    exact hwW'
  · exact le_inf (zpowers_le.2 h.z_mem_S) h.hb.1

theorem Zs_le_ZsK (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    ZsM O K ≤ ZsM O (K₁ ⊔ K₂) := by
  have hKle := h.comp_le hK
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxs := hx.2
  refine ⟨hKle hxK, ?_, ?_, ?_⟩
  · exact Subgroup.le_normalizer (hKle hxK)
  · rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn; exact h.coreK.normal x (hKle hxK) n hn
    · intro hn
      have := h.coreK.normal x⁻¹ (inv_mem (hKle hxK)) _ hn
      simpa [mul_assoc] using this
  · intro k hk
    obtain ⟨hn1, hn2, hcm⟩ := hxs
    obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_sup hk
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have key : ⁅a, x⁆ ∈ O (K₁ ⊔ K₂) ∧ ⁅b, x⁆ ∈ O (K₁ ⊔ K₂) := by
      rcases hK with rfl | rfl
      · refine ⟨h.O_le_OK (Or.inl rfl) (hcm a ha), ?_⟩
        have h1 : ⁅x, b⁆ ∈ O K := (h.cs₁ hb).2.2 x hxK
        have h2 : ⁅b, x⁆ = (⁅x, b⁆)⁻¹ := (commutatorElement_inv x b).symm
        rw [h2]
        exact inv_mem (h.O_le_OK (Or.inl rfl) h1)
      · refine ⟨?_, h.O_le_OK (Or.inr rfl) (hcm b hb)⟩
        have h1 : ⁅x, a⁆ ∈ O K := (h.cs₂ ha).2.2 x hxK
        have h2 : ⁅a, x⁆ = (⁅x, a⁆)⁻¹ := (commutatorElement_inv x a).symm
        rw [h2]
        exact inv_mem (h.O_le_OK (Or.inr rfl) h1)
    exact mul_mem (h.coreK.normal a (mem_sup_left ha) _ key.2) key.1

theorem S_inf_Zs_comp [Finite G] (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : z ∈ K ∧ S ⊓ ZsM O K = zpowers z := by
  obtain ⟨hcard, -⟩ := h.zs K hK
  have hex : ∃ w ∈ S ⊓ ZsM O K, w ≠ 1 := by
    by_contra hne
    push Not at hne
    have : S ⊓ ZsM O K = ⊥ := by
      rw [eq_bot_iff]; intro x hx; exact (Subgroup.mem_bot).2 (hne x hx)
    rw [this] at hcard
    simp at hcard
  obtain ⟨w, hw, hw1⟩ := hex
  have hw2 : w * w = 1 := by
    have := pow_card_eq_one' (G := ↥(S ⊓ ZsM O K)) (x := ⟨w, hw⟩)
    rw [hcard] at this
    have h2 := congrArg Subtype.val this
    simpa [pow_two] using h2
  have hwZ : w ∈ ZsM O (K₁ ⊔ K₂) := h.Zs_le_ZsK hK (hw.2)
  have hwz : w = z := by
    rcases h.inv_ZsK hwZ hw2 with h1 | h1
    · exact absurd h1 hw1
    · exact h1
  have hzmem : z ∈ S ⊓ ZsM O K := hwz ▸ hw
  have hle : zpowers z ≤ S ⊓ ZsM O K := zpowers_le.2 hzmem
  have heq : zpowers z = S ⊓ ZsM O K := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, card_zpowers_of_sq h.z_sq h.z_ne]
  exact ⟨hzmem.2.1, heq.symm⟩

theorem z_mem_comp [Finite G] (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    z ∈ K := (h.S_inf_Zs_comp hK).1

theorem inv_comp [Finite G] (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    {x : G} (hx : x ∈ K) (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  have hz := h.z_mem_comp hK
  have hcomm : x * z = z * x := centralizer_comm (h.K_le_C (h.comp_le hK hx))
  rcases h.rk K hK x hx z hz hx2 h.z_sq hcomm with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.z_ne
  · exact Or.inr h1

end M4

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
