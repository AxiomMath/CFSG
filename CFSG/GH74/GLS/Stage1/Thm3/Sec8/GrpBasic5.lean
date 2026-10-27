module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Lemma87

variable {G : Type*} [Group G]

theorem subgroup_le_or_of_le_union {H K₁ K₂ : Subgroup G} (h : ∀ x ∈ H, x ∈ K₁ ∨ x ∈ K₂) :
    H ≤ K₁ ∨ H ≤ K₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn₁, hn₂⟩ := hcon
  rw [IsConcreteLE.not_le_iff_exists] at hn₁ hn₂
  obtain ⟨x, hxH, hx₁⟩ := hn₁
  obtain ⟨y, hyH, hy₂⟩ := hn₂
  have hx₂ : x ∈ K₂ := (h x hxH).resolve_left hx₁
  have hy₁ : y ∈ K₁ := (h y hyH).resolve_right hy₂
  rcases h (x * y) (mul_mem hxH hyH) with hxy | hxy
  · apply hx₁
    have := mul_mem hxy (inv_mem hy₁)
    simpa using this
  · apply hy₂
    have := mul_mem (inv_mem hx₂) hxy
    simpa using this

theorem elem_eq_or_of_le [Finite G] {Y E₁ E₂ E' : Subgroup G} (hE'Y : E' ≤ Y)
    (hE'sq : ∀ x ∈ E', x * x = 1) (hinvol : ∀ x ∈ Y, x * x = 1 → x ∈ E₁ ∨ x ∈ E₂)
    (hE₁ : Nat.card ↥E₁ = 16) (hE₂ : Nat.card ↥E₂ = 16) (hE' : Nat.card ↥E' = 16) :
    E' = E₁ ∨ E' = E₂ := by
  rcases subgroup_le_or_of_le_union (fun x hx => hinvol x (hE'Y hx) (hE'sq x hx)) with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge h (by omega)
  · right
    exact Subgroup.eq_of_le_of_card_ge h (by omega)

theorem swap_contradiction [Finite G] {Y E₁ E₂ U C : Subgroup G} {s y : G}
    (hE₁Y : E₁ ≤ Y) (hE₂Y : E₂ ≤ Y) (hE₁sq : ∀ e ∈ E₁, e * e = 1)
    (hE₁c : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) (hE₂c : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a)
    (hint : E₁ ⊓ E₂ = U) (hinvol : ∀ x ∈ Y, x * x = 1 → x ∈ E₁ ∨ x ∈ E₂)
    (hcomm : ∀ e ∈ E₁, ∀ f ∈ E₂, e * f * e⁻¹ * f⁻¹ ∈ U)
    (hs2 : s * s = 1) (hswap : ∀ x, x ∈ E₂ ↔ s * x * s⁻¹ ∈ E₁) (hUs : ∀ c ∈ U, s * c * s⁻¹ ∈ U)
    (hUC : U ≤ C) (hCcen : ∀ c ∈ C, ∀ x ∈ U, c * x = x * c)
    (hm : ∀ e ∈ E₁, e * (s⁻¹ * e * s) ∈ C) (hCcard : Nat.card ↥C ≤ 16)
    (hE₁card : Nat.card ↥E₁ = 16) (hUcard : Nat.card ↥U = 4)
    (hyC : y ∈ C) (hy2 : y * y = 1) (hyU : y ∉ U) : False := by
  have hUE₁ : U ≤ E₁ := hint ▸ inf_le_left
  have hUE₂ : U ≤ E₂ := hint ▸ inf_le_right
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hUsq : ∀ c ∈ U, c * c = 1 := fun c hc => hE₁sq c (hUE₁ hc)
  have he' : ∀ e ∈ E₁, s⁻¹ * e * s ∈ E₂ := by
    intro e he
    rw [hswap]
    have : s * (s⁻¹ * e * s) * s⁻¹ = e := by group
    rw [this]
    exact he
  have hUcen₁ : ∀ c ∈ U, ∀ e ∈ E₁, c * e = e * c := fun c hc e he => hE₁c c (hUE₁ hc) e he
  have hUcen₂ : ∀ c ∈ U, ∀ f ∈ E₂, c * f = f * c := fun c hc f hf => hE₂c c (hUE₂ hc) f hf
  obtain ⟨m, hmdef⟩ : ∃ m : G → G, ∀ e, m e = e * (s⁻¹ * e * s) := ⟨_, fun _ => rfl⟩
  have hmC : ∀ e ∈ E₁, m e ∈ C := fun e he => by rw [hmdef]; exact hm e he
  have hmY : ∀ e ∈ E₁, m e ∈ Y := fun e he => by
    rw [hmdef]
    exact mul_mem (hE₁Y he) (hE₂Y (he' e he))
  have hmcen : ∀ c ∈ U, ∀ e ∈ E₁, c * m e = m e * c := by
    intro c hc e he
    rw [hmdef]
    calc c * (e * (s⁻¹ * e * s)) = (c * e) * (s⁻¹ * e * s) := by group
      _ = (e * c) * (s⁻¹ * e * s) := by rw [hUcen₁ c hc e he]
      _ = e * (c * (s⁻¹ * e * s)) := by group
      _ = e * ((s⁻¹ * e * s) * c) := by rw [hUcen₂ c hc _ (he' e he)]
      _ = e * (s⁻¹ * e * s) * c := by group
  have hmU : ∀ e ∈ E₁, m e ∈ U ↔ e ∈ U := by
    intro e he
    constructor
    · intro hU
      have h1 : s⁻¹ * e * s = e⁻¹ * m e := by rw [hmdef]; group
      have h2 : s⁻¹ * e * s ∈ E₁ := by
        rw [h1]
        exact mul_mem (inv_mem he) (hUE₁ hU)
      have h3 : s⁻¹ * e * s ∈ U := by
        rw [← hint]
        exact Subgroup.mem_inf.2 ⟨h2, he' e he⟩
      have h4 := hUs _ h3
      have : s * (s⁻¹ * e * s) * s⁻¹ = e := by group
      rwa [this] at h4
    · intro hU
      have h1 : s⁻¹ * e * s ∈ U := by
        have := hUs e hU
        rw [hsinv] at this ⊢
        exact this
      rw [hmdef]
      exact mul_mem hU h1
  have hmmul : ∀ e ∈ E₁, ∀ f ∈ E₁, ∃ c ∈ U, m e * m f = c * m (e * f) := by
    intro e he f hf
    have hc1 : f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹ ∈ U := hcomm f hf _ (he' e he)
    refine ⟨(f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹, inv_mem hc1, ?_⟩
    have hce : (f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹ * e =
        e * (f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹ :=
      hUcen₁ _ (inv_mem hc1) e he
    rw [hmdef, hmdef, hmdef]
    calc e * (s⁻¹ * e * s) * (f * (s⁻¹ * f * s))
        = e * ((f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹ * (f * (s⁻¹ * e * s))) *
            (s⁻¹ * f * s) := by group
      _ = (e * (f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹) * (f * (s⁻¹ * e * s)) *
            (s⁻¹ * f * s) := by group
      _ = ((f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹ * e) * (f * (s⁻¹ * e * s)) *
            (s⁻¹ * f * s) := by rw [hce]
      _ = (f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹)⁻¹ * (e * f * (s⁻¹ * (e * f) * s)) := by group
  have hnot : ∀ e ∈ E₁, e ∉ U → ¬ (m e * m e = 1) := by
    intro e he heU hsq
    have hme : m e ∈ Y := hmY e he
    have hmU' : m e ∉ U := fun h => heU ((hmU e he).1 h)
    rcases hinvol _ hme hsq with h1 | h1
    · have h2 : s⁻¹ * e * s ∈ E₁ := by
        have : s⁻¹ * e * s = e⁻¹ * m e := by rw [hmdef]; group
        rw [this]
        exact mul_mem (inv_mem he) h1
      apply heU
      have h3 : s⁻¹ * e * s ∈ U := by
        rw [← hint]
        exact Subgroup.mem_inf.2 ⟨h2, he' e he⟩
      have h4 := hUs _ h3
      have : s * (s⁻¹ * e * s) * s⁻¹ = e := by group
      rwa [this] at h4
    · have h2 : e ∈ E₂ := by
        have : e = m e * (s⁻¹ * e * s)⁻¹ := by rw [hmdef]; group
        rw [this]
        exact mul_mem h1 (inv_mem (he' e he))
      exact heU (by rw [← hint]; exact Subgroup.mem_inf.2 ⟨he, h2⟩)
  have hUCn : (U.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxU : (x : G) ∈ U := hx
    have : (g : G) * (x : G) * (g : G)⁻¹ = x := by
      rw [hCcen g g.2 x hxU]
      group
    show ((g * x * g⁻¹ : ↥C) : G) ∈ U
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
    exact hxU
  let φ₀ : ↥E₁ → ↥C ⧸ U.subgroupOf C := fun e => QuotientGroup.mk (⟨m e, hmC e e.2⟩ : ↥C)
  have hφmul : ∀ e f : ↥E₁, φ₀ (e * f) = φ₀ e * φ₀ f := by
    intro e f
    obtain ⟨c, hc, hef⟩ := hmmul e e.2 f f.2
    have hefE : ((e * f : ↥E₁) : G) ∈ E₁ := (e * f).2
    have key : (m ((e * f : ↥E₁) : G))⁻¹ * (m (e : G) * m (f : G)) ∈ U := by
      have hcen := hmcen c hc ((e * f : ↥E₁) : G) hefE
      have h1 : m (e : G) * m (f : G) = c * m ((e * f : ↥E₁) : G) := by
        have : ((e * f : ↥E₁) : G) = (e : G) * (f : G) := rfl
        rw [this]
        exact hef
      have h2 : (m ((e * f : ↥E₁) : G))⁻¹ * (m (e : G) * m (f : G)) = c := by
        rw [h1, hcen]
        group
      rw [h2]
      exact hc
    show QuotientGroup.mk (⟨m ((e * f : ↥E₁) : G), hmC _ (e * f).2⟩ : ↥C) =
      QuotientGroup.mk (⟨m (e : G), hmC e e.2⟩ : ↥C) * QuotientGroup.mk (⟨m (f : G), hmC f f.2⟩ : ↥C)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using key
  let φ : ↥E₁ →* ↥C ⧸ U.subgroupOf C := MonoidHom.mk' φ₀ hφmul
  have hker : φ.ker = U.subgroupOf E₁ := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (⟨m (e : G), hmC e e.2⟩ : ↥C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hmU e e.2
  have hkerc : Nat.card φ.ker = 4 := by
    rw [hker]
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUE₁).toEquiv
    rw [this, hUcard]
  have hrange : Nat.card φ.range = 4 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hkerc, hE₁card] at h1
    omega
  have hUCc : Nat.card (U.subgroupOf C) = 4 := by
    rw [← hUcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
  have hqc : Nat.card (↥C ⧸ U.subgroupOf C) ≤ 4 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf C)
    rw [hUCc] at h1
    have h2 : (U.subgroupOf C).index = Nat.card (↥C ⧸ U.subgroupOf C) := rfl
    omega
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have := Subgroup.card_le_card_group φ.range
    omega
  have hyq : (QuotientGroup.mk (⟨y, hyC⟩ : ↥C) : ↥C ⧸ U.subgroupOf C) ∈ φ.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨e, he⟩ := hyq
  have hmem : (m (e : G))⁻¹ * y ∈ U := by
    have h1 : (QuotientGroup.mk (⟨m (e : G), hmC e e.2⟩ : ↥C) : ↥C ⧸ U.subgroupOf C) =
        QuotientGroup.mk (⟨y, hyC⟩ : ↥C) := he
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hy_eq : y = m (e : G) * ((m (e : G))⁻¹ * y) := by group
  by_cases heU : (e : G) ∈ U
  · apply hyU
    rw [hy_eq]
    exact mul_mem ((hmU e e.2).2 heU) hmem
  · apply hnot e e.2 heU
    have hcsq := hUsq _ hmem
    have hcen := hmcen _ hmem e e.2
    have h1 : (m (e : G) * ((m (e : G))⁻¹ * y)) * (m (e : G) * ((m (e : G))⁻¹ * y)) =
        m (e : G) * m (e : G) := by
      calc (m (e : G) * ((m (e : G))⁻¹ * y)) * (m (e : G) * ((m (e : G))⁻¹ * y))
          = m (e : G) * (((m (e : G))⁻¹ * y) * m (e : G)) * ((m (e : G))⁻¹ * y) := by group
        _ = m (e : G) * (m (e : G) * ((m (e : G))⁻¹ * y)) * ((m (e : G))⁻¹ * y) := by rw [hcen]
        _ = m (e : G) * m (e : G) * (((m (e : G))⁻¹ * y) * ((m (e : G))⁻¹ * y)) := by group
        _ = m (e : G) * m (e : G) := by rw [hcsq, mul_one]
    rw [← h1, ← hy_eq]
    exact hy2

end Lemma87

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
