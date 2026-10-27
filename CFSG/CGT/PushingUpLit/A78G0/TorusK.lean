module

public import CFSG.CGT.PushingUpLit.A78G0.Torus
public import CFSG.CGT.PushingUpLit.A78G0.KData

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools Matrix

section Torus

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  {h : G0Core G L₁ L₂ V W Z Z₂ e} {y : G}

theorem Torus₀.exists_comm_eq (hy : Torus₀ h y) {c : G} (hc : c ∈ V) :
    ∃ v ∈ V, y * v * y⁻¹ * v⁻¹ = c := by
  have hVab := h.jst.abelian_V
  have hmem : ∀ v : ↥V, y * (v : G) * y⁻¹ * (v : G)⁻¹ ∈ V := fun v =>
    mul_mem (conj_mem_of_mem_normalizer' hy.mem_V v.2) (inv_mem v.2)
  have hmul : ∀ a b : G, a ∈ V → b ∈ V →
      y * (a * b) * y⁻¹ * (a * b)⁻¹ = (y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
    intro a b ha hb
    have h1 : a⁻¹ * (y * b * y⁻¹) = (y * b * y⁻¹) * a⁻¹ :=
      (hVab _ (inv_mem ha) _ (conj_mem_of_mem_normalizer' hy.mem_V hb)).eq
    have h2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := (hVab _ (inv_mem ha) _ (inv_mem hb)).eq
    calc y * (a * b) * y⁻¹ * (a * b)⁻¹
        = y * a * y⁻¹ * (y * b * y⁻¹) * (b⁻¹ * a⁻¹) := by group
      _ = y * a * y⁻¹ * (y * b * y⁻¹) * (a⁻¹ * b⁻¹) := by rw [h2]
      _ = y * a * y⁻¹ * ((y * b * y⁻¹) * a⁻¹) * b⁻¹ := by group
      _ = y * a * y⁻¹ * (a⁻¹ * (y * b * y⁻¹)) * b⁻¹ := by rw [h1]
      _ = (y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹) := by group
  let ψ : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨y * (v : G) * y⁻¹ * (v : G)⁻¹, hmem v⟩)
    (fun a b => Subtype.ext (hmul a b a.2 b.2))
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : y * (v : G) * y⁻¹ * (v : G)⁻¹ = 1 := congrArg Subtype.val hv
    exact Subtype.ext (hy.cent_V v v.2 (mul_inv_eq_one.1 h1))
  obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.1 hinj ⟨c, hc⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem Torus₀.inf_V (hy : Torus₀ h y) :
    (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  refine hy.cent_V v hv.2 ?_
  have := Subgroup.mem_centralizer_singleton_iff.1 hv.1.2
  rw [← this]
  group

theorem Torus₀.decomp (hy : Torus₀ h y) {l : G} (hl : l ∈ L₁) :
    ∃ v ∈ V, ∃ k ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G), l = v * k := by
  obtain ⟨v, hv, hvc⟩ := hy.exists_comm_eq (hy.comm_L l hl)
  have hk : y * (v⁻¹ * l) * y⁻¹ = v⁻¹ * l := by
    have e1 : y * l * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l := by group
    calc y * (v⁻¹ * l) * y⁻¹ = (y * v⁻¹ * y⁻¹) * (y * l * y⁻¹) := by group
      _ = (y * v⁻¹ * y⁻¹) * ((y * l * y⁻¹ * l⁻¹) * l) := by rw [← e1]
      _ = (y * v⁻¹ * y⁻¹) * ((y * v * y⁻¹ * v⁻¹) * l) := by rw [hvc]
      _ = v⁻¹ * l := by group
  have hkc : (v⁻¹ * l) * y = y * (v⁻¹ * l) := by
    calc (v⁻¹ * l) * y = (y * (v⁻¹ * l) * y⁻¹) * y := by rw [hk]
      _ = y * (v⁻¹ * l) := by group
  refine ⟨v, hv, v⁻¹ * l, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (h.V_le_L hv)) hl,
    Subgroup.mem_centralizer_singleton_iff.2 hkc⟩, by group⟩

theorem Torus₀.sup_V (hy : Torus₀ h y) :
    V ⊔ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) = L₁ := by
  apply le_antisymm
  · exact sup_le h.V_le_L inf_le_left
  · intro l hl
    obtain ⟨v, hv, k, hk, rfl⟩ := hy.decomp hl
    exact Subgroup.mul_mem_sup hv hk

end Torus

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem V_le_normalizer_W : V ≤ Subgroup.normalizer (W : Set G) := fun _ hv =>
  le_normalizer_of_conj' h.jst.conj_V₂ ((le_sup_left : V ≤ V ⊔ W) hv)

theorem inf_V_of_mem_cliq {B : Subgroup G} (hB : B ∈ cliq Z W) : B ⊓ V = ⊥ := by
  obtain ⟨g, hg⟩ := hB.1
  have hg' : B = cs Z g := hg.symm
  have hBZ := hB.2.1
  subst hg'
  exact h.cs_inf_V hBZ

theorem ne_bot_of_mem_cliq {B : Subgroup G} (hB : B ∈ cliq Z W) : B ≠ ⊥ := by
  obtain ⟨g, hg⟩ := hB.1
  have hg' : B = cs Z g := hg.symm
  subst hg'
  intro hbot
  apply h.hZ
  have := card_cs Z g
  rw [hbot, Subgroup.card_bot] at this
  exact Subgroup.card_eq_one.1 this.symm

theorem normalizer_le_W {B : Subgroup G} (hB : B ∈ cliq Z W) {v : G} (hv : v ∈ V)
    (hvB : v ∈ Subgroup.normalizer (B : Set G)) : v ∈ W := by
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h.ne_bot_of_mem_cliq hB ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hbW : b ∈ W := hB.2.2 hbB
  have hbV : b ∉ V := fun hbV => hb1 (by
    have hmem : b ∈ B ⊓ V := ⟨hbB, hbV⟩
    rw [h.inf_V_of_mem_cliq hB] at hmem
    exact Subgroup.mem_bot.1 hmem)
  have hbJ : b ∈ V ⊔ W := Subgroup.mem_sup_right hbW
  have hbL : b ∈ L₁ := h.J_le_L hbJ
  have hcomm : v * b * v⁻¹ = b := by
    have h1 : v * b * v⁻¹ * b⁻¹ ∈ B :=
      mul_mem (conj_mem_of_mem_normalizer' hvB hbB) (inv_mem hbB)
    have h2 : v * b * v⁻¹ * b⁻¹ ∈ V := by
      have : b * v⁻¹ * b⁻¹ ∈ V :=
        conj_mem_of_mem_normalizer' (h.L_le_M hbL) (inv_mem hv)
      have e1 : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
      rw [e1]
      exact mul_mem hv this
    have h3 : v * b * v⁻¹ * b⁻¹ ∈ B ⊓ V := ⟨h1, h2⟩
    rw [h.inf_V_of_mem_cliq hB, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  have hcomm' : b * v * b⁻¹ = v := by
    have e1 : v * b = b * v := by
      calc v * b = (v * b * v⁻¹) * v := by group
        _ = b * v := by rw [hcomm]
    calc b * v * b⁻¹ = v * b * b⁻¹ := by rw [e1]
      _ = v := by group
  by_contra hvW
  obtain ⟨D⟩ := h.pair.side₁.nat
  obtain ⟨fr⟩ := h.pair.side₁.exists_frame D
  have hvN : v ∉ V ⊓ W := fun hmem => hvW hmem.2
  have hd := (fr.mem_N_iff hv).not.1 hvN
  have hfixv : (D.ρ b : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ v = D.κ v := by
    rw [← D.conj b hbL v hv, hcomm']
  have h1 := eq_one_of_fix_two hd (fr.ρ_x₀ hbJ) hfixv
  exact hbV ((D.ρ_eq_one b hbL).1 h1)

theorem cs_mem_cliq {B : Subgroup G} (hB : B ∈ cliq Z W) {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    cs B g ∈ cliq Z W := by
  refine ⟨cs_mem_zClass hB.1 g, ?_, ?_⟩
  · intro hZ'
    apply hB.2.1
    have h1 : B = cs (cs B g) g⁻¹ := (cs_cs_inv B g).symm
    rw [hZ', h.cs_Z_of_mem ((Subgroup.normalizer (V : Set G)).inv_mem hgV)] at h1
    exact h1
  · exact (cs_mono hB.2.2 g).trans (le_of_eq (cs_of_mem_normalizer hgW))

theorem orbit_eq_cliq {B₀ : Subgroup G} (hB₀ : B₀ ∈ cliq Z W) :
    {C : Subgroup G | ∃ x ∈ V, C = cs B₀ x} = cliq Z W := by
  have hsub : {C : Subgroup G | ∃ x ∈ V, C = cs B₀ x} ⊆ cliq Z W := by
    rintro C ⟨x, hx, rfl⟩
    exact h.cs_mem_cliq hB₀ (Subgroup.le_normalizer hx) (h.V_le_normalizer_W hx)
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [h.ncard_cliq_W, ncard_conj_class]
  have hle : (Subgroup.normalizer (B₀ : Set G)).subgroupOf V ≤ (V ⊓ W).subgroupOf V := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.2 ⟨x.2, h.normalizer_le_W hB₀ x.2 hx⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  have hidx : ((V ⊓ W).subgroupOf V).index = 2 ^ e := h.jst.index_V
  rw [hidx] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd

theorem exists_fixed_cliq {y : G} (hy : IsTorus h y) : ∃ B ∈ cliq Z W, cs B y = B := by
  have hne : (cliq Z W).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [h.ncard_cliq_W]
    exact pow_ne_zero _ two_ne_zero
  obtain ⟨B₀, hB₀⟩ := hne
  have hB₀y : cs B₀ y ∈ cliq Z W := h.cs_mem_cliq hB₀ hy.mem_V hy.mem_W
  have horb := h.orbit_eq_cliq hB₀
  rw [← horb] at hB₀y
  obtain ⟨v₀, hv₀, hv₀e⟩ := hB₀y
  obtain ⟨v, hv, hvc⟩ := hy.exists_comm_eq (inv_mem hv₀)
  refine ⟨cs B₀ v, ?_, ?_⟩
  · rw [← horb]
    exact ⟨v, hv, rfl⟩
  · have e2 : y * v = (y * v * y⁻¹) * y := by group
    have e3 : (y * v * y⁻¹) * v₀ = v := by
      have h1 : y * v * y⁻¹ = v₀⁻¹ * v := by
        calc y * v * y⁻¹ = (y * v * y⁻¹ * v⁻¹) * v := by group
          _ = v₀⁻¹ * v := by rw [hvc]
      rw [h1]
      have hcomm : v * v₀ = v₀ * v := (h.jst.abelian_V v hv v₀ hv₀).eq
      calc v₀⁻¹ * v * v₀ = v₀⁻¹ * (v * v₀) := by group
        _ = v₀⁻¹ * (v₀ * v) := by rw [hcomm]
        _ = v := by group
    calc cs (cs B₀ v) y = cs B₀ (y * v) := (cs_mul B₀ y v).symm
      _ = cs B₀ ((y * v * y⁻¹) * y) := by rw [← e2]
      _ = cs (cs B₀ y) (y * v * y⁻¹) := cs_mul B₀ _ _
      _ = cs (cs B₀ v₀) (y * v * y⁻¹) := by rw [hv₀e]
      _ = cs B₀ ((y * v * y⁻¹) * v₀) := (cs_mul B₀ _ _).symm
      _ = cs B₀ v := by rw [e3]

theorem cent_of_fixed {y : G} (hy : IsTorus h y) {B : Subgroup G} (hB : B ∈ cliq Z W)
    (hfix : cs B y = B) : ∀ b ∈ B, y * b * y⁻¹ = b := by
  intro b hb
  have h0 : y * b * y⁻¹ ∈ B := by
    have := conj_mem_cs y hb
    rwa [hfix] at this
  have h1 : y * b * y⁻¹ * b⁻¹ ∈ B := mul_mem h0 (inv_mem hb)
  have hbL : b ∈ L₁ := h.J_le_L (Subgroup.mem_sup_right (hB.2.2 hb))
  have h2 : y * b * y⁻¹ * b⁻¹ ∈ V := hy.comm_L b hbL
  have h3 : y * b * y⁻¹ * b⁻¹ ∈ B ⊓ V := ⟨h1, h2⟩
  rw [h.inf_V_of_mem_cliq hB, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

theorem exists_kData : ∃ (y : G) (A : Subgroup G), IsTorus h y ∧
    KData h (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) A ∧ A ≤ W := by
  obtain ⟨y, hy⟩ := h.exists_isTorus
  obtain ⟨A, hA, hAy⟩ := h.exists_fixed_cliq hy
  have hcent := h.cent_of_fixed hy hA hAy
  have hAK : A ≤ L₁ ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨h.J_le_L (Subgroup.mem_sup_right (hA.2.2 ha)),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := hcent a ha
    calc a * y = (y * a * y⁻¹) * y := by rw [this]
      _ = y * a := by group
  refine ⟨y, A, hy, ⟨inf_le_left, hy.inf_V, hy.sup_V, hAK, ?_, hA.1⟩, hA.2.2⟩
  obtain ⟨g, hg⟩ := hA.1
  have hg' : A = cs Z g := hg.symm
  rw [hg', card_cs, h.card_Z]

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
