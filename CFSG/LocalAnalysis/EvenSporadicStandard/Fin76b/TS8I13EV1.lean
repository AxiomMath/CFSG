module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13R
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Pi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Ker2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem alt5_involution_commute :
    ∀ d : Equiv.Perm (Fin 5), Equiv.Perm.sign d = 1 → d * d = 1 → d ≠ 1 →
      ∃ d' : Equiv.Perm (Fin 5), d' * d' = 1 ∧ d' ≠ 1 ∧ d' ≠ d ∧ d * d' = d' * d ∧
        Equiv.Perm.sign d' = 1 := by
  decide +kernel

theorem mem_klein_zpowers {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {g : G} (hg : g ∈ zpowers a ⊔ zpowers b) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have hN : ∀ n ∈ zpowers a, b * n * b⁻¹ ∈ zpowers a := by
    intro n hn
    rcases mem_zpowers_sq_eq_one ha hn with h | h
    · rw [h]; simp
    · rw [h]
      have : b * a * b⁻¹ = a := by rw [← hab]; group
      rw [this]; exact mem_zpowers a
  obtain ⟨k, hk, h⟩ := mem_sup_zpowers_of_conj hb hN hg
  rcases mem_zpowers_sq_eq_one ha hk with h1 | h1
  · rcases h with h | h
    · exact Or.inl (h.trans h1)
    · exact Or.inr (Or.inr (Or.inl (by rw [h, h1, one_mul])))
  · rcases h with h | h
    · exact Or.inr (Or.inl (h.trans h1))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, h1])))

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem KR_conj_mem {g k : G} (hg : g ∈ c.N1) (hk : k ∈ c.KR) : g⁻¹ * k * g ∈ c.KR := by
  obtain ⟨hkN, hk1⟩ := c.mem_KR.1 hk
  refine c.mem_KR.2 ⟨mul_mem (mul_mem (inv_mem hg) hkN) hg, ?_⟩
  show c.rho ((⟨g, hg⟩ : ↥c.N1)⁻¹ * ⟨k, hkN⟩ * ⟨g, hg⟩) = 1
  rw [map_mul, map_mul, map_inv, hk1]
  simp

theorem exists_klein_pi {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    {d : Equiv.Perm (Fin 5)} (hdA : Equiv.Perm.sign d = 1) (hd2 : d * d = 1) (hd1 : d ≠ 1) :
    ∃ b₁ b₂ : G, ∃ hb₁ : b₁ ∈ B, ∃ hb₂ : b₂ ∈ B, b₁ * b₁ = 1 ∧ b₂ * b₂ = 1 ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ ∧ π (c.kappa ⟨b₁, hb₁⟩) = d := by
  obtain ⟨d', hd'2, hd'1, hd'd, hcomm, hd'A⟩ := alt5_involution_commute d hdA hd2 hd1
  obtain ⟨β₁, hβ₁⟩ := c.exists_pi_kappa hπ (Equiv.Perm.mem_alternatingGroup.2 hdA)
  obtain ⟨β₂, hβ₂⟩ := c.exists_pi_kappa hπ (Equiv.Perm.mem_alternatingGroup.2 hd'A)
  have hF := c.pi_kappa_injective hπ
  have hβ₁' : (π.comp c.kappa) β₁ = d := hβ₁
  have hβ₂' : (π.comp c.kappa) β₂ = d' := hβ₂
  have h11 : β₁ * β₁ = 1 := hF (by rw [map_mul, map_one, hβ₁']; exact hd2)
  have h22 : β₂ * β₂ = 1 := hF (by rw [map_mul, map_one, hβ₂']; exact hd'2)
  have h12 : β₁ * β₂ = β₂ * β₁ := hF (by rw [map_mul, map_mul, hβ₁', hβ₂']; exact hcomm)
  have n1 : β₁ ≠ 1 := fun h => hd1 (by rw [← hβ₁', h, map_one])
  have n2 : β₂ ≠ 1 := fun h => hd'1 (by rw [← hβ₂', h, map_one])
  have n3 : β₁ ≠ β₂ := fun h => hd'd (by rw [← hβ₂', ← h, hβ₁'])
  exact ⟨(β₁ : G), (β₂ : G), β₁.2, β₂.2, congrArg Subtype.val h11, congrArg Subtype.val h22,
    congrArg Subtype.val h12, fun h => n1 (Subtype.ext h), fun h => n2 (Subtype.ext h),
    fun h => n3 (Subtype.ext h), hβ₁⟩

@[expose] noncomputable def QB1 (b₁ b₂ : G) : Subgroup G := c.Qs ⊔ (zpowers b₁ ⊔ zpowers b₂)

section QB1

variable {b₁ b₂ : G}

theorem Qs_le_QB1 : c.Qs ≤ c.QB1 b₁ b₂ := le_sup_left

theorem B1_le_QB1 : zpowers b₁ ⊔ zpowers b₂ ≤ c.QB1 b₁ b₂ := le_sup_right

theorem Zs_le_QB1 : c.Zs ≤ c.QB1 b₁ b₂ := c.Zs_le_Qs.trans c.Qs_le_QB1

theorem B1_le_N1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : zpowers b₁ ⊔ zpowers b₂ ≤ c.N1 :=
  sup_le (zpowers_le.2 (c.B_le_N1 hb₁)) (zpowers_le.2 (c.B_le_N1 hb₂))

theorem QB1_le_N1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : c.QB1 b₁ b₂ ≤ c.N1 :=
  sup_le c.Qs_le_N1 (c.B1_le_N1 hb₁ hb₂)

theorem B_conj_Qs {b : G} (hb : b ∈ B) {q : G} (hq : q ∈ c.Qs) : b * q * b⁻¹ ∈ c.Qs :=
  (c.mem_Nc.1 (c.B_le_Nc hb) q).1 hq

theorem QB1_pgroup (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1) (h22 : b₂ * b₂ = 1)
    (h12 : b₁ * b₂ = b₂ * b₁) : IsPGroup 2 (c.QB1 b₁ b₂) := by
  have hK2 : IsPGroup 2 (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    show (g : G) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    rcases mem_klein_zpowers h11 h22 h12 g.2 with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact h11
    · rw [h]; exact h22
    · rw [h]
      calc b₁ * b₂ * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
        _ = b₁ * (b₁ * b₂) * b₂ := by rw [h12]
        _ = (b₁ * b₁) * (b₂ * b₂) := by group
        _ = 1 := by rw [h11, h22, one_mul]
  have hKN : (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) ≤ normalizer (c.Qs : Set G) :=
    sup_le (zpowers_le.2 (c.B_le_Nc hb₁)) (zpowers_le.2 (c.B_le_Nc hb₂))
  have := hK2.to_sup_of_normal_right' c.Qs_pgroup hKN
  rw [sup_comm] at this
  exact this

theorem mem_QB1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1) (h22 : b₂ * b₂ = 1)
    (h12 : b₁ * b₂ = b₂ * b₁) {y : G} (hy : y ∈ c.QB1 b₁ b₂) :
    ∃ q ∈ c.Qs, ∃ b : G, (b = 1 ∨ b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) ∧ y = q * b := by
  have hS : c.QB1 b₁ b₂ = (c.Qs ⊔ zpowers b₁) ⊔ zpowers b₂ := by rw [QB1, sup_assoc]
  rw [hS] at hy
  have hN2 : ∀ n ∈ c.Qs ⊔ zpowers b₁, b₂ * n * b₂⁻¹ ∈ c.Qs ⊔ zpowers b₁ := by
    intro n hn
    have hle : c.Qs ⊔ zpowers b₁ ≤
        (c.Qs ⊔ zpowers b₁).comap (MulAut.conj b₂).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (fun u hu => ?_)
      · refine Subgroup.mem_comap.2 (mem_sup_left ?_)
        simpa [MulAut.conj_apply] using c.B_conj_Qs hb₂ hq
      · apply Subgroup.mem_comap.2
        rcases mem_zpowers_sq_eq_one h11 hu with h | h
        · rw [h]; simp
        · rw [h]
          have : b₂ * b₁ * b₂⁻¹ = b₁ := by rw [← h12]; group
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [this]
          exact mem_sup_right (mem_zpowers b₁)
    have := hle hn
    simpa [MulAut.conj_apply] using this
  obtain ⟨k, hk, h⟩ := mem_sup_zpowers_of_conj h22 hN2 hy
  obtain ⟨q, hq, h'⟩ := mem_sup_zpowers_of_conj h11 (fun n hn => c.B_conj_Qs hb₁ hn) hk
  rcases h with h | h
  · rcases h' with h' | h'
    · exact ⟨q, hq, 1, Or.inl rfl, by rw [h, h', mul_one]⟩
    · exact ⟨q, hq, b₁, Or.inr (Or.inl rfl), by rw [h, h']⟩
  · rcases h' with h' | h'
    · exact ⟨q, hq, b₂, Or.inr (Or.inr (Or.inl rfl)), by rw [h, h']⟩
    · exact ⟨q, hq, b₁ * b₂, Or.inr (Or.inr (Or.inr rfl)), by rw [h, h', mul_assoc]⟩

end QB1

@[expose] noncomputable def ThetaS (Y : Subgroup G) : Subgroup G :=
  ((c.Rhat Y).comap c.rho).map c.N1.subtype

theorem mem_ThetaS {Y : Subgroup G} {x : G} :
    x ∈ c.ThetaS Y ↔ ∃ h : x ∈ c.N1, c.rho ⟨x, h⟩ ∈ c.Rhat Y := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem ThetaS_le_N1 {Y : Subgroup G} : c.ThetaS Y ≤ c.N1 := fun _ hx => (c.mem_ThetaS.1 hx).1

theorem le_ThetaS {Y : Subgroup G} (hY : Y ≤ c.N1) : Y ≤ c.ThetaS Y := fun x hx =>
  c.mem_ThetaS.2 ⟨hY hx, c.mem_Rhat.2 ⟨⟨x, hY hx⟩, hx, rfl⟩⟩

variable {c}

namespace IsRs

variable {Rs : Subgroup G}

theorem inf_KR_le_of_pgroup (hR : c.IsRs Rs) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ c.N1) : P ⊓ c.KR ≤ c.Zs := by
  classical
  have hRmax : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ c.N1 → Rs ⊓ c.N1 ≤ R' →
      R' ≤ Rs ⊓ c.N1 :=
    max_of_odd_relIndex hR.R_pgroup hR.R_odd
  obtain ⟨M, ⟨hM2, hMN, hPM⟩, hMmax⟩ :=
    (Set.toFinite {M : Subgroup G | IsPGroup 2 M ∧ M ≤ c.N1 ∧ P ≤ M}).exists_maximalFor id _
      ⟨P, hP, hPN, le_rfl⟩
  have hMmax' : ∀ M' : Subgroup G, IsPGroup 2 M' → M' ≤ c.N1 → M ≤ M' → M' ≤ M :=
    fun M' hM' hM'N hMM' => hMmax ⟨hM', hM'N, hPM.trans hMM'⟩ hMM'
  obtain ⟨g, hgN, hg⟩ := sylow_conj (inf_le_right : Rs ⊓ c.N1 ≤ c.N1) hMN hR.R_pgroup hM2
    hRmax hMmax'
  rintro k ⟨hkP, hkK⟩
  have hgk : g⁻¹ * k * g ∈ Rs ⊓ c.N1 := (hg k).1 (hPM hkP)
  have hZ : g⁻¹ * k * g ∈ c.Zs := hR.R_inf_KR_le ⟨hgk, c.KR_conj_mem hgN hkK⟩
  have h1 := c.Zs_comm_N1 hZ hgN
  have h2 : k * g = (g⁻¹ * k * g) * g := by
    calc k * g = g * (g⁻¹ * k * g) := by group
      _ = (g⁻¹ * k * g) * g := h1
  have h3 : k = g⁻¹ * k * g := mul_right_cancel h2
  rw [h3]
  exact hZ

theorem ThetaS_max (hR : c.IsRs Rs) {Y : Subgroup G} (hZY : c.Zs ≤ Y) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPT : P ≤ c.ThetaS Y) (hYP : Y ≤ P) : P ≤ Y := by
  intro p hp
  have hPN : P ≤ c.N1 := fun x hx => c.ThetaS_le_N1 (hPT hx)
  obtain ⟨hpN, hρp⟩ := c.mem_ThetaS.1 (hPT hp)
  obtain ⟨r, hrY, hrρ⟩ := c.mem_Rhat.1 hρp
  have hkK : p * (r : G)⁻¹ ∈ c.KR := by
    refine c.mem_KR.2 ⟨mul_mem hpN (inv_mem r.2), ?_⟩
    show c.rho (⟨p, hpN⟩ * r⁻¹) = 1
    rw [map_mul, map_inv, hrρ, mul_inv_cancel]
  have hkP : p * (r : G)⁻¹ ∈ P := P.mul_mem hp (P.inv_mem (hYP hrY))
  have hkZ : p * (r : G)⁻¹ ∈ c.Zs := hR.inf_KR_le_of_pgroup hP hPN ⟨hkP, hkK⟩
  have h := Y.mul_mem (hZY hkZ) hrY
  rwa [inv_mul_cancel_right] at h

end IsRs

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
