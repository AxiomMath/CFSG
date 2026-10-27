module

public import CFSG.CGT.PushingUpLit.A78Sp4.Stmts
public import CFSG.CGT.PushingUpLit.A78Sp4.CentAux

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.Assembly CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cj_eq_of_normalizes {k : G} {H : Subgroup G} (h1 : ∀ x ∈ H, k * x * k⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, k⁻¹ * x * k ∈ H) : cj k H = H := by
  ext x
  rw [mem_cj_iff]
  refine ⟨fun hx => ?_, fun hx => h2 x hx⟩
  have h3 : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
  have h4 := h1 _ hx
  rwa [h3] at h4

theorem cj_eq_of_mem_normalizer_set {k : G} {H : Subgroup G}
    (hk : k ∈ Subgroup.normalizer (H : Set G)) : cj k H = H :=
  cj_eq_of_normalizes (fun x hx => (Subgroup.mem_normalizer_iff.1 hk x).1 hx) (fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hk) x).1 hx
    simpa using this)

theorem cj_eq_of_fix {k : G} {H : Subgroup G} (h : ∀ x ∈ H, k * x * k⁻¹ = x) : cj k H = H := by
  ext x
  rw [mem_cj_iff]
  constructor
  · intro hx
    have h1 := h _ hx
    have h2 : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    rw [h2] at h1
    rw [h1]
    exact hx
  · intro hx
    have h1 := h x hx
    have h2 : k⁻¹ * x * k = x := by
      have h3 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [h1] at h3
      exact h3
    rwa [h2]

theorem cj_inf_eq (g : G) (A B : Subgroup G) : cj g (A ⊓ B) = cj g A ⊓ cj g B :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem cj_sup_eq (g : G) (A B : Subgroup G) : cj g (A ⊔ B) = cj g A ⊔ cj g B :=
  Subgroup.map_sup _ _ _

section NoFixed

variable [Finite G] {L L' V V' Z J T M M' Z' : Subgroup G} {e : ℕ}

theorem no_fixed_point {f : G} {Q : Subgroup G}
    (hs : Sp4Side G L V Z J T M e) (hs' : Sp4Side G L' V' Z' J T M' e)
    (hc : Sp4CentL G L V Z f e) (hc' : Sp4CentL G L' V' Z' f e)
    (hVJ : V ≤ J) (hZV' : Z ≤ V') (hQp : IsPGroup 2 Q)
    (hQn : ∀ c ∈ Subgroup.centralizer ({f} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hY : Nat.card ↥(V ⊓ V' ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ e)
    (he : e < 3 * (e / 2)) {z : G} (hzQ : z ∈ Q) (hzV : z ∈ V)
    (hzC : z ∈ Subgroup.centralizer ({f} : Set G)) (hzZ : z ∉ Z) : False := by
  have hQc : ∀ k ∈ Subgroup.centralizer ({f} : Set G), cj k Q = Q := fun k hk =>
    cj_eq_of_normalizes (hQn k hk) (fun x hx => by
      simpa using hQn k⁻¹ ((Subgroup.centralizer ({f} : Set G)).inv_mem hk) x hx)
  have hZV : Z ≤ V := by rw [hs.Z_eq]; exact inf_le_left
  have hVL' : V ≤ L' := hVJ.trans hs'.J_le_L
  have hXV' : Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G)) ≤ V' := by
    have hnorm : ((Q ⊓ (L' ⊓ Subgroup.centralizer ({f} : Set G))).subgroupOf
        (L' ⊓ Subgroup.centralizer ({f} : Set G))).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, (L' ⊓ _).mul_mem ((L' ⊓ _).mul_mem k.2 n.2) ((L' ⊓ _).inv_mem k.2)⟩
      exact hQn k k.2.2 n hn.1
    have hP := hc'.O2 (Q ⊓ (L' ⊓ Subgroup.centralizer ({f} : Set G))) inf_le_right
      (hQp.to_le inf_le_left) hnorm
    intro x hx
    exact hP ⟨hx.1, hVL' hx.2.1, hx.2.2⟩
  have hX'le : (Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G))) ⊔
      (Z ⊓ Subgroup.centralizer ({f} : Set G)) ≤ V ⊓ Subgroup.centralizer ({f} : Set G) :=
    sup_le inf_le_right (inf_le_inf_right _ hZV)
  have hX'Y : (Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G))) ⊔
      (Z ⊓ Subgroup.centralizer ({f} : Set G)) ≤ V ⊓ V' ⊓ Subgroup.centralizer ({f} : Set G) :=
    sup_le (fun x hx => ⟨⟨hx.2.1, hXV' hx⟩, hx.2.2⟩)
      (fun x hx => ⟨⟨hZV hx.1, hZV' hx.1⟩, hx.2⟩)
  have hkV : ∀ k ∈ L, cj k V = V := fun k hk =>
    cj_eq_of_mem_normalizer_set (by rw [← hs.M_eq]; exact hs.L_le_M hk)
  have hkZ : ∀ k ∈ L, cj k Z = Z := fun k hk => cj_eq_of_fix fun y hy => by
    have hy' : y ∈ Subgroup.centralizer (L : Set G) := by
      rw [hs.Z_eq] at hy
      exact hy.2
    have h1 := Subgroup.mem_centralizer_iff.1 hy' k hk
    rw [h1]
    group
  have hinv : ∀ k ∈ L ⊓ Subgroup.centralizer ({f} : Set G),
      cj k ((Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G))) ⊔
        (Z ⊓ Subgroup.centralizer ({f} : Set G))) =
      (Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G))) ⊔
        (Z ⊓ Subgroup.centralizer ({f} : Set G)) := by
    intro k hk
    have hCk : cj k (Subgroup.centralizer ({f} : Set G)) = Subgroup.centralizer ({f} : Set G) :=
      cj_eq_self_of_mem hk.2
    rw [cj_sup_eq, cj_inf_eq, cj_inf_eq, cj_inf_eq, hQc k hk.2, hkV k hk.1, hkZ k hk.1, hCk]
  have hirr := hc.irred _ hX'le le_sup_right hinv
  obtain ⟨k, hk, hkz⟩ := hc.nofix z ⟨hzV, hzC⟩ hzZ
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := by
    rw [← hs.M_eq]
    exact hs.L_le_M hk.1
  have hq : k * z⁻¹ * k⁻¹ ∈ Q := hQn k hk.2 z⁻¹ (Q.inv_mem hzQ)
  have hv : k * z⁻¹ * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hkN z⁻¹).1 (V.inv_mem hzV)
  have hcomm : ⁅z, k⁆ ∈ Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G)) := by
    have heq : ⁅z, k⁆ = z * (k * z⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    refine ⟨?_, ?_, ?_⟩
    · rw [heq]
      exact Q.mul_mem hzQ hq
    · rw [heq]
      exact V.mul_mem hzV hv
    · rw [commutatorElement_def]
      exact (Subgroup.centralizer ({f} : Set G)).mul_mem
        ((Subgroup.centralizer ({f} : Set G)).mul_mem
          ((Subgroup.centralizer ({f} : Set G)).mul_mem hzC hk.2)
          ((Subgroup.centralizer ({f} : Set G)).inv_mem hzC))
        ((Subgroup.centralizer ({f} : Set G)).inv_mem hk.2)
  have hne : (Q ⊓ (V ⊓ Subgroup.centralizer ({f} : Set G))) ⊔
      (Z ⊓ Subgroup.centralizer ({f} : Set G)) ≠ Z ⊓ Subgroup.centralizer ({f} : Set G) := by
    intro heq
    have h1 : ⁅z, k⁆ ∈ Z ⊓ Subgroup.centralizer ({f} : Set G) := heq ▸ Subgroup.mem_sup_left hcomm
    exact hkz h1.1
  have hle : V ⊓ Subgroup.centralizer ({f} : Set G) ≤
      V ⊓ V' ⊓ Subgroup.centralizer ({f} : Set G) := (hirr.resolve_left hne) ▸ hX'Y
  have hcard := Subgroup.card_le_of_le hle
  rw [hY, hc.card_CV] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

end NoFixed

section Main

variable [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem S_cj_inf (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {s : G} (hs : s ∈ S) :
    cj s (V ⊓ V₂) = V ⊓ V₂ := by
  classical
  by_cases hsT : s ∈ T
  · rw [cj_inf_eq, (h.base.T_norm s hsT).1, (h.base.T_norm s hsT).2]
  · rw [cj_inf_eq, (h.base.swap s hs hsT).1, (h.base.swap s hs hsT).2, inf_comm]

theorem sp4_412 (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (hM : Sp4StmtM S J) :
    Sp4Stmt412 T J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Sp4Stmt412
  by_contra hTJ
  obtain ⟨f₀, hf₀T, hf₀J, hf₀2⟩ := h.field.exists_inv hTJ
  have hf₀S : f₀ ∈ S := h.base.T_le hf₀T
  obtain ⟨g, hfS, hR⟩ := exists_fully_centralized h.base.sylow hf₀S
  set f : G := g⁻¹ * f₀ * g with hf
  have hf2 : f * f = 1 := by
    have h1 : f * f = g⁻¹ * (f₀ * f₀) * g := by rw [hf]; group
    rw [h1, hf₀2]
    group
  have hfJ : f ∉ J := fun hfJ => hf₀J (hM f₀ hf₀S hf₀2 g hfJ)
  have hf1 : f ≠ 1 := fun h1 => hfJ (h1 ▸ J.one_mem)
  have hfT : f ∈ T := by
    by_contra hfT
    exact h.field.no_inv hTJ f hfS hfT hf2
  set C : Subgroup G := Subgroup.centralizer ({f} : Set G) with hC
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 C with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hc) q).1 hq
  have hYcard : Nat.card ↥(V ⊓ V₂ ⊓ C) = 2 ^ e := h.field.card_ZJf f hfT hfJ hf2
  have hYel : ElemAb2 (V ⊓ V₂ ⊓ C) := h.base.elem_V.mono (fun x hx => hx.1.1)
  have hYne : (V ⊓ V₂ ⊓ C) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(V ⊓ V₂ ⊓ C) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hYcard] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.base.two_le
    omega
  have hRY : ∀ t ∈ S ⊓ C, cj t (V ⊓ V₂ ⊓ C) = V ⊓ V₂ ⊓ C := fun t ht => by
    rw [cj_inf_eq, S_cj_inf h ht.1, cj_eq_self_of_mem ht.2]
  obtain ⟨z, hzY, hz1, hzfix⟩ := exists_fixed_ne_one (h.base.sylow.isPGroup.to_le inf_le_left)
    hYel hYne hRY
  have hzQ : z ∈ Q := by
    have hcent : z ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqR : q ∈ S ⊓ C := pCoreOf_le_of_isSylowOf hR hq
      have h1 := hzfix q hqR
      calc q * z = q * z * q⁻¹ * q := by group
        _ = z * q := by rw [h1]
    exact cent_le_pCoreOf h.charTwo hf2 hf1 ⟨hzY.2, hcent⟩
  have he : e < 3 * (e / 2) := by
    obtain ⟨k, hk⟩ := h.field.even_e hTJ
    have h2 := h.base.two_le
    omega
  have hVJ : V ≤ J := by rw [← h.base.sup]; exact le_sup_left
  have hV₂J : V₂ ≤ J := by rw [← h.base.sup]; exact le_sup_right
  by_cases hzZ : z ∈ Z
  · have hzZ₂ : z ∉ Z₂ := fun hz2 => hz1 (Subgroup.mem_bot.1 (h.cross.inf_Z ▸ ⟨hzZ, hz2⟩))
    refine no_fixed_point h.side₂ h.side₁ (h.field.cent_L₂ f hfT hfJ hf2)
      (h.field.cent_L f hfT hfJ hf2) hV₂J h.cross.Z₂_le hQp hQn ?_ he hzQ hzY.1.2 hzY.2 hzZ₂
    rw [inf_comm V₂ V]
    exact hYcard
  · exact no_fixed_point h.side₁ h.side₂ (h.field.cent_L f hfT hfJ hf2)
      (h.field.cent_L₂ f hfT hfJ hf2) hVJ h.cross.Z_le hQp hQn hYcard he hzQ hzY.1.1 hzY.2 hzZ

end Main

end CFSG.CGT.PushingUpLit.A78Sp4
