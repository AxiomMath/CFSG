module

public import CFSG.CGT.T75L.Local

public section

namespace CFSG.CGT.T75L

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.false_of_outer5_core (h : Sec4Hyp T T₁ a T₂)
    (hE : EClosure T T₁ T₂) (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {w g a₁ b₁ : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (ha₁ : a₁ ∈ normIn T₁ T)
    (hb₁ : b₁ ∈ normIn T₂ T) (ha₁1 : a₁ ≠ 1) (hb₁1 : b₁ ≠ 1) (hwg : w = g * (a₁ * b₁) * g⁻¹)
    (hwK : w ∈ Subgroup.normalizer (T : Set G))
    (hwN : w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hwT₁ : w ∈ Subgroup.normalizer (T₁ : Set G))
    (hfixT : ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ normIn T T₁)
    (hfixT₁ : ∀ s ∈ T₁, w * s * w⁻¹ * s⁻¹ ∈ normIn T₁ T)
    (hwT₂ : w ∉ Subgroup.normalizer (T₂ : Set G))
    (hR : (∀ n ∈ sec4N T T₁ T₂, w * n * w⁻¹ * n⁻¹ ∈ T) → w ∈ sec4R T T₁ T₂)
    (hwR : w ∉ sec4R T T₁ T₂) : False := by
  have hNab := h.isElemAbelian_sec4N
  have hc := h.sec3.cfg
  have ha₁N : a₁ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_mid ha₁
  have hb₁N : b₁ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_right hb₁
  have hab : a₁ * b₁ = b₁ * a₁ := elemAbelian_mul_comm hNab ha₁N hb₁N
  have hww : w * w = 1 := by
    have h1 : (a₁ * b₁) * (a₁ * b₁) = 1 :=
      elemAbelian_mul_self hNab ((sec4N T T₁ T₂).mul_mem ha₁N hb₁N)
    rw [hwg]
    calc g * (a₁ * b₁) * g⁻¹ * (g * (a₁ * b₁) * g⁻¹) = g * ((a₁ * b₁) * (a₁ * b₁)) * g⁻¹ := by
          group
      _ = 1 := by rw [h1]; group
  have hLK : normIn T T₁ ≤ Subgroup.normalizer (T : Set G) := fun l hl =>
    Subgroup.le_normalizer (normIn_le _ _ hl)
  by_cases hLw : ∀ l ∈ normIn T T₁, w * l = l * w
  ·
    have hL₁w := h.centralizes_normIn₁ hfixT hfixT₁ hLw
    have hwM : ∀ m ∈ cfgM T T₁, w * m = m * w := by
      intro m hm
      obtain ⟨l, hl, l₁, hl₁, rfl⟩ := hc.mem_cfgM_iff.1 hm
      calc w * (l * l₁) = (w * l) * l₁ := (mul_assoc _ _ _).symm
        _ = (l * w) * l₁ := by rw [hLw l hl]
        _ = l * (w * l₁) := mul_assoc _ _ _
        _ = l * (l₁ * w) := by rw [hL₁w l₁ hl₁]
        _ = (l * l₁) * w := (mul_assoc _ _ _).symm
    exact hwR (hR (h.comm_mem_of_centralizes_cfgM hq hwN hww hfixT hwM hwT₂))
  ·
    exfalso
    have hL₁ab : IsElemAbelian 2 (normIn T₁ T) :=
      isElemAbelian_of_le h.isWC₁.1 (normIn_le _ _)
    have hwA : ∀ y ∈ normIn T₁ T, w * y * w⁻¹ ∈ normIn T₁ T := by
      intro y hy
      obtain ⟨hyT₁, hyK⟩ := mem_normIn.1 hy
      exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hwT₁ hyT₁,
        (Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).mul_mem hwK
          hyK) ((Subgroup.normalizer (T : Set G)).inv_mem hwK)⟩
    obtain ⟨x, hxL₁, hx1, hxw⟩ := exists_fixed_ne_one hL₁ab hc.ne₁ hwA hww
    obtain ⟨hxN, hxD, hxT⟩ := h.mem_props_normIn₁ hxL₁ hx1
    obtain ⟨hNa, hDa, hTa⟩ := h.mem_props_normIn₁ ha₁ ha₁1
    obtain ⟨hNb, hDb, hTb⟩ := h.mem_props_normIn₂ hb₁ hb₁1
    have hxE : x ∈ sec4E T T₁ T₂ := subset_sec4E hxD (normIn_mid_le_sec4R hxL₁)
    have haE : a₁ ∈ sec4E T T₁ T₂ := subset_sec4E hDa (normIn_mid_le_sec4R ha₁)
    have hbE : b₁ ∈ sec4E T T₁ T₂ := subset_sec4E hDb (normIn_right_le_sec4R hb₁)
    have hnc : ∀ y, y ∈ sec4N T T₁ T₂ → y ∈ classD T → y ∉ T → ∃ t ∈ T, y * t ≠ t * y := by
      intro y hyN hyD hyT
      by_contra hcon
      push Not at hcon
      have hTL : T ≤ normIn T T₁ := fun t ht =>
        (h.comm_iff_mem_normIn hyN hyD hyT ht).1 (hcon t ht)
      have := Subgroup.card_le_of_le hTL
      omega
    have hx' := hnc x hxN hxD hxT
    have ha' := hnc a₁ hNa hDa hTa
    have hb' := hnc b₁ hNb hDb hTb
    have hxx : x * x = 1 := elemAbelian_mul_self h.isWC₁.1 (normIn_le _ _ hxL₁)
    have ha₁a₁ : a₁ * a₁ = 1 := elemAbelian_mul_self hNab ha₁N
    have hb₁b₁ : b₁ * b₁ = 1 := elemAbelian_mul_self hNab hb₁N
    have hαα : (g * a₁ * g⁻¹) * (g * a₁ * g⁻¹) = 1 := by
      calc (g * a₁ * g⁻¹) * (g * a₁ * g⁻¹) = g * (a₁ * a₁) * g⁻¹ := by group
        _ = 1 := by rw [ha₁a₁]; group
    have hββ : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = 1 := by
      calc (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = g * (b₁ * b₁) * g⁻¹ := by group
        _ = 1 := by rw [hb₁b₁]; group
    have hαE : g * a₁ * g⁻¹ ∈ sec4E T T₁ T₂ := sec4E_conj haE hg
    have hβE : g * b₁ * g⁻¹ ∈ sec4E T T₁ T₂ := sec4E_conj hbE hg
    have hα' := exists_noncomm_conj hg ha'
    have hβ' := exists_noncomm_conj hg hb'
    have hαβ : (g * a₁ * g⁻¹) * (g * b₁ * g⁻¹) = (g * b₁ * g⁻¹) * (g * a₁ * g⁻¹) := by
      calc (g * a₁ * g⁻¹) * (g * b₁ * g⁻¹) = g * (a₁ * b₁) * g⁻¹ := by group
        _ = g * (b₁ * a₁) * g⁻¹ := by rw [hab]
        _ = (g * b₁ * g⁻¹) * (g * a₁ * g⁻¹) := by group
    have hαβw : (g * a₁ * g⁻¹) * (g * b₁ * g⁻¹) = w := by
      rw [hwg]
      group
    have hxw' : x * ((g * a₁ * g⁻¹) * (g * b₁ * g⁻¹)) = ((g * a₁ * g⁻¹) * (g * b₁ * g⁻¹)) * x := by
      rw [hαβw]
      exact hxw.symm
    have hD := h.centralizes_of_dihedral hE hxx hαα hββ hxE hαE hβE hx' hα' hβ' hαβ hxw'
    apply hLw
    intro l hl
    have hlT : l ∈ T := normIn_le _ _ hl
    have hxl : x * l = l * x := (h.comm_iff_mem_normIn hxN hxD hxT hlT).2 hl
    have := hD l hlT hxl
    rw [hαβw] at this
    exact this

end CFSG.CGT.T75L
