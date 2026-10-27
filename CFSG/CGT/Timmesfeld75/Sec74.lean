module

public import CFSG.CGT.Timmesfeld75.Sec74Aux
public import CFSG.CGT.Timmesfeld75.Sec74Stmt

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem exists_conj_transfer {a b c : G}
    (h : ∃ g : G, c * b * c⁻¹ ∈ conjSubgroup g T ∧
      (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹) * (c * a * c⁻¹) ∈ conjSubgroup g T) :
    ∃ g : G, b ∈ conjSubgroup g T ∧ a⁻¹ * b * a ∈ conjSubgroup g T := by
  obtain ⟨g, h1, h2⟩ := h
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [mem_conjSubgroup] at h1 ⊢
    have e : (c⁻¹ * g)⁻¹ * b * (c⁻¹ * g) = g⁻¹ * (c * b * c⁻¹) * g := by group
    rwa [e]
  · rw [mem_conjSubgroup] at h2 ⊢
    have e : (c⁻¹ * g)⁻¹ * (a⁻¹ * b * a) * (c⁻¹ * g) =
        g⁻¹ * ((c * a * c⁻¹)⁻¹ * (c * b * c⁻¹) * (c * a * c⁻¹)) * g := by group
    rwa [e]

theorem exists_conj_transfer' {a b c : G}
    (h : ∃ g : G, c * a * c⁻¹ ∈ conjSubgroup g T ∧
      (c * b * c⁻¹)⁻¹ * (c * a * c⁻¹) * (c * b * c⁻¹) ∈ conjSubgroup g T) :
    ∃ g : G, a ∈ conjSubgroup g T ∧ b⁻¹ * a * b ∈ conjSubgroup g T := by
  obtain ⟨g, h1, h2⟩ := h
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [mem_conjSubgroup] at h1 ⊢
    have e : (c⁻¹ * g)⁻¹ * a * (c⁻¹ * g) = g⁻¹ * (c * a * c⁻¹) * g := by group
    rwa [e]
  · rw [mem_conjSubgroup] at h2 ⊢
    have e : (c⁻¹ * g)⁻¹ * (b⁻¹ * a * b) * (c⁻¹ * g) =
        g⁻¹ * ((c * b * c⁻¹)⁻¹ * (c * a * c⁻¹) * (c * b * c⁻¹)) * g := by group
    rwa [e]

theorem comm_of_mul_self_eq_one {a x : G} (ha : a * a = 1) (hx : x * x = 1)
    (h : (a * x) * (a * x) = 1) : a * x = x * a := by
  have h1 : a * x * a = x := by
    calc a * x * a = a * x * a * (x * x) := by rw [hx, mul_one]
      _ = ((a * x) * (a * x)) * x := by group
      _ = x := by rw [h, one_mul]
  calc a * x = a * x * (a * a) := by rw [ha, mul_one]
    _ = (a * x * a) * a := by group
    _ = x * a := by rw [h1]

theorem Sec6Ctx.sec74_mem (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) (hn3 : 3 ≤ n) {a b : G} (ha : a ∈ T) (ha1 : a ≠ 1)
    (hbD : b ∈ classD T) (hord : orderOf (a * b) = 4) :
    (∃ h : G, a ∈ conjSubgroup h T ∧ b⁻¹ * a * b ∈ conjSubgroup h T) ∨
      (∃ g : G, b ∈ conjSubgroup g T ∧ a⁻¹ * b * a ∈ conjSubgroup g T) := by
  have := hc.finite
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hTab := hP.wc.1
  have hb2 : b * b = 1 := mul_self_eq_one_of_mem_classD hTab hbD
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have ha2 : a * a = 1 := elemAbelian_mul_self hTab ha
  have hx2 : (b * a * b) * (b * a * b) = 1 := by
    calc (b * a * b) * (b * a * b) = b * a * (b * b) * a * b := by group
      _ = b * (a * a) * b := by rw [hb2, mul_one]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  have hcomm : a * (b * a * b) = (b * a * b) * a := by
    have h4 : (a * b) ^ 4 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hsq : (a * b) ^ 2 = a * (b * a * b) := by
      rw [pow_two]
      group
    refine comm_of_mul_self_eq_one ha2 hx2 ?_
    rw [← hsq, ← pow_add]
    exact h4
  have hxD : b * a * b ∈ classD T := by
    have := classD_conj_mul (mem_classD_of_mem ha ha1) b
    rwa [hbi] at this
  have hxN : b * a * b ∈ Subgroup.normalizer (T : Set G) :=
    hP.wc.centralizer_le_normalizer ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  by_cases hxT : b * a * b ∈ T
  · left
    refine ⟨1, ?_, ?_⟩
    · rw [conjSubgroup_one]
      exact ha
    · rw [conjSubgroup_one, hbi]
      exact hxT
  · right
    obtain ⟨⟨y, hyL⟩, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS3.cfg.ne₁
    have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
    obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hyL
    obtain ⟨x₀, hx₀⟩ := hP.conj
    have hyk : y ∈ conjSubgroup x₀ T := hx₀ ▸ hyT₁
    have hyD : y ∈ normD T := mem_normD_of_mem_conjSubgroup hyk hy1 hyN
    have hyT : y ∉ T := by
      intro hT
      have : y ∈ T ⊓ T₁ := ⟨hT, hyT₁⟩
      rw [hS3.cfg.inf, Subgroup.mem_bot] at this
      exact hy1 this
    obtain ⟨g, hgN, hgx⟩ := hc.sec67_conj h1 h62 h63 hA8 hnat (b * a * b) ⟨hxD, hxN⟩ hxT y hyD hyT
    have ha₁ : g * a * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hgN ha
    have ha₁1 : g * a * g⁻¹ ≠ 1 := by
      intro h
      apply ha1
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hb₁D : g * b * g⁻¹ ∈ classD T := classD_conj_mul hbD g
    have hb₁2 : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
      calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
        _ = 1 := by rw [hb2]; group
    have hab₁ : (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) ∈ normIn T₁ T := by
      have e : (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) = g * (b * a * b) * g⁻¹ := by group
      rw [e, ← hgx]
      exact hyL
    exact exists_conj_transfer (c := g)
      (hc.sec74_aux h66 h62 h63 hA8 hn3 ha₁ ha₁1 hb₁D hb₁2 hab₁)

theorem sec74_of (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) : Sec74 := by
  intro G _ T T₁ n m hc hnat hn3 hA8 a ha b hb hord
  obtain ⟨k, s, hsT, hs1, rfl⟩ := ha
  have hb' : k * b * k⁻¹ ∈ classD T := classD_conj_mul hb k
  have e : s * (k * b * k⁻¹) = k * ((k⁻¹ * s * k) * b) * k⁻¹ := by group
  have hord' : orderOf (s * (k * b * k⁻¹)) = 4 := by
    rw [e, ← hord]
    exact MulEquiv.orderOf_eq (MulAut.conj k) _
  rcases hc.sec74_mem h66 h1 h62 h63 hnat hA8 hn3 hsT hs1 hb' hord' with h | h
  · left
    refine exists_conj_transfer' (c := k) ?_
    have e1 : k * (k⁻¹ * s * k) * k⁻¹ = s := by group
    rw [e1]
    exact h
  · right
    refine exists_conj_transfer (c := k) ?_
    have e1 : k * (k⁻¹ * s * k) * k⁻¹ = s := by group
    rw [e1]
    exact h

end CFSG.CGT.Timmesfeld75
