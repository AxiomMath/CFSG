module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9C
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8A

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

omit [Finite G] in
theorem late_orderOf_four {w a₀ : G} (hw : w * w = a₀) (ha₀ : a₀ ≠ 1) (ha₀2 : a₀ * a₀ = 1) :
    orderOf w = 4 := by
  have h2 : w ^ (2 ^ 1) ≠ 1 := by
    rw [pow_one, pow_two, hw]
    exact ha₀
  have h4 : w ^ (2 ^ (1 + 1)) = 1 := by
    have : w ^ (2 ^ (1 + 1)) = (w * w) * (w * w) := by
      rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [this, hw, ha₀2]
  have := orderOf_eq_prime_pow h2 h4
  simpa using this

theorem Std20.late_no_sq_W (d : Std20 p f K K' J S R R' W V z t) (h8 : 8 < Nat.card R)
    {σ : G} (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W) :
    False := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩg := d.late_hΩ
  have hWc := d.late_hWc
  obtain ⟨x, r₀, hd⟩ := late_exists_dData hp hq d.hyp d.hW d.late_R_mem_D d.late_mem_K d.hR
    d.viol.hzK
  obtain ⟨x', r₀', hd'⟩ := late_exists_dData hp hq d.hyp d.hW d.late_R'_mem_D d.late_mem_K'
    d.hR' d.late_hzK'
  obtain ⟨hK'σ, hRσ, hWσ, hSσ⟩ := d.late_swap_data hσ hσK
  have hσz := d.late_S_act_z hσ
  have hconjW : ∀ w ∈ W, σ * w * σ⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) w).mp hw
  obtain ⟨m₀, hm₀⟩ := hd.orderOf_eq
  have hcardR : Nat.card R = 2 * orderOf x := hd.card
  have hm3 : 3 ≤ m₀ := by
    by_contra h
    push Not at h
    have : 2 ^ m₀ ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hN8 : 8 ∣ orderOf x := by
    rw [hm₀]
    exact (pow_dvd_pow 2 hm3 : 2 ^ 3 ∣ 2 ^ m₀)
  have hRR' : Nat.card R' = Nat.card R :=
    (Sec6Gen.natCard_isSylow2In_eq hΩg d.late_mem_K d.late_mem_K' d.hR d.hR').symm
  have hN' : orderOf x' = orderOf x := by
    have := hd'.card
    omega
  have hxW : x ∈ W := hd.u_memW
  have hxK : x ∈ K := hd.u_mem.1
  have hx'W : x' ∈ W := hd'.u_memW
  have hx'K' : x' ∈ K' := hd'.u_mem.1
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have heW : x ^ (orderOf x / 4) ∈ W := Subgroup.pow_mem W hxW _
  have heK : x ^ (orderOf x / 4) ∈ K := Subgroup.pow_mem K hxK _
  have he₃W : x ^ (orderOf x / 8) ∈ W := Subgroup.pow_mem W hxW _
  have he₃K : x ^ (orderOf x / 8) ∈ K := Subgroup.pow_mem K hxK _
  have he₃2 : x ^ (orderOf x / 8) * x ^ (orderOf x / 8) = x ^ (orderOf x / 4) := by
    rw [← pow_add]
    congr 1
    omega
  have he2 : x ^ (orderOf x / 4) * x ^ (orderOf x / 4) = z := by
    rw [← pow_add, ← hd.z_eq]
    congr 1
    omega
  have he'0W : x' ^ (orderOf x / 4) ∈ W := Subgroup.pow_mem W hx'W _
  have he'0K : x' ^ (orderOf x / 4) ∈ K' := Subgroup.pow_mem K' hx'K' _
  have he'02 : x' ^ (orderOf x / 4) * x' ^ (orderOf x / 4) = z := by
    rw [← pow_add, ← hd'.z_eq, hN']
    congr 1
    omega
  generalize x ^ (orderOf x / 4) = e at heW heK he₃2 he2
  generalize x ^ (orderOf x / 8) = e₃ at he₃W he₃K he₃2
  generalize x' ^ (orderOf x / 4) = e₀' at he'0W he'0K he'02
  have heK' : e ∉ K' := by
    intro heK'
    have hA2 : IsPGroup 2 ↥(Subgroup.zpowers e) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS heW))
    have hcard := Sec6Gen.card_le_two_of_le_inf hΩg d.late_mem_K d.late_mem_K' d.ne.symm hA2
      (Subgroup.zpowers_le.mpr heK) (Subgroup.zpowers_le.mpr heK')
    rw [Nat.card_zpowers] at hcard
    have hpos : 0 < orderOf e := by
      rw [← Nat.card_zpowers]
      exact Nat.card_pos
    have hsq : e * e = 1 := by
      rcases (by omega : orderOf e = 1 ∨ orderOf e = 2) with h | h
      · rw [orderOf_eq_one_iff.mp h, one_mul]
      · rw [← pow_two, ← h, pow_orderOf_eq_one]
    exact hz1 (he2.symm.trans hsq)
  have heσK' : σ * e * σ⁻¹ ∈ K' := hσK ▸ conj_mem_conjSub heK
  have heσW : σ * e * σ⁻¹ ∈ W := hconjW e heW
  have he₃σW : σ * e₃ * σ⁻¹ ∈ W := hconjW e₃ he₃W
  have heσ2 : (σ * e * σ⁻¹) * (σ * e * σ⁻¹) = z := by
    calc (σ * e * σ⁻¹) * (σ * e * σ⁻¹) = σ * (e * e) * σ⁻¹ := by group
      _ = σ * z * σ⁻¹ := by rw [he2]
      _ = z := hσz
  have he₃σ2 : (σ * e₃ * σ⁻¹) * (σ * e₃ * σ⁻¹) = σ * e * σ⁻¹ := by
    calc (σ * e₃ * σ⁻¹) * (σ * e₃ * σ⁻¹) = σ * (e₃ * e₃) * σ⁻¹ := by group
      _ = σ * e * σ⁻¹ := by rw [he₃2]
  have hξW : e₃ * (σ * e₃ * σ⁻¹) ∈ W := W.mul_mem he₃W he₃σW
  have ha₀W : e * (σ * e * σ⁻¹) ∈ W := W.mul_mem heW heσW
  have hξ2 : (e₃ * (σ * e₃ * σ⁻¹)) * (e₃ * (σ * e₃ * σ⁻¹)) = e * (σ * e * σ⁻¹) := by
    calc (e₃ * (σ * e₃ * σ⁻¹)) * (e₃ * (σ * e₃ * σ⁻¹))
        = e₃ * ((σ * e₃ * σ⁻¹) * e₃) * (σ * e₃ * σ⁻¹) := by group
      _ = e₃ * (e₃ * (σ * e₃ * σ⁻¹)) * (σ * e₃ * σ⁻¹) := by rw [hWc _ he₃σW _ he₃W]
      _ = (e₃ * e₃) * ((σ * e₃ * σ⁻¹) * (σ * e₃ * σ⁻¹)) := by group
      _ = e * (σ * e * σ⁻¹) := by rw [he₃2, he₃σ2]
  have ha₀2 : (e * (σ * e * σ⁻¹)) * (e * (σ * e * σ⁻¹)) = 1 := by
    calc (e * (σ * e * σ⁻¹)) * (e * (σ * e * σ⁻¹))
        = e * ((σ * e * σ⁻¹) * e) * (σ * e * σ⁻¹) := by group
      _ = e * (e * (σ * e * σ⁻¹)) * (σ * e * σ⁻¹) := by rw [hWc _ heσW _ heW]
      _ = (e * e) * ((σ * e * σ⁻¹) * (σ * e * σ⁻¹)) := by group
      _ = z * z := by rw [he2, heσ2]
      _ = 1 := d.viol.hzK.sq
  have ha₀1 : e * (σ * e * σ⁻¹) ≠ 1 := by
    intro h
    apply heK'
    have : σ * e * σ⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : e = (σ * e * σ⁻¹)⁻¹ := by rw [this, inv_inv]
    rw [h2]
    exact K'.inv_mem heσK'
  have ha₀z : e * (σ * e * σ⁻¹) ≠ z := by
    intro h
    apply heK'
    have h1 : σ * e * σ⁻¹ = e := by
      apply mul_left_cancel (a := e)
      rw [h, ← he2]
    rw [← h1]
    exact heσK'
  have hσe₃ : σ * e₃ * σ⁻¹ * (σ * (σ * e₃ * σ⁻¹) * σ⁻¹) = e₃ * (σ * e₃ * σ⁻¹) := by
    have h1 : σ * (σ * e₃ * σ⁻¹) * σ⁻¹ = (σ * σ) * e₃ * (σ * σ)⁻¹ := by group
    have h2 : (σ * σ) * e₃ * (σ * σ)⁻¹ = e₃ := by
      have := hWc _ hσ2 _ he₃W
      calc (σ * σ) * e₃ * (σ * σ)⁻¹ = (e₃ * (σ * σ)) * (σ * σ)⁻¹ := by rw [this]
        _ = e₃ := by group
    rw [h1, h2]
    exact hWc _ he₃σW _ he₃W
  have hσξ : σ * (e₃ * (σ * e₃ * σ⁻¹)) * σ⁻¹ = e₃ * (σ * e₃ * σ⁻¹) := by
    calc σ * (e₃ * (σ * e₃ * σ⁻¹)) * σ⁻¹
        = (σ * e₃ * σ⁻¹) * (σ * (σ * e₃ * σ⁻¹) * σ⁻¹) := by group
      _ = e₃ * (σ * e₃ * σ⁻¹) := hσe₃
  have hσa₀ : σ * (e * (σ * e * σ⁻¹)) * σ⁻¹ = e * (σ * e * σ⁻¹) := by
    rw [← hξ2]
    calc σ * ((e₃ * (σ * e₃ * σ⁻¹)) * (e₃ * (σ * e₃ * σ⁻¹))) * σ⁻¹
        = (σ * (e₃ * (σ * e₃ * σ⁻¹)) * σ⁻¹) * (σ * (e₃ * (σ * e₃ * σ⁻¹)) * σ⁻¹) := by group
      _ = _ := by rw [hσξ]
  generalize e₃ * (σ * e₃ * σ⁻¹) = α at hξW hξ2 hσξ
  generalize e * (σ * e * σ⁻¹) = a₀ at ha₀W hξ2 ha₀2 ha₀1 ha₀z hσa₀
  have ha₀tz : a₀ = t ∨ a₀ = z * t := by
    rcases d.late_inv_W a₀ ha₀W ha₀2 with h | h | h | h
    · exact absurd h ha₀1
    · exact absurd h ha₀z
    · exact Or.inl h
    · exact Or.inr h
  have hσt : σ * t * σ⁻¹ = t := by
    rcases d.late_S_act_t hσ with h | h
    · exact h
    · exfalso
      have hne : z * t ≠ t := fun h' => hz1 (by simpa using h')
      rcases ha₀tz with ha | ha
      · rw [ha, h] at hσa₀
        exact hne hσa₀
      · rw [ha] at hσa₀
        have : σ * (z * t) * σ⁻¹ = z * (z * t) := by
          calc σ * (z * t) * σ⁻¹ = (σ * z * σ⁻¹) * (σ * t * σ⁻¹) := by group
            _ = z * (z * t) := by rw [hσz, h]
        rw [this] at hσa₀
        apply hne
        calc z * t = z * (z * t) := hσa₀.symm
          _ = t := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]
  obtain ⟨m, hmN, hme⟩ : ∃ m ∈ Subgroup.normalizer (W : Set G), m * z * m⁻¹ = a₀ := by
    rcases ha₀tz with ha | ha
    · rw [ha]
      exact d.late_exists_n
    · rw [ha]
      obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
      exact ⟨t₀, hh.t₀_normW, hh.htz⟩
  obtain ⟨hL₁, hL₂, hL₁₂, hL₁i, hL₂i⟩ := d.late_member_data m
  rw [hme] at hL₁i hL₂i
  have hb₁L : m * e * m⁻¹ ∈ conjSub m K := conj_mem_conjSub heK
  have hb₂L : m * e₀' * m⁻¹ ∈ conjSub m K' := conj_mem_conjSub he'0K
  have hconjm : ∀ w ∈ W, m * w * m⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hmN w).mp hw
  have hb₁W : m * e * m⁻¹ ∈ W := hconjm e heW
  have hb₂W : m * e₀' * m⁻¹ ∈ W := hconjm e₀' he'0W
  have hb₁2 : (m * e * m⁻¹) * (m * e * m⁻¹) = a₀ := by
    calc (m * e * m⁻¹) * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = m * z * m⁻¹ := by rw [he2]
      _ = a₀ := hme
  have hb₂2 : (m * e₀' * m⁻¹) * (m * e₀' * m⁻¹) = a₀ := by
    calc (m * e₀' * m⁻¹) * (m * e₀' * m⁻¹) = m * (e₀' * e₀') * m⁻¹ := by group
      _ = m * z * m⁻¹ := by rw [he'02]
      _ = a₀ := hme
  have hA₂ : ∀ {w : G}, w ∈ W → IsPGroup 2 ↥(Subgroup.zpowers w) := fun hw =>
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hw))
  have hA₄ : ∀ {w : G}, w * w = a₀ → 4 ≤ Nat.card ↥(Subgroup.zpowers w) := fun hw => by
    rw [Nat.card_zpowers, late_orderOf_four hw ha₀1 ha₀2]
  have hne : Subgroup.zpowers (m * e * m⁻¹) ≠ Subgroup.zpowers (m * e₀' * m⁻¹) := by
    intro h
    exact hL₁₂ (Sec6Gen.eq_of_le_of_le hΩg hL₁ hL₂ (hA₂ hb₁W) (hA₄ hb₁2)
      (Subgroup.zpowers_le.mpr hb₁L) (h ▸ Subgroup.zpowers_le.mpr hb₂L))
  have hlines := d.late_two_lines ha₀1 ha₀2 hξW hb₁W hb₂W hξ2 hb₁2 hb₂2 hne
  have hAfix : ∀ w ∈ Subgroup.zpowers α, σ * w * σ⁻¹ = w := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute σ α := by
      calc σ * α = (σ * α * σ⁻¹) * σ := by group
        _ = α * σ := by rw [hσξ]
    have := (Commute.zpow_right hc k).eq
    rw [this]
    group
  have hnorm : ∀ L : Subgroup G, L ∈ CoreAssembly.conjClass K → Subgroup.zpowers α ≤ L →
      conjSub σ L = L := by
    intro L hL hAL
    refine Sec6Gen.eq_of_le_of_le hΩg (d.hyp.conjInvariant σ L hL) hL (hA₂ hξW) (hA₄ hξ2) ?_ hAL
    intro w hw
    rw [mem_conjSub_iff]
    have h1 : σ⁻¹ * (σ * w * σ⁻¹) * σ = w := by group
    rw [hAfix w hw] at h1
    rw [h1]
    exact hAL hw
  have hperm : ∀ L : Subgroup G, L ∈ CoreAssembly.conjClass K → IsUniqueInvolution L a₀ →
      conjSub σ L = conjSub m K ∨ conjSub σ L = conjSub m K' := by
    intro L hL hLi
    have hLi' : IsUniqueInvolution (conjSub σ L) a₀ := by
      have := hLi.conj σ
      rwa [hσa₀] at this
    exact d.late_members_of_inv hme (d.hyp.conjInvariant σ L hL) hLi'
  have hσL : conjSub σ (conjSub m K) = conjSub m K ∧ conjSub σ (conjSub m K') = conjSub m K' := by
    rcases hlines with h | h
    · have h₁ : conjSub σ (conjSub m K) = conjSub m K :=
        hnorm _ hL₁ (h ▸ Subgroup.zpowers_le.mpr hb₁L)
      refine ⟨h₁, ?_⟩
      rcases hperm _ hL₂ hL₂i with h' | h'
      · exact absurd (conjSub_injective σ (h₁.trans h'.symm)) hL₁₂
      · exact h'
    · have h₂ : conjSub σ (conjSub m K') = conjSub m K' :=
        hnorm _ hL₂ (h ▸ Subgroup.zpowers_le.mpr hb₂L)
      refine ⟨?_, h₂⟩
      rcases hperm _ hL₁ hL₁i with h' | h'
      · exact h'
      · exact absurd (conjSub_injective σ (h'.trans h₂.symm)) hL₁₂
  obtain ⟨ρ, hρR, hρt⟩ : ∃ ρ ∈ R, ρ * t * ρ⁻¹ = a₀ := by
    rcases ha₀tz with ha | ha
    · exact ⟨1, Subgroup.one_mem _, by rw [ha]; group⟩
    · obtain ⟨r, hr, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
      exact ⟨r, hr, by rw [ha]; exact hrt⟩
  have hJ'i : IsUniqueInvolution (conjSub ρ J) a₀ := by
    have := d.viol.hzJ.conj ρ
    rwa [hρt] at this
  have hσJ' : conjSub σ (conjSub ρ J) = conjSub ρ J := by
    rcases d.late_members_of_inv hme (d.hyp.conjInvariant ρ J d.late_mem_J) hJ'i with h | h
    · rw [h]
      exact hσL.1
    · rw [h]
      exact hσL.2
  exact d.late_swap_J hσ hσK hσt hρR hσJ'

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
