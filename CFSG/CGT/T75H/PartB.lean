module

public import CFSG.CGT.T75H.Rank2
public import CFSG.CGT.T75H.PartBCase1
public import CFSG.CGT.T75H.PartBCase2

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I CFSG.Open CFSG.OddInversion

theorem step69PartB_of (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h1 : Sec4NoA) (h63 : Sec63) (h57 : Step57) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) (hBen : AschbacherDisconnectedInput) : Step69PartB := by
  intro G _ T T₁ hy h4 S hS α hα β hβ hα1 hβ1 hne hαα hββ hαβ ℓ a b y D N hN hN3 γ hγ h hh hhγ
  classical
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hna := hy.nonab
  have hc := sec6Ctx_of_card_four h214 hInv hIso hy h4
  have h48 : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hc.hS hc.hI
  have h57' := h57 G T T₁ hy
  have hsup := hSub_sup_eq_top_of_card_four h1 h63 hBen hc h48 h57' D
  have hT := hy.pair.wc
  have hαmem := mem_Cbar_iff.1 hα
  have hβmem := mem_Cbar_iff.1 hβ
  have hℓnc : ¬ ∀ t ∈ T, ℓ * t = t * ℓ := by
    intro hcent
    apply D.ha1
    have h1 : ℓ * a = ℓ * 1 := by
      calc ℓ * a = b * ℓ * b := D.conj_ℓ_b.symm
        _ = ℓ * b * b := by rw [← hcent b D.hb]
        _ = ℓ * 1 := by rw [mul_assoc, D.bb]
    exact mul_left_cancel h1
  have hαℓ : α ≠ ℓ := fun hh' => hℓnc (fun t ht => by
    rw [← hh']
    exact (hαmem.2.1 t ht).symm)
  have hβℓ : β ≠ ℓ := fun hh' => hℓnc (fun t ht => by
    rw [← hh']
    exact (hβmem.2.1 t ht).symm)
  have hact : OddAct N ℓ α β :=
    { pgroup := hN3, ℓℓ := D.ℓℓ, ℓ1 := D.hℓ1, αα := hαα, ββ := hββ
      comm_ℓα := hαmem.2.2 ℓ D.hℓT₁, comm_ℓβ := hβmem.2.2 ℓ D.hℓT₁, comm_αβ := hαβ
      α1 := hα1, β1 := hβ1, αβ := hne
      normℓ := fun n hn => hN.norm ℓ D.hℓN n hn
      normα := fun n hn => hN.norm α (hS.norm α hαmem.1) n hn
      normβ := fun n hn => hN.norm β (hS.norm β hβmem.1) n hn }
  have hαβ1 : α * β ≠ 1 := fun hh' => hne (by
    have : α = β⁻¹ := eq_inv_of_mul_eq_one_left hh'
    rw [this]
    exact inv_eq_of_mul_eq_one_right hββ)
  have hαβT : ∀ t ∈ T, t * (α * β) = (α * β) * t := fun t ht => by
    rw [← mul_assoc, hαmem.2.1 t ht, mul_assoc, hβmem.2.1 t ht, mul_assoc]
  have hαβT₁ : ∀ t ∈ T₁, t * (α * β) = (α * β) * t := fun t ht => by
    rw [← mul_assoc, hαmem.2.2 t ht, mul_assoc, hβmem.2.2 t ht, mul_assoc]
  have hJ1 : ∀ j ∈ invertedSet N ℓ, j = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀, hj₀1⟩ := hcon
    by_cases hcase : ∃ γ ∈ ({α, β, α * β} : Set G), ∀ j ∈ invertedSet N ℓ, γ * j = j * γ
    · obtain ⟨γ', hγ', hγJ⟩ := hcase
      rcases hγ' with rfl | rfl | rfl
      · exact case1_false hna hy.ind h215 hT h4 D hN hN3 hsup hα1 (fun t ht => hαmem.2.1 t ht)
          (fun t ht => hαmem.2.2 t ht) ⟨j₀, hj₀, hj₀1⟩ hγJ
      · exact case1_false hna hy.ind h215 hT h4 D hN hN3 hsup hβ1 (fun t ht => hβmem.2.1 t ht)
          (fun t ht => hβmem.2.2 t ht) ⟨j₀, hj₀, hj₀1⟩ hγJ
      · exact case1_false hna hy.ind h215 hT h4 D hN hN3 hsup hαβ1 hαβT hαβT₁ ⟨j₀, hj₀, hj₀1⟩ hγJ
    · push Not at hcase
      have hα' : ¬ ∀ j ∈ invertedSet N ℓ, α * j = j * α := fun hall => by
        obtain ⟨j, hj, hne'⟩ := hcase α (Or.inl rfl)
        exact hne' (hall j hj)
      have hβ' : ¬ ∀ j ∈ invertedSet N ℓ, β * j = j * β := fun hall => by
        obtain ⟨j, hj, hne'⟩ := hcase β (Or.inr (Or.inl rfl))
        exact hne' (hall j hj)
      have hαβ' : ¬ ∀ j ∈ invertedSet N ℓ, (α * β) * j = j * (α * β) := fun hall => by
        obtain ⟨j, hj, hne'⟩ := hcase (α * β) (Or.inr (Or.inr rfl))
        exact hne' (hall j hj)
      have hfix : ∀ {x m : G}, x * m = m * x → x * m * x⁻¹ = m := fun {x m} hx => by
        rw [hx]; group
      have hαβαβ : (α * β) * (α * β) = 1 := by
        calc (α * β) * (α * β) = α * (β * α) * β := by group
          _ = α * (α * β) * β := by rw [← hαβ]
          _ = (α * α) * (β * β) := by group
          _ = 1 := by rw [hαα, hββ, one_mul]
      have hαe : α * (α * β) = (α * β) * α := by
        calc α * (α * β) = α * (β * α) := by rw [hαβ]
          _ = (α * β) * α := by group
      have hβe : β * (α * β) = (α * β) * β := by
        calc β * (α * β) = (β * α) * β := by group
          _ = (α * β) * β := by rw [← hαβ]
      have hprod : ∀ {m : G}, α * m * α⁻¹ = m⁻¹ → β * m * β⁻¹ = m⁻¹ →
          (α * β) * m * (α * β)⁻¹ = m := fun {m} hα' hβ' => by
        calc (α * β) * m * (α * β)⁻¹ = α * (β * m * β⁻¹) * α⁻¹ := by group
          _ = α * m⁻¹ * α⁻¹ := by rw [hβ']
          _ = (α * m * α⁻¹)⁻¹ := by group
          _ = m := by rw [hα', inv_inv]
      have hprod_fi : ∀ {m : G}, α * m * α⁻¹ = m → β * m * β⁻¹ = m⁻¹ →
          (α * β) * m * (α * β)⁻¹ = m⁻¹ := fun {m} hα' hβ' => by
        calc (α * β) * m * (α * β)⁻¹ = α * (β * m * β⁻¹) * α⁻¹ := by group
          _ = α * m⁻¹ * α⁻¹ := by rw [hβ']
          _ = (α * m * α⁻¹)⁻¹ := by group
          _ = m⁻¹ := by rw [hα']
      have hprod_if : ∀ {m : G}, α * m * α⁻¹ = m⁻¹ → β * m * β⁻¹ = m →
          (α * β) * m * (α * β)⁻¹ = m⁻¹ := fun {m} hα' hβ' => by
        calc (α * β) * m * (α * β)⁻¹ = α * (β * m * β⁻¹) * α⁻¹ := by group
          _ = α * m * α⁻¹ := by rw [hβ']
          _ = m⁻¹ := hα'
      rcases exists_two_pure hact hαℓ hβℓ hα' hβ' hαβ' with
        ⟨⟨m₁, ⟨⟨hm₁N, hℓm₁⟩, hαm₁, hβm₁⟩, hm₁1⟩, ⟨m₂, ⟨⟨hm₂N, hℓm₂⟩, hαm₂, hβm₂⟩, hm₂1⟩⟩ |
        ⟨⟨m₁, ⟨⟨hm₁N, hℓm₁⟩, hαm₁, hβm₁⟩, hm₁1⟩, ⟨m₂, ⟨⟨hm₂N, hℓm₂⟩, hαm₂, hβm₂⟩, hm₂1⟩⟩ |
        ⟨⟨m₁, ⟨⟨hm₁N, hℓm₁⟩, hαm₁, hβm₁⟩, hm₁1⟩, ⟨m₂, ⟨⟨hm₂N, hℓm₂⟩, hαm₂, hβm₂⟩, hm₂1⟩⟩
      ·
        exact case2_false hna hy.ind h215 hI hT h4 D hN hN3 (e₁ := α) (e₂ := β)
          (fun t ht => hαmem.2.2 t ht) (fun t ht => hβmem.2.2 t ht)
          (fun t ht => hαmem.2.1 t ht) (fun t ht => hβmem.2.1 t ht) hαα hββ hαβ
          hm₁N hm₂N hm₁1 hm₂1 hℓm₁ hℓm₂ (hfix hαm₁) hαm₂ (hfix hβm₂) hβm₁
      ·
        exact case2_false hna hy.ind h215 hI hT h4 D hN hN3 (e₁ := α) (e₂ := α * β)
          (fun t ht => hαmem.2.2 t ht) hαβT₁ (fun t ht => hαmem.2.1 t ht) hαβT hαα hαβαβ hαe
          hm₁N hm₂N hm₁1 hm₂1 hℓm₁ hℓm₂ (hfix hαm₁) hαm₂ (hprod hαm₂ hβm₂)
          (hprod_fi (hfix hαm₁) hβm₁)
      ·
        exact case2_false hna hy.ind h215 hI hT h4 D hN hN3 (e₁ := β) (e₂ := α * β)
          (fun t ht => hβmem.2.2 t ht) hαβT₁ (fun t ht => hβmem.2.1 t ht) hαβT hββ hαβαβ hβe
          hm₁N hm₂N hm₁1 hm₂1 hℓm₁ hℓm₂ (hfix hβm₁) hβm₂ (hprod hαm₂ hβm₂)
          (hprod_if hαm₁ (hfix hβm₁))
  have hNℓ : ∀ n ∈ N, n * ℓ = ℓ * n := by
    intro n hn
    have hord : orderOf ℓ = 2 := orderOf_eq_prime (by rw [sq]; exact D.ℓℓ) D.hℓ1
    have hnorm : ℓ ∈ Subgroup.normalizer (N : Set G) :=
      mem_normalizer_of_invol D.ℓℓ (fun k hk => hN.norm ℓ D.hℓN k hk)
    have hdec := (CFSG.ABGLocalTools.odd_fixed_mul_inverted hN.odd hord hnorm).1
    have hnmem : n ∈ (N : Set G) := hn
    rw [hdec] at hnmem
    obtain ⟨c, hc, j, hj, rfl⟩ := Set.mem_mul.1 hnmem
    rw [hJ1 j hj, mul_one]
    exact Subgroup.mem_centralizer_singleton_iff.1 hc.2
  exact hNℓ h hh

end CFSG.CGT.T75H
