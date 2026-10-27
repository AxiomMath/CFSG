module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.CGT.PushingUpLit.SYMB.ProdCard
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.RankThree.GF2n (exists_mul_of_mem_sup)

variable {G : Type} [Group G] [Finite G]

theorem lc_generic (Sig : Subgroup G → Prop)
    (hTI : ∀ Q Q', Sig Q → Sig Q' → Q = Q' ∨ Q ⊓ Q' = ⊥)
    (hconj : ∀ Q c, Sig Q → Sig (conjSubgroup c Q))
    (hQ : ∀ Q, Sig Q → Nat.card ↥Q = 4)
    {E L C₀ V : Subgroup G} {c : G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE : Nat.card ↥E = 64)
    (hLE : L ≤ E) (hL : Nat.card ↥L = 16) (hC₀V : C₀ ≤ V) (hC₀ : Nat.card ↥C₀ = 4)
    (hVE : V ≤ E) (hV : Nat.card ↥V = 16) (hLC₀ : L ⊓ C₀ = ⊥)
    (hcom : ∀ e ∈ E, c * e * c⁻¹ * e⁻¹ ∈ C₀) (hcV : ∀ e ∈ E, c * e = e * c → e ∈ V)
    (hVc : ∀ v ∈ V, c * v = v * c)
    (hcov : ∀ l ∈ L, l ≠ 1 → ∃ Q, Sig Q ∧ Q ≤ L ∧ l ∈ Q) :
    Sig (L ⊓ V) ∧ Nat.card ↥(L ⊓ V) = 4 := by
  have hLV : ∀ x ∈ L, ∀ y ∈ V, x * y = y * x := fun x hx y hy => hEc x (hLE hx) y (hVE hy)
  have h1 := SYMB.card_sup_mul_card_inf_of_commute hLV
  have hsupE : Nat.card ↥(L ⊔ V) ≤ 64 := hE ▸ Subgroup.card_le_of_le (sup_le hLE hVE)
  have hge : 4 ≤ Nat.card ↥(L ⊓ V) := by
    by_contra hlt
    have : Nat.card ↥(L ⊔ V) * Nat.card ↥(L ⊓ V) ≤ 64 * 3 :=
      Nat.mul_le_mul hsupE (by omega)
    rw [h1, hL, hV] at this
    omega
  have hC₀Z : ∀ x ∈ C₀, ∀ y ∈ L ⊓ V, x * y = y * x := fun x hx y hy =>
    hEc x (hVE (hC₀V hx)) y (hLE hy.1)
  have hdisj : C₀ ⊓ (L ⊓ V) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ L ⊓ C₀ := ⟨hx.2.1, hx.1⟩
    rw [hLC₀] at this
    exact this
  have h2 := SYMB.card_sup_mul_card_inf_of_commute hC₀Z
  rw [hdisj, Subgroup.card_bot, hC₀] at h2
  have hsupV : Nat.card ↥(C₀ ⊔ (L ⊓ V)) ≤ 16 :=
    hV ▸ Subgroup.card_le_of_le (sup_le hC₀V inf_le_right)
  have hcard : Nat.card ↥(L ⊓ V) = 4 := by omega
  refine ⟨?_, hcard⟩
  obtain ⟨⟨z, hzZ⟩, hz1⟩ : ∃ a : ↥(L ⊓ V), a ≠ 1 := by
    apply Subgroup.ne_bot_iff_exists_ne_one.mp
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  obtain ⟨Q, hQs, hQL, hzQ⟩ := hcov z hzZ.1 hz1'
  have hQc : ∀ q ∈ Q, c * q = q * c := by
    rcases hTI Q (conjSubgroup c Q) hQs (hconj Q c hQs) with heq | hbot
    · intro q hq
      have hqc : c * q * c⁻¹ ∈ Q := by
        have : c * q * c⁻¹ ∈ conjSubgroup c Q := by
          rw [mem_conjSubgroup, show c⁻¹ * (c * q * c⁻¹) * c = q by group]
          exact hq
        rwa [← heq] at this
      have hcm : c * q * c⁻¹ * q⁻¹ ∈ L ⊓ C₀ :=
        ⟨Q.mul_mem hqc (Q.inv_mem hq) |> hQL, hcom q (hLE (hQL hq))⟩
      rw [hLC₀, Subgroup.mem_bot] at hcm
      calc c * q = (c * q * c⁻¹ * q⁻¹) * (q * c) := by group
        _ = q * c := by rw [hcm, one_mul]
    · exfalso
      have hzc : c * z = z * c := hVc z hzZ.2
      have hzq : z ∈ conjSubgroup c Q := by
        rw [mem_conjSubgroup, show c⁻¹ * z * c = z by
          calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
            _ = c⁻¹ * (c * z) := by rw [hzc]
            _ = z := by group]
        exact hzQ
      have : z ∈ Q ⊓ conjSubgroup c Q := ⟨hzQ, hzq⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hz1' this
  have hQZ : Q ≤ L ⊓ V := fun q hq => ⟨hQL hq, hcV q (hLE (hQL hq)) (hQc q hq)⟩
  have hQeq : Q = L ⊓ V :=
    Subgroup.eq_of_le_of_card_ge hQZ (by rw [hQ Q hQs, hcard])
  rw [← hQeq]
  exact hQs

theorem fin_generic (Sig : Subgroup G → Prop)
    (hTI : ∀ Q Q', Sig Q → Sig Q' → Q = Q' ∨ Q ⊓ Q' = ⊥)
    (hconj : ∀ Q c, Sig Q → Sig (conjSubgroup c Q))
    (hQ : ∀ Q, Sig Q → Nat.card ↥Q = 4)
    {V C₀ F₀ : Subgroup G} {h : G} (hC₀s : Sig C₀) (hF₀ : Nat.card ↥F₀ = 4)
    (hC₀F₀ : C₀ ⊓ F₀ = ⊥) (hVsplit : ∀ v ∈ V, ∃ c ∈ C₀, ∃ f ∈ F₀, v = c * f)
    (hhC₀ : ∀ c ∈ C₀, h * c * h⁻¹ ∈ C₀) (hhF₀ : ∀ f ∈ F₀, h * f * h⁻¹ = f)
    (hfpf : ∀ c ∈ C₀, h * c * h⁻¹ = c → c = 1)
    (hcov : ∀ l ∈ V, l ≠ 1 → ∃ Q, Sig Q ∧ Q ≤ V ∧ l ∈ Q) (hF₀V : F₀ ≤ V) :
    Sig F₀ := by
  obtain ⟨⟨f, hfF⟩, hf1⟩ : ∃ a : ↥F₀, a ≠ 1 := by
    apply Subgroup.ne_bot_iff_exists_ne_one.mp
    intro hbot
    rw [hbot, Subgroup.card_bot] at hF₀
    omega
  have hf1' : f ≠ 1 := fun e => hf1 (Subtype.ext e)
  obtain ⟨Q, hQs, hQV, hfQ⟩ := hcov f (hF₀V hfF) hf1'
  have hQh : conjSubgroup h Q = Q := by
    rcases hTI Q (conjSubgroup h Q) hQs (hconj Q h hQs) with heq | hbot
    · exact heq.symm
    · exfalso
      have hfq : f ∈ conjSubgroup h Q := by
        rw [mem_conjSubgroup]
        have : h⁻¹ * f * h = f := by
          have := hhF₀ f hfF
          calc h⁻¹ * f * h = h⁻¹ * (h * f * h⁻¹) * h := by
                rw [this]
            _ = f := by group
        rwa [this]
      have : f ∈ Q ⊓ conjSubgroup h Q := ⟨hfQ, hfq⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hf1' this
  have hQC : Q ⊓ C₀ = ⊥ := by
    rcases hTI Q C₀ hQs hC₀s with heq | hbot
    · exfalso
      have : f ∈ C₀ ⊓ F₀ := ⟨heq ▸ hfQ, hfF⟩
      rw [hC₀F₀, Subgroup.mem_bot] at this
      exact hf1' this
    · exact hbot
  have hQF : Q ≤ F₀ := by
    intro q hq
    obtain ⟨c, hc, f', hf', rfl⟩ := hVsplit q (hQV hq)
    have hhq : h * (c * f') * h⁻¹ ∈ Q := by
      have : h * (c * f') * h⁻¹ ∈ conjSubgroup h Q := by
        rw [mem_conjSubgroup, show h⁻¹ * (h * (c * f') * h⁻¹) * h = c * f' by group]
        exact hq
      rwa [hQh] at this
    have hdiv : h * c * h⁻¹ * c⁻¹ ∈ Q ⊓ C₀ := by
      refine ⟨?_, C₀.mul_mem (hhC₀ c hc) (C₀.inv_mem hc)⟩
      have e : h * c * h⁻¹ * c⁻¹ = (h * (c * f') * h⁻¹) * (c * f')⁻¹ := by
        have := hhF₀ f' hf'
        calc h * c * h⁻¹ * c⁻¹ = (h * c * h⁻¹) * f' * f'⁻¹ * c⁻¹ := by group
          _ = (h * c * h⁻¹) * (h * f' * h⁻¹) * f'⁻¹ * c⁻¹ := by rw [this]
          _ = (h * (c * f') * h⁻¹) * (c * f')⁻¹ := by group
      rw [e]
      exact Q.mul_mem hhq (Q.inv_mem hq)
    rw [hQC, Subgroup.mem_bot] at hdiv
    have hc1 : c = 1 := hfpf c hc (by
      calc h * c * h⁻¹ = (h * c * h⁻¹ * c⁻¹) * c := by group
        _ = c := by rw [hdiv, one_mul])
    rw [hc1, one_mul]
    exact hf'
  have hQeq : Q = F₀ := Subgroup.eq_of_le_of_card_ge hQF (by rw [hQ Q hQs, hF₀])
  rw [← hQeq]
  exact hQs


theorem e16_unique_generic {N S₂ S C₀ E' : Subgroup G}
    (hN2 : ∀ n ∈ N, n * n = 1) (hS₂N : S₂ ≤ Subgroup.normalizer (N : Set G))
    (hN : Nat.card ↥N = 16) (hS₂ : Nat.card ↥S₂ = 64)
    (hC₀ : Nat.card ↥C₀ = 4) (hSS₂ : S ≤ S₂) (hS2 : ∀ s ∈ S, s * s = 1) (hSN : S ⊓ N = C₀)
    (hS : Nat.card ↥S = 16)
    (hcent : ∀ s ∈ S₂, s ∉ N → ∀ m ∈ N, s * m = m * s → m ∈ C₀)
    (hNS₂ : N ≤ S₂) (hE'S₂ : E' ≤ S₂) (hE'c : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x)
    (hE'2 : ∀ x ∈ E', x * x = 1) (hE' : Nat.card ↥E' = 16) (hne : E' ≠ N) : E' = S := by
  obtain ⟨s₀, hs₀E, hs₀N⟩ : ∃ s ∈ E', s ∉ N := by
    by_contra hcon
    have hle : E' ≤ N := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE', hN]))
  have hinfC : N ⊓ E' ≤ C₀ := fun m hm =>
    hcent s₀ (hE'S₂ hs₀E) hs₀N m hm.1 (hE'c s₀ hs₀E m hm.2)
  have hle4 : Nat.card ↥(N ⊓ E') ≤ 4 := hC₀ ▸ Subgroup.card_le_of_le hinfC
  have hnorm : E' ≤ Subgroup.normalizer (N : Set G) := hE'S₂.trans hS₂N
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hsup64 : Nat.card ↥(N ⊔ E') ≤ 64 :=
    hS₂ ▸ Subgroup.card_le_of_le (sup_le hNS₂ hE'S₂)
  rw [hN, hE'] at hprod
  have hcard4 : Nat.card ↥(N ⊓ E') = 4 := by
    by_contra hne4
    have : Nat.card ↥(N ⊔ E') * Nat.card ↥(N ⊓ E') ≤ 64 * 3 :=
      Nat.mul_le_mul hsup64 (by omega)
    omega
  have hinfeq : N ⊓ E' = C₀ :=
    Subgroup.eq_of_le_of_card_ge hinfC (by rw [hC₀, hcard4])
  have hC₀E' : C₀ ≤ E' := hinfeq ▸ inf_le_right
  have hSE' : S ≤ E' := by
    intro s' hs'
    have hsupeq : N ⊔ E' = S₂ := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hNS₂ hE'S₂) ?_
      rw [hS₂]
      have : Nat.card ↥(N ⊔ E') * 4 = 256 := by
        have := hprod
        rw [hcard4] at this
        omega
      omega
    obtain ⟨n, hn, e, he, rfl⟩ := exists_mul_of_mem_sup hnorm (hsupeq ▸ hSS₂ hs')
    by_cases heN : e ∈ N
    · have : n * e ∈ S ⊓ N := ⟨hs', N.mul_mem hn heN⟩
      rw [hSN] at this
      exact hC₀E' this
    · have hsq := hS2 _ hs'
      have hee := hE'2 e he
      have hnn := hN2 n hn
      have h1 : e * n * e = n := by
        calc e * n * e = (n * n) * (e * n * e) := by rw [hnn, one_mul]
          _ = n * (n * e * (n * e)) := by group
          _ = n := by rw [hsq, mul_one]
      have hen : e * n = n * e := by
        calc e * n = e * n * (e * e) := by rw [hee, mul_one]
          _ = (e * n * e) * e := by group
          _ = n * e := by rw [h1]
      exact E'.mul_mem (hC₀E' (hcent e (hE'S₂ he) heN n hn hen)) he
  exact (Subgroup.eq_of_le_of_card_ge hSE' (by rw [hS, hE'])).symm

omit [Finite G] in
theorem norm_identity {S : Subgroup G} {h : G} (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hh3 : h ^ 3 = 1) (hhS : ∀ s ∈ S, h * s * h⁻¹ ∈ S)
    (hfix : ∀ s ∈ S, h * s * h⁻¹ = s → s = 1) {s : G} (hs : s ∈ S) :
    s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) = 1 := by
  set n := s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) with hn
  have hs1 : h * s * h⁻¹ ∈ S := hhS s hs
  have hs2 : h * (h * s * h⁻¹) * h⁻¹ ∈ S := hhS _ hs1
  have hnS : n ∈ S := S.mul_mem (S.mul_mem hs hs1) hs2
  apply hfix n hnS
  have hthree : h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹ = s := by
    have h3 : h * h * h = 1 := by simpa [pow_succ, mul_assoc] using hh3
    have : h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹ = (h * h * h) * s * (h * h * h)⁻¹ := by group
    rw [this, h3]
    group
  calc h * n * h⁻¹ = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) *
        (h * (h * (h * s * h⁻¹) * h⁻¹) * h⁻¹) := by rw [hn]; group
    _ = (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s := by rw [hthree]
    _ = s * (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) := by
        have := hSc _ hs s hs
        have h12 := hSc _ hs1 _ hs2
        calc (h * s * h⁻¹) * (h * (h * s * h⁻¹) * h⁻¹) * s
            = (h * s * h⁻¹) * ((h * (h * s * h⁻¹) * h⁻¹) * s) := by group
          _ = (h * s * h⁻¹) * (s * (h * (h * s * h⁻¹) * h⁻¹)) := by
              rw [hSc _ hs2 s hs]
          _ = ((h * s * h⁻¹) * s) * (h * (h * s * h⁻¹) * h⁻¹) := by group
          _ = (s * (h * s * h⁻¹)) * (h * (h * s * h⁻¹) * h⁻¹) := by
              rw [hSc _ hs1 s hs]
    _ = n := rfl

end CFSG.CGT.PushingUpLit.SolKR2
