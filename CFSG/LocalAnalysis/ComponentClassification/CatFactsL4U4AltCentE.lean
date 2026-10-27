module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentD
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCenter

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AltCent

open CFSG Subgroup Equiv Equiv.Perm

variable {m : ℕ}

theorem swap_mem_iff {s : Finset (Fin m)} {a b : Fin m} (hab : a ∈ s ↔ b ∈ s) (x : Fin m) :
    swap a b x ∈ s ↔ x ∈ s := by
  by_cases hxa : x = a
  · rw [hxa, swap_apply_left]
    exact hab.symm
  by_cases hxb : x = b
  · rw [hxb, swap_apply_right]
    exact hab
  rw [swap_apply_of_ne_of_ne hxa hxb]

theorem dt_comm_cross {i j k l : Fin m} (hn : [i, j, k, l].Nodup) :
    (swap i j * swap k l) * (swap i k * swap j l) =
      (swap i k * swap j l) * (swap i j * swap k l) := by
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := ne_of_nodup4 hn
  have hn' : [i, k, j, l].Nodup := by
    simp [hij, hik, hil, hjl, hkl, Ne.symm hjk]
  obtain ⟨h1i, h1j, h1k, h1l, h1F⟩ := dt_apply (π := swap i j * swap k l) rfl hn
  obtain ⟨h2i, h2k, h2j, h2l, h2F⟩ := dt_apply (π := swap i k * swap j l) rfl hn'
  refine Equiv.ext fun a => ?_
  show (swap i j * swap k l) ((swap i k * swap j l) a) =
    (swap i k * swap j l) ((swap i j * swap k l) a)
  by_cases hai : a = i
  · rw [hai, h2i, h1k, h1i, h2j]
  by_cases haj : a = j
  · rw [haj, h2j, h1l, h1j, h2i]
  by_cases hak : a = k
  · rw [hak, h2k, h1i, h1k, h2l]
  by_cases hal : a = l
  · rw [hal, h2l, h1j, h1l, h2k]
  rw [h2F a hai hak haj hal, h1F a hai haj hak hal, h2F a hai hak haj hal]

theorem sq_swap_mul_swap {a b c d : Fin m} (hn : [a, b, c, d].Nodup) :
    swap a b * swap c d * (swap a b * swap c d) = 1 := by
  have hc : Commute (swap a b) (swap c d) := (disjoint_swap_swap hn).commute
  calc swap a b * swap c d * (swap a b * swap c d)
      = swap a b * (swap c d * swap a b) * swap c d := by group
    _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hc.eq]
    _ = (swap a b * swap a b) * (swap c d * swap c d) := by group
    _ = 1 := by rw [swap_mul_self, swap_mul_self, one_mul]

theorem swap_mul_swap_mem_alt {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin m) := by
  rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]
  rfl

theorem centerSylowAlt : OutInv.CenterSylowAlt := by
  intro G _ _ N α J R τ hcfg n hn hN hJ
  obtain ⟨eN⟩ := hN
  obtain ⟨eJ⟩ := hJ
  obtain ⟨hNn, hC, hα2, hJα, hJc, hstd, hRM, hRα, hRS, hτα, hτJ, hτR, -⟩ := hcfg
  have : N.Normal := hNn
  have hm5 : 5 ≤ n + 4 := by omega
  have hm6 : n + 4 ≠ 6 := by omega
  set ψ := toPerm eN hm5 hm6 with hψ
  have hψinj := toPerm_injective eN hm5 hm6 hC
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  set π := ψ α with hπdef
  have hπ2 : π * π = 1 := by rw [hπdef, ← map_mul, hαα, map_one]
  have hπ1 : π ≠ 1 := by
    intro h
    have h1 : α = 1 := hψinj (by rw [map_one]; exact h)
    rw [h1, orderOf_one] at hα2
    norm_num at hα2
  have hcomm : ∀ {y z : G}, y * z = z * y → ψ y * ψ z = ψ z * ψ y := fun h => by
    rw [← map_mul, ← map_mul, h]
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  set X := J.map ψ with hX
  have hXp : ⁅X, X⁆ = X := by rw [hX, ← map_commutator, hJp]
  have hXπ : ∀ x ∈ X, x * π = π * x := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcomm (mem_centralizer_singleton_iff.mp (hJα hy))
  have hJdvd := card_dvd_of_quot (by omega) eJ
  have hXcard : Nat.card X = Nat.card J := card_map_of_injective hψinj
  have hdvd : n.factorial / 2 ∣ Nat.card (centralizer ({π} : Set (Perm (Fin (n + 4))))) := by
    refine hJdvd.trans (hXcard ▸ card_dvd_of_le ?_)
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact hXπ x hx
  rcases card_cycleType_le_two hn hπ2 hπ1 hdvd with hk | hk
  · exfalso
    have hsupp : π.support.card = 2 := by
      rw [← sum_cycleType, Idx.cycleType_eq_replicate hπ2, hk]
      simp
    obtain ⟨i, j, hij, hπij⟩ := card_support_eq_two.mp hsupp
    exact false_of_swap hn eN hm5 hm6 hC hJα hJc eJ hij hπij
  obtain ⟨i, j, k, l, hn4, hπd, hsupp⟩ := exists_dt hπ2 hk
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := ne_of_nodup4 hn4
  set s : Finset (Fin (n + 4)) := {i, j, k, l} with hs
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_insert_of_notMem (by simp [hij, hik, hil]),
      Finset.card_insert_of_notMem (by simp [hjk, hjl]), Finset.card_pair hkl]
  have hXfix := fixes_support_of_perfect hXp hXπ (by rw [hsupp, hscard])
  have hXle : X ≤ altOff s := fun x hx =>
    mem_altOff (fun a ha => hXfix x hx a (by rw [hsupp]; exact ha))
      (le_alternatingGroup_of_perfect hXp hx)
  have hXeq : X = altOff s := by
    refine eq_of_le_of_card_ge hXle ?_
    rw [card_altOff s (by omega), hscard, hXcard, show n + 4 - 4 = n by omega]
    exact Nat.le_of_dvd Nat.card_pos hJdvd
  set ρ := ψ τ with hρdef
  have hρX : ∀ x ∈ altOff s, ρ * x = x * ρ := by
    rw [← hXeq]
    rintro _ ⟨y, hy, rfl⟩
    exact hcomm (hτJ y hy)
  have hρF : ∀ a, a ∉ s → ρ a = a := fun a ha =>
    eq_of_comm_altOff (by rw [hscard]; omega) hρX ha
  have hρπ : ρ * π = π * ρ := hcomm hτα
  have hpre : ∀ x : Perm (Fin (n + 4)), x ∈ alternatingGroup (Fin (n + 4)) →
      x * π = π * x → (∀ a, x a ∈ s ↔ a ∈ s) → x * x = 1 →
      ∃ c ∈ (N ⊓ normalizer (J : Set G)) ⊓ centralizer ({α} : Set G),
        ρ * (ψ c * x * (ψ c)⁻¹) = (ψ c * x * (ψ c)⁻¹) * ρ := by
    intro x hxA hxπ hxs hx2
    obtain ⟨g, hgN, hgx⟩ := exists_of_mem_alt eN hm5 hm6 hxA
    have hgα : g ∈ centralizer ({α} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      apply hψinj
      rw [map_mul, map_mul, hgx]
      exact hxπ
    have hgJ : g ∈ normalizer (J : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro y hy
      have h1 : ψ (g * y * g⁻¹) ∈ X := by
        rw [map_mul, map_mul, map_inv, hgx, hXeq]
        exact conj_mem_altOff hxs (hXeq ▸ ⟨y, hy, rfl⟩)
      obtain ⟨y', hy', hy'e⟩ := h1
      rw [← hψinj hy'e]
      exact hy'
    have hg2 : IsPGroup 2 ↥(zpowers g) := by
      rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := mem_zpowers_iff.mp hy
      refine ⟨1, Subtype.ext ?_⟩
      have hgg : g * g = 1 := hψinj (by rw [map_mul, hgx, hx2, map_one])
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [sq, ← zpow_add, ← two_mul, zpow_mul, zpow_two, hgg, one_zpow]
    obtain ⟨c, hc, hcR⟩ := exists_conj_le hRM hRα hRS
      (zpowers_le.mpr (mem_inf.mpr ⟨mem_inf.mpr ⟨hgN, hgJ⟩, hgα⟩)) hg2
    refine ⟨c, hc, ?_⟩
    have h1 := hcomm (hτR _ (hcR g (mem_zpowers g)))
    rw [map_mul, map_mul, map_inv, hgx] at h1
    exact h1
  obtain ⟨f₁, hf₁⟩ : ∃ f, f ∉ s := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin (n + 4))) ⊆ s := fun x _ => h x
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, hscard] at this
    omega
  obtain ⟨f₂, hf₂, hf12⟩ : ∃ f, f ∉ s ∧ f ≠ f₁ := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin (n + 4))) ⊆ insert f₁ s := fun x _ => by
      by_cases hx : x ∈ s
      · exact Finset.mem_insert_of_mem hx
      · rw [h x hx]
        exact Finset.mem_insert_self _ _
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem hf₁, hscard] at this
    omega
  simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hf₁ hf₂
  obtain ⟨hf₁i, hf₁j, hf₁k, hf₁l⟩ := hf₁
  obtain ⟨hf₂i, hf₂j, hf₂k, hf₂l⟩ := hf₂
  have hn6 : [i, j, k, l, f₁, f₂].Nodup := by
    simp [hij, hik, hil, hjk, hjl, hkl, Ne.symm hf₁i, Ne.symm hf₁j, Ne.symm hf₁k,
      Ne.symm hf₁l, Ne.symm hf₂i, Ne.symm hf₂j, Ne.symm hf₂k, Ne.symm hf₂l, Ne.symm hf12]
  have hd1 : [i, j, f₁, f₂].Nodup := hn6.sublist (by simp)
  have hd2 : [k, l, f₁, f₂].Nodup := hn6.sublist (by simp)
  have hd3 : [i, j, k, l].Nodup := hn4
  have hd4 : [i, k, j, l].Nodup := by simp [hij, hik, hil, hjl, hkl, Ne.symm hjk]
  have hsIJ : ∀ a, swap i j a ∈ s ↔ a ∈ s := swap_mem_iff (by simp [hs])
  have hsF : ∀ a, swap f₁ f₂ a ∈ s ↔ a ∈ s :=
    swap_mem_iff (by simp [hs, hf₁i, hf₁j, hf₁k, hf₁l, hf₂i, hf₂j, hf₂k, hf₂l])
  have hsIK : ∀ a, swap i k a ∈ s ↔ a ∈ s := swap_mem_iff (by simp [hs])
  have hsJL : ∀ a, swap j l a ∈ s ↔ a ∈ s := swap_mem_iff (by simp [hs])
  have hg₁π : (swap i j * swap f₁ f₂) * π = π * (swap i j * swap f₁ f₂) := by
    rw [hπd]
    have c1 : Commute (swap i j) (swap i j) := Commute.refl _
    have c2 : Commute (swap i j) (swap k l) := (disjoint_swap_swap hd3).commute
    have c3 : Commute (swap f₁ f₂) (swap i j) := (disjoint_swap_swap hd1).commute.symm
    have c4 : Commute (swap f₁ f₂) (swap k l) := (disjoint_swap_swap hd2).commute.symm
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  obtain ⟨c₁, hc₁, h₁⟩ := hpre _ (swap_mul_swap_mem_alt hij hf12.symm) hg₁π
    (fun a => by rw [Perm.mul_apply, hsIJ, hsF]) (sq_swap_mul_swap hd1)
  obtain ⟨c₂, hc₂, h₂⟩ := hpre _ (swap_mul_swap_mem_alt hik hjl)
    (by rw [hπd]; exact (dt_comm_cross hn4).symm)
    (fun a => by rw [Perm.mul_apply, hsIK, hsJL]) (sq_swap_mul_swap hd4)
  have hc₁π : ψ c₁ * π = π * ψ c₁ := hcomm (mem_centralizer_singleton_iff.mp hc₁.2)
  have hc₂π : ψ c₂ * π = π * ψ c₂ := hcomm (mem_centralizer_singleton_iff.mp hc₂.2)
  set σ₁ := (ψ c₁)⁻¹ * ρ * ψ c₁ with hσ₁
  have hσ₁π : σ₁ * π = π * σ₁ := by
    have hi : (ψ c₁)⁻¹ * π = π * (ψ c₁)⁻¹ := by
      calc (ψ c₁)⁻¹ * π = (ψ c₁)⁻¹ * (π * ψ c₁) * (ψ c₁)⁻¹ := by group
        _ = (ψ c₁)⁻¹ * (ψ c₁ * π) * (ψ c₁)⁻¹ := by rw [hc₁π]
        _ = π * (ψ c₁)⁻¹ := by group
    calc σ₁ * π = (ψ c₁)⁻¹ * ρ * (ψ c₁ * π) := by rw [hσ₁]; group
      _ = (ψ c₁)⁻¹ * ρ * (π * ψ c₁) := by rw [hc₁π]
      _ = (ψ c₁)⁻¹ * (ρ * π) * ψ c₁ := by group
      _ = (ψ c₁)⁻¹ * (π * ρ) * ψ c₁ := by rw [hρπ]
      _ = ((ψ c₁)⁻¹ * π) * ρ * ψ c₁ := by group
      _ = (π * (ψ c₁)⁻¹) * ρ * ψ c₁ := by rw [hi]
      _ = π * σ₁ := by rw [hσ₁]; group
  have hσ₁g : σ₁ * (swap i j * swap f₁ f₂) = (swap i j * swap f₁ f₂) * σ₁ := by
    calc σ₁ * (swap i j * swap f₁ f₂) =
        (ψ c₁)⁻¹ * (ρ * (ψ c₁ * (swap i j * swap f₁ f₂) * (ψ c₁)⁻¹)) * ψ c₁ := by
          rw [hσ₁]; group
      _ = (ψ c₁)⁻¹ * ((ψ c₁ * (swap i j * swap f₁ f₂) * (ψ c₁)⁻¹) * ρ) * ψ c₁ := by rw [h₁]
      _ = (swap i j * swap f₁ f₂) * σ₁ := by rw [hσ₁]; group
  have horb₁ := orbitwise_of_comm hπd hn6 hσ₁π hσ₁g
  have hρorb : Orbitwise π ρ := by
    have h := orbitwise_conj horb₁ hc₁π
    have e : ψ c₁ * σ₁ * (ψ c₁)⁻¹ = ρ := by rw [hσ₁]; group
    rwa [e] at h
  set σ₂ := (ψ c₂)⁻¹ * ρ * ψ c₂ with hσ₂
  have hc₂i : (ψ c₂)⁻¹ * π = π * (ψ c₂)⁻¹ := by
    calc (ψ c₂)⁻¹ * π = (ψ c₂)⁻¹ * (π * ψ c₂) * (ψ c₂)⁻¹ := by group
      _ = (ψ c₂)⁻¹ * (ψ c₂ * π) * (ψ c₂)⁻¹ := by rw [hc₂π]
      _ = π * (ψ c₂)⁻¹ := by group
  have horb₂ : Orbitwise π σ₂ := by
    have h := orbitwise_conj hρorb hc₂i
    rwa [inv_inv] at h
  have hσ₂g : σ₂ * (swap i k * swap j l) = (swap i k * swap j l) * σ₂ := by
    calc σ₂ * (swap i k * swap j l) =
        (ψ c₂)⁻¹ * (ρ * (ψ c₂ * (swap i k * swap j l) * (ψ c₂)⁻¹)) * ψ c₂ := by
          rw [hσ₂]; group
      _ = (ψ c₂)⁻¹ * ((ψ c₂ * (swap i k * swap j l) * (ψ c₂)⁻¹) * ρ) * ψ c₂ := by rw [h₂]
      _ = (swap i k * swap j l) * σ₂ := by rw [hσ₂]; group
  have hσ₂F : ∀ a, a ≠ i → a ≠ j → a ≠ k → a ≠ l → σ₂ a = a := by
    intro a hai haj hak hal
    have has : a ∉ π.support := by
      rw [hsupp, hs]
      simp [hai, haj, hak, hal]
    have hca : ψ c₂ a ∉ s := by
      rw [← hsupp]
      exact fun h => has ((mem_support_iff_of_comm hc₂π a).mp h)
    rw [hσ₂, Perm.mul_apply, Perm.mul_apply, hρF _ hca, ← Perm.mul_apply, inv_mul_cancel,
      Perm.one_apply]
  rcases eq_one_or_eq_of_comm hπd hn4 horb₂ hσ₂g hσ₂F with h | h
  · have hρ1 : ρ = 1 := by
      have e : ρ = ψ c₂ * σ₂ * (ψ c₂)⁻¹ := by rw [hσ₂]; group
      rw [e, h, mul_one, mul_inv_cancel]
    have : τ = 1 := hψinj (by rw [map_one]; exact hρ1)
    rw [this]
    exact one_mem _
  · have hρπ' : ρ = π := by
      have e : ρ = ψ c₂ * σ₂ * (ψ c₂)⁻¹ := by rw [hσ₂]; group
      rw [e, h, hc₂π, mul_inv_cancel_right]
    have : τ = α := hψinj hρπ'
    rw [this]
    exact mem_zpowers α

end AltCent

end CFSG.ComponentClassification.CatFactsL4U4
