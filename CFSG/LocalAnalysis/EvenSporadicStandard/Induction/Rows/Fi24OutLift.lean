module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Complement

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Closing

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H}

omit [Finite H] in
theorem fi24out_normalizerAction_of_mem (k : ↥L) :
    normalizerAction L ⟨(k : H), Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (k : ↥L ⧸ center ↥L) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [act_mk]
  show ((k * x * k⁻¹ : ↥L) : ↥L ⧸ center ↥L) = _
  rw [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

omit [Finite H] in
theorem fi24out_normalizerAction_mul {g h : H} (hg : g ∈ normalizer (L : Set H))
    (hh : h ∈ normalizer (L : Set H)) :
    normalizerAction L ⟨g * h, mul_mem hg hh⟩ =
      normalizerAction L ⟨g, hg⟩ * normalizerAction L ⟨h, hh⟩ := by
  rw [← map_mul]
  rfl

theorem fi24out_lift {t u t₁ : H} (hLperf : commutator ↥L = ⊤)
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2)
    (huN : u ∈ normalizer (L : Set H)) (huu : u * u = 1) (hut : u * t = t * u)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩))
    (hcent : ∀ σ : MulAut (↥L ⧸ center ↥L),
      σ * normalizerAction L ⟨u, huN⟩ = normalizerAction L ⟨u, huN⟩ * σ →
      ∃ m ∈ fixSubgroup (normalizerAction L ⟨u, huN⟩),
        σ = MulAut.conj m ∨ σ = normalizerAction L ⟨u, huN⟩ * MulAut.conj m)
    (ht₁N : t₁ ∈ normalizer (L : Set H)) (ht₁₁ : t₁ * t₁ = 1) (ht₁t : t₁ * t = t * t₁)
    (hcomm : normalizerAction L ⟨t₁, ht₁N⟩ * normalizerAction L ⟨u, huN⟩ =
      normalizerAction L ⟨u, huN⟩ * normalizerAction L ⟨t₁, ht₁N⟩) :
    ∃ e ∈ centralizer (L : Set H), e * t = t * e ∧
      (e * t₁ * e⁻¹) * u = u * (e * t₁ * e⁻¹) := by
  classical
  obtain ⟨K₀, hK₀C, hK₀odd, -, hK₀idx, hK₀norm⟩ := exists_K₀ hS2 htC ht2
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  set σ := normalizerAction L ⟨t₁, ht₁N⟩ with hσ
  have ht₁i : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁₁
  have key : ∀ (w : H) (hwN : w ∈ normalizer (L : Set H)), normalizerAction L ⟨w, hwN⟩ = σ →
      w * u = u * w →
      ∃ e ∈ centralizer (L : Set H), e * t = t * e ∧
        (e * t₁ * e⁻¹) * u = u * (e * t₁ * e⁻¹) := by
    intro w hwN hρw hwu
    set c : H := w⁻¹ * t₁ with hc
    have hcN : c ∈ normalizer (L : Set H) := mul_mem (inv_mem hwN) ht₁N
    have hcC : c ∈ centralizer (L : Set H) := by
      refine (normalizerAction_eq_one_iff hLperf ⟨c, hcN⟩).1 ?_
      have : (⟨c, hcN⟩ : ↥(normalizer (L : Set H))) = ⟨w, hwN⟩⁻¹ * ⟨t₁, ht₁N⟩ := rfl
      rw [this, map_mul, map_inv, hρw, inv_mul_cancel]
    have ht₁eq : t₁ = w * c := by rw [hc]; group
    have hyC : u * c⁻¹ * u⁻¹ ∈ centralizer (L : Set H) := by
      have := conj_mem_centralizer huN (Subgroup.inv_mem _ hcC)
      exact this
    set δ : H := c * (u * c⁻¹ * u⁻¹) with hδ
    have hδK : δ ∈ K₀ := by
      refine (hK₀idx c hcC _ hyC).2 ?_
      have hiff : (u * c⁻¹ * u⁻¹ ∈ K₀) ↔ c ∈ K₀ := by
        constructor
        · intro hy
          have h1 : u⁻¹ * (u * c⁻¹ * u⁻¹) * u⁻¹⁻¹ ∈ K₀ := hK₀norm u⁻¹ (inv_mem huN) _ hy
          have h2 : c⁻¹ ∈ K₀ := by
            have e : u⁻¹ * (u * c⁻¹ * u⁻¹) * u⁻¹⁻¹ = c⁻¹ := by group
            rwa [e] at h1
          simpa using K₀.inv_mem h2
        · intro hc'
          exact hK₀norm u huN _ (K₀.inv_mem hc')
      exact hiff.symm
    set x : H := (t₁ * u) * (t₁ * u) with hx
    have hxeq : x = w * δ * w⁻¹ := by
      have h1 : x = (t₁ * u * t₁⁻¹) * u := by rw [hx, ht₁i]; group
      have h2 : t₁ * u * t₁⁻¹ = (w * δ * w⁻¹) * (w * u * w⁻¹) := by
        calc t₁ * u * t₁⁻¹ = (w * c) * u * (w * c)⁻¹ := by rw [← ht₁eq]
          _ = (w * δ * w⁻¹) * (w * u * w⁻¹) := by rw [hδ]; group
      have h3 : w * u * w⁻¹ = u := by
        calc w * u * w⁻¹ = (u * w) * w⁻¹ := by rw [hwu]
          _ = u := by group
      rw [h1, h2, h3, mul_assoc, huu, mul_one]
    have hxK₀ : x ∈ K₀ := by
      rw [hxeq]
      exact hK₀norm w hwN δ hδK
    have hodd := hK₀odd x hxK₀
    have hxn : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    obtain ⟨e, he, hecomm⟩ := fi24out_odd_dihedral_commute ht₁₁ huu hodd hxn
    refine ⟨e, hK₀C ((Subgroup.zpowers_le.2 hxK₀) he), ?_, hecomm⟩
    have hxt : x * t = t * x := by
      have h1 : (t₁ * u) * t = t * (t₁ * u) := by
        calc t₁ * u * t = t₁ * (u * t) := by group
          _ = t₁ * (t * u) := by rw [hut]
          _ = (t₁ * t) * u := by group
          _ = (t * t₁) * u := by rw [ht₁t]
          _ = t * (t₁ * u) := by group
      calc x * t = (t₁ * u) * ((t₁ * u) * t) := by rw [hx]; group
        _ = (t₁ * u) * (t * (t₁ * u)) := by rw [h1]
        _ = ((t₁ * u) * t) * (t₁ * u) := by group
        _ = (t * (t₁ * u)) * (t₁ * u) := by rw [h1]
        _ = t * x := by rw [hx]; group
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (Commute.zpow_left (show Commute x t from hxt) j).eq
  obtain ⟨m, hm, hm'⟩ := hcent σ hcomm
  rw [← hbar] at hm
  obtain ⟨k, hkK, hkm⟩ := mem_bar.1 hm
  have hkK' : (k : H) ∈ K := Subgroup.mem_subgroupOf.1 hkK
  have hkN : (k : H) ∈ normalizer (L : Set H) := Subgroup.le_normalizer k.2
  rcases hm' with hm' | hm'
  · refine key (k : H) hkN ?_ (hKu _ hkK')
    rw [fi24out_normalizerAction_of_mem k, hkm, ← hm']
  · refine key (u * (k : H)) (mul_mem huN hkN) ?_ ?_
    · rw [fi24out_normalizerAction_mul huN hkN, fi24out_normalizerAction_of_mem k, hkm, ← hm']
    · calc u * (k : H) * u = u * ((k : H) * u) := by group
        _ = u * (u * (k : H)) := by rw [hKu _ hkK']

end CFSG.EvenSporadicStandard.Induction
