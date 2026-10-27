module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.One

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.TwoHS

theorem no_order_fifteen_z2s5 {C : Type*} [Group C]
    (ζ : C ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    ∀ c : C, c ^ 15 = 1 → c ^ 3 = 1 ∨ c ^ 5 = 1 := by
  intro c hc
  have h := congrArg ζ hc
  rw [map_pow, map_one] at h
  have h1 : (ζ c).1 ^ 15 = 1 := by
    have := congrArg Prod.fst h
    simpa using this
  have h2 : (ζ c).2 ^ 15 = 1 := by
    have := congrArg Prod.snd h
    simpa using this
  have hfst : ∀ a : Multiplicative (ZMod 2), a ^ 15 = 1 → a ^ 3 = 1 ∧ a ^ 5 = 1 := by decide
  obtain ⟨h3, h5⟩ := hfst _ h1
  rcases perm_five_no_orders.2 _ h2 with h' | h'
  · left
    apply ζ.injective
    rw [map_pow, map_one]
    exact Prod.ext h3 h'
  · right
    apply ζ.injective
    rw [map_pow, map_one]
    exact Prod.ext h5 h'

theorem noZ2S5PSp45_holds :
    NoZ2S5PSp45 := by
  intro G _ _ S hSn hS hcent t ht _ ⟨ζ⟩
  haveI := hSn
  obtain ⟨ψ, hψ⟩ := exists_pgsp45Emb S hS hcent
  have hN : Nat.card ↥(centralizer ({t} : Set G)) = 240 := card_centralizer_of_equiv ζ
  have hno15 : ∀ c ∈ centralizer ({t} : Set G), c ^ 15 = 1 → c ^ 3 = 1 ∨ c ^ 5 = 1 := by
    intro c hc h15
    have := no_order_fifteen_z2s5 ζ ⟨c, hc⟩ (Subtype.ext (by simpa using h15))
    rcases this with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := hψ.exists_conj_tau1 ht hno15 (by rw [hN]; norm_num) (by rw [hN]; norm_num)
  have h960 := card_centralizer_ge_of_conj_tau1 hg
  have hle := hψ.card_le_two_mul (centralizer ({ψ t} : Set PGSp45))
  have hdvd := hψ.card_inf_dvd t (centralizer ({ψ t} : Set PGSp45)) le_rfl
  have h240 : Nat.card ↥(ψ.range ⊓ centralizer ({ψ t} : Set PGSp45)) ≤ 240 := by
    rw [← hN]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have := h960.trans (hle.trans (Nat.mul_le_mul_left 2 h240))
  norm_num at this

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
