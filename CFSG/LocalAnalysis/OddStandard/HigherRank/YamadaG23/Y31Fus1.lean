module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31MFus
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31OutB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Inv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_fusion_zt (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) :
    ∃ g : G, g * s.t * g⁻¹ = s.fr.z ∨ g * s.t * g⁻¹ = s.fr.z * s.t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxne, hxcomm⟩ := Setup.exists_commuting_conjugate (L := L) hS s.t_order
  set t' : G := x * s.t * x⁻¹ with ht'def
  have hxne' : t' ≠ s.t := fun h => hxne (by simpa [ht'def] using h)
  have hxcomm' : s.t * t' = t' * s.t := by simpa [ht'def] using hxcomm
  have htt : s.t * s.t = 1 := by
    rw [← pow_two, ← s.t_order]
    exact pow_orderOf_eq_one s.t
  have ht'H : t' ∈ s.H := by
    change t' ∈ Subgroup.centralizer ({s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm'.symm
  have ht'2 : orderOf t' = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      show (x * s.t * x⁻¹) * (x * s.t * x⁻¹) = 1
      calc (x * s.t * x⁻¹) * (x * s.t * x⁻¹) = x * (s.t * s.t) * x⁻¹ := by group
        _ = 1 := by rw [htt]; group
    · intro h
      have hx1 : x * s.t * x⁻¹ = 1 := by simpa [ht'def] using h
      have ht1 : s.t = 1 := by
        calc s.t = x⁻¹ * (x * s.t * x⁻¹) * x := by group
          _ = 1 := by rw [hx1]; group
      have hord : orderOf s.t = 2 := s.t_order
      rw [ht1, orderOf_one] at hord
      omega
  by_cases ht'M : t' ∈ L ⊔ centIn s.H L
  · obtain ⟨l, _hlL, hl⟩ := s3_M_invol_fusion s hS hZ ht'M ht'2 hxne'
    refine ⟨l * x, ?_⟩
    have hg : (l * x) * s.t * (l * x)⁻¹ = l * t' * l⁻¹ := by
      rw [ht'def]
      group
    rw [hg]
    exact hl
  · have ht'N : t' ∈ normalizer (L : Set G) := s3_H_le_N s hS ht'H
    let α : MulAut (L ⧸ center L) := jHom L ⟨t', ht'N⟩
    have hαacts : ActsAs L t' α := jHom_actsAs L ⟨t', ht'N⟩
    have hαOut : α ∉ innerAut (L ⧸ center L) :=
      s3_outer_of_not_mem_M s hS ht'H ht'M hαacts
    have ht't : t' * t' = 1 := by
      rw [← pow_two, ← ht'2]
      exact pow_orderOf_eq_one t'
    have hα2 : α ^ 2 = 1 := by
      rw [pow_two]
      exact actsAs_unique L (by
        have h := actsAs_mul L hαacts hαacts
        rwa [ht't] at h) (actsAs_one L)
    obtain ⟨i, hiInn, hieq⟩ := frame_outer_invol_conj s.fr' s.facts hOut hα2 hαOut
    rw [← jSub_self] at hiInn
    obtain ⟨l₀, _hl₀L, hl₀acts⟩ := (mem_jSub L).mp hiInn
    set y : G := l₀ * x with hydef
    set t'' : G := y * s.t * y⁻¹ with ht''def
    have ht''eq : t'' = l₀ * t' * l₀⁻¹ := by
      rw [ht''def, hydef, ht'def]
      group
    have ht''acts : ActsAs L t'' s.fr'.σ := by
      have h1 : ActsAs L (l₀ * t' * l₀⁻¹) (i * α * i⁻¹) :=
        actsAs_mul L (actsAs_mul L hl₀acts hαacts) (actsAs_inv L hl₀acts)
      rw [← ht''eq, hieq] at h1
      exact h1
    have ht''2 : t'' ^ 2 = 1 := by
      rw [pow_two, ht''def]
      show (y * s.t * y⁻¹) * (y * s.t * y⁻¹) = 1
      calc (y * s.t * y⁻¹) * (y * s.t * y⁻¹) = y * (s.t * s.t) * y⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have ht''sq : t'' * t'' = 1 := by rw [← pow_two]; exact ht''2
    obtain ⟨u, huL, huinter, hu2, hcomm⟩ :=
      s3_exists_invol_inter s hS hZ hOut (y := y) (by rw [← ht''def]; exact ht''acts)
    have hcomm' : u * t'' = t'' * u := by rw [ht''def]; exact hcomm
    have hu_sq : u * u = 1 := by
      rw [← pow_two, ← hu2]
      exact pow_orderOf_eq_one u
    have hw : (t'' * u) ^ 2 = 1 := by
      rw [pow_two]
      show t'' * u * (t'' * u) = 1
      calc t'' * u * (t'' * u) = t'' * (u * t'') * u := by group
        _ = t'' * (t'' * u) * u := by rw [hcomm']
        _ = (t'' * t'') * (u * u) := by group
        _ = 1 := by rw [ht''sq, hu_sq, one_mul]
    obtain ⟨l₂, _hl₂L, hcoset⟩ :=
      s3_coset_invol_conj s hS hZ hOut ht''acts ht''2 huL hw
    set u' : G := y⁻¹ * u * y with hu'def
    have hu'L : u' ∈ L := by rw [hu'def]; exact huinter
    have hu'sq : u' * u' = 1 := by
      rw [hu'def]
      show (y⁻¹ * u * y) * (y⁻¹ * u * y) = 1
      calc (y⁻¹ * u * y) * (y⁻¹ * u * y) = y⁻¹ * (u * u) * y := by group
        _ = 1 := by rw [hu_sq]; group
    set l₃ : G := y⁻¹ * l₂ * y with hl₃def
    set τ : G := y⁻¹ * (t'' * u) * y with hτdef
    have hτeq : τ = l₃ * s.t * l₃⁻¹ := by
      rw [hτdef, hcoset, hl₃def, ht''def]
      group
    have hτtu : τ = s.t * u' := by
      rw [hτdef, ht''def, hu'def]
      group
    have ht_inf : s.t ∈ centIn s.H L :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, s.t_mem⟩
    have hτM : τ ∈ L ⊔ centIn s.H L := by
      rw [hτtu]
      have h := Subgroup.mul_mem_sup ht_inf hu'L
      rwa [sup_comm] at h
    have hτ2 : τ ^ 2 = 1 := by
      rw [hτtu, pow_two]
      show (s.t * u') * (s.t * u') = 1
      calc (s.t * u') * (s.t * u') = s.t * (u' * s.t) * u' := by group
        _ = s.t * (s.t * u') * u' := by rw [s3_comm_t_of_mem_L s hu'L]
        _ = (s.t * s.t) * (u' * u') := by group
        _ = 1 := by rw [htt, hu'sq, one_mul]
    have hτ1 : τ ≠ 1 := by
      intro h
      have htu : s.t * u' = 1 := by rw [← hτtu, h]
      have ht_eq : s.t = (u')⁻¹ := by
        calc s.t = (s.t * u') * (u')⁻¹ := by group
          _ = (u')⁻¹ := by rw [htu, one_mul]
      exact (s3_t_not_mem_L_of_odd s hZ)
        (by rw [ht_eq]; exact Subgroup.inv_mem L hu'L)
    have hτt : τ ≠ s.t := by
      intro h
      have htu : s.t * u' = s.t := by rw [← hτtu, h]
      have hu'1 : u' = 1 := by
        calc u' = s.t⁻¹ * (s.t * u') := by group
          _ = s.t⁻¹ * s.t := by rw [htu]
          _ = 1 := by group
      have hu1 : u = 1 := by
        calc u = y * (y⁻¹ * u * y) * y⁻¹ := by group
          _ = 1 := by rw [← hu'def, hu'1]; group
      rw [hu1, orderOf_one] at hu2
      omega
    have hτorder : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
    obtain ⟨l', _hl'L, hl'⟩ := s3_M_invol_fusion s hS hZ hτM hτorder hτt
    refine ⟨l' * l₃, ?_⟩
    have hg : (l' * l₃) * s.t * (l' * l₃)⁻¹ = l' * τ * l'⁻¹ := by
      rw [hτeq]
      group
    rw [hg]
    exact hl'

end CFSG.OddStandard.HigherRank.YamadaG23
