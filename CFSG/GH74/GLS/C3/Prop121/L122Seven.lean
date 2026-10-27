module

public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.MooreBasic
public import CFSG.GH74.GLS.C3.Prop121.TU

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

theorem lemma122_seven
    {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a₀ : G}
    {t u g : G} (h : IsAConfig 7 x K T Q S a₀) (hS : Stage3Loc 7 x K Q t u g)
    (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 7))
    (hι2 : ∀ c : ↥(centralizer ({x} : Set G)),
      (((ι c : Fgrp 7) : Amb 7).1 = 1 ↔ (c : G) ∈ Q))
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q)
    (hmem : g * t * g⁻¹ ∈ centralizer ({x} : Set G)) :
    (((ι ⟨g * t * g⁻¹, hmem⟩ : Fgrp 7) : Amb 7).1).IsThreeCycle := by
  classical
  have hn : (7 : ℕ) = 5 ∨ (7 : ℕ) = 6 ∨ (7 : ℕ) = 7 := Or.inr (Or.inr rfl)
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hginv : g⁻¹ = g := sq_eq_one_inv hS.g_sq
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  let cg : G ≃* G := MulAut.conj g
  have hcg : ∀ z : G, cg z = g * z * g⁻¹ := fun z => rfl
  have hcgcg : ∀ z : G, cg (cg z) = z := by
    intro z
    rw [hcg, hcg]
    have h1 : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg2, inv_one]
    calc g * (g * z * g⁻¹) * g⁻¹ = (g * g) * z * (g⁻¹ * g⁻¹) := by group
      _ = z := by rw [hg2, h1]; group
  let lam : ↥K →* Perm (Fin 7) :=
    (MonoidHom.fst (Perm (Fin 7)) (Perm (Fin 4))).comp
      ((Fgrp 7).subtype.comp (ι.toMonoidHom.comp (Subgroup.inclusion hKC)))
  have hlam1 : ∀ k : ↥K, ((ι ⟨k, hKC k.2⟩ : Fgrp 7) : Amb 7) = (lam k, 1) := by
    intro k
    have := (K_iff hn h hι2 ⟨k, hKC k.2⟩).1 k.2
    exact Prod.ext rfl this.2
  have hlamsign : ∀ k : ↥K, sign (lam k) = 1 := fun k =>
    ((K_iff hn h hι2 ⟨k, hKC k.2⟩).1 k.2).1
  have hlaminj : Function.Injective lam := by
    intro k₁ k₂ hk
    have h1 : ι ⟨k₁, hKC k₁.2⟩ = ι ⟨k₂, hKC k₂.2⟩ := by
      apply Subtype.ext
      rw [hlam1 k₁, hlam1 k₂, hk]
    exact Subtype.ext (congrArg (fun z : ↥(centralizer ({x} : Set G)) => (z : G)) (ι.injective h1))
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x⟩ := TU.exists_y hS.Q_card (x := x)
  have hQall := TU.Q_four hS.Q_card hS.Q_sq hS.x_mem hy₀Q hS.x_ne hy₀1 hy₀x
  have hXK : cg x ∈ K := hS.g_Q x hS.x_mem
  have hYK : cg y₀ ∈ K := hS.g_Q y₀ hy₀Q
  have hTK : cg t ∈ K := hS.gt_K
  let X : ↥K := ⟨cg x, hXK⟩
  let Y : ↥K := ⟨cg y₀, hYK⟩
  let T' : ↥K := ⟨cg t, hTK⟩
  show (lam T').IsThreeCycle
  have hx2 : x * x = 1 := by rw [← sq]; exact hS.x_sq
  have hy2 : y₀ * y₀ = 1 := by rw [← sq]; exact hS.Q_sq y₀ hy₀Q
  have hxy : x * y₀ = y₀ * x := hS.Q_comm x hS.x_mem y₀ hy₀Q
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht3' : t * t * t = 1 := by
    calc t * t * t = t ^ 3 := (pow_three' t).symm
      _ = 1 := ht3
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have hcgne : ∀ z : G, z ≠ 1 → cg z ≠ 1 := fun z hz h1 =>
    hz (cg.injective (by rw [h1, map_one]))
  set α := lam X with hα
  set β := lam Y with hβ
  set σ := lam T' with hσ
  have hXX : X * X = 1 := by
    apply Subtype.ext
    show cg x * cg x = 1
    rw [← map_mul, hx2, map_one]
  have hYY : Y * Y = 1 := by
    apply Subtype.ext
    show cg y₀ * cg y₀ = 1
    rw [← map_mul, hy2, map_one]
  have hXY : X * Y = Y * X := by
    apply Subtype.ext
    show cg x * cg y₀ = cg y₀ * cg x
    rw [← map_mul, ← map_mul, hxy]
  have hX1 : X ≠ 1 := fun h1 => hcgne x hS.x_ne (congrArg Subtype.val h1)
  have hY1 : Y ≠ 1 := fun h1 => hcgne y₀ hy₀1 (congrArg Subtype.val h1)
  have hXYne : X ≠ Y := fun h1 => hy₀x (cg.injective (congrArg Subtype.val h1)).symm
  have hT3 : T' * T' * T' = 1 := by
    apply Subtype.ext
    show cg t * cg t * cg t = 1
    rw [← map_mul, ← map_mul, ht3', map_one]
  have hT1 : T' ≠ 1 := fun h1 => hcgne t ht1 (congrArg Subtype.val h1)
  have hαp : α * α = 1 ∧ α ≠ 1 ∧ sign α = 1 :=
    ⟨by rw [hα, ← map_mul, hXX, map_one],
      fun h1 => hX1 (hlaminj (h1.trans (map_one lam).symm)), hlamsign X⟩
  have hβp : β * β = 1 ∧ β ≠ 1 ∧ sign β = 1 :=
    ⟨by rw [hβ, ← map_mul, hYY, map_one],
      fun h1 => hY1 (hlaminj (h1.trans (map_one lam).symm)), hlamsign Y⟩
  have habp : α * β = β * α ∧ α ≠ β :=
    ⟨by rw [hα, hβ, ← map_mul, ← map_mul, hXY], fun h1 => hXYne (hlaminj h1)⟩
  have hσp : σ * σ * σ = 1 ∧ σ ≠ 1 :=
    ⟨by rw [hσ, ← map_mul, ← map_mul, hT3, map_one],
      fun h1 => hT1 (hlaminj (h1.trans (map_one lam).symm))⟩
  have htx : t * x * t⁻¹ ∈ Q := hS.t_norm_Q x hS.x_mem
  have htx1 : t * x * t⁻¹ ≠ 1 := by
    intro h1
    apply hS.x_ne
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have htxx : t * x * t⁻¹ ≠ x := by
    intro h1
    have hc : t * x = x * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h1]
    have h3 : (t * x) ^ 3 = 1 := hS.tx_cube
    have h4 : (t * x) ^ 3 = x := by
      rw [Commute.mul_pow (show Commute t x from hc), ht3, one_mul]
      calc x ^ 3 = x ^ 2 * x := pow_succ x 2
        _ = x := by rw [hS.x_sq, one_mul]
    exact hS.x_ne (h4.symm.trans h3)
  have hTXT : T' * X * T'⁻¹ = Y ∨ T' * X * T'⁻¹ = X * Y := by
    rcases hQall (t * x * t⁻¹) htx with h1 | h1 | h1 | h1
    · exact absurd h1 htx1
    · exact absurd h1 htxx
    · left
      apply Subtype.ext
      show cg t * cg x * (cg t)⁻¹ = cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right
      apply Subtype.ext
      show cg t * cg x * (cg t)⁻¹ = cg x * cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have hσa : σ * α * σ⁻¹ = β ∨ σ * α * σ⁻¹ = α * β := by
    have e : σ * α * σ⁻¹ = lam (T' * X * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hTXT with h1 | h1
    · left; rw [e, h1]
    · right; rw [e, h1, map_mul]
  have hty : t * y₀ * t⁻¹ ∈ Q := hS.t_norm_Q y₀ hy₀Q
  have hty1 : t * y₀ * t⁻¹ ≠ 1 := by
    intro h1
    apply hy₀1
    calc y₀ = t⁻¹ * (t * y₀ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have hTYT : T' * Y * T'⁻¹ = X ∨ T' * Y * T'⁻¹ = Y ∨ T' * Y * T'⁻¹ = X * Y := by
    rcases hQall (t * y₀ * t⁻¹) hty with h1 | h1 | h1 | h1
    · exact absurd h1 hty1
    · left
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg x
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right; left
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right; right
      apply Subtype.ext
      show cg t * cg y₀ * (cg t)⁻¹ = cg x * cg y₀
      rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have hσb : σ * β * σ⁻¹ = α ∨ σ * β * σ⁻¹ = β ∨ σ * β * σ⁻¹ = α * β := by
    have e : σ * β * σ⁻¹ = lam (T' * Y * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hTYT with h1 | h1 | h1
    · left; rw [e, h1]
    · right; left; rw [e, h1]
    · right; right; rw [e, h1, map_mul]
  have hιmul : ∀ z w : ↥(centralizer ({x} : Set G)),
      ((ι (z * w) : Fgrp 7) : Amb 7) = ((ι z : Fgrp 7) : Amb 7) * ((ι w : Fgrp 7) : Amb 7) :=
    fun z w => by rw [map_mul]; rfl
  have hXC : cg x ∈ centralizer ({x} : Set G) := hKC hXK
  have hYC : cg y₀ ∈ centralizer ({x} : Set G) := hKC hYK
  have hιX : ((ι ⟨cg x, hXC⟩ : Fgrp 7) : Amb 7) = (α, 1) := hlam1 X
  have hιY : ((ι ⟨cg y₀, hYC⟩ : Fgrp 7) : Amb 7) = (β, 1) := hlam1 Y
  have hιT : ((ι ⟨cg t, hmem⟩ : Fgrp 7) : Amb 7) = (σ, 1) := hlam1 T'
  have hρ : ∃ ρ : Perm (Fin 7), ρ * ρ * ρ = 1 ∧ ρ ≠ 1 ∧ ρ * α = α * ρ ∧ ρ * β = β * ρ := by
    obtain ⟨ρ₀, hρ₀3, hρ₀1, hρ₀s, hρ₀α⟩ := exists_ord3_comm hαp
    have hmemF : ((ρ₀, 1) : Amb 7) ∈ Fgrp 7 := ⟨by simp, by simp [hρ₀s]⟩
    obtain ⟨s, hs⟩ := ι.surjective ⟨(ρ₀, 1), hmemF⟩
    have hs' : ((ι s : Fgrp 7) : Amb 7) = (ρ₀, 1) := by rw [hs]
    have hsK : (s : G) ∈ K := (K_iff hn h hι2 s).2 (by rw [hs']; exact ⟨hρ₀s, rfl⟩)
    let sK : ↥K := ⟨s, hsK⟩
    have hlams : lam sK = ρ₀ := by
      have h1 := hlam1 sK
      have h2 : ((ι ⟨sK.1, hKC sK.2⟩ : Fgrp 7) : Amb 7) = (ρ₀, 1) := hs'
      exact (Prod.ext_iff.1 (h1.symm.trans h2)).1
    have hsXK : sK * X = X * sK := by
      apply hlaminj
      rw [map_mul, map_mul, hlams, ← hα]
      exact hρ₀α
    have hsX : (s : G) * cg x = cg x * s := congrArg Subtype.val hsXK
    have hsQ : ∀ q ∈ Q, (s : G) * q = q * s := fun q hq => hS.K_comm_Q s hsK q hq
    have hc'x : x * cg s = cg s * x := by
      have := congrArg cg hsX
      rw [map_mul, map_mul, hcgcg] at this
      exact this.symm
    have hc'C : cg s ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hc'x.symm
    let c'C : ↥(centralizer ({x} : Set G)) := ⟨cg s, hc'C⟩
    set f : Fgrp 7 := ι c'C with hf
    have hc'X : c'C * ⟨cg x, hXC⟩ = ⟨cg x, hXC⟩ * c'C := by
      apply Subtype.ext
      show cg s * cg x = cg x * cg s
      rw [← map_mul, ← map_mul, hsQ x hS.x_mem]
    have hc'Y : c'C * ⟨cg y₀, hYC⟩ = ⟨cg y₀, hYC⟩ * c'C := by
      apply Subtype.ext
      show cg s * cg y₀ = cg y₀ * cg s
      rw [← map_mul, ← map_mul, hsQ y₀ hy₀Q]
    have hρα : (f : Amb 7).1 * α = α * (f : Amb 7).1 := by
      have h1 := congrArg (fun z : ↥(centralizer ({x} : Set G)) => ((ι z : Fgrp 7) : Amb 7).1) hc'X
      simp only [hιmul, hιX, Prod.fst_mul] at h1
      exact h1
    have hρβ : (f : Amb 7).1 * β = β * (f : Amb 7).1 := by
      have h1 := congrArg (fun z : ↥(centralizer ({x} : Set G)) => ((ι z : Fgrp 7) : Amb 7).1) hc'Y
      simp only [hιmul, hιY, Prod.fst_mul] at h1
      exact h1
    have hs3 : s * s * s = 1 := by
      apply ι.injective
      apply Subtype.ext
      show ((ι (s * s * s) : Fgrp 7) : Amb 7) = ((ι 1 : Fgrp 7) : Amb 7)
      rw [hιmul, hιmul, hs', map_one]
      show ((ρ₀, 1) * (ρ₀, 1) * (ρ₀, 1) : Amb 7) = 1
      rw [Prod.mk_mul_mk, Prod.mk_mul_mk, hρ₀3]
      rfl
    have hc'3 : c'C * c'C * c'C = 1 := by
      apply Subtype.ext
      show cg s * cg s * cg s = 1
      have hs3G : (s : G) * s * s = 1 := congrArg (fun z : ↥(centralizer ({x} : Set G)) => (z : G)) hs3
      rw [← map_mul, ← map_mul, hs3G, map_one]
    have hf3 : (f : Amb 7) * (f : Amb 7) * (f : Amb 7) = 1 := by
      have := congrArg (fun z : ↥(centralizer ({x} : Set G)) => ((ι z : Fgrp 7) : Amb 7)) hc'3
      simp only [hιmul, map_one] at this
      exact this
    have hρ3 : (f : Amb 7).1 * (f : Amb 7).1 * (f : Amb 7).1 = 1 := by
      have := congrArg Prod.fst hf3
      simpa using this
    have hd3 : (f : Amb 7).2 * (f : Amb 7).2 * (f : Amb 7).2 = 1 := by
      have := congrArg Prod.snd hf3
      simpa using this
    have hd : (f : Amb 7).2 = 1 := eq_one_of_cube_eq_one _ f.2.1 hd3
    have hρ1 : (f : Amb 7).1 ≠ 1 := by
      intro h1
      have hf1 : f = 1 := Subtype.ext (Prod.ext h1 hd)
      have hc' : c'C = 1 := ι.injective (by rw [← hf, hf1, map_one])
      have hcs : cg s = 1 := congrArg Subtype.val hc'
      have hs1 : s = 1 := Subtype.ext (cg.injective (by rw [hcs]; simp))
      have h2 : ((ρ₀, 1) : Amb 7) = 1 := by rw [← hs', hs1, map_one]; rfl
      exact hρ₀1 (Prod.ext_iff.1 h2).1
    exact ⟨(f : Amb 7).1, hρ3, hρ1, hρα, hρβ⟩
  have hτ : ∀ i j : Fin 7, i ≠ j → swap i j * α = α * swap i j → swap i j * β = β * swap i j →
      (σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = 1 ∨ σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = α ∨
        σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = β ∨ σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = α * β) := by
    intro i j hij hα' hβ'
    have hmemF : ((swap i j, swap 0 1) : Amb 7) ∈ Fgrp 7 :=
      ⟨by show (swap (0 : Fin 4) 1) * x4 = x4 * swap 0 1; decide,
        by show sign (swap i j) = sign (swap (0 : Fin 4) 1)
           rw [sign_swap hij, sign_swap (by decide)]⟩
    obtain ⟨yf, hyf⟩ := ι.surjective ⟨(swap i j, swap 0 1), hmemF⟩
    have hyf' : ((ι yf : Fgrp 7) : Amb 7) = (swap i j, swap 0 1) := by rw [hyf]
    have hyfX : yf * ⟨cg x, hXC⟩ = ⟨cg x, hXC⟩ * yf := by
      apply ι.injective
      apply Subtype.ext
      show ((ι (yf * ⟨cg x, hXC⟩) : Fgrp 7) : Amb 7) = ((ι (⟨cg x, hXC⟩ * yf) : Fgrp 7) : Amb 7)
      rw [hιmul, hιmul, hyf', hιX]
      exact Prod.ext hα' (by simp)
    have hyfY : yf * ⟨cg y₀, hYC⟩ = ⟨cg y₀, hYC⟩ * yf := by
      apply ι.injective
      apply Subtype.ext
      show ((ι (yf * ⟨cg y₀, hYC⟩) : Fgrp 7) : Amb 7) = ((ι (⟨cg y₀, hYC⟩ * yf) : Fgrp 7) : Amb 7)
      rw [hιmul, hιmul, hyf', hιY]
      exact Prod.ext hβ' (by simp)
    have hyfX' : (yf : G) * cg x = cg x * (yf : G) := congrArg Subtype.val hyfX
    have hyfY' : (yf : G) * cg y₀ = cg y₀ * (yf : G) := congrArg Subtype.val hyfY
    have hyfQ : ∀ q ∈ Q, cg (yf : G) * q = q * cg (yf : G) := by
      intro q hq
      have h1 : (yf : G) * cg q = cg q * (yf : G) := by
        rcases hQall q hq with h2 | h2 | h2 | h2
        · rw [h2, map_one]; simp
        · rw [h2]; exact hyfX'
        · rw [h2]; exact hyfY'
        · rw [h2, map_mul]
          exact ((show Commute (yf : G) (cg x) from hyfX').mul_right
            (show Commute (yf : G) (cg y₀) from hyfY')).eq
      have h2 := congrArg cg h1
      rw [map_mul, map_mul, hcgcg] at h2
      exact h2
    obtain ⟨k, hk, q', hq', hc⟩ := hCQ (cg (yf : G)) hyfQ
    have hcomm : t * cg (yf : G) * t⁻¹ * (cg (yf : G))⁻¹ ∈ Q := by
      rw [hc]
      have htk : t * k = k * t := hS.t_comm_K k hk
      have hq'1 : t * q' * t⁻¹ ∈ Q := hS.t_norm_Q q' hq'
      have hkq : ∀ r ∈ Q, k * r = r * k := fun r hr => hS.K_comm_Q k hk r hr
      have hA : (t * q' * t⁻¹) * q'⁻¹ ∈ Q := Q.mul_mem hq'1 (Q.inv_mem hq')
      have e : t * (k * q') * t⁻¹ * (k * q')⁻¹ = (t * q' * t⁻¹) * q'⁻¹ := by
        calc t * (k * q') * t⁻¹ * (k * q')⁻¹
            = (t * k) * q' * t⁻¹ * (q'⁻¹ * k⁻¹) := by group
          _ = (k * t) * q' * t⁻¹ * (q'⁻¹ * k⁻¹) := by rw [htk]
          _ = k * ((t * q' * t⁻¹) * q'⁻¹) * k⁻¹ := by group
          _ = (t * q' * t⁻¹) * q'⁻¹ := by rw [hkq _ hA]; group
      rw [e]
      exact hA
    have hW : cg (t * cg (yf : G) * t⁻¹ * (cg (yf : G))⁻¹) =
        cg t * (yf : G) * (cg t)⁻¹ * (yf : G)⁻¹ := by
      simp only [map_mul, map_inv, hcgcg]
    have hWmem : cg t * (yf : G) * (cg t)⁻¹ * (yf : G)⁻¹ = 1 ∨
        cg t * (yf : G) * (cg t)⁻¹ * (yf : G)⁻¹ = cg x ∨
        cg t * (yf : G) * (cg t)⁻¹ * (yf : G)⁻¹ = cg y₀ ∨
        cg t * (yf : G) * (cg t)⁻¹ * (yf : G)⁻¹ = cg x * cg y₀ := by
      rw [← hW]
      rcases hQall _ hcomm with h1 | h1 | h1 | h1
      · left; rw [h1, map_one]
      · right; left; rw [h1]
      · right; right; left; rw [h1]
      · right; right; right; rw [h1, map_mul]
    have hιW : ((ι ((⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G))) * yf *
          (⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * yf⁻¹) : Fgrp 7) : Amb 7).1 =
        σ * swap i j * σ⁻¹ * (swap i j)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hιT, hyf', Prod.fst_mul,
        Prod.fst_inv]
    have hWc : ((⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G))) * yf *
          (⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * yf⁻¹ = 1) ∨
        ((⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G))) * yf *
          (⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * yf⁻¹ = ⟨cg x, hXC⟩) ∨
        ((⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G))) * yf *
          (⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * yf⁻¹ = ⟨cg y₀, hYC⟩) ∨
        ((⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G))) * yf *
          (⟨cg t, hmem⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * yf⁻¹ =
          ⟨cg x, hXC⟩ * ⟨cg y₀, hYC⟩) := by
      rcases hWmem with h1 | h1 | h1 | h1
      · left; exact Subtype.ext h1
      · right; left; exact Subtype.ext h1
      · right; right; left; exact Subtype.ext h1
      · right; right; right; exact Subtype.ext h1
    rw [← hιW]
    rcases hWc with h1 | h1 | h1 | h1
    · left; rw [h1, map_one]; rfl
    · right; left; rw [h1, hιX]
    · right; right; left; rw [h1, hιY]
    · right; right; right
      rw [h1, hιmul, hιX, hιY]
      simp
  exact finite122 hαp hβp habp hρ hσp hσa hσb hτ

end CFSG.GH74.GLS.C3.Prop121
