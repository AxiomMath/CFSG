module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneIdx
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAp

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp
  CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X G T : Subgroup (MulAut V)} {t : MulAut V}
  {m : ℕ}

namespace OneCfg

variable (c : OneCfg G T Y t m X) (D : CbData Y t m X)

include c in
theorem sign_eq_one_of_mem_QG {g : ↥G} (hg : g ∈ QG G X)
    (hn : ∀ y ∈ X, (g : MulAut V) * y * (g : MulAut V)⁻¹ ∈ X) {σ : Equiv.Perm (Fin (m + 2))}
    (hσ : ∀ (y : MulAut V) (hy : y ∈ X),
      (D.θ ⟨(g : MulAut V) * y * (g : MulAut V)⁻¹, hn y hy⟩ : Equiv.Perm (Fin (m + 2))) =
        σ * (D.θ ⟨y, hy⟩ : Equiv.Perm (Fin (m + 2))) * σ⁻¹) :
    Equiv.Perm.sign σ = 1 := by
  obtain ⟨x, hx, q, hq, hgxq⟩ := mem_QG.mp hg
  have hσx : σ = (D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) := by
    refine perm_unique (by have := c.hm; omega) (fun ρ => ?_)
    obtain ⟨y, rfl⟩ := D.θ.surjective ρ
    have h1 := hσ y y.2
    have h2 : (g : MulAut V) * y * (g : MulAut V)⁻¹ = x * y * x⁻¹ := by
      rw [hgxq]
      have hqy : q * (y : MulAut V) = y * q := (Subgroup.mem_centralizer_iff.mp hq y y.2).symm
      calc x * q * y * (x * q)⁻¹ = x * (q * y) * q⁻¹ * x⁻¹ := by group
        _ = x * (y * q) * q⁻¹ * x⁻¹ := by rw [hqy]
        _ = x * y * x⁻¹ := by group
    have h3 : (⟨(g : MulAut V) * y * (g : MulAut V)⁻¹, hn y y.2⟩ : ↥X) =
        ⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹ := Subtype.ext h2
    rw [h3, map_mul, map_mul, map_inv] at h1
    exact h1.symm
  rw [hσx]
  exact Equiv.Perm.mem_alternatingGroup.mp (D.θ ⟨x, hx⟩).2

include c in
theorem tG_not_mem_QG : c.tG ∉ QG G X := by
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  intro h
  have hs := c.sign_eq_one_of_mem_QG D h D.hn (σ := Equiv.swap D.a D.b) (fun y hy => by
    have := D.hconj y hy
    simpa [c.coe_tG] using this)
  rw [Equiv.Perm.sign_swap D.hab] at hs
  exact absurd hs (by decide)

include c in
theorem conj_not_mem_QG (a : ↥G) : a⁻¹ * c.tG * a ∉ QG G X := by
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  intro h
  have hN : ∀ y ∈ X, ((a⁻¹ * c.tG * a : ↥G) : MulAut V) * y *
      ((a⁻¹ * c.tG * a : ↥G) : MulAut V)⁻¹ ∈ X := by
    intro y hy
    obtain ⟨x, hx, q, hq, hgxq⟩ := mem_QG.mp h
    rw [hgxq]
    have hqy : q * y = y * q := (Subgroup.mem_centralizer_iff.mp hq y hy).symm
    have : x * q * y * (x * q)⁻¹ = x * y * x⁻¹ := by
      calc x * q * y * (x * q)⁻¹ = x * (q * y) * q⁻¹ * x⁻¹ := by group
        _ = x * (y * q) * q⁻¹ * x⁻¹ := by rw [hqy]
        _ = x * y * x⁻¹ := by group
    rw [this]
    exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  have hce : ((a⁻¹ * c.tG * a : ↥G) : MulAut V) =
      ((a⁻¹ : ↥G) : MulAut V) * t * ((a⁻¹ : ↥G) : MulAut V)⁻¹ := by
    simp [c.coe_tG]
  have hN' : ∀ y ∈ X, (((a⁻¹ : ↥G) : MulAut V) * t * ((a⁻¹ : ↥G) : MulAut V)⁻¹) * y *
      (((a⁻¹ : ↥G) : MulAut V) * t * ((a⁻¹ : ↥G) : MulAut V)⁻¹)⁻¹ ∈ X := by
    intro y hy
    have := hN y hy
    rwa [hce] at this
  obtain ⟨p, q, hpq, hσ⟩ := c.induces_transposition D (a⁻¹ : ↥G).2 hN'
  have hs := c.sign_eq_one_of_mem_QG D h hN (σ := Equiv.swap p q) (fun y hy => by
    have := hσ y hy
    simpa [hce] using this)
  rw [Equiv.Perm.sign_swap hpq] at hs
  exact absurd hs (by decide)

include c in
theorem mem_QG_or_mul_mem {n : ↥G} (hn : n ∈ NG G X) :
    n ∈ QG G X ∨ n * c.tG ∈ QG G X := by
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  obtain ⟨x, q, e, hx, hq, he, hnxq⟩ := D.normalizer_decomp c.hm hn
  have hee : e = 0 ∨ e = 1 := by omega
  rcases hee with rfl | rfl
  · left
    exact mem_QG.mpr ⟨x, hx, q, hq, by simpa using hnxq⟩
  · right
    refine mem_QG.mpr ⟨x, hx, q, hq, ?_⟩
    show (n : MulAut V) * t = x * q
    rw [hnxq, pow_one]
    calc x * q * t * t = x * q * (t * t) := by group
      _ = x * q := by rw [← pow_two, c.ht2]; group

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
