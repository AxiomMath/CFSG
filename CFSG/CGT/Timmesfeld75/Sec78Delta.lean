module

public import CFSG.CGT.Timmesfeld75.Sec78Final

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem conj_comm_of_comm {w b c : G} (hw : w * c = c * w) (hb : b * c = c * b) :
    (w * b * w⁻¹) * c = c * (w * b * w⁻¹) := by
  have h1 : w⁻¹ * c * w = c := by
    calc w⁻¹ * c * w = w⁻¹ * (c * w) := by group
      _ = w⁻¹ * (w * c) := by rw [hw]
      _ = c := by group
  calc (w * b * w⁻¹) * c = w * b * (w⁻¹ * c * w) * w⁻¹ := by group
    _ = w * b * c * w⁻¹ := by rw [h1]
    _ = w * (b * c) * w⁻¹ := by group
    _ = w * (c * b) * w⁻¹ := by rw [hb]
    _ = (w * c) * b * w⁻¹ := by group
    _ = (c * w) * b * w⁻¹ := by rw [hw]
    _ = c * (w * b * w⁻¹) := by group

theorem comm_mul_of_conj {w b x z : G} (hw : w * (x * z) = (x * z) * w)
    (hbx : (w⁻¹ * b * w) * x = x * (w⁻¹ * b * w)) (hbz : (w⁻¹ * b * w) * z = z * (w⁻¹ * b * w)) :
    b * (x * z) = (x * z) * b := by
  have hbc : (w⁻¹ * b * w) * (x * z) = (x * z) * (w⁻¹ * b * w) := by
    calc (w⁻¹ * b * w) * (x * z) = ((w⁻¹ * b * w) * x) * z := by group
      _ = (x * (w⁻¹ * b * w)) * z := by rw [hbx]
      _ = x * ((w⁻¹ * b * w) * z) := by group
      _ = x * (z * (w⁻¹ * b * w)) := by rw [hbz]
      _ = (x * z) * (w⁻¹ * b * w) := by group
  have h := conj_comm_of_comm hw hbc
  have e : w * (w⁻¹ * b * w) * w⁻¹ = b := by group
  rwa [e] at h

section Delta

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.false_of_delta (h63 : Sec63) (h77 : Sec77) (hc : Sec6Ctx T T₁ n m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1))
    (M : TModel T T₁ n m) {x z δ w : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hz : z ∈ normD T)
    (hzT : z ∉ T) (hxz : x * z = z * x) (hxzD : x * z ∉ classD T) (hδ : δ ∈ normD T)
    (hδT : δ ∉ T) (hδx : δ * x = x * δ) (hδz : δ * z = z * δ)
    {fδ fz : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {vδ vz : Fin n → GaloisField 2 m} (hvδ : vδ ≠ 0) (hvz : vz ≠ 0)
    (hdδ : ∀ v, sact (ubar M.ε δ) v = v + fδ v • vδ)
    (hdz : ∀ v, sact (ubar M.ε z) v = v + fz v • vz)
    (hind : ∀ r t : GaloisField 2 m, r • fδ + t • fz = 0 → r = 0 ∧ t = 0)
    (hw : w * (x * z) = (x * z) * w) (hconj : δ = w * z * w⁻¹ ∨ δ = w * x * w⁻¹) : False := by
  have := hc.finite
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hz1 : z ≠ 1 := ne_one_of_mem_classD hz.1
  have hzc : Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set G)) = (2 ^ m) ^ (n - 1) := by
    rcases h63 G T T₁ n m hc z hz hzT with h | ⟨h16, h8, -⟩
    · rw [h]
      exact hc.card_normIn
    · exact absurd (hc.card_eq_sixteen_iff.1 ⟨h16, h8⟩) hA8
  rcases hconj with hδw | hδw
  ·
    obtain ⟨k, t, ht, -, hzk⟩ := hz.1
    have hzT' : z ∈ conjSubgroup k⁻¹ T := by
      rw [mem_conjSubgroup, inv_inv, hzk]
      have e : k * (k⁻¹ * t * k) * k⁻¹ = t := by group
      rw [e]
      exact ht
    have hT'T : conjSubgroup k⁻¹ T ≠ T := fun h => hzT (h ▸ hzT')
    have hxN' : x ∈ Subgroup.normalizer ((conjSubgroup k⁻¹ T : Subgroup G) : Set G) :=
      (hTwc.conj k⁻¹).centralizer_le_normalizer hzT' hz1
        (Subgroup.mem_centralizer_singleton_iff.2 hxz)
    have hxL : x ∈ normIn T (conjSubgroup k⁻¹ T) := mem_normIn.2 ⟨hxT, hxN'⟩
    have hbot : normIn T (conjSubgroup k⁻¹ T) ≠ ⊥ := fun h0 => hx1 (by
      have h' := hxL
      rw [h0, Subgroup.mem_bot] at h'
      exact h')
    have hS3 : Sec3 T (conjSubgroup k⁻¹ T) := hc.hS k⁻¹ hT'T hbot
    have hCx : conjSubgroup k⁻¹ T ⊓ Subgroup.centralizer ({x} : Set G) =
        normIn (conjSubgroup k⁻¹ T) T := hS3.cfg.symm.inf_centralizer_eq_normIn hxL hx1
    have hzN : z ∈ normIn (conjSubgroup k⁻¹ T) T := mem_normIn.2 ⟨hzT', hz.2⟩
    have hCz : T ⊓ Subgroup.centralizer ({z} : Set G) = normIn T (conjSubgroup k⁻¹ T) :=
      hS3.cfg.inf_centralizer_eq_normIn hzN hz1
    obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = conjSubgroup w
        (conjSubgroup k⁻¹ T ⊓ Subgroup.centralizer ({x} : Set G)) := ⟨_, rfl⟩
    have hBs : B ≤ conjSubgroup (w * k⁻¹) T := by
      rw [hB, ← conjSubgroup_conjSubgroup]
      exact conjSubgroup_mono inf_le_left
    have hδB : δ ∈ B := by
      rw [hB, mem_conjSubgroup]
      have e : w⁻¹ * δ * w = z := by rw [hδw]; group
      rw [e]
      exact ⟨hzT', Subgroup.mem_centralizer_singleton_iff.2 hxz.symm⟩
    have hsT : conjSubgroup (w * k⁻¹) T ≠ T := fun h => hδT (h ▸ hBs hδB)
    have hBc : ∀ b ∈ B, b * (x * z) = (x * z) * b := by
      intro b hb
      rw [hB, mem_conjSubgroup] at hb
      obtain ⟨hb1, hb2⟩ := hb
      exact comm_mul_of_conj hw (Subgroup.mem_centralizer_singleton_iff.1 hb2)
        (elemAbelian_mul_comm (isElemAbelian_conjSubgroup hTab k⁻¹) hb1 hzT')
    have hBcard : Nat.card B = (2 ^ m) ^ (n - 1) := by
      rw [hB, card_conjSubgroup, hCx, hS3.card_normIn_swap, ← hCz]
      exact hzc
    exact hc.false_of_big_group h77 hnat hn3 hA8 M hxT hx1 hz hzT hxz hxzD hδ hδx hδz
      (Or.inl rfl) hBs hsT hBc hδB hBcard hvδ hvz hdδ hdz hind
  ·
    obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = conjSubgroup w
        (T ⊓ Subgroup.centralizer ({z} : Set G)) := ⟨_, rfl⟩
    have hBs : B ≤ conjSubgroup w T := by
      rw [hB]
      exact conjSubgroup_mono inf_le_left
    have hδB : δ ∈ B := by
      rw [hB, mem_conjSubgroup]
      have e : w⁻¹ * δ * w = x := by rw [hδw]; group
      rw [e]
      exact ⟨hxT, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩
    have hsT : conjSubgroup w T ≠ T := fun h => hδT (h ▸ hBs hδB)
    have hBc : ∀ b ∈ B, b * (x * z) = (x * z) * b := by
      intro b hb
      rw [hB, mem_conjSubgroup] at hb
      obtain ⟨hb1, hb2⟩ := hb
      exact comm_mul_of_conj hw (elemAbelian_mul_comm hTab hb1 hxT)
        (Subgroup.mem_centralizer_singleton_iff.1 hb2)
    have hBcard : Nat.card B = (2 ^ m) ^ (n - 1) := by
      rw [hB, card_conjSubgroup]
      exact hzc
    exact hc.false_of_big_group h77 hnat hn3 hA8 M hxT hx1 hz hzT hxz hxzD hδ hδx hδz
      (Or.inr rfl) hBs hsT hBc hδB hBcard hvδ hvz hdδ hdz hind

end Delta

end CFSG.CGT.Timmesfeld75
