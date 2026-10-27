module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.RootChecks

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

@[expose] def e6DiagCoeff : Fin 6 → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def idxPair : List ℤ → ℕ → ℤ
  | [], _ => 0
  | x :: cs, j => x * ((j / 3 ^ cs.length : ℕ) : ℤ) + idxPair cs (j % 3 ^ cs.length)

theorem idxPair_vecIdx : ∀ (c : List ℤ) (v : List ℕ), v.length = c.length →
    (∀ x ∈ v, x < 3) → idxPair c (vecIdx v) = rootDot c v
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | x :: cs, y :: vs, hl, hv => by
    have hlen : vs.length = cs.length := by simpa using hl
    have hy : y < 3 := hv y (by simp)
    have hvs : ∀ z ∈ vs, z < 3 := fun z hz => hv z (by simp [hz])
    have hr : vecIdx vs < 3 ^ cs.length := by
      rw [← hlen]
      exact vecIdx_lt vs hvs
    have hW : 0 < 3 ^ cs.length := by positivity
    have hvi : vecIdx (y :: vs) = vecIdx vs + y * 3 ^ cs.length := by
      show y * 3 ^ vs.length + vecIdx vs = _
      rw [hlen, Nat.add_comm]
    have hdiv : (vecIdx vs + y * 3 ^ cs.length) / 3 ^ cs.length = y := by
      rw [Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr, zero_add]
    have hmod : (vecIdx vs + y * 3 ^ cs.length) % 3 ^ cs.length = vecIdx vs := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    rw [show rootDot (x :: cs) (y :: vs) = x * (y : ℤ) + rootDot cs vs from rfl, hvi]
    simp only [idxPair]
    rw [hdiv, hmod, idxPair_vecIdx cs vs hlen hvs]

@[expose] def outerKilled (roots : List (List ℤ)) (n : ℕ) (c : List ℤ) : Bool :=
  (List.range (3 ^ n)).all fun j =>
    idxPair c j % 3 == 0 || coverAux (2 ^ (3 ^ n) - 1) j (roots.map hyperBits) 0

theorem outerKilled_sound {roots : List (List ℤ)} {n : ℕ} (hlen : ∀ a ∈ roots, a.length = n)
    {c : List ℤ} (hc : c.length = n) (h : outerKilled roots n c = true)
    {v u : List ℕ} (hv : v.length = n) (hu : u.length = n)
    (hv3 : ∀ x ∈ v, x < 3) (hu3 : ∀ x ∈ u, x < 3) (hout : ¬ (3 : ℤ) ∣ rootDot c v) :
    ∃ a ∈ roots, rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0 := by
  unfold outerKilled at h
  rw [List.all_eq_true] at h
  have hjlt : vecIdx v < 3 ^ n := hv ▸ vecIdx_lt v hv3
  have hcov := h (vecIdx v) (List.mem_range.2 hjlt)
  have hnz : idxPair c (vecIdx v) % 3 ≠ 0 := by
    rw [idxPair_vecIdx c v (hv.trans hc.symm) hv3]
    exact fun h0 => hout (Int.dvd_of_emod_eq_zero h0)
  simp only [Bool.or_eq_true, beq_iff_eq] at hcov
  rcases hcov with h0 | hcov
  · exact absurd h0 hnz
  · exact exists_kill_of_cover hlen hv hu hv3 hu3 hcov

theorem three_dvd_sum_iff_mod {n : ℕ} (d : Fin n → ℤ) (k : Fin n → ℕ) :
    (3 : ℤ) ∣ ∑ i, d i * (k i : ℤ) ↔ (3 : ℤ) ∣ ∑ i, d i * ((k i % 3 : ℕ) : ℤ) := by
  have h2 : (3 : ℤ) ∣ ∑ i, d i * (k i : ℤ) - ∑ i, d i * ((k i % 3 : ℕ) : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have : (k i : ℤ) - ((k i % 3 : ℕ) : ℤ) = 3 * ((k i / 3 : ℕ) : ℤ) := by omega
    rw [← mul_sub, this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  constructor
  · intro h
    have e : ∑ i, d i * ((k i % 3 : ℕ) : ℤ) = ∑ i, d i * (k i : ℤ) - (∑ i, d i * (k i : ℤ) -
        ∑ i, d i * ((k i % 3 : ℕ) : ℤ)) := by ring
    rw [e]
    exact dvd_sub h h2
  · intro h
    have e : ∑ i, d i * (k i : ℤ) = (∑ i, d i * (k i : ℤ) - ∑ i, d i * ((k i % 3 : ℕ) : ℤ)) +
        ∑ i, d i * ((k i % 3 : ℕ) : ℤ) := by ring
    rw [e]
    exact dvd_add h2 h

theorem exists_root_kills_outer (τ : Tag) (roots : List (List ℤ))
    (hsub : ∀ a ∈ roots, a ∈ τ.artifactRoots) (c : Fin τ.rank → ℤ)
    (h : outerKilled roots τ.rank (List.ofFn c) = true) (k₁ k₂ : Fin τ.rank → ℕ)
    (hout : ¬ (3 : ℤ) ∣ ∑ i, c i * (k₁ i : ℤ)) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := by
  have hlen : ∀ a ∈ roots, a.length = τ.rank := fun a ha => length_of_mem_artifactRoots (hsub a ha)
  obtain ⟨a, ha, h1, h2⟩ := outerKilled_sound hlen (by simp) h
    (v := List.ofFn fun i => k₁ i % 3) (u := List.ofFn fun i => k₂ i % 3)
    (by simp) (by simp)
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.mod_lt _ (by norm_num))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.mod_lt _ (by norm_num))
    (by
      rw [rootDot_ofFn]
      exact fun hd => hout ((three_dvd_sum_iff_mod c k₁).2 hd))
  have hal : a.length = τ.rank := hlen a ha
  set α : Fin τ.rank → ℤ := fun i => a.getD i 0 with hαdef
  have hα : List.ofFn α = a := by
    refine List.ext_getElem (by simp [hal]) fun m hm hm' => ?_
    simp [hαdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']
  refine ⟨α, isRoot_iff_mem_artifactRoots.2 (by rw [hα]; exact hsub a ha), ?_, ?_⟩
  · rw [← hα, rootDot_ofFn] at h1
    exact three_dvd_sum_of_mod α k₁ h1
  · rw [← hα, rootDot_ofFn] at h2
    exact three_dvd_sum_of_mod α k₂ h2

theorem e6_outerKilled : outerKilled (posRoots e6ArtifactRoots) 6 [1, 0, 2, 0, 1, 2] = true := by
  decide +kernel

theorem e6_diagPair_killed (k₁ k₂ : Fin 6 → ℕ)
    (h : ¬ (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₁ i : ℤ) ∨ ¬ (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₂ i : ℤ)) :
    ∃ α : Fin 6 → ℤ, IsRoot .E6 α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := by
  have hsub : ∀ a ∈ posRoots e6ArtifactRoots, a ∈ Tag.E6.artifactRoots :=
    fun a ha => (List.mem_filter.1 ha).1
  have hck : outerKilled (posRoots e6ArtifactRoots) Tag.E6.rank (List.ofFn e6DiagCoeff) = true := by
    have hc : List.ofFn e6DiagCoeff = [1, 0, 2, 0, 1, 2] := by decide
    rw [hc]
    exact e6_outerKilled
  rcases h with h | h
  · exact exists_root_kills_outer .E6 _ hsub e6DiagCoeff hck k₁ k₂ h
  · obtain ⟨α, hα, h1, h2⟩ := exists_root_kills_outer .E6 _ hsub e6DiagCoeff hck k₂ k₁ h
    exact ⟨α, hα, h2, h1⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree
