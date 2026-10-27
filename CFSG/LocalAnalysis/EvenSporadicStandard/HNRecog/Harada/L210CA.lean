module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L29Lin
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210CAOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210WrInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

private lemma map_inf_centralizer_conj {G : Type*} [Group G] {A : Subgroup G} {v n : G}
    (hn : n ∈ normalizer (A : Set G)) :
    (A ⊓ centralizer ({v} : Set G)).map (MulAut.conj n).toMonoidHom
      = A ⊓ centralizer ({n * v * n⁻¹} : Set G) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨?_, ?_⟩
    · change (MulAut.conj n) y ∈ A
      rw [MulAut.conj_apply]
      exact ((Subgroup.mem_normalizer_iff.mp hn) y).mp hy.1
    · have hyc : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (MulAut.conj n) y * (n * v * n⁻¹) = (n * v * n⁻¹) * (MulAut.conj n) y
      rw [MulAut.conj_apply]
      calc n * y * n⁻¹ * (n * v * n⁻¹)
          = n * (y * v) * n⁻¹ := by group
        _ = n * (v * y) * n⁻¹ := by rw [hyc]
        _ = (n * v * n⁻¹) * (n * y * n⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_map]
    refine ⟨n⁻¹ * x * n, ?_, ?_⟩
    · rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · simpa only [inv_inv] using
          ((Subgroup.mem_normalizer_iff.mp (inv_mem hn)) x).mp hx.1
      · have hxc : x * (n * v * n⁻¹) = (n * v * n⁻¹) * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hx.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc n⁻¹ * x * n * v
            = n⁻¹ * (x * (n * v * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * v * n⁻¹) * x) * n := by rw [hxc]
          _ = v * (n⁻¹ * x * n) := by group
    · show (MulAut.conj n) (n⁻¹ * x * n) = x
      rw [MulAut.conj_apply]
      group

variable {X : Type} [Group X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem L210_card_centralizer_le (h : Abs210 A w ψ) {i : X} (hi : i ∈ normalizer (A : Set X))
    (hiA : i ∉ A) (hi2 : i * i = 1) : Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16 := by
  classical
  let N := ↥(normalizer (A : Set X))
  let iN : N := ⟨i, hi⟩
  have hiN2 : iN * iN = 1 := by
    apply Subtype.ext
    dsimp only [iN]
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    exact hi2
  by_cases hcase : ψ iN ∈ commutator A5WrTwo
  ·
    have hψi_ne : ψ iN ≠ 1 := by
      intro h1
      have hmem : iN ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
      rw [h.ker] at hmem
      have hthis : (iN : X) ∈ A := Subgroup.mem_subgroupOf.mp hmem
      exact hiA hthis
    have hψi2 : ψ iN * ψ iN = 1 := by rw [← map_mul, hiN2, map_one]
    obtain ⟨x, hx5, hcomp⟩ := L210_exists_inverted_component hcase hψi_ne hψi2
    have step : ∀ (y : alternatingGroup (Fin 5)) (s : A5WrTwo), orderOf y = 5 →
        (s = A5WrTwo.baseEmb (y, 1) ∨ s = A5WrTwo.baseEmb (1, y)) →
        ψ iN * s * (ψ iN)⁻¹ = s⁻¹ →
        Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16 := by
      intro y s hy hs hinvs
      obtain ⟨r₀, hr₀⟩ := h.surj s
      have hy5 : y ^ 5 = 1 := by
        have h := pow_orderOf_eq_one y
        rwa [hy] at h
      have hs5 : s ^ 5 = 1 := by
        rcases hs with hs | hs
        · rw [hs, ← map_pow]
          have hpair : ((y, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ^ 5 = 1 := by
            ext <;> simp [Prod.pow_def, hy5]
          rw [hpair, map_one]
        · rw [hs, ← map_pow]
          have hpair : ((1, y) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ^ 5 = 1 := by
            ext <;> simp [Prod.pow_def, hy5]
          rw [hpair, map_one]
      have hs6 : s ^ 6 = s := by
        rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hs5, one_mul]
      have h10 : (r₀ : X) ^ 10 = 1 := by
        have hmem : (r₀ ^ 5 : N) ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_pow, hr₀, hs5]
        rw [h.ker] at hmem
        have hA : ((r₀ ^ 5 : N) : X) ∈ A := Subgroup.mem_subgroupOf.mp hmem
        have h2 : (((r₀ ^ 5 : N) : X) ^ 2) = 1 := h.elemAb.2 _ hA
        rw [Subgroup.coe_pow] at h2
        rw [← pow_mul] at h2
        rw [show 5 * 2 = 10 from rfl] at h2
        exact h2
      let r : N := r₀ ^ 6
      have hpsi_r : ψ r = s := by
        have h6 : ψ r = (ψ r₀) ^ 6 := by
          rw [show r = r₀ ^ 6 from rfl, map_pow]
        rw [h6, hr₀, hs6]
      have hr5 : (r : X) ^ 5 = 1 := by
        have h30 : (r₀ : X) ^ 30 = 1 := by
          have h : (r₀ : X) ^ 30 = ((r₀ : X) ^ 10) ^ 3 := by
            rw [show (30 : ℕ) = 10 * 3 from rfl, pow_mul]
          rw [h, h10]
          group
        calc (r : X) ^ 5 = ((r₀ : X) ^ 6) ^ 5 := by
              rw [show r = r₀ ^ 6 from rfl, Subgroup.coe_pow]
          _ = (r₀ : X) ^ (6 * 5) := (pow_mul (r₀ : X) 6 5).symm
          _ = 1 := by rw [show 6 * 5 = 30 from rfl, h30]
      have hker : (iN * r * iN⁻¹ * r) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : ψ (iN * r * iN⁻¹ * r) = ψ iN * s * (ψ iN)⁻¹ * s := by
          simp only [map_mul, map_inv, hpsi_r]
        rw [h1, hinvs, inv_mul_cancel]
      have hinvX : i * (r : X) * i⁻¹ * (r : X) ∈ A :=
        Subgroup.mem_subgroupOf.mp (by
          rw [← h.ker]
          exact hker)
      have hshape : ψ r = A5WrTwo.baseEmb (y, 1) ∨ ψ r = A5WrTwo.baseEmb (1, y) := by
        rcases hs with hs | hs
        · exact Or.inl (hpsi_r.trans hs)
        · exact Or.inr (hpsi_r.trans hs)
      have hfpf : ∀ a ∈ A, (r : X) * a * (r : X)⁻¹ = a → a = 1 :=
        L28_fixedFree h.toL28Hyp hy hshape
      exact L29_card_centralizer_le h.elemAb h.card hi r.2 hi2 hr5 hinvX hfpf
    rcases hcomp with hcomp | hcomp
    · exact step x (A5WrTwo.baseEmb (x, 1)) hx5 (Or.inl rfl) hcomp
    · exact step x (A5WrTwo.baseEmb (1, x)) hx5 (Or.inr rfl) hcomp
  ·
    obtain ⟨v, hvA, hv2X, hvψ, hCv⟩ := h.outer
    have hv2 : v * v = 1 := Subtype.ext (by simpa using hv2X)
    have hψv2 : (ψ v) ^ 2 = 1 := by rw [pow_two, ← map_mul, hv2, map_one]
    have hψi2 : (ψ iN) ^ 2 = 1 := by rw [pow_two, ← map_mul, hiN2, map_one]
    obtain ⟨b, hb, hbu⟩ :=
      A5WrTwo.exists_conj_of_outer_involutions hvψ hcase hψv2 hψi2
    obtain ⟨n, hn⟩ := h.surj b
    let v' : N := n * v * n⁻¹
    have hv'ψ : ψ v' = ψ iN := by
      have h1 : ψ v' = ψ n * ψ v * (ψ n)⁻¹ := by
        simp only [v', map_mul, map_inv]
      rw [h1, hn, hbu]
    have hv'2 : v' * v' = 1 := by
      calc v' * v' = n * (v * v) * n⁻¹ := by dsimp only [v']; group
        _ = 1 := by rw [hv2]; group
    have hv'2X : (v' : X) * (v' : X) = 1 :=
      congrArg (fun w : N => (w : X)) hv'2
    have hiv'N : iN * v'⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hv'ψ, mul_inv_cancel]
    have hiv' : i * (v' : X)⁻¹ ∈ A :=
      Subgroup.mem_subgroupOf.mp (by
        rw [← h.ker]
        exact hiv'N)
    have hCv' : Nat.card ↥(A ⊓ centralizer ({(v' : X)} : Set X)) ≤ 16 := by
      have hmap := map_inf_centralizer_conj (A := A) (v := (v : X)) (n := (n : X)) n.2
      have hv'coe : (v' : X) = (n : X) * (v : X) * (n : X)⁻¹ := by
        dsimp only [v']
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hcard : Nat.card ↥((A ⊓ centralizer ({(v : X)} : Set X)).map
            (MulAut.conj (n : X)).toMonoidHom)
          = Nat.card ↥(A ⊓ centralizer ({(v : X)} : Set X)) :=
        Nat.card_congr (Subgroup.equivMapOfInjective
          (A ⊓ centralizer ({(v : X)} : Set X)) (MulAut.conj (n : X)).toMonoidHom
          (MulAut.conj (n : X)).injective).toEquiv.symm
      rw [hv'coe, ← hmap, hcard]
      exact hCv
    exact L210_card_centralizer_le_of_coset h.elemAb h.card hi v'.2 hi2 hv'2X hiv' hCv'

end CFSG.EvenSporadicStandard.HNRecog.Harada
