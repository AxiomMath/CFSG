module

public import CFSG.GH74.KGroups.PermCheck
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Local

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

section Model

variable {K G : Type*} [Group K] [Group G] (M : AutModel K G)

@[expose] def modelEmb : K →* G := M.P.subtype.comp M.e.toMonoidHom

theorem modelEmb_apply (k : K) : modelEmb M k = (M.e k : G) := rfl

theorem modelEmb_injective : Function.Injective (modelEmb M) :=
  fun _ _ h => M.e.injective (Subtype.ext h)

theorem modelEmb_mem (k : K) : modelEmb M k ∈ M.P := (M.e k).2

theorem modelEmb_symm (y : G) (hy : y ∈ M.P) : modelEmb M (M.e.symm ⟨y, hy⟩) = y := by
  rw [modelEmb_apply, MulEquiv.apply_symm_apply]

theorem apply_eq_self_iff (θ : MulAut K) (k : K) :
    θ k = k ↔ (M.Φ θ : G) * modelEmb M k = modelEmb M k * (M.Φ θ : G) := by
  rw [modelEmb_apply]
  constructor
  · intro h
    have h1 := M.spec θ k
    rw [h] at h1
    calc (M.Φ θ : G) * (M.e k : G)
        = ((M.Φ θ : G) * (M.e k : G) * (M.Φ θ : G)⁻¹) * (M.Φ θ : G) := by group
      _ = (M.e k : G) * (M.Φ θ : G) := by rw [← h1]
  · intro h
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec θ k, h, mul_inv_cancel_right]

theorem map_fixSubgroup (θ : MulAut K) :
    (GSThmB.Eight.fixSubgroup θ).map (modelEmb M) =
      M.P ⊓ centralizer ({(M.Φ θ : G)} : Set G) := by
  ext y
  rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨modelEmb_mem M k, ((apply_eq_self_iff M θ k).1 hk).symm⟩
  · rintro ⟨hy, hc⟩
    refine ⟨M.e.symm ⟨y, hy⟩, ?_, modelEmb_symm M y hy⟩
    rw [GSThmB.Eight.mem_fixSubgroup, apply_eq_self_iff M θ, modelEmb_symm M y hy]
    exact hc.symm

theorem card_fixSubgroup (θ : MulAut K) :
    Nat.card (GSThmB.Eight.fixSubgroup θ) =
      Nat.card ↥(M.P ⊓ centralizer ({(M.Φ θ : G)} : Set G)) := by
  rw [← map_fixSubgroup M θ, card_map_of_injective (modelEmb_injective M)]

theorem map_centralizer_set (X : Set K) :
    (centralizer X).map (modelEmb M) = M.P ⊓ centralizer (modelEmb M '' X) := by
  ext y
  rw [mem_map, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨modelEmb_mem M k, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.1 hk) x hx]
  · rintro ⟨hy, hc⟩
    refine ⟨M.e.symm ⟨y, hy⟩, mem_centralizer_iff.2 fun x hx => ?_, modelEmb_symm M y hy⟩
    apply modelEmb_injective M
    rw [map_mul, map_mul, modelEmb_symm M y hy]
    exact hc _ ⟨x, hx, rfl⟩

theorem card_centralizer_set (X : Set K) :
    Nat.card (centralizer X) = Nat.card ↥(M.P ⊓ centralizer (modelEmb M '' X)) := by
  rw [← map_centralizer_set M X, card_map_of_injective (modelEmb_injective M)]

variable (hPA : M.P ≤ M.A) (hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1)
include hPA hcent

theorem Φ_conj (k : K) : (M.Φ (MulAut.conj k) : G) = modelEmb M k := by
  have hc : (modelEmb M k)⁻¹ * (M.Φ (MulAut.conj k) : G) ∈ M.A :=
    M.A.mul_mem (M.A.inv_mem (hPA (modelEmb_mem M k))) (M.Φ _).2
  have h1 : (modelEmb M k)⁻¹ * (M.Φ (MulAut.conj k) : G) = 1 := by
    refine hcent _ hc fun x hx => ?_
    obtain ⟨l, rfl⟩ : ∃ l, modelEmb M l = x := ⟨M.e.symm ⟨x, hx⟩, modelEmb_symm M x hx⟩
    have hs := M.spec (MulAut.conj k) l
    have he : ((M.e (MulAut.conj k l) : M.P) : G) =
        modelEmb M k * modelEmb M l * (modelEmb M k)⁻¹ := by
      rw [MulAut.conj_apply, ← modelEmb_apply, map_mul, map_mul, map_inv]
    have key : (M.Φ (MulAut.conj k) : G) * modelEmb M l * (M.Φ (MulAut.conj k) : G)⁻¹ =
        modelEmb M k * modelEmb M l * (modelEmb M k)⁻¹ := by
      rw [← he, hs, modelEmb_apply]
    calc (modelEmb M k)⁻¹ * (M.Φ (MulAut.conj k) : G) * modelEmb M l
        = (modelEmb M k)⁻¹ * ((M.Φ (MulAut.conj k) : G) * modelEmb M l *
            (M.Φ (MulAut.conj k) : G)⁻¹) * (M.Φ (MulAut.conj k) : G) := by group
      _ = (modelEmb M k)⁻¹ * (modelEmb M k * modelEmb M l * (modelEmb M k)⁻¹) *
            (M.Φ (MulAut.conj k) : G) := by rw [key]
      _ = modelEmb M l * ((modelEmb M k)⁻¹ * (M.Φ (MulAut.conj k) : G)) := by group
  calc (M.Φ (MulAut.conj k) : G)
      = modelEmb M k * ((modelEmb M k)⁻¹ * (M.Φ (MulAut.conj k) : G)) := by group
    _ = modelEmb M k := by rw [h1, mul_one]

theorem mem_range_conj_iff (θ : MulAut K) :
    θ ∈ (MulAut.conj : K →* MulAut K).range ↔ (M.Φ θ : G) ∈ M.P := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [Φ_conj M hPA hcent]
    exact modelEmb_mem M k
  · intro h
    obtain ⟨k, hk⟩ := M.inner_of_mem θ h
    exact ⟨k, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hk]⟩

theorem map_centralizer_map_conj (D : Subgroup K) :
    (centralizer ((D.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K))).map M.ι =
      M.A ⊓ centralizer ((D.map (modelEmb M) : Subgroup G) : Set G) := by
  ext y
  rw [mem_map, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨M.ι_mem θ, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have h1 := (mem_centralizer_iff.1 hθ) (MulAut.conj d) ⟨d, hd, rfl⟩
    have h2 := congrArg M.ι h1
    rw [map_mul, map_mul] at h2
    have h3 : M.ι (MulAut.conj d) = modelEmb M d := Φ_conj M hPA hcent d
    rw [h3] at h2
    exact h2
  · rintro ⟨hy, hc⟩
    refine ⟨M.Φ.symm ⟨y, hy⟩, mem_centralizer_iff.2 ?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      apply M.ι_injective
      rw [map_mul, map_mul]
      have h3 : M.ι (MulAut.conj d) = modelEmb M d := Φ_conj M hPA hcent d
      have h4 : M.ι (M.Φ.symm ⟨y, hy⟩) = y := by
        show ((M.Φ (M.Φ.symm ⟨y, hy⟩) : M.A) : G) = y
        rw [MulEquiv.apply_symm_apply]
      rw [h3, h4]
      exact hc _ ⟨d, hd, rfl⟩
    · show ((M.Φ (M.Φ.symm ⟨y, hy⟩) : M.A) : G) = y
      rw [MulEquiv.apply_symm_apply]

theorem card_centralizer_map_conj (D : Subgroup K) :
    Nat.card (centralizer ((D.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K))) =
      Nat.card ↥(M.A ⊓ centralizer ((D.map (modelEmb M) : Subgroup G) : Set G)) := by
  rw [← map_centralizer_map_conj M hPA hcent D, card_map_of_injective M.ι_injective]

theorem pow_eq_one_of_mem_centralizer_conj (k : K) (n : ℕ)
    (h : ∀ g ∈ M.A, g * modelEmb M k = modelEmb M k * g → g ^ n = 1) (θ : MulAut K)
    (hθ : θ ∈ centralizer ({MulAut.conj k} : Set (MulAut K))) : θ ^ n = 1 := by
  rw [mem_centralizer_singleton_iff] at hθ
  have h1 := congrArg M.ι hθ
  rw [map_mul, map_mul] at h1
  have h3 : M.ι (MulAut.conj k) = modelEmb M k := Φ_conj M hPA hcent k
  rw [h3] at h1
  apply M.ι_injective
  rw [map_pow, map_one]
  exact h _ (M.ι_mem θ) h1

end Model

theorem card_inf_eq_length {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (S : Subgroup (Equiv.Perm (Fin n))) (b : Equiv.Perm (Fin n) → Bool)
    (hb : ∀ g ∈ Q.originalSubgroup, g ∈ S ↔ b g = true) :
    Nat.card ↥(Q.originalSubgroup ⊓ S) = ((elemsT Q).filter b).length := by
  refine card_eq_length (fun g => g ∈ Q.originalSubgroup ⊓ S) id Function.injective_id _
    ((nodup_elemsT Q hQ).filter _) ?_
  intro g
  simp only [List.mem_filter, mem_elemsT Q hQ, mem_inf, id_eq, exists_eq_right]
  constructor
  · rintro ⟨hg, hb'⟩
    exact ⟨hg, (hb g hg).2 hb'⟩
  · rintro ⟨hg, hS⟩
    exact ⟨hg, (hb g hg).1 hS⟩

theorem exists_central_involution {G : Type*} [Group G] (E : Subgroup G) (hE : Nat.card E = 8) :
    ∃ z ∈ E, z * z = 1 ∧ z ≠ 1 ∧ ∀ y ∈ E, y * z = z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : Nat.card E = 2 ^ 3 := by rw [hE]; norm_num
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  obtain ⟨k, hk, hck⟩ := IsPGroup.card_center_eq_prime_pow hE' (by norm_num)
  have h2 : 2 ∣ Nat.card (center E) := by
    rw [hck]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  refine ⟨((w : E) : G), (w : E).2, ?_, ?_, ?_⟩
  · have h := congrArg (fun u : center E => (((u : E) : G))) hw2
    simpa [pow_two] using h
  · intro h1
    have : w = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hw
    norm_num at hw
  · intro y hy
    have h := (mem_center_iff.1 w.2) ⟨y, hy⟩
    exact congrArg Subtype.val h

end CFSG.ComponentClassification.CatFactsSmall
