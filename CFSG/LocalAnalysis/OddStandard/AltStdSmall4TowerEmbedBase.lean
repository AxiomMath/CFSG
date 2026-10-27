module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WF9Aff
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarPsi

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup Matrix HbarCoords

variable {G : Type} [Group G] {z : G} {T : Subgroup G} {κ : GL (Fin 3) (ZMod 2) →* G}
  {E₀ : Subgroup G} {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}

section Coord

variable (hc : ModIso.TCoords z T κ E₀ cT)
include hc

theorem cT6_zero : cT6 cT 0 = 1 := by
  have h := cT6_add hc 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem comm_of_mem {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := exists_cT6_eq hc ha
  obtain ⟨y, rfl⟩ := exists_cT6_eq hc hb
  rw [← cT6_add hc, ← cT6_add hc, add_comm]

private def coordHom : Multiplicative (Fin 6 → ZMod 2) →* G where
  toFun x := cT6 cT x.toAdd
  map_one' := cT6_zero hc
  map_mul' x y := cT6_add hc x.toAdd y.toAdd

private theorem coordHom_apply (x : Multiplicative (Fin 6 → ZMod 2)) :
    coordHom hc x = cT6 cT x.toAdd := rfl

end Coord

section Conj

variable {Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)}
  (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
    (g : G) * cT v w * (g : G)⁻¹ =
      cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          Fin.append v w))
        (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          Fin.append v w)))
include hΨ

theorem conj_cT6 (g : normalizer (T : Set G)) (x : Fin 6 → ZMod 2) :
    (g : G) * cT6 cT x * (g : G)⁻¹ =
      cT6 cT ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x) := by
  have h := hΨ g (GL62.fst x) (GL62.snd x)
  rw [GL62.append_fst_snd] at h
  exact h

variable (hc : ModIso.TCoords z T κ E₀ cT)
include hc

theorem psi_normAct_z (hzN : z ∈ normalizer (T : Set G)) :
    Ψ (AltStdBal.normAct T ⟨z, hzN⟩) = GL62.z₀ := by
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_))
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  apply cT6_injective hc
  rw [← conj_cT6 hΨ, GL62.z0_mulVec']
  show z * cT (GL62.fst x) (GL62.snd x) * z⁻¹ =
    cT6 cT (Fin.append (GL62.fst x + GL62.snd x) (GL62.snd x))
  rw [hc.conj_z, cT6_append]

theorem exists_embedding_of_compl {S : Subgroup (GL (Fin 6) (ZMod 2))}
    {φ : S →* MulAut (Multiplicative (Fin 6 → ZMod 2))}
    (hφ : ∀ (s : S) (x : Multiplicative (Fin 6 → ZMod 2)),
      φ s x = Multiplicative.ofAdd
        (((s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x.toAdd))
    {K : Subgroup (normalizer (T : Set G))}
    (hK1 : ∀ k ∈ K, Ψ (AltStdBal.normAct T k) = 1 → k = 1)
    (hKS : K.map (Ψ.toMonoidHom.comp (AltStdBal.normAct T)) = S) :
    ∃ ι : Multiplicative (Fin 6 → ZMod 2) ⋊[φ] S →* G, Function.Injective ι ∧
      ∀ s : S, ∃ k ∈ K, ι (SemidirectProduct.inr s) = (k : G) ∧
        Ψ (AltStdBal.normAct T k) = s := by
  set ρ : normalizer (T : Set G) →* GL (Fin 6) (ZMod 2) :=
    Ψ.toMonoidHom.comp (AltStdBal.normAct T) with hρ
  have hρK : Function.Injective (ρ.comp K.subtype) := by
    intro a b h
    have h1 : ρ ((a : normalizer (T : Set G)) * (b : normalizer (T : Set G))⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 h
    exact Subtype.ext (mul_inv_eq_one.1 (hK1 _ (mul_mem a.2 (inv_mem b.2)) h1))
  have hrange : (ρ.comp K.subtype).range = S := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hKS
  let e : K ≃* S := (MonoidHom.ofInjective hρK).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ s : S, ρ ((e.symm s : K) : normalizer (T : Set G)) = s := fun s => by
    have h : ((e (e.symm s) : S) : GL (Fin 6) (ZMod 2)) =
        ρ ((e.symm s : K) : normalizer (T : Set G)) := rfl
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  let f₂ : S →* G := (normalizer (T : Set G)).subtype.comp (K.subtype.comp e.symm.toMonoidHom)
  have hf₂ : ∀ s : S, f₂ s = (((e.symm s : K) : normalizer (T : Set G)) : G) := fun s => rfl
  have hconj : ∀ s : S, (coordHom hc).comp (φ s).toMonoidHom =
      (MulAut.conj (f₂ s)).toMonoidHom.comp (coordHom hc) := by
    intro s
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ,
      coordHom_apply, toAdd_ofAdd]
    rw [hf₂, conj_cT6 hΨ, ← he s]
    rfl
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => comm_of_mem hc ha hb
  refine ⟨SemidirectProduct.lift (coordHom hc) f₂ hconj, ?_, fun s =>
    ⟨(e.symm s : K), (e.symm s).2, (SemidirectProduct.lift_inr _ _ _ s).trans (hf₂ s), he s⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul,
    SemidirectProduct.lift_inl, SemidirectProduct.lift_inr] at hx
  have h1 : f₂ x.right ∈ T := by
    rw [eq_inv_of_mul_eq_one_right hx, coordHom_apply]
    exact inv_mem (cT6_mem hc _)
  set k : normalizer (T : Set G) := ((e.symm x.right : K) : normalizer (T : Set G)) with hk
  have h1' : (k : G) ∈ T := h1
  have h2 : AltStdBal.normAct T k = 1 := by
    ext w
    rw [AltStdBal.coe_normAct_apply, MulAut.one_apply, hTc _ h1' w w.2, mul_inv_cancel_right]
  have h3 : k = 1 := hK1 k (e.symm x.right).2 (by rw [h2, map_one])
  have h4 : x.right = 1 := by
    have : e.symm x.right = 1 := Subtype.ext h3
    rw [← e.apply_symm_apply x.right, this, map_one]
  have h5 : x.left = 1 := by
    rw [h4, map_one, mul_one, coordHom_apply] at hx
    exact toAdd_eq_zero.1 (cT6_injective hc (hx.trans (cT6_zero hc).symm))
  exact SemidirectProduct.ext h5 h4

end Conj

section Two

private theorem le_normalizer_centralizer {X : Subgroup G} (hXN : X ≤ normalizer (T : Set G)) :
    X ≤ normalizer (centralizer (T : Set G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro c
  have hxN := hXN hx
  constructor
  · intro hc'
    rw [mem_centralizer_iff]
    intro t ht
    have h1 : x⁻¹ * t * x ∈ T := (mem_normalizer_iff''.1 hxN t).1 ht
    have h2 := mem_centralizer_iff.1 hc' _ h1
    calc t * (x * c * x⁻¹) = x * ((x⁻¹ * t * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * t * x)) * x⁻¹ := by rw [h2]
      _ = x * c * x⁻¹ * t := by group
  · intro hc'
    rw [mem_centralizer_iff]
    intro t ht
    have h1 : x * t * x⁻¹ ∈ T := (mem_normalizer_iff.1 hxN t).1 ht
    have h2 := mem_centralizer_iff.1 hc' _ h1
    calc t * c = x⁻¹ * ((x * t * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * t * x⁻¹)) * x := by rw [h2]
      _ = c * t := by group

variable [Finite G] {Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)}

theorem exists_compl_two {X : Subgroup G} (hXN : X ≤ normalizer (T : Set G)) (hzX : z ∈ X)
    (hzz : z * z = 1)
    (h2 : ∀ x ∈ X, x ∈ centralizer (T : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 → x = 1)
    (hcov : normalizer (T : Set G) ≤ X ⊔ centralizer (T : Set G))
    {S : Subgroup (GL (Fin 6) (ZMod 2))} (hS : Nat.card S = 2 ^ 7)
    (hSH : S ≤ (Hbar T).map Ψ.toMonoidHom) (hzN : z ∈ normalizer (T : Set G))
    (hzS : Ψ (AltStdBal.normAct T ⟨z, hzN⟩) ∈ S) :
    ∃ K : Subgroup (normalizer (T : Set G)), ⟨z, hzN⟩ ∈ K ∧
      (∀ k ∈ K, Ψ (AltStdBal.normAct T k) = 1 → k = 1) ∧
      K.map (Ψ.toMonoidHom.comp (AltStdBal.normAct T)) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (T : Set G) with hNdef
  set ρ : N →* GL (Fin 6) (ZMod 2) := Ψ.toMonoidHom.comp (AltStdBal.normAct T) with hρ
  set XS : Subgroup N := X.subgroupOf N ⊓ S.comap ρ with hXS
  set zN : N := ⟨z, hzN⟩ with hzNdef
  have hCnorm := le_normalizer_centralizer hXN
  have hsurj : ∀ s ∈ S, ∃ x ∈ XS, ρ x = s := by
    intro s hs
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hSH hs
    have hgXC : (g : G) ∈ centralizer (T : Set G) ⊔ X := by
      rw [sup_comm]
      exact hcov g.2
    obtain ⟨c, hc, x, hx, hcx⟩ :=
      (WF9.mem_sup_iff_of_le_normalizer hCnorm).1 hgXC
    have hcN : c ∈ N := centralizer_le_normalizer _ hc
    have hxN : x ∈ N := hXN hx
    have hρc : AltStdBal.normAct T ⟨c, hcN⟩ = 1 := by
      ext w
      rw [AltStdBal.coe_normAct_apply, MulAut.one_apply]
      show c * w * c⁻¹ = w
      rw [← mem_centralizer_iff.1 hc w w.2, mul_inv_cancel_right]
    have hgx : g = ⟨c, hcN⟩ * ⟨x, hxN⟩ := Subtype.ext hcx.symm
    have hρx : ρ ⟨x, hxN⟩ = s := by
      rw [← hg]
      show Ψ (AltStdBal.normAct T ⟨x, hxN⟩) = Ψ (AltStdBal.normAct T g)
      rw [hgx, map_mul, hρc, one_mul]
    exact ⟨⟨x, hxN⟩, mem_inf.2 ⟨mem_subgroupOf.2 hx, by rw [mem_comap, hρx]; exact hs⟩, hρx⟩
  have hdvd : 2 ^ 7 ∣ Nat.card XS := by
    rw [← hS]
    let f : XS →* S := (ρ.comp XS.subtype).codRestrict S fun x => (mem_inf.1 x.2).2
    refine Subgroup.card_dvd_of_surjective (f := f) fun s => ?_
    obtain ⟨x, hx, hρx⟩ := hsurj s s.2
    exact ⟨⟨x, hx⟩, Subtype.ext hρx⟩
  have hzXS : zN ∈ XS := mem_inf.2 ⟨mem_subgroupOf.2 hzX, hzS⟩
  have hzcard : Nat.card (zpowers zN) ∣ 2 ^ 7 := by
    rw [Nat.card_zpowers]
    refine (orderOf_dvd_of_pow_eq_one ?_).trans (pow_dvd_pow 2 (by norm_num : 1 ≤ 7))
    rw [pow_one, sq]
    exact Subtype.ext hzz
  obtain ⟨K, hK, hzK, hKXS⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hzcard
    hdvd (zpowers_le.2 hzXS)
  have hK1 : ∀ k ∈ K, Ψ (AltStdBal.normAct T k) = 1 → k = 1 := by
    intro k hk hk1
    have hkX : (k : G) ∈ X := mem_subgroupOf.1 (mem_inf.1 (hKXS hk)).1
    have hkC : (k : G) ∈ centralizer (T : Set G) := by
      have h1 : AltStdBal.normAct T k = 1 := Ψ.injective (by rw [hk1, map_one])
      rw [mem_centralizer_iff]
      intro t ht
      have h2 := congrArg (fun φ : MulAut T => ((φ ⟨t, ht⟩ : T) : G)) h1
      simp only [AltStdBal.coe_normAct_apply, MulAut.one_apply] at h2
      calc t * (k : G) = ((k : G) * t * (k : G)⁻¹) * k := by rw [h2]
        _ = k * t := by group
    have hk7 : (k : G) ^ 2 ^ 7 = 1 := by
      have h := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
      rw [hK] at h
      have h' := congrArg (fun y : K => ((y : N) : G)) h
      simpa using h'
    exact Subtype.ext (h2 _ hkX hkC 7 hk7)
  refine ⟨K, hzK (mem_zpowers zN), hK1, ?_⟩
  have hle : K.map ρ ≤ S := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_inf.1 (hKXS hk)).2
  have hinj : Function.Injective (ρ.comp K.subtype) := by
    intro a b h
    have h1 : ρ ((a : N) * (b : N)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 h
    exact Subtype.ext (mul_inv_eq_one.1 (hK1 _ (mul_mem a.2 (inv_mem b.2)) h1))
  have hcard : Nat.card (K.map ρ) = 2 ^ 7 := by
    have h1 : (ρ.comp K.subtype).range = K.map ρ := by rw [MonoidHom.range_comp, range_subtype]
    rw [← h1, ← hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact eq_of_le_of_card_ge hle (by rw [hS, hcard])

theorem card_hbar_eq_of_compl {X : Subgroup G} (hXN : X ≤ normalizer (T : Set G))
    (hXC : X ⊓ centralizer (T : Set G) = ⊥)
    (hcov : normalizer (T : Set G) ≤ X ⊔ centralizer (T : Set G)) :
    Nat.card (Hbar T) = Nat.card X := by
  have hCnorm := le_normalizer_centralizer hXN
  have hker : ∀ g : normalizer (T : Set G), AltStdBal.normAct T g = 1 ↔
      (g : G) ∈ centralizer (T : Set G) := fun g => mem_ker_normAct_iff g
  let f : X → Hbar T := fun x => ⟨AltStdBal.normAct T ⟨x, hXN x.2⟩, ⟨_, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h1 : AltStdBal.normAct T (⟨a, hXN a.2⟩ * (⟨b, hXN b.2⟩ : normalizer (T : Set G))⁻¹) =
          1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.2 (congrArg Subtype.val h)
      have h2 : (a : G) * (b : G)⁻¹ ∈ X ⊓ centralizer (T : Set G) :=
        mem_inf.2 ⟨mul_mem a.2 (inv_mem b.2), (hker _).1 h1⟩
      rw [hXC, mem_bot, mul_inv_eq_one] at h2
      exact Subtype.ext h2
    · rintro ⟨_, ⟨g, rfl⟩⟩
      have hg : (g : G) ∈ centralizer (T : Set G) ⊔ X := by rw [sup_comm]; exact hcov g.2
      obtain ⟨c, hc, x, hx, hcx⟩ := (WF9.mem_sup_iff_of_le_normalizer hCnorm).1 hg
      have hcN : c ∈ normalizer (T : Set G) := centralizer_le_normalizer _ hc
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      have hgcx : g = ⟨c, hcN⟩ * ⟨x, hXN hx⟩ := Subtype.ext hcx.symm
      show AltStdBal.normAct T ⟨x, hXN hx⟩ = AltStdBal.normAct T g
      rw [hgcx, map_mul, (hker ⟨c, hcN⟩).2 hc, one_mul]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem exists_embedding_of_cover (hc : ModIso.TCoords z T κ E₀ cT)
    (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    {X : Subgroup G} (hXN : X ≤ normalizer (T : Set G)) (hzX : z ∈ X) (hzz : z * z = 1)
    (h2 : ∀ x ∈ X, x ∈ centralizer (T : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 → x = 1)
    (hcov : normalizer (T : Set G) ≤ X ⊔ centralizer (T : Set G))
    {S : Subgroup (GL (Fin 6) (ZMod 2))} (hS : Nat.card S = 2 ^ 7)
    (hSH : S ≤ (Hbar T).map Ψ.toMonoidHom) (hz₀ : GL62.z₀ ∈ S)
    {φ : S →* MulAut (Multiplicative (Fin 6 → ZMod 2))}
    (hφ : ∀ (s : S) (x : Multiplicative (Fin 6 → ZMod 2)),
      φ s x = Multiplicative.ofAdd
        (((s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x.toAdd)) :
    ∃ ι : Multiplicative (Fin 6 → ZMod 2) ⋊[φ] S →* G, Function.Injective ι ∧
      ι (SemidirectProduct.inr ⟨GL62.z₀, hz₀⟩) = z := by
  have hzN := hXN hzX
  have hz : Ψ (AltStdBal.normAct T ⟨z, hzN⟩) = GL62.z₀ := psi_normAct_z hΨ hc hzN
  obtain ⟨K, hzK, hK1, hKS⟩ := exists_compl_two hXN hzX hzz h2 hcov hS hSH hzN (hz ▸ hz₀)
  obtain ⟨ι, hι, hιK⟩ := exists_embedding_of_compl hΨ hc hφ hK1 hKS
  obtain ⟨k, hk, hιk, hkz⟩ := hιK ⟨GL62.z₀, hz₀⟩
  refine ⟨ι, hι, hιk.trans ?_⟩
  have h1 : k * (⟨z, hzN⟩ : normalizer (T : Set G))⁻¹ = 1 := by
    refine hK1 _ (mul_mem hk (inv_mem hzK)) ?_
    rw [map_mul, map_inv, map_mul, map_inv, hkz, hz]
    exact mul_inv_cancel _
  exact congrArg Subtype.val (mul_inv_eq_one.1 h1)

end Two

end CFSG.OddStandard.AltStdSmall4.Tower
