module

public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup

section Elementary

variable {G : Type*} [Group G] {p : ℕ}

theorem isMulCommutative_sylow_of_comm_index [Finite G] [Fact p.Prime] {H : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hidx : ¬ p ∣ H.index) (P : Sylow p G) :
    IsMulCommutative (P : Subgroup G) := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p H) := inferInstance
  set S : Subgroup G := (S₀ : Subgroup H).map H.subtype with hS
  have hSp : IsPGroup p S := S₀.isPGroup'.map H.subtype
  have hSi : ¬ p ∣ S.index := by
    rw [hS, Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (hSp.toSylow hSi)
  have hconj : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = S := by
    have h := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    rw [← h, Subgroup.pointwise_smul_def]
    rfl
  have hmem : ∀ a : (P : Subgroup G), g * (a : G) * g⁻¹ ∈ H := fun a => by
    have h1 : (MulAut.conj g) (a : G) ∈ S := hconj ▸ Subgroup.mem_map_of_mem _ a.2
    exact Subgroup.map_subtype_le _ h1
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  have h2 := hH _ (hmem a) _ (hmem b)
  have h3 : g * ((a : G) * b) * g⁻¹ = g * ((b : G) * a) * g⁻¹ := by
    calc g * ((a : G) * b) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) := by group
      _ = (g * (b : G) * g⁻¹) * (g * (a : G) * g⁻¹) := h2
      _ = g * ((b : G) * a) * g⁻¹ := by group
  have h4 := mul_left_cancel (mul_right_cancel h3)
  exact h4

theorem isMulCommutative_sylow_of_injective {H : Type*} [Group H] [Finite H] [Fact p.Prime]
    (f : G →* H) (hf : Function.Injective f)
    (h : ∀ Q : Sylow p H, IsMulCommutative (Q : Subgroup H)) (P : Sylow p G) :
    IsMulCommutative (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map f).exists_le_sylow
  haveI : IsMulCommutative (Q : Subgroup H) := h Q
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply hf
  have ha : f (a : G) ∈ (Q : Subgroup H) := hQ ⟨a, a.2, rfl⟩
  have hb : f (b : G) ∈ (Q : Subgroup H) := hQ ⟨b, b.2, rfl⟩
  have := setLike_mul_comm ha hb
  simpa using this

theorem isMulCommutative_sylow_of_surjective [Finite G] {N : Type*} [Group N] [Fact p.Prime]
    (f : G →* N) (hf : Function.Surjective f)
    (h : ∀ S : Sylow p G, IsMulCommutative (S : Subgroup G)) (P : Sylow p N) :
    IsMulCommutative (P : Subgroup N) := by
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  rw [Sylow.coe_mapSurjective]
  haveI : IsMulCommutative (S : Subgroup G) := h S
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  obtain ⟨x, hx, hxa⟩ := a.2
  obtain ⟨y, hy, hyb⟩ := b.2
  have hxy := congrArg f (setLike_mul_comm hx hy)
  simp only [map_mul] at hxy
  show (a : N) * b = b * a
  rw [← hxa, ← hyb]
  exact hxy

theorem crossExc_dvd_pow_pred_sub_one {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    p ∣ q ^ (p - 1) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h => hpq (h ▸ dvd_zero p)
  have h1 : 1 ≤ q ^ (p - 1) := Nat.one_le_pow _ _ hq1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow,
    ZMod.pow_card_sub_one_eq_one hq0, Nat.cast_one, sub_self]

theorem crossExc_not_dvd_two_pow_mul_three_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      (by omega)
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
      (by omega)

theorem crossExc_not_dvd_pow_of_ne {p ℓ n : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) :
    ¬ p ∣ ℓ ^ n := fun h =>
  hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)).symm

end Elementary

section Adjoint

variable
  {τ : Tag} {K : Type} [Field K] [Finite K]

theorem crossExc_torusGroup_le_adjointGroup : torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem crossExc_not_dvd_index_torusGroup {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := ((torusGroup τ K).subgroupOf (adjointGroup τ K)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe crossExc_torusGroup_le_adjointGroup).toEquiv,
    card_adjointGroup, finsum_eq_sum_of_fintype, mul_assoc] at hcard
  have hidx := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  have hqp : (Nat.card K : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (Nat.card K - 1) p).2 hpq
    rwa [Nat.cast_sub hq1, Nat.cast_one, sub_eq_zero] at h
  intro hdvd
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  rw [hidx] at h0
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum, hqp, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one, one_mul, Finset.card_univ] at h0
  exact hW (by rw [Nat.card_eq_fintype_card]; exact (ZMod.natCast_eq_zero_iff _ p).1 h0)

theorem isMulCommutative_sylow_adjointGroup_of_dvd {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) (hpq : p ∣ Nat.card K - 1)
    (P : Sylow p (adjointGroup τ K)) : IsMulCommutative (P : Subgroup (adjointGroup τ K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  exact isMulCommutative_sylow_of_comm_index
    (H := (torusGroup τ K).subgroupOf (adjointGroup τ K))
    (fun a ha b hb => Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 _ ha _ hb))
    (crossExc_not_dvd_index_torusGroup hp hW hpq) P

theorem isMulCommutative_sylow_adjointGroup {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) (hpK : ¬ p ∣ Nat.card K)
    (P : Sylow p (adjointGroup τ K)) : IsMulCommutative (P : Subgroup (adjointGroup τ K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  haveI : CharP K ℓ := hℓ
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hℓp, -⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  letI : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  set f := Module.finrank (ZMod ℓ) K with hf
  have hKf : ℓ ^ f = Nat.card K := FiniteField.pow_finrank_eq_natCard ℓ K
  have hf0 : f ≠ 0 := Module.finrank_pos.ne'
  have hm0 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hfm : f * (p - 1) ≠ 0 := Nat.mul_ne_zero hf0 hm0
  have hK' : Nat.card (GaloisField ℓ (f * (p - 1))) = Nat.card K ^ (p - 1) := by
    rw [GaloisField.card ℓ (f * (p - 1)) hfm, pow_mul, hKf]
  have hdvd : p ∣ Nat.card (GaloisField ℓ (f * (p - 1))) - 1 := by
    rw [hK']
    exact crossExc_dvd_pow_pred_sub_one hp hpK
  obtain ⟨ι⟩ : Nonempty (K →ₐ[ZMod ℓ] GaloisField ℓ (f * (p - 1))) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [GaloisField.finrank ℓ hfm]
      exact dvd_mul_right f _)
  have hle : (adjointGroup τ K).map (baseChangeGL ι.toRingHom) ≤
      adjointGroup τ (GaloisField ℓ (f * (p - 1))) := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  let φ : adjointGroup τ K →* adjointGroup τ (GaloisField ℓ (f * (p - 1))) :=
    ((baseChangeGL ι.toRingHom).comp (adjointGroup τ K).subtype).codRestrict _
      fun g => hle (Subgroup.mem_map_of_mem _ g.2)
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective ι.toRingHom (congrArg Subtype.val h))
  haveI : Finite (ModGL τ (GaloisField ℓ (f * (p - 1)))) := finite_modGL
  exact isMulCommutative_sylow_of_injective φ hφ
    (fun Q => isMulCommutative_sylow_adjointGroup_of_dvd hp hW hdvd Q) P

theorem isMulCommutative_sylow_derivedCentralQuotient {H : Subgroup (ModGL τ K)}
    (hH : H ≤ adjointGroup τ K) {p : ℕ} (hp : p.Prime) (hW : ¬ p ∣ Nat.card (WeylGroup τ))
    (hpK : ¬ p ∣ Nat.card K) (P : Sylow p (↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆)) :
    IsMulCommutative (P : Subgroup (↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  have hYH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hY : ⁅H, H⁆ ≤ adjointGroup τ K := hYH.trans hH
  exact isMulCommutative_sylow_of_surjective (QuotientGroup.mk' (Subgroup.center ↥⁅H, H⁆))
    (QuotientGroup.mk'_surjective _)
    (fun S => isMulCommutative_sylow_of_injective (Subgroup.inclusion hY)
      (Subgroup.inclusion_injective hY)
      (fun Q => isMulCommutative_sylow_adjointGroup hp hW hpK Q) S) P

end Adjoint

end CFSG.LocalAnalysis.RankFourTheoremC
