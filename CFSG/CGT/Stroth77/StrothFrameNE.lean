module

public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.CGT.Stroth77.Arch76Frame
public import CFSG.CGT.Stroth77.StrothAmbient

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)

section General

variable {G : Type} [Group G] [Finite G]

theorem le_of_isSylowIn_centralizer {E Q : Subgroup G}
    (hE : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E) (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ Subgroup.centralizer (E : Set G)) : Q ≤ E := by
  obtain ⟨hEC, hEp, hidx⟩ := hE
  have hQN : Q ≤ Subgroup.normalizer (E : Set G) :=
    hQC.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 (E ⊔ Q : Subgroup G) := hEp.to_sup_of_normal_left' hQ hQN
  have hle1 : E ≤ E ⊔ Q := le_sup_left
  have hle2 : E ⊔ Q ≤ Subgroup.centralizer (E : Set G) := sup_le hEC hQC
  have hmul := Subgroup.relIndex_mul_relIndex E (E ⊔ Q) _ hle1 hle2
  have hpow : ∃ k, E.relIndex (E ⊔ Q) = 2 ^ k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hsup.exists_card_eq
    have hd : E.relIndex (E ⊔ Q) ∣ Nat.card (E ⊔ Q : Subgroup G) :=
      Subgroup.relIndex_dvd_card E (E ⊔ Q)
    rw [hn] at hd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hpow
  have hk0 : k = 0 := by
    by_contra h0
    apply hidx
    rw [← hmul, hk]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 h0) _
  rw [hk0, pow_zero, Subgroup.relIndex_eq_one] at hk
  exact le_sup_right.trans hk

private theorem card_le_sixteen_of_isPGroup_perm_six {P : Subgroup (Equiv.Perm (Fin 6))}
    (hP : IsPGroup 2 P) : Nat.card P ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : Nat.card P ∣ Nat.card (Equiv.Perm (Fin 6)) := Subgroup.card_subgroup_dvd_card P
  rw [hn, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hd
  rw [hn]
  have hn4 : n ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h5.trans hd
    revert this
    decide
  calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
    _ = 16 := by norm_num

theorem card_inf_centralizer_mul_le_of_conj {N : Subgroup G} {Z : Set G} {m : ℕ} (p : Fin m → G)
    (hpN : ∀ i, p i ∈ N)
    (hp : ∀ i j, (∀ z ∈ Z, (p i)⁻¹ * z * p i = (p j)⁻¹ * z * p j) → i = j) :
    Nat.card (N ⊓ Subgroup.centralizer Z : Subgroup G) * m ≤ Nat.card N := by
  have key : Nat.card ((N ⊓ Subgroup.centralizer Z : Subgroup G) × Fin m) ≤ Nat.card N := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨(x.1 : G) * p x.2, N.mul_mem (Subgroup.mem_inf.mp x.1.2).1 (hpN x.2)⟩) ?_
    rintro ⟨k, i⟩ ⟨k', j⟩ hkk
    have hkk' : (k : G) * p i = (k' : G) * p j := congrArg Subtype.val hkk
    have hij : i = j := by
      apply hp
      intro z hz
      have h1 : p i * (p j)⁻¹ = (k : G)⁻¹ * k' := by
        calc p i * (p j)⁻¹ = (k : G)⁻¹ * ((k : G) * p i) * (p j)⁻¹ := by group
          _ = (k : G)⁻¹ * ((k' : G) * p j) * (p j)⁻¹ := by rw [hkk']
          _ = (k : G)⁻¹ * k' := by group
      have hm : p i * (p j)⁻¹ ∈ Subgroup.centralizer Z := by
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp k.2).2)
          (Subgroup.mem_inf.mp k'.2).2
      have hc := Subgroup.mem_centralizer_iff.mp hm z hz
      calc (p i)⁻¹ * z * p i = (p i)⁻¹ * (z * (p i * (p j)⁻¹)) * p j := by group
        _ = (p i)⁻¹ * (p i * (p j)⁻¹ * z) * p j := by rw [hc]
        _ = (p j)⁻¹ * z * p j := by group
    subst hij
    exact Prod.ext (Subtype.ext (mul_right_cancel hkk')) rfl
  rwa [Nat.card_prod, Nat.card_fin] at key

theorem mem_omegaIn_one_of_mul_self {D : Subgroup G} {z : G} (hz : z ∈ D) (h2 : z * z = 1) :
    z ∈ omegaIn 1 D := by
  refine ⟨⟨z, hz⟩, Subgroup.subset_closure ?_, rfl⟩
  change (⟨z, hz⟩ : D) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa [pow_two] using h2

end General

theorem StrothWeakTypeData.ofTorus_injective {S : Type*} [Group S] {B : Subgroup S}
    {τ : StrothTypeIndex} (D : StrothWeakTypeData B τ) : Function.Injective D.ofTorus := by
  intro y y' h
  have h1 : (Additive.toMul (D.e.symm y) : B) = Additive.toMul (D.e.symm y') := Subtype.ext h
  exact D.e.symm.injective (Additive.toMul.injective h1)

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem sylow_inf_centralizer_E_le :
    (F.S : Subgroup G) ⊓ Subgroup.centralizer (F.E : Set G) ≤ F.E :=
  le_of_isSylowIn_centralizer F.E_syl (F.S.isPGroup'.to_le inf_le_left) inf_le_right

theorem card_sylow_inf_normalizer_E_le :
    Nat.card ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) : Subgroup G) ≤ 256 := by
  obtain ⟨φ, -, hker⟩ := F.E_quot
  have hle : (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) ≤
      Subgroup.normalizer (F.E : Set G) := inf_le_right
  let H : Subgroup (Subgroup.normalizer (F.E : Set G)) :=
    ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G)).subgroupOf _
  let ψ : H →* Equiv.Perm (Fin 6) := φ.comp H.subtype
  have hcardH : Nat.card H =
      Nat.card ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hHp : IsPGroup 2 H :=
    (F.S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hrange : Nat.card ψ.range ≤ 16 :=
    card_le_sixteen_of_isPGroup_perm_six (hHp.of_surjective ψ.rangeRestrict
      ψ.rangeRestrict_surjective)
  have hE16 : Nat.card F.E = 16 := F.E_isE.2
  have hkerle : Nat.card ψ.ker ≤ 16 := by
    rw [← hE16]
    refine Nat.card_le_card_of_injective
      (fun x => ⟨(((x : H) : Subgroup.normalizer (F.E : Set G)) : G),
        F.sylow_inf_centralizer_E_le ⟨?_, ?_⟩⟩) ?_
    · exact (Subgroup.mem_subgroupOf.mp (x : H).2).1
    · have hx : ψ (x : H) = 1 := x.2
      have h1 : ((x : H) : Subgroup.normalizer (F.E : Set G)) ∈ φ.ker := hx
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    · intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext hxy))
  have hmain := Subgroup.card_ker_mul_card_range ψ
  rw [← hcardH, ← hmain]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 16 * 16 := Nat.mul_le_mul hkerle hrange
    _ = 256 := by norm_num

private def d8 : Fin 8 → G :=
  ![1, F.dA.uv, F.dA.t, F.dA.uv * F.dA.t, F.dA.u, F.dA.u * F.dA.uv, F.dA.u * F.dA.t,
    F.dA.u * F.dA.uv * F.dA.t]

private def d8act : Fin 8 → Torus (StrothTypeIndex.t100 1).k → Torus (StrothTypeIndex.t100 1).k :=
  ![id, (Type100.action 1).φuv, (Type100.action 1).φt,
    (Type100.action 1).φt ∘ (Type100.action 1).φuv, (Type100.action 1).φu,
    (Type100.action 1).φuv ∘ (Type100.action 1).φu, (Type100.action 1).φt ∘ (Type100.action 1).φu,
    (Type100.action 1).φt ∘ (Type100.action 1).φuv ∘ (Type100.action 1).φu]

private theorem d8_conj (i : Fin 8) (y : Torus (StrothTypeIndex.t100 1).k) :
    (F.d8 i)⁻¹ * F.dA.ofTorus y * F.d8 i = F.dA.ofTorus (d8act i y) := by
  have hmul : ∀ g h x : G, (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h :=
    fun _ _ _ => by group
  have huv := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj
  have ht := F.dA.conj_ofTorus F.dA.t_mem F.dA.t_conj
  have hu := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj
  fin_cases i
  · show (1 : G)⁻¹ * F.dA.ofTorus y * 1 = F.dA.ofTorus y
    group
  · exact huv y
  · exact ht y
  · show (F.dA.uv * F.dA.t)⁻¹ * F.dA.ofTorus y * (F.dA.uv * F.dA.t) = _
    rw [hmul, huv, ht]; rfl
  · exact hu y
  · show (F.dA.u * F.dA.uv)⁻¹ * F.dA.ofTorus y * (F.dA.u * F.dA.uv) = _
    rw [hmul, hu, huv]; rfl
  · show (F.dA.u * F.dA.t)⁻¹ * F.dA.ofTorus y * (F.dA.u * F.dA.t) = _
    rw [hmul, hu, ht]; rfl
  · show (F.dA.u * F.dA.uv * F.dA.t)⁻¹ * F.dA.ofTorus y * (F.dA.u * F.dA.uv * F.dA.t) = _
    rw [hmul, hmul, hu, huv, ht]; rfl

private theorem d8act_inj : ∀ i j : Fin 8, d8act i Torus.c = d8act j Torus.c →
    d8act i (Torus.a + Torus.a) = d8act j (Torus.a + Torus.a) →
    d8act i (Torus.b + Torus.b) = d8act j (Torus.b + Torus.b) → i = j := by
  decide

theorem sylow_inf_normalizer_E_inf_centralizer_eq :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) ⊓
      Subgroup.centralizer {F.dA.ofTorus Torus.c, F.dA.ofTorus (Torus.a + Torus.a),
        F.dA.ofTorus (Torus.b + Torus.b)} = F.A := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro z hz
    refine ⟨⟨F.A_le_S hz, F.A_le hz⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hyA : y ∈ F.A := by
      rcases hy with rfl | rfl | rfl <;> exact F.dA.ofTorus_mem _
    exact congrArg Subtype.val (F.dA.isMulCommutative.is_comm.comm ⟨y, hyA⟩ ⟨z, hz⟩)
  · have huv : F.dA.uv ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) :=
      ⟨F.uv_mem_S, F.L_le F.dA.uv_mem_L⟩
    have ht : F.dA.t ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) :=
      ⟨F.t_mem_S, F.L_le F.dA.t_mem_L⟩
    have hu : F.dA.u ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) :=
      ⟨F.u_mem_S, F.L_le F.dA.u_mem_L⟩
    have hcard : Nat.card ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) ⊓
        Subgroup.centralizer {F.dA.ofTorus Torus.c, F.dA.ofTorus (Torus.a + Torus.a),
          F.dA.ofTorus (Torus.b + Torus.b)} : Subgroup G) * 8 ≤
        Nat.card ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.E : Set G) : Subgroup G) :=
      card_inf_centralizer_mul_le_of_conj F.d8 (fun i => by
      fin_cases i
      · exact one_mem _
      · exact huv
      · exact ht
      · exact mul_mem huv ht
      · exact hu
      · exact mul_mem hu huv
      · exact mul_mem hu ht
      · exact mul_mem (mul_mem hu huv) ht) (fun i j h => by
      have hz : ∀ y, F.dA.ofTorus y ∈ ({F.dA.ofTorus Torus.c, F.dA.ofTorus (Torus.a + Torus.a),
          F.dA.ofTorus (Torus.b + Torus.b)} : Set G) → d8act i y = d8act j y := fun y hy =>
        F.dA.ofTorus_injective (by rw [← F.d8_conj, ← F.d8_conj]; exact h _ hy)
      exact d8act_inj i j (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)))
    have h256 := F.card_sylow_inf_normalizer_E_le
    have hA : Nat.card F.A = 32 := by rw [F.dA.card]; rfl
    omega

end StrothFrame

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G]
variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem mem_of_mem_normalizer_E (h : F.IsD D dD) {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgC : g ∈ Subgroup.centralizer (omegaIn 1 D : Set G))
    (hgE : g ∈ Subgroup.normalizer (F.E : Set G)) : g ∈ D := by
  have hsq : ∀ y : Torus (StrothTypeIndex.t100 1).k, y + y = 0 →
      F.dA.ofTorus y ∈ omegaIn 1 D := fun y hy =>
    mem_omegaIn_one_of_mul_self (h.A_le (F.dA.ofTorus_mem y))
      (by rw [← F.dA.ofTorus_add, hy, F.dA.ofTorus_zero])
  apply h.A_le
  rw [← F.sylow_inf_normalizer_E_inf_centralizer_eq]
  refine ⟨⟨hgS, hgE⟩, Subgroup.centralizer_le ?_ hgC⟩
  rintro y (rfl | rfl | rfl)
  · exact hsq _ (by decide)
  · exact hsq _ (by decide)
  · exact hsq _ (by decide)

theorem mem_of_commute (h : F.IsD D dD) {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgC : g ∈ Subgroup.centralizer (omegaIn 1 D : Set G))
    (huv : g * F.dA.uv = F.dA.uv * g) (ht : g * F.dA.t = F.dA.t * g) : g ∈ D := by
  have hsq : ∀ y : Torus (StrothTypeIndex.t100 1).k, y + y + (y + y) = 0 →
      F.dA.ofTorus y ^ 2 * g = g * F.dA.ofTorus y ^ 2 := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hgC _ (mem_omegaIn_one_of_mul_self
      (h.A_le (F.A.pow_mem (F.dA.ofTorus_mem y) 2))
      (by rw [pow_two, ← F.dA.ofTorus_add, ← F.dA.ofTorus_add, hy, F.dA.ofTorus_zero]))
  refine h.mem_of_mem_normalizer_E hgS hgC (Subgroup.centralizer_le_normalizer _ ?_)
  rw [F.E_eq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro y (rfl | rfl | rfl | rfl)
  · exact hsq Torus.a (by decide)
  · exact hsq Torus.b (by decide)
  · exact huv.symm
  · exact ht.symm

end StrothFrame.IsD

end CFSG.CGT.Stroth77
