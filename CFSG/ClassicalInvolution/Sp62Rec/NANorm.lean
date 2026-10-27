module

public import CFSG.ClassicalInvolution.Solomon73.YamakiZRig
public import CFSG.ClassicalInvolution.Solomon73

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

private theorem isE64_map_inj {H K : Type} [Group H] [Group K] {B : Subgroup H} (hB : IsE64 B)
    (f : H →* K) (hf : Function.Injective f) : IsE64 (B.map f) := by
  obtain ⟨hc, hs, hcard⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hc a' ha' b' hb']
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul, hs a' ha', map_one]
  · rw [Subgroup.card_map_of_injective hf, hcard]

private theorem mem_iff_of_map_eq {M N : Type} [Group M] [Group N] {H P : Subgroup M}
    {K S : Subgroup N} (φ : ↥H ≃* ↥K)
    (hφ : (P.subgroupOf H).map φ.toMonoidHom = S.subgroupOf K) (x : M) (hx : x ∈ H) :
    x ∈ P ↔ ((φ ⟨x, hx⟩ : ↥K) : N) ∈ S := by
  constructor
  · intro hxP
    have h1 : φ ⟨x, hx⟩ ∈ (P.subgroupOf H).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [hφ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hS
    have h1 : φ ⟨x, hx⟩ ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hS
    rw [← hφ] at h1
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
    have hyx : y = ⟨x, hx⟩ := φ.injective hyeq
    have hy' : (y : M) ∈ P := Subgroup.mem_subgroupOf.mp hy
    rw [hyx] at hy'
    exact hy'

private theorem conj_mem_iff {M : Type} [Group M] {A : Subgroup M} {g : M}
    (h : A.map (MulAut.conj g).toMonoidHom = A) (x : M) : g * x * g⁻¹ ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx2 : (MulAut.conj g) y = (MulAut.conj g) x := hyx
    have hyx' : y = x := (MulAut.conj g).injective hyx2
    rw [← hyx']
    exact hy
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hx

private theorem map_conj_subgroupOf {N A0 : Subgroup (StatedSp 3 (ZMod 2))} (m : ↥N)
    (hm : (m : StatedSp 3 (ZMod 2)) ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2)))) :
    (A0.subgroupOf N).map (MulAut.conj m).toMonoidHom = A0.subgroupOf N := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hsymm : (((MulAut.conj m).symm x : ↥N) : StatedSp 3 (ZMod 2)) =
      (m : StatedSp 3 (ZMod 2))⁻¹ * (x : StatedSp 3 (ZMod 2)) * (m : StatedSp 3 (ZMod 2)) := rfl
  rw [hsymm]
  exact (Subgroup.mem_normalizer_iff''.mp hm _).symm

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G}
  {A0 : Subgroup (StatedSp 3 (ZMod 2))}

theorem exists_conj_nu {A X : Subgroup G} (hAE : IsE64 A)
    (hXN : X ≤ Subgroup.normalizer (A : Set G)) (hAX : A ≤ X) (hAT : A ≤ (T : Subgroup G))
    (huniq : ∀ A' : Subgroup G, A' ≤ (T : Subgroup G) → IsE64 A' → A' = A)
    (hT : Nat.card (T : Subgroup G) = 512)
    (ν : ↥X ≃* ↥N0) (hνA : (A.subgroupOf X).map ν.toMonoidHom = A0.subgroupOf N0)
    (hS0 : Nat.card S0 = 512) (hN0 : Nat.card N0 = 10752)
    (hA0N : N0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2)))) :
    ∃ (X' : Subgroup G) (ν' : ↥X' ≃* ↥N0), X' ≤ Subgroup.normalizer (A : Set G) ∧
      (T : Subgroup G) ≤ X' ∧ A ≤ X' ∧
      (A.subgroupOf X').map ν'.toMonoidHom = A0.subgroupOf N0 ∧
      ((T : Subgroup G).subgroupOf X').map ν'.toMonoidHom = S0.subgroupOf N0 := by
  haveI : Finite ↥N0 := Nat.finite_of_card_ne_zero (by rw [hN0]; norm_num)
  haveI : Finite (Sylow 2 G) :=
    Finite.of_injective (fun P : Sylow 2 G => (P : Set G)) SetLike.coe_injective
  have hbound : ∀ H : Subgroup G, IsPGroup 2 H → Nat.card H ≤ 512 := by
    intro H hH
    obtain ⟨R, hR⟩ := hH.exists_le_sylow
    have hRT : Nat.card (R : Subgroup G) = Nat.card (T : Subgroup G) :=
      (Sylow.card_eq_multiplicity R).trans (Sylow.card_eq_multiplicity T).symm
    calc Nat.card H ≤ Nat.card (R : Subgroup G) := Subgroup.card_le_of_le hR
      _ = 512 := by rw [hRT, hT]
  have hdvd : 2 ^ 9 ∣ Nat.card X := ⟨21, by rw [Nat.card_congr ν.toEquiv, hN0]; norm_num⟩
  obtain ⟨Q, hQX, hQcard⟩ : ∃ Q : Subgroup G, Q ≤ X ∧ Nat.card Q = 2 ^ 9 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    refine ⟨K.map X.subtype, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective X), hK]
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card hQcard
  have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQX.trans hXN
  have hA2 : IsPGroup 2 (A : Subgroup G) := IsPGroup.to_le T.isPGroup' hAT
  have hAQ : A ≤ Q := by
    have h2 : IsPGroup 2 (Q ⊔ A : Subgroup G) := hQ2.to_sup_of_normal_right' hA2 hQN
    have h3 : Nat.card (Q ⊔ A : Subgroup G) ≤ Nat.card Q := by
      rw [hQcard]
      exact (hbound _ h2).trans (by norm_num)
    have h4 : Q = Q ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_left h3
    rw [h4]
    exact le_sup_right
  have hQi : ¬ 2 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index Q
    have h2 := Subgroup.card_mul_index (T : Subgroup G)
    rw [hQcard] at h1
    rw [hT] at h2
    have h3 : ¬ 2 ∣ (T : Subgroup G).index := Sylow.not_dvd_index T
    have h4 : Q.index = (T : Subgroup G).index := by
      norm_num at h1
      omega
    rw [h4]
    exact h3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hQ2.toSylow hQi) T
  have hgQ : Q.map (MulAut.conj g).toMonoidHom = (T : Subgroup G) := by
    have h := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
    exact h
  have hAT' : A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    rw [← hgQ]
    exact Subgroup.map_mono hAQ
  have hAfix : A.map (MulAut.conj g).toMonoidHom = A :=
    huniq _ hAT' (isE64_map_inj hAE (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have hgN : g ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun h => (conj_mem_iff hAfix h).symm
  have hX'N : X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.normalizer (A : Set G)).mul_mem
      ((Subgroup.normalizer (A : Set G)).mul_mem hgN (hXN hy))
      ((Subgroup.normalizer (A : Set G)).inv_mem hgN)
  have hTX' : (T : Subgroup G) ≤ X.map (MulAut.conj g).toMonoidHom := by
    intro t ht
    rw [← hgQ] at ht
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ht
    exact Subgroup.mem_map.mpr ⟨q, hQX hq, rfl⟩
  have hAX' : A ≤ X.map (MulAut.conj g).toMonoidHom := by
    intro a ha
    have ha' : a ∈ A.map (MulAut.conj g).toMonoidHom := by
      rw [hAfix]
      exact ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ha'
    exact Subgroup.mem_map.mpr ⟨m, hAX hm, rfl⟩
  set X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hX'def
  let ψ : ↥X ≃* ↥X' := X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let ν₁ : ↥X' ≃* ↥N0 := ψ.symm.trans ν
  have hAsub : A.subgroupOf X' = (A.subgroupOf X).map ψ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    have hxz : (x : G) = g * ((ψ.symm x : ↥X) : G) * g⁻¹ :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply ψ x).symm
    rw [hxz]
    exact conj_mem_iff hAfix _
  have hν₁ : ν₁.toMonoidHom.comp ψ.toMonoidHom = ν.toMonoidHom :=
    MonoidHom.ext fun y => by
      show ν (ψ.symm (ψ y)) = ν y
      rw [MulEquiv.symm_apply_apply]
  have hν₁A : (A.subgroupOf X').map ν₁.toMonoidHom = A0.subgroupOf N0 := by
    rw [hAsub, Subgroup.map_map, hν₁, hνA]
  have hT'card : Nat.card ((T : Subgroup G).subgroupOf X') = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX').toEquiv, hT]
  have hP1card : Nat.card (((T : Subgroup G).subgroupOf X').map ν₁.toMonoidHom) = 512 := by
    rw [Subgroup.card_map_of_injective (f := ν₁.toMonoidHom) ν₁.injective, hT'card]
  have hS0card : Nat.card (S0.subgroupOf N0) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_N0).toEquiv, hS0]
  have hP1 : IsPGroup 2 (((T : Subgroup G).subgroupOf X').map ν₁.toMonoidHom) :=
    IsPGroup.of_card (n := 9) (by rw [hP1card]; norm_num)
  have hP2 : IsPGroup 2 (S0.subgroupOf N0) :=
    IsPGroup.of_card (n := 9) (by rw [hS0card]; norm_num)
  have hi1 : ¬ 2 ∣ (((T : Subgroup G).subgroupOf X').map ν₁.toMonoidHom).index := by
    have h := Subgroup.card_mul_index (((T : Subgroup G).subgroupOf X').map ν₁.toMonoidHom)
    rw [hP1card, hN0] at h
    omega
  have hi2 : ¬ 2 ∣ (S0.subgroupOf N0).index := by
    have h := Subgroup.card_mul_index (S0.subgroupOf N0)
    rw [hS0card, hN0] at h
    omega
  haveI : Finite (Sylow 2 ↥N0) :=
    Finite.of_injective (fun P : Sylow 2 ↥N0 => (P : Set ↥N0)) SetLike.coe_injective
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥N0 (hP1.toSylow hi1) (hP2.toSylow hi2)
  have hmP : (((T : Subgroup G).subgroupOf X').map ν₁.toMonoidHom).map
      (MulAut.conj m).toMonoidHom = S0.subgroupOf N0 := by
    have h := congrArg (fun P : Sylow 2 ↥N0 => (P : Subgroup ↥N0)) hm
    exact h
  let ν' : ↥X' ≃* ↥N0 := ν₁.trans (MulAut.conj m)
  have hν'eq : ν'.toMonoidHom = (MulAut.conj m).toMonoidHom.comp ν₁.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  refine ⟨X', ν', hX'N, hTX', hAX', ?_, ?_⟩
  · rw [hν'eq, ← Subgroup.map_map, hν₁A]
    exact map_conj_subgroupOf m (hA0N m.2)
  · rw [hν'eq, ← Subgroup.map_map]
    exact hmP

theorem agree_on_center {X' Ce : Subgroup G} (θ : ↥Ce ≃* ↥Hhat)
    (hTCe : (T : Subgroup G) ≤ Ce)
    (hθT : ((T : Subgroup G).subgroupOf Ce).map θ.toMonoidHom = S0.subgroupOf Hhat)
    (ν : ↥X' ≃* ↥N0) (hTX : (T : Subgroup G) ≤ X')
    (hνT : ((T : Subgroup G).subgroupOf X').map ν.toMonoidHom = S0.subgroupOf N0)
    (haut : ∀ f : ↥S0 ≃* ↥S0, ∀ x : ↥S0, (∀ y : ↥S0, x * y = y * x) → f x = x)
    {c : G} (hcT : c ∈ (T : Subgroup G)) (hcZ : ∀ t ∈ (T : Subgroup G), c * t = t * c) :
    ((ν ⟨c, hTX hcT⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = ((θ ⟨c, hTCe hcT⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) := by
  let ρ : ↥(T : Subgroup G) ≃* ↥S0 :=
    mulEquivS0OfLe S0_le_N0 ν hTX (fun x hx => mem_iff_of_map_eq ν hνT x hx)
  let σ : ↥(T : Subgroup G) ≃* ↥S0 :=
    mulEquivS0OfLe S0_le_Hhat θ hTCe (fun x hx => mem_iff_of_map_eq θ hθT x hx)
  let f : ↥S0 ≃* ↥S0 := ρ.symm.trans σ
  have hcN : ((ν ⟨c, hTX hcT⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ S0 :=
    (mem_iff_of_map_eq ν hνT c (hTX hcT)).mp hcT
  let z : ↥S0 := ⟨((ν ⟨c, hTX hcT⟩ : ↥N0) : StatedSp 3 (ZMod 2)), hcN⟩
  have hzρ : ρ ⟨c, hcT⟩ = z := rfl
  have hzc : ∀ y : ↥S0, z * y = y * z := by
    intro y
    have hy : (⟨(y : StatedSp 3 (ZMod 2)), S0_le_N0 y.2⟩ : ↥N0) ∈ S0.subgroupOf N0 :=
      Subgroup.mem_subgroupOf.mpr y.2
    rw [← hνT] at hy
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hy
    have htT : (t : G) ∈ (T : Subgroup G) := Subgroup.mem_subgroupOf.mp ht
    have hcomm : (⟨c, hTX hcT⟩ : ↥X') * t = t * ⟨c, hTX hcT⟩ := Subtype.ext (hcZ _ htT)
    have h2 : ν (⟨c, hTX hcT⟩ * t) = ν (t * ⟨c, hTX hcT⟩) := congrArg ν hcomm
    rw [map_mul, map_mul] at h2
    have ht' : ν t = ⟨(y : StatedSp 3 (ZMod 2)), S0_le_N0 y.2⟩ := hteq
    rw [ht'] at h2
    apply Subtype.ext
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul] at h3
    exact h3
  have hfix : f z = z := haut f z hzc
  have hfz : f z = σ ⟨c, hcT⟩ := by
    show σ (ρ.symm z) = σ ⟨c, hcT⟩
    rw [← hzρ, MulEquiv.symm_apply_apply]
  have h1 : σ ⟨c, hcT⟩ = z := hfz.symm.trans hfix
  calc ((ν ⟨c, hTX hcT⟩ : ↥N0) : StatedSp 3 (ZMod 2))
      = (z : StatedSp 3 (ZMod 2)) := rfl
    _ = ((σ ⟨c, hcT⟩ : ↥S0) : StatedSp 3 (ZMod 2)) := by rw [h1]
    _ = ((θ ⟨c, hTCe hcT⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) := rfl

end CFSG.ClassicalInvolution.Sp62Rec
