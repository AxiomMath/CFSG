module

public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Off

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Syl

open CFSG.Open CFSG.ABGLocalTools CFSG.Goldschmidt.G310 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem fusion_of_isSylowOf {p : ℕ} [Fact p.Prime] {S K : Subgroup G} (h : IsSylowOf p S K) :
    fusionIsSylowIn p S K := by
  obtain ⟨Q, rfl⟩ := h
  exact fusionIsSylowIn_map Q

theorem isSylowOf_of_fusion {p : ℕ} [Fact p.Prime] {S K : Subgroup G}
    (h : fusionIsSylowIn p S K) : IsSylowOf p S K := by
  obtain ⟨hSK, hS, hmax⟩ := h
  refine ⟨⟨S.subgroupOf K, hS.comap_subtype, fun {Q} hQ hSQ => ?_⟩, ?_⟩
  · have h1 := hmax (Q.map K.subtype) (Subgroup.map_subtype_le Q) (hQ.map K.subtype)
      fun s hs => ⟨⟨s, hSK hs⟩, hSQ (show (⟨s, hSK hs⟩ : K) ∈ S.subgroupOf K from hs), rfl⟩
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q).symm
  · show (S.subgroupOf K).map K.subtype = S
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSK]

theorem map_conj_eq {O : Subgroup G} {g : G} (hg : g ∈ normalizer (O : Set G)) :
    O.map (MulAut.conj g).toMonoidHom = O := by
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by group⟩
    apply (mem_normalizer_iff.mp hg (g⁻¹ * z * g)).mpr
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]

theorem isSylowOf_conj {p : ℕ} [Fact p.Prime] {R O : Subgroup G} (hR : IsSylowOf p R O) {g : G}
    (hg : g ∈ normalizer (O : Set G)) :
    IsSylowOf p (R.map (MulAut.conj g).toMonoidHom) O := by
  rw [isSylowOf_iff] at hR ⊢
  obtain ⟨hle, hp, hidx⟩ := hR
  refine ⟨?_, hp.map _, ?_⟩
  · rw [← map_conj_eq hg]
    exact Subgroup.map_mono hle
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) R O
      (MulAut.conj g).injective
    rw [map_conj_eq hg] at this
    rwa [this]

theorem mem_map_conj_iff (S : Subgroup G) (c x : G) :
    x ∈ S.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ S := by
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
  · intro h
    exact ⟨c⁻¹ * x * c, h, by group⟩

theorem inf_eq_bot_of_pGroup {Q O : Subgroup G} (hQ3 : IsPGroup 3 Q) (hO3 : ¬ 3 ∣ Nat.card O) :
    Q ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ3) ⟨z, hz.1⟩
  have hzk : orderOf z = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hdvd : orderOf z ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨z, hz.2⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hk0 : k = 0 := by
    by_contra hne
    exact hO3 ((dvd_pow_self 3 hne).trans (hzk ▸ hdvd))
  rw [hk0] at hzk
  exact mem_bot.mpr (orderOf_eq_one_iff.mp (by simpa using hzk))

theorem card_sup_mul {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  let f : A × B → (A ⊔ B : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, by
      rw [← SetLike.mem_coe, hset]
      exact Set.mul_mem_mul x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (by
        have := congrArg (fun t => (a' : G) * t) h3
        simpa using this)
      have hb : b = b' := Subtype.ext (by
        rw [ha] at h1
        exact mul_left_cancel h1)
      rw [ha, hb]
    · rintro ⟨x, hx⟩
      rw [← SetLike.mem_coe, hset] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem isSylowOf_sup {Q O : Subgroup G} (hQ3 : IsPGroup 3 Q) (hO3 : ¬ 3 ∣ Nat.card O)
    (hQO : Q ≤ normalizer (O : Set G)) : IsSylowOf 3 Q (Q ⊔ O) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_left, hQ3, ?_⟩
  have hbot := inf_eq_bot_of_pGroup hQ3 hO3
  have h1 := Subgroup.relIndex_mul_card Q (Q ⊔ O)
  rw [inf_eq_left.mpr (le_sup_left : Q ≤ Q ⊔ O), card_sup_mul hQO hbot] at h1
  have h2 : Q.relIndex (Q ⊔ O) = Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q))
    rw [h1, Nat.mul_comm]
  rw [h2]
  exact hO3

theorem exists_invariant_sylow_two {Q O : Subgroup G} (hQ3 : IsPGroup 3 Q)
    (hO3 : ¬ 3 ∣ Nat.card O) (hQO : Q ≤ normalizer (O : Set G)) :
    ∃ R : Subgroup G, IsSylowOf 2 R O ∧ Q ≤ normalizer (R : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, -, hQS⟩ := exists_invariant_sylow_containing Nat.prime_three Nat.prime_two
    (Q := ⊥) hQ3 hO3 hQO bot_le IsPGroup.of_bot
    (by
      intro q _
      refine mem_normalizer_iff.mpr fun x => ?_
      simp only [SetLike.mem_coe, mem_bot]
      constructor
      · rintro rfl
        simp
      · intro h
        have : x = q⁻¹ * (q * x * q⁻¹) * q := by group
        rw [this, h]
        group)
  exact ⟨S, isSylowOf_of_fusion hS, hQS⟩

theorem exists_conj_normalize {Q O R U : Subgroup G} (hQ3 : IsPGroup 3 Q) (hO3 : ¬ 3 ∣ Nat.card O)
    (hQO : Q ≤ normalizer (O : Set G)) (hR : IsSylowOf 2 R O) (hU : U ≤ Q)
    (hUR : U ≤ normalizer (R : Set G)) :
    ∃ c ∈ Q ⊔ O, Q ≤ normalizer ((R.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) ∧
      U.map (MulAut.conj c).toMonoidHom ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₁, hR₁, hQR₁⟩ := exists_invariant_sylow_two hQ3 hO3 hQO
  obtain ⟨k, hkO, hk⟩ := hR.exists_mem_conj hR₁
  have hkQO : k ∈ Q ⊔ O := mem_sup_right hkO
  set Z : Subgroup G := normalizer (R₁ : Set G) ⊓ (Q ⊔ O) with hZ
  have hQZ : Q ≤ Z := le_inf hQR₁ le_sup_left
  have hZQO : Z ≤ Q ⊔ O := inf_le_right
  have hQZsyl : IsSylowOf 3 Q Z := (isSylowOf_sup hQ3 hO3 hQO).of_le hQZ hZQO
  set U' : Subgroup G := U.map (MulAut.conj k).toMonoidHom with hU'
  have hU'QO : U' ≤ Q ⊔ O := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Q ⊔ O).mul_mem ((Q ⊔ O).mul_mem hkQO (mem_sup_left (hU hu))) ((Q ⊔ O).inv_mem hkQO)
  have hU'R₁ : U' ≤ normalizer (R₁ : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_normalizer_iff.mpr fun x => ?_
    rw [hk x, hk (k * u * k⁻¹ * x * (k * u * k⁻¹)⁻¹)]
    have e : k⁻¹ * (k * u * k⁻¹ * x * (k * u * k⁻¹)⁻¹) * k = u * (k⁻¹ * x * k) * u⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.mp (hUR hu) _
  have hU'Z : U' ≤ Z := le_inf hU'R₁ hU'QO
  have hU'p : IsPGroup 3 U' := (hQ3.to_le hU).map _
  obtain ⟨P', hP', hU'P'⟩ := GL83P3A6Off.exists_isSylowOf_of_le (p := 3) hU'p hU'Z
  obtain ⟨z, hzZ, hz⟩ := hQZsyl.exists_mem_conj hP'
  have hzR₁ : z ∈ normalizer (R₁ : Set G) := hzZ.1
  refine ⟨z⁻¹ * k, (Q ⊔ O).mul_mem ((Q ⊔ O).inv_mem (hZQO hzZ)) hkQO, ?_, ?_⟩
  ·
    have hRc : ∀ x, x ∈ R.map (MulAut.conj (z⁻¹ * k)).toMonoidHom ↔ x ∈ R₁ := by
      intro x
      rw [mem_map_conj_iff]
      have e : (z⁻¹ * k)⁻¹ * x * (z⁻¹ * k) = k⁻¹ * (z * x * z⁻¹) * k := by group
      rw [e, ← hk (z * x * z⁻¹)]
      exact (mem_normalizer_iff.mp hzR₁ x).symm
    have hRc' : R.map (MulAut.conj (z⁻¹ * k)).toMonoidHom = R₁ := by
      ext x
      exact hRc x
    rw [hRc']
    exact hQR₁
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : k * u * k⁻¹ ∈ P' := hU'P' ⟨u, hu, rfl⟩
    have h2 := (hz (k * u * k⁻¹)).mp h1
    have e : z⁻¹ * k * u * (z⁻¹ * k)⁻¹ = z⁻¹ * (k * u * k⁻¹) * z := by group
    rw [e]
    exact h2

theorem exists_lift_normalizing {Q O R : Subgroup G} (hQ3 : IsPGroup 3 Q) (hO3 : ¬ 3 ∣ Nat.card O)
    (hQO : Q ≤ normalizer (O : Set G)) (hR : IsSylowOf 2 R O) (hQR : Q ≤ normalizer (R : Set G))
    {g : G} (hgO : g ∈ normalizer (O : Set G)) (hgQ : g ∈ normalizer (Q : Set G)) :
    ∃ c ∈ O ⊓ centralizer (Q : Set G), c * g ∈ normalizer (R : Set G) ∧
      ∀ q ∈ Q, (c * g) * q * (c * g)⁻¹ = g * q * g⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 (R.map (MulAut.conj g).toMonoidHom) O := isSylowOf_conj hR hgO
  have hQS : Q ≤ normalizer ((R.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro q hq
    refine mem_normalizer_iff.mpr fun x => ?_
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have hq' : g⁻¹ * q * g ∈ Q := by
      apply (mem_normalizer_iff.mp hgQ (g⁻¹ * q * g)).mpr
      rwa [show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    have h1 := mem_normalizer_iff.mp (hQR hq') (g⁻¹ * x * g)
    have e : g⁻¹ * (q * x * q⁻¹) * g = (g⁻¹ * q * g) * (g⁻¹ * x * g) * (g⁻¹ * q * g)⁻¹ := by
      group
    rw [e]
    exact h1
  obtain ⟨c, hc, hcR⟩ := exists_conj_of_invariant_sylows Nat.prime_three Nat.prime_two
    (A := Q) (M := O) (S := R.map (MulAut.conj g).toMonoidHom) (S' := R) hQ3 hO3 hQO
    (fusion_of_isSylowOf hS) (fusion_of_isSylowOf hR) hQS hQR
  refine ⟨c, hc, ?_, ?_⟩
  · refine mem_normalizer_iff.mpr fun h => ?_
    have := Set.ext_iff.mp (congrArg (fun S : Subgroup G => (S : Set G)) hcR)
      ((c * g) * h * (c * g)⁻¹)
    simp only [SetLike.mem_coe, mem_map_conj_iff] at this
    rw [show g⁻¹ * (c⁻¹ * (c * g * h * (c * g)⁻¹) * c) * g = h by group] at this
    exact this.symm
  · intro q hq
    have hgq : g * q * g⁻¹ ∈ Q := (mem_normalizer_iff.mp hgQ q).mp hq
    have h1 := mem_centralizer_iff.mp hc.2 (g * q * g⁻¹) hgq
    calc c * g * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ := by group
      _ = g * q * g⁻¹ := by rw [← h1]; group

theorem exists_mul_normalizer {O R : Subgroup G} (hR : IsSylowOf 2 R O) {m : G}
    (hm : m ∈ normalizer (O : Set G)) : ∃ o ∈ O, ∃ h ∈ normalizer (R : Set G), m = o * h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 (R.map (MulAut.conj m).toMonoidHom) O := isSylowOf_conj hR hm
  obtain ⟨k, hkO, hk⟩ := hR.exists_mem_conj hS
  refine ⟨k, hkO, k⁻¹ * m, ?_, by group⟩
  refine mem_normalizer_iff.mpr fun y => ?_
  have h1 := hk (m * y * m⁻¹)
  rw [mem_map_conj_iff] at h1
  have e : m⁻¹ * (m * y * m⁻¹) * m = y := by group
  rw [e] at h1
  have e2 : k⁻¹ * m * y * (k⁻¹ * m)⁻¹ = k⁻¹ * (m * y * m⁻¹) * k := by group
  rw [e2]
  exact h1

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Syl
