module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigM
public import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.StronglyEmbedded.DihedralSylowNoStrongEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.invRep_noncentral : ∀ i : Fin 9, i ≠ 0 →
    ∃ p : SE, p * invRep i ≠ invRep i * p := by
  decide +kernel

variable {G : Type} [Group G]

theorem centralizer_le_of_conj {H : Subgroup G} {k r : G} (hk : k ∈ H)
    (hr : centralizer ({r} : Set G) ≤ H) : centralizer ({k * r * k⁻¹} : Set G) ≤ H := by
  intro x hx
  have h1 : k⁻¹ * x * k ∈ centralizer ({r} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    calc k⁻¹ * x * k * r = k⁻¹ * (x * (k * r * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * r * k⁻¹) * x) * k := by rw [hx]
      _ = r * (k⁻¹ * x * k) := by group
  have h := mul_mem (mul_mem hk (hr h1)) (inv_mem hk)
  rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h

variable [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem false_of_abelian_centralizer {i : Fin 9} (hi : i = 3 ∨ i = 5) {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA : A = (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G)) : False := by
  obtain ⟨p, q, hp, hq, hpq⟩ := SE.centralizer_nonabelian i hi
  have hmem : ∀ r : SE, r * SE.invRep i = SE.invRep i * r → D.toG r ∈ A := fun r hr => by
    rw [hA]
    exact ⟨D.toG_mem r, mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hr])⟩
  apply hpq
  apply D.toG_injective
  rw [map_mul, map_mul]
  exact hAc _ (hmem p hp) _ (hmem q hq)


theorem conj_mem_V_of_conj_Q {g : G} (hg : ∀ q ∈ D.Q, g * q * g⁻¹ ∈ (D.S : Subgroup G))
    {v : G} (hv : v ∈ D.V) : g * v * g⁻¹ ∈ D.V := by
  by_cases hv1 : v = 1
  · rw [hv1, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨s, hs⟩ := D.exists_toG (hg v (D.V_le_Q hv))
  have hvv : v * v = 1 := by rw [← pow_two]; exact D.isElemAbelian_V.2 v hv
  have hs2 : s * s = 1 := D.toG_injective (by
    rw [map_mul, hs, show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hvv,
      map_one]
    group)
  have hs1 : s ≠ 1 := fun h => hv1 (by
    have h' : g * v * g⁻¹ = 1 := by rw [← hs, h, map_one]
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  obtain ⟨-, c₀, hc₀⟩ := SE.cls_spec Certificates.certificate22608.1 (s := s)
    (by simp [SE.isInvB, hs2, hs1])
  generalize Fin.ofNat 9 (SE.clsTab s) = i at hc₀
  set c := D.toG c₀ with hcdef
  set g' := c⁻¹ * g with hg'
  have hr : g' * v * g'⁻¹ = D.toG (SE.invRep i) := by
    rw [show g' * v * g'⁻¹ = c⁻¹ * (g * v * g⁻¹) * c by rw [hg']; group, ← hs, hcdef,
      ← map_inv, ← map_mul, ← map_mul, hc₀]
  have hA : ∀ q ∈ D.Q, g' * q * g'⁻¹ ∈
      (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G) := by
    intro q hq
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show g' * q * g'⁻¹ = c⁻¹ * (g * q * g⁻¹) * c by rw [hg']; group]
      exact mul_mem (mul_mem (inv_mem (D.toG_mem c₀)) (hg q hq)) (D.toG_mem c₀)
    · rw [mem_centralizer_singleton_iff, ← hr]
      have hqv := D.Q_comm hq (D.V_le_Q hv)
      calc g' * q * g'⁻¹ * (g' * v * g'⁻¹) = g' * (q * v) * g'⁻¹ := by group
        _ = g' * (v * q) * g'⁻¹ := by rw [hqv]
        _ = g' * v * g'⁻¹ * (g' * q * g'⁻¹) := by group
  have hle : D.Q.map (MulAut.conj g').toMonoidHom ≤
      (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hA q hq
  have hcard : 64 ≤ SE.invRepCent i := by
    rw [← D.card_centralizer_invRep_G i, ← D.card_Q,
      ← card_map_of_injective (f := (MulAut.conj g').toMonoidHom) (MulAut.conj g').injective]
    exact card_le_of_le hle
  have hAc : ∀ a ∈ D.Q.map (MulAut.conj g').toMonoidHom,
      ∀ b ∈ D.Q.map (MulAut.conj g').toMonoidHom, a * b = b * a := by
    rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩
    rw [← map_mul, ← map_mul, D.Q_comm hq₁ hq₂]
  have heq : SE.invRepCent i = 64 → D.Q.map (MulAut.conj g').toMonoidHom =
      (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G) := fun h64 =>
    eq_of_le_of_card_ge hle (by
      rw [D.card_centralizer_invRep_G i, h64,
        card_map_of_injective (f := (MulAut.conj g').toMonoidHom) (MulAut.conj g').injective,
        D.card_Q])
  have key : g' * v * g'⁻¹ ∈ D.V := by
    rw [hr]
    fin_cases i
    · exact (D.toG_mem_V_iff).mpr (by decide)
    · exact (D.toG_mem_V_iff).mpr (by decide)
    · exact (D.toG_mem_V_iff).mpr (by decide)
    · exact (D.false_of_abelian_centralizer (Or.inl rfl) hAc (heq rfl)).elim
    · exact absurd hcard (by decide)
    · exact (D.false_of_abelian_centralizer (Or.inr rfl) hAc (heq rfl)).elim
    · exact absurd hcard (by decide)
    · exact absurd hcard (by decide)
    · exact absurd hcard (by decide)
  have h := D.conj_mem_V (inv_mem (D.toG_mem c₀)) key
  rwa [inv_inv, show c * (g' * v * g'⁻¹) * c⁻¹ = g * v * g⁻¹ by rw [hg']; group] at h

theorem exists_normalizer_V_conj (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) {u : G} (hu : u ∈ D.V)
    (hu1 : u ≠ 1) : ∃ k ∈ normalizer (D.V : Set G), k * D.z * k⁻¹ = u := by
  obtain ⟨g, hg⟩ := D.conj_z_of_mem_V h10 h20 hu hu1
  have hQ'M : D.Q.map (MulAut.conj g).toMonoidHom ≤ D.M := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqu := D.Q_comm hq (D.V_le_Q hu)
    have hz : D.z = g * u * g⁻¹ := by rw [← hg]; group
    change g * q * g⁻¹ * D.z = D.z * (g * q * g⁻¹)
    rw [hz]
    calc g * q * g⁻¹ * (g * u * g⁻¹) = g * (q * u) * g⁻¹ := by group
      _ = g * (u * q) * g⁻¹ := by rw [hqu]
      _ = g * u * g⁻¹ * (g * q * g⁻¹) := by group
  have hQ'2 : IsPGroup 2 (D.Q.map (MulAut.conj g).toMonoidHom) :=
    (D.S.isPGroup'.to_le D.Q_le_S).map _
  have hSM : IsSylowOf 2 (D.S : Subgroup G) D.M := (isSylowOf_top D.S).of_le D.S_le_M le_top
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isSylowOf hSM hQ'M hQ'2
  set k₀ := m * g with hk₀def
  have hk₀ : ∀ q ∈ D.Q, k₀ * q * k₀⁻¹ ∈ (D.S : Subgroup G) := fun q hq => by
    have h := hm (g * q * g⁻¹) ⟨q, hq, rfl⟩
    rwa [show m * (g * q * g⁻¹) * m⁻¹ = k₀ * q * k₀⁻¹ by rw [hk₀def]; group] at h
  have hVle : D.V.map (MulAut.conj k₀).toMonoidHom ≤ D.V := by
    rintro _ ⟨v, hv, rfl⟩
    exact D.conj_mem_V_of_conj_Q hk₀ hv
  have hVeq : D.V.map (MulAut.conj k₀).toMonoidHom = D.V :=
    eq_of_le_of_card_ge hVle (by
      rw [card_map_of_injective (f := (MulAut.conj k₀).toMonoidHom) (MulAut.conj k₀).injective])
  have hk₀N : k₀ ∈ normalizer (D.V : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact hVeq
  refine ⟨k₀⁻¹, inv_mem hk₀N, ?_⟩
  have hmz := D.z_comm_of_mem_M hmM
  calc k₀⁻¹ * D.z * k₀⁻¹⁻¹ = g⁻¹ * (m⁻¹ * D.z * m) * g := by rw [hk₀def]; group
    _ = u := by rw [hmz, hg]

theorem centralizer_V_le_H
    (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) {u : G}
    (hu : u ∈ D.V) (hu1 : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨k, hk, rfl⟩ := D.exists_normalizer_V_conj h10 h20 hu hu1
  exact centralizer_le_of_conj (D.normalizer_V_le_H hC h10 h20 hk) (D.M_le_H hC h10 h20)

omit [Finite G] in
theorem centralizer_le_of_reps {H : Subgroup G} (hSH : (D.S : Subgroup G) ≤ H)
    (hreps : ∀ i : Fin 9, centralizer ({D.toG (SE.invRep i)} : Set G) ≤ H) {u : G}
    (hu : u ∈ (D.S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    centralizer ({u} : Set G) ≤ H := by
  obtain ⟨s, rfl⟩ := D.exists_toG hu
  have hs2 : s * s = 1 := D.toG_injective (by rw [map_mul, hu2, map_one])
  have hs1 : s ≠ 1 := fun h => hu1 (by rw [h, map_one])
  obtain ⟨-, c, hc⟩ := SE.cls_spec Certificates.certificate22608.1 (s := s)
    (by simp [SE.isInvB, hs2, hs1])
  have e : D.toG s = D.toG c * D.toG (SE.invRep (Fin.ofNat 9 (SE.clsTab s))) * (D.toG c)⁻¹ := by
    rw [← hc, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [e]
  exact centralizer_le_of_conj (hSH (D.toG_mem c)) (hreps _)

omit [Finite G] in
theorem eq_z_of_central {x : G} (hx : x ∈ (D.S : Subgroup G)) (hx2 : orderOf x = 2)
    (hxc : ∀ s ∈ (D.S : Subgroup G), x * s = s * x) : x = D.z := by
  obtain ⟨s, rfl⟩ := D.exists_toG hx
  have hs1 : s ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hs2 : s * s = 1 := D.toG_injective (by
    rw [map_mul, ← pow_two, ← hx2, pow_orderOf_eq_one, map_one])
  obtain ⟨-, c, hc⟩ := SE.cls_spec Certificates.certificate22608.1 (s := s)
    (by simp [SE.isInvB, hs2, hs1])
  have hcen : ∀ p : SE, p * s = s * p := fun p => D.toG_injective (by
    rw [map_mul, map_mul]
    exact (hxc _ (D.toG_mem p)).symm)
  have hcs : c⁻¹ * s * c = s := by rw [mul_assoc, ← hcen c, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcs] at hc
  generalize Fin.ofNat 9 (SE.clsTab s) = i at hc
  by_cases hi : i = 0
  · subst hi
    rw [hc]
    exact congrArg D.toG (by decide : SE.invRep 0 = SE.gen 0)
  · obtain ⟨p, hp⟩ := SE.invRep_noncentral i hi
    rw [← hc] at hp
    exact absurd (hcen p) hp

theorem eq_top_of_centralizer_le {H : Subgroup G}
    (hSH : (D.S : Subgroup G) ≤ H)
    (hC : ∀ u ∈ (D.S : Subgroup G), u * u = 1 → u ≠ 1 → centralizer ({u} : Set G) ≤ H) :
    H = ⊤ := by
  by_contra hne
  have hSyl : IsSylowOf 2 (D.S : Subgroup G) H := (isSylowOf_top D.S).of_le hSH le_top
  have hCH : ∀ t ∈ H, orderOf t = 2 → centralizer ({t} : Set G) ≤ H := by
    intro t ht ht2
    have hz : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
    obtain ⟨c, hcH, hc⟩ := exists_conj_le_of_isSylowOf hSyl (zpowers_le.mpr ht) hz
    have hct := hc t (mem_zpowers t)
    have ht1 : t ≠ 1 := fun h => by
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have h := hC _ hct
      (by rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt]; group)
      (fun h => ht1 (by
        calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group))
    have h' := centralizer_le_of_conj (inv_mem hcH) h
    rwa [show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group] at h'
  have hzS : D.z ∈ (D.S : Subgroup G) := D.toG_mem _
  have hz2 : orderOf D.z = 2 := orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one
  have hzc : ∀ s ∈ (D.S : Subgroup G), D.z * s = s * D.z := fun s hs => by
    have h := D.conj_z_S hs
    calc D.z * s = s * (s⁻¹ * D.z * s) := by group
      _ = s * D.z := by rw [h]
  have hSE := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le_of_unique hne hCH
    D.S hSH hzS hz2 hzc fun x hx hx2 hxc => D.eq_z_of_central hx hx2 hxc
  have hfus : fusionStronglyEmbedded H :=
    ⟨hSE.1, hSE.2.1, fun g hg => hSE.2.2 g⁻¹ fun h => hg (by simpa using inv_mem h)⟩
  have ht2 : orderOf D.t = 2 := orderOf_eq_prime (by rw [pow_two, D.t_mul_t]) D.t_ne_one
  have hcomm := CFSG.StronglyEmbedded.commute_of_mem_sylow_of_fusionStronglyEmbedded hfus D.S
    (D.toG_mem _) ht2 (D.toG_mem ⟨2, 0, 0, 0⟩)
  apply SE.t_not_central
  apply D.toG_injective
  rw [map_mul, map_mul]
  exact hcomm.eq

end GHSylow

end CFSG.ComponentClassification.GHarris
