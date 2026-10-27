module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmega

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G] {L A : Subgroup G}

theorem qdGen45_base (e : L ≃* S24) (hAL : A ≤ L)
    (he : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l) :
    Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A (qdIota e qdA1) ∧
      qdIota e qdA1 * x ∈ egOrb L A (qdIota e qdA1)} = A := by
  obtain ⟨hgs, hA1, hA1l, hX, hcov⟩ := Certificates.certificate24847
  have hnorm : ∀ g ∈ qdGens, QdNorm g := fun g hg => (hgs g hg).norm
  have horb : ∀ y ∈ qdReach qdGens qdA1 qdDepth, qdIota e y ∈ egOrb L A (qdIota e qdA1) := by
    intro y hy
    obtain ⟨m, hm, hma⟩ := exists_norm_of_mem_qdReach hnorm hy
    exact ⟨qdIota e m, qdIota_mem_egNL e hAL he hm, by rw [qdIota_conj, hma]⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he y).1 hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 (hcov s hs)
    refine qdIota_elt_mem (qdIota e) _ qdX45 (fun j => ?_) k
    by_cases hj : j < qdX45.length
    · have hx : qdX45.getD j 1 ∈ qdX45 := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      obtain ⟨hxl, hx1, hx2⟩ := hX _ hx
      refine Subgroup.subset_closure ⟨(qdIota_mem_A e he _).2 hxl, horb _ hx1, ?_⟩
      rw [← map_mul]
      exact horb _ hx2
    · rw [List.getD_eq_default _ _ (not_lt.1 hj), map_one]
      exact one_mem _

theorem closure_gen45_conj {b a₁ n : G} (hn : n ∈ egNL L A) (hnb : n * b * n⁻¹ = a₁)
    (hb : Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A b ∧ b * x ∈ egOrb L A b} = A) :
    Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A := by
  have hnN : n ∈ normalizer (A : Set G) := (mem_inf.1 hn).1
  subst hnb
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  · intro y hy
    have hy' : n⁻¹ * y * n ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) y).1 hy
      simpa using this
    have hsub : (MulAut.conj n).toMonoidHom ''
        {x : G | x ∈ A ∧ x ∈ egOrb L A b ∧ b * x ∈ egOrb L A b} ⊆
        {x : G | x ∈ A ∧ x ∈ egOrb L A (n * b * n⁻¹) ∧
          n * b * n⁻¹ * x ∈ egOrb L A (n * b * n⁻¹)} := by
      rintro _ ⟨x, ⟨hxA, ⟨m, hm, hmx⟩, ⟨m', hm', hm'x⟩⟩, rfl⟩
      have hnm : n * m * n⁻¹ ∈ egNL L A := mul_mem (mul_mem hn hm) (inv_mem hn)
      have hnm' : n * m' * n⁻¹ ∈ egNL L A := mul_mem (mul_mem hn hm') (inv_mem hn)
      refine ⟨?_, ⟨n * m * n⁻¹, hnm, ?_⟩, ⟨n * m' * n⁻¹, hnm', ?_⟩⟩
      · exact (mem_normalizer_iff.1 hnN x).1 hxA
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc n * m * n⁻¹ * (n * b * n⁻¹) * (n * m * n⁻¹)⁻¹ = n * (m * b * m⁻¹) * n⁻¹ := by group
          _ = n * x * n⁻¹ := by rw [hmx]
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc n * m' * n⁻¹ * (n * b * n⁻¹) * (n * m' * n⁻¹)⁻¹ = n * (m' * b * m'⁻¹) * n⁻¹ := by
              group
          _ = n * (b * x) * n⁻¹ := by rw [hm'x]
          _ = n * b * n⁻¹ * (n * x * n⁻¹) := by group
    have h1 : (MulAut.conj n).toMonoidHom (n⁻¹ * y * n) ∈
        (Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A b ∧ b * x ∈ egOrb L A b}).map
          (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (by rw [hb]; exact hy')
    rw [MonoidHom.map_closure] at h1
    have h2 := Subgroup.closure_mono hsub h1
    have h3 : n * (n⁻¹ * y * n) * n⁻¹ ∈ Subgroup.closure {x : G | x ∈ A ∧
        x ∈ egOrb L A (n * b * n⁻¹) ∧ n * b * n⁻¹ * x ∈ egOrb L A (n * b * n⁻¹)} := by
      simpa [MulAut.conj_apply] using h2
    rwa [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at h3

theorem gen45_of_type
    (h : SextetType L A) :
    ∀ a₁ ∈ A, a₁ ≠ 1 → Nat.card (egOrb L A a₁) = 45 →
      Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A := by
  obtain ⟨hAL, e, he⟩ := h
  obtain ⟨-, hgens, ⟨h1m, h11, hr1⟩, ⟨h2m, h21, hr2⟩, hl1, hl2, hne, hcover, -⟩ :=
    Certificates.certificate24841
  obtain ⟨-, hnd, -⟩ := m24_e1_check
  have hι := sxtIota_injective e
  have o1 := sxt_egOrb_eq e hAL he h1m h11 hgens hr1
  have o2 := sxt_egOrb_eq e hAL he h2m h21 hgens hr2
  intro a₁ ha₁ ha₁1 hcard
  obtain ⟨s, hs, rfl⟩ := (sxt_mem_A_iff e hAL he a₁).1 ha₁
  have hs1 : s ≠ 1 := fun h => ha₁1 (by rw [h, map_one])
  rcases hcover s hs hs1 with hf | hf
  · have hcls : s ∈ sxtFixClass sxtA1 := (mem_sxtFixClass sxtA1 s).2 ⟨hs, hs1, hf⟩
    have hsmem : sxtIota e s ∈ egOrb L A (sxtIota e sxtA1) := by
      rw [o1]
      exact ⟨s, hcls, rfl⟩
    obtain ⟨n, hn, hnb⟩ := hsmem
    have hnb' : n * qdIota e qdA1 * n⁻¹ = sxtIota e s := hnb
    exact closure_gen45_conj hn hnb' (qdGen45_base e hAL he)
  · exfalso
    have hcls : s ∈ sxtFixClass sxtA2 := (mem_sxtFixClass sxtA2 s).2 ⟨hs, hs1, hf⟩
    have hsmem : sxtIota e s ∈ egOrb L A (sxtIota e sxtA2) := by
      rw [o2]
      exact ⟨s, hcls, rfl⟩
    obtain ⟨n, hn, hnb⟩ := hsmem
    have hsub : egOrb L A (sxtIota e s) ⊆ egOrb L A (sxtIota e sxtA2) := by
      rintro x ⟨m, hm, rfl⟩
      exact ⟨m * n, mul_mem hm hn, by rw [← hnb]; group⟩
    have hfin : (egOrb L A (sxtIota e sxtA2)).Finite := by
      rw [o2]
      exact Set.Finite.image _ (List.finite_toSet _)
    have hle := Nat.card_mono hfin hsub
    have h18 : Nat.card (egOrb L A (sxtIota e sxtA2)) = 18 := by
      rw [Nat.card_coe_set_eq, o2, sxt_ncard_image_list hι (nodup_sxtFixClass hnd _), hl2]
    omega

theorem sextetFactsQ_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    SextetFactsQ L A := by
  have hF := sextetFacts_of_type h
  refine ⟨gen45_of_type h, fix_of_type h, ?_⟩
  obtain ⟨w, hw, hw3, hconj, hfix⟩ := omegaW_of_type h
  refine ⟨w, hw, hw3, fun n hn => ?_, hfix⟩
  have hnL : n ∈ L := (mem_inf.1 hn).2
  have hwL : w ∈ L := (mem_inf.1 hw).2
  have huL : n * w * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hnL hwL) (L.inv_mem hnL)
  set u : G := n * w * n⁻¹ with hu
  rcases hconj n hn with h1 | h1
  · have hc : w⁻¹ * u ∈ A := by
      refine hF.cent _ (L.mul_mem (L.inv_mem hwL) huL) fun a ha => ?_
      calc w⁻¹ * u * a = w⁻¹ * (u * a * u⁻¹) * u := by group
        _ = w⁻¹ * (w * a * w⁻¹) * u := by rw [h1 a ha]
        _ = a * (w⁻¹ * u) := by group
    exact ⟨_, hc, Or.inl (by group)⟩
  · have hc : w * u ∈ A := by
      refine hF.cent _ (L.mul_mem hwL huL) fun a ha => ?_
      calc w * u * a = w * (u * a * u⁻¹) * u := by group
        _ = w * (w⁻¹ * a * w) * u := by rw [h1 a ha]
        _ = a * (w * u) := by group
    exact ⟨_, hc, Or.inr (by group)⟩

end CFSG.EvenSporadicStandard.M24Std
