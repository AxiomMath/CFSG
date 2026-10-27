module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSTransNT
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardBound

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace PLocalAux

theorem sq_Fz_of_isConj {z : G} (hset : HSSetting G z) {p : G} (hp : IsConj z p) {x : G}
    (hx : x ∈ Fz p) : x ^ 2 = 1 ∨ x ^ 2 = p := by
  obtain ⟨g, rfl⟩ := Transport.exists_eq_of_isConj hp
  obtain ⟨⟨-, -, hz, -⟩, hZ4⟩ := hset
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  rw [Transport.Fz_eq, Width.mem_conjugate_iff] at hx
  have key : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by
    rw [conj_pow]
    group
  rw [key]
  rcases Width.sq_F hD hz hx with h | h
  · left
    rw [h]
    group
  · right
    rw [h]

end PLocalAux

theorem cruxPLocal_holds : CruxPLocalStmt := by
  intro G _ _ z hset0 hti
  have hset := hset0
  obtain ⟨⟨-, -, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
  have hZF : ZF z = Z := PartC.ZF_z hD hz hF2
  have hcardF : Nat.card ↥(Fz z) = 64 := (Width.card_Fz hD hz).trans (by norm_num)
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hzF : z ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_left hD.mem_z
  unfold PLocalFacts
  intro u hu
  obtain ⟨g, hg⟩ := Transport.exists_eq_of_isConj hu.1
  have hFu : Fz u = conjugate (Fz z) g := by
    rw [hg]
    exact Transport.Fz_eq z g
  have huF : u ∈ Fz z := (hti.2 u hu).1
  have hu1 : u ≠ 1 := fun h => hz1 (isConj_one_left.mp (h ▸ hu.1))
  have hHSTIu : HSTI u := Transport.hsTI_of_isConj hti hu.1
  have hzFu : z ∈ Fz u := by
    refine (hHSTIu.2 z ⟨hu.1.symm, fun h => hu.2.1 h.symm, ?_⟩).1
    rw [hZF]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Width.Z_comm_F hD hx huF)
  have huFu : u ∈ Fz u := by
    rw [hFu, Width.mem_conjugate_iff, hg, show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hzF
  have huzFu : u * z ∈ Fz u := (Fz u).mul_mem huFu hzFu
  have hcomm_u : ∀ c ∈ Fz u, c * z * c⁻¹ = z ∨ c * z * c⁻¹ = u * z := by
    intro c hc
    have h := comm_Fz_of_isConj hset0 hu.1 hc hzFu
    rw [commutatorElement_def] at h
    rcases h with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  have hnc : ∃ c ∈ Fz u, c * z * c⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    have hs : g * z * g⁻¹ ∈ Fz z := by
      have h := hzFu
      rw [hFu, Width.mem_conjugate_iff] at h
      exact h
    have hsc : ∀ x ∈ Fz z, x * (g * z * g⁻¹) = (g * z * g⁻¹) * x := by
      intro x hx
      have hy : g⁻¹ * x * g ∈ Fz u := by
        rw [hFu, Width.mem_conjugate_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
        exact hx
      have h2 : (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) := by
        have h1 := hcon _ hy
        rwa [mul_inv_eq_iff_eq_mul] at h1
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
        _ = g * z * g⁻¹ * x := by group
    have hsZ : g * z * g⁻¹ ∈ Z := by
      refine Width.mem_Z_of_comm hD hz hs fun b hb => ?_
      have hbF : b ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_right hb
      exact (hsc b hbF).symm
    have hs2 : (g * z * g⁻¹) ^ 2 = 1 := by
      simp [conj_pow, Width.z_sq hz]
    have hs1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hsz : g * z * g⁻¹ = z := Width.involution_eq hD hz hsZ hs2 hs1
    have hcomm : g * z = z * g := by
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [hsz]
    apply hu.2.1
    rw [hg]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hcomm]
      _ = z := by group
  obtain ⟨cc, hccF, hcc⟩ := hnc
  obtain ⟨zK, hzK⟩ : ∃ x : ↥(Fz u), (x : G) = z := ⟨⟨z, hzFu⟩, rfl⟩
  obtain ⟨wK, hwK⟩ : ∃ x : ↥(Fz u), (x : G) = u * z := ⟨⟨u * z, huzFu⟩, rfl⟩
  have hne : zK ≠ wK := by
    intro h
    apply hu1
    have h' := congrArg Subtype.val h
    rw [hzK, hwK] at h'
    calc u = u * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [← h']
      _ = 1 := by group
  have hclass : conjugatesOf zK = {zK, wK} := by
    ext y
    constructor
    · intro hy
      have hy' : IsConj zK y := hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcomm_u c c.2 with h | h
      · exact Or.inl (Subtype.ext (by simpa [hzK] using h))
      · exact Or.inr (Subtype.ext (by simpa [hzK, hwK] using h))
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact IsConj.refl _
      · refine isConj_iff.mpr ⟨⟨cc, hccF⟩, Subtype.ext ?_⟩
        rcases hcomm_u cc hccF with h | h
        · exact absurd h hcc
        · simpa [hzK, hwK] using h
  have hindex : (Subgroup.centralizer {zK} : Subgroup ↥(Fz u)).index = 2 := by
    rw [Subgroup.index_centralizer_eq_ncard, hclass, Set.ncard_pair hne]
  have hK64 : Nat.card ↥(Fz u) = 64 := by
    rw [hFu, Width.card_conjugate']
    exact hcardF
  have hcentK : Nat.card ↥(Subgroup.centralizer {zK} : Subgroup ↥(Fz u)) = 32 := by
    have h := Subgroup.card_mul_index (H := (Subgroup.centralizer {zK} : Subgroup ↥(Fz u)))
    rw [hindex, hK64] at h
    omega
  have hPmap : (Subgroup.centralizer {zK} : Subgroup ↥(Fz u)).map (Fz u).subtype =
      Fz u ⊓ Hz z := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy' : (y : G) * z = z * (y : G) := by
        have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hzK] at h2
        exact h2
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hy'⟩
    · intro hx
      obtain ⟨hxF, hxH⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.mp hxH
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hzK]
      exact h
  have hcardP : Nat.card ↥(Fz u ⊓ Hz z : Subgroup G) = 32 := by
    rw [← hPmap, Subgroup.card_map_of_injective (Fz u).subtype_injective]
    exact hcentK
  have hE : Nat.card ↥(Fz u ⊓ Fz z : Subgroup G) ≤ 8 := by
    have hsq : ∀ x ∈ Fz u ⊓ Fz z, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
      rcases PLocalAux.sq_Fz_of_isConj hset0 hu.1 h1 with h | h
      · exact h
      · rcases Width.sq_F hD hz h2 with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hu.2.1
    have hcomm : ∀ x ∈ Fz u ⊓ Fz z, ∀ y ∈ Fz u ⊓ Fz z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨hxu, hxz⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hyu, hyz⟩ := Subgroup.mem_inf.mp hy
      have h1 := comm_Fz_of_isConj hset0 hu.1 hxu hyu
      have h2 := Width.comm_F hD hz hxz hyz
      have h3 : ⁅x, y⁆ = 1 := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact h1
        · exact h1
        · exact h2
        · exact absurd (h1.symm.trans h2) hu.2.1
      exact commutatorElement_eq_one_iff_mul_comm.mp h3
    have hel : CFSG.Open.IsElemAbelian 2 (Fz u ⊓ Fz z : Subgroup G) :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hsq x hx⟩
    have h := CFSG.GF2Type.Aschbacher1976Full.HS.Card.card_elemAbelian_le hD hz inf_le_right hel
    exact h.trans (by norm_num)
  have hsqP : ∀ p ∈ Fz u ⊓ Hz z, p * p ∈ Subgroup.zpowers u := by
    intro p hp
    rw [← pow_two]
    rcases PLocalAux.sq_Fz_of_isConj hset0 hu.1 (Subgroup.mem_inf.mp hp).1 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers u
  have hcommP : ∀ p ∈ Fz u ⊓ Hz z, ∀ p' ∈ Fz u ⊓ Hz z,
      p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers u := by
    intro p hp p' hp'
    have h := comm_Fz_of_isConj hset0 hu.1 (Subgroup.mem_inf.mp hp).1 (Subgroup.mem_inf.mp hp').1
    rw [commutatorElement_def] at h
    rcases h with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers u
  have hnorm : ∀ c ∈ Hz z, c * u = u * c → ∀ p ∈ Fz u ⊓ Hz z, c * p * c⁻¹ ∈ Fz u ⊓ Hz z := by
    intro c hc hcu p hp
    obtain ⟨hpu, hpz⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨?_, (Hz z).mul_mem ((Hz z).mul_mem hc hpz) ((Hz z).inv_mem hc)⟩
    exact Width.Fz_conj_mem (Subgroup.mem_centralizer_singleton_iff.mpr hcu) hpu
  have hP2 : IsPGroup 2 ↥(Fz u ⊓ Hz z : Subgroup G) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.iff_card.mpr ⟨5, by rw [hcardP]; norm_num⟩
  exact ⟨hP2, hcardP, Subgroup.mem_inf.mpr ⟨huFu, hFH huF⟩, hE, hsqP, hcommP, hnorm⟩

end CFSG.GF2Type.Aschbacher1976Full.HS
