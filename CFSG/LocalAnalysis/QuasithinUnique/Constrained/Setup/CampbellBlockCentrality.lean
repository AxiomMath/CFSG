module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPropagation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

section Tools

variable {G : Type*} [Group G]

theorem mem_of_not_dvd_orderOf_of_pow_mem {p : ℕ} [Fact p.Prime] {D : Subgroup G} {y : G}
    (hy : ¬ p ∣ orderOf y) {k : ℕ} (hk : y ^ p ^ k ∈ D) : y ∈ D := by
  have hcop : Nat.Coprime (p ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hy)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact D.pow_mem hk m

theorem le_of_noPQuotient [Finite G] {p : ℕ} [Fact p.Prime] {Y D : Subgroup G}
    (hY : NoPQuotient p Y) (h : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ D) : Y ≤ D := by
  calc Y = Subgroup.closure {x : G | x ∈ Y ∧ ¬ p ∣ orderOf x} := hY.closure_eq_ambient.symm
    _ ≤ D := by
      refine (Subgroup.closure_le D).mpr fun x hx => ?_
      obtain ⟨k, hk⟩ := h x hx.1
      exact mem_of_not_dvd_orderOf_of_pow_mem hx.2 hk

theorem exists_pow_mem_of_mem_sup_pGroup {p : ℕ} {L R : Subgroup G} (hR : IsPGroup p R)
    (hRN : R ≤ normalizer (L : Set G)) {g : G} (hg : g ∈ L ⊔ R) : ∃ k : ℕ, g ^ p ^ k ∈ L := by
  rw [sup_comm] at hg
  obtain ⟨r, hr, l, hl, rfl⟩ := C5.mem_sup_of_le_normalizer hRN hg
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ n : ℕ, ∃ l' ∈ L, (r * l) ^ n = r ^ n * l' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', he⟩ := ih
      refine ⟨(r⁻¹ * l' * r) * l, mul_mem ?_ hl, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hRN (inv_mem hr)) l').mp hl'
        simpa using this
      · rw [pow_succ, he]
        simp [pow_succ, mul_assoc]
  obtain ⟨l', hl', he⟩ := hpow (p ^ k)
  exact ⟨k, by rw [he, hk', one_mul]; exact hl'⟩

theorem mem_normalizer_conjJoin {T Y : Subgroup G} {t : G} (ht : t ∈ T) :
    t ∈ normalizer ((conjJoin T Y : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ conjJoin T Y, t * x * t⁻¹ ∈ conjJoin T Y := by
    intro t ht x hx
    refine Subgroup.iSup_induction (fun s : T => Y.map (MulAut.conj (s : G)).toMonoidHom)
      (C := fun x => t * x * t⁻¹ ∈ conjJoin T Y) hx ?_ ?_ ?_
    · rintro s _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_iSup_of_mem (⟨t * s, T.mul_mem ht s.2⟩ : T) ⟨y, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · simp
    · intro a b ha hb
      have := mul_mem ha hb
      simpa [mul_assoc] using this
  exact mem_normalizer_of_conj_mem (key t ht)
    (fun x hx => by simpa using key t⁻¹ (T.inv_mem ht) x hx)

theorem mem_normalizer_of_characteristic {R C : Subgroup G} (hC : (C.subgroupOf R).Characteristic)
    (hCR : C ≤ R) {t : G} (ht : t ∈ normalizer (R : Set G)) : t ∈ normalizer (C : Set G) := by
  have key : ∀ t ∈ normalizer (R : Set G), ∀ x ∈ C, t * x * t⁻¹ ∈ C := by
    intro t ht x hx
    have hmem : ∀ r : R, t * (r : G) * t⁻¹ ∈ R := fun r =>
      (Subgroup.mem_normalizer_iff.mp ht r).mp r.2
    have hmem' : ∀ r : R, t⁻¹ * (r : G) * t ∈ R := fun r => by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) r).mp r.2
      simpa using this
    let φ : R ≃* R :=
      { toFun := fun r => ⟨t * (r : G) * t⁻¹, hmem r⟩
        invFun := fun r => ⟨t⁻¹ * (r : G) * t, hmem' r⟩
        left_inv := fun r => Subtype.ext (by simp [mul_assoc])
        right_inv := fun r => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have h1 := Subgroup.characteristic_iff_map_eq.mp hC φ
    have h2 : φ ⟨x, hCR hx⟩ ∈ (C.subgroupOf R).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  exact mem_normalizer_of_conj_mem (key t ht)
    (fun x hx => by simpa using key t⁻¹ (inv_mem ht) x hx)

theorem subgroupOf_isSubnormal_map_conj {H Y : Subgroup G} (g : G)
    (hY : (Y.subgroupOf H).IsSubnormal) :
    ((Y.map (MulAut.conj g).toMonoidHom).subgroupOf
      (H.map (MulAut.conj g).toMonoidHom)).IsSubnormal := by
  have hmem : ∀ y ∈ H.map (MulAut.conj g).toMonoidHom, g⁻¹ * y * g ∈ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  let ψ : (H.map (MulAut.conj g).toMonoidHom) →* H :=
    { toFun := fun y => ⟨g⁻¹ * y * g, hmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  convert hY.comap ψ using 1
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy
    show g⁻¹ * (y : G) * g ∈ Y
    rw [← hxy]
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem isBlock2_map_conj {H Y : Subgroup G} (hY : IsBlock2 H Y) (g : G) :
    IsBlock2 (H.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) :=
  ⟨Lin2.IsShort2.map_equiv hY.1 (MulAut.conj g), Subgroup.map_mono hY.2.1,
    subgroupOf_isSubnormal_map_conj g hY.2.2⟩

end Tools

section Main

variable {G : Type*} [Group G] [Finite G]

theorem normal_Sylow_part_block_centrality {X T N R P : Subgroup G} (hT : IsSylowTwoOf T X)
    (hNX : N ≤ X) (hNn : X ≤ normalizer (N : Set G)) (hXNT : N ⊔ T = X)
    (hNno : NoPQuotient 2 N) (hRT : R ≤ T) (hRTn : T ≤ normalizer (R : Set G))
    (hRsyl : IsSylowTwoOf R (N ⊔ R)) (hchar : CharTwo (N ⊔ R))
    (hRP : R ≤ P) (hPNR : P ≤ N ⊔ R) (hXP : P ⊔ T = X)
    {s : ℕ} (hs : 1 ≤ s) (Y : Fin s → Subgroup G) (hY : ∀ i, IsBlock2 P (Y i))
    (hgen : R ⊔ ⨆ i, Y i = P) :
    N = ⨆ i, conjJoin T (Y i) ∧ ⁅blockQ (N ⊔ R), N⁆ ≠ ⊥ ∧
      IsElemAbelian 2 (⁅blockQ (N ⊔ R), N⁆ : Subgroup G) ∧
      X ≤ normalizer ((⁅blockQ (N ⊔ R), N⁆ : Subgroup G) : Set G) ∧
      ⁅blockQ (N ⊔ R), N⁆ ≤ centerTorsion 2 (blockQ (N ⊔ R)) ∧
      ⁅⁅blockQ (N ⊔ R), N⁆, N⁆ = ⁅blockQ (N ⊔ R), N⁆ := by
  classical
  set NR : Subgroup G := N ⊔ R with hNR
  set Q : Subgroup G := blockQ NR with hQ
  have hTX : T ≤ X := hT.1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hR2 : IsPGroup 2 R := hRsyl.isPGroup
  have hRX : R ≤ X := hRT.trans hTX
  have hNNR : N ≤ NR := le_sup_left
  have hTN : T ≤ normalizer (N : Set G) := fun t ht => hNn (hTX ht)
  have hRN : R ≤ normalizer (N : Set G) := fun r hr => hNn (hRX hr)
  have hTNR : T ≤ normalizer (NR : Set G) := fun t ht =>
    C1.mem_normalizer_sup (hTN ht) (hRTn ht)
  have hXNR : X ≤ normalizer (NR : Set G) := by
    rw [← hXNT]
    exact sup_le (fun n hn => Subgroup.le_normalizer (hNNR hn)) hTNR
  have hQ2 : IsPGroup 2 Q := C1.blockQ_isPGroup NR
  have hNRQ : NR ≤ normalizer (Q : Set G) := C1.le_normalizer_blockQ NR
  have hXQ : X ≤ normalizer (Q : Set G) := fun g hg => C1.mem_normalizer_blockQ (hXNR hg)
  set D : Subgroup G := ⨆ i, conjJoin T (Y i) with hD
  have hYP : ∀ i, Y i ≤ P := fun i => (hY i).2.1
  have hYN : ∀ i, Y i ≤ N := fun i =>
    le_of_noPQuotient (hY i).1.1
      (fun y hy => exists_pow_mem_of_mem_sup_pGroup hR2 hRN (hPNR (hYP i hy)))
  have hDN : D ≤ N := by
    refine iSup_le fun i => iSup_le fun t x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have := (Subgroup.mem_normalizer_iff.mp (hTN t.2) y).mp (hYN i hy)
    simpa using this
  have hTD : T ≤ normalizer (D : Set G) := fun t ht =>
    mem_normalizer_iSup (fun i => conjJoin T (Y i)) (fun i => mem_normalizer_conjJoin ht)
  have hYD : ∀ i, Y i ≤ D := by
    intro i y hy
    refine Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_iSup_of_mem (⟨1, T.one_mem⟩ : T) ⟨y, hy, ?_⟩)
    simp
  have hPDT : P ≤ D ⊔ T := by
    rw [← hgen]
    exact sup_le (hRT.trans le_sup_right) (iSup_le fun i => (hYD i).trans le_sup_left)
  have hXDT : X ≤ D ⊔ T := by
    rw [← hXP]
    exact sup_le hPDT le_sup_right
  have hND : N ≤ D := le_of_noPQuotient hNno
    (fun n hn => exists_pow_mem_of_mem_sup_pGroup hT2 hTD (hXDT (hNX hn)))
  have hNeq : N = D := le_antisymm hND hDN
  have hbl : ∀ (t : T) (i : Fin s), (Y i).map (MulAut.conj (t : G)).toMonoidHom ≤
      commutatorSubgroup NR Q hNRQ := by
    intro t i x hx
    have hblk := isBlock2_map_conj (hY i) (t : G)
    have hRconj : R ≤ P.map (MulAut.conj (t : G)).toMonoidHom := by
      intro r hr
      refine ⟨(t : G)⁻¹ * r * (t : G), hRP ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hRTn (T.inv_mem t.2)) r).mp hr
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hPconj : P.map (MulAut.conj (t : G)).toMonoidHom ≤ NR := by
      rintro _ ⟨p, hp, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (hXNR (hTX t.2)) p).mp (hPNR hp)
      simpa using this
    obtain ⟨hUW, hQY, -⟩ := full_Sylow_short_core_propagation hchar hRsyl hRconj hPconj hblk
    refine mem_commutatorSubgroup.mpr ⟨hPconj (hblk.2.1 hx), fun q hq => ?_⟩
    have hmem : ⁅q, x⁆ ∈ ⁅Q, (Y i).map (MulAut.conj (t : G)).toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator hq hx
    rw [hQY] at hmem
    exact hUW hmem
  have hDM : D ≤ commutatorSubgroup NR Q hNRQ := iSup_le fun i => iSup_le fun t => hbl t i
  have hQNW : ⁅Q, N⁆ ≤ centerTorsion 2 Q := by
    rw [Subgroup.commutator_le]
    intro q hq n hn
    exact (mem_commutatorSubgroup.mp (hDM (hND hn))).2 q hq
  have hUne : ⁅Q, N⁆ ≠ ⊥ := by
    intro h0
    obtain ⟨-, hQY0, -⟩ :=
      full_Sylow_short_core_propagation hchar hRsyl hRP hPNR (hY ⟨0, hs⟩)
    have hle : ⁅Q, Y ⟨0, hs⟩⁆ ≤ ⁅Q, N⁆ := Subgroup.commutator_mono le_rfl (hYN ⟨0, hs⟩)
    rw [hQY0, h0, le_bot_iff] at hle
    exact blockU_ne_bot_of_isShort2 (hY ⟨0, hs⟩).1 hle
  have hUQ : ⁅Q, N⁆ ≤ Q := commutator_le_left_of_normalizes (hNNR.trans hNRQ)
  have hUab : ∀ a ∈ ⁅Q, N⁆, ∀ b ∈ ⁅Q, N⁆, a * b = b * a := by
    intro a ha b hb
    obtain ⟨-, hac, -⟩ := mem_centerTorsion_iff.mp (hQNW ha)
    exact (hac b (hUQ hb)).symm
  have hU2 : ∀ a ∈ ⁅Q, N⁆, a ^ 2 = 1 := fun a ha => (mem_centerTorsion_iff.mp (hQNW ha)).2.2
  have hsat : ⁅⁅Q, N⁆, N⁆ = ⁅Q, N⁆ :=
    prime_residual_central_commutator_saturation hQ2 (hNNR.trans hNRQ) hNno (fun u hu => by
      obtain ⟨-, huc, -⟩ := mem_centerTorsion_iff.mp (hQNW hu)
      exact Subgroup.mem_centralizer_iff.mpr huc)
  exact ⟨hNeq, hUne, C5.isElemAbelian_two_iff.mpr ⟨hUab, hU2⟩,
    fun g hg => mem_normalizer_commutator (hXQ hg) (hNn hg), hQNW, hsat⟩

end Main

end CFSG.QuasithinUnique.Setup.Campbell
